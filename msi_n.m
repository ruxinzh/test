-- 3-hop, nack-free, invalidation protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount: 2;
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;                -- high priority
  QMax: 2;
  NumVCs: VC2 - VC0 + 1;
  NetMax: ProcCount+1;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };
  Value: scalarset(ValueCount);

  VCType: VC0..NumVCs-1;

  MessageType: enum {  GetS,         -- request for shared state
                       FwdGetS,      -- get data from remote
                       GetS_Ack,         -- read ack (w/ icount)
                       FwdGetS_Ack,      -- forwarded read ack
		                   GetSFwd,         -- forwarded read data

		                   GetM,        -- write request
                       FwdGetM,     -- invalidate remote
                       GetM_Ack,        -- write ack (w/ icount)
                       FwdGetM_Ack,     -- forwarded write ack
		                   GetMFwd,        -- forwarded write data
                      
		                   WBReq,           -- writeback request (w/ or wo/ data)
                       WBAck,           -- writeback ack      
                       WBStaleReadAck,  -- wb ack, but wb was stale due to rd
                       WBStaleWriteAck, -- wb ack, but wb was stale due to wr
 
                       RInvReq,         -- remote invalidation req
                       RIAck            -- ack remote invalidation
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- don't need a destination for verification
      vc: VCType;
      aux: Node;  -- participating node (used when forwarding msgs)
      val: Value;
      cnt: 0..ProcCount;
    End;

  HomeState:
    Record
      state: enum { HM, HS, HI, HMM, HMS };
      owner: Node;	
      pending_node: Node;
      sharers: multiset [ProcCount] of Node; 
      val:Value;
    End;

  ProcState:
    Record
      state: enum { PM, PS, PI,
                    PIS, PIL,          -- I to S and S to I
		                PIM, PIIM, PRIS, PRIF, PMI, PMII, PWIS, PWIF    
                                       -- I to M and M to I
                  };
      val:Value;
      acount: 0..ProcCount;
      icount: 0..ProcCount;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;
--  InBox: array [Node] of array [VCType] of Message;
  msg_processed: boolean;
  LastWrite: Value;

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
               vc:VCType;
	       aux:Node;
               val:Value;
               cnt:0..ProcCount);
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.aux   := aux;
  msg.val   := val;
  msg.cnt   := cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  switch msg.mtype
  case GetM, GetS, WBReq:
    msg_processed := false;  -- we can receive a raw request any time
  else
    error "Unhandled message type!";
  endswitch;
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure SendRInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then
        Send(RInvReq, n, HomeType, VC2, rqst,HomeNode.val, UNDEFINED);
      endif;
      RemoveFromSharersList(n);
    endif;
  endfor;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
var cnthack:0..1;  -- subtracted from RInvReq count to get around compiler
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);

  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = msg.src) != 0
  then 
    cnthack := 1;
  else
    cnthack := 0;
  endif;

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case HI:
    Assert (cnt = 0) "Sharers list non-empty, but line is Invalid";

    switch msg.mtype

    case GetS:
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      Send(GetS_Ack, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,UNDEFINED);

    case GetM:
      HomeNode.state := HM;
      HomeNode.owner := msg.src;
      HomeNode.val   := msg.val;
      Send(GetM_Ack, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,cnt); -- cnt is zero

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HM:
    Assert (IsUndefined(HomeNode.owner) = false) 
       "HomeNode has no owner, but line is Modified";

    switch msg.mtype

    case GetS:
      HomeNode.state := HMS; 
      AddToSharersList(msg.src);    
      HomeNode.pending_node := msg.src;
      Send(FwdGetS, HomeNode.owner, HomeType, VC2, msg.src,UNDEFINED,UNDEFINED);
      
    case GetM:
      HomeNode.state := HMM;
      HomeNode.pending_node := msg.src;
      HomeNode.val   := msg.val;
      Send(FwdGetM, HomeNode.owner, HomeType, VC2, msg.src,UNDEFINED,UNDEFINED);
      
    case WBReq:
      --RemoveFromSharersList(msg.src);
      HomeNode.state := HI;
      HomeNode.val   := msg.val;
      HomeNode.owner := UNDEFINED;
      Send(WBAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HS:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype

    case GetS:
      AddToSharersList(msg.src);
      Send(GetS_Ack, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,UNDEFINED);

    case GetM:
      --RemoveFromSharersList(msg.src);
      HomeNode.state := HM;
      --HomeNode.owner := UNDEFINED;
      HomeNode.val   := msg.val;
      Send(GetM_Ack, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,cnt-cnthack);        
      SendRInvReqToSharers(msg.src); -- removes sharers, too
      HomeNode.owner := msg.src;
      
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HMS:
    switch msg.mtype

    case FwdGetS_Ack:
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      --AddToSharersList(msg.aux);
      HomeNode.val := msg.val;
      undefine HomeNode.owner;
    
    case WBReq:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HS;
      HomeNode.val   := msg.val;
      AddToSharersList(HomeNode.pending_node);
      Send(WBStaleReadAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
      undefine HomeNode.owner;
      undefine HomeNode.pending_node;
    
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
      
  case HMM:
    switch msg.mtype

    case FwdGetM_Ack:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HM;
      HomeNode.owner := HomeNode.pending_node;
      undefine HomeNode.pending_node;

    case WBReq:
      if HomeNode.owner = msg.src
      then
        -- old owner
        Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
	Send(WBStaleWriteAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
	HomeNode.state := HM;
	HomeNode.owner := HomeNode.pending_node;
	--HomeNode.val   := msg.val;
	undefine HomeNode.pending_node;
      elsif HomeNode.pending_node = msg.src
      then
        -- new owner, queue or nack
	msg_processed := false;
      else
        error "WBReq from unexpected node";
      endif;

    else
      ErrorUnhandledMsg(msg, HomeType);
    
    endswitch;

  endswitch;

End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val   do
  switch ps
  case PI:

    switch msg.mtype
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PM:

    switch msg.mtype
    case FwdGetM:
      Send(FwdGetM_Ack, HomeType, p, VC2, UNDEFINED,pv,UNDEFINED);
      Send(GetMFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
      ps := PI;
    case FwdGetS:
      Send(FwdGetS_Ack, HomeType, p, VC2, UNDEFINED,pv, UNDEFINED);
      Send(GetSFwd, msg.aux, p, VC2, UNDEFINED,pv, UNDEFINED);
      ps := PS;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:

    switch msg.mtype
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
      ps := PI;
      pv := msg.val;
    --  LastWrite := msg.val;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  ----------------------------
  -- I/S interaction states
  ----------------------------
  case PIS:

    switch msg.mtype
    case GetS_Ack, GetSFwd:
      pv := msg.val;
      ps := PS;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED, UNDEFINED,UNDEFINED);
      ps := PIL;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PIL:
   
    switch msg.mtype
    case GetS_Ack, GetSFwd:
      ps := PI;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  ----------------------------
  -- I/M interaction states
  ----------------------------
  case PIM:
    
    switch msg.mtype
    case GetMFwd:
      pv := msg.val;
      ps := PM;
    case GetM_Ack:
      Procs[p].icount := msg.cnt;
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
             -- pv := msg.val;
              LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      else
        ps := PIIM;
      endif;
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED, UNDEFINED,UNDEFINED);
    case FwdGetS, FwdGetM:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PIIM:

    switch msg.mtype
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
      -- we've already received the GetM_Ack, so go to M if acount = icount
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
              LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      endif
    case FwdGetS, FwdGetM:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PMI:

    switch msg.mtype
    case WBAck:
      ps := PI;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
      ps := PMII;
    case WBStaleReadAck:
      ps := PRIS;
    case FwdGetS:
      Send(GetSFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
      ps := PRIF;
    case WBStaleWriteAck:
      ps := PWIS;
    case FwdGetM:
      Send(GetMFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
      ps := PWIF;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PMII:
    switch msg.mtype
    case WBAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PRIS:
    switch msg.mtype
    case FwdGetS:
      ps := PI;
      Send(GetSFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PRIF:
    switch msg.mtype
    case WBStaleReadAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PWIS:
    switch msg.mtype
    case FwdGetM:
      ps := PI;
      Send(GetMFwd, msg.aux, p, VC2, UNDEFINED, pv,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PWIF:
    switch msg.mtype
    case WBStaleWriteAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
 
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
ruleset n:Proc Do
  alias p:Procs[n] Do
  
  ruleset v:Value Do 
  rule "read request"
    p.state = PI 
  ==>
    Send(GetS, HomeType, n, VC0, UNDEFINED,UNDEFINED,UNDEFINED);
    p.state := PIS;
  endrule;

  rule "write request PI"
    (p.state = PI)
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED,v, UNDEFINED);
    p.state := PIM;
    p.val   := v;
    clear p.acount;
    clear p.icount;
  endrule;

  rule "write request PM"
    (p.state = PM)
  ==>
    p.val := v;
    LastWrite := v;
  endrule;

  rule "upgrade request"
    (p.state = PS)
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED,v,UNDEFINED);
    p.state := PIM;  -- collapsing states from Nikos' diagrams
    p.val   := v;
    clear p.acount;
    clear p.icount;
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send(WBReq, HomeType, n, VC2, UNDEFINED,p.val,UNDEFINED);  -- fixme
    p.state := PMI;
  endrule;

  rule "evict"
    (p.state = PS)
  ==>
    p.state := PI;
  endrule;
  
  endruleset;
  endalias;

endruleset;

-- receive rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do

    rule "receive"
      (msg.vc = VC2) |
      (msg.vc = VC1 & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0) |
      (msg.vc = VC0 & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0 
                    & MultiSetCount(m:chan, chan[m].vc = VC1)  = 0)
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);

	if msg_processed
	then
	  MultiSetRemove(midx, chan);
	endif;

      else
        ProcReceive(msg, n);

	if msg_processed
	then
	  MultiSetRemove(midx, chan);
	endif;
	  
      endif;

    endrule;
  
    endalias;
    endalias;
  endchoose;  
endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate
For v:Value do
  -- home node initialization
  HomeNode.state := HI;
  undefine HomeNode.sharers;
  undefine HomeNode.owner;
  undefine HomeNode.pending_node;
  undefine HomeNode.sharers;
  HomeNode.val := v;
  endfor;
LastWrite := HomeNode.val;
  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
    clear Procs[i].icount;
    clear Procs[i].acount;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "modified w/ empty sharers list"
  HomeNode.state = HM
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0 ;

invariant "Invalid Implies empty owner"
  HomeNode.state =HI
    ->
      IsUndefined(HomeNode.owner);

invariant "values in valid state match last write"
  Forall n: Proc Do
    Procs[n].state = PS | Procs[n].state =PM
    ->
      Procs[n].val=LastWrite
  end;

invariant "modified implies empty sharers list"
  HomeNode.state=HM
  ->
    MultiSetCount(i:HomeNode.sharers,true)=0;

invariant "Invalid implies empty sharer list"
  HomeNode.state=HI
  ->
    MultiSetCount(i:HomeNode.sharers, true)=0;

invariant "values in memory matches value of last write when shared or invalid"
  Forall n:Proc Do
    HomeNode.state=HS | HomeNode.state=HI
    ->
      HomeNode.val=LastWrite
  end;

invariant "values in shared state match memory"
  Forall n:Proc Do
    HomeNode.state=HS & Procs[n].state=PS
    ->
      HomeNode.val=Procs[n].val
  end;

invariant "modified implies empty sharers list"
  HomeNode.state=HM
  ->
    MultiSetCount(i:HomeNode.sharers, true) =0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = HI
  -> 
    MultiSetCount(i:HomeNode.sharers, true) =0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n: Proc Do
    HomeNode.state = HS | HomeNode.state = HI
    -> 
      HomeNode.val = LastWrite
  end;

invariant "value in shared state match memory"
  Forall n : Proc Do
    HomeNode.state=HS & Procs[n].state = PS
    -> 
      HomeNode.val = Procs[n].val
  end;

invariant "modified implies empty sharers list"
  HomeNode.state = HI
  -> 
    MultiSetCount(i:HomeNode.sharers, true) =0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n: Proc Do
    HomeNode.state=HS |HomeNode.state = HI
    ->
      HomeNode.val=LastWrite
  end;

invariant "values in shared state match memory"
  Forall n: Proc Do
    HomeNode.state = HS &Procs[n].state= PS
    ->
      HomeNode.val=Procs[n].val
  end;


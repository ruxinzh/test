----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;
  QMax: 2;
  NumVCs: VC1 - VC0 + 1;
  NetMax: ProcCount+1;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;

  MessageType: enum { GetS,
                      GetM,
                      PutS,
                      PutM,
                      Data,

                      Fwd_GetS,
                      Fwd_GetM,
                      Inv,
                      Put_Ack,
                      Inv_Ack  --last or not
                     };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType;
      val: Value;
      cnt:0..ProcCount;
    End;

  HomeState:
    Record
      state: enum { HI, HS, HM,					--stable states
      							HS_D }; 								--transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { PI, PS, PM,
                    PIS_D, PIM_AD, PIM_A,
                    PSM_AD, PSM_A, PMI_A, PSI_A, PII_A
                  };
      val: Value;
      counts: 0..ProcCount;
      counti: 0..ProcCount;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
  InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
         val:Value;
         cnt:0..ProcCount
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.cnt   := cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
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

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here 
      endif;
    endif;
  endfor;
End;

procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here
  cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case HI:
    Assert(cnt = 0);
    switch msg.mtype
    case GetS:
      HomeNode.state := HS;
      Send(Data, msg.src, HomeType, VC2, HomeNode.val,cnt);
      AddToSharersList(msg.src);
    case GetM:
      HomeNode.state := HM;
      Send(Data, msg.src, HomeType, VC2, HomeNode.val,cnt);
      HomeNode.owner :=msg.src;
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
    case PutM:
      if(HomeNode.owner != msg.src)
        then
        Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED, cnt);
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HS:
    Assert (cnt != 0);
    switch msg.mtype
    case GetS:
      Send(Data, msg.src, HomeType, VC2, HomeNode.val,cnt);
      AddToSharersList(msg.src); 
    case GetM:
      HomeNode.state := HM;
      if(IsSharer(msg.src))
      then
        Send(Data, msg.src, HomeType, VC2, HomeNode.val,cnt-1);
      else
        Send(Data, msg.src, HomeType, VC2, HomeNode.val,cnt);
      endif;
      HomeNode.owner :=msg.src;
      SendRInvReqToSharers(msg.src); -- removes sharers, too
    case PutS:
      if(cnt = 1 & IsSharer(msg.src))
      then
        HomeNode.state := HI;
      endif;
      RemoveFromSharersList(msg.src);
      Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED, cnt);
    case PutM:
      if(HomeNode.owner != msg.src)
        then
          RemoveFromSharersList(msg.src);
          Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED, cnt);
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HM:
   Assert (IsUndefined(HomeNode.owner) = false) 
   "HomeNode has no owner, but line is Valid";

    switch msg.mtype
    case GetS:
      Send(Fwd_GetS, HomeNode.owner, msg.src, VC2, UNDEFINED, cnt);
      AddToSharersList(msg.src); 
      AddToSharersList(HomeNode.owner);
      HomeNode.owner := UNDEFINED;
      HomeNode.state := HS_D;
    case GetM:
      send(Fwd_GetM, HomeNode.state, msg.src, VC2, UNDEFINED, cnt);
      HomeNode.owner := msg.src;
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
    case PutM:
      if(msg.src = HomeNode.owner)
      then
        Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
        HomeNode.val := msg.val;
        HomeNode.owner := UNDEFINED;
        HomeNode.state := HI;
      else
        Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
  
  case HS_D:
    switch msg.mtype
      case GetS:
        msg_processed := false;
      case GetM:
        msg_processed := false;
      case PutS:
        RemoveFromSharersList(msg.src);
        Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED, cnt);
      case PutM:
        if(HomeNode.owner != msg.src)
          then
            RemoveFromSharersList(msg.src);
            Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED, cnt);
        endif;
      case Data:
        HomeNode.val := msg.val;
        HomeNode.state := HS;
      else
        ErrorUnhandledMsg(msg,HomeType);
    endswitch;
  endswitch;
End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  --alias pcnts:Procs[p].counts do
  --alias pcnti:Procs[p].counti do

  switch ps
  case PI:
    switch msg.mtype
    case Inv:
      send(Inv_Ack, msg.src, p, VC2, UNDEFINED, 0);
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  case PS:
    switch msg.mtype
    case Inv:
      send(Inv_Ack,msg.src,p,VC2,UNDEFINED,0);
      undefine pv;
      ps := PI;
    else 
      ErrorUnhandledMsg(msg,p);
    endswitch;
  
  case PM:
    switch msg.mtype
    case GetM:
      ps  := PI;
      undefine pv;
      send(Data,msg.src,p,VC2,pv,0);
    case GetS:
      ps  := PS;
      send(Data,msg.src,p,VC2,pv,0);
      send(Data,HomeType,p,VC2,pv,0);
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  ----------------------------
  ----------- I/S------------- 
  ----------------------------

  case PIS_D:
    switch msg.mtype
    case Inv:
      msg_processed := false;
    case Data:
      if(msg.src = HomeType)
      then
        Procs[p].counti := msg.cnt;
        if Procs[p].counts = Procs[p].counti
        then
          ps := PS;
          pv := msg.val;
          undefine Procs[p].counts;
          undefine Procs[p].counti;
        endif;
      else
        ps  := PS;
        pv := msg.val;
        --LastWrite  := pv;
      endif;
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  case PSI_A:
    switch msg.mtype
    case Inv:
      ps  := PII_A;
      send(Inv_Ack,msg.src,p,VC2,UNDEFINED,0);
    case Put_Ack:
      ps := PI;
      undefine pv;
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  case PII_A:
    switch msg.mtype
    case Put_Ack:
      ps  := PI;
      undefine pv;
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  ----------------------------
  ----------- I/M------------- 
  ----------------------------

  case PMI_A:
    switch msg.mtype
    case GetM:
      ps  := PII_A;
      send(Data,msg.src,p,VC0,pv,0);
    case GetS:
      ps  := PSI_A;
      send(Data,msg.src,p,VC0,pv,0);
      send(Data,HomeType,p,VC0,pv,0);
    case Put_Ack:
      ps  := PI;
      undefine pv;
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  case PIM_A:
    switch msg.mtype:
    case Inv_Ack:
      Procs[p].counts := Procs[p].counts + 1;
      if Procs[p].counts = Procs[p].counti
      then
        ps := PM;
        LastWrite := pv;
        undefine Procs[p].counts;
        undefine Procs[p].counti;
    case Fwd_GetS, Fwd_GetM:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg,p);
    endswitch;

  case PIM_AD:
   switch msg.mtype
    case Data:
      pv := msg.val;
      if(msg.src = HomeType)
      then
        Procs[p].counti := msg.cnt;
        if Procs[p].counts = Procs[p].counti
        then
          ps := PM;
          LastWrite := pv;
          undefine Procs[p].counts;
          undefine Procs[p].counti;
        else
          ps := PIM_A;
        endif;
      else
        ps  := PM;
        LastWrite  := pv;
      endif;
    case Inv_Ack:
      Procs[p].counts := Procs[p].counts + 1;
    case Fwd_GetS, Fwd_GetM:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  ----------------------------
  ----------- S/M------------- 
  ----------------------------
    case PSM_AD:
      switch msg.mtype     
      case Data:
        pv := msg.val;
        if(msg.src = HomeType)
        then
          Procs[p].counti := msg.cnt;
          if Procs[p].counts = Procs[p].counti
          then
            ps := PM;
            LastWrite := pv;
            undefine Procs[p].counts;
            undefine Procs[p].counti;
          else
            ps := PSM_A;
          endif;
        else
          ps  := PM;
          LastWrite  := pv;
        endif;
      case Inv:
        Send(Inv_Ack, msg.src, p, VC0, UNDEFINED, 0);
        ps := PIM_AD;
      case Fwd_GetM, Fwd_GetS:
        msg_processed   := false;
      else
        ErrorUnhandledMsg(msg,p);
      endswitch;

    case PSM_A:
      switch msg.mtype:
      case Inv_Ack:
        Procs[p].counts := Procs[p].counts + 1;
        if Procs[p].counts = Procs[p].counti
        then
          ps := PM;
          LastWrite := pv;
          undefine Procs[p].counts;
          undefine Procs[p].counti;
      case Fwd_GetS, Fwd_GetM:
        msg_processed := false;
      else
        ErrorUnhandledMsg(msg,p);
      endswitch;

    else
      ErrorUnhandledState();

    endswitch;
    endalias;
    endalias;

  end;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------


-- Processor actions (affecting coherency)
ruleset n:Proc Do
  alias p:Procs[n] Do

  rule "read request"
    (p.state = PI) 
  ==>
    Send(GetS, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    p.state := PIS_D;
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    p.state := PIM_AD;
    clear p.counts;
    clear p.counti;
    p.val := v;
  endrule;
    
  rule "write request PM"
     (p.state = PM)
      ==>
    p.val := v;      
    LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
   endrule;
  
  rule "upgrade request"
    (p.state = PS)
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    p.state := PSM_AD;  -- collapsing states from Nikos' diagrams
    clear p.counts;
    clear p.counti;
    p.val := v;
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send(PutM, HomeType, n, VC2, p.val, UNDEFINED);  -- fixme
    p.state := PMI_A;
  endrule;

  rule "evict PS"
    (p.state = PS)
  ==>
    Send(PutS, HomeType, n, VC2, UNDEFINED, 0); 
    p.state := PSI_A;
  endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

    -- Pick a random message in the network and delivier it
    rule "receive-net"
      (isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
      endif;

      if ! msg_processed
      then
        -- The node refused the message, stick it in the InBox to block the VC.
        box[msg.vc] := msg;
      endif;
    
      MultiSetRemove(midx, chan);
    
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

  -- Try to deliver a message from a blocked VC; perhaps the node can handle it now
  ruleset vc:VCType do
    rule "receive-blocked-vc"
      (! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
      endif;

      if msg_processed
      then
        -- Message has been handled, forget it
        undefine InBox[n][vc];
      endif;
    
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

  For v:Value do
  -- home node initialization
  HomeNode.state := HI;
  undefine HomeNode.owner;
  HomeNode.val := v;
  endfor;
  LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
    clear Procs[i].icount;
    clear Procs[i].acount;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = HI
  ->
      IsUndefined(HomeNode.owner);

invariant "values in valid state match last write"
  Forall n : Proc Do  
    Procs[n].state = PS | Procs[n].state = PM
    ->
      Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
  end;
  
invariant "value is undefined while invalid"
  Forall n : Proc Do  
     Procs[n].state = PI
    ->
      IsUndefined(Procs[n].val)
  end;
  
-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
  HomeNode.state = HM
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = HI
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do
     HomeNode.state = HS | HomeNode.state = HI
    ->
      HomeNode.val = LastWrite
  end;

invariant "values in shared state match memory"
  Forall n : Proc Do  
     HomeNode.state = HS & Procs[n].state = PS
    ->
      HomeNode.val = Procs[n].val
  end;


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

  MessageType: enum {  ReadReq,         -- request for shared state
                       FwdReadReq,      -- get data from remote
                       ReadAck,         -- read ack (w/ icount)
                       FwdReadAck,      -- forwarded read ack
		                   ReadFwd,         -- forwarded read data

		                   WriteReq,        -- write request
                       FwdWriteReq,     -- invalidate remote
                       WriteAck,        -- write ack (w/ icount)
                       FwdWriteAck,     -- forwarded write ack
		                   WriteFwd,        -- forwarded write data
                      
		                   WBReq,           -- writeback request (w/ or wo/ data)
                       WBAck,           -- writeback ack      
                       WBStaleReadAck,  -- wb ack, but wb was stale due to rd
                       WBStaleWriteAck, -- wb ack, but wb was stale due to wr
 
                       RInvReq,         -- remote invalidation req
                       RIAck,            -- ack remote invalidation
		      
                       	FwdShareReq,
			FwdShareAck,
			PutE,
			PutEAck

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
      state: enum { HM, HS, HI,HE, TMM, TMS,TES,TEM,TEMM,TEE };
      owner: Node;	
      pending_node: Node;
      sharers: multiset [ProcCount] of Node; 
      val:Value;
    End;

  ProcState:
    Record
      state: enum { PM, PS, PI, PE,
			PEI,PEII,IEM,IEMI,
                   TISS, TIS, TIL,          -- I to S and S to I
		                IM, IIM, TRIS, TRIF, TMI, TMII, TWIS, TWIF    
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
  case WriteReq, ReadReq, WBReq:
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

    case ReadReq:
      HomeNode.state := HE;
      HomeNode.owner := msg.src;
      Send(ReadAck, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,cnt);

    case WriteReq:
	if Isundefined(msg.cnt)
	then 
      HomeNode.state := HM;
      HomeNode.owner := msg.src;
      HomeNode.val   := msg.val;
      Send(WriteAck, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,cnt); -- cnt is zero
	else 
      HomeNode.state := HI;
      Send(WriteAck, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,cnt); -- cnt is zero
	endif;
   else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HM:
    Assert (IsUndefined(HomeNode.owner) = false) 
       "HomeNode has no owner, but line is Modified";

    switch msg.mtype

    case ReadReq:
      HomeNode.state := TMS; 
      AddToSharersList(msg.src);    
      HomeNode.pending_node := msg.src;
      Send(FwdReadReq, HomeNode.owner, HomeType, VC2, msg.src,UNDEFINED,cnt);
      
    case WriteReq:
      HomeNode.state := TMM;
      HomeNode.pending_node := msg.src;
      HomeNode.val   := msg.val;
      Send(FwdWriteReq, HomeNode.owner, HomeType, VC2, msg.src,HomeNode.val,1);
      
    case WBReq:
      --RemoveFromSharersList(msg.src);
      HomeNode.state := HI;
      HomeNode.val   := msg.val;
      HomeNode.owner := UNDEFINED;
      Send(WBAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,UNDEFINED);

    case PutE:
	Send(PutEAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,0);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HS:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype

    case ReadReq:
      AddToSharersList(msg.src);
      Send(ReadAck, msg.src, HomeType, VC2, UNDEFINED,HomeNode.val,cnt);

    case WriteReq:
	if Isundefined(msg.cnt) 
	then 
      --RemoveFromSharersList(msg.src);
      HomeNode.state := HM;
      --HomeNode.owner := UNDEFINED;
      HomeNode.val   := msg.val;
      Send(WriteAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,cnt-cnthack);        
      SendRInvReqToSharers(msg.src); -- removes sharers, too
      HomeNode.owner := msg.src;
      	else 
	Send(WriteAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,UNDEFINED); 
	endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
----------------------------------------------------------------------------------------
  case HE:
    Assert (IsUndefined(HomeNode.owner)=false) "HomeNode has no owner, but line is Exclusive";

    switch msg.mtype

    case ReadReq:
      HomeNode.state := TES;
      AddToSharersList(msg.src);
      HomeNode.pending_node := msg.src;
      Send(FwdShareReq, HomeNode.owner, HomeType, VC2, UNDEFINED,HomeNode.val,cnt);

    case WriteReq:
      if HomeNode.owner = msg.src
      then 
	HomeNode.state := HM;
	HomeNode.val   := msg.val;
	Send(WriteAck,HomeNode.owner,HomeType,VC2,msg.src,UNDEFINED,UNDEFINED);
      else
	if(Isundefined(msg.cnt)) 
	then 
	HomeNode.state := TEM;
	HomeNode.pending_node := msg.src;
	HomeNode.val := msg.val;
	Send(FwdWriteReq,HomeNode.owner,HomeType,VC2,msg.src,HomeNode.val,UNDEFINED);
	else
	Send(WriteAck,msg.src,HomeType,VC2,msg.src,UNDEFINED,UNDEFINED); 
	endif;
      endif;

    case PutE: 
	HomeNode.state := HI;
	HomeNode.owner := UNDEFINED;
	Send(PutEAck, msg.src,HomeType,VC2,UNDEFINED,UNDEFINED,0); --cnt 0 from HE      
   case FwdShareAck:
	HomeNode.state := HE;
   else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case TES:
    switch msg.mtype

    case FwdShareAck:
	if (msg.cnt = 0)
	then 
		HomeNode.state := TEE;
		
	elsif (msg.cnt = 1)
	then 
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      Send(ReadAck,HomeNode.pending_node,HomeType,VC2,UNDEFINED,HomeNode.val,1);
      undefine HomeNode.owner;
	elsif (msg.cnt = 2)
	then 
	HomeNode.state := HE;
	Send(ReadAck,HomeNode.pending_node,HomeType,VC2,UNDEFINED,UNDEFINED,2); --inv TIS
	RemoveFromSharersList(HomeNode.pending_node);
	HomeNode.pending_node := UNDEFINED;    
	endif;
    case PutE:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := TEE;
      RemoveFromSharersList(HomeNode.pending_node);
      HomeNode.owner := HomeNode.pending_node;
      --Send(ReadAck,HomeNode.pending_node,HomeType,VC2,UNDEFINED,HomeNode.val,0);
      Send(PutEAck,msg.src,HomeType,VC2,UNDEFINED,UNDEFINED,1); --cnt 1 from TES
     -- undefine HomeNode.pending_node;
    
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
  
  case TEE:
	switch msg.mtype
	case FwdShareAck : 
	HomeNode.state := HE;
     	Send(ReadAck,HomeNode.pending_node,HomeType,VC2,UNDEFINED,HomeNode.val,0);
	undefine HomeNode.pending_node;
    case PutE:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HE;
      RemoveFromSharersList(HomeNode.pending_node);
      HomeNode.owner := HomeNode.pending_node;
      --Send(ReadAck,HomeNode.pending_node,HomeType,VC2,UNDEFINED,HomeNode.val,0);
      Send(PutEAck,msg.src,HomeType,VC2,UNDEFINED,UNDEFINED,1); --cnt 1 from TES
     -- undefine HomeNode.pending_node;
 
	else 
	ErrorUnhandledMsg(msg,HomeType);
	endswitch;
	  
  case TEM:
    switch msg.mtype

    case FwdWriteAck:
	if Isundefined(msg.cnt) 
	then 
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HM;
      HomeNode.owner := HomeNode.pending_node;
      Send(WriteAck,HomeNode.owner,HomeType,VC2,UNDEFINED,UNDEFINED,cnt);
      undefine HomeNode.pending_node;
	else 
	HomeNode.state:= TEMM;
	endif;
    case PutE:
      if HomeNode.owner = msg.src
      then
        Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
	Send(PutEAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,1);
	HomeNode.state:=TEMM;
      else
        error "PutE from unexpected node";
      endif;

    else
      ErrorUnhandledMsg(msg, HomeType);
    
    endswitch;

  case TEMM:
	switch msg.mtype
	case FwdWriteAck:
	Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      	HomeNode.state := HM;
     	HomeNode.owner := HomeNode.pending_node;
      	Send(WriteAck,HomeNode.owner,HomeType,VC2,UNDEFINED,UNDEFINED,cnt);
      	undefine HomeNode.pending_node;
	
	case PutE:
      if HomeNode.owner = msg.src
      then
        Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
	Send(PutEAck, msg.src, HomeType, VC2, UNDEFINED,UNDEFINED,1);
      	Send(WriteAck,HomeNode.pending_node,HomeType,VC2,UNDEFINED,UNDEFINED,cnt);
	HomeNode.state := HM;
	HomeNode.owner := HomeNode.pending_node;
	HomeNode.pending_node := UNDEFINED;
      else
        error "PutE from unexpected node";
      endif;
	else 
	ErrorUnhandledMsg(msg,HomeType);
	endswitch;


-----------------------------------------------------------------------------------
  case TMS:
    switch msg.mtype

    case FwdReadAck:
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
      
  case TMM:
    switch msg.mtype

    case FwdWriteAck:
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
    case FwdWriteReq:
      Send(FwdWriteAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,UNDEFINED);
    case FwdShareReq:
      ps := PI; 
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PM:

    switch msg.mtype
    case FwdWriteReq:
      Send(FwdWriteAck, HomeType, p, VC2, UNDEFINED,pv,UNDEFINED);
      Send(WriteFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
      ps := PI;
    case FwdReadReq:
      Send(FwdReadAck, HomeType, p, VC2, UNDEFINED,pv, UNDEFINED);
      Send(ReadFwd, msg.aux, p, VC2, UNDEFINED,pv, UNDEFINED);
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
---------------------------------------------------------------------- 
 case PE:

    switch msg.mtype
    case FwdWriteReq:
      Send(FwdWriteAck, HomeType, p, VC2, UNDEFINED,pv,UNDEFINED); --cnt 1 from PE
      ps := PI;
    case FwdShareReq:
      Send(FwdShareAck,HomeType,p,VC2,UNDEFINED,pv,1); --cnt 1 form PE
      ps := PS;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
------------------------------------------------------------------------


  ----------------------------
  -- I/S interaction states
  ----------------------------
  case TIS:

    switch msg.mtype
    case ReadAck:
      pv := msg.val;
      if msg.cnt = 0
	then
      ps := PE;
      elsif msg.cnt=1
	then
      ps := PS;
	else 
	ps := PS;
--	elsif msg.cnt=1
--	then
--	ps := PI;
      endif;
    case FwdShareReq:
	Send(FwdShareAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,1); --cnt = 1 Form TIS
	ps := TISS;
    case FwdWriteReq:
	ps:= TIL;
	Send(FwdWriteAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,UNDEFINED);
    case ReadFwd:
      pv := msg.val;
      ps := PS;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED, UNDEFINED,UNDEFINED);
      ps := TIL;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TISS:
	switch msg.mtype
	case ReadAck:
	ps:=PS;
	pv:=msg.val;
	case RInvReq:
	Send(RIAck,msg.aux,p,VC2,UNDEFINED,UNDEFINED,UNDEFINED);
	ps := TIL;
	else 
	ErrorUnhandledMsg(msg,p);
	endswitch;
	
  case TIL:
   
    switch msg.mtype
    case ReadAck, ReadFwd:
      ps := PI;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  ----------------------------
  -- I/M interaction states
  ----------------------------
  case IM:
    
    switch msg.mtype
    case WriteFwd:
      pv := msg.val;
      ps := PM;
      LastWrite := msg.val;
    case WriteAck:
      Procs[p].icount := msg.cnt;
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
             -- pv := msg.val;
              LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      else
        ps := IIM;
      endif;
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED, UNDEFINED,UNDEFINED);
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
------------------------------------------------------------------------
  case IEM:
    
    switch msg.mtype
    case WriteFwd:
      pv := msg.val;
      ps := PM;
    case WriteAck:
	ps := PM;
     	LastWrite := pv;
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED, UNDEFINED,UNDEFINED);
    case FwdShareReq :
      Send(FwdShareAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,2); --cnt=2 from IEM
    case FwdReadReq:
 	msg_processed := false; 
    case FwdWriteReq:
	ps := IEMI;
     	Send(FwdWriteAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,UNDEFINED);
	if ( ! Isundefined(msg.cnt))
	then 
        Send(WriteFwd,msg.aux,p,VC2,UNDEFINED,msg.val,UNDEFINED);
	endif
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case IEMI:
	switch msg.mtype
	case WriteAck:
	ps:=PI;
	case WriteFwd:
	ps:=PM;
        LastWrite := pv;
	case FwdShareReq,FwdWriteReq,FwdReadReq:
	msg_processed := false;
	else 
	ErrorUnhandledMsg(msg,p);
	endswitch;
 
  case PEI:
    switch msg.mtype
    case PutEAck:
	if msg.cnt = 0 
	then 
	ps := PI;
	else 
	ps := PEII;
	endif;
    case FwdWriteReq:
	ps := PEII;
	Send(FwdWriteAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,0);--cnt 0 ack from PEI
    case FwdShareReq:
	ps := PEII;
	Send(FwdShareAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,0); --cnt 0 ack from PEI
    else 
      ErrorUnhandledMsg(msg,p);
    endswitch;

    case PEII:
	switch msg.mtype
	case PutEAck:
	ps := PI; 
	case FwdShareReq:
	Send(FwdShareAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,UNDEFINED);
	ps:=PI;
	case FwdWriteReq:
	ps := PI;
	Send(FwdWriteAck,msg.src,p,VC2,UNDEFINED,UNDEFINED,UNDEFINED);
	else 
	ErrorUnhandledMsg(msg,p);

	endswitch;
---------------------------------------------------------------------------

  case IIM:

    switch msg.mtype
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
      -- we've already received the WriteAck, so go to M if acount = icount
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
              LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      endif
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TMI:

    switch msg.mtype
    case WBAck:
      ps := PI;
    case RInvReq:
      Send(RIAck, msg.aux, p, VC2, UNDEFINED,UNDEFINED,UNDEFINED);
      ps := TMII;
    case WBStaleReadAck:
      ps := TRIS;
    case FwdReadReq:
      Send(ReadFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
      ps := TRIF;
    case WBStaleWriteAck:
      ps := TWIS;
    case FwdWriteReq:
      Send(WriteFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
      ps := TWIF;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TMII:
    switch msg.mtype
    case WBAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIS:
    switch msg.mtype
    case FwdReadReq:
      ps := PI;
      Send(ReadFwd, msg.aux, p, VC2, UNDEFINED,pv,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIF:
    switch msg.mtype
    case WBStaleReadAck:
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TWIS:
    switch msg.mtype
    case FwdWriteReq:
      ps := PI;
      Send(WriteFwd, msg.aux, p, VC2, UNDEFINED, pv,UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TWIF:
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
    Send(ReadReq, HomeType, n, VC0, UNDEFINED,UNDEFINED,UNDEFINED);
    p.state := TIS;
  endrule;

  rule "write request PI"
    (p.state = PI)
  ==>
    Send(WriteReq, HomeType, n, VC0, UNDEFINED,v, UNDEFINED);
    p.state := IM;
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

  rule "write request PE"
    (p.state = PE)
  ==>
    Send(WriteReq,HomeType,n,VC0,UNDEFINED,v,1);
    p.state := IEM;
    p.val := v;
  endrule;


  rule "upgrade request"
    (p.state = PS)
  ==>
    Send(WriteReq, HomeType, n, VC0, UNDEFINED,v,UNDEFINED);
    p.state := IM;  -- collapsing states from Nikos' diagrams
    p.val   := v;
    clear p.acount;
    clear p.icount;
  endrule;

  rule "writeback PM"
    (p.state = PM)
  ==>
    Send(WBReq, HomeType, n, VC2, UNDEFINED,p.val,UNDEFINED);  -- fixme
    p.state := TMI;
  endrule;

  rule "evict PE"
    (p.state = PE)
  ==>
    Send(PutE,HomeType,n,VC2,UNDEFINED,p.val,UNDEFINED);
    p.state := PEI;
  endrule;
 
  rule "evict PS"
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


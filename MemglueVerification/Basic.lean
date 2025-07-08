import Mathlib

structure SystemConfig where
    threads     : PNat          -- positive Nat: 1, 2, 3, ...
    steps       : PNat
    addrCount   : PNat
deriving Inhabited


-- TYPES -----------------------------------------
abbrev ShimId (c : SystemConfig) : Type := Fin (c.threads)
abbrev Addr (c : SystemConfig) : Type := Fin (c.addrCount)
abbrev Data : Type := Nat
abbrev Timestamp : Type := Nat
abbrev Node (c : SystemConfig) : Type := Fin (c.threads + 1)

instance (c : SystemConfig) : Inhabited (ShimId c) where default := 0
instance (c : SystemConfig) : Inhabited (Addr c) where default := 0
instance (c : SystemConfig) : Inhabited (Node c) where default := 0

inductive MType : Type where
    | WRITE
    | WRITE_ACK
    | RREQ
    | EVICT
    | FREQ
    | RRESP
    | FRESP

inductive OpStrength : Type where
    | RLX
    | REL
    | ACQ
    | SC
deriving Inhabited, DecidableEq

structure Message (c : SystemConfig) : Type where
    mtype : MType := MType.WRITE
    src : Node c := 0
    dst : Node c := 0
    data :  Data := 0
    addr : Addr c := 0
    ts : Timestamp := 0
    stren : OpStrength := OpStrength.RLX
instance (c : SystemConfig) : Inhabited (Message c) where
    default := {
        mtype := MType.WRITE
        src := 0
        dst := 0
        data := 0
        addr := 0
        ts := 0
        stren := OpStrength.RLX
    }

-- matrix one row of messages per node (CC + shims)
-- def NETOrdered : Type := Matrix Node (Fin NetMax) Message
def NETOrdered (c : SystemConfig) : Type := Vector (List (Message c)) (c.threads + 1)
instance (c : SystemConfig) : Inhabited (NETOrdered c) where default := Vector.replicate (c.threads + 1) (List.singleton (default : (Message c)))
-- NETOrdered: array[Node] of array[0..NetMax-1] of Message;
-- NETOrderedCount: array[Node] of 0..NetMax;
-- NETUnordered: array[Node] of multiset[NetMax] of Message;

inductive CacheState : Type where
    | Invalid | Valid
deriving Inhabited, DecidableEq

structure ShimElemState : Type where
    state : CacheState
    data : Data
    ts : Timestamp
    syncBit : Bool
deriving Inhabited

structure CCElemState (c : SystemConfig) : Type where
    data : Data
    ts : Timestamp
    sharers : Vector Bool c.threads
deriving Inhabited

def ShimCache (c : SystemConfig) : Type := Vector ShimElemState c.addrCount
instance (c : SystemConfig) : Inhabited (ShimCache c) where default := Vector.replicate c.addrCount (default : ShimElemState)

def CCCache (c : SystemConfig) : Type := Vector (CCElemState c) c.addrCount
instance (c : SystemConfig) : Inhabited (CCCache c) where default := Vector.replicate c.addrCount (default : CCElemState c)

-- Litmus test specific---------
inductive PermissionType : Type where
    | load
    | store
    | fence
    | none
deriving DecidableEq, Inhabited

structure Instr (c : SystemConfig) : Type where
    access : PermissionType       -- may not need this
    stren : OpStrength
    addr : Addr c
    data : Data      -- Value store for read operation performed */
    pend : Bool
deriving Inhabited

-- structure FifoQueue : Type where                      -- each shim has a queue of litmust test instructions to perform
--     Queue: Vector Instr InstrCount -- array[0..2] of Instr;
--     QueueInd: Fin (InstrCount + 2) -- 0..2+1;
--     QueueCnt: Fin (InstrCount + 2) -- 0..2+1;

---------------------------------
abbrev QInd (c : SystemConfig) : Type := Fin c.steps
abbrev QCnt (c : SystemConfig) : Type := Fin c.steps
instance (c : SystemConfig) : Inhabited (QInd c) where default := 0
instance (c : SystemConfig) : Inhabited (QCnt c) where default := 0

structure Shim (c : SystemConfig) : Type where
    state : ShimCache c
    active : Bool   -- active = still needs to execute litmus tests instructions
    pendingWSC : Bool
    fencePending : Bool
    -- queue : FifoQueue   -- queue of litmus test instructions to be performed. replaced with tracesets
    qInd : QInd c
    qCnt : QCnt c
deriving Inhabited

structure CCMachine (c : SystemConfig) : Type where
    cache : CCCache c
deriving Inhabited

-- NOTE: this is zero indexed unlike in murphi model....... change?
def ShimType (c : SystemConfig) : Type := Vector (Shim c) c.threads    -- array[ShimId] of Shim;
instance (c : SystemConfig) : Inhabited (ShimType c) where default := Vector.replicate c.threads (default : Shim c)


----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
-- def CC : CCMachine := sorry
-- def Shims : ShimType := sorry       -- Q: queues for each shim are instructions for litmus tests or local reads/writes. Net is 2d array, storing non-local writes from the CC?
-- def Net : NETOrdered := sorry
-- def NetCount : NETOrderedCount := sorry





-- inductive Op where
--     | read (addr : Nat)
--     | write (addr : Nat) (val : Nat)
--     | noop
--     deriving Inhabited, Repr

-- structure Instr : Type where
--     access : PermissionType       -- may not need this
--     stren : OpStrength
--     addr : Addr
--     data : Data      -- Value store for read operation performed */
--     pend : Bool

universe u
set_option diagnostics true
-- A single trace is a sequence of operations.
def Trace (α : Type u) (steps : Nat) := Fin steps → α
-- #check Trace Instr 2
-- def sometrace : Trace Instr 2 :=
--   ![
--     { access := PermissionType.load, stren := OpStrength.RLX, addr := ⟨0, by decide⟩, data := ⟨0, by decide⟩, pend := false },
--     { access := PermissionType.store, stren := OpStrength.SC, addr := ⟨1, by decide⟩, data := ⟨1, by decide⟩, pend := true }
--   ]
-- #check sometrace 0
-- Multi-threaded traces are a sequence of traces.
def TraceSet (α : Type u) (threads : Nat) (steps : Nat) := Fin threads → Trace α steps
-- #check TraceSet Instr 3 2

-- The execution trace generated by the program.
def Execution (c : SystemConfig) := TraceSet (Instr c) c.threads c.steps
instance (c : SystemConfig) : Inhabited (Execution c) where default := fun _ _ => (default : Instr c)
-- #check Execution 3 2
-- The output trace generated by the cache coherence protocol.
def Output (c : SystemConfig) := TraceSet (Option Nat) c.threads c.steps
instance (c : SystemConfig) : Inhabited (Output c) where default := fun _ _ => none
-- #check Output 3 2
-- def QInd (c : SystemConfig) := Vector (Fin c.steps) c.threads
-- #check QInd 3 2
-- def QCnt (c : SystemConfig) := Vector (Fin c.steps) c.threads
/--
1. Writes to the same address are totally ordered.
2. Reads return the most recent write in that order.
3. Writes become visible to all processors atomically.
-/
structure Coherence {c : SystemConfig} (e : Execution c) (o : Output c) : Prop where
    writes_total_order : False -- Placeholder for actual definition
    -- ∀ writes w1, w2. ((∀ threads w1 < w2) or (∀ threads w1 > w2))??
    reads_return_last_write : False -- Placeholder for actual definition
    write_atomicity : False -- Placeholder for actual definition


def protocol {c : SystemConfig} (e : Execution c) : (Output c) :=
    sorry -- Implementation of the protocol goes here

theorem protocol_respects_coherence :
    ∀ {c : SystemConfig} (e : Execution c) (o : Output c), protocol e = o → Coherence e o := by sorry


----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
-- def updateOutput (o : Output 3 2) (targetThread : Fin 3) (targetStep : Fin 2) (val : Nat) : Output 3 2 :=
--   fun (t : Fin 3) =>
--     if t = targetThread then
--       fun (s : Fin 2) =>
--         if s = targetStep then
--           some val              -- update the desired (thread, step) position
--         else
--           o t s                 -- keep the old value for other steps
--     else
--       o t                       -- keep the old trace for other threads
-- def updateMsgNet {threads steps : Nat} (net : NetOrdered threads steps) (netCounts : NetOrderedCounts threads)
--                 (target : Node) ()
def netWithAddedMsg {c : SystemConfig} (msg : Message c) (net : NETOrdered c) : NETOrdered c :=
    let oldList : List (Message c) := net.get msg.dst
    let updatedList : List (Message c) := oldList.append [msg]
    let updatedNet : NETOrdered c := net.set (Fin.val msg.dst) updatedList
    updatedNet

def send {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c)
         (data' : Data) (addr' : Addr c) (ts' : Timestamp) (stren' : OpStrength)
         (net : NETOrdered c)
         : NETOrdered c :=

        let msg : (Message c) := {mtype := mtype', src := src', dst := dst', data := data', addr := addr', ts := ts', stren := stren'}
        netWithAddedMsg msg net

def sendFence {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c) (net : NETOrdered c) : NETOrdered c :=
    let msg : (Message c) := {mtype := mtype',
                              src := src',
                              dst := dst',
                            --   remaining don't matter ↓
                            --   data := 0,
                            --   addr := none,
                            --   ts := 0,
                            --   stren := OpStrength.RLX,
                             }
    netWithAddedMsg msg net

def popMessage {c : SystemConfig} (dst : Node c) (net : NETOrdered c) : NETOrdered c :=
    let oldList : List (Message c) := net.get dst
    let updatedList : List (Message c) := oldList.tail
    let updatedNet : NETOrdered c := net.set (Fin.val dst) updatedList
    updatedNet


-- NOTES: changed data to be in Nat, rather than original Data. shim : Fin nThreads = ShimId (zero indexed now)
-- Update output of litmus test load
#check PermissionType.none
def updateVal {c : SystemConfig} (targetThread : ShimId c) (data : Data)
                (e : Execution c)
                (shimVec : ShimType c)
                (o : Output c) : Output c :=

                let targetStep : QInd c := (shimVec.get targetThread).qInd
                let cntStep := (shimVec.get targetThread).qCnt
                -- CHECK: Do we need qCnt? can't we just have check for no op, and that would mean that we shouldn't write
                if (targetStep < cntStep) ∧ ((e targetThread targetStep).access ≠ PermissionType.none) then
                    -- update output
                    fun (t : ShimId c) =>
                        if t = targetThread then
                            fun (s : Fin c.steps) =>
                                if s = targetStep then
                                    some data
                                else
                                    o t s
                        else
                            o t
                else
                    -- keep same
                    fun (t : ShimId c) => fun (s : Fin c.steps) => o t s

-- Remove litmus test instruction
def popInstr {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c)
            (e : Execution c)
            : (ShimType c) × (Execution c) :=

            let qInd := (shimVec.get shim).qInd
            let qCnt := (shimVec.get shim).qCnt
            let newExec : Execution c :=       -- still a function but for that thread instruction, pend = false
                fun (t : ShimId c) =>
                    fun (s : Fin c.steps) =>
                        if t = shim ∧ s = qInd then {e t s with pend := false}
                        else e t s

            if h : qInd.val + 1 < c.steps then
                -- qInd not about to go out of range → can increment qInd and change active state as in murphi
                let nextQInd : QInd c := ⟨qInd.val + 1, h⟩
                let shimInactive : Prop := nextQInd = qCnt ∨ (e shim nextQInd).access = PermissionType.none
                let newActiveState : Bool := if shimInactive then false else (shimVec.get shim).active
                let newShim : Shim c := {(shimVec.get shim) with qInd := nextQInd, active := newActiveState}
                let newShimVec : ShimType c := shimVec.set shim newShim

                (newShimVec, newExec)
            else
                -- qInd + 1 is out of range, i.e. after pop, shim should def be inactive
                let newShim : Shim c := {(shimVec.get shim) with active := false}
                let newShimVec : ShimType c := shimVec.set shim newShim

                (newShimVec, newExec)

--   Procedure PopInstr(shim: ShimId);
--   Begin
--     alias sQ: Shims[shim].queue.Queue do
--     alias QInd: Shims[shim].queue.QueueInd do
--     alias QCnt: Shims[shim].queue.QueueCnt do

--     sQ[QInd].pend := false;
--     QInd := QInd + 1;
--     if QInd = QCnt then
--       Shims[shim].active := false;
--     else
--       if isundefined(sQ[QInd].access) then -- why is this here? Why would it be undefined?
-- 	      Shims[shim].active := false;
--       endif;
--     endif;

--     endalias;
--     endalias;
--     endalias;
--   End;

-- structure ShimElemState : Type where
--     state : CacheState
--     data : Data
--     ts : Timestamp
--     syncBit : Bool

-- structure CCElemState (c : SystemConfig) : Type where
--     data : Data
--     ts : Timestamp
--     sharers : Vector Bool c.threads

-- def ShimCache (c : SystemConfig) : Type := Vector ShimElemState c.addrCount
-- def CCCache (c : SystemConfig) : Type := Vector (CCElemState c) c.addrCount


-- Shim-specific ------------------------------------------------------------
def shimWriteCache {c : SystemConfig} (shim : ShimId c) (state' : CacheState)
                   (data' : Data) (ts' : Timestamp) (addr : Addr c) (shimVec : ShimType c)
                   : ShimType c :=
                   let curShimCache : ShimCache c := (shimVec.get shim).state
                   let newCacheState : ShimCache c := curShimCache.set addr {curShimCache.get addr with state := state', data := data', ts := ts'}
                   let newShim := {shimVec.get shim with state := newCacheState}
                   let newShimVec := shimVec.set shim newShim

                   newShimVec
--   Procedure ShimWriteCache(shim: ShimId;
-- 			   state: CacheState;
-- 			   data: Data;
-- 			   ts: Timestamp;
-- 			   addr: Addr);
--   Begin
--   alias shimElem: Shims[shim].state[addr] do
--     shimElem.state := state;
--     shimElem.data := data;
--     shimElem.ts := ts;
--   endalias;
--   End;

def shimIncrTS {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (shimVec : ShimType c) : ShimType c :=
    let curShimCache : ShimCache c := (shimVec.get shim).state
    let newCacheState : ShimCache c := curShimCache.set addr {curShimCache.get addr with ts := (curShimCache.get addr).ts + 1}
    let newShim := {shimVec.get shim with state := newCacheState}
    let newShimVec := shimVec.set shim newShim

    newShimVec
--   Procedure ShimIncrTS(shim: ShimId; addr: Addr);
--   Begin
--   alias shimElem: Shims[shim].state[addr] do
--     shimElem.ts := shimElem.ts + 1;
--   endalias;
--   End;

-- def shimWriteCache {c : SystemConfig} (shim : ShimId c) (state' : CacheState)
--                    (data' : Data) (ts' : Timestamp) (addr : Addr c) (shimVec : ShimType c)
--                    : ShimType c


-- SHIM: incoming messages
def shimReceive {c : SystemConfig} (msg : Message c)
                (shimVec : ShimType c) (e : Execution c) (o : Output c)
                : (ShimType c) × (Execution c) × (Output c) :=
    if h1 : msg.dst < c.threads.val then
        let curShim : ShimId c := ⟨msg.dst, h1⟩
        let curShimCache : ShimCache c := (shimVec.get curShim).state
        let addr := msg.addr

        match msg.mtype with
            | MType.WRITE =>
                let shimElem : ShimElemState := curShimCache.get addr
                if msg.ts > shimElem.ts then
                    (shimWriteCache curShim CacheState.Valid msg.data msg.ts addr shimVec, e, o)
                else
                    (shimIncrTS curShim addr shimVec, e, o)
            | MType.WRITE_ACK =>
                let shimElem : ShimElemState := curShimCache.get addr
                if shimElem.syncBit = true then
                    let newTs : Timestamp := msg.ts+shimElem.ts-1
                    let modShims : ShimType c := shimWriteCache curShim CacheState.Valid shimElem.data newTs addr shimVec
                    let modShimElem : ShimElemState := {(modShims.get curShim).state.get addr with syncBit := false}
                    let modShimCache : ShimCache c := (modShims.get curShim).state.set addr modShimElem
                    let modShim : Shim c := {(modShims.get curShim) with state := modShimCache, pendingWSC := false}

                    let newShimVec : ShimType c := modShims.set curShim modShim
                    (newShimVec, e, o)
                else
                    let modShim : Shim c := {(shimVec.get curShim) with pendingWSC := false}
                    let newShimVec : ShimType c := shimVec.set curShim modShim
                    (newShimVec, e, o)
            | MType.RRESP =>
                let modShims : ShimType c := shimWriteCache curShim CacheState.Valid msg.data msg.ts addr shimVec
                let modShimElem : ShimElemState := {(modShims.get curShim).state.get addr with syncBit := false}
                let modShimCache : ShimCache c := (modShims.get curShim).state.set addr modShimElem
                let modShim : Shim c := {(modShims.get curShim) with state := modShimCache}
                let modShims' : ShimType c := modShims.set curShim modShim

                let newOutput := updateVal curShim msg.data e shimVec o
                let (newShimVec, newExec) := popInstr curShim modShims' e
                (newShimVec, newExec, newOutput)
            | MType.FRESP =>
                let modShim : Shim c := {(shimVec.get curShim) with fencePending := false}
                let modShimVec : ShimType c := shimVec.set curShim modShim

                if (shimVec.get curShim).pendingWSC = false then
                    let (newShimVec, newExec) := popInstr curShim modShimVec e
                    (newShimVec, newExec, o)
                else
                    let modShim' := {(shimVec.get curShim) with pendingWSC := false}
                    let newShimVec : ShimType c := modShimVec.set curShim modShim'
                    (newShimVec, e, o)
            | _ => panic! "message with wrong message type was passed into ShimReceive"        -- no change in weird error cases (msg.dst = c.threads means CC but this is shimReceive... shouldn't happen)
    else
        panic! "message with destination that was not a shim was passed into ShimReceive (was CC or some other random dst value)"

--   Procedure ShimReceive(msg:Message);
--   var shimElem:ShimElemState;
--   var addr:Addr;
--   var data:Data;
--   var ts:Timestamp;
--   Begin
--     --addr := msg.addr;
--     --data := msg.data;
--     --ts := msg.ts;

--     switch msg.mtype
--     case WRITE:									-- Q: non-local write from CC from another shim?
--       shimElem := Shims[msg.dst].state[msg.addr];
--       Assert (!shimElem.syncBit) "syncBit set on write update";
--       if msg.ts > shimElem.ts
--       then
--         ShimWriteCache(msg.dst,Valid,msg.data,msg.ts,msg.addr);
--       else
--         ShimIncrTS(msg.dst,msg.addr);
--       endif;

--     case WRITE_ACK:
--       shimElem := Shims[msg.dst].state[msg.addr];

--       if (shimElem.syncBit) then
--         ShimWriteCache(msg.dst,Valid,shimElem.data,msg.ts+shimElem.ts-1,msg.addr);  -- Q: not actually modifying cache data? why -1
--         Shims[msg.dst].state[msg.addr].syncBit := false;
--       endif;
--       if Shims[msg.dst].pendingWSC then
--         Shims[msg.dst].pendingWSC := false;
--       endif;


--     case RRESP:
--       -- if (shimElem.state = Invalid) -- CHECK: do we need invalid check? Probably not
--       -- then
--       shimElem := Shims[msg.dst].state[msg.addr];

--       if (shimElem.syncBit) then
--         Shims[msg.dst].state[msg.addr].syncBit := false;
--       endif;
--       ShimWriteCache(msg.dst,Valid,msg.data,msg.ts,msg.addr);

--       UpdateVal(msg.dst, msg.data);				-- Q: for read, right?
--       PopInstr(msg.dst);

--     case FRESP:
--       Assert(Shims[msg.dst].fencePending = true);
--       Shims[msg.dst].fencePending := false;
--       if (!Shims[msg.dst].pendingWSC) then
--         PopInstr(msg.dst); -- CHECK
--       else
--         Shims[msg.dst].pendingWSC := false;
--       endif;
--     else
--       error "Shim received invalid message type!";
--     endswitch;

--   End;



-- SHIM: outgoing messages
-- Write value, or send WRITE to CC
def shimWrite {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (data : Data) (stren : OpStrength)
              (shimVec : ShimType c) (e : Execution c) (net : NETOrdered c) :
              (ShimType c) × (Execution c) × (NETOrdered c) :=
            let newTs : Timestamp := ((shimVec.get shim).state.get addr).ts + 1
            let (shimVec', e') := popInstr shim shimVec e
            let shimVec'' := shimWriteCache shim CacheState.Valid data newTs addr shimVec'

            let shimNode : Node c := Fin.castSucc shim
            let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
            -- let shimNode : Node c := Fin.castLT shim (Nat.lt_of_lt_of_le shim.isLt (Nat.le_succ c.threads))

            let net' := send MType.WRITE shimNode CCNode data addr newTs stren net
            if stren = OpStrength.SC then
                let modShim := {shimVec''.get shim with pendingWSC := true}
                let shimVec''' := shimVec''.set shim modShim
                (shimVec''', e', net')
            else
                (shimVec'', e', net')
--   Procedure ShimWrite(shim: ShimId; addr: Addr; data: Data; stren: OpStrength);
--   var shimElem:ShimElemState;
--   Begin
--     shimElem := Shims[shim].state[addr];
--     PopInstr(shim); -- CHECK Write perform immediately so no need to wait for CC to respond...
--     ShimWriteCache(shim,Valid,data,shimElem.ts+1,addr);
--     Assert (CCOpen()) "ShimWrite - too many messages";
--     Send(WRITE,shim,0,data,addr,shimElem.ts+1,stren);
--     if stren = SC then
--       Shims[shim].pendingWSC := true;
--     endif;
--   End;

--   -- Read value, or send RREQ to CC
def shimRead {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (stren : OpStrength)
    (shimVec : ShimType c) (net : NETOrdered c) (e : Execution c) (o : Output c) :
    (ShimType c) × (NETOrdered c) × (Execution c) × (Output c) :=
    let shimElem := ((shimVec.get shim).state).get addr
    if shimElem.state ≠ CacheState.Valid then
        let shimNode := shim.castSucc
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
        let net' := send MType.RREQ shimNode CCNode shimElem.data addr shimElem.ts stren net
        (shimVec, net', e, o)
    else
        let o' := updateVal shim shimElem.data e shimVec o
        let (shimVec', e') := popInstr shim shimVec e
        (shimVec', net, e', o')
--   Procedure ShimRead(shim: ShimId; addr: Addr; stren: OpStrength);
--   var shimElem:ShimElemState;
--   Begin
--     shimElem := Shims[shim].state[addr];

--     if (shimElem.state != Valid) then
--       Assert (CCOpen()) "ShimRead - too many messages";
--       Send(RREQ,shim,0,shimElem.data,addr,shimElem.ts,stren);
--     else
--       UpdateVal(shim, shimElem.data);
--       PopInstr(shim); -- CHECK
--     endif;
--   End;

--   -- Stop local reads until FRESP received
def shimFence {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (net : NETOrdered c) :
    (ShimType c) × (NETOrdered c) :=
        let modShim := {shimVec.get shim with fencePending := true}
        let shimVec' := shimVec.set shim modShim

        let shimNode := shim.castSucc
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
        let net' := sendFence MType.FREQ shimNode CCNode net
        (shimVec', net')
--   Procedure ShimFence(shim: ShimId);
--   Begin
--     Shims[shim].fencePending := true;
--     SendFence(FREQ,shim,0);
--   End;


  -- CC: process messages -----------------------------------------------------
def CCSendMsgToSharers {c : SystemConfig} (potentialSharer : Nat) (msg : Message c) (net : NETOrdered c) (CC : CCMachine c) : NETOrdered c :=
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
        if h : potentialSharer < c.threads then
            match potentialSharer with
            | 0 =>
                if 0 ≠ msg.src ∧ (CC.cache.get msg.addr).sharers.get 0 = true then
                    send MType.WRITE CCNode 0 msg.data msg.addr (CC.cache.get msg.addr).ts msg.stren net
                else
                    net
            | ps + 1 =>
                let curShim : ShimId c := ⟨ps + 1, h⟩
                let curNode : Node c := curShim.castSucc
                let next := ps
                if curNode ≠ msg.src ∧ (CC.cache.get msg.addr).sharers.get curShim = true then
                    let net' := send MType.WRITE CCNode curNode msg.data msg.addr (CC.cache.get msg.addr).ts msg.stren net
                    CCSendMsgToSharers next msg net' CC
                else
                    CCSendMsgToSharers next msg net CC
        else panic! "potentialSharer passed into CCsendToSharers is not a valid shimId (≥ c.threads)"

def CCAddSrcShimToSharers {c : SystemConfig} (CC : CCMachine c) (msg : Message c) : CCMachine c :=
    if h : msg.src < c.threads.val then
        let sharerVec' := (CC.cache.get msg.addr).sharers.set msg.src true
        let CCElemData' := {(CC.cache.get msg.addr) with sharers := sharerVec'}
        let CCCache' := CC.cache.set msg.addr CCElemData'
        let CC' := {CC with cache := CCCache'}
        CC'
    else
        panic! "source of message to the CC was the CC??"

def CCReceive {c : SystemConfig} (msg : Message c) (CC : CCMachine c) (net : NETOrdered c) : (CCMachine c) × (NETOrdered c) :=
    let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
    match msg.mtype with
    | MType.WRITE =>
        if h : msg.src < c.threads.val then
            -- write data, increment ts
            let CCElemData' : CCElemState c := {(CC.cache.get msg.addr) with data := msg.data, ts := (CC.cache.get msg.addr).ts + 1}
            let CCCache' : CCCache c := CC.cache.set msg.addr CCElemData'
            let CC' : CCMachine c := {CC with cache := CCCache'}

            -- send write to sharers
            let net' := CCSendMsgToSharers (c.threads - 1) msg net CC'

            -- If SC or first write, send write acknowledgement
            let msgSrcShim : ShimId c := ⟨msg.src, h⟩
            let net'' :=
                if msg.stren = OpStrength.SC ∨ (CC'.cache.get msg.addr).sharers.get msgSrcShim = false then
                    send MType.WRITE_ACK CCNode msg.src msg.data msg.addr (CC'.cache.get msg.addr).ts msg.stren net'
                else net'

            -- add src to sharers
            -- let sharerVec' := (CC'.cache.get msg.addr).sharers.set msgSrcShim true
            -- let CCElemData'' := {(CC'.cache.get msg.addr) with sharers := sharerVec'}
            -- let CCCache'' := CC'.cache.set msg.addr CCElemData''
            -- let CC'' := {CC' with cache := CCCache''}
            let CC'' := CCAddSrcShimToSharers CC' msg
            (CC'', net'')
        else
            panic! "source of message to the CC was the CC??"
    | MType.RREQ =>
        let CC' := CCAddSrcShimToSharers CC msg
        let net' := send MType.RRESP CCNode msg.src (CC.cache.get msg.addr).data msg.addr (CC.cache.get msg.addr).ts msg.stren net
        (CC', net')
--     case RREQ:
--       CC.cache[msg.addr].sharers[msg.src] := Y;    -- Add shim to sharers
--       Assert (NetworkOpen()) "CCReceive RREQ - too many messages";
--       Send(RRESP,0,msg.src,CC.cache[msg.addr].data,msg.addr,CC.cache[msg.addr].ts,msg.stren);
    | MType.FREQ => --SendFence(FRESP,0,msg.src);
        let net' := sendFence MType.FRESP CCNode msg.src net
        (CC, net')
    | _ => panic! "CC received message of invalid type"
--   Procedure CCReceive(msg:Message);
--   Begin
--     switch msg.mtype

--     case WRITE:
--       CC.cache[msg.addr].data := msg.data; -- always perform write
--       CC.cache[msg.addr].ts := CC.cache[msg.addr].ts+1;

--       -- send write to sharers
--       Assert (NetworkOpen()) "CCReceive Write - too many messages";
--       for sharer:ShimId do
--         if (sharer != msg.src & CC.cache[msg.addr].sharers[sharer] = Y)
-- 	      then
--           Send(WRITE,0,sharer,msg.data,msg.addr,CC.cache[msg.addr].ts,msg.stren);
-- 	      endif;
--       endfor;

--       -- If SC or first write, send write acknowledgement
--       if msg.stren = SC | (CC.cache[msg.addr].sharers[msg.src] = N) then
--         Send(WRITE_ACK,0,msg.src,msg.data,msg.addr,CC.cache[msg.addr].ts,msg.stren);
--       endif;

--       -- add src to sharers
--       CC.cache[msg.addr].sharers[msg.src] := Y;

--     case RREQ:
--       CC.cache[msg.addr].sharers[msg.src] := Y;    -- Add shim to sharers
--       Assert (NetworkOpen()) "CCReceive RREQ - too many messages";
--       Send(RRESP,0,msg.src,CC.cache[msg.addr].data,msg.addr,CC.cache[msg.addr].ts,msg.stren);

--     case FREQ:
--       Assert (NetworkOpen()) "CCReceive FREQ - too many messages";
--       SendFence(FRESP,0,msg.src);

--     else
--       error "CC received invalid message type!";
--     endswitch
--   End;


def getInstr {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (e : Execution c)
: (Execution c) × (Instr c) :=
    let qInd := (shimVec.get shim).qInd
    let e' :=
        fun (t : ShimId c) =>
            fun (s : Fin c.steps) =>
                if t = shim ∧ s = qInd then {e t s with pend := true}
                else e t s
    (e', e' shim qInd)

  -- Litmus test-specific -----------------------------------------------------

  -- Fetch shim's next litmus test instructions
--   Function GetInstr(shim: ShimId): Instr;
--   var instr: Instr;
--   Begin
--     alias sQ: Shims[shim].queue.Queue do
--     alias QInd: Shims[shim].queue.QueueInd do
--     alias QCnt: Shims[shim].queue.QueueCnt do
--     undefine instr;

--     if QInd = QCnt
--     then
--       return instr;
--     endif;

--     if !isundefined(sQ[QInd].access)
--     then
--       sQ[QInd].pend := true;
--       return sQ[QInd];
--     endif;

--     endalias;
--     endalias;
--     endalias;
--   End;

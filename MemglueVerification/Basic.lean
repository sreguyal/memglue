import Mathlib
-- CONSTANTS -----------------------------
-- def ShimCount : ℕ := 2
-- def DataCount : ℕ := 4
-- def NetMax : ℕ := 10
-- def AddrCount : ℕ := 2
-- def MaxTimestamp : ℕ := 100
-- def InstrCount : ℕ := 2
structure SystemConfig where
    threads     : Nat
    steps       : Nat
    addrCount   : Nat
deriving Inhabited


-- TYPES -----------------------------------------
abbrev ShimId (c : SystemConfig) : Type := Fin (c.threads)
abbrev Addr (c : SystemConfig) : Type := Fin (c.addrCount)
-- def Data : Type := Fin (DataCount + 1)
abbrev Data : Type := Nat
-- def Timestamp : Type := Fin (MaxTimestamp + 1)
abbrev Timestamp : Type := Nat
abbrev Node (c : SystemConfig) : Type := Fin (c.threads + 1)
-- ShimId: 1..ShimCount;       	-- For indexing into list of shims
-- Addr: 0..AddrCount-1;		      -- For indexing into cache
-- Data: 0..DataCount;
-- Timestamp: 0..MaxTimestamp;
-- Node: 0..ShimCount;         	-- This represents the CC plus the shims: CC = 0, Shims = 1..ShimCount+1

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
structure Message (c : SystemConfig) : Type where
    mtype : MType
    src : Node c
    dst : Node c
    data :  Data
    addr : Option (Addr c)
    ts : Timestamp
    stren : OpStrength

-- matrix one row of messages per node (CC + shims)
-- def NETOrdered : Type := Matrix Node (Fin NetMax) Message
def NETOrdered (c : SystemConfig) : Type := Vector (List (Message c)) (c.threads + 1)
-- def NETOrderedCount : Type := Vector ℕ (ShimCount + 1)
-- NETOrdered: array[Node] of array[0..NetMax-1] of Message;
-- NETOrderedCount: array[Node] of 0..NetMax;
-- NETUnordered: array[Node] of multiset[NetMax] of Message;

inductive CacheState : Type where
    | Invalid | Valid

structure ShimElemState : Type where
    state : CacheState
    data : Data
    ts : Timestamp
    syncBit : Bool

structure CCElemState (c : SystemConfig) : Type where
    data : Data
    ts : Timestamp
    sharers : Vector Bool c.threads

def ShimCache (c : SystemConfig) : Type := Vector ShimElemState c.addrCount
def CCCache (c : SystemConfig) : Type := Vector (CCElemState c) c.addrCount

-- Litmus test specific---------
inductive PermissionType : Type where
    | load
    | store
    | fence
    | none
deriving DecidableEq

structure Instr (c : SystemConfig) : Type where
    access : PermissionType       -- may not need this
    stren : OpStrength
    addr : Addr c
    data : Data      -- Value store for read operation performed */
    pend : Bool

-- structure FifoQueue : Type where                      -- each shim has a queue of litmust test instructions to perform
--     Queue: Vector Instr InstrCount -- array[0..2] of Instr;
--     QueueInd: Fin (InstrCount + 2) -- 0..2+1;
--     QueueCnt: Fin (InstrCount + 2) -- 0..2+1;

---------------------------------
abbrev QInd (c : SystemConfig) : Type := Fin c.steps
abbrev QCnt (c : SystemConfig) : Type := Fin c.steps
structure Shim (c : SystemConfig) : Type where
    state : ShimCache c
    active : Bool   -- active = still needs to execute litmus tests instructions
    pendingWSC : Bool
    fencePending : Bool
    -- queue : FifoQueue   -- queue of litmus test instructions to be performed. replaced with tracesets
    qInd : QInd c
    qCnt : QCnt c

structure CCMachine (c : SystemConfig) : Type where
    cache : CCCache c

-- NOTE: this is zero indexed unlike in murphi model....... change?
def ShimType (c : SystemConfig) : Type := Vector (Shim c) c.threads    -- array[ShimId] of Shim;



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
-- #check Execution 3 2
-- The output trace generated by the cache coherence protocol.
def Output (c : SystemConfig) := TraceSet (Option Nat) c.threads c.steps
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
                              data := 0,
                              addr := none,
                              ts := 0,
                              stren := OpStrength.RLX,
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
    if h1 : msg.dst < c.threads then
        let curShim : ShimId c := ⟨msg.dst, h1⟩
        let curShimCache : ShimCache c := (shimVec.get curShim).state

        match msg.mtype, msg.addr with
            | MType.WRITE, some addr =>
                let shimElem : ShimElemState := curShimCache.get addr
                if msg.ts > shimElem.ts then
                    (shimWriteCache curShim CacheState.Valid msg.data msg.ts addr shimVec, e, o)
                else
                    (shimIncrTS curShim addr shimVec, e, o)
            | MType.WRITE_ACK, some addr =>
                let shimElem : ShimElemState := curShimCache.get addr
                if shimElem.syncBit = true then
                    let modShims : ShimType c := ShimWriteCache curShim CacheState.Valid shimElem.data msg.ts+shimElem.ts-1 addr
                    -- TODO
            -- shimElem := Shims[msg.dst].state[msg.addr];

        --       if (shimElem.syncBit) then
        --         ShimWriteCache(msg.dst,Valid,shimElem.data,msg.ts+shimElem.ts-1,msg.addr);  -- Q: not actually modifying cache data? why -1
        --         Shims[msg.dst].state[msg.addr].syncBit := false;
        --       endif;
        --       if Shims[msg.dst].pendingWSC then
        --         Shims[msg.dst].pendingWSC := false;
        --       endif;
            | MType.RRESP, some addr => (shimVec, e, o)
            | MType.FRESP, some addr => (shimVec, e, o)
            | _, _ => (shimVec, e, o)
    else
        (shimVec, e, o)             -- no change in weird error cases (msg.dst = c.threads means CC but this is shimReceive... shouldn't happen)

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

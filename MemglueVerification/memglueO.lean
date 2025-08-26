import Mathlib
set_option diagnostics true

universe u
instance {α : Type u} {n : ℕ} : GetElem (Vector α n) ℕ α (fun _ i => i < n) where
  getElem v i h := v.get ⟨i, h⟩
instance {α : Type u} : GetElem (List α) ℕ α (fun v i => i < v.length) where
  getElem v i h := v.get ⟨i, h⟩

-- inductive neList (α : Type) : Type where
-- | singleton (a : α) : neList α
-- | cons (a : α) (l : neList α) : neList α
-- deriving Repr, Inhabited
-- namespace neList
-- def toList {α : Type} : neList α → List α
-- | singleton a => [a]
-- | cons a l => a :: l.toList
-- instance {α : Type} : Coe (neList α) (List α) where
--   coe := toList
-- end neList

structure SystemConfig where
    threads     : PNat          -- positive Nat: 1, 2, 3, ...
    -- steps       : Vector PNat threads  -- steps in each thread
    addrCount   : PNat
-- instance : Inhabited (SystemConfig) where default := {threads := 2, steps := 2, addrCount := 1}
instance : Inhabited (SystemConfig) where default := {threads := 2, addrCount := 2}

-- TYPES -----------------------------------------
abbrev ShimId (c : SystemConfig) : Type := Fin (c.threads)
abbrev Addr (c : SystemConfig) : Type := Fin (c.addrCount)
abbrev Data : Type := Nat
abbrev Timestamp : Type := Nat
abbrev Node (c : SystemConfig) : Type := Fin (c.threads + 1)

instance (c : SystemConfig) : Inhabited (ShimId c) where default := Fin.ofNat c.threads 0
instance (c : SystemConfig) : Inhabited (Addr c) where default := Fin.ofNat c.addrCount 0
instance (c : SystemConfig) : Inhabited (Node c) where default := Fin.ofNat (c.threads + 1) 0
#eval (default : ShimId (default : SystemConfig))

inductive MType : Type where
    | WRITE
    | WRITE_ACK
    | RREQ
    | EVICT
    | FREQ
    | RRESP
    | FRESP
deriving Repr
--TODO proof that na < rlx
inductive OpStrength : Type where
    | RLX
    | REL
    | ACQ
    | SC
deriving Inhabited, DecidableEq, Repr

structure Message (c : SystemConfig) : Type where
    mtype : MType := MType.WRITE
    src : Node c := 0
    dst : Node c := 0
    data :  Data := 0
    addr : Addr c := 0
    ts : Timestamp := 0
    stren : OpStrength := OpStrength.RLX
    id : Nat := 0               -- ids are assigned to each message received at a node in increasing order so that we can track orderedness of network
deriving Repr   --, DecidableEq

instance (c : SystemConfig) : Inhabited (Message c) where
    default := {
        mtype := MType.WRITE
        src := 0
        dst := 0
        data := 0
        addr := 0
        ts := 0
        stren := OpStrength.RLX
        id := 0
    }


abbrev MessageIds (c : SystemConfig) : Type := Vector Nat (c.threads + 1)
-- matrix one row of messages per node (CC + shims)
abbrev NETOrdered (c : SystemConfig) : Type := Vector (List (Message c)) (c.threads + 1)
instance (c : SystemConfig) : Inhabited (NETOrdered c) where default := Vector.replicate (c.threads + 1) (List.nil)
instance (c : SystemConfig) [Repr (List (Message c))] : Repr (NETOrdered c) where
  reprPrec net _ := repr (net.toList)
-- instance (c : SystemConfig) : Inhabited (NETOrdered c) where default := Vector.replicate (c.threads + 1) (List.singleton (default : (Message c)))

inductive CacheState : Type where
    | Invalid | Valid -- put Valid first for store buffer test
deriving Inhabited, DecidableEq, Repr
#eval (default : CacheState)

structure ShimElemState : Type where
    state : CacheState
    data : Data
    ts : Timestamp
    syncBit : Bool
deriving Inhabited, Repr
instance : Inhabited ShimElemState where
    default := {
        state := (default : CacheState)
        data := (default : Data)
        ts := (default : Timestamp)
        syncBit := true
    }

structure CCElemState (c : SystemConfig) : Type where
    data : Data
    ts : Timestamp
    sharers : Vector Bool c.threads
deriving Inhabited, Repr
instance (c : SystemConfig) : Inhabited (CCElemState c) where
    default := {
        data := default
        ts := default
        sharers := Vector.replicate c.threads false -- make this true for store buffer test
        }

abbrev ShimCache (c : SystemConfig) : Type := Vector ShimElemState c.addrCount
instance (c : SystemConfig) : Inhabited (ShimCache c) where default := Vector.replicate c.addrCount (default : ShimElemState)
instance (c : SystemConfig) [Repr ShimElemState] : Repr (ShimCache c) where
  reprPrec cache _ := repr (cache.toList)

abbrev CCCache (c : SystemConfig) : Type := Vector (CCElemState c) c.addrCount
instance (c : SystemConfig) : Inhabited (CCCache c) where default := Vector.replicate c.addrCount (default : CCElemState c)
instance (c : SystemConfig) [Repr (CCElemState c)] : Repr (CCCache c) where
    reprPrec cache _ := repr (cache.toList)
-- Litmus test specific---------
inductive PermissionType : Type where
    | load
    | store
    | fence
deriving DecidableEq, Inhabited, Repr
#eval (default : PermissionType)

structure Instr (c : SystemConfig) : Type where
    access : PermissionType
    stren : OpStrength
    addr : Addr c
    data : Data      -- (not) Value store for read operation performed */
    pend : Bool
deriving Inhabited, Repr

structure neList (α : Type) : Type where
    list : List α
    nonempty : list ≠ []
deriving Repr
instance {c : SystemConfig} : Inhabited (neList (Instr c)) where
    default := {list := [default], nonempty := by simp}

def test_neList : neList Nat := {list := [1,2,3], nonempty := by simp}
example : test_neList.list.length > 0 := by
    unfold test_neList
    simp
---------------------------------

abbrev QInd : Type := Nat
-- abbrev QCnt (c : SystemConfig) (shim : ShimId c) : Type := Fin (c.steps[(shim : Nat)] + 1)
-- instance (c : SystemConfig) (shim : ShimId c) : Inhabited (QInd c shim) where default := Fin.ofNat (c.steps[(shim : Nat)]) 0
-- instance (c : SystemConfig) (shim : ShimId c) : Inhabited (QCnt c shim) where default := Fin.ofNat (c.steps[(shim : Nat)] + 1) (c.steps[(shim : Nat)])
#eval (default : QInd)
-- #eval (default : QCnt default default)
structure Shim (c : SystemConfig) : Type where
    state : ShimCache c
    active : Bool   -- active = still needs to execute litmus tests instructions
    pendingWSC : Bool
    fencePending : Bool
    qInd : QInd
    -- qCnt : QCnt c
deriving Inhabited, Repr
instance (c : SystemConfig) : Inhabited (Shim c) where
    default := {
        state := (default : ShimCache c)
        active := true
        pendingWSC := false
        fencePending := false
        qInd := 0
        -- qCnt := ⟨c.steps, Nat.lt_succ_self c.steps⟩
    }
-- #eval (default : QInd (default : SystemConfig))
#eval (default : Shim (default : SystemConfig))

structure CCMachine (c : SystemConfig) : Type where
    cache : CCCache c
deriving Inhabited, Repr



abbrev ShimType (c : SystemConfig) : Type := Vector (Shim c) c.threads
instance (c : SystemConfig) : Inhabited (ShimType c) where default := Vector.replicate c.threads (default : Shim c)
instance (c : SystemConfig) [Repr (Shim c)] : Repr (ShimType c) where
  reprPrec shims _ := repr (shims.toList)
#eval (default : ShimType (default : SystemConfig))


-- A single trace is a sequence of operations.
-- def Trace (α : Type u) (steps : Nat) := Fin steps → α
-- todo change execution to vector of Traces
-- Multi-threaded traces are a sequence of traces.
-- def TraceSet (α : Type u) (threads : Nat) (steps : Nat) := Fin threads → Trace α steps
-- #check TraceSet Instr 3 2

-- The execution trace generated by the program.
abbrev Execution (c : SystemConfig) : Type := Vector (neList (Instr c)) c.threads
instance {c : SystemConfig} : Inhabited (Execution c) where
    default := Vector.replicate c.threads (default : neList (Instr c))
instance (c : SystemConfig) [Repr (neList (Instr c))] : Repr (Execution c) where
  reprPrec exec _ := repr (exec.toList)
-- def Execution (c : SystemConfig) := TraceSet (Instr c) c.threads c.steps
-- instance (c : SystemConfig) : Inhabited (Execution c) where default := fun _ _ => (default : Instr c)
-- def executionToList {c : SystemConfig} (e : Execution c) : List (List (Instr c)) :=
--   (List.finRange c.threads.val).map fun t =>
--     (List.finRange c.steps.val).map fun s => e t s
-- instance {c : SystemConfig} [Repr (Instr c)] : Repr (Execution c) where
--   reprPrec e _ :=
--     repr (executionToList e)

structure IncState (c : SystemConfig) where
    cc : CCMachine c
    shimVec : ShimType c
    net : NETOrdered c
    msgIds : MessageIds c
    execution : Execution c
    -- output : Output c
    done : Bool
deriving Inhabited, Repr



/--
1. Writes to the same address are totally ordered.
2. Reads return the most recent write in that order.
3. Writes become visible to all processors atomically.
-/
structure Coherence {c : SystemConfig} (e e': Execution c) : Prop where
    writes_total_order : False -- Placeholder for actual definition
    -- ∀ writes w1, w2. ((∀ threads w1 < w2) or (∀ threads w1 > w2))??
    reads_return_last_write : False -- Placeholder for actual definition
    write_atomicity : False -- Placeholder for actual definition


-- def protocol {c : SystemConfig} (e : Execution c) : Execution c :=
--     sorry -- Implementation of the protocol goes here

-- theorem protocol_respects_coherence :
--     ∀ {c : SystemConfig} (e e': Execution c), protocol e = e' → Coherence e e' := by sorry


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
    let oldList : List (Message c) := net[msg.dst]
    let updatedList : List (Message c) := oldList.append [msg]
    let updatedNet : NETOrdered c := net.set msg.dst.val updatedList
    updatedNet

#eval (default : NETOrdered (default : SystemConfig))
#eval netWithAddedMsg ({(default : Message (default : SystemConfig)) with mtype := MType.WRITE_ACK, src := 0, ts := 10000, stren := OpStrength.SC, dst := 1}) (default : NETOrdered (default : SystemConfig))

def send {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c)
         (data' : Data) (addr' : Addr c) (ts' : Timestamp) (stren' : OpStrength)
         (net : NETOrdered c) (msgIds : MessageIds c)
         : NETOrdered c × MessageIds c :=

        let msg : (Message c) := {mtype := mtype', src := src', dst := dst', data := data', addr := addr', ts := ts', stren := stren', id := msgIds[dst']}
        let msgIds' := msgIds.set dst' (msgIds[dst'] + 1)
        (netWithAddedMsg msg net, msgIds')

-- def res := send MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) 10 0 100 OpStrength.ACQ default (default : NETOrdered (default : SystemConfig))
-- #eval send MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) 10 0 100 OpStrength.ACQ res.1 res.2

def sendFence {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c) (net : NETOrdered c) (msgIds : MessageIds c)
: NETOrdered c × MessageIds c:=
    let msg : (Message c) := {(default : Message c) with mtype := mtype', src := src', dst := dst', id := msgIds[dst']}
    let msgIds' := msgIds.set dst' (msgIds[dst'] + 1)
    (netWithAddedMsg msg net, msgIds')

-- def res := sendFence MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) default default
-- #eval sendFence MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) res.1 res.2

-- def testnet := sendFence MType.EVICT (0 : Node (default : SystemConfig)) (1 : Node (default : SystemConfig)) (default : NETOrdered (default : SystemConfig))
-- #eval testnet

def popMessage {c : SystemConfig} (dst : Node c) (net : NETOrdered c) : NETOrdered c :=
    let oldList : List (Message c) := net[dst]
    let updatedList : List (Message c) := oldList.tail
    let updatedNet : NETOrdered c := net.set dst.val updatedList
    updatedNet

-- #eval popMessage (2 : Node (default : SystemConfig)) (default : NETOrdered (default : SystemConfig))
-- #eval popMessage (1 : Node (default : SystemConfig)) testnet

-- Update output of litmus test load
def updateVal {c : SystemConfig} (targetThread : ShimId c) (data : Data)
    (e : Execution c) (shimVec : ShimType c)
    : Execution c :=
    let targetStep : QInd := (shimVec[targetThread]).qInd
    let stepCount := e[targetThread].list.length
    -- let stepCount := (shimVec[targetThread]).qCnt
    -- qCnt?
    if targetStep < stepCount then
        -- update output
        let newInstr : Instr c := {e[targetThread].list[targetStep]! with data := data}
        let newList : List (Instr c) := e[targetThread].list.set targetStep newInstr
        let e' := e.set targetThread {list := newList, nonempty := (by unfold newList; simp; exact e[↑targetThread].nonempty)}
        e'
        -- fun (t : ShimId c) =>
        --     fun (s : Fin c.steps) =>
        --         if t = targetThread ∧ s = targetStep then
        --             {e t s with data := data}
        --         else e t s
    else
        -- keep same
        e

-- def test {c : SystemConfig} (targetThread : ShimId c) (data : Data)
--     (e : Execution c) (shimVec : ShimType c) (o : Output c)
--     : Bool :=
--     let targetStep : QInd c := (shimVec.get targetThread).qInd
--     let cntStep := (shimVec.get targetThread).qEnd
--     -- qCnt?
--     (targetStep <= cntStep) ∧ ((e targetThread targetStep).access ≠ PermissionType.none)
-- #eval test (default : ShimId (default : SystemConfig)) 10 (default : Execution (default : SystemConfig)) ((default : ShimType (default : SystemConfig)).set 0 {(default : Shim (default : SystemConfig)) with qInd := (1 : QInd (default : SystemConfig)), qEnd := (1 : QEnd default)}) (default : Output (default : SystemConfig))

#eval (default : ShimType (default))
-- example that does update


-- Remove litmus test instruction
def popInstr {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (e : Execution c)
    : (ShimType c) × (Execution c) :=

    let qInd := (shimVec[shim]).qInd
    let qCnt := e[shim].list.length
    -- let qCnt := (shimVec[shim]).qCnt
    -- let newExec : Execution c :=       -- still a function but for that thread instruction, pend = false
    --     fun (t : ShimId c) =>
    --         fun (s : Fin c.steps) =>
    --             if t = shim ∧ s = qInd then {e t s with pend := false}
    --             else e t s
    let instr' : Instr c := {e[shim].list[qInd]! with pend := false}
    let list' : List (Instr c) := e[shim].list.set qInd instr'
    let e' : Execution c := e.set shim {list := list', nonempty := (by unfold list'; simp; exact e[↑shim].nonempty)}

    let nextQInd := qInd + 1
    if h : nextQInd < e'[shim].list.length then
        let newActiveState := if nextQInd = qCnt then false else (shimVec[shim].active)
        let shim' := {shimVec[shim] with qInd := nextQInd, active := newActiveState}
        let shimVec' := shimVec.set shim shim'

        (shimVec', e')
    else  -- finished last instruction → don't increment qInd out of bounds, just set shim inactive
        let shim' := {shimVec[shim] with active := false}
        let shimVec' := shimVec.set shim shim'

        (shimVec', e')
    --todo fix thiss
    -- if h : qInd + 1 < c.steps then
    --     -- qInd not about to go out of range → can increment qInd and change active state as in murphi
    --     let nextQInd : QInd c := ⟨qInd.val + 1, h⟩
    --     -- CHECK: changed nextQInd = qCnt to nextQInd > qEnd
    --     let shimInactive : Prop := nextQInd.val = qCnt.val ∨ (e shim nextQInd).access = PermissionType.none
    --     let newActiveState : Bool := if shimInactive then false else (shimVec[shim]).active
    --     let newShim : Shim c := {(shimVec[shim]) with qInd := nextQInd, active := newActiveState}
    --     let newShimVec : ShimType c := shimVec.set shim newShim

    --     (newShimVec, newExec)
    -- else
    --     -- qInd + 1 is out of range, i.e. after pop, shim should def be inactive
    --     let newShim : Shim c := {(shimVec[shim]) with active := false}
    --     let newShimVec : ShimType c := shimVec.set shim newShim

    --     (newShimVec, newExec)

#eval popInstr (1:ShimId default) (default : ShimType default) (default : Execution default)

-- Shim-specific ------------------------------------------------------------
def shimWriteCache {c : SystemConfig} (shim : ShimId c) (state' : CacheState)
    (data' : Data) (ts' : Timestamp) (addr : Addr c) (shimVec : ShimType c)
    : ShimType c :=
    let curShimCache : ShimCache c := (shimVec[shim]).state
    let newCacheState : ShimCache c := curShimCache.set addr {curShimCache[addr] with state := state', data := data', ts := ts'}
    let newShim := {shimVec[shim] with state := newCacheState}
    let newShimVec := shimVec.set shim newShim

    newShimVec

#eval shimWriteCache (1 : ShimId default) (CacheState.Valid) (10 : Data) (20 : Timestamp) (0 : Addr default) (default : ShimType default)

def shimIncrTS {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (shimVec : ShimType c) : ShimType c :=
    let curShimCache : ShimCache c := (shimVec[shim]).state
    let newCacheState : ShimCache c := curShimCache.set addr {curShimCache[addr] with ts := (curShimCache[addr]).ts + 1}
    let newShim := {shimVec[shim] with state := newCacheState}
    let newShimVec := shimVec.set shim newShim

    newShimVec

def ts1shimvec := shimIncrTS (0 : ShimId default) (0 : Addr default) (default : ShimType default)
#eval shimIncrTS (0 : ShimId default) (0 : Addr default) ts1shimvec

-- -- SHIM: incoming messages
def shimReceive {c : SystemConfig} (shim : ShimId c) (msg : Message c)
                (shimVec : ShimType c) (e : Execution c)
                : (ShimType c) × (Execution c) :=
    if h1 : msg.dst < c.threads.val then    -- msg.dst is in fact a shim
        let curShim : ShimId c := shim      --⟨msg.dst, h1⟩
        let curShimCache : ShimCache c := (shimVec[curShim]).state
        let addr := msg.addr

        match msg.mtype with
            | MType.WRITE =>
                let shimElem : ShimElemState := curShimCache[addr]
                if msg.ts > shimElem.ts then
                    (shimWriteCache curShim CacheState.Valid msg.data msg.ts addr shimVec, e)
                else
                    (shimIncrTS curShim addr shimVec, e)
            | MType.WRITE_ACK =>
                let shimElem : ShimElemState := curShimCache[addr]
                if shimElem.syncBit = true then
                    let newTs : Timestamp := msg.ts+shimElem.ts-1
                    let modShims : ShimType c := shimWriteCache curShim CacheState.Valid shimElem.data newTs addr shimVec
                    let modShimElem : ShimElemState := {(modShims[curShim]).state[addr] with syncBit := false}
                    let modShimCache : ShimCache c := (modShims[curShim]).state.set addr modShimElem
                    let modShim : Shim c := {(modShims[curShim]) with state := modShimCache, pendingWSC := false}

                    let newShimVec : ShimType c := modShims.set curShim modShim
                    (newShimVec, e)
                else
                    let modShim : Shim c := {(shimVec[curShim]) with pendingWSC := false}
                    let newShimVec : ShimType c := shimVec.set curShim modShim
                    (newShimVec, e)
            | MType.RRESP =>
                let modShims : ShimType c := shimWriteCache curShim CacheState.Valid msg.data msg.ts addr shimVec
                let modShimElem : ShimElemState := {(modShims[curShim]).state[addr] with syncBit := false}
                let modShimCache : ShimCache c := (modShims[curShim]).state.set addr modShimElem
                let modShim : Shim c := {(modShims[curShim]) with state := modShimCache}
                let modShims' : ShimType c := modShims.set curShim modShim

                let e' : Execution c := updateVal curShim msg.data e shimVec
                let (newShimVec, e'') := popInstr curShim modShims' e'
                (newShimVec, e'')
            | MType.FRESP =>
                let modShim : Shim c := {(shimVec[curShim]) with fencePending := false}
                let modShimVec : ShimType c := shimVec.set curShim modShim

                if (shimVec[curShim]).pendingWSC = false then
                    let (newShimVec, newExec) := popInstr curShim modShimVec e
                    (newShimVec, newExec)
                else
                    let modShim' := {(shimVec[curShim]) with pendingWSC := false}
                    let newShimVec : ShimType c := modShimVec.set curShim modShim'
                    (newShimVec, e)
            | _ => panic! "message with wrong message type was passed into ShimReceive"
    else
        panic! "message with destination that was not a shim was passed into ShimReceive (was CC or some other random dst value)"

def shimReceiveAndPopMsg {c : SystemConfig} (shim : ShimId c) (state : IncState c) : IncState c :=
    let shimNode : Node c := shim.castSucc
    let msg := (state.net[shimNode]).head!
    let (shimVec', e') := shimReceive shim msg state.shimVec state.execution
    let state' := {state with shimVec := shimVec', execution := e'}

    let net' := popMessage shimNode state'.net
    let state'' := {state' with net := net'}
    state''


-- SHIM: outgoing messages
-- Write value, or send WRITE to CC
def shimWrite {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (data : Data) (stren : OpStrength)
              (shimVec : ShimType c) (e : Execution c) (net : NETOrdered c) (msgIds : MessageIds c):
              (ShimType c) × (Execution c) × (NETOrdered c) × (MessageIds c) :=
            let newTs : Timestamp := ((shimVec[shim].state)[addr]).ts + 1
            let (shimVec', e') := popInstr shim shimVec e
            let shimVec'' := shimWriteCache shim CacheState.Valid data newTs addr shimVec'

            let shimNode : Node c := Fin.castSucc shim
            let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
            -- let shimNode : Node c := Fin.castLT shim (Nat.lt_of_lt_of_le shim.isLt (Nat.le_succ c.threads))

            let (net', msgIds') := send MType.WRITE shimNode CCNode data addr newTs stren net msgIds
            if stren = OpStrength.SC then
                let modShim := {shimVec''[shim] with pendingWSC := true}
                let shimVec''' := shimVec''.set shim modShim
                (shimVec''', e', net', msgIds')
            else
                (shimVec'', e', net', msgIds')
-- mp
-- Read value, or send RREQ to CC
def shimRead {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (stren : OpStrength)
    (shimVec : ShimType c) (net : NETOrdered c) (e : Execution c) (msgIds : MessageIds c) :
    (ShimType c) × (NETOrdered c) × (Execution c) × (MessageIds c):=
    let shimElem := ((shimVec[shim]).state)[addr]
    if shimElem.state ≠ CacheState.Valid then
        let shimNode := shim.castSucc
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
        let (net', msgIds') := send MType.RREQ shimNode CCNode shimElem.data addr shimElem.ts stren net msgIds
        (shimVec, net', e, msgIds')
    else
        let e' := updateVal shim shimElem.data e shimVec
        let (shimVec', e'') := popInstr shim shimVec e'
        (shimVec', net, e'', msgIds)

--   -- Stop local reads until FRESP received
def shimFence {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (net : NETOrdered c) (msgIds : MessageIds c) :
    (ShimType c) × (NETOrdered c) × (MessageIds c) :=
        let modShim := {shimVec[shim] with fencePending := true}
        let shimVec' := shimVec.set shim modShim

        let shimNode := shim.castSucc
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
        let (net', msgIds') := sendFence MType.FREQ shimNode CCNode net msgIds
        (shimVec', net', msgIds')

  -- CC: process messages -----------------------------------------------------
def foldSharers {c : SystemConfig} (sharers : List (Node c)) (msg : Message c) (net : NETOrdered c) (msgIds : MessageIds c) (CC : CCMachine c)
: NETOrdered c × MessageIds c :=
    let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)

    List.foldl
        (fun (net_msgIds : NETOrdered c × MessageIds c) (shim : Node c) =>
        send MType.WRITE CCNode shim msg.data msg.addr CC.cache[msg.addr].ts msg.stren
            net_msgIds.1 net_msgIds.2
        )
        (net, msgIds)
        sharers

def CCSendMsgToSharers {c : SystemConfig} (msg : Message c) (net : NETOrdered c) (msgIds : MessageIds c) (CC : CCMachine c)
: NETOrdered c × MessageIds c :=

    let allNodes : List (Node c) := (List.finRange (c.threads + 1))
    let sharers : List (Node c) := allNodes.filter (fun shim =>
        (shim : Nat) ≠ (msg.src : Nat) ∧ CC.cache[msg.addr].sharers[shim]! = true ∧
        (shim : Nat) ≠ (c.threads : Nat)
    )

    foldSharers sharers msg net msgIds CC





    -- Fin.foldl c.threads
    --     (
    --         fun (net_msgIds : NETOrdered c × MessageIds c) (shim : ShimId c) =>
    --             if (shim : Nat) ≠ (msg.src : Nat) ∧ (CC.cache[msg.addr].sharers[shim] = true) then
    --                 send MType.WRITE CCNode shim.castSucc msg.data msg.addr CC.cache[msg.addr].ts msg.stren net_msgIds.1 net_msgIds.2
    --             else
    --                 net_msgIds
    --     )
    --     (net, msgIds)

-- def CCSendMsgToSharers {c : SystemConfig} (potentialSharer : Nat) (msg : Message c) (net : NETOrdered c) (msgIds : MessageIds c) (CC : CCMachine c)
-- : NETOrdered c × MessageIds c:=
--         let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
--         if h : potentialSharer < c.threads then
--             -- let shim : ShimId c := ⟨potentialSharer, h⟩
--             -- let node := shim.castSucc

--             -- if node ≠ msg.src ∧ (CC.cache[msg.addr]).sharers[shim] = true then
--             -- match potentialSharer with
--             -- | 0 =>


--             match potentialSharer with
--             | 0 =>
--                 if 0 ≠ msg.src ∧ (CC.cache[msg.addr]).sharers[0] = true then
--                     send MType.WRITE CCNode 0 msg.data msg.addr (CC.cache[msg.addr]).ts msg.stren net msgIds
--                 else
--                     (net, msgIds)
--             | ps + 1 =>
--                 let curShim : ShimId c := ⟨ps + 1, h⟩
--                 let curNode : Node c := curShim.castSucc
--                 let next := ps
--                 if curNode ≠ msg.src ∧ (CC.cache[msg.addr]).sharers[curShim] = true then
--                     let (net', msgIds') := send MType.WRITE CCNode curNode msg.data msg.addr (CC.cache[msg.addr]).ts msg.stren net msgIds
--                     CCSendMsgToSharers next msg net' msgIds' CC
--                 else
--                     CCSendMsgToSharers next msg net msgIds CC
--         else panic! "potentialSharer passed into CCsendToSharers is not a valid shimId (≥ c.threads)"

#eval (default : NETOrdered default)
def cceveryonesharers := {(default : CCMachine default) with cache := (default : CCCache default).set 0 {(default : CCElemState default ) with sharers := Vector.mk #[true, true] (by decide)}}
#eval cceveryonesharers
#eval CCSendMsgToSharers {(default : Message default) with src := 2} (default : NETOrdered default) default cceveryonesharers
#eval (cceveryonesharers.cache[0]).sharers[0] = true ∧ 0 ≠ (default : Message default).src

def CCAddSrcShimToSharers {c : SystemConfig} (CC : CCMachine c) (msg : Message c) : CCMachine c :=
    if h : msg.src < c.threads.val then
        let sharerVec' := (CC.cache[msg.addr]).sharers.set msg.src true
        let CCElemData' := {(CC.cache[msg.addr]) with sharers := sharerVec'}
        let CCCache' := CC.cache.set msg.addr CCElemData'
        let CC' := {CC with cache := CCCache'}
        CC'
    else
        panic! "source of message to the CC was the CC??"

def CCReceive {c : SystemConfig} (msg : Message c) (CC : CCMachine c) (net : NETOrdered c) (msgIds : MessageIds c)
: (CCMachine c) × (NETOrdered c) × (MessageIds c) :=
    let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
    match msg.mtype with
    | MType.WRITE =>
        if h : msg.src < c.threads.val then
            -- write data, increment ts
            let CCElemData' : CCElemState c := {(CC.cache[msg.addr]) with data := msg.data, ts := (CC.cache[msg.addr]).ts + 1}
            let CCCache' : CCCache c := CC.cache.set msg.addr CCElemData'
            let CC' : CCMachine c := {CC with cache := CCCache'}

            -- send write to sharers
            let (net', msgIds') := CCSendMsgToSharers msg net msgIds CC'

            -- If SC or first write, send write acknowledgement
            let msgSrcShim : ShimId c := ⟨msg.src, h⟩
            let (net'', msgIds'') :=
                if msg.stren = OpStrength.SC ∨ (CC'.cache[msg.addr]).sharers[msgSrcShim] = false then
                    send MType.WRITE_ACK CCNode msg.src msg.data msg.addr (CC'.cache[msg.addr]).ts msg.stren net' msgIds'
                else (net', msgIds')

            -- add src to sharers
            -- let sharerVec' := (CC'.cache.get msg.addr).sharers.set msgSrcShim true
            -- let CCElemData'' := {(CC'.cache.get msg.addr) with sharers := sharerVec'}
            -- let CCCache'' := CC'.cache.set msg.addr CCElemData''
            -- let CC'' := {CC' with cache := CCCache''}
            let CC'' := CCAddSrcShimToSharers CC' msg
            (CC'', net'', msgIds'')
        else
            panic! "source of message to the CC was the CC??"
    | MType.RREQ =>
        let CC' := CCAddSrcShimToSharers CC msg
        let (net', msgIds') := send MType.RRESP CCNode msg.src (CC.cache[msg.addr]).data msg.addr (CC.cache[msg.addr]).ts msg.stren net msgIds
        (CC', net', msgIds')
    | MType.FREQ => --SendFence(FRESP,0,msg.src);
        let (net', msgIds') := sendFence MType.FRESP CCNode msg.src net msgIds
        (CC, net', msgIds')
    | _ => panic! "CC received message of invalid type"

def CCReceiveAndPopMsg {c : SystemConfig} (state : IncState c) : IncState c :=
    let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩
    let msg := (state.net[CCNode]).head!
    let (cc', net', msgIds') := CCReceive msg state.cc state.net state.msgIds
    let state' := {state with cc := cc', net := net', msgIds := msgIds'}

    let net'' := popMessage CCNode state'.net
    let state'' := {state' with net := net''}
    state''

def getInstr {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (e : Execution c)
: (Execution c) × (Instr c) :=
    let qInd := (shimVec[shim]).qInd

    let instr' := {e[shim].list[qInd]! with pend := true}
    let list' := e[shim].list.set qInd instr'
    let e' := e.set shim {list := list', nonempty := (by unfold list'; simp; exact e[↑shim].nonempty)}
    -- let e' :=
    --     fun (t : ShimId c) =>
    --         fun (s : Fin c.steps) =>
    --             if t = shim ∧ s = qInd then {e t s with pend := true}
    --             else e t s
    (e', e'[shim].list[qInd]!)

-- Call the appropriate functions given an instruction
def getAndIssueInstr {c : SystemConfig} (shim : ShimId c) (state : IncState c) : IncState c :=
    let (e', instr) := getInstr shim state.shimVec state.execution
    let state' := {state with execution := e'}

    match instr.access with
    | PermissionType.load =>
        let (shimVec', net', e'', msgIds') := shimRead shim instr.addr instr.stren state'.shimVec state'.net state'.execution state'.msgIds
        let state'' := {state' with shimVec := shimVec', net := net', execution := e'', msgIds := msgIds'}
        state''
    | PermissionType.store =>
        let (shimVec', e'', net', msgIds') := shimWrite shim instr.addr instr.data instr.stren state'.shimVec state'.execution state'.net state'.msgIds
        let state'' := {state' with shimVec := shimVec', execution := e'', net := net', msgIds := msgIds'}
        state''
    | PermissionType.fence =>
        let (shimVec', net', msgIds') := shimFence shim state'.shimVec state'.net state'.msgIds
        let state'' := {state' with shimVec := shimVec', net := net', msgIds := msgIds'}
        state''

def canIssueInstr {c : SystemConfig} (shimId : ShimId c) (state : IncState c) : Prop :=
    let shimStruct := state.shimVec[shimId]
    (
        shimStruct.active = true ∧
        shimStruct.fencePending = false ∧
        shimStruct.pendingWSC = false ∧
        (state.execution[shimId].list[shimStruct.qInd]!).pend = false
    )

-- @[simp]
-- theorem List.get_tail_succ {α : Type u} [Inhabited α] (v : List α) :
--     v.length > 0 →
--     (forall (i : Fin (v.tail.length)), v.tail[i] = v[i.succ]!) := by
--     intro h i
--     simp only [List.tail]
--     split
--     case h_1 =>
--         exfalso
--         simp at h
--     case h_2 x xs =>
--         simp at *
--         rfl
    -- | mk l h =>
    -- simp [Vector.tail]
    -- ring_nf
-----------------------------------------------------------------------
-- state transition

-- inductive increment_init {c : SystemConfig} : IncState c → Prop where
--     | IncInit : forall (e : Execution c),                     -- IncInit is a proof that the state {...} satisfies increment_init
--         increment_init {
--             cc := (default : CCMachine c)
--             shimVec := (default : ShimType c)
--             net := (default : NETOrdered c)
--             execution := e
--             done := default
--         }

-- negation of all the preconditions to first three constructors of increment_step
def isDone {c : SystemConfig} (state : IncState c) : Prop :=
    let CCNode : Node c := ⟨c.threads, c.threads.lt_succ_self⟩
    (state.net[CCNode]).length = 0 ∧
    forall (shim : ShimId c), ¬ canIssueInstr shim state ∧ (state.net[(shim.castSucc)]).length = 0


def valid_CCReceive_MType (mt : MType) : Bool :=
match mt with
| MType.WRITE => true
| MType.RREQ => true
| MType.FREQ => true
| _ => false

inductive increment_step {c : SystemConfig} : IncState c → IncState c → Prop where
    | ProcessInstr : forall (s s' : IncState c) (shim : ShimId c),
                canIssueInstr shim s →
                s' = getAndIssueInstr shim s →
                increment_step s s'
    | ShimProcessMsg : forall (s s' : IncState c) (shim : ShimId c),
                (s.net[(shim.castSucc)]).length > 0 →
                s' = shimReceiveAndPopMsg shim s →
                increment_step s s'
    | CCProcessMsg : forall (s s' : IncState c),
                (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)]).length > 0 →
                valid_CCReceive_MType (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)].head!).mtype →
                ↑(s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)].head!).src.val < (↑c.threads.val) →
                s' = CCReceiveAndPopMsg s →
                increment_step s s'
    | Finish : forall (s s' : IncState c),
             s.done = false → isDone s → s' = {s with done := true} →
             increment_step s s'

inductive increment_reachable {c : SystemConfig} : IncState c → Prop where
  | init :
        forall (e : Execution c),
            increment_reachable {
                cc := default,
                shimVec := default,
                net := default,
                msgIds := default
                execution := e,
                done := default
            }
  | step :
      forall (s s' : IncState c),
        increment_reachable s →
        increment_step s s' →
        increment_reachable s'

def end_state {c : SystemConfig} (s : IncState c) : Prop :=
  s.done = true ∧ increment_reachable s

-- example
-- namespace small_example
-- def starting_state : IncState default :=
-- {   cc := default
--     shimVec := default
--     net := default
--     execution := default
--     done := default
-- }
-- -- proof that starting_state is a valid initial state (proved by IncInit)
-- example : increment_init starting_state := increment_init.IncInit (default : Execution default)

-- def next_state : IncState default := getAndIssueInstr 1 starting_state
-- #eval next_state
-- example : increment_step starting_state next_state :=
-- increment_step.ProcessInstr starting_state next_state 1
--     (by
--       unfold canIssueInstr
--     --   simp [getAndIssueInstr]
--       exact if_false_right.mp rfl
--     )
-- end small_example



/-Inductive increment_step : increment_state -> increment_state -> Prop :=
| IncLock : forall g,
  increment_step {| Shared := {| Locked := false; Global := g |};
                    Private := Lock |}
                 {| Shared := {| Locked := true; Global := g |};
                    Private := Read |}
| IncRead : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Read |}
                 {| Shared := {| Locked := l; Global := g |};
                    Private := Write g |}
| IncWrite : forall l g v,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Write v |}
                 {| Shared := {| Locked := l; Global := S v |};
                    Private := Unlock |}
| IncUnlock : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Unlock |}
                 {| Shared := {| Locked := false; Global := g |};
                    Private := Done |}.-/







-----------------------------------------------------------------
-- TESTING functions --------------------------------------------
----------------------------------------------------------------
-- def litmusEx : Execution (default : SystemConfig) :=
--     fun (t : ShimId default) =>
--         fun (s : QInd default) =>
--             match t, s with
--             | 0, 0 => {(default : Instr default) with access := PermissionType.store, addr := 0, data := 1}
--             | 0, 1 => {(default : Instr default) with access := PermissionType.store, addr := 1, data := 1}
--             | 1, 0 => {(default : Instr default) with access := PermissionType.load, addr := 1, data := 1}
--             | 1, 1 => {(default : Instr default) with access := PermissionType.load, addr := 0, data := 1}

---------------------------------------------------------------------------
-- namespace test1
-- def shimVec := (default : ShimType default)
-- #eval shimVec
-- def net := (default : NETOrdered default)
-- #eval net
-- def cc := (default : CCMachine default)
-- #eval cc
-- def out := (default : Output default)
-- #eval out
-- -- TEST 1: MP: start with x, y invalid in both shims
-- --  shim1Write -> CCReceive WRITE -> shim1Write -> CCReceive WRITE ->
-- --  shim2Read -> CCReceive RREQ -> shim2Receive RRESP (y=1) -> shim1Receive WRITE_ACK (syncbit = off)

-- def res1 := getInstr (0 : ShimId default) shimVec litmusEx
-- def litmusEx' := res1.1
-- def instr1 := res1.2
-- #eval litmusEx'
-- #eval instr1
-- -- def shimWrite {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (data : Data) (stren : OpStrength)
--             --   (shimVec : ShimType c) (e : Execution c) (net : NETOrdered c) : shimtype x execution x net

-- def res2 := shimWrite (0 : ShimId default) instr1.addr instr1.data instr1.stren shimVec litmusEx' net
-- def shimVec' : ShimType default := res2.1
-- def litmusEx'' : Execution default := res2.2.1
-- def net' : NETOrdered default := res2.2.2
-- #eval shimVec'
-- #eval litmusEx''
-- #eval net'

-- -- Message c → CCMachine c → NETOrdered c → CCMachine c × NETOrdered c
-- def res3 := CCReceive (net'.get 2).head! cc net'
-- def cc' := res3.1
-- def net'' := res3.2
-- #eval cc'
-- #eval net''
-- -- popMessage {c : SystemConfig} (dst : Node c) (net : NETOrdered c) : NETOrdered c
-- def net''' := popMessage 2 net''
-- #eval net'''
-- -- Wx = 1 done

-- def res4 := getInstr (0 : ShimId default) shimVec' litmusEx''
-- def litmusEx''' := res4.1
-- def instr2 := res4.2
-- #eval litmusEx'''
-- #eval instr2

-- def res5 := shimWrite (0 : ShimId default) instr2.addr instr2.data instr2.stren shimVec' litmusEx''' net'''
-- def shimVec'' : ShimType default := res5.1
-- def litmusEx'''' : Execution default := res5.2.1
-- def net'''' : NETOrdered default := res5.2.2
-- #eval shimVec''
-- #eval litmusEx''''
-- #eval net''''

-- def res6 := CCReceive (net''''.get 2).head! cc' net''''
-- def cc'' := res6.1
-- def net''''' := res6.2
-- #eval cc''
-- #eval net'''''
-- def net6 := popMessage 2 net'''''
-- #eval net6
-- -- Wy = 1 done

-- def res7 := getInstr (1 : ShimId default) shimVec'' litmusEx''''
-- def litmusEx5 := res7.1
-- def instr3 := res7.2
-- #eval litmusEx5
-- #eval instr3

-- def res8 := shimRead (1 : ShimId default) instr3.addr instr3.stren shimVec'' net6 litmusEx5 out
-- def shimVec3 := res8.1
-- def net7 : NETOrdered default := res8.2.1
-- def LitmusEx6 : Execution default := res8.2.2.1
-- def output1 : Output default := res8.2.2.2
-- #eval shimVec3
-- #eval net7
-- #eval LitmusEx6
-- #eval output1

-- def res9 := CCReceive (net7.get 2).head! cc'' net7
-- def cc3 := res9.1
-- def net8 := res9.2
-- #eval cc3
-- #eval net8
-- def net9 := popMessage 2 net8
-- #eval net9

-- -- SHIM: incoming messages
-- -- def shimReceive {c : SystemConfig} (msg : Message c)
--                 -- (shimVec : ShimType c) (e : Execution c) (o : Output c)
--                 -- : (ShimType c) × (Execution c) × (Output c)
-- def res10 := shimReceive (net9.get 1).head! shimVec3 LitmusEx6 output1
-- def shimVec4 := res10.1
-- def litmusEx7 := res10.2.1
-- def out2 := res10.2.2
-- #eval shimVec4
-- #eval litmusEx7
-- #eval out2
-- def net10 := popMessage 1 net9
-- #eval net10

-- def res11 := shimReceive (net10.get 0).head! shimVec4 litmusEx7 out2
-- def shimVec5 := res11.1
-- def litmusEx8 := res11.2.1
-- def out3 := res11.2.2
-- #eval shimVec5
-- #eval litmusEx8
-- #eval out3
-- end test1

-- ----------------------------------------------------------------------
-- -- TEST 2: MP: S1 caches x; S2 caches y initially
-- -- Shim2Read y=0 -> Shim1Write x=1 -> CCReceive WRITEx=1 -> Shim2Read
-- -- CCreceive RREQ x -> Shim2Receive RRESP x=1
-- namespace test2
-- def shimcache1 := (default : ShimCache default).set 0 {(default : ShimElemState) with state := CacheState.Valid}
-- def shim1 := {(default : Shim default) with state := shimcache1}
-- def shimcache2 := (default : ShimCache default).set 1 {(default : ShimElemState) with state := CacheState.Valid}
-- def shim2 := {(default : Shim default) with state := shimcache2}
-- def shimVec := ((default : ShimType default).set 0 shim1).set 1 shim2
-- #eval shimVec
-- def net := (default : NETOrdered default)
-- #eval net
-- def ccelem1 := {(default : CCElemState default) with sharers := ((default : Vector Bool (default : SystemConfig).threads).set 0 true)}
-- def ccelem2 := {(default : CCElemState default) with sharers := ((default : Vector Bool (default : SystemConfig).threads).set 1 true)}
-- def cccache := ((default : CCCache default).set 0 ccelem1).set 1 ccelem2
-- def cc := {(default : CCMachine default) with cache := cccache}
-- #eval cc
-- def out := (default : Output default)
-- #eval out

-- -- Shim2Read y=0 -> Shim1Write x=1 -> CCReceive WRITEx=1 -> Shim2Read
-- -- CCreceive RREQ x -> Shim2Receive RRESP x=1
-- def res1 := getInstr (1 : ShimId default) shimVec litmusEx
-- def e1 : Execution default := res1.1
-- def i1 : Instr default := res1.2
-- #eval e1
-- #eval i1
-- def res2 := shimRead (1 : ShimId default) i1.addr i1.stren shimVec net e1 out
-- def sv1 : ShimType default := res2.1
-- def net1 : NETOrdered default := res2.2.1
-- def e2 : Execution default := res2.2.2.1
-- def o1 : Output default := res2.2.2.2
-- #eval sv1
-- #eval net1
-- #eval e2
-- #eval o1
-- -- if we immediately process the Ry=1 in thread 2, is it supposed to read with timestamp 0? seems like murphi does this too but check

-- def res3 := getInstr 0 sv1 e2
-- def e3 := res3.1
-- def i2 := res3.2
-- def res4 := shimWrite 0 i2.addr i2.data i2.stren sv1 e3 net1
-- def sv2 := res4.1
-- def e4 := res4.2.1
-- def net2 := res4.2.2
-- #eval sv2
-- #eval e4
-- #eval net2

-- def res5 := getInstr 1 sv2 e4
-- def e5 := res5.1
-- def i3 := res5.2
-- #eval e5
-- #eval i2
-- def res6 := shimRead 1 i3.addr i3.stren sv2 net2 e4 o1
-- def sv3 := res6.1
-- def net3 := res6.2.1
-- def e6 := res6.2.2.1
-- def o2 := res6.2.2.2
-- #eval sv3
-- #eval net3
-- #eval e6
-- #eval o2
-- -- ccreceive write x=1
-- def res7 := CCReceive (net3.get 2).head! cc net3
-- def cc1 := res7.1
-- def net4 := res7.2
-- #eval cc1
-- #eval net4
-- def net5 := popMessage 2 net4
-- #eval net5
-- -- ccreceive RREQ for x
-- def res8 := CCReceive (net5.get 2).head! cc1 net5
-- def cc2 := res8.1
-- def net6 := res8.2
-- #eval cc2
-- #eval net6
-- def net7 := popMessage 2 net6
-- #eval net7
-- -- shimReceive RRESP for x
-- def res9 := shimReceive (net7.get 1).head! sv3 e6 o2
-- def sv4 := res9.1
-- def e7 := res9.2.1
-- def o3 := res9.2.2
-- #eval sv4
-- #eval e7
-- #eval o3
-- end test2


-- -----------------------------------------------------------
-- -- test3 : storebuffer:
-- -- don't process any memglue messages, just do instructions and read 0's
-- -- setup: both shims cache all addresses at start (all valid)
-- namespace test3
-- def litmusEx : Execution (default : SystemConfig) :=
--     fun (t : ShimId default) =>
--         fun (s : QInd default) =>
--             match t, s with
--             | 0, 0 => {(default : Instr default) with access := PermissionType.store, addr := 0, data := 1}
--             | 0, 1 => {(default : Instr default) with access := PermissionType.load, addr := 1, data := 0}
--             | 1, 0 => {(default : Instr default) with access := PermissionType.store, addr := 1, data := 1}
--             | 1, 1 => {(default : Instr default) with access := PermissionType.load, addr := 0, data := 0}
-- def shimVec1 := (default : ShimType default)
-- def out1 := (default : Output default)
-- def net1 := (default : NETOrdered default)

-- def res1 := getInstr 1 shimVec1 litmusEx
--     def e1 := res1.1
--     def i1 := res1.2
--     #eval e1
--     #eval i1
-- def res2 := shimWrite 1 i1.addr i1.data i1.stren shimVec1 e1 net1
--     def shimVec2 := res2.1
--     def e2 := res2.2.1
--     def net2 := res2.2.2
--     #eval shimVec2
--     #eval e2
--     #eval net2

-- def res3 := getInstr 1 shimVec2 e2
--     def e3 := res3.1
--     def i2 := res3.2
--     #eval e3
--     #eval i2
-- def res4 := shimRead 1 i2.addr i2.stren shimVec2 net2 e3 out1
--     def shimVec3 := res4.1
--     def net3 : NETOrdered default := res4.2.1
--     def e4 := res4.2.2.1
--     def out2 := res4.2.2.2
--     #eval shimVec3
--     #eval net3
--     #eval e4
--     #eval out2

-- def res5 := getInstr 0 shimVec3 e4
--     def e5 := res5.1
--     def i3 := res5.2
--     #eval e5
--     #eval i3
-- def res6 := shimWrite 0 i3.addr i3.data i3.stren shimVec3 e5 net3
--     def shimVec4 := res6.1
--     def e6 := res6.2.1
--     def net4 := res6.2.2
--     #eval shimVec4
--     #eval e6
--     #eval net4

-- def res7 := getInstr 0 shimVec4 e6
--     def e7 := res7.1
--     def i4 := res7.2
--     #eval e7
--     #eval i4
-- def res8 := shimRead 0 i4.addr i4.stren shimVec4 net4 e7 out2
--     def shimVec5 := res8.1
--     def net5 : NETOrdered default := res8.2.1
--     def e8 := res8.2.2.1
--     def out3 := res8.2.2.2
--     #eval shimVec5
--     #eval net5
--     #eval e8
--     #eval out3
-- end test3
-- ----------------------------------------------------------------------
-- -- test 4: 4 shims, test msg send to sharers
-- -- setup: all shims cache all addresses (all valid and sharers)
-- namespace test4
-- def c := {(default : SystemConfig) with threads := 4}
-- def shimVec1 := Vector.replicate 4 (default : Shim c)
-- #eval shimVec1
-- #eval (default : Instr c)
-- def e1 : Execution c :=
--     fun (s : ShimId c) =>
--         fun (t : QInd c) =>
--             match s, t with
--             | 0, 0 => {(default : Instr c) with access := PermissionType.store, data := 1}
--             | _, _ => (default)
-- def out1 := (default : Output c)
-- def net1 := (default : NETOrdered c)
-- def cc1 := (default : CCMachine c)
-- #eval cc1

-- def res1 := getInstr 0 shimVec1 e1
--     def e2 := res1.1
--     def i1 := res1.2
--     #eval e2
--     #eval i1
-- def res2 := shimWrite 0 i1.addr i1.data i1.stren shimVec1 e2 net1
--     def shimVec2 := res2.1
--     def e3 := res2.2.1
--     def net2 := res2.2.2
--     #eval shimVec2
--     #eval e3
--     #eval net2

-- def res3 := CCReceive (net2.get 4).head! cc1 net2
--     def cc2 := res3.1
--     def net3 := res3.2
--     #eval cc2
--     #eval net3

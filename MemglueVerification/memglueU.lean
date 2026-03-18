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
abbrev Lwc : Type := Nat
abbrev RfBufCnt : Type := Nat
abbrev Node (c : SystemConfig) : Type := Fin (c.threads + 1)
abbrev SeenSet : Type := List Nat
abbrev WriteId : Type := Nat
abbrev FenceCnt : Type := Nat
abbrev MsgCnt : Type := Nat

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
deriving Repr, DecidableEq
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
    cnt : MsgCnt := 0               -- count is the ocnt of sender at time it is sent
    id : Nat := 0
    fenceCnt : FenceCnt := 0
    writeId : WriteId := 0
    seenId : WriteId := 0
    wCnt : WriteId := 0
    qInd : MsgCnt := 0
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
        cnt := 0
        id := 0
        fenceCnt := 0
        writeId := 0
        seenId := 0
        wCnt := 0
        qInd := 0
    }


abbrev MessageIds (c : SystemConfig) : Type := Vector Nat (c.threads + 1)
-- matrix one row of messages per node (CC + shims)
abbrev NETUnordered (c : SystemConfig) : Type := Vector (List (Message c)) (c.threads + 1)
instance (c : SystemConfig) : Inhabited (NETUnordered c) where default := Vector.replicate (c.threads + 1) (List.nil)
instance (c : SystemConfig) [Repr (List (Message c))] : Repr (NETUnordered c) where
  reprPrec net _ := repr (net.toList)
-- instance (c : SystemConfig) : Inhabited (NETOrdered c) where default := Vector.replicate (c.threads + 1) (List.singleton (default : (Message c)))
abbrev MsgBuffer (c : SystemConfig) : Type := List (Message c)
instance (c : SystemConfig) : Inhabited (MsgBuffer c) where default := List.nil

inductive CacheState : Type where
    | Invalid | Valid -- put Valid first for store buffer test
deriving Inhabited, DecidableEq, Repr
#eval (default : CacheState)

structure ShimElemState : Type where
    state : CacheState
    data : Data
    ts : Timestamp
    syncBit : Bool
    lwc : Lwc
    rfBufCnt : RfBufCnt
deriving Inhabited, Repr
instance : Inhabited ShimElemState where
    default := {
        state := (default : CacheState)
        data := (default : Data)
        ts := (default : Timestamp)
        syncBit := true
        lwc := 0
        rfBufCnt := 0
    }

structure CCElemState (c : SystemConfig) : Type where
    data : Data
    ts : Timestamp
    sharers : Vector Bool c.threads
    lastWriteShim : Node c
deriving Inhabited, Repr
instance (c : SystemConfig) : Inhabited (CCElemState c) where
    default := {
        data := default
        ts := default
        sharers := Vector.replicate c.threads false -- make this true for store buffer test
        lastWriteShim := 0
        }

abbrev ShimCache (c : SystemConfig) : Type := Vector ShimElemState c.addrCount
instance (c : SystemConfig) : Inhabited (ShimCache c) where default := Vector.replicate c.addrCount (default : ShimElemState)
instance (c : SystemConfig) [Repr ShimElemState] : Repr (ShimCache c) where
  reprPrec cache _ := repr (cache.toList)

abbrev CCCache (c : SystemConfig) : Type := Vector (CCElemState c) c.addrCount
instance (c : SystemConfig) : Inhabited (CCCache c) where default := Vector.replicate c.addrCount (default : CCElemState c)
instance (c : SystemConfig) [Repr (CCElemState c)] : Repr (CCCache c) where
    reprPrec cache _ := repr (cache.toList)

structure CCCounterElem : Type where
    localWriteCount : Nat
    fenceCount : Nat
deriving Inhabited, Repr
instance : Inhabited CCCounterElem where
    default := {
        localWriteCount := 0
        fenceCount := 0
    }

abbrev CCCounterElemPerAddr (c : SystemConfig): Type := Vector CCCounterElem c.addrCount
instance (c : SystemConfig) : Inhabited (CCCounterElemPerAddr c) where default := Vector.replicate c.addrCount (default : CCCounterElem )
instance (c : SystemConfig) [Repr CCCounterElem] : Repr (CCCounterElemPerAddr c) where
    reprPrec cache _ := repr (cache.toList)

structure CCCounterPerShim (c : SystemConfig) : Type where
    ccCounterElemPerAddr : CCCounterElemPerAddr c
    ocnt : MsgCnt
    icnt : MsgCnt
deriving Inhabited, Repr
instance (c : SystemConfig): Inhabited (CCCounterPerShim c) where
    default := {
        ccCounterElemPerAddr := default
        ocnt := 0
        icnt := 0
    }

abbrev CCCounters (c : SystemConfig) : Type := Vector (CCCounterPerShim c ) c.threads
instance (c : SystemConfig) : Inhabited (CCCounters c) where default := Vector.replicate c.threads (default : CCCounterPerShim c )
instance (c : SystemConfig) [Repr (CCCounterPerShim c) ] : Repr (CCCounters c) where
    reprPrec cache _ := repr (cache.toList)

structure CCSeenIdsElem : Type where
    writeId : WriteId
    seenId : WriteId
deriving Inhabited, Repr
instance  : Inhabited CCSeenIdsElem where
    default := {
        writeId := 0
        seenId := 0
    }

abbrev CCSeenIdsPerAddr (c : SystemConfig) : Type := Vector CCSeenIdsElem c.addrCount
instance (c : SystemConfig) : Inhabited (CCSeenIdsPerAddr c) where default := Vector.replicate c.addrCount (default : CCSeenIdsElem )
instance (c : SystemConfig) [Repr CCSeenIdsElem] : Repr (CCSeenIdsPerAddr c) where
    reprPrec cache _ := repr (cache.toList)

structure CCSeenIdsPerShim (c : SystemConfig) : Type where
    ccSeenIdsPerAddr : CCSeenIdsPerAddr c
    seenPerShim : WriteId
deriving Inhabited, Repr
instance (c : SystemConfig) : Inhabited (CCSeenIdsPerShim c) where
    default := {
        ccSeenIdsPerAddr := default
        seenPerShim := 0
    }

abbrev CCSeenIds (c : SystemConfig) : Type := Vector (CCSeenIdsPerShim c) c.threads
instance (c : SystemConfig) : Inhabited (CCSeenIds c) where default := Vector.replicate c.threads (default : CCSeenIdsPerShim c)
instance (c : SystemConfig) [Repr (CCSeenIdsPerShim c)] : Repr (CCSeenIds c) where
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
    icnt : Nat
    ocnt : Nat
    fenceCnt : Nat
    seenCache : SeenSet
    seenBuf : SeenSet
    msgBuf : MsgBuffer c
    qInd : QInd
    -- qCnt : QCnt c
deriving Inhabited, Repr
instance (c : SystemConfig) : Inhabited (Shim c) where
    default := {
        state := (default : ShimCache c)
        active := true
        pendingWSC := false
        fencePending := false
        icnt := 0
        ocnt := 0
        fenceCnt := 0
        seenCache := { } -- default list?
        seenBuf := { }
        msgBuf := default
        qInd := 0
        -- qCnt := ⟨c.steps, Nat.lt_succ_self c.steps⟩
    }
-- #eval (default : QInd (default : SystemConfig))
#eval (default : Shim (default : SystemConfig))

structure CCMachine (c : SystemConfig) : Type where
    cache : CCCache c
    counters : CCCounters c
    seenIds : CCSeenIds c
    buf : MsgBuffer c
    wIdCounter : WriteId
deriving Inhabited, Repr
instance (c : SystemConfig) : Inhabited (CCMachine c) where
    default := {
        cache := default,
        counters := default,
        seenIds := default,
        buf := default,
        wIdCounter := 1      -- Initialized to 1 per Murphi model
    }

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
    net : NETUnordered c
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
-- Return whether writeId v is in the seenSet of shim s
def inSeenSet {c : SystemConfig} (s : Shim c) (v : WriteId) : Bool :=
  match s.seenCache with
  | [] => false
  | (head :: tail) => v <= head || tail.contains v

-- Return whether writeId v is in the seenSetBuf of shim s
def inSeenSetShimBuf {c : SystemConfig} (s : Shim c) (v : WriteId) : Bool :=
  s.seenBuf.contains v

/-- Adds v to the seenSet of shim s -/
def addSeenId {c : SystemConfig} (s : Shim c) (v : WriteId) : Option (Shim c) :=
  if inSeenSet s v then
    some s
--   else if s.seenCache.length >= s.maxSize then
--     none -- Equivalent to "Seen set is full" assertion
  else
    some { s with seenCache := s.seenCache ++ [v] }

/-- Adds v to the shim buffer seenSetBuf of shim s -/
def addSeenIdShimBuf {c : SystemConfig} (s : Shim c) (v : WriteId) : Option (Shim c) :=
  if inSeenSetShimBuf s v then
    some s
--   else if s.seenBuf.length >= s.maxSize then #TODO: max size?
--     none
  else
    some { s with seenBuf := s.seenBuf ++ [v] }

/-- Helper function to replicate Murphi's manual shift-removal -/
def eraseFirst {α : Type} [BEq α] (l : List α) (v : α) : List α :=
  match l with
  | [] => []
  | x :: xs => if x == v then xs else x :: eraseFirst xs v

/-- Removes v from the shim buffer seenSet of shim s -/
def removeSeenIdShimBuf {c : SystemConfig} (s : Shim c) (v : WriteId) : Shim c :=
  if s.seenBuf.contains v then
    { s with seenBuf := eraseFirst s.seenBuf v }
  else
    s

def maxSeenId {c : SystemConfig} (s : Shim c) : WriteId :=
  s.seenCache.foldl max 0

def maxSeenIdBoth {c : SystemConfig} (s : Shim c) : WriteId :=
    let m1 := s.seenCache.foldl max 0
    let m2 := s.seenBuf.foldl max 0
    max m1 m2

def cullSeenSet {c : SystemConfig} (s : Shim c) : Shim c :=
  -- 1. Identify the maximum value across both lists
  let maxVal := maxSeenIdBoth s

  -- 2. Construct the new state:
  --    - seenSet becomes a singleton list containing only the watermark.
  --    - seenBuf is cleared (emptied).
  { s with
      seenCache := [maxVal],
      seenBuf := []
  }

def sameAddrReadsInQueue {c : SystemConfig} (shim : ShimId c) (qInd : QInd) (addr : Addr c) (shimVec : ShimType c) (e : Execution c) : Bool :=
    let instrs := e[shim].list
    -- Iterate from index 0 to qInd - 1
    let rec checkIdx (i : Nat) : Bool :=
        if i >= qInd then false
        else if i < instrs.length then
            let instr := instrs[i]!
            if instr.pend ∧ instr.addr = addr then true
            else checkIdx (i + 1)
        else false
    checkIdx 0

def acceptRRESPEarly {c : SystemConfig} (shim : ShimId c) (msg : Message c) (shimVec : ShimType c) (e : Execution c) : Bool :=
    let noSameAddrRead := !(sameAddrReadsInQueue shim msg.qInd msg.addr shimVec e)
    let cacheTs := shimVec[shim].state[msg.addr].ts
    noSameAddrRead ∧ (msg.ts <= cacheTs)

def removeNth {α : Type} (l : List α) (n : Nat) : List α :=
  l.take n ++ l.drop (n + 1)
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

def netWithAddedMsg {c : SystemConfig} (msg : Message c) (net : NETUnordered c) : NETUnordered c :=
    let oldList : List (Message c) := net[msg.dst]
    let updatedList : List (Message c) := oldList.append [msg]
    let updatedNet : NETUnordered c := net.set msg.dst.val updatedList
    updatedNet

#eval (default : NETUnordered (default : SystemConfig))
#eval netWithAddedMsg ({(default : Message (default : SystemConfig)) with mtype := MType.WRITE_ACK, src := 0, ts := 10000, stren := OpStrength.SC, dst := 1}) (default : NETUnordered (default : SystemConfig))

def send {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c)
         (data' : Data) (addr' : Addr c) (ts' : Timestamp) (stren' : OpStrength)
         (cnt' : MsgCnt) (fenceCnt' : FenceCnt) (writeId' : WriteId) (seenId' : WriteId) (qInd' : MsgCnt) (wCnt' : WriteId)
         (net : NETUnordered c) (msgIds : MessageIds c)
         : NETUnordered c × MessageIds c :=

        let msg : (Message c) := {mtype := mtype', src := src', dst := dst', data := data', addr := addr', ts := ts', stren := stren', id := msgIds[dst'],
                                    cnt := cnt', fenceCnt := fenceCnt', writeId := writeId', seenId := seenId', qInd := qInd', wCnt := wCnt' }
        let msgIds' := msgIds.set dst' (msgIds[dst'] + 1)
        (netWithAddedMsg msg net, msgIds')

-- def res := send MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) 10 0 100 OpStrength.ACQ default (default : NETOrdered (default : SystemConfig))
-- #eval send MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) 10 0 100 OpStrength.ACQ res.1 res.2

def sendFence {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c) (cnt' : MsgCnt)
                (net : NETUnordered c) (msgIds : MessageIds c)
: NETUnordered c × MessageIds c:=
    let msg : (Message c) := {(default : Message c) with mtype := mtype', src := src', dst := dst', id := msgIds[dst'], cnt := cnt'}
    let msgIds' := msgIds.set dst' (msgIds[dst'] + 1)
    (netWithAddedMsg msg net, msgIds')

-- def res := sendFence MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) default default
-- #eval sendFence MType.EVICT (1 : Node (default : SystemConfig)) (0 : Node (default : SystemConfig)) res.1 res.2

-- def testnet := sendFence MType.EVICT (0 : Node (default : SystemConfig)) (1 : Node (default : SystemConfig)) (default : NETOrdered (default : SystemConfig))
-- #eval testnet

def popMessage {c : SystemConfig} (dst : Node c) (net : NETUnordered c) : NETUnordered c :=
    let oldList : List (Message c) := net[dst]
    let updatedList : List (Message c) := oldList.tail
    let updatedNet : NETUnordered c := net.set dst.val updatedList
    updatedNet

-- #eval popMessage (2 : Node (default : SystemConfig)) (default : NETOrdered (default : SystemConfig))
-- #eval popMessage (1 : Node (default : SystemConfig)) testnet

-- Update output of litmus test load
def updateVal {c : SystemConfig} (targetThread : ShimId c) (data : Data) (resolveQInd : QInd)
    (e : Execution c) : Execution c :=

    let stepCount := e[targetThread].list.length

    if resolveQInd < stepCount then
        -- Update the data and explicitly set pend := false
        let newInstr : Instr c := {e[targetThread].list[resolveQInd]! with data := data, pend := false}
        let newList : List (Instr c) := e[targetThread].list.set resolveQInd newInstr
        let e' := e.set targetThread {list := newList, nonempty := (by unfold newList; simp; exact e[↑targetThread].nonempty)}
        e'
    else
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

def popInstr {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (e : Execution c) : ShimType c :=
    let qInd := shimVec[shim].qInd
    let qCnt := e[shim].list.length

    let nextQInd := qInd + 1

    -- If the next index exceeds or equals the instruction count, the shim is no longer active
    let isActive := if nextQInd >= qCnt then false else shimVec[shim].active

    let shimVec' := shimVec.set shim { shimVec[shim] with
        qInd := nextQInd,
        active := isActive
    }

    shimVec'

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
def shimReceive {c : SystemConfig} (shim : ShimId c) (msg : Message c) (inOrder : Bool)
                (shimVec : ShimType c) (e : Execution c)
                : (ShimType c) × (Execution c) :=
    if h1 : msg.dst.val < c.threads.val then
        let curShim : ShimId c := ⟨msg.dst.val, h1⟩
        let curShimCache : ShimCache c := (shimVec[curShim]).state
        let addr := msg.addr

        match msg.mtype with
            | MType.WRITE =>
                let shimElem : ShimElemState := curShimCache[addr]

                let (shimVec', e') := if msg.ts > shimElem.ts then
                    (shimWriteCache curShim CacheState.Valid msg.data msg.ts addr shimVec, e)
                else
                    (shimIncrTS curShim addr shimVec, e)

                -- Handle SeenIds based on inOrder
                let modShim := shimVec'[curShim]
                let finalShim := if inOrder then
                    if inSeenSet modShim msg.writeId then modShim else { modShim with seenCache := modShim.seenCache ++ [msg.writeId] }
                else
                    if inSeenSetShimBuf modShim msg.writeId then modShim else { modShim with seenBuf := modShim.seenBuf ++ [msg.writeId] }

                let finalShimVec := shimVec'.set curShim finalShim
                (finalShimVec, e')

            | MType.WRITE_ACK =>
                let shimElem : ShimElemState := curShimCache[addr]

                let shimVec' := if shimElem.syncBit = true then
                    let data' := if shimElem.lwc > 1 then shimElem.data else msg.data
                    let ts' := msg.ts + shimElem.lwc - 1
                    let modShims : ShimType c := shimWriteCache curShim CacheState.Valid data' ts' addr shimVec
                    let modShimElem : ShimElemState := { modShims[curShim].state[addr] with syncBit := false }
                    let modShimCache : ShimCache c := modShims[curShim].state.set addr modShimElem
                    modShims.set curShim { modShims[curShim] with state := modShimCache }
                else
                    shimVec

                let finalShimVec := if shimVec'[curShim].pendingWSC then
                    shimVec'.set curShim { shimVec'[curShim] with pendingWSC := false }
                else
                    shimVec'

                (finalShimVec, e)

            | MType.RRESP =>
                let shimElem : ShimElemState := curShimCache[addr]

                -- Determine actual data based on syncBit/lwc overrides
                let data' := if shimElem.syncBit ∧ shimElem.lwc > 0 then shimElem.data else msg.data

                let shimVec' := if shimElem.syncBit then
                    let ts' := msg.ts + shimElem.lwc
                    let modShims := shimWriteCache curShim CacheState.Valid data' ts' addr shimVec
                    let modShimElem := { modShims[curShim].state[addr] with syncBit := false }
                    modShims.set curShim { modShims[curShim] with state := modShims[curShim].state.set addr modShimElem }
                else
                    if shimElem.ts <= msg.ts then
                        shimWriteCache curShim CacheState.Valid data' msg.ts addr shimVec
                    else
                        shimVec

                -- Handle SeenIds
                let modShim := shimVec'[curShim]
                let seenShim := if inOrder then
                    if inSeenSet modShim msg.writeId then modShim else { modShim with seenCache := modShim.seenCache ++ [msg.writeId] }
                else
                    if inSeenSetShimBuf modShim msg.writeId then modShim else { modShim with seenBuf := modShim.seenBuf ++ [msg.writeId] }
                let finalShimVec := shimVec'.set curShim seenShim

                -- Update test values and pop instruction
                -- REMOVED finalShimVec from updateVal call
                let e' : Execution c := updateVal curShim data' msg.qInd e

                -- popInstr now returns only ShimType c
                let newShimVec := popInstr curShim finalShimVec e'
                (newShimVec, e')

            | MType.FREQ =>
                let modShim := { shimVec[curShim] with fenceCnt := shimVec[curShim].fenceCnt + 1 }
                (shimVec.set curShim modShim, e)

            | MType.FRESP =>
                let modShim := { shimVec[curShim] with fencePending := false }
                let modShimVec := shimVec.set curShim modShim

                -- Pop instruction conditionally based on pendingWSC
                if shimVec[curShim].pendingWSC = false then
                    let newShimVec := popInstr curShim modShimVec e
                    (newShimVec, e)
                else
                    let modShim' := { modShimVec[curShim] with pendingWSC := false }
                    let newShimVec := modShimVec.set curShim modShim'
                    (newShimVec, e)

            | _ => panic! "message with wrong message type was passed into ShimReceive"
    else
        panic! "message with destination that was not a shim was passed into ShimReceive"

def shimAcceptMessage {c : SystemConfig} (shim : ShimId c) (msg : Message c) (shimVec : ShimType c) (e : Execution c) : Bool :=
    let s := shimVec[shim]
    let isFence : Bool := msg.mtype == MType.FREQ || msg.mtype == MType.FRESP

    if s.fencePending || (!isFence && s.fenceCnt < msg.fenceCnt) then
        false
    else if !isFence && s.state[msg.addr].syncBit then
        false
    else if msg.mtype == MType.WRITE_ACK then
        false
    else
        match msg.mtype with
        | MType.WRITE =>
            let cacheState := s.state[msg.addr]
            if msg.ts + cacheState.lwc - msg.wCnt != cacheState.ts + 1 then
                false
            else
                match msg.stren with
                | OpStrength.RLX => true
                | OpStrength.REL => inSeenSet s msg.seenId
                | _ => false -- SC
        | MType.RRESP =>
            if !acceptRRESPEarly shim msg shimVec e then
                false
            else
                match msg.stren with
                | OpStrength.RLX => true
                | OpStrength.ACQ => inSeenSet s msg.seenId
                | _ => false -- SC
        | MType.FREQ => false
        | MType.FRESP => false
        | _ => false

def shimReceiveAndPopMsg {c : SystemConfig} (shim : ShimId c) (state : IncState c) : IncState c :=
    let shimNode : Node c := shim.castSucc
    let msg := state.net[shimNode].head!
    let expectedIcnt := state.shimVec[shim].icnt

    if msg.cnt = expectedIcnt then
        -- IN-ORDER
        let shimVec_icnt := state.shimVec.set shim { state.shimVec[shim] with icnt := expectedIcnt + 1 }

        let (shimVec', e') := shimReceive shim msg true shimVec_icnt state.execution
        let net' := popMessage shimNode state.net

        { state with shimVec := shimVec', execution := e', net := net' }
    else
        -- OUT-OF-ORDER
        if shimAcceptMessage shim msg state.shimVec state.execution then
            -- Early acceptance
            let (shimVec', e') := shimReceive shim msg false state.shimVec state.execution

            -- Push to buffer
            let shimBuf' := shimVec'[shim].msgBuf ++ [msg]
            let shimVec'' := shimVec'.set shim { shimVec'[shim] with msgBuf := shimBuf' }

            let net' := popMessage shimNode state.net
            { state with shimVec := shimVec'', execution := e', net := net' }
        else
            -- Push to buffer without processing
            let shimBuf' := state.shimVec[shim].msgBuf ++ [msg]
            let shimVec' := state.shimVec.set shim { state.shimVec[shim] with msgBuf := shimBuf' }

            let net' := popMessage shimNode state.net
            { state with shimVec := shimVec', net := net' }


-- SHIM: outgoing messages
-- Write value, or send WRITE to CC
def shimWrite {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (data : Data) (stren : OpStrength)
              (shimVec : ShimType c) (e : Execution c) (net : NETUnordered c) (msgIds : MessageIds c):
              (ShimType c) × (Execution c) × (NETUnordered c) × (MessageIds c) :=

    let currentQInd := shimVec[shim].qInd

    -- 1. Mark instruction as complete (pend := false)
    let instr' := {e[shim].list[currentQInd]! with pend := false}
    let list' := e[shim].list.set currentQInd instr'
    let e' := e.set shim {list := list', nonempty := (by unfold list'; simp; exact e[↑shim].nonempty)}

    -- 2. Increment qInd (PC) and check active state
    let shimVec_advanced := popInstr shim shimVec e'

    -- 3. Check sync bit and process cache
    let shimElem' := shimVec_advanced[shim].state[addr]
    if ((shimElem'.state = CacheState.Invalid) ∧ (shimElem'.syncBit = false)) then
        panic! "Sync Bit improperly set"
    else
        let newTs : Timestamp := shimElem'.ts + 1
        let shimVec'' := shimWriteCache shim CacheState.Valid data newTs addr shimVec_advanced

        let shim' := shimVec''[shim]
        let shimCache' := shim'.state
        let shimElem'' := shimCache'[addr]
        let shimElem''' := { shimElem'' with lwc := shimElem''.lwc + 1 }
        let shimCache'' := shimCache'.set addr shimElem'''
        let shim'' := { shim' with
            state := shimCache'',
            ocnt := shim'.ocnt + 1
        }
        let shimVec''' := shimVec''.set shim shim''

        let shimNode : Node c := Fin.castSucc shim
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)

        let (net', msgIds') := send MType.WRITE shimNode CCNode data addr newTs stren shim''.ocnt 0 0 (maxSeenIdBoth shim'') currentQInd 0 net msgIds

        if stren = OpStrength.SC then
            let modShim := {shimVec'''[shim] with pendingWSC := true}
            let shimVec'''' := shimVec'''.set shim modShim
            (shimVec'''', e', net', msgIds')
        else
            (shimVec''', e', net', msgIds')
-- mp
-- Read value, or send RREQ to CC
def shimRead {c : SystemConfig} (shim : ShimId c) (addr : Addr c) (stren : OpStrength)
    (shimVec : ShimType c) (net : NETUnordered c) (e : Execution c) (msgIds : MessageIds c) :
    (ShimType c) × (NETUnordered c) × (Execution c) × (MessageIds c):=

    let currentQInd := shimVec[shim].qInd

    -- 1. Increment qInd (we always advance the PC)
    let shimVec_advanced := popInstr shim shimVec e

    let shimElem := shimVec_advanced[shim].state[addr]

    if shimElem.state ≠ CacheState.Valid then
        -- Cache Miss: Instruction remains pending (pend = true)
        let shimNode := shim.castSucc
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)

        -- Send RREQ stamped with currentQInd
        let (net', msgIds') := send MType.RREQ shimNode CCNode shimElem.data addr shimElem.ts stren shimVec_advanced[shim].ocnt 0 0 0 currentQInd 0 net msgIds

        -- Update ocnt
        let shimVec_final := shimVec_advanced.set shim { shimVec_advanced[shim] with ocnt := shimVec_advanced[shim].ocnt + 1 }

        (shimVec_final, net', e, msgIds')
    else
        -- Cache Hit: updateVal resolves the data and sets pend := false
        let e' := updateVal shim shimElem.data currentQInd e
        (shimVec_advanced, net, e', msgIds)

--   -- Stop local reads until FRESP received
def shimFence {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (net : NETUnordered c) (msgIds : MessageIds c) (e : Execution c) :
    (ShimType c) × (NETUnordered c) × (Execution c) × (MessageIds c) :=

    let currentQInd := shimVec[shim].qInd

    -- 1. Mark instruction as complete (pend := false)
    let instr' := {e[shim].list[currentQInd]! with pend := false}
    let list' := e[shim].list.set currentQInd instr'
    let e' := e.set shim {list := list', nonempty := (by unfold list'; simp; exact e[↑shim].nonempty)}

    -- 2. Increment qInd and check active state
    let shimVec_advanced := popInstr shim shimVec e'

    let ocnt' := shimVec_advanced[shim].ocnt
    let modShim := {shimVec_advanced[shim] with fencePending := true, ocnt := ocnt' + 1}
    let shimVec' := shimVec_advanced.set shim modShim

    let shimNode := shim.castSucc
    let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)

    let (net', msgIds') := sendFence MType.FREQ shimNode CCNode ocnt' net msgIds

    (shimVec', net', e', msgIds')

  -- CC: process messages -----------------------------------------------------
-- Helper to fold over the filtered list of sharers and send WRITE messages
def foldSharersWrites {c : SystemConfig}
    (sharers : List (ShimId c))
    (msg : Message c)
    (ts' : Timestamp)
    (acc : NETUnordered c × MessageIds c × CCMachine c)
    : NETUnordered c × MessageIds c × CCMachine c :=

    let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)

    List.foldl (fun (currAcc : NETUnordered c × MessageIds c × CCMachine c) (sharer : ShimId c) =>
        let (n, ids, currCC) := currAcc
        let elem := currCC.cache[msg.addr]

        -- Extract the last write shim and handle the type cast (ShimId vs Node)
        let lastWriteShim := elem.lastWriteShim
        let lastWriteShimId : ShimId c := ⟨lastWriteShim.val, sorry⟩ -- Replace sorry with actual proof

        let srcSeen := (currCC.seenIds[lastWriteShimId]).ccSeenIdsPerAddr[msg.addr]
        let destCntrs := currCC.counters[sharer]
        let destSeenAddr := (currCC.seenIds[sharer]).ccSeenIdsPerAddr[msg.addr]

        -- Send the message
        let (n', ids') := send MType.WRITE CCNode sharer.castSucc msg.data msg.addr ts' msg.stren
            destCntrs.ocnt destCntrs.ccCounterElemPerAddr[msg.addr].fenceCount
            srcSeen.writeId srcSeen.seenId msg.qInd destCntrs.ccCounterElemPerAddr[msg.addr].localWriteCount n ids

        -- Increment ocnt for the sharer in the CC state
        let currCC' := { currCC with
            counters := currCC.counters.set sharer { destCntrs with ocnt := destCntrs.ocnt + 1 }
        }

        (n', ids', currCC')
    ) acc sharers


-- Helper to filter the shims and initiate the fold
def CCSendWriteToSharers {c : SystemConfig}
    (msg : Message c)
    (ts' : Timestamp)
    (msgSrcShim : ShimId c)
    (net : NETUnordered c)
    (msgIds : MessageIds c)
    (CC : CCMachine c)
    : NETUnordered c × MessageIds c × CCMachine c :=

    let allShims : List (ShimId c) := List.finRange c.threads

    -- Filter for shims that are sharing the address AND are not the source of the write
    let sharers : List (ShimId c) := allShims.filter (fun shim =>
        CC.cache[msg.addr].sharers[shim]! = true ∧ shim != msgSrcShim
    )

    foldSharersWrites sharers msg ts' (net, msgIds, CC)

-- Helper to send a WRITE_ACK if the operation is SC or the source is not yet a sharer
def CCSendWriteAck {c : SystemConfig}
    (msg : Message c)
    (ts' : Timestamp)
    (msgSrcShim : ShimId c)
    (net : NETUnordered c)
    (msgIds : MessageIds c)
    (CC : CCMachine c)
    : NETUnordered c × MessageIds c × CCMachine c :=

    if msg.stren = OpStrength.SC ∨ CC.cache[msg.addr].sharers[msgSrcShim]! = false then
        let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
        let lastWriteShim := CC.cache[msg.addr].lastWriteShim

        -- Type cast for indexing seenIds (assuming lastWriteShim < c.threads here)
        let lastWriteShimId : ShimId c := ⟨lastWriteShim.val, sorry⟩

        let srcSeen := (CC.seenIds[lastWriteShimId]).ccSeenIdsPerAddr[msg.addr]
        let destCntrs := CC.counters[msgSrcShim]

        -- Send the WRITE_ACK message
        let (net_ack, ids_ack) := send MType.WRITE_ACK CCNode msgSrcShim.castSucc msg.data msg.addr ts' msg.stren
            destCntrs.ocnt 0 -- 0 represents the empty fence count context here
            srcSeen.writeId srcSeen.seenId msg.qInd destCntrs.ccCounterElemPerAddr[msg.addr].localWriteCount net msgIds

        -- Increment ocnt for the source shim in the CC state
        let CC_ack := { CC with
            counters := CC.counters.set msgSrcShim { destCntrs with ocnt := destCntrs.ocnt + 1 }
        }

        (net_ack, ids_ack, CC_ack)
    else
        -- If conditions aren't met, return state unmodified
        (net, msgIds, CC)

def CCAddSrcShimToSharers {c : SystemConfig} (CC : CCMachine c) (msg : Message c) : CCMachine c :=
    if h : msg.src.val < c.threads.val then
        -- Safely cast the Node ID to a Shim ID using the proof 'h'
        let msgSrcShim : ShimId c := ⟨msg.src.val, h⟩

        -- Extract the current cache element for the message's address
        let cacheElem := CC.cache[msg.addr]

        -- Set the sharer boolean to true for this specific shim
        let updatedSharers := cacheElem.sharers.set msgSrcShim true

        -- Rebuild the nested state structures
        let updatedCacheElem := { cacheElem with sharers := updatedSharers }
        let updatedCache := CC.cache.set msg.addr updatedCacheElem

        { CC with cache := updatedCache }
    else
        panic! "Source of message to the CC was the CC itself (invalid shim ID)"

def CCReceive {c : SystemConfig} (msg : Message c) (CC : CCMachine c) (net : NETUnordered c) (msgIds : MessageIds c)
: (CCMachine c) × (NETUnordered c) × (MessageIds c) :=
    let CCNode : Node c := Fin.mk c.threads (Nat.lt_succ_self c.threads)
    match msg.mtype with
    | MType.WRITE =>
        if h : msg.src < c.threads.val then -- msg src is a shim
            let msgSrcShim : ShimId c := ⟨msg.src, h⟩
            -- 1. increment ts
            let ts' :=
                if CC.cache[msg.addr].ts >= msg.ts then
                    CC.cache[msg.addr].ts + 1
                else
                    msg.ts

            -- 2. always perform write -- Update Cache Data, TS, and lastWriteShim
            let CCElemData' : CCElemState c := { (CC.cache[msg.addr]) with
                data := msg.data,
                ts := ts',
                lastWriteShim := msg.src
            }
            let CCCache' : CCCache c := CC.cache.set msg.addr CCElemData'
            let CC' : CCMachine c := { CC with cache := CCCache' }

            -- 3. Update wCntr (mapped to localWriteCount in counters)
            let shimCntrs := CC'.counters.get msgSrcShim
            let addrCntr := shimCntrs.ccCounterElemPerAddr.get msg.addr
            let shimCntrs' := { shimCntrs with
                ccCounterElemPerAddr := shimCntrs.ccCounterElemPerAddr.set msg.addr
                    { addrCntr with localWriteCount := addrCntr.localWriteCount + 1 }
            }
            let CC'' := { CC' with counters := CC'.counters.set msgSrcShim shimCntrs' }

            -- 4. Update seenIds and seenPerShim logic
            let shimSeen := CC''.seenIds.get msgSrcShim
            let addrSeen := shimSeen.ccSeenIdsPerAddr.get msg.addr

            let newSeenId :=
                if msg.stren != OpStrength.RLX then
                    if shimSeen.seenPerShim > msg.seenId then shimSeen.seenPerShim else msg.seenId
                else
                    addrSeen.seenId

            let currentWId := CC''.wIdCounter

            let updatedAddrSeen := { addrSeen with
                seenId := newSeenId,
                writeId := currentWId
            }
            let shimSeen' := { shimSeen with
                ccSeenIdsPerAddr := shimSeen.ccSeenIdsPerAddr.set msg.addr updatedAddrSeen,
                seenPerShim := currentWId
            }

            -- Pack the updated seenIds AND the incremented wIdCounter into CC'''
            let CC''' := { CC'' with
                seenIds := CC''.seenIds.set msgSrcShim shimSeen',
                wIdCounter := currentWId + 1
            }

            -- 5. Send WRITE to sharers (except source)
            -- We fold over shims to handle the 'for' loop and ocnt increments
            -- 5. Send WRITE to sharers (except source)
            let (net', msgIds', CC'''') := CCSendWriteToSharers msg ts' msgSrcShim net msgIds CC'''

            -- 6. Send WRITE_ACK if SC or first write (msg.src not in sharers)
            -- only fields used in this msg are ts, data, ocnt, other fields not considered
            let (net'', msgIds'', CC''''') := CCSendWriteAck msg ts' msgSrcShim net' msgIds' CC''''

            -- 7. Add src to sharers
            let finalElem := CC'''''.cache[msg.addr]
            let CC_final := { CC''''' with
                cache := CC'''''.cache.set msg.addr { finalElem with
                    sharers := finalElem.sharers.set msgSrcShim true
                }
            }

            (CC_final, net'', msgIds'')

        else
            panic! "source of message to the CC was the CC??"
    | MType.RREQ =>
        if h : msg.src.val < c.threads.val then
            let msgSrcShim : ShimId c := ⟨msg.src.val, h⟩
            let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩

            -- 1. Add shim to sharers
            let CC' := CCAddSrcShimToSharers CC msg

            let lastWriteShim := CC'.cache[msg.addr].lastWriteShim
            let isInitialData := lastWriteShim.val == c.threads.val -- In Lean, CC node acts as '0' initial state

            let destCntrs := CC'.counters[msgSrcShim]
            let destFenceCnt := destCntrs.ccCounterElemPerAddr[msg.addr].fenceCount

            -- 2. Determine writeId, seenId, and seenPerShim updates
            let (wId, sId, updatedSeenPerShim) := if isInitialData then
                (0, 0, CC'.seenIds[msgSrcShim].seenPerShim)
            else
                let lastShimId : ShimId c := ⟨lastWriteShim.val, sorry⟩ -- Safe if not initial data
                let srcSeen := (CC'.seenIds[lastShimId]).ccSeenIdsPerAddr[msg.addr]

                let newSeenPerShim := if srcSeen.writeId > CC'.seenIds[msgSrcShim].seenPerShim then
                    srcSeen.writeId
                else
                    CC'.seenIds[msgSrcShim].seenPerShim

                (srcSeen.writeId, srcSeen.seenId, newSeenPerShim)

            -- 3. Send RRESP
            let (net', msgIds') := send MType.RRESP CCNode msg.src (CC'.cache[msg.addr]).data msg.addr (CC'.cache[msg.addr]).ts msg.stren
                destCntrs.ocnt destFenceCnt wId sId msg.qInd 0 net msgIds

            -- 4. Update CC counters and seenIds
            let shimSeen := CC'.seenIds[msgSrcShim]
            let CC'' := { CC' with
                seenIds := CC'.seenIds.set msgSrcShim { shimSeen with seenPerShim := updatedSeenPerShim },
                counters := CC'.counters.set msgSrcShim { destCntrs with ocnt := destCntrs.ocnt + 1 }
            }

            (CC'', net', msgIds')
        else
            panic! "source of RREQ was not a valid shim"

    | MType.FREQ =>
        if h : msg.src.val < c.threads.val then
            let msgSrcShim : ShimId c := ⟨msg.src.val, h⟩
            let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩

            -- 1. Broadcast FREQ to all OTHER shims
            let (net', msgIds', CC') := List.foldl (fun (n, ids, currCC) (shim : ShimId c) =>
                if shim.val != msgSrcShim.val then
                    let destCntrs := currCC.counters[shim]

                    -- Increment fence count
                    let addrCntr := destCntrs.ccCounterElemPerAddr[msg.addr]
                    let updatedAddrCntr := { addrCntr with fenceCount := addrCntr.fenceCount + 1 }
                    let updatedDestCntrs := { destCntrs with
                        ccCounterElemPerAddr := destCntrs.ccCounterElemPerAddr.set msg.addr updatedAddrCntr,
                        ocnt := destCntrs.ocnt + 1
                    }

                    -- Note: Lean sendFence does not take stren like Murphi does
                    let (n', ids') := sendFence MType.FREQ CCNode shim.castSucc destCntrs.ocnt n ids

                    let currCC' := { currCC with
                        counters := currCC.counters.set shim updatedDestCntrs
                    }
                    (n', ids', currCC')
                else
                    (n, ids, currCC)
            ) (net, msgIds, CC) (List.finRange c.threads)

            -- 2. Send FRESP to the requesting shim
            let srcCntrs := CC'.counters[msgSrcShim]
            let (net'', msgIds'') := sendFence MType.FRESP CCNode msg.src srcCntrs.ocnt net' msgIds'

            -- 3. Update CC ocnt for the source shim
            let CC'' := { CC' with
                counters := CC'.counters.set msgSrcShim { srcCntrs with ocnt := srcCntrs.ocnt + 1 }
            }

            (CC'', net'', msgIds'')
        else
            panic! "source of FREQ was not a valid shim"
    | _ => panic! "CC received message of invalid type"

def CCReceiveAndPopMsg {c : SystemConfig} (state : IncState c) : IncState c :=
    let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩
    let msg := (state.net[CCNode]).head!

    -- Verify the message source is a valid shim
    if h : msg.src.val < c.threads.val then
        let msgSrcShim : ShimId c := ⟨msg.src.val, h⟩
        let expectedIcnt := state.cc.counters[msgSrcShim].icnt

        -- Allow relaxed operations to bypass strict sequence enforcement
        let isRelaxed := msg.stren == OpStrength.RLX

        if msg.cnt = expectedIcnt ∨ isRelaxed then
            -- IN-ORDER or RELAXED: Process the message
            let (cc', net', msgIds') := CCReceive msg state.cc state.net state.msgIds

            -- Increment the CC's icnt ONLY if it matches the expected sequence.
            -- If we process an out-of-order RLX message, leave icnt alone
            -- so older bypassed messages do not fail the expectedIcnt check later.
            let shimCntrs := cc'.counters[msgSrcShim]
            let cc'' := if msg.cnt = expectedIcnt then
                { cc' with
                    counters := cc'.counters.set msgSrcShim { shimCntrs with icnt := shimCntrs.icnt + 1 }
                }
            else
                cc'

            let net'' := popMessage CCNode net'
            { state with cc := cc'', net := net'', msgIds := msgIds' }

        else
            -- OUT-OF-ORDER (and not relaxed): Push to the CC buffer and skip processing
            let ccBuf' := state.cc.buf ++ [msg]
            let cc' := { state.cc with buf := ccBuf' }
            let net' := popMessage CCNode state.net
            { state with cc := cc', net := net' }

    else
        panic! "CC received a message from an invalid source (not a shim)"

def CCReceiveAndPopMsgAt {c : SystemConfig} (state : IncState c) (msgIdx : Nat) : IncState c :=
    let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩
    let ccQueue := state.net[CCNode]

    if h_bounds : msgIdx < ccQueue.length then
        let msg := ccQueue[msgIdx] -- Valid due to the user's GetElem instance

        -- Verify the message source is a valid shim
        if h : msg.src.val < c.threads.val then
            let msgSrcShim : ShimId c := ⟨msg.src.val, h⟩
            let expectedIcnt := state.cc.counters[msgSrcShim].icnt
            let isRelaxed := msg.stren == OpStrength.RLX

            if msg.cnt = expectedIcnt ∨ isRelaxed then
                -- IN-ORDER or RELAXED
                let (cc', net', msgIds') := CCReceive msg state.cc state.net state.msgIds

                let shimCntrs := cc'.counters[msgSrcShim]
                let cc'' := if msg.cnt = expectedIcnt then
                    { cc' with
                        counters := cc'.counters.set msgSrcShim { shimCntrs with icnt := shimCntrs.icnt + 1 }
                    }
                else
                    cc'

                -- Remove the specific message instead of the head
                let newQueue := removeNth (net'[CCNode]) msgIdx
                let net'' := net'.set CCNode.val newQueue

                { state with cc := cc'', net := net'', msgIds := msgIds' }
            else
                -- OUT-OF-ORDER (and not relaxed): Push to buffer, remove from network
                let ccBuf' := state.cc.buf ++ [msg]
                let cc' := { state.cc with buf := ccBuf' }
                let newQueue := removeNth ccQueue msgIdx
                let net' := state.net.set CCNode.val newQueue
                { state with cc := cc', net := net' }
        else
            panic! "CC received a message from an invalid source"
    else
        state -- Fallback for invalid index

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
    -- getInstr sets the initial pend := true
    let (e', instr) := getInstr shim state.shimVec state.execution

    match instr.access with
    | PermissionType.load =>
        let (shimVec', net', e'', msgIds') := shimRead shim instr.addr instr.stren state.shimVec state.net e' state.msgIds
        {state with shimVec := shimVec', net := net', execution := e'', msgIds := msgIds'}

    | PermissionType.store =>
        let (shimVec', e'', net', msgIds') := shimWrite shim instr.addr instr.data instr.stren state.shimVec e' state.net state.msgIds
        {state with shimVec := shimVec', execution := e'', net := net', msgIds := msgIds'}

    | PermissionType.fence =>
        let (shimVec', net', e'', msgIds') := shimFence shim state.shimVec state.net state.msgIds e'
        {state with shimVec := shimVec', execution := e'', net := net', msgIds := msgIds'}

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
    -- | CCProcessMsg : forall (s s' : IncState c),
    --             (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)]).length > 0 →
    --             valid_CCReceive_MType (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)].head!).mtype →
    --             ↑(s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)].head!).src.val < (↑c.threads.val) →
    --             s' = CCReceiveAndPopMsg s →
    --             increment_step s s'
    | CCProcessMsg : forall (s s' : IncState c) (idx : Nat),
                idx < (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)]).length →
                valid_CCReceive_MType (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)][idx]!).mtype →
                ↑(s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)][idx]!).src.val < (↑c.threads.val) →
                s' = CCReceiveAndPopMsgAt s idx →
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

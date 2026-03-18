import MemglueVerification.memglueU

namespace LitmusTests

-- ============================================================
-- Bool decision procedures for protocol predicates
-- ============================================================

/-- Decidable version of canIssueInstr -/
def canIssueInstrBool {c : SystemConfig} (shimId : ShimId c) (state : IncState c) : Bool :=
  let s := state.shimVec[shimId]
  s.active && !s.fencePending && !s.pendingWSC &&
  !(state.execution[shimId].list[s.qInd]!).pend

/-- Decidable version of isDone -/
def isDoneBool {c : SystemConfig} (state : IncState c) : Bool :=
  let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩
  (state.net[CCNode]).isEmpty &&
  (List.finRange c.threads).all fun shim =>
    !canIssueInstrBool shim state && (state.net[shim.castSucc]).isEmpty

-- ============================================================
-- State-space exploration
-- ============================================================

/-- All IncStates reachable in one step from s, corresponding to the
    three constructors of increment_step plus the Finish transition. -/
def enabledSteps {c : SystemConfig} (state : IncState c) : List (IncState c) :=
  if state.done then []
  else
    let CCNode : Node c := ⟨c.threads, Nat.lt_succ_self c.threads⟩
    -- ProcessInstr: issue the next instruction on any active shim
    let instrSteps :=
      (List.finRange c.threads).filterMap fun shim =>
        if canIssueInstrBool shim state then some (getAndIssueInstr shim state) else none
    -- ShimProcessMsg: deliver the head message from any shim's inbox
    let shimMsgSteps :=
      (List.finRange c.threads).filterMap fun shim =>
        if !(state.net[shim.castSucc]).isEmpty then some (shimReceiveAndPopMsg shim state) else none
    -- CCProcessMsg: deliver the head message from the CC's inbox
    let ccMsgStep :=
      let ccMsgs := state.net[CCNode]
      if !ccMsgs.isEmpty &&
         valid_CCReceive_MType ccMsgs.head!.mtype &&
         decide (ccMsgs.head!.src.val < c.threads.val)
      then [CCReceiveAndPopMsg state] else []
    -- Finish: mark done when no further transitions are possible
    let finishStep :=
      if isDoneBool state then [{ state with done := true }] else []
    instrSteps ++ shimMsgSteps ++ ccMsgStep ++ finishStep

/-- BFS over all reachable states.  Uses a repr-string visited set to avoid
    re-exploring the same state.  fuel bounds the number of distinct states
    dequeued, preventing non-termination in case of bugs. -/
def reachableFinalStatesAux {c : SystemConfig}
    (fuel    : Nat)
    (queue   : List (IncState c))
    (visited : List String)
    (finals  : List (IncState c)) : List (IncState c) :=
  match fuel with
  | 0 => finals
  | n + 1 =>
    match queue with
    | [] => finals
    | s :: rest =>
      let key := reprStr s
      if visited.contains key then
        reachableFinalStatesAux n rest visited finals
      else
        let visited' := key :: visited
        if s.done then
          reachableFinalStatesAux n rest visited' (s :: finals)
        else
          let nexts := enabledSteps s
          reachableFinalStatesAux n (rest ++ nexts) visited' finals

def reachableFinalStates {c : SystemConfig}
    (init : IncState c) (fuel : Nat := 10000) : List (IncState c) :=
  reachableFinalStatesAux fuel [init] [] []

-- ============================================================
-- Outcome extraction
-- ============================================================

/-- For each thread, collect the final data values of completed load
    instructions in program order.  Stores do not appear in this list. -/
def readResults {c : SystemConfig} (s : IncState c) : Vector (List Data) c.threads :=
  s.execution.map fun threadInstrs =>
    threadInstrs.list.filterMap fun instr =>
      if instr.access == PermissionType.load then some instr.data else none

-- ============================================================
-- LitmusTest structure and runner
-- ============================================================

inductive LitmusOutcome where
  | Observable   : LitmusOutcome
  | Unobservable : LitmusOutcome
  deriving Repr, DecidableEq, BEq

/-- A litmus test bundles an execution (per-thread instruction list), a
    predicate on load results that encodes the forbidden outcome (analogous
    to the `exists` clause in .litmus files), and the expected outcome for
    regression checking. -/
structure LitmusTest (c : SystemConfig) where
  name      : String
  execution : Execution c
  /-- Returns true if the forbidden outcome has occurred.
      Argument: per-thread list of load result values, in program order. -/
  forbidden : Vector (List Data) c.threads → Bool
  /-- Documented expected outcome — used by printTestResult to flag regressions. -/
  expected  : LitmusOutcome

/-- The canonical initial IncState for a litmus test execution. -/
def makeInitState {c : SystemConfig} (e : Execution c) : IncState c :=
  { cc := default, shimVec := default, net := default,
    msgIds := default, execution := e, done := false }

/-- Run a litmus test: explore all reachable final states and check whether
    any of them satisfies the forbidden-outcome predicate. -/
def runLitmusTest {c : SystemConfig} (test : LitmusTest c) (fuel : Nat := 10000) : LitmusOutcome :=
  let init   := makeInitState test.execution
  let finals := reachableFinalStates init fuel
  if finals.any (fun s => test.forbidden (readResults s))
  then .Observable
  else .Unobservable

/-- Format a single test result, marking ✓ when the outcome matches expected. -/
def printTestResult {c : SystemConfig} (test : LitmusTest c) (fuel : Nat := 10000) : String :=
  let outcome := runLitmusTest test fuel
  let mark    := if outcome == test.expected then "pass" else "FAIL"
  s!"[{mark}] {test.name}: {repr outcome} (expected {repr test.expected})"

end LitmusTests

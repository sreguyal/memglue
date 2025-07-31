import MemglueVerification.memglueO
import MemglueVerification.c11

def increments_ts {c : SystemConfig} (s s' : IncState c) (shim : ShimId c) : Prop :=
  (s'.shimVec[shim].state[(getInstr shim s.shimVec s.execution).2.addr]).ts =
  (s.shimVec[shim].state[(getInstr shim s.shimVec s.execution).2.addr]).ts + 1

-- *local* writes increment timestamp
lemma local_W_inc_ts {c : SystemConfig} :
  forall (s s' : IncState c) (shim : ShimId c),
    canIssueInstr shim s →
    s' = getAndIssueInstr shim s →
    (getInstr shim s.shimVec s.execution).2.access = PermissionType.store →
    increment_step s s' →
    increments_ts s s' shim
  := by
    intro s s' shim h_issue h_s' h_W h_step
    unfold increments_ts

    rw [h_s']
    unfold getAndIssueInstr
    simp [h_W]
    unfold shimWrite
    simp

    split <;> unfold shimWriteCache <;> simp
    -- case isTrue =>
    --   unfold shimWriteCache
    --   simp
    -- case isFalse =>
    --   unfold shimWriteCache
    --   -- simp [List.Vector.get_set_same]
    --   simp
      -- simp [Vector.getElem_set_self shim.isLt]   -- this one

-- goal: show that any execution forbidden by c11 is also forbidden by memglue
-- for all eg's forbidden by c11, ¬ ∃ an end_state reachable via memglue with that corresponding execution
theorem memglue_respects_c11 {c : SystemConfig} :
  forall (eg : ExecutionGraph c),
    valid_exec_graph eg →
    ¬ rc11_consistent eg →
    ¬ exists (s : IncState c), eg.evts = executionToSet s.execution ∧
      end_state s
   := by
   intro eg h1 h2
   unfold rc11_consistent at h2
   simp only [not_and_or] at h2
   cases h2 with
   | inl h_co => sorry
   | inr h_rest => sorry

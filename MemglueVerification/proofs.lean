import MemglueVerification.memglueO
import MemglueVerification.c11

def w_instr_increments_ts {c : SystemConfig} (s s' : IncState c) (shim : ShimId c) : Prop :=
  (s'.shimVec[shim].state[(getInstr shim s.shimVec s.execution).2.addr]).ts =
  (s.shimVec[shim].state[(getInstr shim s.shimVec s.execution).2.addr]).ts + 1

-- *local* writes increment timestamp
lemma local_W_inc_ts {c : SystemConfig} :
  forall (s s' : IncState c) (shim : ShimId c),
    canIssueInstr shim s →
    s' = getAndIssueInstr shim s →
    (getInstr shim s.shimVec s.execution).2.access = PermissionType.store →
    increment_step s s' →
    w_instr_increments_ts s s' shim
  := by
    intro s s' shim h_issue h_s' h_W h_step
    unfold w_instr_increments_ts

    rw [h_s']
    unfold getAndIssueInstr
    simp [h_W]
    unfold shimWrite
    simp

    split <;> unfold shimWriteCache <;> simp

--------------------------------------------------------------
-- wts that when a message is added to the network, it has the greatest id out of all the messages in the queue
-- for that node.
lemma added_msg_greatest_id {c : SystemConfig} :
  forall (s : IncState c) (node : Node c) (i : Fin s.net[node].length),
    increment_reachable s →
    (s.net[node][i]).id < s.msgIds[node] := by
  intro s node i h
  induction h with
  | init _ =>
    exfalso
    simp at i
    dsimp [default] at i
    simp at i
    apply Fin.elim0 i
  | step s s' h1 h2 ih =>
    cases h2 with
      | ProcessInstr shim h_issue h_s' =>
        unfold getAndIssueInstr at h_s'
        simp at h_s'
        split at h_s'
        case h_1 =>
          unfold shimRead at h_s'
          simp at h_s'
          split at h_s'
          case isTrue =>
            simp at h_s'
            simp [h_s']
            have h_same_net_size : s'.net[node].length = s.net[node].length := by simp [h_s']
            change s.net[↑node][Fin.cast h_same_net_size i].id < s.msgIds[↑node]
            exact ih (Fin.cast h_same_net_size i)
          case isFalse =>
            simp [h_s']
            unfold send
            unfold netWithAddedMsg
            simp

            have h_cc_or_shim : (c.threads : Nat) = (node : Nat) ∨ (c.threads : Nat) ≠ (node : Nat) := by
              exact eq_or_ne (c.threads : Nat) (node : Nat)

            cases h_cc_or_shim with
            | inl h_cc =>
              simp [h_cc] at h_s' ⊢

              have h_i : i = s.net[node].length ∨ i < s.net[node].length ∨
                                                  i > s.net[node].length := by
                sorry

              have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                unfold send netWithAddedMsg at h_s'
                simp [h_s']

              cases h_i with
              | inl i_last =>
                have : i = Fin.mk s.net[node].length s_netlen_bound := by
                  exact Fin.eq_mk_iff_val_eq.mpr i_last
                simp [this]
              | inr i_not_last =>
                -- have : ¬ i = Fin.mk s.net[node].length s_netlen_bound := by
                --   exact Fin.ne_of_val_ne i_not_last


                -- have : i < Fin.mk s.net[node].length s_netlen_bound := by
                --   refine Fin.lt_def.mpr ?_
                --   simp [this, Fin.is_lt]

                  -- have : s.net[node].length < s'.net[node].length := by
                  --   unfold send netWithAddedMsg at h_s'
                  --   simp [h_s']
                -- simp [this]
                -- TODO continue.....
                sorry
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by
                simp [h_s']
                unfold send netWithAddedMsg
                simp [h_shim]
              sorry
              -- change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              -- exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
        case h_2 => sorry
        case h_3 => sorry
        case h_4 => sorry
      | ShimProcessMsg shim h_net h_s' => sorry
      | CCProcessMsg h_net h_s' => sorry
      | Finish h_false h_done h_s' => sorry

def net_ordered {c : SystemConfig} (net : NETOrdered c) : Prop :=
  forall (node : Node c) (i j : Fin net[node].length),
    i < j → (net[node][i]).id < (net[node][j]).id

lemma net_orderedness_prop {c : SystemConfig} :
  forall (s : IncState c),
    increment_reachable s →
    net_ordered s.net := by
    intro s h_s
    unfold net_ordered
    -- intro node i j h_ij
    induction h_s with
    | init _ =>
      intro node --i j h_ij
      dsimp [default]
      simp [Vector.getElem_replicate] at *
      have h_get : Fin (Vector.replicate (↑c.threads + 1) ([] : List (Message c)))[(node : Nat)].length = Fin 0 := by simp
      intro i j
      exfalso
      rw [h_get] at i j
      apply Fin.elim0 i
    | step s s' h1 h2 ih =>
      intro node i j h_ij

      cases h2 with
      | ProcessInstr shim h_issue h_s' =>
        unfold getAndIssueInstr at h_s'
        simp at h_s'
        split at h_s'
        case h_1 =>
          unfold shimRead at h_s'
          simp at h_s'
          split at h_s'
          case isTrue =>
            simp at h_s'
            have h_same_net : s'.net = s.net := by simp [h_s']
            simp [h_same_net]
            have h_same_net_size : s'.net[node].length = s.net[node].length := by simp [h_s']
            change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
            exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
          case isFalse =>
            simp [h_s']
            unfold send
            unfold netWithAddedMsg
            simp
            -- have h_cc_or_shim : node = ⟨c.threads, Nat.lt_succ_self c.threads⟩ ∨ node ≠ ⟨c.threads, Nat.lt_succ_self c.threads⟩ := by
              -- exact eq_or_ne node ⟨↑c.threads, Nat.lt_succ_self ↑c.threads⟩
            have h_cc_or_shim : (c.threads : Nat) = (node : Nat) ∨ (c.threads : Nat) ≠ (node : Nat) := by
              exact eq_or_ne (c.threads : Nat) (node : Nat)

            cases h_cc_or_shim with
            | inl h_cc =>
              simp [h_cc] at h_s' ⊢
              have h_j : j > s.net[node].length ∨ j < s.net[node].length ∨ j = s.net[node].length := by
                sorry
              cases h_j with
              | inl j_vac => sorry
              | inr j_right =>
                cases j_right with
                | inl j_not_last => sorry
                | inr j_last =>
                  have h_s_lt_s' : s.net[node].length < s'.net[node].length := by
                    unfold send netWithAddedMsg at h_s'
                    simp [h_s']
                  have h_j_eq_fin_s : j = Fin.mk s.net[node].length h_s_lt_s' := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [h_j_eq_fin_s]
                  have h_i_lt_s : ↑i < s.net[node].length := by
                    rw [← j_last]
                    exact h_ij

                  change ((s.net[↑node] ++
        [{ mtype := MType.RREQ, src := Fin.castSucc shim, dst := node,
            data := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  s.msgIds[↑node]
                  simp only [List.getElem_append_left h_i_lt_s]

                  change (s.net[node][i]).id < s.msgIds[node]
                  exact added_msg_greatest_id s node (Fin.mk i h_i_lt_s) h1
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by
                simp [h_s']
                unfold send netWithAddedMsg
                simp [h_shim]
              change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
        case h_2 =>
          unfold shimWrite at h_s'
          simp at h_s'
          split at h_s'
          -- TODO msg added case (WRITE message is sent to CC regardless of SC or not)
          case isTrue => sorry
          case isFalse => sorry
        case h_3 =>
          unfold shimFence at h_s'
          simp at h_s'
          -- TODO msg added case (sendFence is always called)
          sorry
        case h_4 h_none => -- !this case should never happen (trying to process instruction with access = none)

          unfold canIssueInstr at h_issue
          exfalso
          simp at *
          exact h_issue.right h_none
      | ShimProcessMsg shim h_net h_s' =>
          unfold shimReceiveAndPopMsg at h_s'
          simp at h_s'
          unfold popMessage at h_s'
          simp at h_s'
          simp [h_s']
          have : (shim : Nat) = (node : Nat) ∨ (shim : Nat) ≠ (node : Nat) := by
            exact eq_or_ne (shim : Nat) (node : Nat)
          cases this with
          | inl h_popped =>
            simp [h_popped] at h_s' h_net ⊢
            have : s'.net[node].length = s.net[node].tail.length := by
              simp [h_s']
            change s.net[↑node].tail[Fin.cast this i].id < s.net[↑node].tail[Fin.cast this j].id
            simp

            have : s'.net[node].length + 1 = s.net[node].length := by
              simp [h_s']
              exact Nat.sub_add_cancel h_net
            have i_succ_bound : forall (i : Fin (s'.net[node].length)), i + 1 < s.net[node].length := by
              rw [← this]
              simp
            change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.net[↑node][Fin.mk (j + 1) (i_succ_bound j)].id

            have h_ij' : Fin.mk (i + 1) (i_succ_bound i) < Fin.mk (j + 1) (i_succ_bound j) := by
              simp
              exact h_ij
            exact ih node ⟨↑i + 1, i_succ_bound i⟩ ⟨↑j + 1, i_succ_bound j⟩ h_ij'
          | inr h_no_change =>
            simp [h_no_change]
            have h_same_net_size : s'.net[node].length = s.net[node].length := by
              simp [h_s', h_no_change]
            change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
            exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
      | CCProcessMsg h_net h_s' => sorry
      | Finish h_false h_done h_s' =>
        simp [h_s']
        have h_same_net_size : s'.net[node].length = s.net[node].length := by
          simp [h_s']
        change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
        exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij

def w_msg_increments_ts {c : SystemConfig} (s s' : IncState c) (shim : ShimId c) : Prop :=
  s'.shimVec[shim].state[(s.net[shim]).head!.addr].ts =
  s.shimVec[shim].state[(s.net[shim]).head!.addr].ts + 1

def nonlocal_W_inc_ts {c : SystemConfig} :
  forall (s s' : IncState c) (shim : ShimId c),
    increment_reachable s →
    (s.net[(shim.castSucc)]).length > 0 →
    (s.net[shim]).head!.mtype = MType.WRITE →
    s' = shimReceiveAndPopMsg shim s →
    increment_step s s' →
    w_msg_increments_ts s s' shim := by
    intro s s' shim h_reach h_net h_W h_s' h_inc
    unfold w_msg_increments_ts
    rw [h_s']
    unfold shimReceiveAndPopMsg
    unfold shimReceive
    simp
    sorry -- add some sort of counter for nonlocal writes processed so far for each shim for each address?


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

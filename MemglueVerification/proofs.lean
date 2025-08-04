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
  forall (node : Node c) (s : IncState c),
    increment_reachable s →
    (forall (i j : Fin (s.net[node].length)), i < j → s.net[node][i].id < s.net[node][j].id) := by

  intro node s h_reach i
  induction h_reach with
  | init => sorry
  | step s s' h1 h2 ih => sorry
  -- cases h_step with
  -- | ProcessInstr shim h_issue h_s' =>
  --   unfold getAndIssueInstr at h_s'
  --   simp at h_s'
  --   split at h_s'
  --   case h_1 =>
  --     unfold shimRead at h_s'
  --     simp at h_s'
  --     split at h_s'
  --     case isTrue =>
  --       simp at h_s'
  --       -- have h_same_net : s'.net = s.net := by simp [h_s']
  --       -- simp [h_same_net]
  --       have h_same_net_size : s'.net[node].length = s.net[node].length := by simp [h_s']
  --       exfalso
  --       rw [h_same_net_size] at h_len
  --       exact (lt_self_iff_false s.net[node].length).mp h_len
  --     case isFalse =>
  --       simp [h_s']
  --       unfold send netWithAddedMsg
  --       simp
  --       have h_cc_or_shim : (c.threads : Nat) = (node : Nat) ∨ (c.threads : Nat) ≠ (node : Nat) := by
  --         exact eq_or_ne (c.threads : Nat) (node : Nat)

  --       cases h_cc_or_shim with
  --       | inl h_cc =>
  --         simp [h_cc] at h_s' ⊢
  --         simp [← h_cc]
  --         -- induction s.net[node].length with
  --         -- | zero => sorry
  --         -- | succ n ih_msg_list_len =>
  --         --   sorry
  --         sorry -- need to show that the message added has id greater than all the messages in the list
  --       | inr h_shim =>
  --         simp [h_shim]
  --         have h_same_net_size : s'.net[node].length = s.net[node].length := by
  --           simp [h_s']
  --           unfold send netWithAddedMsg
  --           simp [h_shim]
  --         -- change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
  --         -- exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
  --         sorry
  --   case h_2 => sorry
  --   case h_3 => sorry
  --   case h_4 => sorry
  -- | ShimProcessMsg shim h_net h_s' => sorry
  -- | CCProcessMsg h_net h_s' => sorry
  -- | Finish h_false h_done h_s' => sorry


  -- have : s'.net[node].length - 1 < s'.net[node].length := sorry


-- wts that network is ordered, that whenever we add a message, its index will be greater than that of all the messages in the list currently, and if we remove a message its index will be smaller than that of all the messages currently in the list.
/-def send {c : SystemConfig} (mtype' : MType) (src' : Node c) (dst' : Node c)
         (data' : Data) (addr' : Addr c) (ts' : Timestamp) (stren' : OpStrength)
         (net : NETOrdered c) (msgIds : MessageIds c)-/

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

              -- have : s.msgIds[↑node] > s.net[node][i]!.id := by
              --   sorry
              -- induction s.net[node].length with
              -- | zero => sorry
              -- | succ n ih_msg_list_len =>
              --   sorry
              sorry -- need to show that the message added has id greater than all the messages in the list
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by
                simp [h_s']
                unfold send netWithAddedMsg
                simp [h_shim]
              change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
        case h_2 => sorry
        case h_3 => sorry
        case h_4 => sorry

      | ShimProcessMsg shim h_net h_s' => sorry
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

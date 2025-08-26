import MemglueVerification.memglueO
import MemglueVerification.randomproofs
import MemglueVerification.c11

set_option maxHeartbeats 20000000

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

------------------------------------------------------------
-- preemptive proof that qInd stays within bounds
-- first show that any pair of states has the same length of list of instructions
-- lemma num_instr_constant {c : SystemConfig}:
--   forall (s s' : IncState c) (shim : ShimId c),
--     increment_reachable s →
--     increment_step s s' →
--     s'.execution[shim].list.length = s.execution[shim].list.length := by sorry

lemma qInd_in_bounds {c : SystemConfig} :
  forall (s : IncState c) (shim : ShimId c),
    increment_reachable s →
    s.shimVec[shim].qInd < s.execution[shim].list.length := by

    intro s shim_cons h_reach
    induction h_reach with
    | init e =>
      simp
      dsimp [default]
      simp
      refine List.length_pos_iff.mpr ?_
      exact e[↑shim_cons].nonempty

    | step s s' h1 h2 ih =>
      have nat_i_lt_cthreads : forall (i : ShimId c), (i : Nat) < ↑c.threads := by
          intro i
          exact i.isLt

      cases h2 with
      | ProcessInstr shim_instr h_issue h_s' =>
        have cons_instr_n_eq : ((shim_instr : Nat) = (shim_cons : Nat)) ∨ ((shim_instr : Nat) ≠ (shim_cons : Nat)) := by
          exact eq_or_ne (shim_instr : Nat) (shim_cons : Nat)

        have h_s'_copy := h_s'
        unfold getAndIssueInstr at h_s'
        simp at h_s'
        split at h_s'
        case h_1 => -- read
          unfold shimRead at h_s'
          simp at h_s'
          split at h_s'

          case isTrue => -- shim hit/miss
            unfold popInstr at h_s'
            simp at h_s' ⊢
            split at h_s'

            case isTrue h_qInd_bound => -- next qInd in bounds or out of bounds
              simp at h_s'

              cases cons_instr_n_eq with
              | inl h_cons_instr_eq =>
                simp [h_s', h_cons_instr_eq]
                simp [h_cons_instr_eq] at h_qInd_bound
                exact h_qInd_bound
              | inr h_cons_instr_neq =>
                simp [h_s', h_cons_instr_neq]
                unfold updateVal getInstr ; simp
                split
                case isTrue =>
                  simp [h_cons_instr_neq] ; exact ih
                case isFalse =>
                  simp [h_cons_instr_neq] ; exact ih

            case isFalse h_qInd_not_bound => -- next qInd out of bounds
              simp at h_s'

              cases cons_instr_n_eq with
              | inl h_cons_instr_eq =>
                simp [h_s', h_cons_instr_eq]
                unfold updateVal getInstr ; simp
                split
                case isTrue =>
                  simp [h_cons_instr_eq] ; exact ih
                case isFalse =>
                  simp [h_cons_instr_eq] ; exact ih

              | inr h_cons_instr_neq =>
                simp [h_s', h_cons_instr_neq]
                unfold updateVal getInstr ; simp
                split
                case isTrue =>
                  simp [h_cons_instr_neq] ; exact ih
                case isFalse =>
                  simp [h_cons_instr_neq] ; exact ih
          case isFalse => -- read miss
            simp [h_s']
            unfold getInstr ; simp
            cases cons_instr_n_eq with
            | inl h_cons_instr_eq =>
              simp [h_cons_instr_eq] ; exact ih
            | inr h_cons_instr_neq =>
              simp [h_cons_instr_neq] ; exact ih

        case h_2 => -- shim write instr
          unfold shimWrite at h_s'
          simp at h_s'
          split at h_s'
          case isTrue => -- sc strength write
            unfold popInstr at h_s'
            simp at h_s'
            split at h_s'
            case isTrue h_qInd_bound => -- next qInd in bounds
              simp [h_s']
              unfold getInstr at h_qInd_bound
              unfold shimWriteCache getInstr ; simp

              cases cons_instr_n_eq with
              | inl h_cons_instr_eq =>
                simp [h_cons_instr_eq]
                simp [h_cons_instr_eq] at h_qInd_bound
                exact h_qInd_bound
              | inr h_cons_instr_neq =>
                simp [h_cons_instr_neq] ; exact ih

            case isFalse h_qInd_not_bound => -- next qInd out of bounds
              simp at h_s'

              cases cons_instr_n_eq with
              | inl h_cons_instr_eq =>
                simp [h_s', h_cons_instr_eq]
                unfold shimWriteCache getInstr ; simp [h_cons_instr_eq]
                exact ih

              | inr h_cons_instr_neq =>
                simp [h_s']
                unfold shimWriteCache getInstr ; simp [h_cons_instr_neq]
                exact ih

          case isFalse => -- todo non-sc strength write. ↓ is the exact same as the sc case...
            unfold popInstr at h_s'
            simp at h_s'
            split at h_s'
            case isTrue h_qInd_bound => -- next qInd in bounds
              simp [h_s']
              unfold getInstr at h_qInd_bound
              unfold shimWriteCache getInstr ; simp

              cases cons_instr_n_eq with
              | inl h_cons_instr_eq =>
                simp [h_cons_instr_eq]
                simp [h_cons_instr_eq] at h_qInd_bound
                exact h_qInd_bound
              | inr h_cons_instr_neq =>
                simp [h_cons_instr_neq] ; exact ih

            case isFalse h_qInd_not_bound => -- next qInd out of bounds
              simp at h_s'

              cases cons_instr_n_eq with
              | inl h_cons_instr_eq =>
                simp [h_s', h_cons_instr_eq]
                unfold shimWriteCache getInstr ; simp [h_cons_instr_eq]
                exact ih

              | inr h_cons_instr_neq =>
                simp [h_s']
                unfold shimWriteCache getInstr ; simp [h_cons_instr_neq]
                exact ih
        case h_3 =>
          unfold shimFence at h_s'
          simp at h_s'
          simp [h_s']

          cases cons_instr_n_eq with
          | inl h_cons_instr_eq =>
            unfold getInstr ; simp [h_cons_instr_eq] ; exact ih
          | inr h_cons_instr_neq =>
            unfold getInstr ; simp [h_cons_instr_neq] ; exact ih
      | ShimProcessMsg shim_msg h_net h_s' =>
        have h_msg_cons_n_eq : (shim_msg : ℕ) = (shim_cons : ℕ) ∨ (shim_msg : ℕ) ≠ (shim_cons : ℕ) := by exact eq_or_ne (shim_msg : ℕ) (shim_cons : ℕ)
        unfold shimReceiveAndPopMsg popMessage shimReceive at h_s'
        simp at h_s' ih
        split at h_s'
        case isTrue =>        -- shimReceive msg to shim_msg (msg.dst was a valid shim)
          split at h_s'
          case h_1 =>     -- shim receive WRITE
            split at h_s'
            case isTrue =>        -- WRITE passes timestamp check
              unfold shimWriteCache at h_s'
              simp at h_s'
              simp [h_s']

              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [msg_cons_eq]
                exact ih
              | inr msg_cons_neq =>
                simp [msg_cons_neq]
                exact ih
            case isFalse =>       -- WRITE fails timestamp check
              unfold shimIncrTS at h_s' ; simp at h_s'
              simp [h_s']

              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [msg_cons_eq] ; exact ih
              | inr msg_cons_neq =>
                simp [msg_cons_neq] ; exact ih

          case h_2 =>       -- shimReceive WRITE_ACK
            split at h_s'
            case isTrue =>        -- WRITE_ACK syncbit for addr is on
              unfold shimWriteCache at h_s'
              simp at h_s'
              simp [h_s']

              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [msg_cons_eq] ; exact ih
              | inr msg_cons_neq =>
                simp [msg_cons_neq] ; exact ih
            case isFalse =>       -- WRITE_ACK syncbit off
              simp [h_s']

              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [msg_cons_eq] ; exact ih
              | inr msg_cons_neq =>
                simp [msg_cons_neq] ; exact ih
          case h_3 =>         -- shimReceive RRESP
            unfold popInstr shimWriteCache at h_s' ; simp at h_s'
            split at h_s'
            case isTrue h_qInd_succ =>          -- next qInd in bounds
              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [h_s']
                simp [msg_cons_eq] at h_qInd_succ ⊢
                exact h_qInd_succ
              | inr msg_cons_neq =>
                simp [h_s', msg_cons_neq]
                have : (updateVal shim_msg s.net[(shim_msg : Nat)].head!.data s.execution s.shimVec)[(shim_cons : Nat)].list.length =
                       s.execution[↑shim_cons].list.length := by
                  unfold updateVal ; simp
                  split
                  case isTrue => simp [msg_cons_neq]
                  case isFalse => rfl
                simp [this] ; exact ih
            case isFalse =>         -- qInd not incr (at end)
              simp [h_s']

              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [msg_cons_eq]
                unfold updateVal ; simp
                split
                case isTrue =>
                  simp [msg_cons_eq]
                  exact ih
                case isFalse =>
                  exact ih
              | inr msg_cons_neq =>
                simp [msg_cons_neq]
                unfold updateVal ; simp
                split
                case isTrue => simp [msg_cons_neq] ; exact ih
                case isFalse => exact ih
          case h_4 =>       -- shimReceive FRESP
            split at h_s'
            case isTrue =>        -- FRESP not pending WSC
              unfold popInstr at h_s' ; simp at h_s'

              split at h_s'
              case isTrue h_qInd =>        -- qInd in bounds
                simp [h_s']
                cases h_msg_cons_n_eq with
                | inl msg_cons_eq =>
                  simp [msg_cons_eq] at h_qInd ⊢ ; exact h_qInd
                | inr msg_cons_neq =>
                  simp [msg_cons_neq] ; exact ih

              case isFalse =>       -- qInd at end
                simp [h_s']
                cases h_msg_cons_n_eq with
                | inl msg_cons_eq =>
                  simp [msg_cons_eq] ; exact ih
                | inr msg_cons_neq =>
                  simp [msg_cons_neq] ; exact ih

            case isFalse =>         -- FRESP WSC = true
              cases h_msg_cons_n_eq with
              | inl msg_cons_eq =>
                simp [h_s', msg_cons_eq] ; exact ih
              | inr msg_cons_neq =>
                simp [h_s', msg_cons_neq] ; exact ih

          case h_5 =>       -- error/panic case
            cases h_msg_cons_n_eq with
            | inl msg_cons_eq =>
              simp [h_s', msg_cons_eq]
              dsimp [default]
              simp
            | inr msg_cons_neq =>
              simp [h_s']
              dsimp [default]
              simp

        case isFalse =>     -- shimReceive error, msg.dst was cc, not shim..
          cases h_msg_cons_n_eq with
            | inl msg_cons_eq =>
              simp [h_s', msg_cons_eq]
              dsimp [default]
              simp
            | inr msg_cons_neq =>
              simp [h_s']
              dsimp [default]
              simp

      | CCProcessMsg h_net _ _ h_s' =>
        unfold CCReceiveAndPopMsg at h_s' ; simp at h_s'
        simp [h_s'] ; exact ih

      | Finish h_false h_done h_s' =>
        simp [h_s'] ; exact ih










--------------------------------------------------------------

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
      have h_cc_or_shim : (c.threads : Nat) = (node : Nat) ∨ (c.threads : Nat) ≠ (node : Nat) := by exact eq_or_ne (c.threads : Nat) (node : Nat)
      have h_j : j < s.net[node].length ∨ j = s.net[node].length ∨ s.net[node].length < j := by
                exact Nat.lt_trichotomy (↑j) s.net[node].length

      cases h2 with
      | ProcessInstr shim h_issue h_s' =>
        unfold getAndIssueInstr at h_s'
        simp at h_s'
        split at h_s'
        case h_1 =>     -- read instr
          unfold shimRead at h_s'
          simp at h_s'
          split at h_s'
          case isTrue =>      -- read hit so net no change
            simp at h_s'
            have h_same_net : s'.net = s.net := by simp [h_s']
            simp [h_same_net]
            have h_same_net_size : s'.net[node].length = s.net[node].length := by simp [h_s']
            change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
            exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
          case isFalse =>     -- read miss
            simp [h_s']
            unfold send
            unfold netWithAddedMsg
            simp
            -- have h_cc_or_shim : node = ⟨c.threads, Nat.lt_succ_self c.threads⟩ ∨ node ≠ ⟨c.threads, Nat.lt_succ_self c.threads⟩ := by
              -- exact eq_or_ne node ⟨↑c.threads, Nat.lt_succ_self ↑c.threads⟩


            cases h_cc_or_shim with
            | inl h_cc =>
              simp [h_cc] at h_s' ⊢

              have h_s_lt_s' : s.net[node].length < s'.net[node].length := by
                unfold send netWithAddedMsg at h_s'
                simp [h_s']

              cases h_j with
              | inl j_not_last =>
                have h_i_lt_s : ↑i < s.net[node].length := by
                  exact Nat.lt_trans h_ij j_not_last
                simp
                -- let msg :=
                change ((s.net[node] ++
        [{ mtype := MType.RREQ, src := Fin.castSucc shim, dst := node,
            data := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  ((s.net[node] ++
        [{ mtype := MType.RREQ, src := Fin.castSucc shim, dst := node,
            data := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(j : Nat)]'(by simp; exact Nat.lt_add_right 1 j_not_last)).id

                simp only [List.getElem_append_left h_i_lt_s]
                simp only [List.getElem_append_left j_not_last]
                simp at ih ⊢
                exact ih node (Fin.mk i h_i_lt_s) (Fin.mk j j_not_last) h_ij
              | inr j_right =>
                cases j_right with
                | inl j_last =>
                  have h_j_eq_fin_s : j = Fin.mk s.net[node].length h_s_lt_s' := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [h_j_eq_fin_s]
                  have h_i_lt_s : ↑i < s.net[node].length := by
                    rw [← j_last]
                    exact h_ij

                  change ((s.net[node] ++
        [{ mtype := MType.RREQ, src := Fin.castSucc shim, dst := node,
            data := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  s.msgIds[↑node]
                  simp only [List.getElem_append_left h_i_lt_s]

                  change (s.net[node][i]).id < s.msgIds[node]
                  exact added_msg_greatest_id s node (Fin.mk i h_i_lt_s) h1
                | inr j_vac =>
                  exfalso
                  have hj1 : j < s.net[node].length + 1 := by
                    have : j < s'.net[node].length := by exact j.isLt
                    simp [h_s'] at this
                    unfold send netWithAddedMsg at this ; simp at this
                    exact this
                  have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                  have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                  rw [hj3] at j_vac
                  exact (lt_self_iff_false s.net[node].length).mp j_vac
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by
                simp [h_s']
                unfold send netWithAddedMsg
                simp [h_shim]
              change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
        case h_2 =>                   -- shimWrite instr
          unfold shimWrite at h_s'
          simp at h_s'
          split at h_s'

          case isTrue =>          -- shimWrite instr SC stren
            simp [h_s'] ; unfold send netWithAddedMsg ; simp
            cases h_cc_or_shim with
            | inl h_cc =>
              simp [h_cc]
              have h_s_lt_s' : s.net[node].length < s'.net[node].length := by
                unfold send netWithAddedMsg at h_s'
                simp [h_s', h_cc]

              cases h_j with
              | inl j_not_last =>
                have h_i_lt_s : ↑i < s.net[node].length := by
                  exact Nat.lt_trans h_ij j_not_last

                simp
                -- let msg :=
                change ((s.net[node] ++
        [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  ((s.net[node] ++
        [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(j : Nat)]'(by simp; exact Nat.lt_add_right 1 j_not_last)).id

                simp only [List.getElem_append_left h_i_lt_s, List.getElem_append_left j_not_last]
                simp at ih ⊢
                exact ih node (Fin.mk i h_i_lt_s) (Fin.mk j j_not_last) h_ij
              | inr j_right =>
                cases j_right with
                | inl j_last =>
                  have h_j_eq_fin_s : j = Fin.mk s.net[node].length h_s_lt_s' := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [h_j_eq_fin_s]
                  have h_i_lt_s : ↑i < s.net[node].length := by
                    rw [← j_last]
                    exact h_ij

                  change ((s.net[node] ++
        [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  s.msgIds[↑node]
                  simp only [List.getElem_append_left h_i_lt_s]

                  change (s.net[node][i]).id < s.msgIds[node]
                  exact added_msg_greatest_id s node (Fin.mk i h_i_lt_s) h1
                | inr j_vac =>
                  exfalso
                  have hj1 : j < s.net[node].length + 1 := by
                    have : j < s'.net[node].length := by exact j.isLt
                    simp [h_s'] at this
                    unfold send netWithAddedMsg at this ; simp [h_cc] at this
                    exact this
                  have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                  have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                  rw [hj3] at j_vac
                  exact (lt_self_iff_false s.net[node].length).mp j_vac
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by
                simp [h_s']
                unfold send netWithAddedMsg
                simp [h_shim]
              change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
          case isFalse =>         -- shimWrite instr non SC stren -- todo below is exactly the same as shimWrite for SC case...
            simp [h_s'] ; unfold send netWithAddedMsg ; simp
            cases h_cc_or_shim with
            | inl h_cc =>
              simp [h_cc]
              have h_s_lt_s' : s.net[node].length < s'.net[node].length := by
                unfold send netWithAddedMsg at h_s'
                simp [h_s', h_cc]

              cases h_j with
              | inl j_not_last =>
                have h_i_lt_s : ↑i < s.net[node].length := by
                  exact Nat.lt_trans h_ij j_not_last

                simp
                -- let msg :=
                change ((s.net[node] ++
        [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  ((s.net[node] ++
        [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(j : Nat)]'(by simp; exact Nat.lt_add_right 1 j_not_last)).id

                simp only [List.getElem_append_left h_i_lt_s, List.getElem_append_left j_not_last]
                simp at ih ⊢
                exact ih node (Fin.mk i h_i_lt_s) (Fin.mk j j_not_last) h_ij
              | inr j_right =>
                cases j_right with
                | inl j_last =>
                  have h_j_eq_fin_s : j = Fin.mk s.net[node].length h_s_lt_s' := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [h_j_eq_fin_s]
                  have h_i_lt_s : ↑i < s.net[node].length := by
                    rw [← j_last]
                    exact h_ij

                  change ((s.net[node] ++
        [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
            addr := (getInstr shim s.shimVec s.execution).2.addr,
            ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
            stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  s.msgIds[↑node]
                  simp only [List.getElem_append_left h_i_lt_s]

                  change (s.net[node][i]).id < s.msgIds[node]
                  exact added_msg_greatest_id s node (Fin.mk i h_i_lt_s) h1
                | inr j_vac =>
                  exfalso
                  have hj1 : j < s.net[node].length + 1 := by
                    have : j < s'.net[node].length := by exact j.isLt
                    simp [h_s'] at this
                    unfold send netWithAddedMsg at this ; simp [h_cc] at this
                    exact this
                  have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                  have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                  rw [hj3] at j_vac
                  exact (lt_self_iff_false s.net[node].length).mp j_vac
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by
                simp [h_s']
                unfold send netWithAddedMsg
                simp [h_shim]
              change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij
        case h_3 =>
          unfold shimFence sendFence netWithAddedMsg at h_s' ; simp at h_s'
          simp [h_s']

          cases h_cc_or_shim with
            | inl h_cc =>
              simp [h_cc]
              have h_s_lt_s' : s.net[node].length < s'.net[node].length := by simp [h_s', h_cc]

              cases h_j with
              | inl j_not_last =>
                have h_i_lt_s : ↑i < s.net[node].length := by exact Nat.lt_trans h_ij j_not_last

                simp
                -- let msg :=
                change ((s.net[node] ++
        [{ mtype := MType.FREQ, src := Fin.castSucc shim, dst := node, data := (default : Message c).data, addr := (default : Message c).addr,
            ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  ((s.net[node] ++
        [{ mtype := MType.FREQ, src := Fin.castSucc shim, dst := node, data := (default : Message c).data, addr := (default : Message c).addr,
            ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node] }])[(j : Nat)]'(by simp; exact Nat.lt_add_right 1 j_not_last)).id

                simp only [List.getElem_append_left h_i_lt_s, List.getElem_append_left j_not_last]
                simp at ih ⊢
                exact ih node (Fin.mk i h_i_lt_s) (Fin.mk j j_not_last) h_ij
              | inr j_right =>
                cases j_right with
                | inl j_last =>
                  have h_j_eq_fin_s : j = Fin.mk s.net[node].length h_s_lt_s' := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [h_j_eq_fin_s]
                  have h_i_lt_s : ↑i < s.net[node].length := by
                    rw [← j_last]
                    exact h_ij

                  change ((s.net[node] ++
        [{ mtype := MType.FREQ, src := Fin.castSucc shim, dst := node, data := (default : Message c).data, addr := (default : Message c).addr,
            ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node] }])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 h_i_lt_s)).id <
  s.msgIds[↑node]
                  simp only [List.getElem_append_left h_i_lt_s]

                  change (s.net[node][i]).id < s.msgIds[node]
                  exact added_msg_greatest_id s node (Fin.mk i h_i_lt_s) h1
                | inr j_vac =>
                  exfalso
                  have hj1 : j < s.net[node].length + 1 := by
                    have : j < s'.net[node].length := by exact j.isLt
                    simp [h_s'] at this
                    simp [h_cc] at this
                    exact this
                  have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                  have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                  rw [hj3] at j_vac
                  exact (lt_self_iff_false s.net[node].length).mp j_vac
            | inr h_shim =>
              simp [h_shim]
              have h_same_net_size : s'.net[node].length = s.net[node].length := by simp [h_s', h_shim]

              change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
              exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij

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
      | CCProcessMsg h_net h_valid_mtype h_ccreceive_from_shim h_s' =>
        simp [h_s']
        unfold CCReceiveAndPopMsg CCReceive ; simp

        let mtype := s.net[(c.threads : Nat)].head!.mtype
        cases h : mtype

        case WRITE =>
          dsimp [mtype] at h
          simp [h]
          split
          case isTrue h_src_is_shim =>  -- CCReceive msg from shim
            split
            case isTrue h_sc_first =>      -- WRITE SC or first
              cases h_cc_or_shim with
              | inl h_cc =>
                unfold CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg popMessage
                simp [h_cc]

                have h_node_not_sharer : !(((List.filter
                  (fun shim ↦
                    !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                      (s.cc.cache[↑s.net[↑node.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))
                  (List.finRange (↑c.threads + 1)))).contains node) := by simp

                have h_fold :
                  let res :=
                  (foldSharers
                  (List.filter
                    (fun shim ↦
                      !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                        (s.cc.cache[↑(s.net[↑node.val].head!.addr).val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))

                  (List.finRange (↑c.threads + 1)))

                    s.net[↑node.val].head! s.net s.msgIds
                  ({
                    cache :=
                      Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                        { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                  } : CCMachine c));
                  res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] :=

                  foldNonSharersLemma s node (List.filter
                    (fun shim ↦
                      !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                        (s.cc.cache[↑s.net[↑node.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))
                    (List.finRange (↑c.threads + 1)))
                    s.net[↑node.val].head!
                    (s.net, s.msgIds)
                    h_node_not_sharer
                    (by simp) (by simp)

                simp [h_cc] at h_fold
                -- simp [h_fold]

                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at h_s' ; simp [h, h_src_is_shim, h_sc_first] at h_s'

                have node_not_src :  ↑s.net[↑node.val].head!.src.val ≠ ↑node.val := by
                  simp only [h_cc] at h_src_is_shim
                  exact Nat.ne_of_lt h_src_is_shim

                simp [node_not_src, h_fold]     -- h_sc_first

                have : s'.net[node].length = s.net[node].tail.length := by
                  simp [h_s']
                  -- unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_sc_first]
                  simp [h_cc]
                  simp [node_not_src, h_fold.left]

                change s.net[↑node].tail[Fin.cast this i].id < s.net[↑node].tail[Fin.cast this j].id
                simp

                have : s'.net[node].length + 1 = s.net[node].length := by
                  simp [h_s']
                  -- unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_sc_first]
                  simp [h_cc]
                  simp [node_not_src, h_fold.left]
                  refine Nat.sub_add_cancel ?_
                  simp [h_cc] at h_net
                  exact h_net
                have i_succ_bound : forall (i : Fin (s'.net[node].length)), i + 1 < s.net[node].length := by
                  rw [← this]
                  simp

                change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.net[↑node][Fin.mk (j + 1) (i_succ_bound j)].id
                have : Fin.mk (↑i + 1) (i_succ_bound i) < Fin.mk (↑j + 1) (i_succ_bound j) := by
                  simp at h_ij ⊢
                  exact h_ij
                exact ih node ⟨↑i + 1, i_succ_bound i⟩ ⟨↑j + 1, i_succ_bound j⟩ this
              | inr h_shim =>
                unfold CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg popMessage
                simp [h_shim]

                let is_src := decide (↑node.val = ↑s.net[↑c.threads.val].head!.src.val)
                let is_sharer := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑node]!

                cases h_is_src : is_src
                case true =>          -- node = src → WRITE_ACK sent, no WRITE message will be sent to node
                  dsimp [is_src] at h_is_src
                  have h_node_not_sharer : !((List.filter
                    (fun shim ↦
                      !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                        (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                    (List.finRange (↑c.threads + 1))).contains node) := by
                      --dsimp [is_src] at h_is_src ;
                      -- simp at h_is_src
                      simp [h_is_src]

                  have h_fold :
                    let res :=
                      (foldSharers
                      (List.filter
                        (fun shim ↦
                          !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                            (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1)))
                      s.net[↑c.threads.val].head! s.net s.msgIds
                      {
                        cache :=
                          Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                            { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                              sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                      }) ;
                    res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] :=

                    foldNonSharersLemma s node
                        (List.filter
                        (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1)))
                      s.net[↑c.threads.val].head!
                      (s.net, s.msgIds)
                      h_node_not_sharer
                      (by simp) (by simp)
                  -- dsimp [is_src] at h_is_src ;
                  simp at h_is_src
                  simp [h_is_src.symm] at h_fold
                  simp [h_is_src.symm, h_fold]
                  -- simp []

                  have h_j : (j : Nat) < s.net[node].length ∨ (j : Nat) = s.net[node].length ∨
                                            s.net[node].length < (j : Nat) := by
                    exact Nat.lt_trichotomy (↑j) s.net[node].length


                  unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at h_s' ; simp [h, h_src_is_shim, h_sc_first] at h_s'
                  have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                    simp [h_s', h_shim, h_is_src.symm, h_fold]

                  change (i.val < j.val) at h_ij

                  cases h_j with
                  | inl j_not_last =>
                    have i_not_last : i.val < s.net[node].length := by exact Nat.lt_trans h_ij j_not_last
                    change ((s.net[↑node] ++ [({ mtype := MType.WRITE_ACK, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 i_not_last)).id <
                           ((s.net[↑node] ++ [({ mtype := MType.WRITE_ACK, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(j : Nat)]'(by simp; exact Nat.lt_add_right 1 j_not_last)).id
                    simp only [List.getElem_append_left i_not_last, List.getElem_append_left j_not_last]
                    change s.net[node][Fin.mk i i_not_last].id < s.net[node][Fin.mk j j_not_last].id

                    change (Fin.mk i i_not_last) < (Fin.mk j j_not_last) at h_ij
                    exact ih node (Fin.mk i i_not_last) (Fin.mk j j_not_last) h_ij
                  | inr j_last_or_vac =>
                    cases j_last_or_vac with
                    | inl j_last =>
                      have : j = Fin.mk s.net[node].length s_netlen_bound := by
                        exact Fin.eq_mk_iff_val_eq.mpr j_last
                      simp [this]
                      have : i.val < s.net[↑node.val].length := by change (i.val < s.net[node].length) ; rw [←j_last] ; exact h_ij
                      change ((s.net[↑node] ++ [({ mtype := MType.WRITE_ACK, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 this)).id <
                             s.msgIds[↑node]
                      simp [this]
                      exact added_msg_greatest_id s node (Fin.mk i this) h1
                      -- apply added_msg_greatest_id?
                    | inr j_vac =>
                      exfalso
                      have hj1 : j < s.net[node].length + 1 := by
                        have : j < s'.net[node].length := by exact j.isLt
                        simp [h_s', h_shim, h_is_src.symm, h_fold] at this
                        -- unfold send netWithAddedMsg at this ; simp at this
                        exact this
                      have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                      have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                      rw [hj3] at j_vac
                      exact (lt_self_iff_false s.net[node].length).mp j_vac

                case false =>         -- node is shim and ≠ src → message sent if sharer, otherwise no
                  dsimp [is_src] at h_is_src ; simp at h_is_src

                  cases h_is_sharer : is_sharer
                  case true =>        -- WRITE sent to node b/c node is shim and ≠ src and sharer
                    dsimp [is_sharer] at h_is_sharer

                    have h_node_sharer : (List.filter
                      (fun shim ↦
                      !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                        (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                      (List.finRange (↑c.threads + 1))).contains node := by
                      simp
                      -- dsimp [is_src] at h_is_src; simp at h_is_src
                      -- dsimp [is_sharer] at h_is_sharer
                      have : ¬↑node.val = ↑c.threads := by
                        simp [h_shim.symm]

                      apply And.intro
                      case left => exact h_is_src
                      case right =>
                        apply And.intro
                        case left => exact h_is_sharer
                        case right => exact this

                    have h_sharer_list_nodup : List.Nodup (List.filter
                        (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1))) := by
                        exact List.Nodup.filter (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val))) (List.nodup_finRange (↑c.threads + 1))

                    have h_fold := foldSharersLemma s node (List.filter
                        (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1)))
                      -- s.net[↑c.threads.val].head!
                      (s.net, s.msgIds)
                      h_shim.symm
                      h_sharer_list_nodup
                      h_node_sharer
                      (by simp) (by simp)
                    simp at h_fold
                    simp [(Ne.intro h_is_src).symm, h_fold]  -- todo here now 8/18

                    -- have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                    --   simp [h_s']
                    --   unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_sc_first]
                    --   simp [h_shim, h_fold]
                    unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at h_s' ; simp [h, h_src_is_shim, h_sc_first] at h_s'
                    have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                      simp [h_s', h_shim, (Ne.intro h_is_src).symm, h_fold]

                    cases (Nat.lt_trichotomy (↑j) s.net[node].length) with
                    | inl j_not_last =>
                      have i_not_last : i.val < s.net[node].length := by exact Nat.lt_trans h_ij j_not_last
                      change ((s.net[↑node] ++ [({ src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := node, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 i_not_last)).id <
                             ((s.net[↑node] ++ [({ src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := node, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(j : Nat)]'(by simp; exact Nat.lt_add_right 1 j_not_last)).id
                      simp only [List.getElem_append_left i_not_last, List.getElem_append_left j_not_last]
                      change s.net[node][Fin.mk i i_not_last].id < s.net[node][Fin.mk j j_not_last].id

                      change (Fin.mk i i_not_last) < (Fin.mk j j_not_last) at h_ij
                      exact ih node (Fin.mk i i_not_last) (Fin.mk j j_not_last) h_ij
                    | inr j_last_or_vac =>    -- todo here 8/20
                      cases j_last_or_vac with
                      | inl j_last =>
                        have : j = Fin.mk s.net[node].length s_netlen_bound := by
                          exact Fin.eq_mk_iff_val_eq.mpr j_last
                        simp [this]
                        have : i.val < s.net[↑node.val].length := by change (i.val < s.net[node].length) ; rw [←j_last] ; exact h_ij
                        change ((s.net[↑node] ++ [({ src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := node, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 this)).id <
                              s.msgIds[↑node]
                        simp [this]
                        exact added_msg_greatest_id s node (Fin.mk i this) h1
                        -- apply added_msg_greatest_id?
                      | inr j_vac =>
                        exfalso
                        have hj1 : j < s.net[node].length + 1 := by
                          have : j < s'.net[node].length := by exact j.isLt
                          simp [h_s', h_shim, (Ne.intro h_is_src).symm, h_fold] at this
                          -- unfold send netWithAddedMsg at this ; simp at this
                          exact this
                        have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                        have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                        rw [hj3] at j_vac
                        exact (lt_self_iff_false s.net[node].length).mp j_vac

                  case false =>       -- no msg sent b/c node not sharer

                    have h_node_not_sharer : !((List.filter
                      (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                      (List.finRange (↑c.threads + 1))).contains node) := by
                        dsimp [is_sharer] at h_is_sharer
                        simp [h_is_sharer]

                    have h_fold :
                      let res :=
                        (foldSharers
                        (List.filter
                          (fun shim ↦
                            !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                              (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                          (List.finRange (↑c.threads + 1)))
                        s.net[↑c.threads.val].head! s.net s.msgIds
                        {
                          cache :=
                            Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                              { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                                sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                        }) ;
                      res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] :=

                      foldNonSharersLemma s node
                          (List.filter
                          (fun shim ↦
                          !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                            (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                          (List.finRange (↑c.threads + 1)))
                        s.net[↑c.threads.val].head!
                        (s.net, s.msgIds)
                        h_node_not_sharer
                        (by simp) (by simp)

                    simp [(Ne.intro h_is_src).symm, h_fold]

                    have : s'.net[node].length = s.net[node].length := by
                      simp [h_s']
                      unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_sc_first]
                      simp [h_shim, (Ne.intro h_is_src).symm, h_fold]

                    change s.net[node][Fin.cast this i].id < s.net[node][Fin.cast this j].id
                    change (i < j) at h_ij
                    exact ih node (Fin.cast this i) (Fin.cast this j) h_ij






            case isFalse h_not_sc_first =>       -- WRITE not SC or first
              cases h_cc_or_shim with
              | inl h_cc =>
                unfold CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg popMessage
                simp [h_cc]

                have h_node_not_sharer : !(((List.filter
                  (fun shim ↦
                    !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                      (s.cc.cache[↑s.net[↑node.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))
                  (List.finRange (↑c.threads + 1)))).contains node) := by simp

                have h_fold :
                  let res :=
                  (foldSharers
                  (List.filter
                    (fun shim ↦
                      !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                        (s.cc.cache[↑(s.net[↑node.val].head!.addr).val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))

                  (List.finRange (↑c.threads + 1)))

                    s.net[↑node.val].head! s.net s.msgIds
                  ({
                    cache :=
                      Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                        { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                  } : CCMachine c));
                  res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] :=

                  foldNonSharersLemma s node (List.filter
                    (fun shim ↦
                      !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                        (s.cc.cache[↑s.net[↑node.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))
                    (List.finRange (↑c.threads + 1)))
                    s.net[↑node.val].head!
                    (s.net, s.msgIds)
                    h_node_not_sharer
                    (by simp) (by simp)

                simp [h_cc] at h_fold
                simp [h_fold]



                have : s'.net[node].length = s.net[node].tail.length := by
                  simp [h_s']
                  unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_not_sc_first]
                  simp [h_cc]
                  simp [h_fold.left]

                change s.net[↑node].tail[Fin.cast this i].id < s.net[↑node].tail[Fin.cast this j].id
                simp

                have : s'.net[node].length + 1 = s.net[node].length := by
                  simp [h_s']
                  unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_not_sc_first]
                  simp [h_cc]
                  simp [h_fold.left]
                  refine Nat.sub_add_cancel ?_
                  simp [h_cc] at h_net
                  exact h_net
                have i_succ_bound : forall (i : Fin (s'.net[node].length)), i + 1 < s.net[node].length := by
                  rw [← this]
                  simp

                change s.net[node][Fin.mk (i + 1) (i_succ_bound i)].id < s.net[node][Fin.mk (j + 1) (i_succ_bound j)].id
                exact ih node (Fin.mk (i + 1) (i_succ_bound i)) (Fin.mk (j + 1) (i_succ_bound j)) (Nat.succ_lt_succ h_ij)
              | inr h_shim =>
                unfold CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg popMessage
                simp [h_shim]

                let is_src := decide (↑node.val = ↑s.net[↑c.threads.val].head!.src.val)
                let is_sharer := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑node]!

                cases h_is_src : is_src
                case true =>          -- node = src → no message will be sent to node

                  have h_node_not_sharer : !((List.filter
                    (fun shim ↦
                      !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                        (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                    (List.finRange (↑c.threads + 1))).contains node) := by
                      dsimp [is_src] at h_is_src ; simp at h_is_src
                      simp [h_is_src]

                  have h_fold :
                    let res :=
                      (foldSharers
                      (List.filter
                        (fun shim ↦
                          !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                            (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1)))
                      s.net[↑c.threads.val].head! s.net s.msgIds
                      {
                        cache :=
                          Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                            { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                              sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                      }) ;
                    res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] :=

                    foldNonSharersLemma s node
                        (List.filter
                        (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1)))
                      s.net[↑c.threads.val].head!
                      (s.net, s.msgIds)
                      h_node_not_sharer
                      (by simp) (by simp)

                  simp [h_fold]

                  have : s'.net[node].length = s.net[node].length := by
                    simp [h_s']
                    unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_not_sc_first]
                    simp [h_shim, h_fold.left]

                  change s.net[node][Fin.cast this i].id < s.net[node][Fin.cast this j].id
                  exact ih node (Fin.cast this i) (Fin.cast this j) h_ij
                case false =>         -- node is shim and ≠ src → message sent if sharer, otherwise no
                  dsimp [is_src] at h_is_src ; simp at h_is_src
                  cases h_is_sharer : is_sharer
                  case true =>        -- WRITE sent to node b/c node is shim and ≠ src and sharer
                    have h_node_sharer : (List.filter
                      (fun shim ↦
                      !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                        (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                      (List.finRange (↑c.threads + 1))).contains node := by
                      simp
                      -- dsimp [is_src] at h_is_src; simp at h_is_src
                      dsimp [is_sharer] at h_is_sharer
                      have : ¬↑node.val = ↑c.threads := by
                        simp [h_shim.symm]

                      apply And.intro
                      case left => exact h_is_src
                      case right =>
                        apply And.intro
                        case left => exact h_is_sharer
                        case right => exact this

                    have h_sharer_list_nodup : List.Nodup (List.filter
                        (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1))) := by
                        exact List.Nodup.filter (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val))) (List.nodup_finRange (↑c.threads + 1))

                    have h_fold := foldSharersLemma s node (List.filter
                        (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                        (List.finRange (↑c.threads + 1)))
                      -- s.net[↑c.threads.val].head!
                      (s.net, s.msgIds)
                      h_shim.symm
                      h_sharer_list_nodup
                      h_node_sharer
                      (by simp) (by simp)
                    simp at h_fold
                    simp [h_fold]

                    have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                      simp [h_s']
                      unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_not_sc_first]
                      simp [h_shim, h_fold.left]

                    change (i.val < j.val) at h_ij
-- todo here 8/22
                    cases (Nat.lt_trichotomy (↑j) s.net[node.val].length) with
                    | inl j_not_last =>
                      have i_not_last : ↑i < s.net[node.val].length := by
                        exact Nat.lt_trans h_ij j_not_last
                      change ((s.net[↑node.val] ++
                      [({ src := (Fin.mk ↑c.threads (Nat.lt_succ_self c.threads)), dst := node, data := s.net[↑c.threads.val].head!.data,
                          addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)])[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
                      ((s.net[↑node.val] ++
                      [({ src := (Fin.mk ↑c.threads (Nat.lt_succ_self c.threads)), dst := node, data := s.net[↑c.threads.val].head!.data,
                          addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)])[(j : Nat)]'(by simp ; exact Nat.lt_add_right 1 j_not_last)).id

                      simp only [List.getElem_append_left i_not_last]
                      simp only [List.getElem_append_left j_not_last]
                      change s.net[node][Fin.mk i i_not_last].id < s.net[node][Fin.mk j j_not_last].id
                      exact ih node (Fin.mk i i_not_last) (Fin.mk j j_not_last) h_ij
                    | inr j_last_or_vac =>
                      cases j_last_or_vac with
                      | inl j_last =>
                        have : j = Fin.mk s.net[node].length s_netlen_bound := by
                          exact Fin.eq_mk_iff_val_eq.mpr j_last
                        simp [this]
                        have : i.val < s.net[↑node.val].length := by rw [←j_last] ; exact h_ij
                        change ((s.net[↑node] ++ [({ src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := node, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 this)).id <
                              s.msgIds[↑node]
                        simp [this]
                        exact added_msg_greatest_id s node (Fin.mk i this) h1
                      | inr j_vac =>
                        exfalso
                        have hj1 : j < s.net[node].length + 1 := by
                          have : j < s'.net[node].length := by exact j.isLt
                          simp [h_s'] at this
                          unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg  at this ; simp [h, h_src_is_shim, h_not_sc_first] at this
                          simp [h_shim, h_fold] at this
                          exact this
                        have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                        have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                        rw [hj3] at j_vac
                        exact (lt_self_iff_false s.net[node].length).mp j_vac


                  case false =>       -- no msg sent b/c node not sharer

                    have h_node_not_sharer : !((List.filter
                      (fun shim ↦
                        !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                          (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                      (List.finRange (↑c.threads + 1))).contains node) := by
                        dsimp [is_sharer] at h_is_sharer
                        simp [h_is_sharer]

                    have h_fold :
                      let res :=
                        (foldSharers
                        (List.filter
                          (fun shim ↦
                            !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                              (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                          (List.finRange (↑c.threads + 1)))
                        s.net[↑c.threads.val].head! s.net s.msgIds
                        {
                          cache :=
                            Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                              { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                                sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                        }) ;
                      res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] :=

                      foldNonSharersLemma s node
                          (List.filter
                          (fun shim ↦
                          !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                            (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                          (List.finRange (↑c.threads + 1)))
                        s.net[↑c.threads.val].head!
                        (s.net, s.msgIds)
                        h_node_not_sharer
                        (by simp) (by simp)

                    simp [h_fold]

                    have : s'.net[node].length = s.net[node].length := by
                      simp [h_s']
                      unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg ; simp [h, h_src_is_shim, h_not_sc_first]
                      simp [h_shim, h_fold.left]

                    change s.net[node][Fin.cast this i].id < s.net[node][Fin.cast this j].id
                    exact ih node (Fin.cast this i) (Fin.cast this j) h_ij

          case isFalse h_ccreceive_not_from_shim =>     -- error case CCReceive msg from itself
            exfalso
            contradiction
        case RREQ =>
          dsimp [mtype] at h ; simp [h]
          change (i.val < j.val) at h_ij
          unfold popMessage send netWithAddedMsg
          cases h_cc_or_shim with
          | inl h_cc =>
            simp only [h_cc] at h_ccreceive_from_shim h ⊢
            simp at h_ccreceive_from_shim
            simp [Nat.ne_of_lt h_ccreceive_from_shim]

            have j_lt_s_tail : j.val < s.net[↑node.val].tail.length := by
              have : j.val < s'.net[↑node.val].length := by exact j.isLt
              simp [h_s'] at this
              unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at this
              simp [h_cc, h, Nat.ne_of_lt h_ccreceive_from_shim] at this
              simp
              exact this
            have i_lt_s_tail : i.val < s.net[node.val].tail.length := Nat.lt_trans h_ij j_lt_s_tail
            change s.net[↑node.val].tail[Fin.mk i i_lt_s_tail].id < s.net[↑node.val].tail[Fin.mk j j_lt_s_tail].id
            simp

            have : s'.net[node].length + 1 = s.net[node].length := by
              simp [h_s']
              unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg
              simp [h_cc, h, Nat.ne_of_lt h_ccreceive_from_shim]
              refine Nat.sub_add_cancel ?_
              simp [h_cc] at h_net
              exact h_net

            have i_succ_bound : forall (i : Fin (s'.net[node].length)), i + 1 < s.net[node].length := by
              rw [← this]
              simp

            change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.net[↑node][Fin.mk (j + 1) (i_succ_bound j)].id
            exact ih node (Fin.mk (i + 1) (i_succ_bound i)) (Fin.mk (j + 1) (i_succ_bound j)) (Nat.succ_lt_succ h_ij)
          | inr h_shim =>
            simp [h_shim]

            have h_node_src : (↑s.net[↑c.threads.val].head!.src.val : Nat) = (node.val : Nat) ∨ (↑s.net[↑c.threads.val].head!.src.val : Nat) ≠ (node.val : Nat) := by exact eq_or_ne (↑s.net[↑c.threads.val].head!.src.val : Nat) (node.val : Nat)
            cases h_node_src with
            | inl node_src_eq =>
              have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                simp only [h_s']
                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg
                simp [h_shim, h, node_src_eq]

              simp [node_src_eq]
              have h_j_tri : (↑j : Nat) < s.net[node.val].length ∨ (↑j) = s.net[node.val].length ∨ s.net[node.val].length < (↑j) := (Nat.lt_trichotomy (↑j) s.net[node.val].length)
              cases h_j_tri with
              | inl j_not_last =>
                have i_not_last : (↑i : Nat) < s.net[node.val].length := by exact Nat.lt_trans h_ij j_not_last
                change (((s.net[↑node.val] ++ [({ mtype := MType.RRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.cc.cache[↑s.net[(↑c.threads.val : Nat)].head!.addr.val].data, addr := s.net[(↑c.threads.val : Nat)].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node] } : Message c)]))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
                       (((s.net[↑node.val] ++ [({ mtype := MType.RRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.cc.cache[↑s.net[(↑c.threads.val : Nat)].head!.addr.val].data, addr := s.net[(↑c.threads.val : Nat)].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node] } : Message c)]))[(j : Nat)]'(by simp ; exact Nat.lt_add_right 1 j_not_last)).id

                simp only [List.getElem_append_left i_not_last, List.getElem_append_left j_not_last]
                change s.net[node][Fin.mk i i_not_last].id < s.net[node][Fin.mk j j_not_last].id
                exact ih node (Fin.mk i i_not_last) (Fin.mk j j_not_last) h_ij
              | inr j_last_or_vac =>
                cases j_last_or_vac with
                | inl j_last =>
                  have : j = Fin.mk s.net[node].length s_netlen_bound := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [this]
                  have : i.val < s.net[↑node.val].length := by rw [←j_last] ; exact h_ij
                  change ((s.net[↑node.val] ++ [({ mtype := MType.RRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)])[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 this)).id < s.msgIds[↑node]
                  simp [this]
                  exact added_msg_greatest_id s node (Fin.mk i this) h1
                | inr j_vac =>
                  exfalso
                  have hj1 : j < s.net[node].length + 1 := by
                    have : j < s'.net[node].length := by exact j.isLt
                    simp [h_s'] at this
                    unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at this
                    simp [h_shim, h, node_src_eq] at this
                    exact this
                  have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                  have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                  rw [hj3] at j_vac
                  exact (lt_self_iff_false s.net[node].length).mp j_vac
            | inr node_src_neq =>
              simp [node_src_neq]
              have : s'.net[node.val].length = s.net[node.val].length := by
                simp only [h_s']
                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers send netWithAddedMsg
                simp [h, h_shim, node_src_neq]
              change s.net[node][Fin.cast this i].id < s.net[node][Fin.cast this j].id
              exact ih node (Fin.cast this i) (Fin.cast this j) h_ij
        case FREQ =>
          dsimp [mtype] at h ; simp [h]
          change (i.val < j.val) at h_ij
          unfold popMessage send sendFence netWithAddedMsg
          cases h_cc_or_shim with
          | inl h_cc =>
            simp only [h_cc] at h_ccreceive_from_shim h ⊢
            simp at h_ccreceive_from_shim
            simp [Nat.ne_of_lt h_ccreceive_from_shim]

            have j_lt_s_tail : j.val < s.net[↑node.val].tail.length := by
              have : j.val < s'.net[↑node.val].length := by exact j.isLt
              simp [h_s'] at this
              unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers sendFence send netWithAddedMsg at this
              simp [h_cc, h, Nat.ne_of_lt h_ccreceive_from_shim] at this
              simp
              exact this
            have i_lt_s_tail : i.val < s.net[node.val].tail.length := Nat.lt_trans h_ij j_lt_s_tail
            change s.net[↑node.val].tail[Fin.mk i i_lt_s_tail].id < s.net[↑node.val].tail[Fin.mk j j_lt_s_tail].id
            simp

            have : s'.net[node].length + 1 = s.net[node].length := by
              simp [h_s']
              unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers sendFence send netWithAddedMsg
              simp [h_cc, h, Nat.ne_of_lt h_ccreceive_from_shim]
              refine Nat.sub_add_cancel ?_
              simp [h_cc] at h_net
              exact h_net

            have i_succ_bound : forall (i : Fin (s'.net[node].length)), i + 1 < s.net[node].length := by
              rw [← this]
              simp

            change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.net[↑node][Fin.mk (j + 1) (i_succ_bound j)].id
            exact ih node (Fin.mk (i + 1) (i_succ_bound i)) (Fin.mk (j + 1) (i_succ_bound j)) (Nat.succ_lt_succ h_ij)
          | inr h_shim =>
            simp [h_shim]

            have h_node_src : (↑s.net[↑c.threads.val].head!.src.val : Nat) = (node.val : Nat) ∨ (↑s.net[↑c.threads.val].head!.src.val : Nat) ≠ (node.val : Nat) := by exact eq_or_ne (↑s.net[↑c.threads.val].head!.src.val : Nat) (node.val : Nat)
            cases h_node_src with
            | inl node_src_eq =>
              have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                simp only [h_s']
                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers sendFence send netWithAddedMsg
                simp [h_shim, h, node_src_eq]

              simp [node_src_eq]
              have h_j_tri : (↑j : Nat) < s.net[node.val].length ∨ (↑j) = s.net[node.val].length ∨ s.net[node.val].length < (↑j) := (Nat.lt_trichotomy (↑j) s.net[node.val].length)
              cases h_j_tri with
              | inl j_not_last =>
                have i_not_last : (↑i : Nat) < s.net[node.val].length := by exact Nat.lt_trans h_ij j_not_last
                change (((s.net[↑node.val] ++ [({ mtype := MType.FRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := (default : Message c).data, addr := (default : Message c).addr, ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node.val] } : Message c)]))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
                       (((s.net[↑node.val] ++ [({ mtype := MType.FRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := (default : Message c).data, addr := (default : Message c).addr, ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node.val] } : Message c)]))[(j : Nat)]'(by simp ; exact Nat.lt_add_right 1 j_not_last)).id

                simp only [List.getElem_append_left i_not_last, List.getElem_append_left j_not_last]
                change s.net[node][Fin.mk i i_not_last].id < s.net[node][Fin.mk j j_not_last].id
                exact ih node (Fin.mk i i_not_last) (Fin.mk j j_not_last) h_ij
              | inr j_last_or_vac =>
                cases j_last_or_vac with
                | inl j_last =>
                  have : j = Fin.mk s.net[node].length s_netlen_bound := by
                    exact Fin.eq_mk_iff_val_eq.mpr j_last
                  simp [this]
                  have : i.val < s.net[↑node.val].length := by rw [←j_last] ; exact h_ij
                  change ((s.net[↑node] ++ [({ mtype := MType.FRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := (default : Message c).data, addr := (default : Message c).addr, ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 this)).id <
                        s.msgIds[↑node]
                  simp [this]
                  exact added_msg_greatest_id s node (Fin.mk i this) h1
                | inr j_vac =>
                  exfalso
                  have hj1 : j < s.net[node].length + 1 := by
                    have : j < s'.net[node].length := by exact j.isLt
                    simp [h_s'] at this
                    unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers sendFence send netWithAddedMsg at this
                    simp [h_shim, h, node_src_eq] at this
                    exact this
                  have hj2 : ¬ j < s.net[node].length := by exact Nat.not_lt_of_gt j_vac
                  have hj3 : ↑j = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hj1 hj2

                  rw [hj3] at j_vac
                  exact (lt_self_iff_false s.net[node].length).mp j_vac
            | inr node_src_neq =>
              simp [node_src_neq]
              have : s'.net[node.val].length = s.net[node.val].length := by
                simp only [h_s']
                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers send sendFence netWithAddedMsg
                simp [h, h_shim, node_src_neq]
              change s.net[node][Fin.cast this i].id < s.net[node][Fin.cast this j].id
              exact ih node (Fin.cast this i) (Fin.cast this j) h_ij

        -- error cases ↓
        case WRITE_ACK =>
          exfalso
          dsimp [mtype] at h
          change (valid_CCReceive_MType s.net[↑c.threads.val].head!.mtype = true) at h_valid_mtype
          rw [h] at h_valid_mtype
          unfold valid_CCReceive_MType at h_valid_mtype
          simp at h_valid_mtype
        case EVICT =>
          exfalso
          dsimp [mtype] at h
          change (valid_CCReceive_MType s.net[↑c.threads.val].head!.mtype = true) at h_valid_mtype
          rw [h] at h_valid_mtype
          unfold valid_CCReceive_MType at h_valid_mtype
          simp at h_valid_mtype
        case RRESP =>
          exfalso
          dsimp [mtype] at h
          change (valid_CCReceive_MType s.net[↑c.threads.val].head!.mtype = true) at h_valid_mtype
          rw [h] at h_valid_mtype
          unfold valid_CCReceive_MType at h_valid_mtype
          simp at h_valid_mtype
        case FRESP =>
          exfalso
          dsimp [mtype] at h
          change (valid_CCReceive_MType s.net[↑c.threads.val].head!.mtype = true) at h_valid_mtype
          rw [h] at h_valid_mtype
          unfold valid_CCReceive_MType at h_valid_mtype
          simp at h_valid_mtype
      | Finish h_false h_done h_s' =>
        simp [h_s']
        have h_same_net_size : s'.net[node].length = s.net[node].length := by
          simp [h_s']
        change s.net[↑node][Fin.cast h_same_net_size i].id < s.net[↑node][Fin.cast h_same_net_size j].id
        exact ih node (Fin.cast h_same_net_size i) (Fin.cast h_same_net_size j) h_ij

-- todo list
-- check email for old posters from rachel,
-- finish proof for network orderedness
-- finish proof for added message greatest id
-- go back to proof for nonlocal writes increment timestamp (finally...)

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

/-∀ (eg : ExecutionGraph),
    ¬ rc11_consistent eg →
    ¬ ∃ (s : MemGlueState),
      end_state s ∧ execution_matches_eg (s.exeution, eg)
      -/

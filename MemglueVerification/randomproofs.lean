import MemglueVerification.memglueO
set_option profiler true
set_option maxHeartbeats 20000000

lemma foldNonSharersLemma {c : SystemConfig} :
forall (s : IncState c) (node : Node c) (sharers : List (Node c)) (msg : Message c) (init : NETOrdered c × MessageIds c),
  !(sharers.contains node) →
  init.1[↑node.val] = s.net[↑node.val] →
  init.2[↑node.val] = s.msgIds[↑node.val] →
  let res := (foldSharers sharers msg init.1 init.2
   ({
      cache :=
        Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
          { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
            sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
    } : CCMachine c)) ;
  res.1[↑node.val] = s.net[↑node.val] ∧ res.2[↑node.val] = s.msgIds[↑node.val] := by

  intro s node sharers msg init h_not_sharer h_init_net h_init_msgIds
  -- apply And.intro
  -- case left =>
  unfold foldSharers send netWithAddedMsg
  simp at h_not_sharer ⊢

  induction sharers generalizing init
  case nil => simp [h_init_net, h_init_msgIds]
  case cons x xs ih =>
    have h_node_notmem_xs : node ∉ xs := by exact List.not_mem_of_not_mem_cons h_not_sharer
    simp only [List.foldl_cons]

    have h_node_ne_x : ↑node.val ≠ ↑x := by
      have : node ≠ x := by exact List.ne_of_not_mem_cons h_not_sharer
      exact Fin.val_ne_of_ne this

    let init' := (Vector.set init.1 (↑x)
          (init.1[↑x] ++
            [{ src := ⟨↑c.threads, (by simp)⟩, dst := x, data := msg.data, addr := msg.addr,
                ts :=
                  (Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
                        { data := s.net[↑c.threads.val].head!.data,
                          ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
                        )[↑msg.addr.val].ts,
                stren := msg.stren, id := init.2[↑x.val] }])
          ,
        Vector.set init.2 (↑x) (init.2[↑x] + 1))

    have h_init'_net : init'.1[↑node] = s.net[↑node] := by
      dsimp [init']
      simp [Vector.getElem_set_ne x.isLt node.isLt h_node_ne_x.symm]
      exact h_init_net
    have h_init'_msgIds : init'.2[↑node] = s.msgIds[↑node] := by
      dsimp[init']
      simp [h_node_ne_x.symm]
      exact h_init_msgIds

    exact ih init' h_init'_net h_init'_msgIds h_node_notmem_xs

lemma foldSharersLemma {c : SystemConfig} :
forall (s : IncState c) (node : Node c) (sharers : List (Node c)) (init : NETOrdered c × MessageIds c),
  node.val ≠ c.threads.val →
  (List.Nodup sharers) →
  (sharers.contains node) →
  init.1[↑node.val] = s.net[↑node.val] →
  init.2[↑node.val] = s.msgIds[↑node.val] →
  let res := (foldSharers sharers
    s.net[↑c.threads.val].head!
    init.1 init.2
   ({ -- ? i think maybe we generalize this part and just do another universal over forall (cc : CCMachine c)
      cache :=
        Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
          { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
            sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
    } : CCMachine c)) ;

    res.1[↑node.val] = s.net[↑node.val] ++
                    [{ src := Fin.mk c.threads (Nat.lt_succ_self c.threads), dst := node, data := s.net[↑c.threads.val].head!.data,
                        addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                        stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] }] ∧
    res.2[↑node.val] = s.msgIds[↑node.val] + 1 := by
    intro s node sharers init h_node_not_cc h_sharer_list_nodup h_sharer h_init_net h_init_msgIds
    -- apply And.intro
    -- case left =>
    unfold foldSharers send netWithAddedMsg
    simp at h_sharer ⊢

    induction sharers generalizing init
    case nil =>
      exfalso
      exact (List.mem_nil_iff node).mp h_sharer
    case cons x xs ih =>
      simp only [List.foldl_cons]
      let init' := (Vector.set init.1 (↑x)
                  (init.1[↑x] ++
            [{ src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := x, data := s.net[↑c.threads.val].head!.data,
                addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                stren := s.net[↑c.threads.val].head!.stren, id := init.2[↑x.val] }])
                  ,
                Vector.set init.2 (↑x) (init.2[↑x] + 1))

      have : node.val = x.val ∨ node ∈ xs := by
        simp [List.mem_cons] at h_sharer
        exact Or.symm (Or.imp_right (congrArg Fin.val) (id (Or.symm h_sharer)))

      cases this with
      | inl h_node_eq_x =>
        have h_neq_init'_net : init'.1[↑node] = s.net[↑node.val] ++
            [{ src := Fin.mk c.threads (Nat.lt_succ_self c.threads), dst := node, data := s.net[↑c.threads.val].head!.data,
                addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] }] := by
          dsimp [init']
          have : node = x := by exact Fin.eq_of_val_eq h_node_eq_x
          simp [this.symm]
          rw [h_init_net, h_init_msgIds]
        let s' := {s with net := (s.net.set ↑node (s.net[↑node] ++
          [({ src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := node, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr,
              ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren,
              id := s.msgIds[↑node] } : Message c)])), msgIds := s.msgIds.set ↑node.val (s.msgIds[node.val] + 1)
              }
        have h_node_notin_xs : !(xs.contains node) := by
          simp [Fin.eq_of_val_eq h_node_eq_x]
          simp at h_sharer_list_nodup
          exact h_sharer_list_nodup.left

        have h_init'_net : init'.1[↑node] = s'.net[↑node] := by
          dsimp [init', s']
          simp [← h_node_eq_x, h_init_net, h_init_msgIds, Fin.eq_of_val_eq h_node_eq_x]
        have h_init'_msgIds : init'.2[↑node] = s'.msgIds[↑node] := by
          dsimp [init', s']
          simp [← h_node_eq_x, h_init_msgIds, Fin.eq_of_val_eq h_node_eq_x]

        have h_fold_non_sharers := (foldNonSharersLemma s' node xs
          ({ src := Fin.mk c.threads (Nat.lt_succ_self c.threads), dst := node, data := s.net[↑c.threads.val].head!.data,
                      addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                      stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)
          init' h_node_notin_xs h_init'_net h_init'_msgIds)       -- .left
        dsimp [s', init'] at h_fold_non_sharers ; unfold foldSharers send netWithAddedMsg at h_fold_non_sharers ; simp [h_node_not_cc] at h_fold_non_sharers
        exact h_fold_non_sharers
      | inr h_node_in_xs =>
        have : node.val ≠ x.val := by
          simp at h_sharer_list_nodup
          refine Fin.val_ne_of_ne ?_
          exact ne_of_mem_of_not_mem h_node_in_xs h_sharer_list_nodup.left

        have h_init'_net : init'.1[↑node] = s.net[↑node] := by
          dsimp [init'] ; simp [this.symm, h_init_net]
        have h_init'_msgIds : init'.2[↑node] = s.msgIds[↑node] := by
          dsimp [init'] ; simp [this.symm, h_init_msgIds]
        exact ih init' (by simp at h_sharer_list_nodup; exact h_sharer_list_nodup.right) h_init'_net h_init'_msgIds h_node_in_xs



lemma added_msg_greatest_id_step_ProcessInstr {c : SystemConfig} :
  forall (s s': IncState c) (node : Node c) (shim : ShimId c),
    increment_reachable s →
    canIssueInstr shim s →
    s' = getAndIssueInstr shim s →
    (forall (i : Fin s.net[node].length), (s.net[node][i]).id < s.msgIds[node]) →
    (forall (i : Fin s'.net[node].length), (s'.net[node][i]).id < s'.msgIds[node]) := by

  intro s s' node shim h h_issue h_s' ih i
  have h_cc_or_shim := by exact eq_or_ne (c.threads : Nat) (node : Nat)

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
    case isFalse =>       -- shim read miss
      simp [h_s']
      unfold send
      unfold netWithAddedMsg
      simp

      cases h_cc_or_shim with
      | inl h_cc =>
        simp [h_cc] at h_s' ⊢

        have h_i : (i : Nat) < s.net[node].length ∨ (i : Nat) = s.net[node].length ∨
                                            s.net[node].length < (i : Nat) := by
          exact Nat.lt_trichotomy (↑i) s.net[node].length

        have s_netlen_bound : s.net[node].length < s'.net[node].length := by
          unfold send netWithAddedMsg at h_s'
          simp [h_s']

        cases h_i with
        | inl i_not_last =>
          change ((s.net[↑node] ++
  [({ mtype := MType.RREQ, src := Fin.castSucc shim, dst := node,
      data := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].data,
      addr := (getInstr shim s.shimVec s.execution).2.addr,
      ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts,
      stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] } : Message c)] : (List (Message c)))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 i_not_last)).id <
s.msgIds[↑node] + 1

          simp only [List.getElem_append_left i_not_last]
          change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
          exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
        | inr i_last_or_vac =>
          cases i_last_or_vac with
          | inl i_last =>
            have : i = Fin.mk s.net[node].length s_netlen_bound := by
              exact Fin.eq_mk_iff_val_eq.mpr i_last
            simp [this]
          | inr i_vac =>
            exfalso
            have hi1 : i < s.net[node].length + 1 := by
              have : i < s'.net[node].length := by exact i.isLt
              simp [h_s'] at this
              unfold send netWithAddedMsg at this ; simp at this
              exact this
            have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
            have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

            rw [hi3] at i_vac
            exact (lt_self_iff_false s.net[node].length).mp i_vac
      | inr h_shim =>
        simp [h_shim]
        have h_same_net_size : s'.net[node].length = s.net[node].length := by
          simp [h_s']
          unfold send netWithAddedMsg
          simp [h_shim]

        change s.net[node][Fin.cast h_same_net_size i].id < s.msgIds[node]
        exact ih (Fin.cast h_same_net_size i)
  case h_2 =>                   -- shimWrite instr
    unfold shimWrite at h_s'
    simp at h_s'
    split at h_s'

    case isTrue =>          -- shimWrite instr SC stren
      simp [h_s'] ; unfold send netWithAddedMsg ; simp
      cases h_cc_or_shim with
      | inl h_cc =>
        simp [h_cc]

        have h_i : (i : Nat) < s.net[node].length ∨ (i : Nat) = s.net[node].length ∨
                                            s.net[node].length < (i : Nat) := by
          exact Nat.lt_trichotomy (↑i) s.net[node].length

        have s_netlen_bound : s.net[node].length < s'.net[node].length := by
          unfold send netWithAddedMsg at h_s'
          simp [h_s', h_cc]

        cases h_i with
        | inl i_not_last =>
          change ((s.net[↑node] ++
  [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
      addr := (getInstr shim s.shimVec s.execution).2.addr,
      ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
      stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }] : List (Message c))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
s.msgIds[↑node] + 1

          simp only [List.getElem_append_left i_not_last]
          change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
          exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
        | inr i_last_or_vac =>
          cases i_last_or_vac with
          | inl i_last =>
            have : i = Fin.mk s.net[node].length s_netlen_bound := by
              exact Fin.eq_mk_iff_val_eq.mpr i_last
            simp [this]
          | inr i_vac =>
            exfalso
            have hi1 : i < s.net[node].length + 1 := by
              have : i < s'.net[node].length := by exact i.isLt
              simp [h_s'] at this
              unfold send netWithAddedMsg at this ; simp [h_cc] at this
              exact this
            have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
            have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

            rw [hi3] at i_vac
            exact (lt_self_iff_false s.net[node].length).mp i_vac

      | inr h_shim =>
        simp [h_shim]
        have h_same_net_size : s'.net[node].length = s.net[node].length := by
          simp [h_s']
          unfold send netWithAddedMsg
          simp [h_shim]

        change s.net[node][Fin.cast h_same_net_size i].id < s.msgIds[node]
        exact ih (Fin.cast h_same_net_size i)
    case isFalse =>         -- shimWrite instr non SC stren
      simp [h_s'] ; unfold send netWithAddedMsg ; simp
      cases h_cc_or_shim with
      | inl h_cc =>
        simp [h_cc]

        have h_i : (i : Nat) < s.net[node].length ∨ (i : Nat) = s.net[node].length ∨
                                            s.net[node].length < (i : Nat) := by
          exact Nat.lt_trichotomy (↑i) s.net[node].length

        have s_netlen_bound : s.net[node].length < s'.net[node].length := by
          unfold send netWithAddedMsg at h_s'
          simp [h_s', h_cc]

        cases h_i with
        | inl i_not_last =>
          change ((s.net[↑node] ++
  [{ src := Fin.castSucc shim, dst := node, data := (getInstr shim s.shimVec s.execution).2.data,
      addr := (getInstr shim s.shimVec s.execution).2.addr,
      ts := s.shimVec[↑shim].state[↑(getInstr shim s.shimVec s.execution).2.addr].ts + 1,
      stren := (getInstr shim s.shimVec s.execution).2.stren, id := s.msgIds[↑node] }] : List (Message c))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
s.msgIds[↑node] + 1

          simp only [List.getElem_append_left i_not_last]
          change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
          exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
        | inr i_last_or_vac =>
          cases i_last_or_vac with
          | inl i_last =>
            have : i = Fin.mk s.net[node].length s_netlen_bound := by
              exact Fin.eq_mk_iff_val_eq.mpr i_last
            simp [this]
          | inr i_vac =>
            exfalso
            have hi1 : i < s.net[node].length + 1 := by
              have : i < s'.net[node].length := by exact i.isLt
              simp [h_s'] at this
              unfold send netWithAddedMsg at this ; simp [h_cc] at this
              exact this
            have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
            have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

            rw [hi3] at i_vac
            exact (lt_self_iff_false s.net[node].length).mp i_vac

      | inr h_shim =>
        simp [h_shim]
        have h_same_net_size : s'.net[node].length = s.net[node].length := by
          simp [h_s']
          unfold send netWithAddedMsg
          simp [h_shim]

        change s.net[node][Fin.cast h_same_net_size i].id < s.msgIds[node]
        exact ih (Fin.cast h_same_net_size i)

  case h_3 =>
    simp [h_s']
    unfold shimFence sendFence netWithAddedMsg ; simp

    cases h_cc_or_shim with
      | inl h_cc =>
        simp [h_cc]

        have h_i : (i : Nat) < s.net[node].length ∨ (i : Nat) = s.net[node].length ∨
                                            s.net[node].length < (i : Nat) := by
          exact Nat.lt_trichotomy (↑i) s.net[node].length

        have s_netlen_bound : s.net[node].length < s'.net[node].length := by
          unfold shimFence sendFence netWithAddedMsg at h_s'
          simp [h_s', h_cc]

        cases h_i with
        | inl i_not_last =>
          change ((s.net[↑node] ++
  [{ mtype := MType.FREQ, src := Fin.castSucc shim, dst := node, data := (default : Message c).data, addr := (default : Message c).addr,
      ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node] }] : List (Message c))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
s.msgIds[↑node] + 1

          simp only [List.getElem_append_left i_not_last]
          change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
          exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
        | inr i_last_or_vac =>
          cases i_last_or_vac with
          | inl i_last =>
            have : i = Fin.mk s.net[node].length s_netlen_bound := by
              exact Fin.eq_mk_iff_val_eq.mpr i_last
            simp [this]
          | inr i_vac =>
            exfalso
            have hi1 : i < s.net[node].length + 1 := by
              have : i < s'.net[node].length := by exact i.isLt
              simp [h_s'] at this
              unfold shimFence sendFence netWithAddedMsg at this ; simp [h_cc] at this
              exact this
            have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
            have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

            rw [hi3] at i_vac
            exact (lt_self_iff_false s.net[node].length).mp i_vac

      | inr h_shim =>
        simp [h_shim]
        have h_same_net_size : s'.net[node].length = s.net[node].length := by
          simp [h_s']
          unfold shimFence sendFence netWithAddedMsg
          simp [h_shim]

        change s.net[node][Fin.cast h_same_net_size i].id < s.msgIds[node]
        exact ih (Fin.cast h_same_net_size i)


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
    have h_cc_or_shim : (c.threads : Nat) = (node : Nat) ∨ (c.threads : Nat) ≠ (node : Nat) := by
              exact eq_or_ne (c.threads : Nat) (node : Nat)

    cases h2 with
      | ProcessInstr shim h_issue h_s' =>
/-c : SystemConfig
s✝ : IncState c
node : Node c
s s' : IncState c
h1 : increment_reachable s
ih : ∀ (i : Fin s.net[node].length), s.net[node][i].id < s.msgIds[node]
i : Fin s'.net[node].length
h_cc_or_shim : ↑c.threads = ↑node ∨ ↑c.threads ≠ ↑node
shim : ShimId c
h_issue : canIssueInstr shim s
h_s' : s' = getAndIssueInstr shim s
⊢ s'.net[node][i].id < s'.msgIds[node]-/
        exact added_msg_greatest_id_step_ProcessInstr s s' node shim h1 h_issue h_s' ih i
      | ShimProcessMsg shim h_net h_s' =>
        unfold shimReceiveAndPopMsg at h_s'
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

          change s.net[↑node].tail[Fin.cast this i].id < s.msgIds[↑node]
          simp

          have : s'.net[node].length + 1 = s.net[node].length := by
            simp [h_s']
            exact Nat.sub_add_cancel h_net
          have i_succ_bound : forall (i : Fin (s'.net[node].length)), i + 1 < s.net[node].length := by
            rw [← this]
            simp

          change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.msgIds[↑node]
          exact ih ⟨↑i + 1, i_succ_bound i⟩
        | inr h_no_change =>
          simp [h_no_change]
          have h_same_net_size : s'.net[node].length = s.net[node].length := by
            simp [h_s', h_no_change]
          change s.net[↑node][Fin.cast h_same_net_size i].id < s.msgIds[↑node]
          exact ih (Fin.cast h_same_net_size i)
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

                change s.net[↑node].tail[Fin.cast this i].id < s.msgIds[↑node]
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

                change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.msgIds[↑node]
                exact ih ⟨↑i + 1, i_succ_bound i⟩
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

                  have h_i : (i : Nat) < s.net[node].length ∨ (i : Nat) = s.net[node].length ∨
                                            s.net[node].length < (i : Nat) := by
                    exact Nat.lt_trichotomy (↑i) s.net[node].length


                  unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at h_s' ; simp [h, h_src_is_shim, h_sc_first] at h_s'
                  have s_netlen_bound : s.net[node].length < s'.net[node].length := by
                    simp [h_s', h_shim, h_is_src.symm, h_fold]

                  cases h_i with
                  | inl i_not_last =>
                    change ((s.net[↑node] ++ [({ mtype := MType.WRITE_ACK, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.net[↑c.threads.val].head!.data, addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)] : List (Message c))[(i : Nat)]'(by simp; exact Nat.lt_add_right 1 i_not_last)).id <
                      s.msgIds[↑node] + 1
                    simp only [List.getElem_append_left i_not_last]
                    change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
                    exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
                  | inr i_last_or_vac =>
                    cases i_last_or_vac with
                    | inl i_last =>
                      have : i = Fin.mk s.net[node].length s_netlen_bound := by
                        exact Fin.eq_mk_iff_val_eq.mpr i_last
                      simp [this]
                    | inr i_vac =>
                      exfalso
                      have hi1 : i < s.net[node].length + 1 := by
                        have : i < s'.net[node].length := by exact i.isLt
                        simp [h_s', h_shim, h_is_src.symm, h_fold] at this
                        -- unfold send netWithAddedMsg at this ; simp at this
                        exact this
                      have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
                      have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

                      rw [hi3] at i_vac
                      exact (lt_self_iff_false s.net[node].length).mp i_vac

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

                    /-lemma foldSharersLemma {c : SystemConfig} :
forall (s : IncState c) (node : Node c) (sharers : List (Node c)) (msg : Message c) (init : NETOrdered c × MessageIds c),
  (sharers.contains node) →
  init.1[↑node.val] = s.net[↑node.val] →
  init.2[↑node.val] = s.msgIds[↑node.val] →
  let res := (foldSharers sharers msg init.1 init.2
   ({
      cache :=
        Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
          { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
            sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
    } : CCMachine c)) ;

    res.1[↑node.val] = s.net[↑node.val] ++
                    [{ src := Fin.mk c.threads (Nat.lt_succ_self c.threads), dst := node, data := s.net[↑c.threads.val].head!.data,
                        addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                        stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] }] ∧
    res.2[↑node.val] = s.msgIds[↑node.val] + 1 -/
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

                    cases (Nat.lt_trichotomy (↑i) s.net[node].length) with
                    | inl i_not_last =>
                      change ((s.net[↑node] ++
                      [({ src := (Fin.mk ↑c.threads (Nat.lt_succ_self c.threads)), dst := node, data := s.net[↑c.threads.val].head!.data,
                          addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)])[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
                      s.msgIds[↑node] + 1

                      simp only [List.getElem_append_left i_not_last]
                      change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
                      exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
                    | inr i_last_or_vac =>
                      cases i_last_or_vac with
                      | inl i_last =>
                        have : i = Fin.mk s.net[node].length s_netlen_bound := by
                          exact Fin.eq_mk_iff_val_eq.mpr i_last
                        simp [this]
                      | inr i_vac =>
                        exfalso
                        have hi1 : i < s.net[node].length + 1 := by
                          have : i < s'.net[node].length := by exact i.isLt
                          simp [h_s'] at this
                          simp [h_shim, (Nat.ne_of_lt h_src_is_shim), (Ne.intro h_is_src).symm, h_fold] at this
                          -- unfold send netWithAddedMsg at this ; simp [h_cc] at this
                          exact this
                        have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
                        have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

                        rw [hi3] at i_vac
                        exact (lt_self_iff_false s.net[node].length).mp i_vac
                    -- unfold foldSharers send netWithAddedMsg ; simp

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

                    change s.net[↑node][Fin.cast this i].id < s.msgIds[↑node]
                    exact ih (Fin.cast this i)






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

                change s.net[↑node].tail[Fin.cast this i].id < s.msgIds[↑node]
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

                change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.msgIds[↑node]
                exact ih ⟨↑i + 1, i_succ_bound i⟩
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

                  change s.net[↑node][Fin.cast this i].id < s.msgIds[↑node]
                  exact ih (Fin.cast this i)
                case false =>         -- node is shim and ≠ src → message sent if sharer, otherwise no
                  cases h_is_sharer : is_sharer
                  case true =>        -- WRITE sent to node b/c node is shim and ≠ src and sharer
                    have h_node_sharer : (List.filter
                      (fun shim ↦
                      !decide (↑shim.val = ↑s.net[↑c.threads.val].head!.src.val) &&
                        (s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑c.threads.val)))
                      (List.finRange (↑c.threads + 1))).contains node := by
                      simp
                      dsimp [is_src] at h_is_src; simp at h_is_src
                      dsimp [is_sharer] at h_is_sharer
                      have : ¬↑node.val = ↑c.threads := by
                        simp [h_shim.symm]

                      apply And.intro
                      case left => exact h_is_src
                      case right =>
                        apply And.intro
                        case left => exact h_is_sharer
                        case right => exact this

                    /-lemma foldSharersLemma {c : SystemConfig} :
forall (s : IncState c) (node : Node c) (sharers : List (Node c)) (msg : Message c) (init : NETOrdered c × MessageIds c),
  (sharers.contains node) →
  init.1[↑node.val] = s.net[↑node.val] →
  init.2[↑node.val] = s.msgIds[↑node.val] →
  let res := (foldSharers sharers msg init.1 init.2
   ({
      cache :=
        Vector.set s.cc.cache ↑s.net[↑c.threads.val].head!.addr.val
          { data := s.net[↑c.threads.val].head!.data, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
            sharers := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].sharers }
    } : CCMachine c)) ;

    res.1[↑node.val] = s.net[↑node.val] ++
                    [{ src := Fin.mk c.threads (Nat.lt_succ_self c.threads), dst := node, data := s.net[↑c.threads.val].head!.data,
                        addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                        stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] }] ∧
    res.2[↑node.val] = s.msgIds[↑node.val] + 1 -/
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

                    cases (Nat.lt_trichotomy (↑i) s.net[node].length) with
                    | inl i_not_last =>
                      change ((s.net[↑node] ++
                      [({ src := (Fin.mk ↑c.threads (Nat.lt_succ_self c.threads)), dst := node, data := s.net[↑c.threads.val].head!.data,
                          addr := s.net[↑c.threads.val].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts + 1,
                          stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node.val] } : Message c)])[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id <
                      s.msgIds[↑node] + 1

                      simp only [List.getElem_append_left i_not_last]
                      change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
                      exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
                    | inr i_last_or_vac =>
                      cases i_last_or_vac with
                      | inl i_last =>
                        have : i = Fin.mk s.net[node].length s_netlen_bound := by
                          exact Fin.eq_mk_iff_val_eq.mpr i_last
                        simp [this]
                      | inr i_vac =>
                        exfalso
                        have hi1 : i < s.net[node].length + 1 := by
                          have : i < s'.net[node].length := by exact i.isLt
                          simp [h_s'] at this
                          unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at this ; simp [h, h_src_is_shim, h_not_sc_first] at this
                          simp [h_shim, h_fold.left] at this
                          -- unfold send netWithAddedMsg at this ; simp [h_cc] at this
                          exact this
                        have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
                        have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

                        rw [hi3] at i_vac
                        exact (lt_self_iff_false s.net[node].length).mp i_vac
                    -- unfold foldSharers send netWithAddedMsg ; simp


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

                    change s.net[↑node][Fin.cast this i].id < s.msgIds[↑node]
                    exact ih (Fin.cast this i)
                -- let is_sharer := (((List.filter
                --   (fun shim ↦
                --     !decide (shim.val = ↑s.net[↑node.val].head!.src) &&
                --       (s.cc.cache[↑s.net[↑node.val].head!.addr.val].sharers[↑shim.val]! && !decide (↑shim.val = ↑node)))
                --   (List.finRange (↑c.threads + 1)))).contains node)

                -- cases h : is_sharer
                -- case true =>       -- node is not a sharer → doesn't receive WRITE message
                --   have h_node_sharer : (List.filter
                --   (fun shim ↦
                --   !decide (↑shim = ↑s.net[↑c.threads].head!.src) &&
                --     (s.cc.cache[↑s.net[↑c.threads].head!.addr].sharers[↑shim]! && !decide (↑shim = ↑c.threads)))
                --   (List.finRange (↑c.threads + 1))).contains node := by

                --     sorry
                --   sorry
                -- case false =>        -- node is sharer → receives WRITE message
                --   sorry
          case isFalse h_ccreceive_not_from_shim =>     -- error case CCReceive msg from itself
            exfalso
            contradiction
        case RREQ =>
          dsimp [mtype] at h ; simp [h]
          unfold popMessage send netWithAddedMsg
          cases h_cc_or_shim with
          | inl h_cc =>
            simp only [h_cc] at h_ccreceive_from_shim h ⊢
            simp at h_ccreceive_from_shim
            simp [Nat.ne_of_lt h_ccreceive_from_shim]

            have : i.val < s.net[↑node.val].tail.length := by
              have : i.val < s'.net[↑node.val].length := by exact i.isLt
              simp [h_s'] at this
              unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at this
              simp [h_cc, h, Nat.ne_of_lt h_ccreceive_from_shim] at this
              simp
              exact this
            change s.net[↑node.val].tail[Fin.mk i this].id < s.msgIds[↑node.val]
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

            change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.msgIds[↑node]
            exact ih ⟨↑i + 1, i_succ_bound i⟩
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
              have h_i_tri : (↑i : Nat) < s.net[node.val].length ∨ (↑i) = s.net[node.val].length ∨ s.net[node.val].length < (↑i) := (Nat.lt_trichotomy (↑i) s.net[node.val].length)
              cases h_i_tri with
              | inl i_not_last =>
                change (((s.net[↑node.val] ++ [({ mtype := MType.RRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := s.cc.cache[↑s.net[(↑c.threads.val : Nat)].head!.addr.val].data, addr := s.net[(↑c.threads.val : Nat)].head!.addr, ts := s.cc.cache[↑s.net[↑c.threads.val].head!.addr.val].ts, stren := s.net[↑c.threads.val].head!.stren, id := s.msgIds[↑node] } : Message c)]))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id < s.msgIds[↑node] + 1

                simp only [List.getElem_append_left i_not_last]
                change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
                exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
              | inr i_last_or_vac =>
                cases i_last_or_vac with
                | inl i_last =>
                  have : i = Fin.mk s.net[node].length s_netlen_bound := by
                    exact Fin.eq_mk_iff_val_eq.mpr i_last
                  simp [this]
                | inr i_vac =>
                  exfalso
                  have hi1 : i < s.net[node].length + 1 := by
                    have : i < s'.net[node].length := by exact i.isLt
                    simp [h_s'] at this
                    unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers CCSendMsgToSharers send netWithAddedMsg at this
                    simp [h_shim, h, node_src_eq] at this
                    change ↑i < s.net[node.val].length + 1
                    -- unfold send netWithAddedMsg at this ; simp [h_cc] at this
                    exact this
                  have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
                  have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

                  rw [hi3] at i_vac
                  exact (lt_self_iff_false s.net[node].length).mp i_vac
            | inr node_src_neq =>
              simp [node_src_neq]
              have : s'.net[node.val].length = s.net[node.val].length := by
                simp only [h_s']
                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers send netWithAddedMsg
                simp [h, h_shim, node_src_neq]
              change s.net[↑node][Fin.cast this i].id < s.msgIds[↑node]
              exact ih (Fin.cast this i)
        case FREQ =>
          dsimp [mtype] at h ; simp [h]
          unfold popMessage send sendFence netWithAddedMsg
          cases h_cc_or_shim with
          | inl h_cc =>
            simp only [h_cc] at h_ccreceive_from_shim h ⊢
            simp at h_ccreceive_from_shim
            simp [Nat.ne_of_lt h_ccreceive_from_shim]

            have : i.val < s.net[↑node.val].tail.length := by
              have : i.val < s'.net[↑node.val].length := by exact i.isLt
              simp [h_s'] at this
              unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers send sendFence netWithAddedMsg at this
              simp [h_cc, h, Nat.ne_of_lt h_ccreceive_from_shim] at this
              simp
              exact this
            change s.net[↑node.val].tail[Fin.mk i this].id < s.msgIds[↑node.val]
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

            change s.net[↑node][Fin.mk (i + 1) (i_succ_bound i)].id < s.msgIds[↑node]
            exact ih ⟨↑i + 1, i_succ_bound i⟩
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
              have h_i_tri : (↑i : Nat) < s.net[node.val].length ∨ (↑i) = s.net[node.val].length ∨ s.net[node.val].length < (↑i) := (Nat.lt_trichotomy (↑i) s.net[node.val].length)
              cases h_i_tri with
              | inl i_not_last =>
                change (((s.net[↑node.val] ++ [({ mtype := MType.FRESP, src := ⟨↑c.threads, Nat.lt_succ_self c.threads⟩, dst := s.net[↑c.threads.val].head!.src, data := (default : Message c).data, addr := (default : Message c).addr, ts := (default : Message c).ts, stren := (default : Message c).stren, id := s.msgIds[↑node.val] } : Message c)]))[(i : Nat)]'(by simp ; exact Nat.lt_add_right 1 i_not_last)).id < s.msgIds[↑node.val] + 1

                simp only [List.getElem_append_left i_not_last]
                change s.net[node][Fin.mk i i_not_last].id < s.msgIds[node] + 1
                exact Nat.lt_add_right 1 (ih ⟨↑i, i_not_last⟩)
              | inr i_last_or_vac =>
                cases i_last_or_vac with
                | inl i_last =>
                  have : i = Fin.mk s.net[node].length s_netlen_bound := by
                    exact Fin.eq_mk_iff_val_eq.mpr i_last
                  simp [this]
                | inr i_vac =>
                  exfalso
                  have hi1 : i < s.net[node].length + 1 := by
                    have : i < s'.net[node].length := by exact i.isLt
                    simp [h_s'] at this
                    unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers sendFence send netWithAddedMsg at this
                    simp [h_shim, h, node_src_eq] at this
                    change ↑i < s.net[node.val].length + 1
                    -- unfold send netWithAddedMsg at this ; simp [h_cc] at this
                    exact this
                  have hi2 : ¬ i < s.net[node].length := by exact Nat.not_lt_of_gt i_vac
                  have hi3 : ↑i = s.net[node].length := by exact Nat.eq_of_lt_succ_of_not_lt hi1 hi2

                  rw [hi3] at i_vac
                  exact (lt_self_iff_false s.net[node].length).mp i_vac
            | inr node_src_neq =>
              simp [node_src_neq]
              have : s'.net[node.val].length = s.net[node.val].length := by
                simp only [h_s']
                unfold CCReceiveAndPopMsg CCReceive popMessage CCAddSrcShimToSharers send sendFence netWithAddedMsg
                simp [h, h_shim, node_src_neq]
              change s.net[↑node][Fin.cast this i].id < s.msgIds[↑node]
              exact ih (Fin.cast this i)

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
        simp only [h_s']
        have : s'.net[node].length = s.net[node].length := by simp [h_s']
        change s.net[node][Fin.cast this i].id < s.msgIds[node]
        exact ih (Fin.cast this i)

import MemglueVerification.memglueO
import MemglueVerification.randomproofs
import MemglueVerification.c11
import MemglueVerification.proofs


set_option maxHeartbeats 40000000

--this lemma is proving: given I < _po I', their msgId has the same order in CC

-- from proof.lean file which I forgot to import and too lazy to restart file :(
-- def net_ordered {c : SystemConfig} (net : NETOrdered c) : Prop :=
--   forall (node : Node c) (i j : Fin net[node].length),
--     i < j → (net[node][i]).id < (net[node][j]).id

-- lemma net_orderedness_prop {c : SystemConfig} :
--   forall (s : IncState c),
--     increment_reachable s →
--     net_ordered s.net := by
--     sorry


--so that we can use net_orderedness_prop...
lemma send_increments_msgIds {c : SystemConfig}
    (mtype : MType) (src dst : Node c) (data : Data) (addr : Addr c)
    (ts : Timestamp) (stren : OpStrength) (net : NETOrdered c) (msgIds : MessageIds c) :
    (send mtype src dst data addr ts stren net msgIds).2[dst] = msgIds[dst] + 1 := by
  unfold send netWithAddedMsg; simp

--three types of instructions send to CC from shim
def sends_to_cc {c : SystemConfig} (s : IncState c) (shim : ShimId c) : Prop :=
  (getInstr shim s.shimVec s.execution).2.access = PermissionType.store ∨
  (getInstr shim s.shimVec s.execution).2.access = PermissionType.fence ∨
  ((getInstr shim s.shimVec s.execution).2.access = PermissionType.load ∧
   (s.shimVec[shim].state[(getInstr shim s.shimVec s.execution).2.addr]).state ≠ CacheState.Valid)

-- msgId increases by 1 after execution of 1 instruction from shim to CC: write, fence or cache miss
lemma msgId_inc {c : SystemConfig} :
  forall (s s' : IncState c) (shim : ShimId c),
    canIssueInstr shim s →
    s' = getAndIssueInstr shim s →
    ((getInstr shim s.shimVec s.execution).2.access = PermissionType.store ∨
     (getInstr shim s.shimVec s.execution).2.access = PermissionType.fence ∨
     ((getInstr shim s.shimVec s.execution).2.access = PermissionType.load ∧
      (s.shimVec[shim].state[(getInstr shim s.shimVec s.execution).2.addr]).state ≠ CacheState.Valid)) →
    s'.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] =
    s.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] + 1 := by

  intro s s' shim _h_can h_s' h_sends
  rcases h_sends with hw | hf | ⟨hr, hm⟩ --h_miss, two cases
  · --write
    simp [h_s', getAndIssueInstr, hw]
    unfold shimWrite send netWithAddedMsg
    simp
    split <;> simp
  · -- fence
    simp [h_s', getAndIssueInstr, hf, shimFence, sendFence]
  · -- cache read miss
    subst h_s'
    unfold getAndIssueInstr
    simp only [hr]
    unfold shimRead
    simp only []
    split
    case isTrue =>
      simp [send, netWithAddedMsg]
    case isFalse =>
      --simp [send, netWithAddedMsg]
      contradiction

-- IH
lemma msgIds_CC_mono_step {c : SystemConfig} {s s' : IncState c}
    (h_inc: increment_step s s'):
    s.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] ≤
    s'.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] := by

    cases h_inc with
    | ProcessInstr shim _ h_eq =>
      unfold getAndIssueInstr at h_eq; simp at h_eq; split at h_eq
      · unfold shimRead at h_eq; simp at h_eq; split at h_eq --load
        · simp [h_eq]
        · simp [h_eq, send, netWithAddedMsg]
      · unfold shimWrite at h_eq; simp at h_eq; split at h_eq <;> --store
        unfold popInstr at h_eq; simp at h_eq; split at h_eq <;>
        simp [h_eq, send, netWithAddedMsg]
        sorry
      · unfold shimFence at h_eq; simp at h_eq; simp [h_eq, sendFence] --fence

    | ShimProcessMsg shim _ h_eq =>
      sorry

    | CCProcessMsg _ _ _ h_eq =>
      sorry

    | Finish _ _ h_eq => subst h_eq; simp

    --exact net_orderedness_prop increment_reachable


lemma msgIds_CC_mono {c : SystemConfig} : --msgIds increase monotonically
  forall (s s' : IncState c),
    Relation.TransGen increment_step s s' →
    s.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] ≤
    s'.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] := by

    intro s s' htran
    induction htran with
    | single h_step => exact msgIds_CC_mono_step h_step
    | tail htran h_step ih =>
      exact Nat.le_trans ih (msgIds_CC_mono_step h_step)

-- inductive TransGen (R : α → α → Prop) : α → α → Prop
-- | single : R s t → TransGen R s t
-- | tail   : TransGen R s t →
--            R t u →
--            TransGen R s u



lemma qInd_mono_step {c : SystemConfig} (shim : ShimId c) {s s' : IncState c}
    (h : increment_step s s') :
    s.shimVec[shim].qInd ≤ s'.shimVec[shim].qInd := by

    cases h with
    | ProcessInstr shim2 _ h_eq =>
      sorry
      --unfold getAndIssueInstr at h_eq; simp at h_eq; split at h_eq
      -- · unfold shimRead at h_eq; simp at h_eq; split at h_eq
      --   · simp [h_eq]
      --     sorry
      --   · simp [h_eq]
      -- · unfold shimWrite at h_eq; simp at h_eq
      --   split at h_eq <;> (unfold popInstr at h_eq; simp at h_eq; split at h_eq) <;>
      --     simp [h_eq]
      --   sorry
      --· unfold shimFence at h_eq; simp at h_eq

    | ShimProcessMsg shim2 _ h_eq =>
      subst h_eq; simp [shimReceiveAndPopMsg, shimReceive, popMessage]
      sorry

    | CCProcessMsg _ _ _ h_eq =>
    subst h_eq; simp [CCReceiveAndPopMsg, CCReceive, CCAddSrcShimToSharers]

    | Finish _ _ h_eq => subst h_eq; simp


lemma qInd_mono {c : SystemConfig} (shim : ShimId c) {s s' : IncState c}
    (h : Relation.TransGen increment_step s s') :
    s.shimVec[shim].qInd ≤ s'.shimVec[shim].qInd := by
  induction h with
  | single h => exact qInd_mono_step shim h
  | tail _ h ih => exact Nat.le_trans ih (qInd_mono_step shim h)



-- inductive TransGen (R : α → α → Prop) : α → α → Prop
-- | single : R s t → TransGen R s t
-- | tail   : TransGen R s t →
--            R t u →
--            TransGen R s u


lemma sb_cc {c : SystemConfig} :
  forall (s₁ s₂ : IncState c) (shim : ShimId c),
    increment_reachable s₁ →
    increment_reachable s₂ →
    Relation.TransGen increment_step s₁ s₂ →
    canIssueInstr shim s₁ →
    canIssueInstr shim s₂ →
    sends_to_cc s₁ shim →
    sends_to_cc s₂ shim →
    s₁.shimVec[shim].qInd < s₂.shimVec[shim].qInd → --given I1 < I2 where I_i is instruction
    s₁.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] < --msgId follows the same order CC...
    s₂.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] := by


    intro s₁ s₂ shim _h1 _h2 ht hc1 _hc2 hs1 _hs2 h_qInd
    set CC := Fin.mk c.threads (Nat.lt_succ_self c.threads)
    suffices h : s₁.msgIds[CC] + 1 ≤ s₂.msgIds[CC] by omega --sufficient to show less equal relation, so that we can use previous lemmas

    induction ht with  -- trangen induction
    | single h_step =>
      cases h_step with
      | ProcessInstr shim2 h_can2 h_eq =>
        subst h_eq
        by_cases h_same : (shim : ℕ) = (shim2 : ℕ)
        · have heq : shim = shim2 := Fin.ext h_same; subst heq -- this part suggested by llm
          linarith [msgId_inc s₁ _ shim hc1 rfl hs1]
        · exfalso
          have h_ne : (shim : ℕ) ≠ (shim2 : ℕ) := h_same
          unfold getAndIssueInstr at h_qInd; simp at h_qInd; split at h_qInd
          · unfold shimRead at h_qInd; simp at h_qInd; split at h_qInd
            · sorry
            · simp at h_qInd

          · unfold shimWrite at h_qInd; simp at h_qInd
            sorry

          · unfold shimFence at h_qInd; simp at h_qInd
            simp [Vector.getElem_set_ne _ _ (Ne.symm h_ne)] at h_qInd

      | ShimProcessMsg shim2 _ h_eq =>
        subst h_eq; exfalso
        by_cases h_same : (shim : ℕ) = (shim2 : ℕ)
        · sorry
        · sorry

      | CCProcessMsg _ _ _ h_eq =>
        subst h_eq
        simp [CCReceiveAndPopMsg, CCReceive, CCAddSrcShimToSharers] at h_qInd

      | Finish _ _ h_eq => subst h_eq; simp at h_qInd


    | tail h_prefix h_last ih =>
      rename_i smid
      by_cases h_mid : s₁.shimVec[shim].qInd < smid.shimVec[shim].qInd
      · -- qInd increased
        sorry
      · -- qInd unchanged
        push_neg at h_mid
        have h_qInd_eq : smid.shimVec[shim].qInd = s₁.shimVec[shim].qInd := by sorry

        have h_last_qInd : smid.shimVec[shim].qInd < s₂.shimVec[shim].qInd := by sorry

        cases h_last with
        | ProcessInstr shim2 h_can_smid h_eq =>
          sorry

        | ShimProcessMsg shim2 _ h_eq =>
          sorry

        | CCProcessMsg _ _ _ h_eq =>
          subst h_eq
          simp [CCReceiveAndPopMsg, CCReceive, CCAddSrcShimToSharers] at h_last_qInd
          sorry

        | Finish _ _ h_eq =>
          sorry

    --have h_after_issue : (getAndIssueInstr shim s₁).msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] =
       --s₁.msgIds[Fin.mk c.threads (Nat.lt_succ_self c.threads)] + 1 :=


-- timestamp of the address at each shim always ahead of timestamp of cc
def shim_ts_inv {c : SystemConfig} (s : IncState c) : Prop :=
  ∀ (shim : ShimId c) (addr : Addr c),
    s.shimVec[shim].state[addr].ts ≤ s.cc.cache[addr].ts


-- induction step
lemma shim_ts_inv_inductivestep {c : SystemConfig} {s s' : IncState c}
    (h_inv : shim_ts_inv s) (h_step : increment_step s s') :
   shim_ts_inv s' := by
  intro shim addr
  cases h_step
  case ProcessInstr shim2 _ h_eq =>
    unfold getAndIssueInstr at h_eq
    simp at h_eq
    split at h_eq
    · -- load
      unfold shimRead at h_eq; simp at h_eq
      sorry
    · -- store
      unfold shimWrite at h_eq; simp at h_eq
      split at h_eq
      · unfold popInstr at h_eq; simp at h_eq
        split at h_eq
        · simp
          sorry
        · simp
          sorry
      · unfold popInstr at h_eq; simp at h_eq
        split at h_eq
        · simp
          sorry
        · simp
          sorry

    · --fence
      unfold shimFence at h_eq; simp at h_eq
      simp only [h_eq]
      sorry

  case ShimProcessMsg shim_msg _ h_eq =>
    sorry

  case CCProcessMsg _ _ _ h_eq =>
    sorry

  case Finish _ _ h_eq =>
    subst h_eq; exact h_inv shim addr

lemma shim_ts_inv_induction {c : SystemConfig} {s : IncState c}
    (h : increment_reachable s) : shim_ts_inv s := by
  induction h with
  | init e => intro shim addr; simp [default]
  | step s s' h_reach h_step ih => exact shim_ts_inv_inductivestep ih h_step


lemma update_order {c : SystemConfig} (shim : ShimId c) (addr : Addr c)
    {s s' : IncState c}
    (h_ts   : shim_ts_inv s)
    (h_step : increment_step s s') :
    s.shimVec[shim].state[addr].ts ≤ s'.shimVec[shim].state[addr].ts := by
    sorry

lemma update_order_trans {c : SystemConfig} (shim : ShimId c) (addr : Addr c)
    {s s' : IncState c} (h_reach : increment_reachable s)
    (ht : Relation.TransGen increment_step s s') :
    s.shimVec[shim].state[addr].ts ≤ s'.shimVec[shim].state[addr].ts := by
    sorry


def read_completes_with_ts {c : SystemConfig}
    (s : IncState c) (shim : ShimId c) (qi : QInd) (addr : Addr c) (ts : Timestamp) : Prop :=
  s.shimVec[shim].qInd = qi ∧
  canIssueInstr shim s ∧
  (getInstr shim s.shimVec s.execution).2.access = PermissionType.load ∧
  (getInstr shim s.shimVec s.execution).2.addr = addr ∧
  s.shimVec[shim].state[addr].ts = ts


theorem sc_per_location {c : SystemConfig}
    (shim : ShimId c) (addr : Addr c)
    (s s' : IncState c)
    (h_reach : increment_reachable s)
    (h_before  : Relation.TransGen increment_step s s)
    (qi qi' : QInd) (ts ts' : Timestamp)
    (h_R : read_completes_with_ts s shim qi addr ts)
    (h_R' : read_completes_with_ts s' shim qi' addr ts')
    (h_sb : qi < qi) :
    ts ≤ ts := by
    sorry


-- inductive TransGen (R : α → α → Prop) : α → α → Prop
-- | single : R s t → TransGen R s t
-- | tail   : TransGen R s t →
--            R t u →
--            TransGen R s u



--Reference from the other file:

-- inductive increment_step {c : SystemConfig} : IncState c → IncState c → Prop where
--     | ProcessInstr : forall (s s' : IncState c) (shim : ShimId c),
--                 canIssueInstr shim s →
--                 s' = getAndIssueInstr shim s →
--                 increment_step s s'
--     | ShimProcessMsg : forall (s s' : IncState c) (shim : ShimId c),
--                 (s.net[(shim.castSucc)]).length > 0 →
--                 s' = shimReceiveAndPopMsg shim s →
--                 increment_step s s'
--     | CCProcessMsg : forall (s s' : IncState c),
--                 (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)]).length > 0 →
--                 valid_CCReceive_MType (s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)].head!).mtype →
--                 ↑(s.net[Fin.mk c.threads (Nat.lt_succ_self c.threads)].head!).src.val < (↑c.threads.val) →
--                 s' = CCReceiveAndPopMsg s →
--                 increment_step s s'
--     | Finish : forall (s s' : IncState c),
--              s.done = false → isDone s → s' = {s with done := true} →
--              increment_step s s'


-- def getInstr {c : SystemConfig} (shim : ShimId c) (shimVec : ShimType c) (e : Execution c)
-- : (Execution c) × (Instr c) :=
--     let qInd := (shimVec[shim]).qInd

--     let instr' := {e[shim].list[qInd]! with pend := true}
--     let list' := e[shim].list.set qInd instr'
--     let e' := e.set shim {list := list', nonempty := (by unfold list'; simp; exact e[↑shim].nonempty)}
--     -- let e' :=
--     --     fun (t : ShimId c) =>
--     --         fun (s : Fin c.steps) =>
--     --             if t = shim ∧ s = qInd then {e t s with pend := true}
--     --             else e t s
--     (e', e'[shim].list[qInd]!)

-- -- Call the appropriate functions given an instruction
-- def getAndIssueInstr {c : SystemConfig} (shim : ShimId c) (state : IncState c) : IncState c :=
--     let (e', instr) := getInstr shim state.shimVec state.execution
--     let state' := {state with execution := e'}

--     match instr.access with
--     | PermissionType.load =>
--         let (shimVec', net', e'', msgIds') := shimRead shim instr.addr instr.stren state'.shimVec state'.net state'.execution state'.msgIds
--         let state'' := {state' with shimVec := shimVec', net := net', execution := e'', msgIds := msgIds'}
--         state''
--     | PermissionType.store =>
--         let (shimVec', e'', net', msgIds') := shimWrite shim instr.addr instr.data instr.stren state'.shimVec state'.execution state'.net state'.msgIds
--         let state'' := {state' with shimVec := shimVec', execution := e'', net := net', msgIds := msgIds'}
--         state''
--     | PermissionType.fence =>
--         let (shimVec', net', msgIds') := shimFence shim state'.shimVec state'.net state'.msgIds
--         let state'' := {state' with shimVec := shimVec', net := net', msgIds := msgIds'}
--         state''

-- def canIssueInstr {c : SystemConfig} (shimId : ShimId c) (state : IncState c) : Prop :=
--     let shimStruct := state.shimVec[shimId]
--     (
--         shimStruct.active = true ∧
--         shimStruct.fencePending = false ∧
--         shimStruct.pendingWSC = false ∧
--         (state.execution[shimId].list[shimStruct.qInd]!).pend = false
--     )

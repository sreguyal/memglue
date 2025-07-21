import Mathlib
import MemglueVerification.memglueO

abbrev rlt (α : Type) := Rel α α
def example_relation : rlt Nat :=
    fun a => fun b => a = b

abbrev EventId := Nat × Nat

inductive Mode where
    | NA | RLX | ACQ | REL | ACQREL | SC
    deriving DecidableEq

def same_stren (s : OpStrength) (m : Mode) : Bool :=
    match (s, m) with
    | (OpStrength.RLX, Mode.RLX)
    | (OpStrength.ACQ, Mode.ACQ)
    | (OpStrength.REL, Mode.REL)
    | (OpStrength.SC, Mode.SC) => true
    | _ => false

structure Event (c : SystemConfig) where
    access : PermissionType
    mode : Mode
    addr : Addr c
    data : Data
    eid : EventId
deriving DecidableEq

def executionToSet {c : SystemConfig} (e : Execution c) : Set (Event c) :=
    let evts_from_exe :=
        {a : Event c | ∃ (t : ShimId c) (s : QInd c),
        (e t s).access = a.access ∧
        (e t s).addr = a.addr ∧
        (e t s).data = a.data ∧
        (same_stren (e t s).stren a.mode) ∧
        a.eid = (t.val, s.val) ∧
        (e t s).access ≠ PermissionType.none}
    let initialization_evts : Set (Event c) := (Finset.image
        (fun i =>
            ({ access := PermissionType.store, mode := Mode.SC, addr := Fin.ofNat c.addrCount i, data := 0, eid := (c.threads + i, 0) } : Event c))
        (Finset.range c.addrCount)).toSet

    evts_from_exe ∪ initialization_evts

open Mode
def weaker_mode (m1 m2 : Mode) : Bool :=
match (m1, m2) with
  | (NA, NA) => false
  | (NA, _) => true
  | (RLX, NA) | (RLX, RLX) => false
  | (RLX, _) => true
  | (ACQ, ACQREL) | (ACQ, SC) => true
  | (ACQ, _) => false
  | (REL, ACQREL) | (REL, SC) => true
  | (REL, _) => false
  | (ACQREL, SC) => true
  | (ACQREL, _) => false
  | (SC, _) => false

def stronger_or_eq_mode (m1 m2 : Mode) : Bool :=
    ¬ (weaker_mode m1 m2)

/-(** [res_eq_loc r] restricts a relation [r] to the pairs of events that affect
the same location *)
-/
def res_eq_loc {c : SystemConfig} (r : rlt (Event c)) : rlt (Event c) :=
    (fun x =>
        fun y =>
            (r x y) ∧ (x.addr = y.addr))

def res_neq_loc {c : SystemConfig} (r : rlt (Event c)) : rlt (Event c) :=
    (fun x =>
        fun y =>
            (r x y) ∧ (x.addr ≠ y.addr))

def imm {α : Type} (r : rlt α) : rlt α :=
    fun a => fun b =>
        r a b ∧
        (forall c, r c b → r c a) ∧
        (forall c, r a c → r b c)


def partial_order {α : Type} (r : rlt α) (xs : Set α) : Prop :=
  (∀ x y, r x y → x ∈ xs ∧ y ∈ xs) ∧
  (∀ x y z, r x y ∧ r y z → r x z) ∧
  (∀ x, ¬ r x x)

def total_rel {α : Type} (r : rlt α) (xs : Set α) : Prop :=
    forall (x y : α), (x ≠ y ∧ x ∈ xs ∧ y ∈ xs) →
        ((r x y) ∨ (r y x))

def writes_loc {c : SystemConfig} (evts : Set (Event c)) (addr : Addr c) : Set (Event c) :=
    {e | e ∈ evts ∧ e.access = PermissionType.store ∧ e.addr = addr}

open Mode
def read_mode (m : Mode) : Prop :=
    match m with
    | NA
    | RLX
    | ACQ
    | SC => True
    | _ => False

def write_mode (m : Mode) : Prop :=
    match m with
    | NA | RLX | REL | SC => True
    | _ => False

def fence_mode (m : Mode) : Prop :=
  match m with
  | ACQ | REL | ACQREL | SC => True
  | _ => False

def valid_mode {c : SystemConfig} (e : Event c) : Prop :=
    match e.access with
    | PermissionType.load => read_mode e.mode
    | PermissionType.store => write_mode e.mode
    | PermissionType.fence => fence_mode e.mode
    | PermissionType.none => panic! "a;skdfj"

def valid_evts {c : SystemConfig} (evts : Set (Event c)) : Prop :=
    (∀ e1 e2, e1 ∈ evts ∧ e2 ∈ evts →
        e1.eid ≠ e2.eid ∨ e1 = e2) ∧
    (∀ e, e ∈ evts → valid_mode e)

----------------------------------------------------------------
/-Base relations-------------------------------------------------/
----------------------------------------------------------------
def valid_sb {c : SystemConfig} (evts : Set (Event c)) (sb : rlt (Event c)) : Prop :=
    partial_order sb evts ∧
    forall (addr : Addr c), exists (e : Event c),
        (e.eid.1 ≥ c.threads) ∧        -- an event that is an initialization event
        (e.addr = addr ∧ e.data = 0) ∧
        (forall e', ¬ (sb e' e)) ∧
        (forall e', (exists e'', sb e'' e') → sb e e')

-------------------------------------------------------
def valid_rmw_pair {c : SystemConfig} (sb : rlt (Event c)) (r : Event c) (w : Event c) : Prop :=
    match (r.mode, w.mode) with
    | (RLX, RLX)
    | (ACQ, RLX)
    | (RLX, REL)
    | (ACQ, REL)
    | (SC, SC) =>
        (r.access = PermissionType.load ∧
         w.access = PermissionType.store ∧
         r.addr = w.addr ∧
         (imm sb) r w)
    | _ => false

def valid_rmw {c : SystemConfig} (evts : Set (Event c)) (sb : rlt (Event c)) (rmw : rlt (Event c)) : Prop :=
    (∀ r w, rmw r w → valid_rmw_pair sb r w) ∧
    (∀ r w, rmw r w → r ∈ evts ∧ w ∈ evts)
------------------------------------------------------
def valid_rf {c : SystemConfig} (evts : Set (Event c)) (rf : rlt (Event c)) : Prop :=
    (forall w r,
        rf w r →
            (w.addr = r.addr ∧
            w.data = r.data) ∧
            (w ∈ evts ∧ r ∈ evts) ∧
            (w.access = PermissionType.store ∧
            r.access = PermissionType.load)) ∧
    ∀ w1 w2 r,
        (rf w1 r) ∧ (rf w2 r) → w1 = w2
-------------------------------------------------------
def mo_for_loc {c : SystemConfig} (mo : rlt (Event c)) (addr : (Addr c)) : rlt (Event c) :=
    fun w1 => fun w2 =>
        mo w1 w2 ∧
        w1.addr = addr ∧ w2.addr = addr

def valid_mo {c : SystemConfig} (evts : Set (Event c)) (mo : rlt (Event c)) : Prop :=
    (∀ w1 w2, mo w1 w2 →
        w1.access = PermissionType.store ∧
        w2.access = PermissionType.store ∧
        w1.addr = w2.addr) ∧
    (partial_order mo evts) ∧
    (forall addr, total_rel (mo_for_loc mo addr) (writes_loc evts addr))
----------------------------------------------------------




structure ExecutionGraph (c : SystemConfig) : Type where
    evts : Set (Event c)
    sb : rlt (Event c)
    rmw : rlt (Event c)
    rf :  rlt (Event c)
    mo : rlt (Event c)

def valid_exec_graph {c : SystemConfig} (eg : ExecutionGraph c) : Prop :=
    valid_evts eg.evts ∧
    valid_sb eg.evts eg.sb ∧
    valid_rmw eg.evts eg.sb eg.rmw ∧
    valid_rf eg.evts eg.rf ∧
    valid_mo eg.evts eg.mo
----------------------------------------------

def restrict_rel {c : SystemConfig} (r : rlt (Event c)) (p q : (Event c) → Prop) : rlt (Event c) :=
    fun e1 =>
        fun e2 =>
            r e1 e2 ∧ p e1 ∧ q e2

def is_write {c : SystemConfig} (e : Event c) : Prop :=
    e.access = PermissionType.store

def id_rel {c : SystemConfig} : rlt (Event c) :=
    fun x y => x = y

def is_fence {c : SystemConfig} (e : Event c) : Prop := e.access = PermissionType.fence

def fence_id {c : SystemConfig} : rlt (Event c) :=
    restrict_rel id_rel is_fence is_fence



--------------------------------------------------------------------
/-Derived relations-------------------------------------------------/
--------------------------------------------------------------------

/-(** ** Release sequence *)

(** The release sequence of a write event contains the write itself (if it is
atomic) and all later atomic writes to the same location in the same thread, as
well as all read-modify-write that recursively read from such writes. *)

Definition rs  :=
  [W] ⋅ (res_eq_loc (sb ex)) ? ⋅ [W] ⋅ [Mse Rlx] ⋅ ((rf ex) ⋅ (rmw ex)) ^*.-/



def rs {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let optional_sb : rlt (Event c) := Relation.ReflGen (res_eq_loc eg.sb)

    let is_atomic_w : Event c → Prop :=
        fun (e : Event c) =>
            e.access = PermissionType.store ∧
            (stronger_or_eq_mode e.mode RLX)

    let W_sb_opt_atomic_W : rlt (Event c) := restrict_rel optional_sb is_write is_atomic_w

    let rf_rmw := Rel.comp eg.rf eg.rmw
    let iter := Relation.ReflTransGen rf_rmw

    Rel.comp W_sb_opt_atomic_W iter


/-(** ** Synchronises with *)

(** A release event [a] synchronises with an acquire event [b] whenever [b] (or,
in case [b] is a fence, a [sb]-prior read) reads from the release sequence of
[a] *)-/

/-Definition sw :=
  [Mse Rel] ⋅ ([F] ⋅ (sb ex)) ? ⋅ rs ⋅ (rf ex) ⋅ [R] ⋅ [Mse Rlx] ⋅ ((sb ex) ⋅ [F]) ? ⋅ [Mse Acq].-/
def sw {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let geq_rel_filter : Event c → Prop :=
        fun e => stronger_or_eq_mode e.mode REL

    --? need fence_id here because how else can i compose and do reflgen?
    let optional_fence_sb : rlt (Event c) := Relation.ReflGen (Rel.comp fence_id eg.sb)
    --? could do ↓
    -- let optional_fence_sb : rlt (Event c) := Relation.ReflGen (restrict_rel eg.sb is_fence (fun e => true))

    let geq_rlx_r_filter : Event c → Prop :=
        fun e => stronger_or_eq_mode e.mode RLX ∧
                 e.access = PermissionType.load

    -- [Mse Rel] ⋅ ([F] ⋅ (sb ex)) ? ⋅ rs ⋅ (rf ex) ⋅ [R] ⋅ [Mse Rlx]
    let opt_f_sb_rs_rf := (Rel.comp ((Rel.comp optional_fence_sb (rs eg))) eg.rf)
    let base :=
        restrict_rel opt_f_sb_rs_rf geq_rel_filter geq_rlx_r_filter

    let optional_sb_fence : rlt (Event c) := Relation.ReflGen (Rel.comp eg.sb fence_id)

    let geq_acq_filter : Event c → Prop :=
        fun e => stronger_or_eq_mode e.mode ACQ
    let geq_acq : rlt (Event c) := restrict_rel id_rel geq_acq_filter geq_acq_filter

    Rel.comp (Rel.comp base optional_sb_fence) geq_acq
    -- Rel.comp (Rel.comp (Rel.comp (Rel.comp (Rel.comp (Rel.comp (Rel.comp
        -- geq_rel
        -- optional_fence_sb)
        -- (rs eg))
        -- eg.rf)
        -- read_id)
        -- geq_rlx)
        -- optional_sb_fence)
        -- geq_acq

/-(** ** Reads-before *)

(** A read event [r] reads-before a write event [w] if it reads-from a write
event sequenced before [w] by the modification order. It corresponds to the
from-read relation in some other works on axiomatic memory models. *)

Definition rb :=
  (rf ex) ° ⋅ (mo ex).-/

def rb {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let rf_inv :=
        fun e1 =>
            fun e2 =>
                eg.rf e2 e1
    Rel.comp rf_inv eg.mo
    -- λ r w => ∃ w', eg.rf w' r ∧ eg.mo w' w

/-(** ** Happens-before *)

(** Intuitively, the happens-before relation records when an event is globally
perceived as occurring before another one.
We say that an event happens-before another one if there is a path between the
two events consisting of [sb] and [sw] edges *)

Definition hb  :=
  ((sb ex) ⊔ sw)^+.-/

def hb {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let union_sb_sw : rlt (Event c) :=
        fun e1 =>
            fun e2 =>
                eg.sb e1 e2 ∨ (sw eg e1 e2)
    Relation.TransGen union_sb_sw


/-(** ** SC-before *)

Definition scb :=
 (sb ex) ⊔  ((res_neq_loc (sb ex)) ⋅ hb ⋅ (res_neq_loc (sb ex))) ⊔ (res_eq_loc hb) ⊔ (mo ex) ⊔  (rb ex).-/

 def scb {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let opt1 := eg.sb
    let opt2 := Rel.comp (Rel.comp (
        res_neq_loc eg.sb)
        (hb eg))
        (res_neq_loc eg.sb)
    let opt3 := res_eq_loc (hb eg)
    let opt4 := eg.mo
    let opt5 := rb eg

    fun e1 => fun e2 =>
        opt1 e1 e2 ∨ opt2 e1 e2 ∨
        opt3 e1 e2 ∨ opt4 e1 e2 ∨
        opt5 e1 e2

/-(** ** Partial-SC base *)

(** We give a semantic to SC atomics by enforcing the order in which they should
occur *)-/

def psc_base {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let is_sc : Event c → Prop := fun e => e.mode = Mode.SC
    let M_sc : rlt (Event c) := restrict_rel id_rel is_sc is_sc

    let F_M_sc_opt_hb := Rel.comp (Rel.comp
        fence_id
        M_sc)
        (Relation.ReflGen (hb eg))

    let part1 := fun e1 => fun e2 =>
        M_sc e1 e2 ∨ F_M_sc_opt_hb e1 e2
    /-Definition psc_base :=
  ([M Sc] ⊔ (([F] ⋅ [M Sc]) ⋅ (hb ?))) ⋅
  (scb) ⋅
  ([M Sc] ⊔ ((hb ?) ⋅ ([F] ⋅ [M Sc]))).-/

    let opt_hb_F_M_sc : rlt (Event c) := Rel.comp
        (Relation.ReflGen (hb eg))
        (Rel.comp fence_id
        M_sc)
    let part3 := fun e1 => fun e2 =>
        M_sc e1 e2 ∨ opt_hb_F_M_sc e1 e2

    Rel.comp (Rel.comp part1 (scb eg)) part3

/-(** ** Extended coherence order *)

(** The extended coherence order is the transitive closure of the union of
reads-from, modification order and reads-before. It corresponds to the
communication relation in some other works on axiomatic memory models *)

Definition eco := ((rf ex) ⊔ (mo ex) ⊔ rb)^+.-/
def eco {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let union : rlt (Event c) :=
        fun e1 =>
            fun e2 =>
                eg.rf e1 e2 ∨
                eg.mo e1 e2 ∨
                (rb eg) e1 e2

    Relation.TransGen union


/-(** ** Partial-SC fence *)

(** We give a semantic to SC fences by enforcing the order in which they should
occur *)

Definition psc_fence :=
  [F] ⋅ [M Sc] ⋅ (hb ⊔ (hb ⋅ (eco ex) ⋅ hb)) ⋅ [F] ⋅ [M Sc].
-/

def psc_fence {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    let f_sc_filter : Event c → Prop :=
        fun e => e.access = PermissionType.fence ∧ e.mode = SC
    let hb_eco_hb := Rel.comp (Rel.comp (hb eg) (eco eg)) (hb eg)
    let union : rlt (Event c) :=
        fun e1 =>
            fun e2 =>
                (hb eg) e1 e2 ∨ hb_eco_hb e1 e2

    restrict_rel union f_sc_filter f_sc_filter


/-(** ** Partial SC *)

Definition psc :=
  psc_base ⊔ psc_fence.-/

def psc {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=
    fun e1 =>
        fun e2 =>
            (psc_base eg) e1 e2 ∨ (psc_fence eg) e1 e2

---------------------------------------------------------------------
/-C11 Axioms-------------------------------------------------------/
---------------------------------------------------------------------

/-Definition coherence :=
  forall x, ~(hb ⋅ (eco ex) ?) x x.-/

def coherence {c : SystemConfig} (eg : ExecutionGraph c) : Prop :=
    forall x, ¬(Rel.comp (hb eg) (Relation.ReflGen (eco eg))) x x


/-(** In a coherent execution, [hb] is irreflexive. This means that an event
should not occur before itself. *)

Lemma coherence_irr_hb:
  coherence -> (forall x, ~hb x x).
Proof.
  intros H x Hnot.
  apply (H x). exists x.
  - auto.
  - right. simpl; auto.
Qed.-/
lemma coherence_irr_hb {c : SystemConfig} (eg : ExecutionGraph c) : coherence eg → (forall x, ¬ (hb eg) x x) := by
    intros H x Hnot  -- H: forall x, ¬ (hb ∘ (eco?)) x x
    apply H x           -- x is st hb x x (proving by contradiction with Hnot, i assume)
    use x
    -- constructor
    -- · exact Hnot
    -- · apply Relation.reflTransGen.refl


/-(** ** Atomicity *)

(** Atomicity ensures that the read and the write composing a RMW pair are
adjacent in [eco]: there is no write event in between *)

Definition atomicity :=
  forall x y, ~ ((rmw ex) ⊓ ((rb ex) ⋅ (mo ex))) x y.-/

def atomicity {c : SystemConfig} (eg : ExecutionGraph c) : Prop :=
    let rmw_and_rb_mo : rlt (Event c) :=
        fun e1 =>
            fun e2 =>
                eg.rmw e1 e2 ∧
                (Rel.comp (rb eg) eg.mo) e1 e2
    forall x y, ¬ rmw_and_rb_mo x y

/-(** ** SC *)

(** The SC condition gives a semantic to SC atomics and fences in executions. It
is defined. It is defined  *)

Definition SC :=
  acyclic psc.-/

def acyclic {c : SystemConfig} (r : rlt (Event c)) : Prop :=
    Irreflexive (Relation.TransGen r)

def SC {c : SystemConfig} (eg : ExecutionGraph c) : Prop :=
    acyclic (psc eg)


/-(** ** No-thin-air *)

(** We want to forbid out-of-thin-air, which means excluding executions where
the value written by a write event depends on the value read by a read event,
which reads from this same write event. *)

Definition no_thin_air :=
  acyclic ((sb ex) ⊔ (rf ex)).
-/

def no_thin_air {c : SystemConfig} (eg : ExecutionGraph c) : Prop :=
    let sb_or_rf : rlt (Event c) :=
        fun e1 =>
            fun e2 =>
                eg.sb e1 e2 ∨ eg.rf e1 e2
    acyclic sb_or_rf


/-(** ** RC11-consistent executions *)

(** An execution is RC11-consistent when it verifies the four conditions we just
defined *)

Definition rc11_consistent :=
  coherence /\ atomicity /\ SC /\ no_thin_air.-/
def rc11_consistent {c : SystemConfig} (eg : ExecutionGraph c) : Prop :=
    coherence eg ∧ atomicity eg ∧ SC eg ∧ no_thin_air eg

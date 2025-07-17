import Mathlib
import MemglueVerification.memglueO

def rlt (α : Type) := α → α → Prop
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
    -- instr : Instr c
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
-- ? does mode matter here
    evts_from_exe ∪ initialization_evts


-- #eval Std.Set.ofList (executionToSet (default : Execution default))
----------------------------------------------
-- some functions

-- def W {c : SystemConfig} (evts : Set (Event c)) : Set (Event c) :=
--     {evt | evt ∈ evts ∧ evt.access = PermissionType.store}

-- def R {c : SystemConfig} (evts : Set (Event c)) : Set (Event c) :=
--     {evt | evt ∈ evts ∧ evt.access = PermissionType.load}

-- def F {c : SystemConfig} (evts : Set (Event c)) : Set (Event c) :=
--     {evt | evt ∈ evts ∧ evt.access = PermissionType.fence}

/-(** [res_eq_loc r] restricts a relation [r] to the pairs of events that affect
the same location *)
-/
def res_eq_loc {c : SystemConfig} (r : rlt (Event c)) : rlt (Event c) :=
    (fun x =>
        fun y =>
            (r x y) ∧ (x.addr = y.addr))

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






----------------------------------------------------------
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



/-(** ** Release sequence *)

(** The release sequence of a write event contains the write itself (if it is
atomic) and all later atomic writes to the same location in the same thread, as
well as all read-modify-write that recursively read from such writes. *)

Definition rs  :=
  [W] ⋅ (res_eq_loc (sb ex)) ? ⋅ [W] ⋅ [Mse Rlx] ⋅ ((rf ex) ⋅ (rmw ex)) ^*.-/

def restrict_rel {c : SystemConfig} (r : rlt (Event c)) (p q : (Event c) → Prop) : rlt (Event c) :=
    fun e1 =>
        fun e2 =>
            r e1 e2 ∧ p e1 ∧ q e2

def is_write {c : SystemConfig} (e : Event c) : Prop :=
    e.access = PermissionType.store

-- def write_id {c : SystemConfig} : rlt (Event c) :=
--     restrict_rel id is_write is_write

def rs {c : SystemConfig} (eg : ExecutionGraph c) : rlt (Event c) :=

    eg.sb

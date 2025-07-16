import MemglueVerification.memglueO

def rlt (α : Type) := α → α → Prop
-- TODO separate instruction type for c11 vs memglue
abbrev EventId (c : SystemConfig) := (ShimId c) × (QInd c)
structure Event (c : SystemConfig) where
    instr : Instr c
    eid : EventId c

-- ? if we use a set and the events have no thread field, is there no notion of separate threads`
-- ? in the coq implementation and the murphi model, they put read values in the event/instruction, as opposed to having a separate output traceset. should we also do this, but then that makes the Output type redundant
-- ? coq implementation had modes not in memglue version. put in.
/-Inductive Mode : Set :=
| Na : Mode < rlx
| Rlx : Mode
| Acq : Mode
| Rel : Mode
| AcqRel : Mode fence
| Sc : Mode.
vs
inductive OpStrength : Type where
    | RLX
    | REL
    | ACQ
    | SC
    -/
open OpStrength PermissionType
def executionToSet {c : SystemConfig} (e : Execution c) : Set (Event c) :=
    -- {a | ∃ (t : ShimId c) (s : QInd c), e t s = a}
    {a | ∃ (t : ShimId c) (s : QInd c), a.instr = e t s ∧ a.eid = (t, s) ∧
    (e t s).access ≠ PermissionType.none} -- ? should i filter this out?
-- #eval Std.Set.ofList (executionToSet (default : Execution default))


def imm {α : Type} (r : rlt α) : rlt α :=
    fun a => fun b =>
        r a b ∧
        (forall c, r c b → r c a) ∧
        (forall c, r a c → r b c)
/-
(** There is an immediate edge between two elements [a] and [b] of a strict partial
order if :

- there is no event before [b] but not before [a] in the relation
- there is no event after [a] but not after [b] in the relation
 *)

Definition imm {A: Type} (r: rlt A) : rlt A :=
  fun a => fun b =>
    r a b /\
    (forall c, r c b -> (r ?) c a) /\
    (forall c, r a c -> (r ?) b c).
---/


def partial_order {α : Type} (r : rlt α) (xs : Set α) : Prop :=
  (∀ x y, r x y → x ∈ xs ∧ y ∈ xs) ∧
  (∀ x y z, r x y ∧ r y z → r x z) ∧
  (∀ x, ¬ r x x)
/-
Definition partial_order {A:Type} (r:rlt A) (xs: Ensemble A) : Prop :=
  r = [I xs] ⋅ r ⋅ [I xs] /\ (* Inclusion in the set *)
  (r ⋅ r ≦ r)/\ (* Transitivity *)
  (forall x, ~(r x x)).     (* Irreflexivity *)
--/

/-Definition total_rel {A:Type} (r:rlt A) (xs: Ensemble A) : Prop :=
  forall x y, (x <> y) ->
              (In _ xs x) ->
              (In _ xs y) ->
              (r x y) \/ (r y x).-/
def total_rel {α : Type} (r : rlt α) (xs : Set α) : Prop :=
    forall (x y : α), (x ≠ y ∧ x ∈ xs ∧ y ∈ xs) →
        ((r x y) ∨ (r y x))

/-Definition writes_loc (evts: Ensemble Event) (l: Loc) : Ensemble Event :=
  fun e =>
    (In _ evts e) /\
    is_write e /\
    (get_loc e) = Some l.-/
def writes_loc {c : SystemConfig} (evts : Set (Event c)) (addr : Addr c) : Set (Event c) :=
    {e | e ∈ evts ∧ e.instr.access = PermissionType.store ∧ e.instr.addr = addr}
-- TODO valid_mode, read/write/fence_mode
def valid_mode {c : SystemConfig} (e : Event c) : Prop :=
    match e.instr.access with
    | load => True -- TODO replace with read_mode
    | store => True
    | fence => True
    | PermissionType.none => panic! "a;skdfj"
/-Definition valid_mode (e: Event) : Prop :=
  match e with
  | Read _ m _ _ => read_mode m
  | Write _ m _ _ => write_mode m
  | Fence _ m => fence_mode m
  end.Definition valid_mode (e: Event) : Prop :=
  match e with
  | Read _ m _ _ => read_mode m
  | Write _ m _ _ => write_mode m
  | Fence _ m => fence_mode m
  end.-/

/-Definition valid_evts (evts: Ensemble Event) : Prop :=
  (forall e1 e2, (In _ evts e1) -> (In _ evts e2) ->
    (get_eid e1) <> (get_eid e2) \/ e1 = e2) /\
  (forall e, (In _ evts e) -> valid_mode e).-/

def valid_evts {c : SystemConfig} (evts : Set (Event c)) : Prop :=
    (∀ e1 e2, e1 ∈ evts ∧ e2 ∈ evts → e1.eid ≠ e2.eid ∨ e1 = e2) ∧
    (∀ e, e ∈ evts → valid_mode e)







def valid_sb {c : SystemConfig} (evts : Set (Event c)) (sb : rlt (Event c)) : Prop :=
    partial_order sb evts
/-
Definition valid_sb (evts: Ensemble Event) (sb : rlt Event) : Prop :=
  (partial_order sb evts) /\
--/
-- ? are we supposed to have initialization instructions in our Execution?
/-
  (forall (l : Loc),
  exists (e: Event),
    (get_loc e) = Some l /\
    (get_val e) = Some O /\
    ~(In _ (ran sb) e) /\
    forall e', In _ (ran sb) e' -> sb e e').
--/



def valid_rmw_pair {c : SystemConfig} (sb : rlt (Event c)) (r : Event c) (w : Event c) : Prop :=
    match (r.instr.stren, w.instr.stren) with
    | (RLX, RLX) | (ACQ, RLX) | (RLX, REL) | (ACQ, REL) | (SC, SC) =>
        (r.instr.access = load ∧ w.instr.access = store ∧
         r.instr.addr = w.instr.addr ∧
         (imm sb) r w)
    | _ => false
-- end OpStrength, PermissionType
/-
Definition valid_rmw_pair (sb : rlt Event) (r: Event) (w: Event) : Prop :=
  match (get_mode r, get_mode w) with
  | (Rlx, Rlx) | (Acq, Rlx) | (Rlx, Rel) | (Acq, Rel) | (Sc, Sc) =>
    (is_read r /\
     is_write w /\
     (get_loc r) = (get_loc w) /\
     (imm sb) r w)
  | _ => False
  end.
----/
def valid_rmw {c : SystemConfig} (evts : Set (Event c)) (sb : rlt (Event c)) (rmw : rlt (Event c)) : Prop :=
    (∀ r w, rmw r w → valid_rmw_pair sb r w) ∧
    (∀ r w, rmw r w → r ∈ evts ∧ w ∈ evts)
/-
A read-modify-write relation is a set of read-modify-write pairs

Definition valid_rmw (evts: Ensemble Event) (sb : rlt Event) (rmw : rlt Event) : Prop :=
  (forall r w, rmw r w -> valid_rmw_pair sb r w) /\
  (rmw = [I evts] ⋅ rmw ⋅ [I evts]).---/

/-
(** ** Reads-from relation *)

(** The reads-from relation connects a write and a read events of the same value to
the same location and is such that if [rf r1 w] and [rf r2 w], then [r1 = r2].
To put it more simply, the read-from relation connects every read event to
exactly one write event that wrote the value it reads
*)
---/
def valid_rf {c : SystemConfig} (evts : Set (Event c)) (rf : rlt (Event c)) : Prop :=
    (forall w r,
        rf w r →
            (w.instr.addr = r.instr.addr ∧
            w.instr.data = r.instr.data) ∧
            (w ∈ evts ∧ r ∈ evts) ∧
            (w.instr.access = store ∧ r.instr.access = load)) ∧
    ∀ w1 w2 r,
        (rf w1 r) ∧ (rf w2 r) → w1 = w2
/-
Definition valid_rf (evts : Ensemble Event) (rf : rlt Event) : Prop :=
  (forall w r,
    rf w r ->
    ((get_loc w) = (get_loc r) /\
     (get_val w) = (get_val r))) /\
  (rf = [I evts] ⋅ rf ⋅ [I evts]) /\
  ([W]⋅rf⋅[R] = rf) /\
  (forall w1 w2 r,
    (rf w1 r) /\ (rf w2 r) -> w1 = w2).
----/


/-
(** ** Modification order *)

(** The modification order is a strict partial order on the write events, which
is the disjoint union of total orders on the write events to a specific location
for each location.
It correponds to write serialisation or coherence order in some other works on
axiomatic memory models.
*)
---/
def mo_for_loc {c : SystemConfig} (mo : rlt (Event c)) (addr : (Addr c)) : rlt (Event c) :=
    fun w1 => fun w2 =>
        mo w1 w2 ∧
        w1.instr.addr = addr ∧ w2.instr.addr = addr

def valid_mo {c : SystemConfig} (evts : Set (Event c)) (mo : rlt (Event c)) : Prop :=
    (∀ w1 w2, mo w1 w2 →
        w1.instr.access = store ∧ w2.instr.access = store ∧
        w1.instr.addr = w2.instr.addr) ∧
    (partial_order mo evts) ∧
    (forall addr, total_rel (mo_for_loc mo addr) (writes_loc evts addr))
/-
Definition mo_for_loc (mo : rlt Event) (l : Loc) : rlt Event :=
  fun w1 => fun w2 =>
    mo w1 w2 /\
    (get_loc w1) = (Some l) /\
    (get_loc w2) = (Some l).

Definition valid_mo (evts: Ensemble Event) (mo : rlt Event) : Prop :=
  ([W]⋅mo⋅[W] = mo) /\
  (forall x y, mo x y ->
               (get_loc x) = (get_loc y)) /\
  (partial_order mo evts) /\
  (forall l, total_rel (mo_for_loc mo l) (writes_loc evts l)).
---/


/-(** * Executions *)

(** ** Validity *)

(** An execution is:
- A set of events with valid modes
- A valid sequenced-before relation on these events
- A valid reads-from relation on these events
- A valid modification order on these events
*)
-/
structure ExecutionGraph (c : SystemConfig) : Type where
    evts : Set (Event c)
    sb : rlt (Event c)
    rmw : rlt (Event c)
    rf :  rlt (Event c)
    mo : rlt (Event c)

/-
Record Execution : Type := mkex {
  evts : Ensemble Event;
  sb : rlt Event;
  rmw : rlt Event;
  rf : rlt Event;
  mo : rlt Event;
}.

Definition valid_exec (e: Execution) : Prop :=
  (* valid events mode *)
  valid_evts e.(evts) /\
  (* sequenced-before is valid *)
  valid_sb e.(evts) e.(sb) /\
  (* read-modify-write is valid *)
  valid_rmw e.(evts) e.(sb) e.(rmw) /\
  (* reads-from is valid *)
  valid_rf e.(evts) e.(rf) /\
  (* modification order is valid *)
  valid_mo e.(evts) e.(mo).-/

-- def valid_exec_graph {c : SystemConfig} (e : ExecutionGraph c) : Prop :=

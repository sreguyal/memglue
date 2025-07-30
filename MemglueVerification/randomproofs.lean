import MemglueVerification.memglueO
import MemglueVerification.c11

variable (p q r : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

open Classical
#check Classical.em p
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (Classical.em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h₁ : p ∧ q => ⟨h₁.right, h₁.left⟩)
    (fun h₂ : q ∧ p => ⟨h₂.right, h₂.left⟩)

example : p ∨ ¬p := Classical.em p

-- de morgans
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h₁ : ¬(p ∨ q) =>   -- ¬(p ∨ q) → ¬p ∧ ¬q
      And.intro
        (fun hp : p => h₁ (Or.intro_left q hp)) -- prove ¬ p which is equivalent to p → False
        (fun hq : q => h₁ (Or.intro_right p hq)) -- prove that ¬ q meaning assume q and show False) _
    )
    (fun h₂ : ¬p ∧ ¬q =>   --  ¬p ∧ ¬q → ¬(p ∨ q)
      (fun h : p ∨ q => -- WTS (p ∨ q) → False
        Or.elim h       -- proof by cases. assume p ∨ q, and in each case, p/q → False so (p ∨ q) → False, as desired
          (fun hp : p => h₂.left hp)
          (fun hq : q => h₂.right hq))
    )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h₁ : p ∨ q → r => -- WTS (p ∨ q → r) → (p → r) ∧ (q → r)
      And.intro
        (fun hp : p => h₁ (Or.inl hp))
        (fun hq : q => h₁ (Or.inr hq))
    )

    (fun h₂ : (p → r) ∧ (q → r) => -- WTS (p → r) ∧ (q → r) → p ∨ q → r
      fun h : p ∨ q => -- WTS p ∨ q → r
        Or.elim h h₂.left h₂.right -- show r
    )


------------------------------------------------------------------
/-Some lemmas from coq---------------------------------------------/
------------------------------------------------------------------

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

/-(** sequenced-before is included in happens-before *)

Lemma sb_incl_hb:
  sb ex ≦ hb.
Proof.
  unfold hb. kat.
Qed.-/

lemma sb_incl_hb {c : SystemConfig} (eg : ExecutionGraph c) :
    ∀ (e1 e2 : Event c), eg.sb e1 e2 → (hb eg) e1 e2 := by
        unfold hb
        intros e1 e2 h
        constructor
        · exact Or.intro_left ((sw eg) e1 e2) h

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from Exists.intro w (And.intro hw.right hw.left))

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  case mp =>
    intro h
    apply Or.elim (And.right h)
    case left =>
      intro hq
      have h_left : p ∧ q := by
        apply And.intro h.left hq
      apply Or.inl h_left
    case right => sorry
  case mpr => sorry

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

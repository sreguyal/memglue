import MemglueVerification.LitmusTests.TestFramework

/-!
## Message Passing (MP) litmus tests

Classic pattern:
  P0: store x=1 ; store y=1
  P1: load  y   ; load  x
  Forbidden: P1 reads y=1 AND x=0

The forbidden outcome is possible when there is no synchronisation between
the two stores (P0) and the corresponding loads (P1).  A release store of y
paired with an acquire load of y creates a happens-before edge that makes
the forbidden outcome unreachable.
-/

namespace LitmusTests.MP

-- addr 0 = x,  addr 1 = y
def cfg : SystemConfig := default   -- { threads := 2, addrCount := 2 }

private def forbidden (results : Vector (List Data) 2) : Bool :=
  -- Thread 1 issues: load y (index 0), load x (index 1)
  -- Forbidden: P1 sees y=1 but x=0
  let t1 := results.toList.getD 1 []
  t1.getD 0 0 == 1 && t1.getD 1 0 == 0

/-!
### mp_W_rlx_rlx_R_rlx_rlx

All operations relaxed — no synchronisation.
C11 allows the forbidden outcome; MemGlue should also allow it.
-/
def mp_rlx_rlx : LitmusTest cfg where
  name := "mp_W_rlx_rlx_R_rlx_rlx"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [ { access := .store, stren := .RLX, addr := (0 : Fin 2), data := 1, pend := false }
              , { access := .store, stren := .RLX, addr := (1 : Fin 2), data := 1, pend := false }
              ]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .RLX, addr := (1 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1] rfl
  forbidden := forbidden
  expected  := .Observable

/-!
### mp_W_rlx_rel_R_acq_rlx

P0 uses a release store of y; P1 uses an acquire load of y.
The REL/ACQ pair on y creates a happens-before edge:
  P0's store of x=1 happens before P0's REL store of y=1,
  which happens before P1's ACQ load of y,
  which happens before P1's load of x.
Therefore P1 must see x=1 whenever it sees y=1 → forbidden outcome is unreachable.
-/
def mp_rel_acq : LitmusTest cfg where
  name := "mp_W_rlx_rel_R_acq_rlx"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [ { access := .store, stren := .RLX, addr := (0 : Fin 2), data := 1, pend := false }
              , { access := .store, stren := .REL, addr := (1 : Fin 2), data := 1, pend := false }
              ]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .ACQ, addr := (1 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1] rfl
  forbidden := forbidden
  expected  := .Unobservable

def allTests : List (LitmusTest cfg) := [mp_rlx_rlx, mp_rel_acq]

end LitmusTests.MP

import MemglueVerification.LitmusTests.TestFramework

/-!
## Write-Read-Causality (WRC) litmus tests

Classic 3-thread pattern:
  P0: store x=1
  P1: load x ; store y=1
  P2: load y ; load x
  Forbidden: P1 reads x=1, P2 reads y=1 AND x=0

The forbidden outcome would mean that P2 observes P1's store of y (which
causally depended on seeing P0's store of x), yet does not observe P0's
store of x — violating causality.

With a release store from P0, an acquire load at P1, a release store from
P1, and an acquire load at P2, the chain of happens-before edges prevents
the forbidden outcome.  Under fully relaxed orderings the outcome is allowed.
-/

namespace LitmusTests.WRC

-- 3 threads: P0 writes x, P1 reads x and writes y, P2 reads y then x
-- addr 0 = x,  addr 1 = y
def cfg : SystemConfig := { threads := 3, addrCount := 2 }

private def forbidden (results : Vector (List Data) 3) : Bool :=
  -- Thread 1 issues: load x, store y  → loads = [x_value]
  -- Thread 2 issues: load y, load x   → loads = [y_value, x_value]
  -- Forbidden: P1 sees x=1, P2 sees y=1 but x=0
  let t1 := results.toList.getD 1 []
  let t2 := results.toList.getD 2 []
  t1.getD 0 0 == 1 && t2.getD 0 0 == 1 && t2.getD 1 0 == 0

/-!
### wrc_W_rlx_R_rlx_W_rlx_R_rlx_rlx

All operations relaxed.
Without ordering constraints the protocol may allow P2 to observe y=1
(from P1's store) without having observed x=1 (from P0's store).
-/
def wrc_rlx : LitmusTest cfg where
  name := "wrc_W_rlx_R_rlx_W_rlx_R_rlx_rlx"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [{ access := .store, stren := .RLX, addr := (0 : Fin 2), data := 1, pend := false }]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [ { access := .load,  stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              , { access := .store, stren := .RLX, addr := (1 : Fin 2), data := 1, pend := false }
              ]
      nonempty := by simp }
    let t2 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .RLX, addr := (1 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1, t2] rfl
  forbidden := forbidden
  expected  := .Observable

/-!
### wrc_W_rel_R_acq_W_rel_R_acq_rlx

P0 uses a release store of x; P1 uses an acquire load of x and a release
store of y; P2 uses an acquire load of y.
The REL/ACQ chain:
  P0 REL-x → P1 ACQ-x → P1 REL-y → P2 ACQ-y
establishes transitively that P2's load of y=1 happens after P0's store of
x=1, so P2 must see x=1.  The forbidden outcome is unreachable.
-/
def wrc_rel_acq : LitmusTest cfg where
  name := "wrc_W_rel_R_acq_W_rel_R_acq_rlx"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [{ access := .store, stren := .REL, addr := (0 : Fin 2), data := 1, pend := false }]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [ { access := .load,  stren := .ACQ, addr := (0 : Fin 2), data := 0, pend := false }
              , { access := .store, stren := .REL, addr := (1 : Fin 2), data := 1, pend := false }
              ]
      nonempty := by simp }
    let t2 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .ACQ, addr := (1 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1, t2] rfl
  forbidden := forbidden
  expected  := .Unobservable

def allTests : List (LitmusTest cfg) := [wrc_rlx, wrc_rel_acq]

end LitmusTests.WRC

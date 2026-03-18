import MemglueVerification.LitmusTests.TestFramework

/-!
## Store Buffer (SB) litmus tests

Classic pattern:
  P0: store x=1 ; load y
  P1: store y=1 ; load x
  Forbidden: P0 reads y=0 AND P1 reads x=0

This is the "store buffer" test.  Under SC the forbidden outcome is
unreachable because one of the two stores must happen first in the total
order, making the paired load see 1.  Under relaxed orderings a processor's
store may be buffered past its own subsequent load, making the outcome
observable.
-/

namespace LitmusTests.SB

-- addr 0 = x,  addr 1 = y
def cfg : SystemConfig := default   -- { threads := 2, addrCount := 2 }

private def forbidden (results : Vector (List Data) 2) : Bool :=
  -- Thread 0 issues: store x, load y  → loads = [y_value]
  -- Thread 1 issues: store y, load x  → loads = [x_value]
  -- Forbidden: both threads read 0
  let t0 := results.toList.getD 0 []
  let t1 := results.toList.getD 1 []
  t0.getD 0 0 == 0 && t1.getD 0 0 == 0

/-!
### sb_W_rlx_R_rlx

All operations relaxed.
C11 and MemGlue both allow the forbidden outcome.
-/
def sb_rlx : LitmusTest cfg where
  name := "sb_W_rlx_R_rlx"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [ { access := .store, stren := .RLX, addr := (0 : Fin 2), data := 1, pend := false }
              , { access := .load,  stren := .RLX, addr := (1 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [ { access := .store, stren := .RLX, addr := (1 : Fin 2), data := 1, pend := false }
              , { access := .load,  stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1] rfl
  forbidden := forbidden
  expected  := .Observable

/-!
### sb_W_sc_R_sc

All operations sequentially consistent.
SC imposes a total order on all operations, so one store must precede the
other; the load that follows the later store must see the earlier store's
value.  The forbidden outcome (both loads returning 0) is unreachable.
-/
def sb_sc : LitmusTest cfg where
  name := "sb_W_sc_R_sc"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [ { access := .store, stren := .SC, addr := (0 : Fin 2), data := 1, pend := false }
              , { access := .load,  stren := .SC, addr := (1 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [ { access := .store, stren := .SC, addr := (1 : Fin 2), data := 1, pend := false }
              , { access := .load,  stren := .SC, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1] rfl
  forbidden := forbidden
  expected  := .Unobservable

def allTests : List (LitmusTest cfg) := [sb_rlx, sb_sc]

end LitmusTests.SB

import MemglueVerification.LitmusTests.TestFramework

/-!
## Independent Reads of Independent Writes (IRIW) litmus tests

Classic 4-thread pattern:
  P0: store x=1
  P1: store y=1
  P2: load x ; load y
  P3: load y ; load x
  Forbidden: P2 sees (x=1, y=0) AND P3 sees (y=1, x=0)

The forbidden outcome would mean that P2 observes the write to x before the
write to y, while P3 observes the write to y before the write to x — i.e.
the two readers disagree on the order of the two writes.

Under SC (and under C11 RC11), this outcome is forbidden because writes must
appear in a single total order to all readers.  Under relaxed memory models
without multi-copy atomicity the outcome may be observable.
-/

namespace LitmusTests.IRIW

-- 4 threads: P0 writes x, P1 writes y, P2 reads x/y, P3 reads y/x
-- addr 0 = x,  addr 1 = y
def cfg : SystemConfig := { threads := 4, addrCount := 2 }

private def forbidden (results : Vector (List Data) 4) : Bool :=
  -- Thread 2 issues: load x (index 0), load y (index 1)
  -- Thread 3 issues: load y (index 0), load x (index 1)
  -- Forbidden: P2 sees x=1,y=0  AND  P3 sees y=1,x=0
  let t2 := results.toList.getD 2 []
  let t3 := results.toList.getD 3 []
  t2.getD 0 0 == 1 && t2.getD 1 0 == 0 &&
  t3.getD 0 0 == 1 && t3.getD 1 0 == 0

/-!
### iriw_W_rlx_W_rlx_R_rlx_rlx_R_rlx_rlx

All operations relaxed.
MemGlue may allow the outcome if the protocol lacks multi-copy atomicity
under relaxed ordering.
-/
def iriw_rlx : LitmusTest cfg where
  name := "iriw_W_rlx_W_rlx_R_rlx_rlx_R_rlx_rlx"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [{ access := .store, stren := .RLX, addr := (0 : Fin 2), data := 1, pend := false }]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [{ access := .store, stren := .RLX, addr := (1 : Fin 2), data := 1, pend := false }]
      nonempty := by simp }
    let t2 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .RLX, addr := (1 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    let t3 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .RLX, addr := (1 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .RLX, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1, t2, t3] rfl
  forbidden := forbidden
  expected  := .Observable

/-!
### iriw_W_sc_W_sc_R_sc_sc_R_sc_sc

All operations sequentially consistent.
SC guarantees a single total write order visible to all threads, so the
forbidden outcome (readers disagreeing on write order) is unreachable.
-/
def iriw_sc : LitmusTest cfg where
  name := "iriw_W_sc_W_sc_R_sc_sc_R_sc_sc"
  execution :=
    let t0 : neList (Instr cfg) := {
      list := [{ access := .store, stren := .SC, addr := (0 : Fin 2), data := 1, pend := false }]
      nonempty := by simp }
    let t1 : neList (Instr cfg) := {
      list := [{ access := .store, stren := .SC, addr := (1 : Fin 2), data := 1, pend := false }]
      nonempty := by simp }
    let t2 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .SC, addr := (0 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .SC, addr := (1 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    let t3 : neList (Instr cfg) := {
      list := [ { access := .load, stren := .SC, addr := (1 : Fin 2), data := 0, pend := false }
              , { access := .load, stren := .SC, addr := (0 : Fin 2), data := 0, pend := false }
              ]
      nonempty := by simp }
    Vector.mk #[t0, t1, t2, t3] rfl
  forbidden := forbidden
  expected  := .Unobservable

def allTests : List (LitmusTest cfg) := [iriw_rlx, iriw_sc]

end LitmusTests.IRIW

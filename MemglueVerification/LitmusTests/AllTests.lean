import MemglueVerification.LitmusTests.Patterns.MP
import MemglueVerification.LitmusTests.Patterns.SB
import MemglueVerification.LitmusTests.Patterns.IRIW
import MemglueVerification.LitmusTests.Patterns.WRC

/-!
## Aggregated litmus test runner

Imports all pattern namespaces and runs every test against the unordered
MemGlue protocol (memglueU).  Results are printed to the #eval output as:

    [pass] <name>: <outcome> (expected <expected>)
    [FAIL] <name>: <outcome> (expected <expected>)

A "FAIL" line indicates that the observed outcome differs from the expected
outcome documented in the test definition, signalling either a protocol bug
or an incorrect expectation.
-/

namespace LitmusTests

private def runGroup {c : SystemConfig} (groupName : String)
    (tests : List (LitmusTest c)) : IO Unit := do
  IO.println s!"=== {groupName} ==="
  for test in tests do
    IO.println (printTestResult test)
  IO.println ""

def runAll : IO Unit := do
  runGroup "MP"   MP.allTests
  runGroup "SB"   SB.allTests
  runGroup "IRIW" IRIW.allTests
  runGroup "WRC"  WRC.allTests

-- Uncomment to run the full test suite when elaborating this file:
#eval! runAll

end LitmusTests

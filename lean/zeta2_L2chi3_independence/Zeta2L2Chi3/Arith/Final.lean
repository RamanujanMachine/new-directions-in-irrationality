/-
# The arithmetic content bound

Assembly: chambers (walls from `ChamberData`), certified forward bounds (`FwdCert`, valid for every
lift), certified dual bounds (`DualCert*`, lifts `L ≤ 19`), per-chamber valuation bounds
(`CellBounds`), small primes and `p = 2, 3` (`FwdVal`, `DeltaVal`, (3.1)), the summation theorem
(`Sum`), and the numerical evaluation of the chamber density (`Density`); the assembly is
`contentBound_of` (`FinalAux`).
-/
import Zeta2L2Chi3.Arith.FinalAux
import Zeta2L2Chi3.Arith.FwdCert
import Zeta2L2Chi3.Arith.DualCert0
import Zeta2L2Chi3.Arith.DualCert1
import Zeta2L2Chi3.Arith.DualCert2
import Zeta2L2Chi3.Arith.DualCert3
import Zeta2L2Chi3.Arith.DualCert4
import Zeta2L2Chi3.Arith.DualCert5
import Zeta2L2Chi3.Arith.DualCert6
import Zeta2L2Chi3.Arith.DualCert7
import Zeta2L2Chi3.Arith.DualCert8
import Zeta2L2Chi3.Arith.DualCert9
import Zeta2L2Chi3.Arith.DualCert10
import Zeta2L2Chi3.Arith.DualCert11

namespace Zeta2L2Chi3.Arith

set_option maxRecDepth 100000

/-- all certified dual chambers -/
def dcellsAll : List DCell :=
  dcells0 ++ dcells1 ++ dcells2 ++ dcells3 ++ dcells4 ++ dcells5 ++ dcells6 ++ dcells7 ++
    dcells8 ++ dcells9 ++ dcells10 ++ dcells11

theorem dcellsAll_ok : dcellsAll.all DCell.ok = true := by
  simp [dcellsAll, List.all_append, dcells0_ok, dcells1_ok, dcells2_ok, dcells3_ok, dcells4_ok,
    dcells5_ok, dcells6_ok, dcells7_ok, dcells8_ok, dcells9_ok, dcells10_ok, dcells11_ok]

theorem dualOk_all : dualOk dcellsAll = true := by decide +kernel

theorem contentBound : ContentBound :=
  contentBound_of dcellsAll fcells_ok dcellsAll_ok dualOk_all

end Zeta2L2Chi3.Arith

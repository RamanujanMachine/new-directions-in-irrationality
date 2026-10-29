/-
# The residue rows over `ℚ` and over `ℝ` agree (casts)
-/
import Zeta2L2Chi3.Dual

open Finset

namespace Zeta2L2Chi3

@[simp] lemma cast_rf (x : ℚ) (m : ℕ) : ((rf x m : ℚ) : ℝ) = rf (x : ℝ) m := by
  simp [rf]

@[simp] lemma cast_FNum (n : ℕ) (s : ℚ) : ((FNum n s : ℚ) : ℝ) = FNum n (s : ℝ) := by
  simp [FNum]

@[simp] lemma cast_tP (j : ℕ) : ((tP j : ℚ) : ℝ) = tP j := by simp [tP]
@[simp] lemma cast_hP (n j : ℕ) : ((hP n j : ℚ) : ℝ) = hP n j := by simp [hP]
@[simp] lemma cast_iP (n j : ℕ) : ((iP n j : ℚ) : ℝ) = iP n j := by simp [iP]

@[simp] lemma cast_resT (n j : ℕ) : ((resT n j : ℚ) : ℝ) = resT n j := by simp [resT]
@[simp] lemma cast_resH (n j : ℕ) : ((resH n j : ℚ) : ℝ) = resH n j := by simp [resH]
@[simp] lemma cast_resI (n j : ℕ) : ((resI n j : ℚ) : ℝ) = resI n j := by simp [resI]

@[simp] lemma cast_hwT (j : ℕ) : ((hwT j : ℚ) : ℝ) = hwT j := by simp [hwT]
@[simp] lemma cast_hwH (n j : ℕ) : ((hwH n j : ℚ) : ℝ) = hwH n j := by simp [hwH]
@[simp] lemma cast_hwI (n j : ℕ) : ((hwI n j : ℚ) : ℝ) = hwI n j := by simp [hwI]

@[simp] lemma cast_BT (n k : ℕ) : ((BT n k : ℚ) : ℝ) = BT n k := by simp [BT]
@[simp] lemma cast_BH (n k : ℕ) : ((BH n k : ℚ) : ℝ) = BH n k := by simp [BH]
@[simp] lemma cast_BI (n k : ℕ) : ((BI n k : ℚ) : ℝ) = BI n k := by simp [BI]
@[simp] lemma cast_B0 (n k : ℕ) : ((B0 n k : ℚ) : ℝ) = B0 n k := by simp [B0]

end Zeta2L2Chi3

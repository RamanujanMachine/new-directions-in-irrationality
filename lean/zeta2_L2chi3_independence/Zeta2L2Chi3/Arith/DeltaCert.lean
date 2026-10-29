/-
# Certificate for the one-step identity of `det Q(n)` (multiset comparison of linear factors)
-/
import Zeta2L2Chi3.Arith.DeltaAux

namespace Zeta2L2Chi3.Arith

open Zeta2L2Chi3

/-! ### The one-step identity -/

def stepN1 : List (ℤ × ℤ) := Data.QdetLin
def stepD1 : List (ℤ × ℤ) := Data.QdenLin ++ Data.QdenLin ++ Data.QdenLin
def stepN2 : List (ℤ × ℤ) := shL gN ++ gD ++ gNum gammaF
def stepD2 : List (ℤ × ℤ) := shL gD ++ gN ++ gDen gammaF

theorem step_perm : ((stepN1 ++ stepD2).map nrm).Perm ((stepN2 ++ stepD1).map nrm) := by
  decide +kernel

theorem step_gcds1 : gcds (stepN1 ++ stepD2) = 119439360 := by decide +kernel
theorem step_gcds2 : gcds (stepN2 ++ stepD1) = 3276800 := by decide +kernel

theorem gConst_gammaF : gConst gammaF = 32 / 9 := by
  decide +kernel

theorem stepD1_pos : ∀ f ∈ stepD1, 0 ≤ f.1 ∧ 0 < f.2 := by decide +kernel
theorem stepD2_pos : ∀ f ∈ stepD2, 0 ≤ f.1 ∧ 0 < f.2 := by decide +kernel
theorem gN_pos : ∀ f ∈ gN, 0 ≤ f.1 ∧ 0 < f.2 := by decide +kernel
theorem gD_pos : ∀ f ∈ gD, 0 ≤ f.1 ∧ 0 < f.2 := by decide +kernel

lemma det_Q_step (n : ℕ) :
    (Q n).det = (2 ^ 8 * 3 ^ 30 * gConst gammaF) * PL stepN2 n / PL stepD2 n := by
  rw [det_Q_fr, show Data.QdetLin = stepN1 from rfl,
    show Data.QdenLin ++ Data.QdenLin ++ Data.QdenLin = stepD1 from rfl]
  have hx : (0 : ℚ) ≤ n := by positivity
  refine fr_eq (n : ℚ) (PL_pos _ stepD1_pos _ hx).ne' (PL_pos _ stepD2_pos _ hx).ne' step_perm ?_
  rw [step_gcds1, step_gcds2, gConst_gammaF]
  simp only [Data.QdetConst, Data.QdenConst]
  norm_num

end Zeta2L2Chi3.Arith

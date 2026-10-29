/-
# The trigamma constants `ψ₁(1/3) = 4Z + 9C/2` and `ψ₁(1/2) = 3Z` (DEF01)

Defined directly as reciprocal-square series; the identities follow by splitting `ζ(2)` by
residue classes.  No independence of `C` and `Z` is used anywhere.
-/
import Zeta2L2Chi3.Defs

open Real

namespace Zeta2L2Chi3

/-- `ψ₁(1/3) = ∑_{l ≥ 0} (l + 1/3)^{-2}` -/
noncomputable def psiT : ℝ := ∑' l : ℕ, 1 / ((l : ℝ) + 1 / 3) ^ 2
/-- `ψ₁(1/2) = ∑_{l ≥ 0} (l + 1/2)^{-2}` -/
noncomputable def psiH : ℝ := ∑' l : ℕ, 1 / ((l : ℝ) + 1 / 2) ^ 2

lemma summable_shift_sq (a : ℝ) (ha : 0 < a) : Summable (fun l : ℕ => 1 / ((l : ℝ) + a) ^ 2) := by
  simpa using summable_inv_sq_affine (a := 1) (b := a) one_pos ha

lemma psiT_eq : psiT = 4 * Z + 9 * C / 2 := by
  have h1 : psiT = 9 * ∑' k : ℕ, 1 / (3 * (k : ℝ) + 1) ^ 2 := by
    unfold psiT; rw [← tsum_mul_left]; congr 1; ext l
    have : (l : ℝ) + 1 / 3 = (3 * l + 1) / 3 := by ring
    rw [this, div_pow]; field_simp; ring
  have hs := Z_split
  have hc := C_eq
  rw [h1]; linarith

lemma psiH_eq : psiH = 3 * Z := by
  have h1 : psiH = 4 * ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 2 := by
    unfold psiH; rw [← tsum_mul_left]; congr 1; ext l
    have : (l : ℝ) + 1 / 2 = (2 * l + 1) / 2 := by ring
    rw [this, div_pow]; field_simp; ring
  -- `Z = ∑ odd + ∑ even = ∑ odd + Z/4`
  have hodd : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) :=
    summable_inv_sq_affine (by norm_num) (by norm_num)
  have heven : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 2) ^ 2 = Z / 4 := by
    unfold Z; rw [← tsum_div_const]; congr 1; ext k
    have : (2 * (k : ℝ) + 2) ^ 2 = 4 * ((k : ℝ) + 1) ^ 2 := by ring
    rw [this]; field_simp
  have key := Nat.sumByResidueClasses summable_Z 2
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton] at key
  have v0 : (0 : ZMod 2).val = 0 := rfl
  have v1 : (1 : ZMod 2).val = 1 := rfl
  rw [v0, v1] at key
  push_cast at key
  have a1 : ∀ m : ℕ, ((0 : ℝ) + 2 * m + 1) = 2 * m + 1 := fun m => by ring
  have a2 : ∀ m : ℕ, ((1 : ℝ) + 2 * m + 1) = 2 * m + 2 := fun m => by ring
  simp only [a1, a2] at key
  rw [h1]
  have hZ : Z = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := rfl
  rw [← hZ, heven] at key
  linarith

end Zeta2L2Chi3

/-
Copyright (c) 2026. All rights reserved.

# Basic definitions: the constants `C = L(2, χ₋₃)`, `Z = ζ(2)` and the mixtures `α(A,B)`

`C = ∑_{k≥0} ((3k+1)^{-2} - (3k+2)^{-2})` (this is `L(2,χ_{-3})`, *not* Catalan's constant),
`Z = ∑_{k≥1} k^{-2}`.
-/
import Mathlib

open Real Filter Topology

namespace Zeta2L2Chi3

/-- `Z = ζ(2) = ∑_{k ≥ 1} 1/k²`, indexed from `k = 0` as `1/(k+1)²`. -/
noncomputable def Z : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2

/-- `C = L(2,χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)² - 1/(3k+2)²)`. -/
noncomputable def C : ℝ := ∑' k : ℕ, (1 / (3 * (k : ℝ) + 1) ^ 2 - 1 / (3 * (k : ℝ) + 2) ^ 2)

/-- The fixed integer mixtures `α(A,B) = A (C + 2Z/3) + B (C - 2Z/3)`. -/
noncomputable def alpha (A B : ℤ) : ℝ := A * (C + 2 * Z / 3) + B * (C - 2 * Z / 3)

lemma alpha_eq (A B : ℤ) : alpha A B = (A + B : ℝ) * C + (2 / 3 * (A - B) : ℝ) * Z := by
  unfold alpha; ring

/-! ### Summability of the basic reciprocal-square series -/

/-- `∑ 1/(a k + b)²` is summable for `a > 0`, `b > 0`. -/
lemma summable_inv_sq_affine {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Summable (fun k : ℕ => 1 / (a * (k : ℝ) + b) ^ 2) := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  have hc : 0 < min a b := lt_min ha hb
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hs.mul_left (1 / (min a b) ^ 2))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : min a b * ((k : ℝ) + 1) ≤ a * k + b := by
    have := min_le_left a b; have := min_le_right a b; nlinarith
  have h2 : 0 < min a b * ((k : ℝ) + 1) := by positivity
  rw [div_mul_div_comm, one_mul, ← mul_pow]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h2.le h1 2)

lemma summable_Z : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  simpa using summable_inv_sq_affine (a := 1) (b := 1) one_pos one_pos

lemma summable_third1 : Summable (fun k : ℕ => 1 / (3 * (k : ℝ) + 1) ^ 2) :=
  summable_inv_sq_affine (by norm_num) (by norm_num)

lemma summable_third2 : Summable (fun k : ℕ => 1 / (3 * (k : ℝ) + 2) ^ 2) :=
  summable_inv_sq_affine (by norm_num) (by norm_num)

lemma summable_third3 : Summable (fun k : ℕ => 1 / (3 * (k : ℝ) + 3) ^ 2) :=
  summable_inv_sq_affine (by norm_num) (by norm_num)

lemma C_eq : C = (∑' k : ℕ, 1 / (3 * (k : ℝ) + 1) ^ 2) - ∑' k : ℕ, 1 / (3 * (k : ℝ) + 2) ^ 2 := by
  unfold C; exact summable_third1.tsum_sub summable_third2

lemma Z_eq_pi : Z = π ^ 2 / 6 := by
  have h := hasSum_zeta_two
  have h' : HasSum (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr h
    simpa using this
  unfold Z
  simpa using h'.tsum_eq

lemma Z_pos : 0 < Z := by rw [Z_eq_pi]; positivity

/-- Splitting `ζ(2)` by residues modulo 3:  `Z = S₁ + S₂ + Z/9`. -/
lemma Z_split :
    Z = (∑' k : ℕ, 1 / (3 * (k : ℝ) + 1) ^ 2) + (∑' k : ℕ, 1 / (3 * (k : ℝ) + 2) ^ 2) + Z / 9 := by
  have e3 : ∑' k : ℕ, 1 / (3 * (k : ℝ) + 3) ^ 2 = Z / 9 := by
    unfold Z
    rw [← tsum_div_const]
    congr 1; ext k
    have : (3 * (k : ℝ) + 3) ^ 2 = 9 * ((k : ℝ) + 1) ^ 2 := by ring
    rw [this]; field_simp
  have key := Nat.sumByResidueClasses summable_Z 3
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at key
  conv_lhs => rw [show Z = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 from rfl, key]
  rw [← e3]
  have v0 : (0 : ZMod 3).val = 0 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  have v1 : (1 : ZMod 3).val = 1 := rfl
  rw [v0, v1, v2]
  push_cast
  have a1 : ∀ m : ℕ, ((0 : ℝ) + 3 * m + 1) = 3 * m + 1 := fun m => by ring
  have a2 : ∀ m : ℕ, ((1 : ℝ) + 3 * m + 1) = 3 * m + 2 := fun m => by ring
  have a3 : ∀ m : ℕ, ((2 : ℝ) + 3 * m + 1) = 3 * m + 3 := fun m => by ring
  simp only [a1, a2, a3, zero_add]
  ring_nf

end Zeta2L2Chi3

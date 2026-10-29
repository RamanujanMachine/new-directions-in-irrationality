/-
# Initial values of the forward rows (n = 0)

At `n = 0`, `R₀(t) = (t+1)(t+4/3)(t+3/2) / (t²(t-1)²)` with explicit partial fractions; the rows are
`φ¹ = (41/3, 35/3, 35/3, 35/3)`, `φᵀ = (1807/16, 1339/16, 8495/144, 37819/1296)`,
`φᴴ = (2353/54, 818/27, 3649/216, 311/432)`.
-/
import Zeta2L2Chi3.Forward

open Polynomial Finset

noncomputable section

namespace Zeta2L2Chi3

lemma KF_zero : KF 0 = {0, 1} := by
  ext x; simp only [KF, Finset.mem_image, Finset.mem_Icc]; constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    have : k = 0 ∨ k = 1 := by push_cast at h1 h2; omega
    rcases this with rfl | rfl <;> simp
  · intro h; simp at h; rcases h with rfl | rfl
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩

/-- explicit polynomial parts `q_j` at `n = 0` -/
def q0 : Fin 4 → ℝ[X] := ![0, 1, X + Polynomial.C (35 / 6), X ^ 2 + Polynomial.C (35 / 6) * X + Polynomial.C (31 / 2)]
/-- double-pole coefficients at `0` and `1` -/
def a00 : Fin 4 → ℝ := ![2, 0, 0, 0]
def a01 : Fin 4 → ℝ := ![35 / 3, 35 / 3, 35 / 3, 35 / 3]
/-- simple-pole coefficients at `0` and `1` -/
def b00 : Fin 4 → ℝ := ![53 / 6, 2, 0, 0]
def b01 : Fin 4 → ℝ := ![-47 / 6, 23 / 6, 31 / 2, 163 / 6]

def a0f (j : Fin 4) (k : ℝ) : ℝ := if k = 0 then a00 j else a01 j
def b0f (j : Fin 4) (k : ℝ) : ℝ := if k = 0 then b00 j else b01 j

lemma pf0_identity (j : Fin 4) (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    (X ^ (j : ℕ) * RNumPoly 0).eval t / ∏ k ∈ KF 0, (t - k) ^ eF 0 k =
      pfEval (KF 0) (q0 j) (a0f j) (b0f j) t := by
  rw [KF_zero]
  have hne : (0 : ℝ) ≠ 1 := by norm_num
  simp only [pfEval, Finset.prod_pair hne, Finset.sum_pair hne, eF, a0f, b0f]
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 h1
  simp only [RNumPoly, Finset.prod_range_one, mul_zero, zero_add, Nat.cast_zero]
  fin_cases j <;> simp [q0, a00, a01, b00, b01] <;> field_simp <;> ring

theorem fdata_zero (j : Fin 4) :
    fq 0 j = q0 j ∧ ∀ k ∈ KF 0, fa 0 j k = a0f j k ∧ fb 0 j k = b0f j k := by
  have h := pf_unique (KF 0) (fq 0 j) (q0 j) (fa 0 j) (fb 0 j) (a0f j) (b0f j) ∅ (fun t ht => by
    simp only [Finset.union_empty] at ht
    rw [← fdata_spec 0 j t ht]
    rw [KF_zero] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact pf0_identity j t ht.1 ht.2)
  exact h

/-! ### Values of the functionals at `n = 0` -/

lemma bern3_zero : _root_.bernoulli 3 = 0 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_three]

lemma zetaNeg_zero (x : ℝ) : zetaNeg 0 x = 1 / 2 - x := by
  simp [zetaNeg, Polynomial.bernoulli, Finset.sum_range_succ, _root_.bernoulli_one]; ring

lemma zetaNeg_one (x : ℝ) : zetaNeg 1 x = -(x ^ 2 - x + 1 / 6) / 2 := by
  simp [zetaNeg, Polynomial.bernoulli, Finset.sum_range_succ, _root_.bernoulli_one, _root_.bernoulli_two]; ring

lemma zetaNeg_two (x : ℝ) : zetaNeg 2 x = -(x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x) / 3 := by
  simp [zetaNeg, Polynomial.bernoulli, Finset.sum_range_succ, _root_.bernoulli_one, _root_.bernoulli_two, bern3_zero,
    Nat.choose]; ring

lemma q0_nd2 : (q0 2).natDegree = 1 := by simp only [q0]; compute_degree!
lemma nd_aux : (X ^ 2 + Polynomial.C (35 / 6 : ℝ) * X).natDegree = 2 := by
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · calc (Polynomial.C (35 / 6 : ℝ) * X).natDegree ≤ 1 := by
          refine (natDegree_C_mul_le _ _).trans ?_; simp
      _ < (X ^ 2 : ℝ[X]).natDegree := by simp

lemma phi_zero_eval (j : Fin 4) (ρ : ℝ) (m : ℤ) :
    pfun (KF 0) (fq 0 j) (fa 0 j) (fb 0 j) ρ m =
      (a00 j * Hsig 2 ρ m - b00 j * Hsig 1 ρ m) + (a01 j * Hsig 2 ρ (1 + m) - b01 j * Hsig 1 ρ (1 + m))
        - Ubern (q0 j) (ρ + m) := by
  obtain ⟨hq, hab⟩ := fdata_zero j
  have h0 := hab 0 (by rw [KF_zero]; simp)
  have h1 := hab 1 (by rw [KF_zero]; simp)
  rw [pfun, hq, KF_zero, Finset.sum_pair (by norm_num : (0 : ℝ) ≠ 1), h0.1, h0.2, h1.1, h1.2]
  simp [a0f, b0f]

theorem phi1_zero (j : Fin 4) : phi1 0 j = a00 j + a01 j := by
  obtain ⟨-, hab⟩ := fdata_zero j
  have h0 := hab 0 (by rw [KF_zero]; simp)
  have h1 := hab 1 (by rw [KF_zero]; simp)
  rw [phi1, KF_zero, Finset.sum_pair (by norm_num : (0 : ℝ) ≠ 1), h0.1, h1.1]
  simp [a0f]

theorem phiT_zero : (fun j : Fin 4 => phiT 0 j) = ![1807 / 16, 1339 / 16, 8495 / 144, 37819 / 1296] := by
  funext j
  simp only [phiT, phi_zero_eval]
  fin_cases j <;>
    simp [a00, a01, b00, b01, q0, Hsig, Ubern, zetaNeg_zero, zetaNeg_one, zetaNeg_two,
      Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one, q0_nd2, nd_aux] <;>
    norm_num

theorem phiH_zero : (fun j : Fin 4 => phiH 0 j) = ![2353 / 54, 818 / 27, 3649 / 216, 311 / 432] := by
  funext j
  simp only [phiH, phi_zero_eval]
  fin_cases j <;>
    simp [a00, a01, b00, b01, q0, Hsig, Ubern, zetaNeg_zero, zetaNeg_one, zetaNeg_two,
      Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one, q0_nd2, nd_aux] <;>
    norm_num

end Zeta2L2Chi3

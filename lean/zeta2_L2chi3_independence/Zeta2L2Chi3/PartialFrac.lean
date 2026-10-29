import Mathlib

namespace Zeta2L2Chi3

open Polynomial Finset

/-- residue coefficient of `p(s) / ∏_{λ∈Λ} (λ - s)` at `λ` -/
noncomputable def pfCoeff (Λ : Finset ℝ) (p : ℝ[X]) (l : ℝ) : ℝ :=
  -p.eval l / ∏ μ ∈ Λ.erase l, (μ - l)

lemma prod_sub_swap (t : Finset ℝ) (a : ℝ) :
    ∏ μ ∈ t, (μ - a) = (-1) ^ t.card * ∏ μ ∈ t, (a - μ) := by
  rw [← Finset.prod_neg]
  exact Finset.prod_congr rfl fun μ _ => by ring

lemma pfCoeff_eq (Λ : Finset ℝ) (p : ℝ[X]) {l : ℝ} (hl : l ∈ Λ) :
    pfCoeff Λ p l = (-1) ^ Λ.card * (p.eval l / ∏ μ ∈ Λ.erase l, (l - μ)) := by
  unfold pfCoeff
  rw [prod_sub_swap, card_erase_of_mem hl]
  have hcard : 0 < Λ.card := card_pos.mpr ⟨l, hl⟩
  obtain ⟨n, hn⟩ : ∃ n, Λ.card = n + 1 := ⟨Λ.card - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel, pow_succ]
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> ring

theorem partialFrac (Λ : Finset ℝ) (p : ℝ[X]) (hp : p.natDegree < Λ.card) (s : ℝ)
    (hs : s ∉ Λ) :
    p.eval s / ∏ l ∈ Λ, (l - s) = ∑ l ∈ Λ, pfCoeff Λ p l / (s - l) := by
  have hvs : Set.InjOn (fun x : ℝ => x) (Λ : Set ℝ) := Function.injective_id.injOn
  have hdeg : p.degree < Λ.card :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hp)
  have hx : ∀ i ∈ Λ, s ≠ (fun x : ℝ => x) i := fun i hi h => hs (h ▸ hi)
  have key := Lagrange.eval_interpolate_not_at_node (fun l => p.eval l) hx
  rw [← Lagrange.eq_interpolate hvs hdeg, Lagrange.eval_nodal] at key
  simp only [Lagrange.nodalWeight] at key
  have hprod : ∏ l ∈ Λ, (s - l) ≠ 0 :=
    prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr fun h => hs (h ▸ hl)
  rw [prod_sub_swap, key]
  rw [mul_comm ((-1 : ℝ) ^ Λ.card), mul_div_mul_left _ _ hprod, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [pfCoeff_eq Λ p hl, prod_inv_distrib]
  rcases neg_one_pow_eq_or ℝ Λ.card with h | h <;> rw [h]
  · simp only [inv_one, one_mul]; ring
  · simp only [inv_neg, inv_one]; ring

theorem sum_pfCoeff_eq_zero (Λ : Finset ℝ) (p : ℝ[X]) (hp : p.natDegree + 1 < Λ.card) :
    ∑ l ∈ Λ, pfCoeff Λ p l = 0 := by
  have hvs : Set.InjOn (fun x : ℝ => x) (Λ : Set ℝ) := Function.injective_id.injOn
  have hdeg : p.degree < Λ.card :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (by omega : p.natDegree < Λ.card))
  have hc := Lagrange.coeff_eq_sum hvs hdeg
  rw [coeff_eq_zero_of_natDegree_lt (by omega)] at hc
  rw [Finset.sum_congr rfl fun l hl => pfCoeff_eq Λ p hl, ← Finset.mul_sum, ← hc, mul_zero]

end Zeta2L2Chi3

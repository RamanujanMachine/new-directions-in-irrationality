/-
# Assembling valuation bounds for the explicit forward vector

`fvecE_vge`: bounds on the coefficients `a_k, b_k`, the harmonic sums, the Bernoulli terms and
`K(n) e₀` combine to a bound on `fvecE n i`.  Also: the "sixth" lemmas (rationals with
denominator dividing `6`), `UQ` and `KQ` bounds.
-/
import Zeta2L2Chi3.Arith.FwdRat
import Zeta2L2Chi3.Arith.Valuation

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

section
variable {p : ℕ} [hp : Fact p.Prime]

/-- the three harmonic shifts used by the forward rows -/
def rhoSet : Finset ℚ := {1 / 3, 1 / 2, 1}

theorem fvecE_vge (n : ℕ) (T H2 H1 U K : ℤ) (A B : ℤ → ℤ)
    (ha : ∀ j ≤ 3, ∀ k ∈ KZ n, VGe p (A k) (aQ n j k))
    (hb : ∀ j ≤ 3, ∀ k ∈ KZ n, VGe p (B k) (bQ n j k))
    (hH : ∀ k ∈ KZ n, ∀ m : ℤ, 0 ≤ m → m ≤ 2 * n + 1 → ∀ ρ ∈ rhoSet,
      VGe p H2 (HsigQ 2 ρ (k + m)) ∧ VGe p H1 (HsigQ 1 ρ (k + m)))
    (hU : ∀ j ≤ 3, ∀ x : ℚ, (∃ a : ℤ, x * 6 = a) → VGe p U (UQ n j x))
    (hK : ∀ j, VGe p K (KQ n j))
    (hTA : ∀ k ∈ KZ n, T ≤ A k ∧ T ≤ A k + H2 ∧ T ≤ B k + H1) (hTU : T ≤ U) (i : Fin 3) :
    VGe p (T + K) (fvecE n i) := by
  have hpf : ∀ j ≤ 3, ∀ ρ ∈ rhoSet, ∀ m : ℤ, 0 ≤ m → m ≤ 2 * n + 1 →
      VGe p T (pfunQ n j ρ m) := by
    intro j hj ρ hρ m hm0 hm1
    unfold pfunQ
    refine VGe.sub (VGe.finset_sum fun k hk => ?_) ((hU j hj _ ?_).mono hTU)
    · obtain ⟨h2, h1⟩ := hH k hk m hm0 hm1 ρ hρ
      obtain ⟨-, t2, t1⟩ := hTA k hk
      exact ((ha j hj k hk).mul h2).mono t2 |>.sub (((hb j hj k hk).mul h1).mono t1)
    · simp only [rhoSet, mem_insert, mem_singleton] at hρ
      rcases hρ with rfl | rfl | rfl
      · exact ⟨2 + 6 * m, by push_cast; ring⟩
      · exact ⟨3 + 6 * m, by push_cast; ring⟩
      · exact ⟨6 + 6 * m, by push_cast; ring⟩
  have hr1 : ∀ j : Fin 4, VGe p T (phi1Q n j) := fun j =>
    VGe.finset_sum fun k hk => (ha j (by omega) k hk).mono (hTA k hk).1
  have hrT : ∀ j : Fin 4, VGe p T (phiTQ n j) := fun j =>
    (hpf j (by omega) _ (by simp [rhoSet]) 1 (by norm_num) (by omega)).sub
      (hpf j (by omega) _ (by simp [rhoSet]) _ (by positivity) (by omega))
  have hrH : ∀ j : Fin 4, VGe p T (phiHQ n j) := fun j =>
    (hpf j (by omega) _ (by simp [rhoSet]) _ (by positivity) le_rfl).sub
      (hpf j (by omega) _ (by simp [rhoSet]) _ (by positivity) (by omega))
  fin_cases i
  · show VGe p (T + K) (∑ j : Fin 4, phi1Q n j * KQ n j)
    exact VGe.finset_sum fun j _ => (hr1 j).mul (hK j)
  · show VGe p (T + K) (∑ j : Fin 4, phiTQ n j * KQ n j)
    exact VGe.finset_sum fun j _ => (hrT j).mul (hK j)
  · show VGe p (T + K) (∑ j : Fin 4, phiHQ n j * KQ n j)
    exact VGe.finset_sum fun j _ => (hrH j).mul (hK j)

end

end Zeta2L2Chi3.Arith

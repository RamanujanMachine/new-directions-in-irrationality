/-
# Bounded-denominator parts of the forward vector

`Six p c`: every rational with denominator dividing `6` lies in `p^c ℤ_(p)`; this holds with
`c = -1` for every prime and with `c = 0` for `p ≥ 5`.  The coefficients of the polynomial parts,
the Bernoulli terms and `K(n) e₀` are then bounded in terms of `c`.
-/
import Zeta2L2Chi3.Arith.FwdAssemble

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

/-- every rational with denominator dividing `6` lies in `p^c ℤ_(p)` -/
def Six (p : ℕ) (c : ℤ) : Prop := ∀ (x : ℚ) (a : ℤ), x * 6 = a → VGe p c x

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem vge_sixth : VGe p (-(padicValNat p 6 : ℤ)) (1 / 6 : ℚ) := by
  right
  rw [show (1 / 6 : ℚ) = ((6 : ℕ) : ℚ)⁻¹ by norm_num, padicValRat.inv, padicValRat.of_nat]

theorem six_of (c : ℤ) (hc : -(padicValNat p 6 : ℤ) ≥ c) : Six p c := by
  intro x a hx
  have : x = (a : ℚ) * (1 / 6) := by rw [← hx]; ring
  rw [this]
  have := (VGe.intCast (p := p) a).mul vge_sixth
  exact this.mono (by omega)

theorem six_general : Six p (-1) := by
  apply six_of
  have : padicValNat p 6 ≤ 1 := by
    by_contra h
    push Not at h
    have h1 : p ^ 2 ∣ 6 := (pow_dvd_pow p h).trans pow_padicValNat_dvd
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 : p ≤ 2 := by nlinarith [hp.out.two_le]
    have h4 : p = 2 := le_antisymm h3 hp.out.two_le
    subst h4
    norm_num at h1
  omega

theorem six_large (hp5 : 5 ≤ p) : Six p 0 := by
  apply six_of
  have : ¬ p ∣ 6 := fun h => by
    have h1 := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> norm_num at h
    exact absurd hp.out (by norm_num)
  rw [padicValNat.eq_zero_of_not_dvd this]
  simp

theorem multiset_prod_vge (c : ℤ) (u : Multiset ℚ) (hu : ∀ x ∈ u, VGe p c x) :
    VGe p (Multiset.card u * c) u.prod := by
  induction u using Multiset.induction_on with
  | empty => right; simp
  | cons a u ih =>
    rw [Multiset.prod_cons, Multiset.card_cons]
    have := (hu a (Multiset.mem_cons_self a u)).mul (ih fun x hx => hu x (Multiset.mem_cons_of_mem hx))
    convert this using 1
    push_cast; ring

theorem esymm_vge (s : Multiset ℚ) (c : ℤ) (h : ∀ x ∈ s, VGe p c x) (k : ℕ) :
    VGe p (k * c) (s.esymm k) := by
  unfold Multiset.esymm
  refine Multiset.sum_induction _ _ (fun a b ha hb => ha.add hb) (VGe.zero _) fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hus, huk⟩ := Multiset.mem_powersetCard.1 hu
  have := multiset_prod_vge c u fun x hx => h x (Multiset.mem_of_le hus hx)
  rwa [huk] at this

variable {c : ℤ}

theorem ZQ_six (n : ℕ) : ∀ x ∈ ZQ n, ∃ a : ℤ, x * 6 = a := by
  intro x hx
  simp only [ZQ, Multiset.mem_add, Multiset.mem_map] at hx
  rcases hx with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · exact ⟨-(12 * n + 6 + 6 * i), by push_cast; ring⟩
  · exact ⟨-(8 + 6 * i), by push_cast; ring⟩
  · exact ⟨-(12 * n + 9 + 6 * i), by push_cast; ring⟩

theorem PQ_six (n : ℕ) : ∀ x ∈ PQ n, ∃ a : ℤ, x * 6 = a := by
  intro x hx
  simp only [PQ, Multiset.mem_add, Multiset.mem_map] at hx
  rcases hx with ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
  · exact ⟨6 * i, by push_cast; ring⟩
  · exact ⟨6 * i - 6 * n, by push_cast; ring⟩

theorem qc_vge (hc : c ≤ 0) (h6 : Six p c) (n j i : ℕ) : VGe p (2 * c) (qc n j i) := by
  have hZ : ∀ k : ℕ, VGe p (k * c) ((ZQ n).esymm k) := esymm_vge _ c fun x hx => by
    obtain ⟨a, ha⟩ := ZQ_six n x hx; exact h6 x a ha
  have hP : ∀ k : ℕ, VGe p (k * c) ((PQ n).esymm k) := esymm_vge _ c fun x hx => by
    obtain ⟨a, ha⟩ := PQ_six n x hx; exact h6 x a ha
  have h1 : VGe p c (c1 n) := by
    unfold c1; have := (hP 1).sub (hZ 1); simpa using this
  have h2 : VGe p (2 * c) (c2 n) := by
    unfold c2
    have := ((hZ 2).sub (hP 2)).add ((h1.mul (hP 1)).mono (by push_cast; omega))
    simpa using this
  have hone : VGe p (2 * c) 1 := (show VGe p 0 1 by right; simp).mono (by omega)
  unfold qc
  split <;> first | exact hone | exact h2 | exact h1.mono (by omega) | exact VGe.zero _

theorem zQ_vge (hc : c ≤ 0) (h6 : Six p c) (i : ℕ) (hi : i < 3) (x : ℚ) (a : ℤ) (hx : x * 6 = a) :
    VGe p (4 * c) (zQ i x) := by
  have vx : VGe p c x := h6 x a hx
  have v2 : VGe p c (1 / 2) := h6 _ 3 (by norm_num)
  have v3 : VGe p c (1 / 3) := h6 _ 2 (by norm_num)
  have v6 : VGe p c (1 / 6) := h6 _ 1 (by norm_num)
  have v32 : VGe p c (3 / 2) := h6 _ 9 (by norm_num)
  interval_cases i
  · show VGe p (4 * c) (1 / 2 - x)
    exact (v2.sub vx).mono (by omega)
  · show VGe p (4 * c) (-(x ^ 2 - x + 1 / 6) / 2)
    rw [show -(x ^ 2 - x + 1 / 6) / 2 = -(1 / 2 * (x ^ 2 - x + 1 / 6)) by ring]
    refine VGe.neg ?_
    have hs : VGe p (2 * c) (x ^ 2 - x + 1 / 6) := by
      have := VGe.pow 2 vx
      exact ((this.mono (by push_cast; omega)).sub (vx.mono (by omega))).add (v6.mono (by omega))
    exact (v2.mul hs).mono (by omega)
  · show VGe p (4 * c) (-(x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x) / 3)
    rw [show -(x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x) / 3 = -(1 / 3 * (x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x))
      by ring]
    refine VGe.neg ?_
    have hs : VGe p (3 * c) (x ^ 3 - 3 / 2 * x ^ 2 + 1 / 2 * x) := by
      have a3 := VGe.pow 3 vx
      have a2 := v32.mul (VGe.pow 2 vx)
      have a1 := v2.mul vx
      exact ((a3.mono (by push_cast; omega)).sub (a2.mono (by push_cast; omega))).add
        (a1.mono (by omega))
    exact (v3.mul hs).mono (by omega)

theorem UQ_vge (hc : c ≤ 0) (h6 : Six p c) (n j : ℕ) (x : ℚ) (hx : ∃ a : ℤ, x * 6 = a) :
    VGe p (6 * c) (UQ n j x) := by
  obtain ⟨a, ha⟩ := hx
  unfold UQ
  refine VGe.finset_sum fun i hi => ?_
  have hm : VGe p 0 ((-1 : ℚ) ^ i) := by
    have := VGe.pow i (VGe.intCast (p := p) (-1)); simpa using this
  have := ((qc_vge hc h6 n j i).mul hm).mul (zQ_vge hc h6 i (mem_range.1 hi) x a ha)
  exact this.mono (by omega)

theorem KQ_vge (h6 : Six p c) (n : ℕ) (j : Fin 4) : VGe p c (KQ n j) := by
  have hh : ∀ l : List ℤ, hornerR l (n : ℚ) = ((hornerR l (n : ℤ) : ℤ) : ℚ) := fun l => by
    have := hornerR_map (Int.castRingHom ℚ) l (n : ℤ)
    simpa using this.symm
  refine h6 _ (hornerR (Data.Knum j 0) (n : ℤ) * (6 / Data.Kden j 0)) ?_
  fin_cases j <;> simp [KQ, hh, Data.Kden] <;> ring

end

end Zeta2L2Chi3.Arith

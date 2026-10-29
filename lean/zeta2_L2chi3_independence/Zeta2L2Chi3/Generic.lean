/-
# Module 1: the generic final deduction (FIN01–FIN03)

* `irrational_of_linear_forms`: integer linear forms `Q_N α - P_N` tending to `0`, nonzero
  infinitely often, force irrationality (FIN01).
* `delta_lower_bound`: for an irrational `α` and rationals `r_N` with
  `|den r_N · α - num r_N| ≤ e^{-aN}` and `log den r_N ≤ H N`, eventually `δ_N ≥ a/H` (FIN02).
* `linIndep_of_irrational_mixtures`: irrationality of every nonzero integer mixture
  `α(A,B)` gives `ℚ`-linear independence of `1, C, Z` (FIN03).
-/
import Zeta2L2Chi3.Defs

open Real Filter Topology

namespace Zeta2L2Chi3

/-! ### FIN01: irrationality from small nonzero integer linear forms -/

theorem irrational_of_linear_forms (α : ℝ) (P Qd : ℕ → ℤ) (ε : ℕ → ℝ)
    (hbound : ∀ᶠ N in atTop, |(Qd N : ℝ) * α - P N| ≤ ε N)
    (hε : Tendsto ε atTop (𝓝 0))
    (hne : ∃ᶠ N in atTop, (Qd N : ℝ) * α ≠ P N) : Irrational α := by
  rintro ⟨q, rfl⟩
  have hq : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hsmall : ∀ᶠ N in atTop, ε N < 1 / q.den :=
    (tendsto_order.1 hε).2 _ (by positivity)
  obtain ⟨N, hN1, hN2⟩ := (hne.and_eventually (hbound.and hsmall)).exists
  obtain ⟨hb, hs⟩ := hN2
  -- `Q q - P = (Q num - P den)/den` is a nonzero integer divided by `den`
  have hkey : (Qd N : ℝ) * (q : ℝ) - P N = ((Qd N * q.num - P N * q.den : ℤ) : ℝ) / q.den := by
    rw [Rat.cast_def]; push_cast; field_simp
  have hz : (Qd N * q.num - P N * q.den : ℤ) ≠ 0 := by
    intro h; apply hN1; rw [← sub_eq_zero, hkey, h]; simp
  have h1 : (1 : ℝ) ≤ |((Qd N * q.num - P N * q.den : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
  have : 1 / (q.den : ℝ) ≤ |(Qd N : ℝ) * (q : ℝ) - P N| := by
    rw [hkey, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right h1 hq.le
  linarith

/-! ### FIN02: the strict liminf bound for `δ_N` -/

/-- The irrationality exponent of an approximation: `δ = -1 - log|α - r| / log(den r)`. -/
noncomputable def delta (α : ℝ) (r : ℚ) : ℝ := -1 - Real.log |α - r| / Real.log r.den

/-- If `α` is irrational and `|den r_N α - num r_N| → 0`, then `den r_N → ∞`. -/
theorem den_tendsto_atTop (α : ℝ) (hα : Irrational α) (r : ℕ → ℚ)
    (h : Tendsto (fun N => |((r N).den : ℝ) * α - (r N).num|) atTop (𝓝 0)) :
    Tendsto (fun N => (r N).den) atTop atTop := by
  rw [tendsto_atTop]
  intro D
  by_contra hcon
  rw [not_eventually] at hcon
  -- frequently `den < D`; pick a value `d < D` that occurs frequently
  have hfreq : ∃ᶠ N in atTop, (r N).den ∈ Finset.range D := by
    refine hcon.mono fun N hN => ?_
    simpa using hN
  have : ∃ d ∈ Finset.range D, ∃ᶠ N in atTop, (r N).den = d := by
    by_contra hno
    push Not at hno
    have hall : ∀ᶠ N in atTop, ∀ d ∈ Finset.range D, (r N).den ≠ d := by
      rw [Filter.eventually_all_finset]
      intro d hd
      simpa [Filter.not_frequently] using hno d hd
    obtain ⟨N, hN, hN'⟩ := (hfreq.and_eventually hall).exists
    exact hN' _ hN rfl
  obtain ⟨d, -, hd⟩ := this
  have hdpos : 0 < d := by
    obtain ⟨N, hN⟩ := hd.exists
    rw [← hN]; exact (r N).den_pos
  -- along this subsequence `d α` is within `1/3` of the integers `num`, hence an integer
  set m : ℤ := round ((d : ℝ) * α)
  have hlim : ∀ δ > 0, ∃ᶠ N in atTop, (r N).den = d ∧ |((r N).den : ℝ) * α - (r N).num| < δ :=
    fun δ hδ => hd.and_eventually ((tendsto_order.1 h).2 δ hδ)
  have hclose : ∀ δ > 0, δ < 1 / 2 → |(d : ℝ) * α - m| < δ := by
    intro δ hδ hδ'
    obtain ⟨N, hN1, hN2⟩ := (hlim δ hδ).exists
    rw [hN1] at hN2
    have hr : (r N).num = m := by
      have h1 := round_le ((d : ℝ) * α) ((r N).num)
      have h2 : |(d : ℝ) * α - m| < 1 / 2 := lt_of_le_of_lt h1 (by linarith)
      have h3 : |((r N).num : ℝ) - m| < 1 := by
        calc |((r N).num : ℝ) - m| = |((d : ℝ) * α - m) - ((d : ℝ) * α - (r N).num)| := by ring_nf
          _ ≤ |(d : ℝ) * α - m| + |(d : ℝ) * α - (r N).num| := abs_sub _ _
          _ < 1 / 2 + 1 / 2 := by linarith
          _ = 1 := by norm_num
      have h4 : |(r N).num - m| < 1 := by exact_mod_cast h3
      have := abs_lt.1 h4
      omega
    rw [hr] at hN2; exact hN2
  have hzero : (d : ℝ) * α - m = 0 := by
    by_contra hne
    have hpos : 0 < |(d : ℝ) * α - m| := abs_pos.2 hne
    have := hclose (min (|(d : ℝ) * α - m|) (1 / 4)) (lt_min hpos (by norm_num))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    exact absurd this (not_lt.2 (min_le_left _ _))
  apply hα
  refine ⟨(m : ℚ) / d, ?_⟩
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  push_cast
  field_simp
  linarith

/-- FIN02: eventual lower bound `δ_N ≥ a / H`. -/
theorem delta_lower_bound (α : ℝ) (hα : Irrational α) (r : ℕ → ℚ) (a H : ℝ)
    (ha : 0 < a) (hH : 0 < H)
    (herr : ∀ᶠ N in atTop, |((r N).den : ℝ) * α - (r N).num| ≤ Real.exp (-(a * N)))
    (hden : ∀ᶠ N in atTop, Real.log (r N).den ≤ H * N) :
    ∀ᶠ N in atTop, a / H ≤ delta α (r N) := by
  have hlim : Tendsto (fun N => |((r N).den : ℝ) * α - (r N).num|) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => Real.exp (-(a * N))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      apply tendsto_neg_atTop_atBot.comp
      exact Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop
    exact squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) herr h0
  have hden2 : ∀ᶠ N in atTop, 2 ≤ (r N).den :=
    (den_tendsto_atTop α hα r hlim).eventually (eventually_ge_atTop 2)
  filter_upwards [herr, hden, hden2, eventually_gt_atTop 0] with N h1 h2 h3 h4
  have hdpos : (0 : ℝ) < (r N).den := by exact_mod_cast (r N).den_pos
  have hlogd : 0 < Real.log (r N).den := Real.log_pos (by exact_mod_cast h3)
  have hne : ((r N).den : ℝ) * α - (r N).num ≠ 0 := by
    intro h0
    apply hα
    refine ⟨(r N).num / (r N).den, ?_⟩
    push_cast
    field_simp
    linarith
  have hpos : 0 < |((r N).den : ℝ) * α - (r N).num| := abs_pos.2 hne
  -- `|α - r| = |den α - num| / den`
  have hdiff : |α - (r N : ℝ)| = |((r N).den : ℝ) * α - (r N).num| / (r N).den := by
    rw [← abs_of_pos hdpos, ← abs_div, abs_of_pos hdpos]
    congr 1
    rw [Rat.cast_def]; field_simp
  have hdelta : delta α (r N) = -Real.log |((r N).den : ℝ) * α - (r N).num| / Real.log (r N).den := by
    unfold delta
    rw [hdiff, Real.log_div hpos.ne' hdpos.ne']
    field_simp
    ring
  rw [hdelta]
  have hl : a * N ≤ -Real.log |((r N).den : ℝ) * α - (r N).num| := by
    have := Real.log_le_log hpos h1
    rw [Real.log_exp] at this
    linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast h4
  rw [div_le_div_iff₀ hH hlogd]
  calc a * Real.log (r N).den ≤ a * (H * N) := by gcongr
    _ = (a * N) * H := by ring
    _ ≤ -Real.log |((r N).den : ℝ) * α - (r N).num| * H := by gcongr

/-! ### FIN03: linear independence of `1, C, Z` -/

theorem linIndep_of_irrational_mixtures
    (h : ∀ A B : ℤ, (A, B) ≠ (0, 0) → Irrational (alpha A B)) :
    ∀ u v w : ℚ, (u : ℝ) + v * C + w * Z = 0 → u = 0 ∧ v = 0 ∧ w = 0 := by
  intro u v w huvw
  -- the rational coefficients of `C` and `Z` in `α(A',B')` for `A' = (v + 3w/2)/2`, `B' = (v - 3w/2)/2`
  set A' : ℚ := (v + 3 * w / 2) / 2
  set B' : ℚ := (v - 3 * w / 2) / 2
  set lam : ℕ := A'.den * B'.den
  have hlam : (0 : ℚ) < lam := by positivity
  have hA : ((lam : ℚ) * A').den = 1 := by
    have : (lam : ℚ) * A' = ((A'.num * B'.den : ℤ) : ℚ) := by
      simp only [lam]; push_cast
      rw [mul_comm (A'.den : ℚ), mul_assoc, Rat.den_mul_eq_num]; ring
    rw [this]; exact Rat.den_intCast _
  have hB : ((lam : ℚ) * B').den = 1 := by
    have : (lam : ℚ) * B' = ((B'.num * A'.den : ℤ) : ℚ) := by
      simp only [lam]; push_cast
      rw [mul_assoc, Rat.den_mul_eq_num]; ring
    rw [this]; exact Rat.den_intCast _
  set A : ℤ := ((lam : ℚ) * A').num
  set B : ℤ := ((lam : ℚ) * B').num
  have hAeq : (A : ℚ) = lam * A' := by
    have := Rat.num_div_den ((lam : ℚ) * A'); rw [hA] at this; simpa using this
  have hBeq : (B : ℚ) = lam * B' := by
    have := Rat.num_div_den ((lam : ℚ) * B'); rw [hB] at this; simpa using this
  have halpha : alpha A B = (lam : ℝ) * (v * C + w * Z) := by
    rw [alpha_eq]
    have e1 : ((A : ℝ) + B) = (lam : ℝ) * v := by
      have : ((A : ℚ) + B) = lam * v := by rw [hAeq, hBeq]; simp only [A', B']; ring
      have := congrArg (Rat.cast : ℚ → ℝ) this; push_cast at this; linarith
    have e2 : (2 / 3 * ((A : ℝ) - B)) = (lam : ℝ) * w := by
      have : (2 / 3 * ((A : ℚ) - B)) = lam * w := by rw [hAeq, hBeq]; simp only [A', B']; ring
      have := congrArg (Rat.cast : ℚ → ℝ) this; push_cast at this; linarith
    rw [e1, e2]; ring
  by_cases hvw : v = 0 ∧ w = 0
  · obtain ⟨rfl, rfl⟩ := hvw
    refine ⟨?_, rfl, rfl⟩
    simpa using huvw
  · exfalso
    have hAB : (A, B) ≠ (0, 0) := by
      intro h0
      simp only [Prod.mk.injEq] at h0
      obtain ⟨hA0, hB0⟩ := h0
      have h1 : (lam : ℚ) * A' = 0 := by rw [← hAeq, hA0]; simp
      have h2 : (lam : ℚ) * B' = 0 := by rw [← hBeq, hB0]; simp
      have hA'0 : A' = 0 := (mul_eq_zero.1 h1).resolve_left hlam.ne'
      have hB'0 : B' = 0 := (mul_eq_zero.1 h2).resolve_left hlam.ne'
      apply hvw
      simp only [A', B'] at hA'0 hB'0
      constructor <;> linarith
    apply h A B hAB
    refine ⟨-(lam * u), ?_⟩
    rw [halpha]
    have : (v : ℝ) * C + w * Z = -u := by linarith
    rw [this]; push_cast; ring

theorem linearIndependent_one_C_Z
    (h : ∀ A B : ℤ, (A, B) ≠ (0, 0) → Irrational (alpha A B)) :
    LinearIndependent ℚ ![(1 : ℝ), C, Z] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h3 := linIndep_of_irrational_mixtures h (g 0) (g 1) (g 2)
  simp [Fin.sum_univ_three, Algebra.smul_def] at hg
  have := h3 (by simpa [mul_comm] using hg)
  fin_cases i <;> simp [this]

end Zeta2L2Chi3

/-
# The all-`n` dual transport `B̂_{n+1} = -B̂_n Q(n)` (END02, ANA06)

* the series state transports: `S(n+1) = -S(n) Q(n)` (telescoping of `G_k'` at the negative
  integers, using `G_k'(-1) = 0` and `G_k' → 0` at `-∞`);
* hence the harmonic row `B₀` transports (subtracting the already transported `B_T, B_H`);
* consequently the residue matrix equals the matrix product: `Bres n = Bhat n` for all `n`.
-/
import Zeta2L2Chi3.SeriesState
import Zeta2L2Chi3.GDeriv

open Filter Topology Finset

noncomputable section

namespace Zeta2L2Chi3

lemma hasDerivAt_sF (n k : ℕ) (hk : k ≤ 2) (x : ℝ) (hx : x < 0) :
    HasDerivAt (fun s : ℝ => s ^ k * F n s)
      (∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) / (x - l) ^ 2) x := by
  have hev : (fun s : ℝ => s ^ k * F n s) =ᶠ[𝓝 x]
      fun s => ∑ l ∈ Λ n, pfCoeff (Λ n) (pk n k) l / (s - l) := by
    filter_upwards [Iio_mem_nhds hx] with s hs
    refine sF_partialFrac n k hk s fun hmem => ?_
    have := Λ_nonneg n s hmem
    simp only [Set.mem_Iio] at hs; linarith
  have hd : HasDerivAt (fun s => ∑ l ∈ Λ n, pfCoeff (Λ n) (pk n k) l / (s - l))
      (∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) / (x - l) ^ 2) x := by
    apply HasDerivAt.fun_sum
    intro l hl
    have hne : x - l ≠ 0 := by have := Λ_nonneg n l hl; intro h; linarith
    have := ((hasDerivAt_id x).sub_const l).inv hne
    have h2 := this.const_mul (pfCoeff (Λ n) (pk n k) l)
    convert h2 using 1
    · ext s; simp [div_eq_mul_inv]
    · simp; ring
  exact hd.congr_of_eventuallyEq hev

lemma summable_S_terms (n k : ℕ) (hk : k ≤ 2) :
    Summable (fun m : ℕ => deriv (fun s : ℝ => s ^ k * F n s) (-((m : ℝ) + 1))) := by
  have h : ∀ m : ℕ, deriv (fun s : ℝ => s ^ k * F n s) (-((m : ℝ) + 1)) =
      ∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) * (1 / ((m : ℝ) + 1 + l) ^ 2) := by
    intro m
    rw [deriv_sF n k hk _ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (-((m : ℝ) + 1) - l) ^ 2 = ((m : ℝ) + 1 + l) ^ 2 := by ring
    rw [this]; ring
  simp_rw [h]
  exact summable_sum fun l hl => (summable_inv_sq_shift l (Λ_nonneg n l hl)).mul_left _

/-- derivative of `f_k` at negative points, as a combination of derivatives of `s^j F_m` -/
lemma hasDerivAt_fk (n : ℕ) (k : Fin 3) (x : ℝ) (hx : x < 0) :
    HasDerivAt (fk n k) (deriv (fun s : ℝ => s ^ (k : ℕ) * F (n + 1) s) x +
      ∑ j : Fin 3, Qk n j k * deriv (fun s : ℝ => s ^ (j : ℕ) * F n s) x) x := by
  have hk : (k : ℕ) ≤ 2 := by omega
  have e : fk n k = fun s : ℝ => s ^ (k : ℕ) * F (n + 1) s +
      ∑ j : Fin 3, Qk n j k * (s ^ (j : ℕ) * F n s) := by
    funext s; unfold fk; congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine (hasDerivAt_sF (n + 1) k hk x hx).differentiableAt.hasDerivAt.add ?_
  exact HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_sF n j (by omega) x hx).differentiableAt.hasDerivAt).const_mul _

/-- functions equal on a punctured neighbourhood and continuous at the point agree near it -/
lemma eventuallyEq_of_punctured {f g : ℝ → ℝ} {x : ℝ} (h : ∀ᶠ s in 𝓝[≠] x, f s = g s)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : f =ᶠ[𝓝 x] g := by
  have hx : f x = g x := by
    have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) := hf.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[≠] x) (𝓝 (g x)) := hg.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h1 (h2.congr' (h.mono fun s hs => hs.symm))
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with s hs
  by_cases hsx : s = x
  · rw [hsx, hx]
  · exact hs hsx

lemma deriv_fk (n : ℕ) (k : Fin 3) (x : ℝ) (hx : x < 0) :
    deriv (fk n k) x = deriv (Gk n k : ℝ → ℝ) x - deriv (Gk n k : ℝ → ℝ) (x - 1) := by
  have hG : DifferentiableAt ℝ (Gk n k) x := differentiableAt_Gk n k x hx
  have hG1 : DifferentiableAt ℝ (Gk n k) (x - 1) := differentiableAt_Gk n k (x - 1) (by linarith)
  have hfd : DifferentiableAt ℝ (fk n k) x := (hasDerivAt_fk n k x hx).differentiableAt
  have hD : HasDerivAt (fun s => Gk n k s - Gk n k (s - 1))
      (deriv (Gk n k : ℝ → ℝ) x - deriv (Gk n k : ℝ → ℝ) (x - 1)) x :=
    hG.hasDerivAt.sub (HasDerivAt.comp_sub_const x 1 hG1.hasDerivAt)
  have hev : fk n k =ᶠ[𝓝 x] fun s => Gk n k s - Gk n k (s - 1) :=
    eventuallyEq_of_punctured (f_eq_G_eventually n k x) hfd.continuousAt
      hD.differentiableAt.continuousAt
  rw [hev.deriv_eq, hD.deriv]

/-- `∑_m f_k'(-(m+1)) = 0`. -/
theorem tsum_deriv_fk (n : ℕ) (k : Fin 3) :
    ∑' m : ℕ, deriv (fk n k) (-((m : ℝ) + 1)) = 0 := by
  have hk : (k : ℕ) ≤ 2 := by omega
  -- summability
  have hsum : Summable (fun m : ℕ => deriv (fk n k) (-((m : ℝ) + 1))) := by
    have e : ∀ m : ℕ, deriv (fk n k) (-((m : ℝ) + 1)) =
        deriv (fun s : ℝ => s ^ (k : ℕ) * F (n + 1) s) (-((m : ℝ) + 1)) +
          ∑ j : Fin 3, Qk n j k * deriv (fun s : ℝ => s ^ (j : ℕ) * F n s) (-((m : ℝ) + 1)) :=
      fun m => (hasDerivAt_fk n k _ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)).deriv
    simp_rw [e]
    exact (summable_S_terms (n + 1) k hk).add
      (summable_sum fun j _ => (summable_S_terms n j (by omega)).mul_left _)
  -- partial sums telescope
  have hpart : ∀ M : ℕ, ∑ m ∈ range M, deriv (fk n k) (-((m : ℝ) + 1)) =
      deriv (Gk n k : ℝ → ℝ) (-1) - deriv (Gk n k : ℝ → ℝ) (-((M : ℝ) + 1)) := by
    intro M
    have h := Finset.sum_range_sub (fun m : ℕ => -deriv (Gk n k : ℝ → ℝ) (-((m : ℝ) + 1))) M
    rw [Finset.sum_congr rfl fun m _ => deriv_fk n k _
      (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)]
    have e : ∀ m : ℕ, -((m : ℝ) + 1) - 1 = -(((m + 1 : ℕ) : ℝ) + 1) := fun m => by push_cast; ring
    simp only [e]
    simp only [Nat.cast_zero, zero_add] at h
    linarith [h, show ∑ m ∈ range M, (deriv (Gk n k : ℝ → ℝ) (-((m : ℝ) + 1)) -
        deriv (Gk n k : ℝ → ℝ) (-(((m + 1 : ℕ) : ℝ) + 1))) =
        ∑ m ∈ range M, (-deriv (Gk n k : ℝ → ℝ) (-(((m + 1 : ℕ) : ℝ) + 1)) -
          -deriv (Gk n k : ℝ → ℝ) (-((m : ℝ) + 1))) from
        Finset.sum_congr rfl fun m _ => by ring]
  have hlim : Tendsto (fun M : ℕ => ∑ m ∈ range M, deriv (fk n k) (-((m : ℝ) + 1))) atTop
      (𝓝 (deriv (Gk n k : ℝ → ℝ) (-1) - 0)) := by
    simp_rw [hpart]
    refine tendsto_const_nhds.sub ?_
    refine (tendsto_deriv_Gk n k).comp ?_
    refine tendsto_neg_atTop_atBot.comp ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  rw [deriv_Gk_neg_one, sub_zero] at hlim
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim

/-- **Transport of the series state.** -/
theorem S_succ (n : ℕ) (k : Fin 3) : S (n + 1) k = -∑ j : Fin 3, S n j * Qk n j k := by
  have hk : (k : ℕ) ≤ 2 := by omega
  have h := tsum_deriv_fk n k
  have e : ∀ m : ℕ, deriv (fk n k) (-((m : ℝ) + 1)) =
      deriv (fun s : ℝ => s ^ (k : ℕ) * F (n + 1) s) (-((m : ℝ) + 1)) +
        ∑ j : Fin 3, Qk n j k * deriv (fun s : ℝ => s ^ (j : ℕ) * F n s) (-((m : ℝ) + 1)) :=
    fun m => (hasDerivAt_fk n k _ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)).deriv
  simp_rw [e] at h
  have hs1 := summable_S_terms (n + 1) k hk
  have hs2 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Summable (fun m : ℕ =>
      Qk n j k * deriv (fun s : ℝ => s ^ (j : ℕ) * F n s) (-((m : ℝ) + 1))) :=
    fun j _ => (summable_S_terms n j (by omega)).mul_left _
  rw [Summable.tsum_add hs1 (summable_sum hs2), Summable.tsum_finsetSum hs2] at h
  simp only [tsum_mul_left] at h
  unfold S
  rw [eq_neg_iff_add_eq_zero, ← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Transport of the harmonic row.** -/
theorem B0_succ_real (n : ℕ) (k : Fin 3) :
    (B0 (n + 1) k : ℝ) = -∑ j : Fin 3, (B0 n j : ℝ) * Qk n j k := by
  have hS := S_succ n k
  rw [S_eq (n + 1) k (by omega)] at hS
  simp only [fun j : Fin 3 => S_eq n j (by omega : (j : ℕ) ≤ 2)] at hS
  rw [BT_succ_real, BH_succ_real] at hS
  simp only [Fin.sum_univ_three] at hS ⊢
  linarith

/-! ### Conclusion over `ℚ` -/

theorem Bres_succ (n : ℕ) : (Bres (n + 1) : Matrix (Fin 3) (Fin 3) ℚ) = -(Bres n * Q n) := by
  ext i k
  have hQ : ∀ j k : Fin 3, (Qk n j k : ℝ) = ((Q n j k : ℚ) : ℝ) := fun j k => Qk_cast n j k
  simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three]
  apply Rat.cast_injective (α := ℝ)
  push_cast
  fin_cases i <;> fin_cases k
  · have h := B0_succ_real n 0; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := B0_succ_real n 1; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := B0_succ_real n 2; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := BT_succ_real n 0; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := BT_succ_real n 1; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := BT_succ_real n 2; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := BH_succ_real n 0; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := BH_succ_real n 1; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h
  · have h := BH_succ_real n 2; simp only [Fin.sum_univ_three, hQ] at h; simpa [Bres] using h

/-- **The residue rows are the matrix-product endpoint matrix for every `n`.** -/
theorem Bres_eq_Bhat (n : ℕ) : (Bres n : Matrix (Fin 3) (Fin 3) ℚ) = Bhat n := by
  induction n with
  | zero => exact Bres_zero
  | succ n ih => rw [Bres_succ, ih, Bhat]

end Zeta2L2Chi3

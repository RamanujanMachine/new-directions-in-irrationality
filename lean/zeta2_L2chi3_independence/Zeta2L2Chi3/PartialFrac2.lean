import Mathlib

noncomputable section

namespace Zeta2L2Chi3

open Polynomial Finset Filter Topology

/-- a function in partial-fraction form: polynomial part plus double and simple poles -/
def pfEval (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (t : ℝ) : ℝ :=
  q.eval t + ∑ k ∈ K, (a k / (t - k) ^ 2 + b k / (t - k))

theorem pf_exists (K : Finset ℝ) (e : ℝ → ℕ) (he : ∀ k ∈ K, e k ≤ 2) (N : ℝ[X]) :
    ∃ (q : ℝ[X]) (a b : ℝ → ℝ), (∀ k ∈ K, e k ≤ 1 → a k = 0) ∧ (∀ k ∈ K, e k = 0 → b k = 0) ∧
      ∀ t ∉ K, N.eval t / ∏ k ∈ K, (t - k) ^ e k = pfEval K q a b t := by
  classical
  obtain ⟨q, r, hr, hN⟩ := Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow (s := K) N
    (g := fun k => X - Polynomial.C k) (fun k _ => monic_X_sub_C k)
    (fun i _ j _ hij => isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hij).isUnit) e
  obtain ⟨c, hc⟩ : ∃ c : ℝ → ℕ → ℝ, ∀ k ∈ K, ∀ j : Fin (e k),
      r k j = Polynomial.C (c k j) := by
    refine ⟨fun k j => if h : j < e k then (r k ⟨j, h⟩).coeff 0 else 0, fun k hk j => ?_⟩
    have h := hr k hk j
    rw [degree_X_sub_C] at h
    simp only [j.2, dite_true]
    exact eq_C_of_degree_le_zero (Order.le_of_lt_succ h)
  refine ⟨q, fun k => if e k = 2 then c k 0 else 0,
    fun k => if e k = 2 then c k 1 else if e k = 1 then c k 0 else 0, ?_, ?_, ?_⟩
  · intro k _ h
    have : e k ≠ 2 := by omega
    simp [this]
  · intro k _ h
    simp [h]
  · intro t ht
    have hne : ∀ k ∈ K, t - k ≠ 0 := fun k hk => sub_ne_zero.2 (fun h => ht (h ▸ hk))
    have hP : ∏ k ∈ K, (t - k) ^ e k ≠ 0 :=
      prod_ne_zero_iff.2 fun k hk => pow_ne_zero _ (hne k hk)
    have hev := congrArg (Polynomial.eval t) hN
    simp only [eval_add, eval_mul, eval_finsetSum, eval_prod, eval_pow, eval_sub, eval_X,
      eval_C] at hev
    rw [hev, add_div, mul_div_assoc, div_self hP, mul_one, pfEval, sum_div]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    have hQ : ∏ m ∈ K.erase k, (t - m) ^ e m ≠ 0 :=
      prod_ne_zero_iff.2 fun m hm => pow_ne_zero _ (hne m (mem_of_mem_erase hm))
    rw [← mul_prod_erase K (fun m => (t - m) ^ e m) hk, sum_div]
    have key : ∀ j : Fin (e k), (eval t (r k j) * (t - k) ^ (j : ℕ) *
        ∏ m ∈ K.erase k, (t - m) ^ e m) / ((t - k) ^ e k * ∏ m ∈ K.erase k, (t - m) ^ e m) =
        c k j * (t - k) ^ (j : ℕ) / (t - k) ^ e k := by
      intro j
      rw [hc k hk j, eval_C, mul_div_mul_right _ _ hQ]
    rw [sum_congr rfl fun j _ => key j,
      Fin.sum_univ_eq_sum_range (fun j => c k j * (t - k) ^ j / (t - k) ^ e k)]
    have hk0 := hne k hk
    have h2 := he k hk
    obtain h | h | h : e k = 0 ∨ e k = 1 ∨ e k = 2 := by omega
    · simp [h]
    · simp [h]
    · simp only [h, sum_range_succ, sum_range_zero, ite_true, pow_zero, pow_one]
      field_simp
      ring

/-- the part of `pfEval` regular at `k₀` -/
def pfRest (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (k₀ t : ℝ) : ℝ :=
  q.eval t + ∑ k ∈ K.erase k₀, (a k / (t - k) ^ 2 + b k / (t - k))

theorem pfEval_split (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (k₀ : ℝ) (hk : k₀ ∈ K) (t : ℝ) :
    pfEval K q a b t = a k₀ / (t - k₀) ^ 2 + b k₀ / (t - k₀) + pfRest K q a b k₀ t := by
  rw [pfEval, pfRest, ← add_sum_erase K _ hk]
  ring

theorem pfRest_continuousAt (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (k₀ : ℝ) :
    ContinuousAt (pfRest K q a b k₀) k₀ := by
  unfold pfRest
  refine q.continuous.continuousAt.add ?_
  refine tendsto_finsetSum _ fun k hk => ?_
  have hne : k₀ - k ≠ 0 := sub_ne_zero.2 (ne_of_mem_erase hk).symm
  have h1 : ContinuousAt (fun t : ℝ => t - k) k₀ := (continuous_id.sub continuous_const).continuousAt
  exact (continuousAt_const.div (h1.pow 2) (pow_ne_zero _ hne)).add
    (continuousAt_const.div h1 hne)

theorem tendsto_double (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (k₀ : ℝ) (hk : k₀ ∈ K) :
    Tendsto (fun t => (t - k₀) ^ 2 * pfEval K q a b t) (𝓝[≠] k₀) (𝓝 (a k₀)) := by
  have hc : ContinuousAt (fun t => a k₀ + (t - k₀) * b k₀ + (t - k₀) ^ 2 * pfRest K q a b k₀ t)
      k₀ := by
    have h1 : ContinuousAt (fun t : ℝ => t - k₀) k₀ :=
      (continuous_id.sub continuous_const).continuousAt
    exact (continuousAt_const.add (h1.mul continuousAt_const)).add
      ((h1.pow 2).mul (pfRest_continuousAt K q a b k₀))
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {k₀}ᶜ))
  simp only [sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hl
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - k₀ ≠ 0 := sub_ne_zero.2 ht
  rw [pfEval_split K q a b k₀ hk t]
  field_simp

theorem tendsto_simple (K : Finset ℝ) (q : ℝ[X]) (a b : ℝ → ℝ) (k₀ : ℝ) (hk : k₀ ∈ K) :
    Tendsto (fun t => (t - k₀) * (pfEval K q a b t - a k₀ / (t - k₀) ^ 2)) (𝓝[≠] k₀)
      (𝓝 (b k₀)) := by
  have hc : ContinuousAt (fun t => b k₀ + (t - k₀) * pfRest K q a b k₀ t) k₀ := by
    have h1 : ContinuousAt (fun t : ℝ => t - k₀) k₀ :=
      (continuous_id.sub continuous_const).continuousAt
    exact continuousAt_const.add (h1.mul (pfRest_continuousAt K q a b k₀))
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {k₀}ᶜ))
  simp only [sub_self, zero_mul, add_zero] at hl
  refine hl.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - k₀ ≠ 0 := sub_ne_zero.2 ht
  rw [pfEval_split K q a b k₀ hk t]
  field_simp
  ring

theorem pfEval_sub (K : Finset ℝ) (q₁ q₂ : ℝ[X]) (a₁ b₁ a₂ b₂ : ℝ → ℝ) (t : ℝ) :
    pfEval K (q₁ - q₂) (a₁ - a₂) (b₁ - b₂) t = pfEval K q₁ a₁ b₁ t - pfEval K q₂ a₂ b₂ t := by
  simp only [pfEval, eval_sub, Pi.sub_apply, sub_div]
  rw [← sub_add_sub_comm, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  ring

theorem pf_eventually_notMem (S : Finset ℝ) (x : ℝ) : ∀ᶠ t in 𝓝[≠] x, t ∉ S := by
  classical
  have h1 : ∀ᶠ t in 𝓝 x, t ∉ S.erase x :=
    (S.erase x).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t h1 h2 h
  exact h1 (mem_erase.2 ⟨h2, h⟩)

/-- uniqueness: two partial-fraction forms agreeing outside a finite set coincide -/
theorem pf_unique (K : Finset ℝ) (q₁ q₂ : ℝ[X]) (a₁ b₁ a₂ b₂ : ℝ → ℝ) (E : Finset ℝ)
    (h : ∀ t ∉ K ∪ E, pfEval K q₁ a₁ b₁ t = pfEval K q₂ a₂ b₂ t) :
    q₁ = q₂ ∧ ∀ k ∈ K, a₁ k = a₂ k ∧ b₁ k = b₂ k := by
  classical
  set D := pfEval K (q₁ - q₂) (a₁ - a₂) (b₁ - b₂) with hD
  have hD0 : ∀ t ∉ K ∪ E, D t = 0 := fun t ht => by
    rw [hD, pfEval_sub, h t ht, sub_self]
  have hab : ∀ k ∈ K, a₁ k = a₂ k ∧ b₁ k = b₂ k := by
    intro k hk
    have hev := pf_eventually_notMem (K ∪ E) k
    have ha := tendsto_double K (q₁ - q₂) (a₁ - a₂) (b₁ - b₂) k hk
    have ha0 : Tendsto (fun t => (t - k) ^ 2 * D t) (𝓝[≠] k) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with t ht
      rw [hD0 t ht, mul_zero]
    have haeq := tendsto_nhds_unique ha ha0
    simp only [Pi.sub_apply] at haeq
    have hb := tendsto_simple K (q₁ - q₂) (a₁ - a₂) (b₁ - b₂) k hk
    have hb0 : Tendsto (fun t => (t - k) * (D t - (a₁ - a₂) k / (t - k) ^ 2)) (𝓝[≠] k)
        (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with t ht
      rw [hD0 t ht, Pi.sub_apply, haeq]
      simp
    have hbeq := tendsto_nhds_unique hb hb0
    simp only [Pi.sub_apply] at hbeq
    exact ⟨sub_eq_zero.1 haeq, sub_eq_zero.1 hbeq⟩
  refine ⟨?_, hab⟩
  have hq : q₁ - q₂ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := ((K ∪ E : Finset ℝ) : Set ℝ)ᶜ) ?_
      (K ∪ E).finite_toSet.infinite_compl
    intro t ht
    have ht' : t ∉ K ∪ E := ht
    have h0 := hD0 t ht'
    rw [hD, pfEval, sum_eq_zero, add_zero] at h0
    · exact h0
    · intro k hk
      obtain ⟨h1, h2⟩ := hab k hk
      simp [h1, h2]
  exact sub_eq_zero.1 hq

end Zeta2L2Chi3

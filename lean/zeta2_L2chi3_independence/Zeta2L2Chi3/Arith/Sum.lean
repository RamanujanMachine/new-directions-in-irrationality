/-
# Summation over primes: from per-prime valuation bounds to the content rate

Abstract summation theorem.  Per-prime lower bounds for `v_p(w_n)` are given on chambers
`n/p ∈ (L + lo, L + hi)` (with margin) for `p ≡ e (mod 6)`, `L < L2`, up to a loss `γ n p ≥ 0` of total
mass `O(log n)`; a crude uniform bound holds for all large primes; small primes and `p = 2, 3` have
the stated bounds.  The prime number theorem in progressions mod 6 (density `1/2` for each of the
classes 1, 5; `WeakPNT_AP`) then gives

`log cont(w_n) ≥ (12 log 2 + 18 log 3 + ½ Σ_{L, cells} m (1/(L+lo) - 1/(L+hi)) - C'/L2 - ε) n`

for all large `n`.
-/
import Zeta2L2Chi3.Arith.Valuation
import Zeta2L2Chi3.Matrices
import PrimeNumberTheoremAnd.Wiener

namespace Zeta2L2Chi3.Arith

open Filter Finset Chebyshev ArithmeticFunction Asymptotics

/-- a chamber `x - L ∈ (lo, hi)` for primes `p ≡ e (mod 6)` carrying the valuation bound `m` -/
structure Chamber where
  e : ℕ
  lo : ℚ
  hi : ℚ
  m : ℤ

/-- the chambers of each lift `L` and residue `e ∈ {1, 5}` form a chain from `0` to `1` -/
def ChainCover (ch : List Chamber) (e : ℕ) : Prop :=
  ∃ pts : List ℚ, pts.head? = some 0 ∧ pts.getLast? = some 1 ∧
    (ch.filter (fun c => c.e = e)).map (fun c => (c.lo, c.hi)) = pts.zip pts.tail ∧
    pts.Pairwise (· < ·)

/-- the density contribution `½ Σ m (1/(L+lo) - 1/(L+hi))` (the `L = 0, lo = 0` chamber must
carry `m = 0` and contributes `0`) -/
noncomputable def chamberDensity (cells : ℕ → List Chamber) (L2 : ℕ) : ℝ :=
  ∑ L ∈ Finset.range L2, ((cells L).map (fun c =>
    if L = 0 ∧ c.lo = 0 then 0 else
      (c.m : ℝ) / 2 * (1 / ((L : ℝ) + c.lo) - 1 / ((L : ℝ) + c.hi)))).sum

/-! ### Prime number theorem in the progressions `1, 5 mod 6` -/

/-- `θ(x; 6, e) = Σ_{p ≤ x, p ≡ e (6)} log p` -/
noncomputable def thetaE (e : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊ with (p % 6 = e ∧ p.Prime), Real.log p

lemma thetaE_nonneg (e : ℕ) (x : ℝ) : 0 ≤ thetaE e x :=
  sum_nonneg fun p _ => Real.log_natCast_nonneg p

lemma cumsum_AP_eq (e m : ℕ) :
    cumsum (fun n ↦ if n % 6 = e then Λ n else 0) (m + 1) =
      ∑ n ∈ Ioc 0 m with n % 6 = e, Λ n := by
  have hr : range (m + 1) = insert 0 (Ioc 0 m) := by
    ext i; simp only [mem_range, mem_insert, mem_Ioc]; omega
  rw [cumsum, hr, sum_insert (by simp), sum_filter]
  simp

lemma thetaE_cumsum (e : ℕ) (x : ℝ) :
    thetaE e x ≤ cumsum (fun n ↦ if n % 6 = e then Λ n else 0) (⌊x⌋₊ + 1) ∧
    cumsum (fun n ↦ if n % 6 = e then Λ n else 0) (⌊x⌋₊ + 1) - thetaE e x ≤ ψ x - θ x := by
  rw [cumsum_AP_eq, psi_sub_theta_eq_sum_not_prime]
  have hsplit := sum_filter_add_sum_filter_not ((Ioc 0 ⌊x⌋₊).filter (· % 6 = e)) Nat.Prime Λ
  rw [filter_filter, filter_filter] at hsplit
  have h1 : ∑ n ∈ Ioc 0 ⌊x⌋₊ with (n % 6 = e ∧ n.Prime), Λ n = thetaE e x :=
    sum_congr rfl (fun n hn => vonMangoldt_apply_prime (mem_filter.1 hn).2.2)
  have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊ with (n % 6 = e ∧ ¬ n.Prime), Λ n ≤
      ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬ n.Prime, Λ n :=
    sum_le_sum_of_subset_of_nonneg (fun n hn => by simp at hn ⊢; tauto)
      (fun _ _ _ => vonMangoldt_nonneg)
  have h3 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊ with (n % 6 = e ∧ ¬ n.Prime), Λ n :=
    sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  constructor <;> linarith

lemma totient_six : Nat.totient 6 = 2 := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.totient_mul (by norm_num),
    Nat.totient_prime Nat.prime_two, Nat.totient_prime Nat.prime_three]

lemma thetaE_asymp {e : ℕ} (he : e = 1 ∨ e = 5) :
    ∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, |thetaE e x - x / 2| ≤ ε * x := by
  intro ε hε
  have hT : Tendsto (fun N ↦ cumsum (fun n ↦ if n % 6 = e then Λ n else 0) N / N) atTop
      (nhds (1 / 2)) := by
    have := WeakPNT_AP (q := 6) (a := e) (by norm_num)
      (by rcases he with rfl | rfl <;> norm_num) (by omega)
    rwa [totient_six, Nat.cast_ofNat] at this
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 hT) (ε / 4) (by positivity)
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  set C' := max C 0 with hC'
  refine ⟨max (max (N0 : ℝ) (2 / ε)) (max 1 ((4 * C' / ε) ^ 2)), fun x hx => ?_⟩
  have hxN0 : (N0 : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxe : 2 / ε ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxC : (4 * C' / ε) ^ 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 ≤ x := by linarith
  set N := ⌊x⌋₊ + 1 with hN
  have hNN0 : N0 ≤ N := by
    have : N0 ≤ ⌊x⌋₊ := Nat.le_floor hxN0
    omega
  have hNx : x < (N : ℝ) := by rw [hN]; push_cast; exact Nat.lt_floor_add_one x
  have hNx' : (N : ℝ) ≤ x + 1 := by
    rw [hN]; push_cast; linarith [Nat.floor_le hx0]
  have hNpos : (0 : ℝ) < N := by linarith
  have hd := hN0 N hNN0
  rw [Real.dist_eq, abs_lt] at hd
  have hd1 : cumsum (fun n ↦ if n % 6 = e then Λ n else 0) N - N / 2 < ε / 4 * N := by
    have h' : cumsum (fun n ↦ if n % 6 = e then Λ n else 0) N / N < 1 / 2 + ε / 4 := by
      linarith [hd.2]
    rw [div_lt_iff₀ hNpos] at h'
    linarith
  have hd2 : N / 2 - cumsum (fun n ↦ if n % 6 = e then Λ n else 0) N < ε / 4 * N := by
    have h' : 1 / 2 - ε / 4 < cumsum (fun n ↦ if n % 6 = e then Λ n else 0) N / N := by
      linarith [hd.1]
    rw [lt_div_iff₀ hNpos] at h'
    linarith
  obtain ⟨hc1, hc2⟩ := thetaE_cumsum e x
  have hpt : ψ x - θ x ≤ C' * √x :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))
  have hsq : 4 * C' / ε ≤ √x := by
    rw [Real.le_sqrt (by positivity) hx0]; exact hxC
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0
  have hC'x : C' * √x ≤ ε / 4 * x := by
    have h1 : C' ≤ ε / 4 * √x := by
      rw [div_le_iff₀ hε] at hsq; linarith
    calc C' * √x ≤ ε / 4 * √x * √x := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg x)
      _ = ε / 4 * x := by rw [mul_assoc, hsx]
  have hhalf : 1 / 2 ≤ ε / 4 * x := by
    rw [div_le_iff₀ hε] at hxe; nlinarith
  have hN2 : ε / 4 * N ≤ ε / 2 * x := by
    have : (N : ℝ) ≤ 2 * x := by linarith
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- a linear-growth sample of the progression sum -/
lemma ev_lin (a b c : ℝ) (ha : 0 < a) : ∀ᶠ n : ℕ in atTop, c ≤ a * n + b := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ((c - b) / a)] with n hn
  have := (div_le_iff₀ ha).1 hn
  linarith

lemma thetaE_lin {e : ℕ} (he : e = 1 ∨ e = 5) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |thetaE e (α * n + β) - α * n / 2| ≤ ε * n := by
  intro ε hε
  obtain ⟨X, hX⟩ := thetaE_asymp he (ε / (2 * α)) (by positivity)
  have h2 : ∀ᶠ n : ℕ in atTop, |β| / 2 + ε / (2 * α) * |β| ≤ ε / 2 * n :=
    by simpa using ev_lin (ε / 2) 0 (|β| / 2 + ε / (2 * α) * |β|) (by positivity)
  filter_upwards [ev_lin α β X hα, h2] with n h1 h2
  have h := abs_le.1 (hX _ h1)
  have key : ε / (2 * α) * (α * n + β) = ε / 2 * n + ε / (2 * α) * β := by
    field_simp
  have hb1 : ε / (2 * α) * β ≤ ε / (2 * α) * |β| :=
    mul_le_mul_of_nonneg_left (le_abs_self β) (by positivity)
  have hb2 : -(ε / (2 * α) * |β|) ≤ ε / (2 * α) * β := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le β) (by positivity)
  rw [abs_le]
  constructor
  · nlinarith [le_abs_self β, neg_abs_le β]
  · nlinarith [le_abs_self β, neg_abs_le β]

/-! ### Linear lower-bound rates -/

/-- `f n ≥ (a - o(1)) n` -/
def LB (f : ℕ → ℝ) (a : ℝ) : Prop := ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (a - ε) * n ≤ f n

lemma LB.add {f g : ℕ → ℝ} {a b : ℝ} (hf : LB f a) (hg : LB g b) :
    LB (fun n => f n + g n) (a + b) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity)] with n h1 h2
  have : (a + b - ε) * n = (a - ε / 2) * n + (b - ε / 2) * n := by ring
  linarith

lemma LB.mono {f g : ℕ → ℝ} {a b : ℝ} (hf : LB f a) (hab : b ≤ a)
    (hfg : ∀ᶠ n in atTop, f n ≤ g n) : LB g b := by
  intro ε hε
  filter_upwards [hf ε hε, hfg] with n h1 h2
  have : (b - ε) * n ≤ (a - ε) * n :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  linarith

lemma LB.const_mul {f : ℕ → ℝ} {a : ℝ} (c : ℝ) (hc : 0 ≤ c) (hf : LB f a) :
    LB (fun n => c * f n) (c * a) := by
  rcases hc.eq_or_lt with rfl | hc
  · intro ε hε
    filter_upwards with n
    simp only [zero_mul, zero_sub, neg_mul, Left.neg_nonpos_iff]
    positivity
  · intro ε hε
    filter_upwards [hf (ε / c) (by positivity)] with n h
    have h1 := mul_le_mul_of_nonneg_left h hc.le
    have h2 : c * ((a - ε / c) * n) = (c * a - ε) * n := by field_simp
    linarith

lemma LB.zero_of_small {g : ℕ → ℝ} (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |g n| ≤ ε * n) :
    LB g 0 := by
  intro ε hε
  filter_upwards [h ε hε] with n hn
  have := neg_abs_le (g n)
  linarith

lemma LB.list_sum {ι : Type*} (f : ι → ℕ → ℝ) (a : ι → ℝ) :
    ∀ l : List ι, (∀ i ∈ l, LB (f i) (a i)) →
      LB (fun n => (l.map (fun i => f i n)).sum) (l.map a).sum
  | [], _ => by
    intro ε hε
    filter_upwards with n
    simp only [List.map_nil, List.sum_nil, zero_sub, neg_mul, Left.neg_nonpos_iff]
    positivity
  | i :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (LB.list_sum f a l (fun j hj => h j (by simp [hj])))

lemma LB_thetaE {e : ℕ} (he : e = 1 ∨ e = 5) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    LB (fun n => thetaE e (α * n + β)) (α / 2) := by
  intro ε hε
  filter_upwards [thetaE_lin he hα β ε hε] with n h
  have := (abs_le.1 h).1
  have e : (α / 2 - ε) * n = α * n / 2 - ε * n := by ring
  linarith

lemma LB_neg_thetaE {e : ℕ} (he : e = 1 ∨ e = 5) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    LB (fun n => -thetaE e (α * n + β)) (-(α / 2)) := by
  intro ε hε
  filter_upwards [thetaE_lin he hα β ε hε] with n h
  have := (abs_le.1 h).2
  have e : (-(α / 2) - ε) * n = -(α * n / 2) - ε * n := by ring
  linarith

/-! ### Negligible terms -/

lemma small_of_isLittleO {g : ℝ → ℝ} (hg : g =o[atTop] id) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |g n| ≤ ε * n := by
  intro ε hε
  have h1 := hg.bound hε
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with n hn
  simpa [Real.norm_eq_abs, Nat.abs_cast] using hn

lemma isLittleO_sqrt_mul_log : (fun x : ℝ => √x * Real.log x) =o[atTop] id := by
  have h1 : Real.log =o[atTop] fun x : ℝ => √x := by
    have := isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)
    refine this.congr' (by filter_upwards with x; rfl) ?_
    filter_upwards with x
    rw [Real.sqrt_eq_rpow]
  have h2 := (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO h1
  refine h2.congr' (by filter_upwards with x; rfl) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx

lemma isLittleO_sqrt : (fun x : ℝ => √x) =o[atTop] id := by
  have h1 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => √x := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    have := Real.tendsto_sqrt_atTop
    exact tendsto_norm_atTop_atTop.comp this
  have h2 := (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO h1
  refine h2.congr' (by filter_upwards with x; ring) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx

lemma isLittleO_log_succ : (fun x : ℝ => Real.log (x + 1)) =o[atTop] id := by
  have h1 := Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have h2 : (fun x : ℝ => x + 1) =O[atTop] (id : ℝ → ℝ) := by
    refine (isBigO_refl (id : ℝ → ℝ) atTop).add ?_
    exact (isLittleO_const_id_atTop (1 : ℝ)).isBigO
  exact h1.trans_isBigO h2

lemma thetaE_sub_le (e : ℕ) (u v : ℝ) :
    thetaE e v - thetaE e u ≤ ∑ q ∈ Ioc ⌊u⌋₊ ⌊v⌋₊ with (q % 6 = e ∧ q.Prime), Real.log q := by
  unfold thetaE
  have hsub : (Ioc 0 ⌊v⌋₊).filter (fun q => q % 6 = e ∧ q.Prime) ⊆
      (Ioc 0 ⌊u⌋₊).filter (fun q => q % 6 = e ∧ q.Prime) ∪
        (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun q => q % 6 = e ∧ q.Prime) := by
    intro q hq
    simp only [mem_union, mem_filter, mem_Ioc] at hq ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    by_cases hqu : q ≤ ⌊u⌋₊
    · exact Or.inl ⟨⟨h1, hqu⟩, h3⟩
    · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
  have hdisj : Disjoint ((Ioc 0 ⌊u⌋₊).filter (fun q => q % 6 = e ∧ q.Prime))
      ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun q => q % 6 = e ∧ q.Prime)) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    simp only [mem_filter, mem_Ioc] at h1 h2
    omega
  have := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => Real.log_natCast_nonneg q)
  rw [sum_union hdisj] at this
  linarith

lemma prime_mod_six {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) : q % 6 = 1 ∨ q % 6 = 5 := by
  have h2 : ¬ 2 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h; omega
  have h3 : ¬ 3 ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h; omega
  omega

/-! ### Negligible (`o(n)`) sequences -/

def Small (g : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |g n| ≤ ε * n

lemma Small.add {f g : ℕ → ℝ} (hf : Small f) (hg : Small g) : Small (fun n => f n + g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity)] with n h1 h2
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ ε / 2 * n + ε / 2 * n := add_le_add h1 h2
    _ = ε * n := by ring

lemma Small.const_mul {f : ℕ → ℝ} (c : ℝ) (hf : Small f) : Small (fun n => c * f n) := by
  intro ε hε
  filter_upwards [hf (ε / (|c| + 1)) (by positivity)] with n h
  have hc : 0 ≤ |c| := abs_nonneg c
  rw [abs_mul]
  calc |c| * |f n| ≤ |c| * (ε / (|c| + 1) * n) := mul_le_mul_of_nonneg_left h hc
    _ ≤ (|c| + 1) * (ε / (|c| + 1) * n) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε * n := by field_simp

lemma Small.mono {f g : ℕ → ℝ} (hg : Small g) (h : ∀ᶠ n : ℕ in atTop, |f n| ≤ |g n|) :
    Small f := by
  intro ε hε
  filter_upwards [hg ε hε, h] with n h1 h2
  linarith

lemma Small.lb {g : ℕ → ℝ} (h : Small g) : LB g 0 := LB.zero_of_small h

lemma LB_lin (c : ℝ) : LB (fun n => c * n) c := by
  intro ε hε
  filter_upwards with n
  have : 0 ≤ ε * n := by positivity
  nlinarith

lemma small_log (c : ℝ) : Small (fun n => c * Real.log n) :=
  Small.const_mul c (small_of_isLittleO Real.isLittleO_log_id_atTop)

lemma small_log_succ (c : ℝ) : Small (fun n => c * Real.log (n + 1)) :=
  Small.const_mul c (small_of_isLittleO isLittleO_log_succ)

lemma small_sqrt_log (c : ℝ) : Small (fun n => c * (√n * Real.log n)) :=
  Small.const_mul c (small_of_isLittleO isLittleO_sqrt_mul_log)

lemma small_sqrt : Small (fun n => √n) := small_of_isLittleO isLittleO_sqrt

/-! ### Chains -/

lemma zip_tail_pairwise : ∀ pts : List ℚ, pts.Pairwise (· < ·) →
    (∀ p ∈ pts.zip pts.tail, p.1 < p.2 ∧ p.1 ∈ pts ∧ p.2 ∈ pts) ∧
    (pts.zip pts.tail).Pairwise (fun p p' => p.2 ≤ p'.1)
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: rest, h => by
    have ih := zip_tail_pairwise (b :: rest) (List.pairwise_cons.1 h).2
    have hab : ∀ y ∈ b :: rest, a < y := (List.pairwise_cons.1 h).1
    have hb : ∀ y ∈ rest, b < y := (List.pairwise_cons.1 (List.pairwise_cons.1 h).2).1
    simp only [List.tail_cons, List.zip_cons_cons]
    simp only [List.tail_cons] at ih
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hab b (by simp), by simp, by simp⟩
      · obtain ⟨h1, h2, h3⟩ := ih.1 p hp
        exact ⟨h1, List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
    · refine List.Pairwise.cons ?_ ih.2
      intro p' hp'
      obtain ⟨_, h2, _⟩ := ih.1 p' hp'
      rcases List.mem_cons.1 h2 with h | h
      · exact le_of_eq h.symm
      · exact (hb _ h).le

lemma zip_tail_telescope (F : ℚ → ℝ) : ∀ (pts : List ℚ) (x y : ℚ), pts.head? = some x →
    pts.getLast? = some y → ((pts.zip pts.tail).map (fun p => F p.1 - F p.2)).sum = F x - F y
  | [], x, y, h, _ => by simp at h
  | [a], x, y, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    subst h1; subst h2; simp
  | a :: b :: rest, x, y, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have ih := zip_tail_telescope F (b :: rest) b y rfl
      (by rw [List.getLast?_cons_cons] at h2; exact h2)
    simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

lemma pts_head (pts : List ℚ) (h0 : pts.head? = some 0) : ∃ t, pts = 0 :: t := by
  cases pts with
  | nil => simp at h0
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at h0; exact ⟨t, by rw [h0]⟩

lemma pts_bounds (pts : List ℚ) (h0 : pts.head? = some 0) (h1 : pts.getLast? = some 1)
    (hs : pts.Pairwise (· < ·)) : ∀ p ∈ pts, 0 ≤ p ∧ p ≤ 1 := by
  intro p hp
  constructor
  · obtain ⟨t, rfl⟩ := pts_head pts h0
    rcases List.mem_cons.1 hp with rfl | hp
    · exact le_refl _
    · exact ((List.pairwise_cons.1 hs).1 p hp).le
  · obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.1 h1
    rcases List.mem_append.1 hp with hp | hp
    · exact ((List.pairwise_append.1 hs).2.2 p hp 1 (by simp)).le
    · simp only [List.mem_singleton] at hp; rw [hp]

lemma chain_props {ch : List Chamber} {e : ℕ} (h : ChainCover ch e) :
    (∀ c ∈ ch, c.e = e → 0 ≤ c.lo ∧ c.lo < c.hi ∧ c.hi ≤ 1) ∧
    (ch.filter (fun c => c.e = e)).Pairwise (fun c c' => c.hi ≤ c'.lo) ∧
    (∀ F : ℚ → ℝ,
      ((ch.filter (fun c => c.e = e)).map (fun c => F c.lo - F c.hi)).sum = F 0 - F 1) ∧
    (∃ c ∈ ch, c.e = e ∧ c.lo = 0) := by
  obtain ⟨pts, h0, h1, hz, hs⟩ := h
  obtain ⟨hz1, hz2⟩ := zip_tail_pairwise pts hs
  have hb := pts_bounds pts h0 h1 hs
  have hmem : ∀ c ∈ ch.filter (fun c => c.e = e), (c.lo, c.hi) ∈ pts.zip pts.tail :=
    fun c hc => hz ▸ List.mem_map_of_mem hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc hce
    have hc' : c ∈ ch.filter (fun c => c.e = e) := List.mem_filter.2 ⟨hc, by simpa using hce⟩
    obtain ⟨h1, h2, h3⟩ := hz1 _ (hmem c hc')
    exact ⟨(hb _ h2).1, h1, (hb _ h3).2⟩
  · have : ((ch.filter (fun c => c.e = e)).map (fun c => (c.lo, c.hi))).Pairwise
        (fun p p' => p.2 ≤ p'.1) := hz ▸ hz2
    exact List.pairwise_map.1 this
  · intro F
    have := zip_tail_telescope F pts 0 1 h0 h1
    rw [← hz, List.map_map] at this
    exact this
  · obtain ⟨t, rfl⟩ := pts_head pts h0
    cases t with
    | nil => simp at h1
    | cons b r =>
      have : ((0 : ℚ), b) ∈ (ch.filter (fun c => c.e = e)).map (fun c => (c.lo, c.hi)) := by
        rw [hz]; simp
      obtain ⟨c, hc, hcb⟩ := List.mem_map.1 this
      have hc2 := List.mem_filter.1 hc
      exact ⟨c, hc2.1, by simpa using hc2.2, by simp only [Prod.mk.injEq] at hcb; exact hcb.1⟩

lemma pairwise_of_filter {α : Type*} (key : α → ℕ) (R : α → α → Prop) : ∀ (l : List α),
    (∀ e, (l.filter (fun a => key a = e)).Pairwise R) →
      l.Pairwise (fun a b => key a ≠ key b ∨ R a b)
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    rw [List.pairwise_cons]
    constructor
    · intro b hb
      by_cases hk : key a = key b
      · right
        have := h (key a)
        rw [List.filter_cons_of_pos (by simp)] at this
        exact (List.pairwise_cons.1 this).1 b (List.mem_filter.2 ⟨hb, by simp [hk]⟩)
      · left; exact hk
    · apply pairwise_of_filter key R l
      intro e
      have := h e
      by_cases hk : key a = e
      · rw [List.filter_cons_of_pos (by simpa using hk)] at this
        exact (List.pairwise_cons.1 this).2
      · rw [List.filter_cons_of_neg (by simpa using hk)] at this
        exact this

lemma list_sum_split (G : Chamber → ℝ) : ∀ (l : List Chamber), (∀ c ∈ l, c.e = 1 ∨ c.e = 5) →
    (l.map G).sum = ((l.filter (fun c => c.e = 1)).map G).sum +
      ((l.filter (fun c => c.e = 5)).map G).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := list_sum_split G l (fun c hc => h c (by simp [hc]))
    rcases h a (by simp) with ha | ha
    · rw [List.filter_cons_of_pos (by simp [ha]), List.filter_cons_of_neg (by simp [ha])]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring
    · rw [List.filter_cons_of_neg (by simp [ha]), List.filter_cons_of_pos (by simp [ha])]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring

/-! ### The list of all chambers -/

def allc (cells : ℕ → List Chamber) (N : ℕ) : List (ℕ × Chamber) :=
  (List.range N).flatMap (fun L => (cells L).map (fun c => (L, c)))

lemma mem_allc {cells : ℕ → List Chamber} {N : ℕ} {x : ℕ × Chamber} :
    x ∈ allc cells N ↔ x.1 < N ∧ x.2 ∈ cells x.1 := by
  simp only [allc, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨L, hL, c, hc, rfl⟩; exact ⟨hL, hc⟩
  · intro h; exact ⟨x.1, h.1, x.2, h.2, rfl⟩

lemma allc_sum (cells : ℕ → List Chamber) (G : ℕ × Chamber → ℝ) : ∀ N,
    ((allc cells N).map G).sum = ∑ L ∈ Finset.range N, ((cells L).map (fun c => G (L, c))).sum
  | 0 => by simp [allc]
  | N + 1 => by
    rw [Finset.sum_range_succ, ← allc_sum cells G N]
    simp [allc, List.range_succ, List.flatMap_append, Function.comp_def]

lemma allc_pairwise (cells : ℕ → List Chamber) (N : ℕ)
    (hbd : ∀ L < N, ∀ c ∈ cells L, 0 ≤ c.lo ∧ c.lo < c.hi ∧ c.hi ≤ 1)
    (hpw : ∀ L < N, (cells L).Pairwise (fun c c' => c.e ≠ c'.e ∨ c.hi ≤ c'.lo)) :
    (allc cells N).Pairwise (fun x y => x.2.e ≠ y.2.e ∨ (x.1 : ℚ) + x.2.hi ≤ y.1 + y.2.lo) := by
  unfold allc
  rw [List.pairwise_flatMap]
  constructor
  · intro L hL
    rw [List.pairwise_map]
    refine (hpw L (List.mem_range.1 hL)).imp ?_
    rintro c c' (h | h)
    · exact Or.inl h
    · right; simp only; linarith
  · refine List.pairwise_lt_range.imp_of_mem ?_
    intro L L' hL hL' hlt x hx y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hy
    right
    have h1 := (hbd L (List.mem_range.1 hL) c hc).2.2
    have h2 := (hbd L' (List.mem_range.1 hL') c' hc').1
    have h3 : (L : ℚ) + 1 ≤ L' := by exact_mod_cast hlt
    simp only
    linarith

lemma cells_facts (cells : ℕ → List Chamber) (L2 : ℕ)
    (hcov : ∀ L < L2, ChainCover (cells L) 1 ∧ ChainCover (cells L) 5)
    (he : ∀ L < L2, ∀ c ∈ cells L, c.e = 1 ∨ c.e = 5) :
    (∀ L < L2, ∀ c ∈ cells L, 0 ≤ c.lo ∧ c.lo < c.hi ∧ c.hi ≤ 1) ∧
    (allc cells L2).Pairwise (fun x y => x.2.e ≠ y.2.e ∨ (x.1 : ℚ) + x.2.hi ≤ y.1 + y.2.lo) ∧
    (∀ L < L2, ∀ F : ℚ → ℝ, ((cells L).map (fun c => F c.lo - F c.hi)).sum = 2 * (F 0 - F 1)) ∧
    (0 < L2 → ∀ e, e = 1 ∨ e = 5 → ∃ c ∈ cells 0, c.e = e ∧ c.lo = 0) := by
  have hbd : ∀ L < L2, ∀ c ∈ cells L, 0 ≤ c.lo ∧ c.lo < c.hi ∧ c.hi ≤ 1 := by
    intro L hL c hc
    rcases he L hL c hc with h | h
    · exact (chain_props (hcov L hL).1).1 c hc h
    · exact (chain_props (hcov L hL).2).1 c hc h
  refine ⟨hbd, allc_pairwise cells L2 hbd ?_, ?_, ?_⟩
  · intro L hL
    apply pairwise_of_filter Chamber.e (fun c c' => c.hi ≤ c'.lo) (cells L)
    intro e
    by_cases h1 : e = 1
    · subst h1; exact (chain_props (hcov L hL).1).2.1
    by_cases h5 : e = 5
    · subst h5; exact (chain_props (hcov L hL).2).2.1
    rw [List.filter_eq_nil_iff.2 ?_]
    · exact List.Pairwise.nil
    intro c hc
    have := he L hL c hc
    simp only [decide_eq_true_eq]
    omega
  · intro L hL F
    rw [list_sum_split _ _ (he L hL), (chain_props (hcov L hL).1).2.2.1 F,
      (chain_props (hcov L hL).2).2.2.1 F]
    ring
  · intro hL2 e he'
    rcases he' with rfl | rfl
    · exact (chain_props (hcov 0 hL2).1).2.2.2
    · exact (chain_props (hcov 0 hL2).2).2.2.2

/-! ### Misc list/finset tools -/

lemma exists_bound_list (g : Chamber → ℝ) : ∀ l : List Chamber, ∃ D : ℕ, ∀ c ∈ l, g c ≤ D
  | [] => ⟨0, by simp⟩
  | a :: l => by
    obtain ⟨D, hD⟩ := exists_bound_list g l
    refine ⟨max D ⌈g a⌉₊, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    · exact (hD c hc).trans (by exact_mod_cast le_max_left _ _)

lemma exists_bound_cells (cells : ℕ → List Chamber) (g : ℕ → Chamber → ℝ) :
    ∀ N : ℕ, ∃ D : ℕ, ∀ L < N, ∀ c ∈ cells L, g L c ≤ D
  | 0 => ⟨0, by simp⟩
  | N + 1 => by
    obtain ⟨D, hD⟩ := exists_bound_cells cells g N
    obtain ⟨D', hD'⟩ := exists_bound_list (g N) (cells N)
    refine ⟨max D D', fun L hL c hc => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hL with hL | rfl
    · exact (hD L hL c hc).trans (by exact_mod_cast le_max_left _ _)
    · exact (hD' c hc).trans (by exact_mod_cast le_max_right _ _)

lemma list_ind_le {ι : Type*} (P : ι → Prop) [DecidablePred P] (g : ι → ℝ) (X : ℝ) (hX : 0 ≤ X) :
    ∀ l : List ι, l.Pairwise (fun a b => ¬ (P a ∧ P b)) → (∀ a ∈ l, P a → g a ≤ X) →
    (l.map (fun a => if P a then g a else 0)).sum ≤ X
  | [], _, _ => by simpa using hX
  | a :: l, hp, hg => by
    rw [List.pairwise_cons] at hp
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : P a
    · have h0 : (l.map (fun a => if P a then g a else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
        rw [ite_eq_right (fun hb' => hp.1 b hb ⟨ha, hb'⟩)]
      rw [ite_eq_left ha, h0, add_zero]; exact hg a (by simp) ha
    · rw [ite_eq_right ha, zero_add]
      exact list_ind_le P g X hX l hp.2 (fun b hb => hg b (by simp [hb]))

lemma finset_sum_list_sum {ι κ : Type*} (s : Finset κ) (g : κ → ι → ℝ) : ∀ l : List ι,
    ∑ q ∈ s, (l.map (fun x => g q x)).sum = (l.map (fun x => ∑ q ∈ s, g q x)).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, finset_sum_list_sum s g l]

/-! ### Valuation lower bounds for the content -/

lemma real_le_vcont {w : Fin 3 → ℚ} (hw : w ≠ 0) {q : ℕ} (hq : q.Prime) {r : ℝ}
    (h : ∀ i, w i ≠ 0 → r ≤ padicValRat q (w i)) : r ≤ padicValRat q (cont w) := by
  have := Fact.mk hq
  have := le_padicValRat_cont w hw ⌈r⌉ (fun i => by
    by_cases hi : w i = 0
    · exact Or.inl hi
    · exact Or.inr (Int.ceil_le.2 (h i hi)))
  calc r ≤ ⌈r⌉ := Int.le_ceil r
    _ ≤ _ := by exact_mod_cast this

lemma int_le_vcont {w : Fin 3 → ℚ} (hw : w ≠ 0) {q : ℕ} (hq : q.Prime) {k : ℤ}
    (h : ∀ i, VGe q k (w i)) : (k : ℝ) ≤ padicValRat q (cont w) := by
  have := Fact.mk hq
  exact_mod_cast le_padicValRat_cont w hw k h

/-! ### The prime ranges -/

/-- primes above `Qf P n` are `≥ P` and beyond `√(144 n + 24)` -/
def Qf (P n : ℕ) : ℕ := P + Nat.sqrt (144 * n + 24)

/-- `p` lies in the safe zone of the chamber `x = (L, c)` -/
def Pq (K n q : ℕ) (x : ℕ × Chamber) : Prop :=
  q % 6 = x.2.e ∧ ((x.1 : ℚ) + x.2.lo) * q + K ≤ n ∧ (n : ℚ) + K ≤ ((x.1 : ℚ) + x.2.hi) * q

instance (K n q : ℕ) : DecidablePred (Pq K n q) := fun x => by unfold Pq; infer_instance

/-- the large primes `Qf P n < q ≤ D n` -/
def Bset (P D n : ℕ) : Finset ℕ := (Finset.Ioc (Qf P n) (D * n)).filter Nat.Prime

/-- `θ` over the safe zone of a chamber -/
noncomputable def Sx (P K D n : ℕ) (x : ℕ × Chamber) : ℝ :=
  ∑ q ∈ (Bset P D n).filter (fun q => Pq K n q x), Real.log q

/-- `1/(L + x)`, with the value `D` at `L + x = 0` -/
noncomputable def Fv (D L : ℕ) (x : ℚ) : ℝ :=
  if (L : ℝ) + x = 0 then (D : ℝ) else 1 / ((L : ℝ) + x)

lemma Qf_big {P n q : ℕ} (hq : Qf P n < q) : P ≤ q ∧ 144 * n + 24 < q ^ 2 := by
  unfold Qf at hq
  refine ⟨by omega, ?_⟩
  have h1 := Nat.lt_succ_sqrt (144 * n + 24)
  have h2 : (144 * n + 24).sqrt.succ ≤ q := by omega
  calc 144 * n + 24 < _ := h1
    _ ≤ q * q := Nat.mul_le_mul h2 h2
    _ = q ^ 2 := (sq q).symm

lemma Qf_le {P n : ℕ} (hn : 1 ≤ n) : (Qf P n : ℝ) ≤ P + 13 * √n := by
  unfold Qf
  push_cast
  have h1 : ((144 * n + 24).sqrt : ℝ) ≤ √((144 * n + 24 : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
  have h2 : √(((144 * n + 24 : ℕ)) : ℝ) ≤ 13 * √n := by
    have h13 : (13 : ℝ) * √n = √(169 * n) := by
      rw [Real.sqrt_mul (by norm_num), show (169 : ℝ) = 13 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h13]
    apply Real.sqrt_le_sqrt
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  linarith

lemma Qf_ev (P L2 : ℕ) (hL2 : 1 ≤ L2) : ∀ᶠ n : ℕ in atTop, (Qf P n : ℝ) ≤ n / L2 := by
  have hl : (0 : ℝ) < L2 := by exact_mod_cast hL2
  filter_upwards [eventually_ge_atTop 1, small_sqrt (1 / (26 * L2)) (by positivity),
    ev_lin (1 / (2 * L2)) 0 P (by positivity)] with n hn h1 h2
  have h3 := Qf_le (P := P) hn
  have h4 : √(n : ℝ) ≤ 1 / (26 * L2) * n := (le_abs_self _).trans h1
  have h5 : (n : ℝ) / L2 = 1 / (2 * L2) * n + 0 + 13 * (1 / (26 * L2) * n) := by
    field_simp; ring
  linarith


/-- the (nonnegative) coefficient `max(m, -C') + C'` of a chamber -/
noncomputable def acoef (C' : ℕ) (y : ℕ × Chamber) : ℝ :=
  ((max y.2.m (-(C' : ℤ)) : ℤ) : ℝ) + C'

/-- the density weight `1/(L+lo) - 1/(L+hi)` of a chamber -/
noncomputable def Dl (D : ℕ) (y : ℕ × Chamber) : ℝ := Fv D y.1 y.2.lo - Fv D y.1 y.2.hi

/-- the prime sum over the safe zone of a chamber has the expected density -/
lemma Sx_LB (P K D L2 : ℕ) (hL2 : 1 ≤ L2) (hD1 : (1 : ℝ) ≤ D) (L : ℕ) (hL : L < L2)
    (c : Chamber) (he : c.e = 1 ∨ c.e = 5)
    (hb : (0 : ℝ) ≤ c.lo ∧ (c.lo : ℝ) < c.hi ∧ (c.hi : ℝ) ≤ 1)
    (hDlo : 1 / ((L : ℝ) + c.lo) ≤ D) :
    LB (fun n => Sx P K D n (L, c)) ((Fv D L c.lo - Fv D L c.hi) / 2) := by
  obtain ⟨hlo0, hlohi, hhi1⟩ := hb
  have hQev := Qf_ev P L2 hL2
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hLhi : (0 : ℝ) < L + c.hi := by linarith
  have hLL2 : (L : ℝ) + c.hi ≤ L2 := by
    have : (L : ℝ) + 1 ≤ L2 := by exact_mod_cast hL
    linarith
  have hFhi : Fv D L c.hi = 1 / ((L : ℝ) + c.hi) := by
    unfold Fv; rw [ite_eq_right hLhi.ne']
  set αv := Fv D L c.lo with hαv
  set βv : ℝ := if (L : ℝ) + c.lo = 0 then 0 else -((K : ℝ) / ((L : ℝ) + c.lo)) with hβv
  have hαvpos : 0 < αv := by
    rw [hαv]; unfold Fv
    split_ifs with h
    · linarith
    · have : 0 < (L : ℝ) + c.lo := lt_of_le_of_ne (by linarith) (Ne.symm h)
      positivity
  have hvD : ∀ n : ℕ, αv * n + βv ≤ D * n := by
    intro n
    rw [hαv, hβv]; unfold Fv
    split_ifs with h
    · simp
    · have hpos : 0 < (L : ℝ) + c.lo := lt_of_le_of_ne (by linarith) (Ne.symm h)
      have h1 := hDlo
      have h2 : 0 ≤ (K : ℝ) / ((L : ℝ) + c.lo) := by positivity
      have h3 : 1 / ((L : ℝ) + c.lo) * n ≤ D * n :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
      linarith
  have hthe := (LB_thetaE he hαvpos βv).add
    (LB_neg_thetaE he (by positivity : (0 : ℝ) < 1 / ((L : ℝ) + c.hi))
      ((K : ℝ) / ((L : ℝ) + c.hi)))
  refine hthe.mono (by rw [hFhi]; linarith) ?_
  filter_upwards [eventually_ge_atTop K, hQev] with n hnK hQn
  refine le_trans ?_ (le_trans (thetaE_sub_le c.e
    (1 / ((L : ℝ) + c.hi) * n + K / ((L : ℝ) + c.hi)) (αv * n + βv)) ?_)
  · linarith
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Real.log_natCast_nonneg _)
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
  obtain ⟨⟨hq1, hq2⟩, hqe, hqp⟩ := hq
  have hu0 : 0 ≤ 1 / ((L : ℝ) + c.hi) * n + K / ((L : ℝ) + c.hi) := by positivity
  have huq := (Nat.floor_lt hu0).1 hq1
  have hv0 : 0 ≤ αv * n + βv := by
    by_contra h
    push Not at h
    rw [Nat.floor_of_nonpos h.le] at hq2
    omega
  have hqv : (q : ℝ) ≤ αv * n + βv := (Nat.le_floor_iff hv0).1 hq2
  have hQu : (Qf P n : ℝ) ≤ 1 / ((L : ℝ) + c.hi) * n + K / ((L : ℝ) + c.hi) := by
    have h1 : (n : ℝ) / L2 ≤ n / ((L : ℝ) + c.hi) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hLhi hLL2
    have h2 : (n : ℝ) / ((L : ℝ) + c.hi) = 1 / ((L : ℝ) + c.hi) * n := by ring
    have h3 : 0 ≤ (K : ℝ) / ((L : ℝ) + c.hi) := by positivity
    linarith
  have hmemB : q ∈ Bset P D n := by
    unfold Bset
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hqp⟩
    · exact_mod_cast hQu.trans_lt huq
    · exact_mod_cast hqv.trans (hvD n)
  have hP1 : ((L : ℚ) + c.lo) * q + K ≤ n := by
    have : ((L : ℝ) + c.lo) * q + K ≤ n := by
      by_cases h0 : (L : ℝ) + c.lo = 0
      · rw [h0, zero_mul, zero_add]; exact_mod_cast hnK
      · have hpos : 0 < (L : ℝ) + c.lo := lt_of_le_of_ne (by linarith) (Ne.symm h0)
        have hv' : αv * n + βv = (n - K) / ((L : ℝ) + c.lo) := by
          rw [hαv, hβv]; unfold Fv; rw [ite_eq_right h0, ite_eq_right h0]
          field_simp; ring
        rw [hv', le_div_iff₀ hpos] at hqv
        linarith
    exact_mod_cast this
  have hP2 : (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * q := by
    have : (n : ℝ) + K ≤ ((L : ℝ) + c.hi) * q := by
      have hu' : 1 / ((L : ℝ) + c.hi) * n + K / ((L : ℝ) + c.hi) =
          (n + K) / ((L : ℝ) + c.hi) := by field_simp
      rw [hu', div_lt_iff₀ hLhi] at huq
      linarith
    exact_mod_cast this
  exact Finset.mem_filter.2 ⟨hmemB, hqe, hP1, hP2⟩

/-- the pointwise lower bound for `log cont(W n)` -/
lemma main_ineq (W : ℕ → Fin 3 → ℚ) (hw : ∀ n, W n ≠ 0) (cells : ℕ → List Chamber) (L2 : ℕ)
    (hL2 : 1 ≤ L2) (hzero : ∀ c ∈ cells 0, c.lo = 0 → c.m = 0) (γ : ℕ → ℕ → ℕ) (Cg : ℝ)
    (hCg : ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
      ∑ q ∈ S, (γ n q : ℝ) * Real.log q ≤ Cg * Real.log (n + 1))
    (C' P K D : ℕ) (hP5 : 5 ≤ P) (hK1n : 1 ≤ K) (hD1n : 1 ≤ D)
    (hcellU : ∀ L < L2, ∀ c ∈ cells L, ∀ n p : ℕ, p.Prime → P ≤ p → p % 6 = c.e →
      ((L : ℚ) + c.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * p →
      144 * n + 24 < p ^ 2 → ∀ i, VGe p (c.m - γ n p) (W n i))
    (hcrudeU : ∀ n p : ℕ, p.Prime → P ≤ p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (-(C' : ℤ) - γ n p) (W n i))
    (Cs C2 C3 : ℝ) (hCsnn : 0 ≤ Cs)
    (hCs : ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p → ∀ i, W n i ≠ 0 →
      -Cs * (Real.log n / Real.log p + 1) ≤ padicValRat p (W n i))
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∀ i, W n i ≠ 0 →
      12 * (n : ℝ) - C2 * Real.log n ≤ padicValRat 2 (W n i))
    (hC3 : ∀ n : ℕ, 2 ≤ n → ∀ i, W n i ≠ 0 →
      18 * (n : ℝ) - C3 * Real.log n ≤ padicValRat 3 (W n i))
    (hbdR : ∀ L < L2, ∀ c ∈ cells L, (0 : ℝ) ≤ c.lo ∧ (c.lo : ℝ) < c.hi ∧ (c.hi : ℝ) ≤ 1)
    (hDhi : ∀ c ∈ cells 0, 2 / (c.hi : ℝ) ≤ D)
    (hpw : (allc cells L2).Pairwise
      (fun x y => x.2.e ≠ y.2.e ∨ (x.1 : ℚ) + x.2.hi ≤ y.1 + y.2.lo))
    (hfirst : ∀ e, e = 1 ∨ e = 5 → ∃ c ∈ cells 0, c.e = e ∧ c.lo = 0) :
    ∀ᶠ n : ℕ in atTop,
    ((12 * n - C2 * Real.log n) * Real.log 2 + (18 * n - C3 * Real.log n) * Real.log 3) +
      (-(((Qf P n : ℝ) + 1) * (2 * Cs * Real.log n))) +
      (-(C' : ℝ) * (thetaE 1 (D * n + 0) + thetaE 5 (D * n + 0))) +
      ((allc cells L2).map (fun y => acoef C' y * Sx P K D n y)).sum +
      (-(Cg * Real.log (n + 1))) ≤ Real.log (cont (W n)) := by
  have hL2pos : 0 < L2 := hL2
  have hQev := Qf_ev P L2 hL2
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop K, hQev] with n hn2 hnK hQn
  have hn1 : 1 ≤ n := by omega
  have hL2r : (1 : ℝ) ≤ L2 := by exact_mod_cast hL2
  have hQn' : Qf P n ≤ n := by
    have : (n : ℝ) / L2 ≤ n := div_le_self (Nat.cast_nonneg _) hL2r
    exact_mod_cast hQn.trans this
  have hQ5 : 5 ≤ Qf P n := by unfold Qf; omega
  have hDn : n ≤ D * n := Nat.le_mul_of_pos_left n (by omega)
  have hK1 : (1 : ℚ) ≤ K := by exact_mod_cast hK1n
  set x := cont (W n) with hx
  have hxpos : 0 < x := cont_pos _ (hw n)
  set T := ((Finset.range (D * n + 1)).filter Nat.Prime ∪ x.num.natAbs.primeFactors) ∪
    x.den.primeFactors with hT
  have hTp : ∀ q ∈ T, q.Prime := by
    intro q hq
    simp only [hT, Finset.mem_union, Finset.mem_filter] at hq
    rcases hq with (hq | hq) | hq
    · exact hq.2
    · exact Nat.prime_of_mem_primeFactors hq
    · exact Nat.prime_of_mem_primeFactors hq
  have hlog := log_eq_sum_padicValRat x hxpos T hTp
    (fun q hq => Finset.mem_union_left _ (Finset.mem_union_right _ hq))
    (fun q hq => Finset.mem_union_right _ hq)
  rw [hlog]
  have hPT : ∀ q, q.Prime → q ≤ D * n → q ∈ T := by
    intro q hq hqD
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq⟩))
  have hB : (T.filter (fun q => ¬ q ≤ Qf P n)).filter (fun q => q ≤ D * n) = Bset P D n := by
    ext q
    simp only [Bset, Finset.mem_filter, Finset.mem_Ioc, not_le]
    constructor
    · rintro ⟨⟨hqT, hq1⟩, hq2⟩; exact ⟨⟨hq1, hq2⟩, hTp q hqT⟩
    · rintro ⟨⟨hq1, hq2⟩, hqp⟩; exact ⟨⟨hPT q hqp hq2, hq1⟩, hq2⟩
  have e1 := Finset.sum_filter_add_sum_filter_not T (fun q => q ≤ Qf P n)
    (fun q => (padicValRat q x : ℝ) * Real.log q)
  have e2 := Finset.sum_filter_add_sum_filter_not (T.filter (fun q => ¬ q ≤ Qf P n))
    (fun q => q ≤ D * n) (fun q => (padicValRat q x : ℝ) * Real.log q)
  rw [hB] at e2
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- (I) the primes `q ≤ Qf P n`
  have hI : (12 * n - C2 * Real.log n) * Real.log 2 + (18 * n - C3 * Real.log n) * Real.log 3 -
      ((Qf P n : ℝ) + 1) * (2 * Cs * Real.log n) ≤
      ∑ q ∈ T.filter (fun q => q ≤ Qf P n), (padicValRat q x : ℝ) * Real.log q := by
    have h2A : 2 ∈ T.filter (fun q => q ≤ Qf P n) :=
      Finset.mem_filter.2 ⟨hPT 2 Nat.prime_two (by omega), by omega⟩
    have h3A : 3 ∈ T.filter (fun q => q ≤ Qf P n) :=
      Finset.mem_filter.2 ⟨hPT 3 Nat.prime_three (by omega), by omega⟩
    have hφ : ∀ q ∈ T.filter (fun q => q ≤ Qf P n),
        (if q = 2 then (12 * n - C2 * Real.log n) * Real.log 2 else 0) +
        (if q = 3 then (18 * n - C3 * Real.log n) * Real.log 3 else 0) +
        (if 5 ≤ q then -(2 * Cs * Real.log n) else 0) ≤
          (padicValRat q x : ℝ) * Real.log q := by
      intro q hq
      obtain ⟨hqT, hqQ⟩ := Finset.mem_filter.1 hq
      have hqp := hTp q hqT
      by_cases hq2 : q = 2
      · subst hq2
        rw [ite_eq_left rfl, ite_eq_right (by norm_num), ite_eq_right (by norm_num),
          add_zero, add_zero]
        have := real_le_vcont (hw n) Nat.prime_two (fun i hi => hC2 n hn2 i hi)
        push_cast
        exact mul_le_mul_of_nonneg_right this (Real.log_nonneg (by norm_num))
      by_cases hq3 : q = 3
      · subst hq3
        rw [ite_eq_right (by norm_num), ite_eq_left rfl, ite_eq_right (by norm_num),
          zero_add, add_zero]
        have := real_le_vcont (hw n) Nat.prime_three (fun i hi => hC3 n hn2 i hi)
        push_cast
        exact mul_le_mul_of_nonneg_right this (Real.log_nonneg (by norm_num))
      have hq5 : 5 ≤ q := by
        have := hqp.two_le
        have h4 : q ≠ 4 := by rintro rfl; exact absurd hqp (by decide)
        omega
      rw [ite_eq_right hq2, ite_eq_right hq3, ite_eq_left hq5, zero_add, zero_add]
      have hv := real_le_vcont (hw n) hqp (fun i hi => hCs n q hn2 hqp hq5 i hi)
      have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
      have hlqn : Real.log q ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < q))
          (by exact_mod_cast (by omega : q ≤ n))
      have key : -Cs * (Real.log n / Real.log q + 1) * Real.log q =
          -Cs * (Real.log n + Real.log q) := by field_simp
      have := mul_le_mul_of_nonneg_right hv hlq.le
      rw [key] at this
      nlinarith
    have hsum := Finset.sum_le_sum hφ
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', ite_eq_left h2A, ite_eq_left h3A] at hsum
    have hcard : -(((Qf P n : ℝ) + 1) * (2 * Cs * Real.log n)) ≤
        ∑ q ∈ T.filter (fun q => q ≤ Qf P n),
          (if 5 ≤ q then -(2 * Cs * Real.log n) else 0) := by
      have h0 : 0 ≤ 2 * Cs * Real.log n := by positivity
      have hle : ∀ q ∈ T.filter (fun q => q ≤ Qf P n),
          -(2 * Cs * Real.log n) ≤ (if 5 ≤ q then -(2 * Cs * Real.log n) else 0) := by
        intro q _
        split_ifs
        · exact le_rfl
        · linarith
      have h1 := Finset.card_nsmul_le_sum _ _ _ hle
      rw [nsmul_eq_mul] at h1
      have hcardA : ((T.filter (fun q => q ≤ Qf P n)).card : ℝ) ≤ Qf P n + 1 := by
        have : (T.filter (fun q => q ≤ Qf P n)).card ≤ (Finset.range (Qf P n + 1)).card :=
          Finset.card_le_card (fun q hq => Finset.mem_range.2
            (by have := (Finset.mem_filter.1 hq).2; omega))
        rw [Finset.card_range] at this
        exact_mod_cast this
      nlinarith
    linarith
  -- (II) the primes `Qf P n < q ≤ D n`
  have hII : ∀ q ∈ Bset P D n, (-(C' : ℝ) + ((allc cells L2).map
      (fun y => if Pq K n q y then acoef C' y else 0)).sum - γ n q) * Real.log q ≤
        (padicValRat q x : ℝ) * Real.log q := by
    intro q hq
    simp only [Bset, Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨hqQ, hqD⟩, hqp⟩ := hq
    obtain ⟨hPq, hsq⟩ := Qf_big hqQ
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg q)
    have hcr : (-(C' : ℝ) - γ n q) ≤ padicValRat q x := by
      have := int_le_vcont (hw n) hqp (hcrudeU n q hqp hPq hsq)
      push_cast at this
      exact this
    have hind := list_ind_le (Pq K n q) (acoef C') ((padicValRat q x : ℝ) + C' + γ n q) (by linarith)
      (allc cells L2) ?_ ?_
    · linarith
    · refine hpw.imp ?_
      rintro y z hyz ⟨⟨hy1, hy2, hy3⟩, ⟨hz1, hz2, hz3⟩⟩
      rcases hyz with h | h
      · exact h (hy1.symm.trans hz1)
      · have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
        have := mul_le_mul_of_nonneg_right h hq0
        linarith
    · intro y hy hPy
      obtain ⟨hyL, hyc⟩ := mem_allc.1 hy
      have hc := int_le_vcont (hw n) hqp
        (hcellU y.1 hyL y.2 hyc n q hqp hPq hPy.1 hPy.2.1 hPy.2.2 hsq)
      push_cast at hc
      simp only [acoef]
      have : ((max y.2.m (-(C' : ℤ)) : ℤ) : ℝ) ≤ (padicValRat q x : ℝ) + γ n q := by
        push_cast
        exact max_le (by linarith) (by linarith)
      linarith
  have hIIsum := Finset.sum_le_sum hII
  have hIIeq : ∑ q ∈ Bset P D n, (-(C' : ℝ) + ((allc cells L2).map
      (fun y => if Pq K n q y then acoef C' y else 0)).sum - γ n q) * Real.log q =
      -(C' : ℝ) * ∑ q ∈ Bset P D n, Real.log q +
        ((allc cells L2).map (fun y => acoef C' y * Sx P K D n y)).sum -
        ∑ q ∈ Bset P D n, (γ n q : ℝ) * Real.log q := by
    have h1 : ∀ q ∈ Bset P D n, (-(C' : ℝ) + ((allc cells L2).map
        (fun y => if Pq K n q y then acoef C' y else 0)).sum - γ n q) * Real.log q =
        -(C' : ℝ) * Real.log q + ((allc cells L2).map
          (fun y => (if Pq K n q y then acoef C' y else 0) * Real.log q)).sum -
          (γ n q : ℝ) * Real.log q := by
      intro q _
      rw [List.sum_map_mul_right]; ring
    have h2 : ((allc cells L2).map (fun y => ∑ q ∈ Bset P D n,
        (if Pq K n q y then acoef C' y else 0) * Real.log q)).sum =
        ((allc cells L2).map (fun y => acoef C' y * Sx P K D n y)).sum := by
      apply congrArg
      apply List.map_congr_left
      intro y _
      simp only [Sx, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      finset_sum_list_sum, h2]
  have hV : ∑ q ∈ Bset P D n, Real.log q ≤ thetaE 1 (D * n + 0) + thetaE 5 (D * n + 0) := by
    have hfl : ⌊(D : ℝ) * n + 0⌋₊ = D * n := by
      rw [add_zero, ← Nat.cast_mul, Nat.floor_natCast]
    unfold thetaE
    rw [hfl, ← Finset.sum_filter_add_sum_filter_not (Bset P D n) (fun q => q % 6 = 1)]
    apply add_le_add
    · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Real.log_natCast_nonneg _)
      intro q hq
      simp only [Bset, Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
      exact ⟨⟨by omega, h2⟩, h4, h3⟩
    · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Real.log_natCast_nonneg _)
      intro q hq
      simp only [Bset, Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
      have := prime_mod_six h3 (by omega)
      exact ⟨⟨by omega, h2⟩, by omega, h3⟩
  -- (III) the primes `q > D n`
  have hIII : ∀ q ∈ (T.filter (fun q => ¬ q ≤ Qf P n)).filter (fun q => ¬ q ≤ D * n),
      -((γ n q : ℝ) * Real.log q) ≤ (padicValRat q x : ℝ) * Real.log q := by
    intro q hq
    simp only [Finset.mem_filter, not_le] at hq
    obtain ⟨⟨hqT, hqQ⟩, hqD⟩ := hq
    have hqp := hTp q hqT
    obtain ⟨hPq, hsq⟩ := Qf_big hqQ
    have he6 := prime_mod_six hqp (by omega)
    obtain ⟨c0, hc0, hc0e, hc0lo⟩ := hfirst (q % 6) he6
    obtain ⟨hlo0, hlohi, hhi1⟩ := hbdR 0 hL2pos c0 hc0
    have hhiD := hDhi c0 hc0
    have hVG := hcellU 0 hL2pos c0 hc0 n q hqp hPq hc0e.symm ?_ ?_ hsq
    · have := int_le_vcont (hw n) hqp hVG
      rw [hzero c0 hc0 hc0lo] at this
      push_cast at this
      have hl := Real.log_natCast_nonneg q
      nlinarith
    · rw [hc0lo]
      simpa using (by exact_mod_cast hnK : (K : ℚ) ≤ n)
    · have hhipos : (0 : ℝ) < c0.hi := by
        have : ((c0.lo : ℚ) : ℝ) = 0 := by rw [hc0lo]; simp
        linarith
      have h1 : (2 : ℝ) ≤ D * c0.hi := by
        rw [div_le_iff₀ hhipos] at hhiD
        linarith
      have h2 : (D : ℝ) * n + 1 ≤ q := by
        have : D * n + 1 ≤ q := hqD
        exact_mod_cast this
      have h3 : (n : ℝ) + K ≤ c0.hi * q := by
        have hKn : (K : ℝ) ≤ n := by exact_mod_cast hnK
        have h4 : (c0.hi : ℝ) * (D * n + 1) ≤ c0.hi * q :=
          mul_le_mul_of_nonneg_left h2 hhipos.le
        have h5 : (2 : ℝ) * n ≤ D * c0.hi * n :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
        nlinarith
      have : ((n : ℚ) + K ≤ c0.hi * q) := by exact_mod_cast h3
      simpa using this
  have hIIIsum := Finset.sum_le_sum hIII
  rw [Finset.sum_neg_distrib] at hIIIsum
  -- (IV) the losses
  have hdisj : Disjoint (Bset P D n)
      ((T.filter (fun q => ¬ q ≤ Qf P n)).filter (fun q => ¬ q ≤ D * n)) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    simp only [Bset, Finset.mem_filter, Finset.mem_Ioc, not_le] at h1 h2
    obtain ⟨⟨_, h1⟩, _⟩ := h1
    obtain ⟨_, h2⟩ := h2
    omega
  have hIV := hCg n hn1 (Bset P D n ∪
      (T.filter (fun q => ¬ q ≤ Qf P n)).filter (fun q => ¬ q ≤ D * n)) (by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact (Finset.mem_filter.1 h).2
    · exact hTp q (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1)
  rw [Finset.sum_union hdisj] at hIV
  have hC'V := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg (α := ℝ) C')
  linarith

/-- the constant: `chamberDensity - C'/L2` is dominated by the density of the lower bound -/
lemma const_ineq (cells : ℕ → List Chamber) (L2 : ℕ) (hL2 : 1 ≤ L2)
    (hzero : ∀ c ∈ cells 0, c.lo = 0 → c.m = 0) (C' D : ℕ)
    (hbdR : ∀ L < L2, ∀ c ∈ cells L, (0 : ℝ) ≤ c.lo ∧ (c.lo : ℝ) < c.hi ∧ (c.hi : ℝ) ≤ 1)
    (htel : ∀ L < L2, ∀ F : ℚ → ℝ,
      ((cells L).map (fun c => F c.lo - F c.hi)).sum = 2 * (F 0 - F 1)) :
    chamberDensity cells L2 - C' / L2 ≤
      -((C' : ℝ) * D) + ((allc cells L2).map (fun y => acoef C' y * (Dl D y / 2))).sum := by
  have hL2pos : 0 < L2 := hL2
  have hsplit : ((allc cells L2).map (fun y => acoef C' y * (Dl D y / 2))).sum =
      ((allc cells L2).map (fun y => ((max y.2.m (-(C' : ℤ)) : ℤ) : ℝ) * (Dl D y / 2))).sum +
        (C' : ℝ) / 2 * ((allc cells L2).map (Dl D)).sum := by
    rw [← List.sum_map_mul_left, ← List.sum_map_add]
    apply congrArg
    apply List.map_congr_left
    intro y _
    simp only [acoef]; ring
  have hΔsum : ((allc cells L2).map (Dl D)).sum = 2 * ((D : ℝ) - 1 / L2) := by
    rw [allc_sum]
    have h1 : ∀ L ∈ Finset.range L2, ((cells L).map (fun c => Dl D (L, c))).sum =
        2 * (Fv D L 0 - Fv D (L + 1) 0) := by
      intro L hL
      have := htel L (Finset.mem_range.1 hL) (Fv D L)
      simp only [Dl]
      rw [this]
      have e1 : Fv D L 1 = Fv D (L + 1) 0 := by
        unfold Fv
        have : (L : ℝ) + ((1 : ℚ) : ℝ) ≠ 0 := by push_cast; positivity
        have h' : ((L + 1 : ℕ) : ℝ) + ((0 : ℚ) : ℝ) ≠ 0 := by push_cast; positivity
        rw [ite_eq_right this, ite_eq_right h']
        push_cast; ring
      rw [e1]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_range_sub' (fun L => Fv D L 0)]
    have e0 : Fv D 0 0 = D := by unfold Fv; simp
    have eL : Fv D L2 0 = 1 / L2 := by
      unfold Fv
      have : (L2 : ℝ) + ((0 : ℚ) : ℝ) ≠ 0 := by push_cast; positivity
      rw [ite_eq_right this]; push_cast; ring
    rw [e0, eL]
  have hdens : chamberDensity cells L2 ≤
      ((allc cells L2).map (fun y => ((max y.2.m (-(C' : ℤ)) : ℤ) : ℝ) * (Dl D y / 2))).sum := by
    rw [allc_sum, chamberDensity]
    apply Finset.sum_le_sum
    intro L hL
    have hL' := Finset.mem_range.1 hL
    apply List.sum_le_sum
    intro c hc
    obtain ⟨hlo0, hlohi, hhi1⟩ := hbdR L hL' c hc
    simp only [Dl]
    split_ifs with h0
    · obtain ⟨rfl, hlo⟩ := h0
      rw [hzero c hc hlo]
      have : max (0 : ℤ) (-(C' : ℤ)) = 0 := max_eq_left (by omega)
      rw [this]; simp
    · have hpos : 0 < (L : ℝ) + c.lo := by
        rcases Nat.eq_zero_or_pos L with hL0 | hL0
        · subst hL0
          have : c.lo ≠ 0 := fun h => h0 ⟨rfl, h⟩
          have : (0 : ℝ) < c.lo := lt_of_le_of_ne hlo0 (by exact_mod_cast this.symm)
          simpa using this
        · have : (1 : ℝ) ≤ L := by exact_mod_cast hL0
          linarith
      have hpos2 : 0 < (L : ℝ) + c.hi := by linarith
      have e1 : Fv D L c.lo = 1 / ((L : ℝ) + c.lo) := by unfold Fv; rw [ite_eq_right hpos.ne']
      have e2 : Fv D L c.hi = 1 / ((L : ℝ) + c.hi) := by unfold Fv; rw [ite_eq_right hpos2.ne']
      rw [e1, e2]
      have hd : 0 ≤ 1 / ((L : ℝ) + c.lo) - 1 / ((L : ℝ) + c.hi) := by
        have := one_div_le_one_div_of_le hpos (by linarith : (L : ℝ) + c.lo ≤ L + c.hi)
        linarith
      have hm : (c.m : ℝ) ≤ ((max c.m (-(C' : ℤ)) : ℤ) : ℝ) := by
        exact_mod_cast le_max_left c.m (-(C' : ℤ))
      nlinarith
  rw [hsplit, hΔsum]
  have hL2r : (0 : ℝ) < L2 := by exact_mod_cast hL2pos
  have : (C' : ℝ) / 2 * (2 * ((D : ℝ) - 1 / L2)) = C' * D - C' / L2 := by field_simp
  linarith

/-! ### The summation theorem for an abstract vector sequence -/

theorem content_rate_gen (W : ℕ → Fin 3 → ℚ) (cells : ℕ → List Chamber) (L2 : ℕ) (hL2 : 1 ≤ L2)
    (hcov : ∀ L < L2, ChainCover (cells L) 1 ∧ ChainCover (cells L) 5)
    (he : ∀ L < L2, ∀ c ∈ cells L, c.e = 1 ∨ c.e = 5)
    (hzero : ∀ c ∈ cells 0, c.lo = 0 → c.m = 0)
    (γ : ℕ → ℕ → ℕ)
    (hγ : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
      ∑ q ∈ S, (γ n q : ℝ) * Real.log q ≤ C * Real.log (n + 1))
    (hcell : ∀ L < L2, ∀ c ∈ cells L, ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = c.e →
      ((L : ℚ) + c.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (c.m - γ n p) (W n i))
    (C' : ℕ) (hcrude : ∃ P0 : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (-(C' : ℤ) - γ n p) (W n i))
    (hsmall : ∃ C : ℝ, ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p → ∀ i, W n i ≠ 0 →
      -C * (Real.log n / Real.log p + 1) ≤ padicValRat p (W n i))
    (h2 : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, W n i ≠ 0 →
      12 * (n : ℝ) - C * Real.log n ≤ padicValRat 2 (W n i))
    (h3 : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, W n i ≠ 0 →
      18 * (n : ℝ) - C * Real.log n ≤ padicValRat 3 (W n i))
    (hw : ∀ n, W n ≠ 0) :
    LB (fun n => Real.log (cont (W n)))
      (12 * Real.log 2 + 18 * Real.log 3 + chamberDensity cells L2 - C' / L2) := by
  obtain ⟨C2, hC2⟩ := h2
  obtain ⟨C3, hC3⟩ := h3
  obtain ⟨Cs0, hCs0⟩ := hsmall
  obtain ⟨Cg, hCg⟩ := hγ
  obtain ⟨Pc, hPc⟩ := hcrude
  set Cs := max Cs0 0 with hCs_def
  have hCsnn : 0 ≤ Cs := le_max_right _ _
  have hCs : ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p → ∀ i, W n i ≠ 0 →
      -Cs * (Real.log n / Real.log p + 1) ≤ padicValRat p (W n i) := by
    intro n p hn hp hp5 i hi
    refine le_trans ?_ (hCs0 n p hn hp hp5 i hi)
    have : 0 ≤ Real.log n / Real.log p + 1 := by
      have := Real.log_natCast_nonneg n; have := Real.log_natCast_nonneg p; positivity
    nlinarith [le_max_left Cs0 0]
  have hL2pos : 0 < L2 := hL2
  -- chamber facts
  obtain ⟨hbd, hpw, htel, hfirst⟩ := cells_facts cells L2 hcov he
  -- uniform constants
  have hcell2 : ∀ L c, ∃ P0 K : ℕ, L < L2 → c ∈ cells L → ∀ n p : ℕ, p.Prime → P0 ≤ p →
      p % 6 = c.e → ((L : ℚ) + c.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * p →
      144 * n + 24 < p ^ 2 → ∀ i, VGe p (c.m - γ n p) (W n i) := by
    intro L c
    by_cases h : L < L2 ∧ c ∈ cells L
    · obtain ⟨P0, K, hK⟩ := hcell L h.1 c h.2; exact ⟨P0, K, fun _ _ => hK⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose P0f Kf hPK using hcell2
  obtain ⟨Pb, hPb⟩ := exists_bound_cells cells (fun L c => (P0f L c : ℝ)) L2
  obtain ⟨Kb, hKb⟩ := exists_bound_cells cells (fun L c => (Kf L c : ℝ)) L2
  obtain ⟨Db, hDb⟩ := exists_bound_cells cells
    (fun L c => 1 / ((L : ℝ) + c.lo) + 2 / ((L : ℝ) + c.hi)) L2
  set P : ℕ := Pb + Pc + 5 with hP
  set K : ℕ := Kb + 1 with hK
  set D : ℕ := Db + 1 with hD
  have hcellU : ∀ L < L2, ∀ c ∈ cells L, ∀ n p : ℕ, p.Prime → P ≤ p → p % 6 = c.e →
      ((L : ℚ) + c.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * p →
      144 * n + 24 < p ^ 2 → ∀ i, VGe p (c.m - γ n p) (W n i) := by
    intro L hL c hc n p hp hPp hpe h1 h2 h3 i
    have hP0 : P0f L c ≤ Pb := by exact_mod_cast hPb L hL c hc
    have hK0 : (Kf L c : ℚ) ≤ K := by
      have : Kf L c ≤ Kb := by exact_mod_cast hKb L hL c hc
      exact_mod_cast (by omega : Kf L c ≤ Kb + 1)
    exact hPK L c hL hc n p hp (by omega) hpe (by linarith) (by linarith) h3 i
  have hcrudeU : ∀ n p : ℕ, p.Prime → P ≤ p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (-(C' : ℤ) - γ n p) (W n i) := fun n p hp hPp => hPc n p hp (by omega)
  have hD1 : (1 : ℝ) ≤ D := by
    have : (0 : ℝ) ≤ Db := Nat.cast_nonneg Db
    rw [hD]; push_cast; linarith
  have hbdR : ∀ L < L2, ∀ c ∈ cells L,
      (0 : ℝ) ≤ c.lo ∧ (c.lo : ℝ) < c.hi ∧ (c.hi : ℝ) ≤ 1 := by
    intro L hL c hc
    obtain ⟨h1, h2, h3⟩ := hbd L hL c hc
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  have hDlohi : ∀ L < L2, ∀ c ∈ cells L,
      1 / ((L : ℝ) + c.lo) ≤ D ∧ 2 / ((L : ℝ) + c.hi) ≤ D := by
    intro L hL c hc
    obtain ⟨h1, h2, h3⟩ := hbdR L hL c hc
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hb := hDb L hL c hc
    have hDb' : (Db : ℝ) ≤ D := by rw [hD]; push_cast; linarith
    have ha : 0 ≤ 1 / ((L : ℝ) + c.lo) := by
      have : (0 : ℝ) ≤ L + c.lo := by linarith
      positivity
    have hb' : 0 ≤ 2 / ((L : ℝ) + c.hi) := by
      have : (0 : ℝ) ≤ L + c.hi := by linarith
      positivity
    constructor <;> linarith
  have hann : ∀ y, 0 ≤ acoef C' y := by
    intro y
    simp only [acoef]
    have : (-(C' : ℝ)) ≤ ((max y.2.m (-(C' : ℤ)) : ℤ) : ℝ) := by
      have := le_max_right y.2.m (-(C' : ℤ))
      exact_mod_cast this
    linarith
  have hDhi : ∀ c ∈ cells 0, 2 / (c.hi : ℝ) ≤ D := by
    intro c hc
    have := (hDlohi 0 hL2pos c hc).2
    simpa using this
  have hmain := main_ineq W hw cells L2 hL2 hzero γ Cg hCg C' P K D (by omega) (by omega)
    (by omega) hcellU hcrudeU Cs C2 C3 hCsnn hCs hC2 hC3 hbdR hDhi hpw (hfirst hL2pos)
  -- the rates of the five pieces
  have hf1 : LB (fun n : ℕ => ((12 * n - C2 * Real.log n) * Real.log 2 +
      (18 * n - C3 * Real.log n) * Real.log 3)) (12 * Real.log 2 + 18 * Real.log 3) := by
    refine ((LB_lin (12 * Real.log 2 + 18 * Real.log 3)).add
      (small_log (-(C2 * Real.log 2 + C3 * Real.log 3))).lb).mono (by simp) ?_
    filter_upwards with n
    apply le_of_eq; ring
  have hf2 : LB (fun n : ℕ => -(((Qf P n : ℝ) + 1) * (2 * Cs * Real.log n))) 0 := by
    refine Small.lb (Small.mono ((small_log (2 * Cs * (P + 1))).add (small_sqrt_log (26 * Cs))) ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hq := Qf_le (P := P) hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hs : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hQ0 : (0 : ℝ) ≤ Qf P n := Nat.cast_nonneg _
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    have h0 : 0 ≤ ((Qf P n : ℝ) + 1) * (2 * Cs * Real.log n) := by positivity
    have h1 : 0 ≤ 2 * Cs * (P + 1) * Real.log n + 26 * Cs * (√n * Real.log n) := by positivity
    rw [abs_neg, abs_of_nonneg h0, abs_of_nonneg h1]
    have : ((Qf P n : ℝ) + 1) * (2 * Cs * Real.log n) ≤
        ((P : ℝ) + 13 * √n + 1) * (2 * Cs * Real.log n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hf3 : LB (fun n : ℕ => -(C' : ℝ) * (thetaE 1 (D * n + 0) + thetaE 5 (D * n + 0)))
      (C' * (-((D : ℝ) / 2)) + C' * (-((D : ℝ) / 2))) := by
    have hDpos : (0 : ℝ) < D := by linarith
    refine ((LB.const_mul (C' : ℝ) (Nat.cast_nonneg _) (LB_neg_thetaE (Or.inl rfl) hDpos 0)).add
      (LB.const_mul (C' : ℝ) (Nat.cast_nonneg _) (LB_neg_thetaE (Or.inr rfl) hDpos 0))).mono
      le_rfl ?_
    filter_upwards with n
    apply le_of_eq; ring
  have hS : ∀ y ∈ allc cells L2, LB (fun n => Sx P K D n y) (Dl D y / 2) := by
    rintro ⟨L, c⟩ hy
    obtain ⟨hL, hc⟩ := mem_allc.1 hy
    exact Sx_LB P K D L2 hL2 hD1 L hL c (he L hL c hc) (hbdR L hL c hc) (hDlohi L hL c hc).1
  have hf4 : LB (fun n => ((allc cells L2).map (fun y => acoef C' y * Sx P K D n y)).sum)
      ((allc cells L2).map (fun y => acoef C' y * (Dl D y / 2))).sum :=
    LB.list_sum (fun y n => acoef C' y * Sx P K D n y) (fun y => acoef C' y * (Dl D y / 2))
      (allc cells L2) (fun y hy => LB.const_mul (acoef C' y) (hann y) (hS y hy))
  have hf5 : LB (fun n : ℕ => -(Cg * Real.log (n + 1))) 0 :=
    Small.lb (by simpa using (small_log_succ (-Cg)))
  have htot := ((((hf1.add hf2).add hf3).add hf4).add hf5)
  refine htot.mono ?_ hmain
  have := const_ineq cells L2 hL2 hzero C' D hbdR htel
  linarith

theorem content_rate (cells : ℕ → List Chamber) (L2 : ℕ) (hL2 : 1 ≤ L2)
    (hcov : ∀ L < L2, ChainCover (cells L) 1 ∧ ChainCover (cells L) 5)
    (he : ∀ L < L2, ∀ c ∈ cells L, c.e = 1 ∨ c.e = 5)
    (hzero : ∀ c ∈ cells 0, c.lo = 0 → c.m = 0)
    (γ : ℕ → ℕ → ℕ)
    (hγ : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
      ∑ q ∈ S, (γ n q : ℝ) * Real.log q ≤ C * Real.log (n + 1))
    (hcell : ∀ L < L2, ∀ c ∈ cells L, ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = c.e →
      ((L : ℚ) + c.lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + c.hi) * p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (c.m - γ n p) (w n i))
    (C' : ℕ) (hcrude : ∃ P0 : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → 144 * n + 24 < p ^ 2 →
      ∀ i, VGe p (-(C' : ℤ) - γ n p) (w n i))
    (hsmall : ∃ C : ℝ, ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p → ∀ i, w n i ≠ 0 →
      -C * (Real.log n / Real.log p + 1) ≤ padicValRat p (w n i))
    (h2 : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, w n i ≠ 0 → 12 * (n : ℝ) - C * Real.log n ≤ padicValRat 2 (w n i))
    (h3 : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, w n i ≠ 0 → 18 * (n : ℝ) - C * Real.log n ≤ padicValRat 3 (w n i))
    (hw : ∀ n, w n ≠ 0) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (12 * Real.log 2 + 18 * Real.log 3 + chamberDensity cells L2 - C' / L2 - ε) * n
        ≤ Real.log (cont (w n)) :=
  content_rate_gen w cells L2 hL2 hcov he hzero γ hγ hcell C' hcrude hsmall h2 h3 hw

end Zeta2L2Chi3.Arith

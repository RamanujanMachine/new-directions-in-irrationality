/-
# Exponential rates for the series state and for `B̂`

Gauge-normalizing the recurrence `y(n+1) = -y(n) Q(n)` produces `z(m+1) = z(m) A(m+1)` with
`A(n) → T`; the spectral data of `T` (a tiny real eigenvalue `r ≤ rh` and a complex pair of
modulus `√c ≤ Rh`) together with the dichotomy give
* `|S n k| ≲ (s∞ rh)^n` (`decay_rate`), using the crude bound `|S n k| ≤ 2 (40n+12) 16^n`;
* `|B̂ n i j| ≲ (s∞ Rh)^n` (`growth_rate`).
-/
import Zeta2L2Chi3.Gauge
import Zeta2L2Chi3.Dichotomy
import Zeta2L2Chi3.CrudeBound
import Zeta2L2Chi3.DualTransport

noncomputable section

namespace Zeta2L2Chi3

open Filter Topology Matrix Real

/-! ### Exponential rates -/

/-- `|f m| ≤ K μ^m` eventually, for every `μ > L`. -/
def RateLe (f : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ μ > L, ∃ K, ∀ᶠ m in atTop, |f m| ≤ K * μ ^ m

lemma RateLe.mono {f : ℕ → ℝ} {L L' : ℝ} (h : RateLe f L) (hL : L ≤ L') : RateLe f L' :=
  fun μ hμ => h μ (lt_of_le_of_lt hL hμ)

lemma RateLe.of_le {f g : ℕ → ℝ} {L : ℝ} (h : RateLe g L) (hfg : ∀ᶠ m in atTop, |f m| ≤ |g m|) :
    RateLe f L := by
  intro μ hμ
  obtain ⟨K, hK⟩ := h μ hμ
  exact ⟨K, (hK.and hfg).mono fun m hm => hm.2.trans hm.1⟩

lemma RateLe.mul {f g : ℕ → ℝ} {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hf : RateLe f L₁) (hg : RateLe g L₂) : RateLe (fun m => f m * g m) (L₁ * L₂) := by
  intro μ hμ
  set δ := min 1 ((μ - L₁ * L₂) / (L₁ + L₂ + 1)) with hδ
  have hpos : 0 < (μ - L₁ * L₂) / (L₁ + L₂ + 1) := div_pos (by linarith) (by linarith)
  have hδ0 : 0 < δ := lt_min one_pos hpos
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ (μ - L₁ * L₂) / (L₁ + L₂ + 1) := min_le_right _ _
  have hδ3 : δ * (L₁ + L₂ + 1) ≤ μ - L₁ * L₂ := by
    rwa [le_div_iff₀ (by linarith)] at hδ2
  obtain ⟨K₁, hK₁⟩ := hf (L₁ + δ) (by linarith)
  obtain ⟨K₂, hK₂⟩ := hg (L₂ + δ) (by linarith)
  have hprod : (L₁ + δ) * (L₂ + δ) ≤ μ := by nlinarith
  refine ⟨|K₁ * K₂|, (hK₁.and hK₂).mono fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := hm
  have e0 : 0 ≤ K₁ * (L₁ + δ) ^ m := (abs_nonneg _).trans h1
  have e1 : |f m * g m| ≤ K₁ * (L₁ + δ) ^ m * (K₂ * (L₂ + δ) ^ m) := by
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) e0
  have e2 : ((L₁ + δ) * (L₂ + δ)) ^ m ≤ μ ^ m :=
    pow_le_pow_left₀ (by positivity) hprod m
  have e3 : K₁ * (L₁ + δ) ^ m * (K₂ * (L₂ + δ) ^ m) = (K₁ * K₂) * ((L₁ + δ) * (L₂ + δ)) ^ m := by
    rw [mul_pow]; ring
  have e4 : (K₁ * K₂) * ((L₁ + δ) * (L₂ + δ)) ^ m ≤ |K₁ * K₂| * ((L₁ + δ) * (L₂ + δ)) ^ m :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have e5 := mul_le_mul_of_nonneg_left e2 (abs_nonneg (K₁ * K₂))
  linarith

lemma RateLe.of_succ {f : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : RateLe (fun m => f (m + 1)) L) :
    RateLe f L := by
  intro μ hμ
  have hμ0 : 0 < μ := lt_of_le_of_lt hL hμ
  obtain ⟨K, hK⟩ := h μ hμ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hK
  refine ⟨K / μ, eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hN m (by omega)
  calc |f (m + 1)| ≤ K * μ ^ m := this
    _ = K / μ * μ ^ (m + 1) := by rw [pow_succ]; field_simp

lemma RateLe.sq_succ : RateLe (fun m => ((m : ℝ) + 1) ^ 2) 1 := by
  intro μ hμ
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 2 hμ).comp (tendsto_add_atTop_nat 1)
  refine ⟨μ, (h.eventually (eventually_le_nhds one_pos)).mono fun m hm => ?_⟩
  simp only [Function.comp_apply] at hm
  have hp : 0 < μ ^ (m + 1) := pow_pos (by linarith) _
  rw [div_le_iff₀ hp, one_mul] at hm
  push_cast at hm
  rw [abs_of_nonneg (by positivity), ← pow_succ']
  exact hm

lemma RateLe.of_geom {f : ℕ → ℝ} {L : ℝ}
    (h : ∀ ε > 0, ∃ K, ∀ m, |f m| ≤ K * (L + ε) ^ m) : RateLe f L := by
  intro μ hμ
  obtain ⟨K, hK⟩ := h (μ - L) (by linarith)
  exact ⟨K, Eventually.of_forall fun m => by simpa using hK m⟩

lemma RateLe.exp_bound {f : ℕ → ℝ} {L : ℝ} (hL : 0 < L) (h : RateLe f L) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |f n| ≤ Real.exp ((Real.log L + ε) * n) := by
  intro ε hε
  set μ := L * Real.exp (ε / 2) with hμ
  have hμL : L < μ := by
    rw [hμ]; exact lt_mul_of_one_lt_right hL (Real.one_lt_exp_iff.2 (by linarith))
  obtain ⟨K, hK⟩ := h μ hμL
  have ht : Tendsto (fun n : ℕ => Real.exp (ε / 2 * n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith))
  refine (hK.and (ht.eventually (eventually_ge_atTop K))).mono fun n hn => ?_
  obtain ⟨h1, h2⟩ := hn
  have hlogμ : Real.log μ = Real.log L + ε / 2 := by
    rw [hμ, Real.log_mul hL.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hμn : μ ^ n = Real.exp ((Real.log L + ε / 2) * n) := by
    rw [← hlogμ, mul_comm, Real.exp_nat_mul, Real.exp_log (by linarith)]
  have e : Real.exp ((Real.log L + ε) * n) =
      Real.exp (ε / 2 * n) * Real.exp ((Real.log L + ε / 2) * n) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← hμn]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))


/-! ### Spectral data of the limit matrix -/

def rl : ℝ := 325999287587431764 / 10 ^ 46
def rh : ℝ := 325999287587431765 / 10 ^ 46
def Rh : ℝ := 32723294395333 / 10 ^ 14

def cq1 : ℚ := -162060225797/305977695940
def cq2 : ℚ := 40100849267287098349209/374489401651004369934400
def cq3 : ℚ := -25/7161587766945221818712445059146

/-- the real limit matrix -/
def Treal : Matrix (Fin 3) (Fin 3) ℝ := Tlim.map (fun x : ℚ => (x : ℝ))

lemma Tlim_cubic : Tlim * Tlim * Tlim + cq1 • (Tlim * Tlim) + cq2 • Tlim +
    cq3 • (1 : Matrix (Fin 3) (Fin 3) ℚ) = 0 := by
  decide +kernel

lemma Treal_cubic : Treal * Treal * Treal + (cq1 : ℝ) • (Treal * Treal) + (cq2 : ℝ) • Treal +
    (cq3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  ext i j
  have h := congrFun (congrFun Tlim_cubic i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.zero_apply, smul_eq_mul] at h ⊢
  simp only [Treal, Matrix.map_apply, Matrix.one_apply]
  have h' := congrArg (fun x : ℚ => (x : ℝ)) h
  simp only [Matrix.one_apply] at h'
  push_cast at h'
  convert h' using 2; split_ifs <;> simp

lemma cubic_root : ∃ r : ℝ, rl ≤ r ∧ r ≤ rh ∧
    r ^ 3 + (cq1 : ℝ) * r ^ 2 + (cq2 : ℝ) * r + (cq3 : ℝ) = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + (cq1 : ℝ) * x ^ 2 + (cq2 : ℝ) * x + (cq3 : ℝ))
      (Set.Icc rl rh) := by fun_prop
  have hle : rl ≤ rh := by norm_num [rl, rh]
  have h0 : (0 : ℝ) ∈ Set.Icc (rl ^ 3 + (cq1 : ℝ) * rl ^ 2 + (cq2 : ℝ) * rl + (cq3 : ℝ))
      (rh ^ 3 + (cq1 : ℝ) * rh ^ 2 + (cq2 : ℝ) * rh + (cq3 : ℝ)) := by
    constructor <;> norm_num [rl, rh, cq1, cq2, cq3]
  obtain ⟨r, ⟨h1, h2⟩, h3⟩ := intermediate_value_Icc hle hc h0
  exact ⟨r, h1, h2, h3⟩

/-- spectral data of the limit matrix -/
theorem spectral : ∃ r b c : ℝ, b ^ 2 < 4 * c ∧ r ^ 2 < c ∧
    (Treal - r • 1) * (Treal * Treal + b • Treal + c • 1) = 0 ∧
    0 < r ∧ r ≤ rh ∧ 3 / 10 < Real.sqrt c ∧ Real.sqrt c ≤ Rh := by
  obtain ⟨r, hr1, hr2, hr3⟩ := cubic_root
  have hrl : (0 : ℝ) < rl := by norm_num [rl]
  have hrh : rh ≤ 1 / 10 ^ 20 := by norm_num [rh]
  have hc1 : (cq1 : ℝ) = -162060225797/305977695940 := by norm_num [cq1]
  have hc2 : (cq2 : ℝ) = 40100849267287098349209/374489401651004369934400 := by norm_num [cq2]
  have hc3 : (cq3 : ℝ) = -(cq2 : ℝ) * r - (cq1 : ℝ) * r ^ 2 - r ^ 3 := by linarith
  set b := (cq1 : ℝ) + r with hb
  set c := (cq2 : ℝ) + r * b with hc
  have hr0 : 0 < r := lt_of_lt_of_le hrl hr1
  have hrs : r ≤ 1 / 10 ^ 20 := hr2.trans hrh
  have hcl : 9 / 100 < c := by rw [hc, hb, hc1, hc2]; nlinarith
  have hcu : c ≤ Rh ^ 2 := by
    have e1 : c ≤ (cq2 : ℝ) + (cq1 : ℝ) * rl + rh ^ 2 := by
      rw [hc, hb, hc1]
      rw [hc1] at *
      nlinarith
    refine e1.trans ?_
    rw [hc1, hc2]; norm_num [rl, rh, Rh]
  refine ⟨r, b, c, ?_, ?_, ?_, hr0, hr2, ?_, ?_⟩
  · rw [hc, hb, hc1, hc2]; nlinarith
  · nlinarith
  · have e : (Treal - r • 1) * (Treal * Treal + b • Treal + c • 1) =
        Treal * Treal * Treal + (cq1 : ℝ) • (Treal * Treal) + (cq2 : ℝ) • Treal +
          (cq3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [hc3, hc, hb]
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      module
    rw [e, Treal_cubic]
  · rw [show (3 / 10 : ℝ) = Real.sqrt ((3 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)
  · rw [show Rh = Real.sqrt (Rh ^ 2) by rw [Real.sqrt_sq (by norm_num [Rh])]]
    exact Real.sqrt_le_sqrt hcu


/-! ### Positivity of `Q₀₀` -/

lemma hornerR_nonneg_of_nonneg (l : List ℤ) (h : ∀ c ∈ l, 0 ≤ c) (x : ℚ) (hx : 0 ≤ x) :
    0 ≤ hornerR l x := by
  induction l with
  | nil => simp [hornerR]
  | cons c cs ih =>
    have hc : (0 : ℚ) ≤ c := by exact_mod_cast h c (by simp)
    have := ih fun d hd => h d (by simp [hd])
    simp only [hornerR]
    positivity

lemma hornerR_pos_of_pos (l : List ℤ) (hl : 0 < l.length) (h : ∀ c ∈ l, 0 < c) (x : ℚ)
    (hx : 0 ≤ x) : 0 < hornerR l x := by
  cases l with
  | nil => simp at hl
  | cons c cs =>
    have hc : (0 : ℚ) < c := by exact_mod_cast h c (by simp)
    have := hornerR_nonneg_of_nonneg cs (fun d hd => (h d (by simp [hd])).le) x hx
    simp only [hornerR]
    positivity

lemma Qnum00_pos : 0 < (Data.Qnum 0 0).length ∧ ∀ c ∈ Data.Qnum 0 0, 0 < c := by
  decide +kernel

lemma Q00_pos (n : ℕ) : 0 < ((Q n 0 0 : ℚ) : ℝ) := by
  have h1 := hornerR_pos_of_pos _ Qnum00_pos.1 Qnum00_pos.2 (n : ℚ) (by positivity)
  have h2 := Qden_pos (n : ℚ) (by positivity)
  have : 0 < Q n 0 0 := div_pos h1 h2
  exact_mod_cast this

/-! ### The normalized sequence -/

/-- `∏_{j<m} Q₀₀(j+1)` -/
def Pq (m : ℕ) : ℝ := ∏ j ∈ Finset.range m, ((Q (j + 1) 0 0 : ℚ) : ℝ)

lemma Pq_pos (m : ℕ) : 0 < Pq m := Finset.prod_pos fun j _ => Q00_pos (j + 1)

lemma Pq_succ (m : ℕ) : Pq (m + 1) = Pq m * ((Q (m + 1) 0 0 : ℚ) : ℝ) :=
  Finset.prod_range_succ _ _

/-- the gauge-normalized vector attached to a solution `y` -/
def znorm (y : ℕ → Fin 3 → ℝ) (m : ℕ) : Fin 3 → ℝ :=
  fun i => (-1) ^ m / Pq m * (y (m + 1) i / ((m : ℝ) + 1) ^ (i : ℕ))

lemma znorm_succ (y : ℕ → Fin 3 → ℝ)
    (hy : ∀ n j, y (n + 1) j = -∑ l : Fin 3, y n l * ((Q n l j : ℚ) : ℝ)) (m : ℕ) :
    znorm y (m + 1) = znorm y m ᵥ* Anorm (m + 1) := by
  ext i
  have hP := (Pq_pos m).ne'
  have hQ := (Q00_pos (m + 1)).ne'
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
  simp only [znorm, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Anorm, Pq_succ]
  rw [hy (m + 1) i]
  simp only [Fin.sum_univ_three]
  push_cast
  field_simp
  ring

lemma y_le_znorm (y : ℕ → Fin 3 → ℝ) (m : ℕ) (i : Fin 3) :
    |y (m + 1) i| ≤ Pq m * ((m : ℝ) + 1) ^ 2 * ‖znorm y m‖ := by
  have hP := Pq_pos m
  have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hpi : 0 < ((m : ℝ) + 1) ^ (i : ℕ) := by positivity
  have e : y (m + 1) i = (-1) ^ m * Pq m * ((m : ℝ) + 1) ^ (i : ℕ) * znorm y m i := by
    simp only [znorm]
    field_simp
    have h2 : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h2, mul_one]
  have hz := norm_le_pi_norm (znorm y m) i
  rw [Real.norm_eq_abs] at hz
  have hi : ((m : ℝ) + 1) ^ (i : ℕ) ≤ ((m : ℝ) + 1) ^ 2 :=
    pow_le_pow_right₀ h1 (by omega)
  rw [e, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hP, abs_of_pos hpi]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hi hP.le) hz (abs_nonneg _) (by positivity)

lemma rate_Pq : RateLe Pq ((sInf : ℚ) : ℝ) := by
  intro μ hμ
  have hμ0 : 0 < μ := lt_trans (by norm_num [sInf]) hμ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_Q00.eventually (eventually_le_nhds hμ))
  obtain ⟨K, hK⟩ := dich_geom Pq Pq μ hμ0 N (fun n => (Pq_pos n).le) (fun n _ => le_rfl)
    (fun n hn => by
      rw [Pq_succ, mul_comm μ]
      exact mul_le_mul_of_nonneg_left (hN (n + 1) (by omega)) (Pq_pos n).le)
  exact ⟨K, Eventually.of_forall fun m => by rw [abs_of_pos (Pq_pos m)]; exact hK m⟩

lemma rate_of_znorm (y : ℕ → Fin 3 → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (h : ∀ ε > 0, ∃ K, ∀ m, ‖znorm y m‖ ≤ K * (lam + ε) ^ m) (i : Fin 3) :
    RateLe (fun n => y n i) (((sInf : ℚ) : ℝ) * lam) := by
  have hs : (0 : ℝ) ≤ ((sInf : ℚ) : ℝ) := by norm_num [sInf]
  have hz : RateLe (fun m => ‖znorm y m‖) lam :=
    RateLe.of_geom fun ε hε => by
      obtain ⟨K, hK⟩ := h ε hε
      exact ⟨K, fun m => by rw [abs_norm]; exact hK m⟩
  have h1 := (rate_Pq.mul hs zero_le_one RateLe.sq_succ).mul (by positivity) hlam hz
  rw [mul_one] at h1
  refine RateLe.of_succ (by positivity) (h1.of_le (Eventually.of_forall fun m => ?_))
  exact (y_le_znorm y m i).trans (le_abs_self _)

lemma tendsto_Anorm_succ : Tendsto (fun n => Anorm (n + 1)) atTop (𝓝 Treal) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  exact (tendsto_Anorm i j).comp (tendsto_add_atTop_nat 1)

/-! ### The series state: decay -/

/-- the series state as a vector sequence -/
def ySer (n : ℕ) : Fin 3 → ℝ := fun k => S n k

lemma ySer_succ (n : ℕ) (j : Fin 3) :
    ySer (n + 1) j = -∑ l : Fin 3, ySer n l * ((Q n l j : ℚ) : ℝ) := by
  simp only [ySer, S_succ, Qk_cast]

lemma znorm_ySer_crude : ∃ K₀, ∀ m, ‖znorm ySer m‖ ≤ K₀ * (64 / ((sInf : ℚ) : ℝ)) ^ m := by
  have hs : ((sInf : ℚ) : ℝ) = 156660580321280 := by norm_num [sInf]
  set u : ℕ → ℝ := fun m => 2 * (40 * ((m : ℝ) + 1) + 12) * 16 ^ (m + 1) / Pq m with hu
  have hle : ∀ m, ‖znorm ySer m‖ ≤ u m := by
    intro m
    have hP := Pq_pos m
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ (i : ℕ) :=
      one_le_pow₀ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
    have hS := abs_S_le (m + 1) i (by omega) (by omega)
    push_cast at hS
    simp only [znorm, ySer]
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hP, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) ^ (i : ℕ))]
    rw [hu]
    have h2 : |S (m + 1) ↑i| / ((m : ℝ) + 1) ^ (i : ℕ) ≤ |S (m + 1) ↑i| :=
      div_le_self (abs_nonneg _) h1
    calc 1 / Pq m * (|S (m + 1) ↑i| / ((m : ℝ) + 1) ^ (i : ℕ)) ≤ 1 / Pq m * |S (m + 1) ↑i| :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 1 / Pq m * (2 * (40 * ((m : ℝ) + 1) + 12) * 16 ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by ring
  have hsp : (0 : ℝ) < ((sInf : ℚ) : ℝ) / 2 := by rw [hs]; norm_num
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_Q00.eventually (eventually_ge_nhds
    (half_lt_self (by rw [hs]; norm_num : (0 : ℝ) < ((sInf : ℚ) : ℝ)))))
  refine dich_geom u (fun m => ‖znorm ySer m‖) _ (by rw [hs]; norm_num) N (fun n => norm_nonneg _)
    (fun n _ => hle n) fun n hn => ?_
  have hq := hN (n + 1) (by omega)
  have hP := Pq_pos n
  have hq0 : 0 < ((Q (n + 1) 0 0 : ℚ) : ℝ) := Q00_pos (n + 1)
  simp only [hu, Pq_succ]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have key : 2 * (40 * ((n : ℝ) + 1 + 1) + 12) * 16 ^ (n + 1 + 1) * ((sInf : ℚ) : ℝ) ≤
      64 * (2 * (40 * ((n : ℝ) + 1) + 12) * 16 ^ (n + 1)) * ((Q (n + 1) 0 0 : ℚ) : ℝ) := by
    have hpow : (16 : ℝ) ^ (n + 1 + 1) = 16 * 16 ^ (n + 1) := by ring
    rw [hpow]
    have h16 : (0 : ℝ) < 16 ^ (n + 1) := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsq : ((sInf : ℚ) : ℝ) ≤ 2 * ((Q (n + 1) 0 0 : ℚ) : ℝ) := by linarith
    have e1 : (40 * ((n : ℝ) + 1 + 1) + 12) ≤ 2 * (40 * ((n : ℝ) + 1) + 12) := by linarith
    have hsi : 0 ≤ ((sInf : ℚ) : ℝ) := by rw [hs]; norm_num
    calc 2 * (40 * ((n : ℝ) + 1 + 1) + 12) * (16 * 16 ^ (n + 1)) * ((sInf : ℚ) : ℝ)
        ≤ 2 * (2 * (40 * ((n : ℝ) + 1) + 12)) * (16 * 16 ^ (n + 1)) * ((sInf : ℚ) : ℝ) := by
          gcongr
      _ ≤ 2 * (2 * (40 * ((n : ℝ) + 1) + 12)) * (16 * 16 ^ (n + 1)) *
            (2 * ((Q (n + 1) 0 0 : ℚ) : ℝ)) := by gcongr
      _ = _ := by ring
  have hsi : 0 < ((sInf : ℚ) : ℝ) := by rw [hs]; norm_num
  rw [show ∀ B : ℝ, 64 / ((sInf : ℚ) : ℝ) * (B / Pq n) * (Pq n * ((Q (n + 1) 0 0 : ℚ) : ℝ)) =
      64 * B * ((Q (n + 1) 0 0 : ℚ) : ℝ) / ((sInf : ℚ) : ℝ) from fun B => by field_simp,
    le_div_iff₀ hsi]
  linarith

theorem decay_rate : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : Fin 3,
    |S n k| ≤ Real.exp ((Real.log (156660580321280 * rh) + ε) * n) := by
  intro ε hε
  have hs : ((sInf : ℚ) : ℝ) = 156660580321280 := by norm_num [sInf]
  obtain ⟨r, b, c, hbc, hrc, hT, hr0, hrh, hc3, -⟩ := spectral
  obtain ⟨K₀, hK₀⟩ := znorm_ySer_crude
  have hρ : 64 / ((sInf : ℚ) : ℝ) < Real.sqrt c := lt_trans (by rw [hs]; norm_num) hc3
  have hdec := dichotomy_decay Treal r b c hbc hT hrc (fun n => Anorm (n + 1)) tendsto_Anorm_succ
    (znorm ySer) (znorm_succ ySer ySer_succ) _ K₀ hρ hK₀
  rw [abs_of_pos hr0] at hdec
  have hL : (0 : ℝ) < 156660580321280 * rh := by norm_num [rh]
  refine eventually_all.2 fun k => ?_
  have h := ((rate_of_znorm ySer r hr0.le hdec k).mono
    (mul_le_mul_of_nonneg_left hrh (by rw [hs]; norm_num))).exp_bound (by rwa [hs]) ε hε
  rw [hs] at h
  exact h

/-! ### The rows of `B̂`: growth -/

/-- the `i`-th row of `B̂ n`, as a real vector -/
def yRow (i : Fin 3) (n : ℕ) : Fin 3 → ℝ := fun j => ((Bhat n i j : ℚ) : ℝ)

lemma yRow_succ (i : Fin 3) (n : ℕ) (j : Fin 3) :
    yRow i (n + 1) j = -∑ l : Fin 3, yRow i n l * ((Q n l j : ℚ) : ℝ) := by
  simp only [yRow, Bhat, Matrix.neg_apply, Matrix.mul_apply]
  push_cast
  ring

theorem growth_rate : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i j : Fin 3,
    |((Bhat n i j : ℚ) : ℝ)| ≤ Real.exp ((Real.log (156660580321280 * Rh) + ε) * n) := by
  intro ε hε
  have hs : ((sInf : ℚ) : ℝ) = 156660580321280 := by norm_num [sInf]
  obtain ⟨r, b, c, hbc, hrc, hT, -, -, -, hcR⟩ := spectral
  have hL : (0 : ℝ) < 156660580321280 * Rh := by norm_num [Rh]
  refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
  have hup := dichotomy_upper Treal r b c hbc hT hrc (fun n => Anorm (n + 1)) tendsto_Anorm_succ
    (znorm (yRow i)) (znorm_succ (yRow i) (yRow_succ i))
  have h := ((rate_of_znorm (yRow i) (Real.sqrt c) (Real.sqrt_nonneg _) hup j).mono
    (mul_le_mul_of_nonneg_left hcR (by rw [hs]; norm_num))).exp_bound (by rwa [hs]) ε hε
  rw [hs] at h
  exact h

end Zeta2L2Chi3

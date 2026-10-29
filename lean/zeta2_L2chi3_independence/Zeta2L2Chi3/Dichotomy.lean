import Mathlib

/-!
# An abstract dichotomy for perturbations of a fixed 3×3 matrix

`T` has spectrum `{r} ∪ {complex pair of modulus √c}`, encoded by
`(T - r) (T² + bT + c) = 0` with `b² < 4c` and `r² < c`.
-/

noncomputable section

namespace Zeta2L2Chi3

open Filter Topology Matrix

section Algebra

variable (T : Matrix (Fin 3) (Fin 3) ℝ) (r b c : ℝ)

/-- The quadratic factor `T² + bT + c`. -/
def dichQuad : Matrix (Fin 3) (Fin 3) ℝ := T * T + b • T + c • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- The projection onto the `r`-eigenline (acting on the right). -/
def dichPr : Matrix (Fin 3) (Fin 3) ℝ := (r ^ 2 + b * r + c)⁻¹ • dichQuad T b c

/-- The complementary projection. -/
def dichPq : Matrix (Fin 3) (Fin 3) ℝ := 1 - dichPr T r b c

variable {T r b c}

lemma dichQuad_pos (hbc : b ^ 2 < 4 * c) : 0 < r ^ 2 + b * r + c := by
  nlinarith [sq_nonneg (2 * r + b)]

lemma dich_T_mul_quad (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) :
    T * dichQuad T b c = r • dichQuad T b c := by
  have h := hT
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

lemma dich_quad_mul_T : dichQuad T b c * T = T * dichQuad T b c := by
  simp only [dichQuad, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]

lemma dich_quad_mul_quad (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) :
    dichQuad T b c * dichQuad T b c = (r ^ 2 + b * r + c) • dichQuad T b c := by
  have h := dich_T_mul_quad hT
  have e : dichQuad T b c * dichQuad T b c =
      T * (T * dichQuad T b c) + b • (T * dichQuad T b c) + c • dichQuad T b c := by
    nth_rewrite 1 [dichQuad]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [e, h, Matrix.mul_smul, h]
  module

lemma dich_T_mul_Pr (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) :
    T * dichPr T r b c = r • dichPr T r b c := by
  rw [dichPr, Matrix.mul_smul, dich_T_mul_quad hT, smul_comm]

lemma dich_Pr_mul_T (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) :
    dichPr T r b c * T = r • dichPr T r b c := by
  rw [dichPr, Matrix.smul_mul, dich_quad_mul_T, dich_T_mul_quad hT, smul_comm]

lemma dich_T_mul_Pq (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) :
    T * dichPq T r b c = dichPq T r b c * T := by
  rw [dichPq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    dich_T_mul_Pr hT, dich_Pr_mul_T hT]

lemma dich_Pq_mul_quad (hbc : b ^ 2 < 4 * c)
    (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) :
    dichPq T r b c * dichQuad T b c = 0 := by
  rw [dichPq, Matrix.sub_mul, Matrix.one_mul, dichPr, Matrix.smul_mul, dich_quad_mul_quad hT,
    smul_smul, inv_mul_cancel₀ (dichQuad_pos hbc).ne', one_smul, sub_self]

lemma dich_Pr_add_Pq : dichPr T r b c + dichPq T r b c = 1 := by
  rw [dichPq]; abel

end Algebra

section GMap

variable (T : Matrix (Fin 3) (Fin 3) ℝ) (b c : ℝ)

/-- The linear map whose Euclidean norm realizes `√Φ`. -/
def dichG : (Fin 3 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 ⊕ Fin 3) where
  toFun v := WithLp.toLp 2 (Sum.elim (v ᵥ* T + (b / 2) • v) (Real.sqrt (c - b ^ 2 / 4) • v))
  map_add' v w := by
    ext i
    rcases i with i | i
    · simp [Matrix.add_vecMul]; ring
    · simp [Matrix.add_vecMul]
  map_smul' a v := by
    ext i
    rcases i with i | i <;> simp [Matrix.smul_vecMul] <;> ring

variable {T b c}

lemma dichG_norm_sq (hbc : b ^ 2 < 4 * c) (v : Fin 3 → ℝ) :
    ‖dichG T b c v‖ ^ 2 = ∑ i, ((v ᵥ* T) i + b / 2 * v i) ^ 2 +
      (c - b ^ 2 / 4) * ∑ i, (v i) ^ 2 := by
  have hd : 0 ≤ c - b ^ 2 / 4 := by linarith
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type, Finset.mul_sum]
  simp [dichG, mul_pow, Real.sq_sqrt hd]

lemma dichG_scale (hbc : b ^ 2 < 4 * c) (p : Fin 3 → ℝ) (hp : p ᵥ* dichQuad T b c = 0) :
    ‖dichG T b c (p ᵥ* T)‖ = Real.sqrt c * ‖dichG T b c p‖ := by
  have hc : 0 ≤ c := by nlinarith [sq_nonneg b]
  have hw : ∀ i, (p ᵥ* T ᵥ* T) i = -b * (p ᵥ* T) i - c * p i := by
    intro i
    have := congrFun hp i
    simp only [dichQuad, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one,
      ← Matrix.vecMul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linarith
  have hsq : ‖dichG T b c (p ᵥ* T)‖ ^ 2 = c * ‖dichG T b c p‖ ^ 2 := by
    rw [dichG_norm_sq hbc, dichG_norm_sq hbc]
    simp only [Fin.sum_univ_three, hw]
    ring
  rw [← Real.sqrt_sq (norm_nonneg (dichG T b c (p ᵥ* T))), hsq, Real.sqrt_mul hc,
    Real.sqrt_sq (norm_nonneg _)]

lemma dichG_lower (hbc : b ^ 2 < 4 * c) (v : Fin 3 → ℝ) :
    ‖v‖ ≤ ‖dichG T b c v‖ / Real.sqrt (c - b ^ 2 / 4) := by
  have hd : 0 < c - b ^ 2 / 4 := by linarith
  have hs : 0 < Real.sqrt (c - b ^ 2 / 4) := Real.sqrt_pos.2 hd
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀ hs]
  have h := PiLp.norm_apply_le (dichG T b c v) (Sum.inr i)
  have e : (dichG T b c v) (Sum.inr i) = Real.sqrt (c - b ^ 2 / 4) * v i := by
    simp [dichG]
  rw [e, norm_mul, Real.norm_of_nonneg hs.le] at h
  linarith

end GMap

section Sequences

/-- Eventually geometric decay transfers to a global bound after enlarging the constant. -/
lemma dich_geom (x y : ℕ → ℝ) (μ : ℝ) (hμ : 0 < μ) (n₀ : ℕ) (hy : ∀ n, 0 ≤ y n)
    (hxy : ∀ n ≥ n₀, y n ≤ x n) (h : ∀ n ≥ n₀, x (n + 1) ≤ μ * x n) :
    ∃ K, ∀ n, y n ≤ K * μ ^ n := by
  have hx0 : 0 ≤ x n₀ := (hy n₀).trans (hxy n₀ le_rfl)
  have claim : ∀ k, x (n₀ + k) ≤ μ ^ k * x n₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x (n₀ + (k + 1)) = x (n₀ + k + 1) := by rw [Nat.add_assoc]
        _ ≤ μ * x (n₀ + k) := h _ (Nat.le_add_right _ _)
        _ ≤ μ * (μ ^ k * x n₀) := mul_le_mul_of_nonneg_left ih hμ.le
        _ = μ ^ (k + 1) * x n₀ := by ring
  set S := ∑ m ∈ Finset.range (n₀ + 1), y m / μ ^ m with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => div_nonneg (hy m) (pow_pos hμ m).le
  refine ⟨S + x n₀ / μ ^ n₀, fun n => ?_⟩
  have hxμ : 0 ≤ x n₀ / μ ^ n₀ := div_nonneg hx0 (pow_pos hμ _).le
  rcases le_or_gt n n₀ with hn | hn
  · have h1 : y n / μ ^ n ≤ S :=
      Finset.single_le_sum (f := fun m => y m / μ ^ m)
        (fun m _ => div_nonneg (hy m) (pow_pos hμ m).le) (Finset.mem_range.2 (by omega))
    have h2 : y n / μ ^ n ≤ S + x n₀ / μ ^ n₀ := by linarith
    rwa [div_le_iff₀ (pow_pos hμ n)] at h2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn.le
    have e : μ ^ k * x n₀ = x n₀ / μ ^ n₀ * μ ^ (n₀ + k) := by
      rw [pow_add]; field_simp
    calc y (n₀ + k) ≤ x (n₀ + k) := hxy _ (Nat.le_add_right _ _)
      _ ≤ μ ^ k * x n₀ := claim k
      _ = x n₀ / μ ^ n₀ * μ ^ (n₀ + k) := e
      _ ≤ (S + x n₀ / μ ^ n₀) * μ ^ (n₀ + k) :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_pos hμ _).le

lemma dich_seq_upper (a g δ : ℕ → ℝ) (s t : ℝ) (ht : 0 ≤ t) (hts : t ≤ s)
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (hδ : Tendsto δ atTop (𝓝 0))
    (h1 : ∀ n, a (n + 1) ≤ t * a n + δ n * (a n + g n))
    (h2 : ∀ n, g (n + 1) ≤ s * g n + δ n * (a n + g n)) :
    ∀ ε > 0, ∃ K, ∀ n, a n + g n ≤ K * (s + ε) ^ n := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hδ.eventually (eventually_le_nhds (half_pos hε)))
  refine dich_geom (fun n => a n + g n) (fun n => a n + g n) (s + ε) (by linarith) n₀
    (fun n => add_nonneg (ha n) (hg n)) (fun n _ => le_rfl) fun n hn => ?_
  have hN := add_nonneg (ha n) (hg n)
  have e1 := mul_le_mul_of_nonneg_right (hn₀ n hn) hN
  have e2 := mul_le_mul_of_nonneg_right hts (ha n)
  have e3 := h1 n
  have e4 := h2 n
  linarith

lemma dich_seq_decay (a g δ : ℕ → ℝ) (s t : ℝ) (ht : 0 ≤ t) (hts : t < s)
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (hδ : Tendsto δ atTop (𝓝 0))
    (h1 : ∀ n, a (n + 1) ≤ t * a n + δ n * (a n + g n))
    (h3 : ∀ n, s * g n - δ n * (a n + g n) ≤ g (n + 1))
    (ρ K₁ : ℝ) (hρ : ρ < s) (hb : ∀ n, a n + g n ≤ K₁ * ρ ^ n) :
    ∀ ε > 0, ∃ K, ∀ n, a n + g n ≤ K * (t + ε) ^ n := by
  intro ε hε
  set η := min (ε / 2) (min ((s - t) / 4) ((s - ρ) / 4)) with hη
  have hη0 : 0 < η := lt_min (half_pos hε) (lt_min (by linarith) (by linarith))
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ (s - t) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ (s - ρ) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hδ.eventually (eventually_le_nhds hη0))
  set l := s - 2 * η with hl
  have hl0 : 0 < l := by linarith
  have hlρ : ρ < l := by linarith
  -- one step inside the cone `a ≤ g`
  have step : ∀ n ≥ n₀, a n ≤ g n → a (n + 1) ≤ g (n + 1) ∧ l * g n ≤ g (n + 1) := by
    intro n hn hag
    have hN := add_nonneg (ha n) (hg n)
    have e1 := mul_le_mul_of_nonneg_right (hn₀ n hn) hN
    have e2 := h1 n
    have e3 := h3 n
    have e4 := mul_le_mul_of_nonneg_left hag hη0.le
    have e6 := mul_le_mul_of_nonneg_left hag ht
    have e7 := mul_le_mul_of_nonneg_right hη2 (hg n)
    constructor
    · linarith
    · linarith
  have cone : ∀ n ≥ n₀, a n ≤ g n → ∀ k, a (n + k) ≤ g (n + k) ∧ l ^ k * g n ≤ g (n + k) := by
    intro n hn hag k
    induction k with
    | zero => simp [hag]
    | succ k ih =>
      obtain ⟨h1', h2'⟩ := step (n + k) (by omega) ih.1
      refine ⟨h1', ?_⟩
      calc l ^ (k + 1) * g n = l * (l ^ k * g n) := by ring
        _ ≤ l * g (n + k) := mul_le_mul_of_nonneg_left ih.2 hl0.le
        _ ≤ g (n + k + 1) := h2'
  have hK₁ : 0 ≤ K₁ := by
    have h0 := hb 0
    rw [pow_zero, mul_one] at h0
    linarith [ha 0, hg 0]
  have excl : ∀ n ≥ n₀, g n ≤ a n := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have hgpos : 0 < g n := lt_of_le_of_lt (ha n) hcon
    have hc := cone n hn hcon.le
    have hbd : ∀ k, l ^ k * g n ≤ K₁ * ρ ^ (n + k) := fun k =>
      (hc k).2.trans ((le_add_of_nonneg_left (ha _)).trans (hb _))
    rcases lt_or_ge ρ 0 with hρ0 | hρ0
    · have hodd : ρ ^ (n + (n + 1)) < 0 := Odd.pow_neg ⟨n, by ring⟩ hρ0
      have f1 := hbd (n + 1)
      have f2 : K₁ * ρ ^ (n + (n + 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK₁ hodd.le
      have f3 : 0 < l ^ (n + 1) * g n := mul_pos (pow_pos hl0 _) hgpos
      linarith
    · have hlim : Tendsto (fun k : ℕ => K₁ * ρ ^ n * (ρ / l) ^ k) atTop
          (𝓝 (K₁ * ρ ^ n * 0)) :=
        tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ0 hl0.le)
          ((div_lt_one hl0).2 hlρ))
      have hle : ∀ k, g n ≤ K₁ * ρ ^ n * (ρ / l) ^ k := by
        intro k
        rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hl0 k), mul_assoc, ← pow_add,
          mul_comm]
        exact hbd k
      have f := ge_of_tendsto' hlim hle
      rw [mul_zero] at f
      linarith
  refine dich_geom (fun n => 2 * a n) (fun n => a n + g n) (t + ε) (by linarith) n₀
    (fun n => add_nonneg (ha n) (hg n)) (fun n hn => by linarith [excl n hn])
    fun n hn => ?_
  have hN := add_nonneg (ha n) (hg n)
  have e1 := mul_le_mul_of_nonneg_right (hn₀ n hn) hN
  have e2 := h1 n
  have e3 := excl n hn
  have e4 := mul_le_mul_of_nonneg_left e3 hη0.le
  have e5 := mul_le_mul_of_nonneg_right hη1 (ha n)
  linarith

end Sequences

section Main

/-- A crude operator bound for `z ↦ z ᵥ* M` in the sup norm. -/
def dichGam (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, |M i j|

lemma dichGam_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ dichGam M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma dich_vecMul_le (z : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖z ᵥ* M‖ ≤ dichGam M * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (dichGam_nonneg M) (norm_nonneg _))).2
    fun j => ?_
  rw [Real.norm_eq_abs]
  calc |(z ᵥ* M) j| = |∑ i, z i * M i j| := by simp [Matrix.vecMul, dotProduct]
    _ ≤ ∑ i, |z i * M i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖z‖ * ∑ j', |M i j'| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        have hz := norm_le_pi_norm z i
        rw [Real.norm_eq_abs] at hz
        exact mul_le_mul hz (Finset.single_le_sum (f := fun j' => |M i j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) (abs_nonneg _) (norm_nonneg _)
    _ = dichGam M * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]; rfl

lemma dichGam_tendsto {T : Matrix (Fin 3) (Fin 3) ℝ} {A : ℕ → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Tendsto A atTop (𝓝 T)) : Tendsto (fun n => dichGam (A n - T)) atTop (𝓝 0) := by
  have hc : Continuous dichGam :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem i j).abs
  have h := (hc.tendsto (T - T)).comp (hA.sub tendsto_const_nhds)
  have h0 : dichGam (T - T) = 0 := by simp [dichGam]
  rw [h0] at h
  exact h

variable (T : Matrix (Fin 3) (Fin 3) ℝ) (r b c : ℝ)

/-- The `r`-component size. -/
def dichA (v : Fin 3 → ℝ) : ℝ := ‖v ᵥ* dichPr T r b c‖

/-- The size `√Φ` of the oscillating component. -/
def dichGn (v : Fin 3 → ℝ) : ℝ := ‖dichG T b c (v ᵥ* dichPq T r b c)‖

/-- Upper equivalence constant. -/
def dichα : ℝ := dichGam (dichPr T r b c) +
  ‖LinearMap.toContinuousLinearMap (dichG T b c)‖ * dichGam (dichPq T r b c)

/-- Lower equivalence constant. -/
def dichβ : ℝ := 1 + 1 / Real.sqrt (c - b ^ 2 / 4)

variable {T r b c}

lemma dichα_nonneg : 0 ≤ dichα T r b c :=
  add_nonneg (dichGam_nonneg _) (mul_nonneg (norm_nonneg _) (dichGam_nonneg _))

lemma dichβ_nonneg : 0 ≤ dichβ b c := by
  unfold dichβ
  have := Real.sqrt_nonneg (c - b ^ 2 / 4)
  positivity

lemma dich_norm_le (hbc : b ^ 2 < 4 * c) (v : Fin 3 → ℝ) :
    ‖v‖ ≤ dichβ b c * (dichA T r b c v + dichGn T r b c v) := by
  have hsplit : v ᵥ* dichPr T r b c + v ᵥ* dichPq T r b c = v := by
    rw [← Matrix.vecMul_add, dich_Pr_add_Pq, Matrix.vecMul_one]
  have h1 : ‖v‖ ≤ ‖v ᵥ* dichPr T r b c‖ + ‖v ᵥ* dichPq T r b c‖ := by
    calc ‖v‖ = ‖v ᵥ* dichPr T r b c + v ᵥ* dichPq T r b c‖ := by rw [hsplit]
      _ ≤ _ := norm_add_le _ _
  have h2 := dichG_lower (T := T) hbc (v ᵥ* dichPq T r b c)
  set k := 1 / Real.sqrt (c - b ^ 2 / 4) with hk
  have hk0 : 0 ≤ k := by rw [hk]; have := Real.sqrt_nonneg (c - b ^ 2 / 4); positivity
  have h3 : ‖dichG T b c (v ᵥ* dichPq T r b c)‖ / Real.sqrt (c - b ^ 2 / 4) =
      k * dichGn T r b c v := by
    rw [hk, dichGn]; ring
  have ha0 : 0 ≤ dichA T r b c v := norm_nonneg _
  have h4 := mul_nonneg hk0 ha0
  have hg0 : 0 ≤ dichGn T r b c v := norm_nonneg _
  unfold dichβ
  rw [← hk]
  unfold dichA at *
  linarith

lemma dich_norm_ge (v : Fin 3 → ℝ) :
    dichA T r b c v + dichGn T r b c v ≤ dichα T r b c * ‖v‖ := by
  have h1 := dich_vecMul_le v (dichPr T r b c)
  have h2 := (LinearMap.toContinuousLinearMap (dichG T b c)).le_opNorm (v ᵥ* dichPq T r b c)
  rw [LinearMap.coe_toContinuousLinearMap'] at h2
  have h3 := mul_le_mul_of_nonneg_left (dich_vecMul_le v (dichPq T r b c))
    (norm_nonneg (LinearMap.toContinuousLinearMap (dichG T b c)))
  unfold dichA dichGn dichα
  linarith

lemma dich_step (hbc : b ^ 2 < 4 * c) (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0)
    (v : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    dichA T r b c (v ᵥ* M) ≤ |r| * dichA T r b c v +
        dichα T r b c * dichGam (M - T) * dichβ b c *
          (dichA T r b c v + dichGn T r b c v) ∧
      dichGn T r b c (v ᵥ* M) ≤ Real.sqrt c * dichGn T r b c v +
        dichα T r b c * dichGam (M - T) * dichβ b c *
          (dichA T r b c v + dichGn T r b c v) ∧
      Real.sqrt c * dichGn T r b c v - dichα T r b c * dichGam (M - T) * dichβ b c *
          (dichA T r b c v + dichGn T r b c v) ≤ dichGn T r b c (v ᵥ* M) := by
  set e := v ᵥ* (M - T) with he
  have hw : v ᵥ* M = v ᵥ* T + e := by rw [he, ← Matrix.vecMul_add, add_sub_cancel]
  -- size of the error
  have hE : dichA T r b c e + dichGn T r b c e ≤
      dichα T r b c * dichGam (M - T) * dichβ b c * (dichA T r b c v + dichGn T r b c v) := by
    have k1 := dich_norm_ge (T := T) (r := r) (b := b) (c := c) e
    have k2 := mul_le_mul_of_nonneg_left (dich_vecMul_le v (M - T)) (dichα_nonneg (T := T)
      (r := r) (b := b) (c := c))
    have k3 := mul_le_mul_of_nonneg_left (dich_norm_le (T := T) (r := r) hbc v)
      (mul_nonneg (dichα_nonneg (T := T) (r := r) (b := b) (c := c)) (dichGam_nonneg (M - T)))
    rw [← he] at k2
    calc _ ≤ _ := k1
      _ ≤ _ := k2
      _ = dichα T r b c * dichGam (M - T) * ‖v‖ := by ring
      _ ≤ _ := k3
      _ = _ := by ring
  have hEa : 0 ≤ dichA T r b c e := norm_nonneg _
  have hEg : 0 ≤ dichGn T r b c e := norm_nonneg _
  -- the `r`-component
  have hu : (v ᵥ* M) ᵥ* dichPr T r b c = r • (v ᵥ* dichPr T r b c) + e ᵥ* dichPr T r b c := by
    rw [hw, Matrix.add_vecMul, Matrix.vecMul_vecMul, dich_T_mul_Pr hT, Matrix.vecMul_smul]
  have hA1 : dichA T r b c (v ᵥ* M) ≤ |r| * dichA T r b c v + dichA T r b c e := by
    unfold dichA
    rw [hu]
    calc _ ≤ ‖r • (v ᵥ* dichPr T r b c)‖ + ‖e ᵥ* dichPr T r b c‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs]
  -- the oscillating component
  have hp : (v ᵥ* M) ᵥ* dichPq T r b c = (v ᵥ* dichPq T r b c) ᵥ* T + e ᵥ* dichPq T r b c := by
    rw [hw, Matrix.add_vecMul, Matrix.vecMul_vecMul, dich_T_mul_Pq hT, ← Matrix.vecMul_vecMul]
  have hq : (v ᵥ* dichPq T r b c) ᵥ* dichQuad T b c = 0 := by
    rw [Matrix.vecMul_vecMul, dich_Pq_mul_quad hbc hT, Matrix.vecMul_zero]
  have hsc := dichG_scale hbc _ hq
  have hG : dichG T b c ((v ᵥ* M) ᵥ* dichPq T r b c) =
      dichG T b c ((v ᵥ* dichPq T r b c) ᵥ* T) + dichG T b c (e ᵥ* dichPq T r b c) := by
    rw [hp, map_add]
  have hG1 : dichGn T r b c (v ᵥ* M) ≤ Real.sqrt c * dichGn T r b c v + dichGn T r b c e := by
    unfold dichGn
    rw [hG, ← hsc]
    exact norm_add_le _ _
  have hG2 : Real.sqrt c * dichGn T r b c v - dichGn T r b c e ≤ dichGn T r b c (v ᵥ* M) := by
    unfold dichGn
    rw [hG, ← hsc]
    have := norm_sub_le (dichG T b c ((v ᵥ* dichPq T r b c) ᵥ* T) +
      dichG T b c (e ᵥ* dichPq T r b c)) (dichG T b c (e ᵥ* dichPq T r b c))
    rw [add_sub_cancel_right] at this
    linarith
  refine ⟨by linarith, by linarith, by linarith⟩

theorem dichotomy_upper (T : Matrix (Fin 3) (Fin 3) ℝ) (r b c : ℝ) (hbc : b ^ 2 < 4 * c)
    (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) (hr : r ^ 2 < c)
    (A : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (hA : Tendsto A atTop (𝓝 T))
    (z : ℕ → (Fin 3 → ℝ)) (hz : ∀ n, z (n + 1) = z n ᵥ* A n) :
    ∀ ε > 0, ∃ K, ∀ n, ‖z n‖ ≤ K * (Real.sqrt c + ε) ^ n := by
  have hrs : |r| < Real.sqrt c := Real.lt_sqrt (abs_nonneg r) |>.2 (by rwa [sq_abs])
  have hδ : Tendsto (fun n => dichα T r b c * dichGam (A n - T) * dichβ b c) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (dichGam_tendsto hA)).mul
      (tendsto_const_nhds (x := dichβ b c))
  intro ε hε
  obtain ⟨K, hK⟩ := dich_seq_upper (fun n => dichA T r b c (z n)) (fun n => dichGn T r b c (z n))
    (fun n => dichα T r b c * dichGam (A n - T) * dichβ b c) (Real.sqrt c) |r| (abs_nonneg r)
    hrs.le (fun n => norm_nonneg _) (fun n => norm_nonneg _) hδ
    (fun n => by rw [hz]; exact (dich_step hbc hT (z n) (A n)).1)
    (fun n => by rw [hz]; exact (dich_step hbc hT (z n) (A n)).2.1) ε hε
  refine ⟨dichβ b c * K, fun n => ?_⟩
  calc ‖z n‖ ≤ dichβ b c * (dichA T r b c (z n) + dichGn T r b c (z n)) := dich_norm_le hbc _
    _ ≤ dichβ b c * (K * (Real.sqrt c + ε) ^ n) :=
        mul_le_mul_of_nonneg_left (hK n) dichβ_nonneg
    _ = _ := by ring

theorem dichotomy_decay (T : Matrix (Fin 3) (Fin 3) ℝ) (r b c : ℝ) (hbc : b ^ 2 < 4 * c)
    (hT : (T - r • 1) * (T * T + b • T + c • 1) = 0) (hr : r ^ 2 < c)
    (A : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (hA : Tendsto A atTop (𝓝 T))
    (z : ℕ → (Fin 3 → ℝ)) (hz : ∀ n, z (n + 1) = z n ᵥ* A n)
    (ρ K₀ : ℝ) (hρ : ρ < Real.sqrt c) (hbound : ∀ n, ‖z n‖ ≤ K₀ * ρ ^ n) :
    ∀ ε > 0, ∃ K, ∀ n, ‖z n‖ ≤ K * (|r| + ε) ^ n := by
  have hrs : |r| < Real.sqrt c := Real.lt_sqrt (abs_nonneg r) |>.2 (by rwa [sq_abs])
  have hδ : Tendsto (fun n => dichα T r b c * dichGam (A n - T) * dichβ b c) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (dichGam_tendsto hA)).mul
      (tendsto_const_nhds (x := dichβ b c))
  intro ε hε
  obtain ⟨K, hK⟩ := dich_seq_decay (fun n => dichA T r b c (z n)) (fun n => dichGn T r b c (z n))
    (fun n => dichα T r b c * dichGam (A n - T) * dichβ b c) (Real.sqrt c) |r| (abs_nonneg r)
    hrs (fun n => norm_nonneg _) (fun n => norm_nonneg _) hδ
    (fun n => by rw [hz]; exact (dich_step hbc hT (z n) (A n)).1)
    (fun n => by rw [hz]; exact (dich_step hbc hT (z n) (A n)).2.2)
    ρ (dichα T r b c * K₀) hρ
    (fun n => (dich_norm_ge (z n)).trans (by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hbound n) dichα_nonneg)) ε hε
  refine ⟨dichβ b c * K, fun n => ?_⟩
  calc ‖z n‖ ≤ dichβ b c * (dichA T r b c (z n) + dichGn T r b c (z n)) := dich_norm_le hbc _
    _ ≤ dichβ b c * (K * (|r| + ε) ^ n) :=
        mul_le_mul_of_nonneg_left (hK n) dichβ_nonneg
    _ = _ := by ring

end Main

end Zeta2L2Chi3

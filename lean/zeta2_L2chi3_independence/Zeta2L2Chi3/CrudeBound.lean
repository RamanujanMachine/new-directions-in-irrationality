import Zeta2L2Chi3.SeriesState

/-!
# A crude exponential bound for the series state

For `x ≥ 1` we write `s ^ k * F n s` as a product of ratios `(s + a) / (b - s)` (each bounded at
`s = -x`) times four factors `1 / (b - s)`; the product rule then gives
`|(s^k F_n)'(-x)| ≤ (40 n + 12) 16^n / x^2`, and summing over `x = m + 1` gives
`|S n k| ≤ 2 (40 n + 12) 16^n`.
-/

noncomputable section

namespace Zeta2L2Chi3

open Finset Filter Topology

/-- `f` has a derivative at `y` with `|f y| ≤ c` and `|f' y| ≤ N c`. -/
def CGood (f : ℝ → ℝ) (y c N : ℝ) : Prop :=
  ∃ f' : ℝ, HasDerivAt f f' y ∧ |f y| ≤ c ∧ |f'| ≤ N * c

lemma CGood.nonneg {f : ℝ → ℝ} {y c N : ℝ} (h : CGood f y c N) : 0 ≤ c := by
  obtain ⟨_, _, h1, _⟩ := h
  exact (abs_nonneg _).trans h1

lemma CGood.mul {f g : ℝ → ℝ} {y c c' N N' : ℝ} (hf : CGood f y c N) (hg : CGood g y c' N') :
    CGood (fun s => f s * g s) y (c * c') (N + N') := by
  have hc' := hg.nonneg
  obtain ⟨f', hf1, hf2, hf3⟩ := hf
  obtain ⟨g', hg1, hg2, hg3⟩ := hg
  refine ⟨f' * g y + f y * g', hf1.fun_mul hg1, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul hf2 hg2 (abs_nonneg _) ((abs_nonneg _).trans hf2)
  · calc |f' * g y + f y * g'| ≤ |f'| * |g y| + |f y| * |g'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (N * c) * c' + c * (N' * c') := by
          gcongr
          · exact (abs_nonneg _).trans hf3
          · exact (abs_nonneg _).trans hf2
      _ = (N + N') * (c * c') := by ring

lemma CGood.congr {f g : ℝ → ℝ} {y c N : ℝ} (hf : CGood f y c N) (h : ∀ s, f s = g s) :
    CGood g y c N := by
  have : f = g := funext h
  rwa [← this]

lemma CGood.mono {f : ℝ → ℝ} {y c c' N N' : ℝ} (hf : CGood f y c N) (hc : c ≤ c') (hN : N ≤ N')
    (hN0 : 0 ≤ N) : CGood f y c' N' := by
  have hc0 := hf.nonneg
  obtain ⟨f', h1, h2, h3⟩ := hf
  refine ⟨f', h1, h2.trans hc, h3.trans ?_⟩
  calc N * c ≤ N * c' := mul_le_mul_of_nonneg_left hc hN0
    _ ≤ N' * c' := mul_le_mul_of_nonneg_right hN (hc0.trans hc)

lemma CGood.prod_range {y c N : ℝ} (f : ℕ → ℝ → ℝ) (m : ℕ) (h : ∀ i < m, CGood (f i) y c N)
    (hN : 0 ≤ N) : CGood (fun s => ∏ i ∈ range m, f i s) y (c ^ m) (m * N) := by
  induction m with
  | zero =>
    refine ⟨0, ?_, ?_, ?_⟩
    · simpa using hasDerivAt_const y (1 : ℝ)
    · simp
    · simp
  | succ m ih =>
    have h1 := (ih fun i hi => h i (by omega)).mul (h m (by omega))
    refine (h1.congr fun s => ?_).mono (le_of_eq (by ring)) (le_of_eq (by push_cast; ring)) ?_
    · rw [prod_range_succ]
    · positivity

/-- the basic ratio `(s + a) / (b - s)` at `s = -x` -/
lemma cgood_ratio (a b c x : ℝ) (hx : 1 ≤ x) (hb : 0 ≤ b) (hc : 1 ≤ c)
    (h : |a - x| ≤ c * (b + x)) : CGood (fun s => (s + a) / (b - s)) (-x) c 2 := by
  have hbx : 0 < b + x := by linarith
  have hne : b - -x ≠ 0 := by rw [sub_neg_eq_add]; exact hbx.ne'
  refine ⟨_, ((hasDerivAt_id (-x)).add_const a).fun_div
    ((hasDerivAt_const (-x) b).sub (hasDerivAt_id (-x))) hne, ?_, ?_⟩
  · simp only [sub_neg_eq_add]
    rw [abs_div, abs_of_pos hbx, div_le_iff₀ hbx]
    calc |-x + a| = |a - x| := by ring_nf
      _ ≤ c * (b + x) := h
  · simp only [id, sub_neg_eq_add]
    have e : (1 * (b + x) - (-x + a) * (0 - 1)) = (a - x) + 2 * (b + x) - (b + x) := by ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (b + x) ^ 2), div_le_iff₀ (by positivity)]
    calc |a - x + 2 * (b + x) - (b + x)| ≤ |a - x| + (b + x) := by
          rw [show a - x + 2 * (b + x) - (b + x) = (a - x) + (b + x) by ring]
          exact (abs_add_le _ _).trans (by rw [abs_of_pos hbx])
      _ ≤ c * (b + x) + c * (b + x) := by gcongr; nlinarith
      _ = 2 * c * (b + x) := by ring
      _ ≤ 2 * c * (b + x) ^ 2 := by
          have : b + x ≤ (b + x) ^ 2 := by nlinarith
          have : 0 ≤ 2 * c := by linarith
          exact mul_le_mul_of_nonneg_left (by assumption) this

/-- the unmatched factor `1 / (b - s)` at `s = -x` -/
lemma cgood_inv (b x : ℝ) (hx : 1 ≤ x) (hb : 0 ≤ b) :
    CGood (fun s => 1 / (b - s)) (-x) (1 / x) 1 := by
  have hbx : 0 < b + x := by linarith
  have hx0 : 0 < x := by linarith
  have hne : b - -x ≠ 0 := by rw [sub_neg_eq_add]; exact hbx.ne'
  refine ⟨_, (hasDerivAt_const (-x) (1 : ℝ)).fun_div
    ((hasDerivAt_const (-x) b).sub (hasDerivAt_id (-x))) hne, ?_, ?_⟩
  · simp only [sub_neg_eq_add]
    rw [abs_div, abs_one, abs_of_pos hbx]
    exact one_div_le_one_div_of_le hx0 (by linarith)
  · simp only [sub_neg_eq_add]
    rw [show (0 * (b + x) - 1 * (0 - 1)) = (1 : ℝ) by ring, abs_div, abs_one,
      abs_of_pos (by positivity : (0 : ℝ) < (b + x) ^ 2), one_mul]
    apply one_div_le_one_div_of_le hx0
    nlinarith

lemma cgood_pow (k : ℕ) (x : ℝ) (hx : 1 ≤ x) : CGood (fun s => s ^ k) (-x) (x ^ k) k := by
  refine ⟨_, hasDerivAt_pow k (-x), ?_, ?_⟩
  · rw [abs_pow, abs_neg, abs_of_nonneg (by linarith)]
  · rw [abs_mul, abs_pow, abs_neg, Nat.abs_cast, abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.sub_le k 1)) (Nat.cast_nonneg k)

/-! ### Splitting `s ^ k F_n(s)` into bounded ratios -/

section split

variable (n d : ℕ)

/-- matched block: first numerator block against `P1` -/
def blkI (s : ℝ) : ℝ := ∏ i ∈ range (10 * n + 1), (s + (1 + (i : ℝ))) / ((2 * n + i : ℝ) - s)
/-- matched block: nonpositive part of the second numerator block against the middle of `P3` -/
def blkA (s : ℝ) : ℝ :=
  ∏ i ∈ range n, (s + (1 - n + (i : ℝ))) / ((2 * n + 1 / 2 + ((d : ℝ) + i) : ℝ) - s)
/-- matched block: middle of the second numerator block against `P2` -/
def blkB (s : ℝ) : ℝ := ∏ i ∈ range (6 * n + 2), (s + (1 + (i : ℝ))) / ((1 / 3 + i : ℝ) - s)
/-- matched block: end of the second numerator block against the start of `P3` -/
def blkC (s : ℝ) : ℝ :=
  ∏ i ∈ range d, (s + (6 * n + 3 + (i : ℝ))) / ((2 * n + 1 / 2 + i : ℝ) - s)
/-- the four unmatched denominator factors -/
def blkU (s : ℝ) : ℝ :=
  1 / ((12 * n + 1 : ℝ) - s) * (1 / ((2 * n + 1 / 2 + ((d : ℝ) + n) : ℝ) - s) *
    (1 / ((2 * n + 1 / 2 + ((d : ℝ) + n + 1) : ℝ) - s) *
      (1 / ((2 * n + 1 / 2 + ((d : ℝ) + n + 2) : ℝ) - s))))

lemma FNum_split (hd : 2 * n = d + 1) (s : ℝ) :
    FNum n s = (∏ i ∈ range (10 * n + 1), (s + (1 + (i : ℝ)))) *
      ((∏ i ∈ range n, (s + (1 - n + (i : ℝ)))) * (∏ i ∈ range (6 * n + 2), (s + (1 + (i : ℝ)))) *
        ∏ i ∈ range d, (s + (6 * n + 3 + (i : ℝ)))) := by
  simp only [FNum, rf]
  have h1 := prod_range_add (fun i : ℕ => s + 1 - (n : ℝ) + i) (n + (6 * n + 2)) d
  have h2 := prod_range_add (fun i : ℕ => s + 1 - (n : ℝ) + i) n (6 * n + 2)
  rw [show 9 * n + 1 = n + (6 * n + 2) + d by omega, h1, h2]
  congr 1
  · exact prod_congr rfl fun i _ => by ring
  · congr 1; congr 1
    · exact prod_congr rfl fun i _ => by ring
    · exact prod_congr rfl fun i _ => by push_cast; ring
    · exact prod_congr rfl fun i _ => by push_cast; ring

lemma P1_split (s : ℝ) :
    P1 n s = (∏ i ∈ range (10 * n + 1), ((2 * n + i : ℝ) - s)) * ((12 * n + 1 : ℝ) - s) := by
  rw [P1, show 10 * n + 2 = (10 * n + 1) + 1 by omega, prod_range_succ]
  congr 1; push_cast; ring

lemma P3_split (hd : 2 * n = d + 1) (s : ℝ) :
    P3 n s = (∏ i ∈ range d, ((2 * n + 1 / 2 + i : ℝ) - s)) *
      (∏ i ∈ range n, ((2 * n + 1 / 2 + ((d : ℝ) + i) : ℝ) - s)) *
      (((2 * n + 1 / 2 + ((d : ℝ) + n) : ℝ) - s) * (((2 * n + 1 / 2 + ((d : ℝ) + n + 1) : ℝ) - s) *
        ((2 * n + 1 / 2 + ((d : ℝ) + n + 2) : ℝ) - s))) := by
  rw [P3, show 3 * n + 2 = d + n + 3 by omega, prod_range_add, prod_range_add]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  congr 1
  · congr 1
    exact prod_congr rfl fun i _ => by push_cast; ring
  · push_cast; ring

lemma sF_split (k : ℕ) (hd : 2 * n = d + 1) (s : ℝ) :
    s ^ k * F n s = s ^ k * ((((blkI n s * blkA n d s) * blkB n s) * blkC n d s) * blkU n d s) := by
  rw [F, FDen_eq, FNum_split n d hd, P1_split, P3_split n d hd, P2]
  simp only [blkI, blkA, blkB, blkC, blkU, prod_div_distrib]
  simp only [div_eq_mul_inv, mul_inv, one_mul]
  ring

end split

/-! ### Bounds for the blocks at `s = -x` -/

section blocks

variable {n d : ℕ} {x : ℝ}

lemma cgood_blkI (hx : 1 ≤ x) : CGood (blkI n) (-x) (1 ^ (10 * n + 1)) ((10 * n + 1 : ℕ) * 2) := by
  refine CGood.prod_range (fun i s => (s + (1 + (i : ℝ))) / ((2 * n + i : ℝ) - s)) _
    (fun i _ => cgood_ratio _ _ _ _ hx (by positivity) le_rfl ?_) (by norm_num)
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]; constructor <;> linarith

lemma cgood_blkA (hx : 1 ≤ x) (hn : 1 ≤ n) (hd : 2 * n = d + 1) :
    CGood (blkA n d) (-x) (1 ^ n) ((n : ℕ) * 2) := by
  have hd' : (d : ℝ) = 2 * n - 1 := by
    have : ((2 * n : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) := by rw [hd]
    push_cast at this; linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine CGood.prod_range
    (fun i s => (s + (1 - n + (i : ℝ))) / ((2 * n + 1 / 2 + ((d : ℝ) + i) : ℝ) - s)) _
    (fun i _ => cgood_ratio _ _ _ _ hx (by positivity) le_rfl ?_) (by norm_num)
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [abs_le]; constructor <;> linarith

lemma cgood_blkB (hx : 1 ≤ x) : CGood (blkB n) (-x) (1 ^ (6 * n + 2)) ((6 * n + 2 : ℕ) * 2) := by
  refine CGood.prod_range (fun i s => (s + (1 + (i : ℝ))) / ((1 / 3 + i : ℝ) - s)) _
    (fun i _ => cgood_ratio _ _ _ _ hx (by positivity) le_rfl ?_) (by norm_num)
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [abs_le]; constructor <;> linarith

lemma cgood_blkC (hx : 1 ≤ x) (hn : 1 ≤ n) : CGood (blkC n d) (-x) (4 ^ d) ((d : ℕ) * 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine CGood.prod_range
    (fun i s => (s + (6 * n + 3 + (i : ℝ))) / ((2 * n + 1 / 2 + i : ℝ) - s)) _
    (fun i _ => cgood_ratio _ _ _ _ hx (by positivity) (by norm_num) ?_) (by norm_num)
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [abs_le]; constructor <;> linarith

lemma cgood_blkU (hx : 1 ≤ x) :
    CGood (blkU n d) (-x) (1 / x * (1 / x * (1 / x * (1 / x)))) (1 + (1 + (1 + 1))) := by
  have h := (cgood_inv (12 * n + 1 : ℝ) x hx (by positivity)).mul
    ((cgood_inv (2 * n + 1 / 2 + ((d : ℝ) + n) : ℝ) x hx (by positivity)).mul
      ((cgood_inv (2 * n + 1 / 2 + ((d : ℝ) + n + 1) : ℝ) x hx (by positivity)).mul
        (cgood_inv (2 * n + 1 / 2 + ((d : ℝ) + n + 2) : ℝ) x hx (by positivity))))
  exact h

end blocks

/-- **Pointwise bound** for the derivative of `s^k F_n(s)` at `s = -x`, `x ≥ 1`. -/
theorem abs_deriv_sF_le (n k : ℕ) (hk : k ≤ 2) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    |deriv (fun s : ℝ => s ^ k * F n s) (-x)| ≤ (40 * n + 12) * (16 ^ n / x ^ 2) := by
  obtain ⟨d, hd⟩ : ∃ d, 2 * n = d + 1 := ⟨2 * n - 1, by omega⟩
  have hd' : (d : ℝ) = 2 * n - 1 := by
    have : ((2 * n : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) := by rw [hd]
    push_cast at this; linarith
  have hx0 : 0 < x := by linarith
  have hG := (cgood_pow k x hx).mul ((((((cgood_blkI (n := n) hx).mul (cgood_blkA hx hn hd)).mul
    (cgood_blkB (n := n) hx)).mul (cgood_blkC (n := n) (d := d) hx hn)).mul (cgood_blkU (n := n) (d := d) hx)))
  have hc : x ^ k * ((((1 ^ (10 * n + 1) * 1 ^ n) * 1 ^ (6 * n + 2)) * 4 ^ d) *
      (1 / x * (1 / x * (1 / x * (1 / x))))) ≤ 16 ^ n / x ^ 2 := by
    have h1 : x ^ k ≤ x ^ 2 := pow_le_pow_right₀ hx hk
    have h2 : (4 : ℝ) ^ d ≤ 16 ^ n := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul, hd]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc x ^ k * ((((1 ^ (10 * n + 1) * 1 ^ n) * 1 ^ (6 * n + 2)) * 4 ^ d) *
          (1 / x * (1 / x * (1 / x * (1 / x))))) = (x ^ k * 4 ^ d) * (1 / x) ^ 4 := by
            simp only [one_pow, one_mul]; ring
      _ ≤ (x ^ 2 * 16 ^ n) * (1 / x) ^ 4 := by gcongr
      _ = 16 ^ n / x ^ 2 := by field_simp
  have hN : (k : ℝ) + ((((((10 * n + 1 : ℕ) : ℝ) * 2 + (n : ℕ) * 2) + ((6 * n + 2 : ℕ) : ℝ) * 2) +
      (d : ℕ) * 2) + (1 + (1 + (1 + 1)))) ≤ 40 * n + 12 := by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    push_cast; linarith
  obtain ⟨g', hg1, -, hg3⟩ := hG.mono hc hN (by positivity)
  have e : (fun s : ℝ => s ^ k * F n s) =
      fun s => s ^ k * ((((blkI n s * blkA n d s) * blkB n s) * blkC n d s) * blkU n d s) :=
    funext (sF_split n d k hd)
  rw [e, hg1.deriv]
  exact hg3

/-- **Crude exponential bound for the series state.** -/
theorem abs_S_le (n k : ℕ) (hk : k ≤ 2) (hn : 1 ≤ n) :
    |S n k| ≤ 2 * (40 * n + 12) * 16 ^ n := by
  set K : ℝ := (40 * n + 12) * 16 ^ n with hK
  have hK0 : 0 ≤ K := by positivity
  have hsum : HasSum (fun m : ℕ => K * (1 / ((m : ℝ) + 1) ^ 2)) (K * Z) :=
    summable_Z.hasSum.mul_left K
  have hb : ∀ m : ℕ, ‖deriv (fun s : ℝ => s ^ k * F n s) (-((m : ℝ) + 1))‖ ≤
      K * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    rw [Real.norm_eq_abs]
    refine (abs_deriv_sF_le n k hk hn _ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)).trans
      (le_of_eq ?_)
    rw [hK]; ring
  have h := tsum_of_norm_bounded hsum hb
  rw [Real.norm_eq_abs] at h
  have hZ : Z ≤ 2 := by
    rw [Z_eq_pi]
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  unfold S
  calc _ ≤ K * Z := h
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left hZ hK0
    _ = 2 * (40 * n + 12) * 16 ^ n := by rw [hK]; ring

end Zeta2L2Chi3

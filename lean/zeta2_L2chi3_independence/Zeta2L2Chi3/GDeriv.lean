/-
# Differentiability and derivative asymptotics of the certificate quotient `G_k`

`G_k(s) = A(s) / B(s)` for explicit real polynomials `A`, `B` with `deg A ≤ deg B`, `B > 0` on
`s < 0`, and `(s + 1)^2 ∣ A`.  Hence `G_k` is differentiable on `s < 0`, `G_k'(-1) = 0`, and
`G_k'(s) → 0` as `s → -∞`.
-/
import Zeta2L2Chi3.TransportTH
import Zeta2L2Chi3.PartialFrac

noncomputable section

namespace Zeta2L2Chi3

open Filter Topology Finset Polynomial

/-! ### Polynomial model of `G_k` -/

/-- the constant `1 / (12 (3n+1) D_Q(n))` -/
def gκ (n : ℕ) : ℝ := 1 / (12 * (3 * n + 1) * hornerR Data.Qden (n : ℝ))

def H1P (n : ℕ) : ℝ[X] := ∏ i ∈ range (10 * n), (X + Polynomial.C ((i : ℝ) + 2))
def H2P (n : ℕ) : ℝ[X] := ∏ i ∈ (range (9 * n + 1)).erase n, (X + Polynomial.C ((i : ℝ) + 1 - n))

/-- numerator polynomial of `G_k` -/
def AP (n : ℕ) (k : Fin 3) : ℝ[X] :=
  (X + Polynomial.C 1) ^ 2 * (Polynomial.C (gκ n) * H1P n * H2P n * (Ncert k).polyS (n : ℝ))

/-- the linear factor `c - s` -/
def linP (c : ℝ) : ℝ[X] := Polynomial.C c - X

/-- denominator polynomial of `G_k` -/
def BP (n : ℕ) : ℝ[X] :=
  (∏ i ∈ range (10 * n + 2), linP (2 * n + i)) * (∏ i ∈ range (6 * n + 2), linP (1 / 3 + i)) *
    (∏ i ∈ range (3 * n + 2), linP (2 * n + 1 / 2 + i)) *
    (∏ i ∈ range 12, linP (12 * n + 2 + i)) * (∏ i ∈ range 6, linP (6 * n + 7 / 3 + i)) *
    (∏ i ∈ range 5, linP (5 * n + 5 / 2 + i))

lemma FNum_eq_sq (n : ℕ) (s : ℝ) :
    FNum n s = (s + 1) ^ 2 * ((∏ i ∈ range (10 * n), (s + ((i : ℝ) + 2))) *
      ∏ i ∈ (range (9 * n + 1)).erase n, (s + ((i : ℝ) + 1 - n))) := by
  have hmem : n ∈ range (9 * n + 1) := by simp only [mem_range]; omega
  have e1 : rf (s + 1) (10 * n + 1) = (s + 1) * ∏ i ∈ range (10 * n), (s + ((i : ℝ) + 2)) := by
    unfold rf
    rw [prod_range_succ', mul_comm]
    congr 1
    · simp
    · exact prod_congr rfl fun i _ => by push_cast; ring
  have e2 : rf (s + 1 - n) (9 * n + 1) =
      (s + 1) * ∏ i ∈ (range (9 * n + 1)).erase n, (s + ((i : ℝ) + 1 - n)) := by
    unfold rf
    rw [← mul_prod_erase _ _ hmem]
    congr 1
    · ring
    · exact prod_congr rfl fun i _ => by ring
  rw [FNum, e1, e2]; ring

lemma eval_AP (n : ℕ) (k : Fin 3) (s : ℝ) :
    (AP n k).eval s = gκ n * FNum n s * (Ncert k).val (n : ℝ) s := by
  rw [FNum_eq_sq]
  simp only [AP, H1P, H2P, eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_prod,
    PE.eval_polyS]
  ring

lemma eval_BP (n : ℕ) (s : ℝ) : (BP n).eval s = FDen n s * rdenR (n : ℝ) s := by
  rw [FDen_eq, rdenR_eq]
  simp only [BP, linP, eval_mul, eval_prod, eval_sub, eval_C, eval_X, P1, P2, P3, R12, R6, R5]
  ring

lemma Gk_eq_poly (n : ℕ) (k : Fin 3) : Gk n k = fun s => (AP n k).eval s / (BP n).eval s := by
  funext s
  rw [eval_AP, eval_BP, Gk, F, gκ]
  generalize 12 * (3 * (n : ℝ) + 1) * hornerR Data.Qden (n : ℝ) = c
  ring

/-! ### Degrees -/

lemma natDegree_linP (c : ℝ) : (linP c).natDegree = 1 := by
  rw [linP, ← neg_sub, natDegree_neg, natDegree_X_sub_C]

lemma linP_ne_zero (c : ℝ) : linP c ≠ 0 := by
  intro h; have := natDegree_linP c; rw [h, natDegree_zero] at this; exact zero_ne_one this

lemma natDegree_prod_linP (S : Finset ℕ) (f : ℕ → ℝ) :
    (∏ i ∈ S, linP (f i)).natDegree = S.card := by
  rw [natDegree_prod _ _ fun i _ => linP_ne_zero _]
  simp [natDegree_linP]

lemma prod_linP_ne_zero (S : Finset ℕ) (f : ℕ → ℝ) : (∏ i ∈ S, linP (f i)) ≠ 0 :=
  prod_ne_zero_iff.2 fun _ _ => linP_ne_zero _

lemma natDegree_BP (n : ℕ) : (BP n).natDegree = 19 * n + 29 := by
  simp only [BP]
  rw [natDegree_mul (by simp only [ne_eq, mul_eq_zero, prod_linP_ne_zero, or_self,
      not_false_eq_true]) (prod_linP_ne_zero _ _),
    natDegree_mul (by simp only [ne_eq, mul_eq_zero, prod_linP_ne_zero, or_self,
      not_false_eq_true]) (prod_linP_ne_zero _ _),
    natDegree_mul (by simp only [ne_eq, mul_eq_zero, prod_linP_ne_zero, or_self,
      not_false_eq_true]) (prod_linP_ne_zero _ _),
    natDegree_mul (by simp only [ne_eq, mul_eq_zero, prod_linP_ne_zero, or_self,
      not_false_eq_true]) (prod_linP_ne_zero _ _),
    natDegree_mul (prod_linP_ne_zero _ _) (prod_linP_ne_zero _ _)]
  simp only [natDegree_prod_linP, card_range]
  ring

lemma BP_ne_zero (n : ℕ) : BP n ≠ 0 := by
  intro h; have := natDegree_BP n; rw [h, natDegree_zero] at this; omega

lemma degS_Ncert (k : Fin 3) : (Ncert k).degS = 27 := by
  fin_cases k <;> rfl

lemma natDegree_AP_le (n : ℕ) (k : Fin 3) : (AP n k).natDegree ≤ 19 * n + 29 := by
  have hX : ((X + Polynomial.C 1 : ℝ[X]) ^ 2).natDegree ≤ 2 := by
    refine natDegree_pow_le.trans ?_; rw [natDegree_X_add_C]
  have h1 : (H1P n).natDegree ≤ 10 * n := by
    rw [H1P, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one, le_refl]
  have h2 : (H2P n).natDegree ≤ 9 * n := by
    rw [H2P, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    have hmem : n ∈ range (9 * n + 1) := by simp only [mem_range]; omega
    simp only [natDegree_X_add_C, sum_const, card_erase_of_mem hmem, card_range, smul_eq_mul,
      mul_one]
    omega
  have h3 := PE.natDegree_polyS_le (Ncert k) (n : ℝ)
  rw [degS_Ncert] at h3
  have hC : (Polynomial.C (gκ n)).natDegree = 0 := natDegree_C _
  unfold AP
  refine natDegree_mul_le.trans ?_
  have := (natDegree_mul_le (p := Polynomial.C (gκ n) * H1P n * H2P n) (q := (Ncert k).polyS (n : ℝ)))
  have := (natDegree_mul_le (p := Polynomial.C (gκ n) * H1P n) (q := H2P n))
  have := (natDegree_mul_le (p := Polynomial.C (gκ n)) (q := H1P n))
  omega

/-! ### Positivity of the denominator on `s < 0` -/

lemma prod_linP_pos (S : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℝ) (hs : s < 0) :
    0 < (∏ i ∈ S, linP (f i)).eval s := by
  rw [eval_prod]
  exact prod_pos fun i _ => by
    simp only [linP, eval_sub, eval_C, eval_X]; linarith [hf i]

lemma BP_pos (n : ℕ) (s : ℝ) (hs : s < 0) : 0 < (BP n).eval s := by
  simp only [BP, eval_mul]
  refine mul_pos (mul_pos (mul_pos (mul_pos (mul_pos ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact prod_linP_pos _ _ (fun i => by positivity) s hs

/-! ### Main results -/

lemma hasDerivAt_Gk (n : ℕ) (k : Fin 3) (x : ℝ) (hx : x < 0) :
    HasDerivAt (Gk n k) (((AP n k).derivative.eval x * (BP n).eval x -
      (AP n k).eval x * (BP n).derivative.eval x) / ((BP n).eval x) ^ 2) x := by
  rw [Gk_eq_poly]
  exact ((AP n k).hasDerivAt x).div ((BP n).hasDerivAt x) (BP_pos n x hx).ne'

theorem differentiableAt_Gk (n : ℕ) (k : Fin 3) (x : ℝ) (hx : x < 0) :
    DifferentiableAt ℝ (Gk n k) x :=
  (hasDerivAt_Gk n k x hx).differentiableAt

theorem deriv_Gk_neg_one (n : ℕ) (k : Fin 3) : deriv (Gk n k : ℝ → ℝ) (-1) = 0 := by
  rw [(hasDerivAt_Gk n k (-1 : ℝ) (by norm_num)).deriv]
  have hA : (AP n k).eval (-1) = 0 := by
    simp [AP]
  have hA' : (AP n k).derivative.eval (-1) = 0 := by
    simp [AP, derivative_mul, derivative_pow]
  rw [hA, hA']; simp

theorem tendsto_deriv_Gk (n : ℕ) (k : Fin 3) : Tendsto (deriv (Gk n k : ℝ → ℝ)) atBot (𝓝 0) := by
  have hev : (fun x => ((AP n k).derivative * BP n - AP n k * (BP n).derivative).eval x /
      (BP n ^ 2).eval x) =ᶠ[atBot] deriv (Gk n k : ℝ → ℝ) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    rw [(hasDerivAt_Gk n k x hx).deriv]
    simp only [eval_sub, eval_mul, eval_pow]
  refine Tendsto.congr' hev (Polynomial.div_tendsto_atBot_zero_of_degree_lt _ _ ?_)
  apply degree_lt_degree
  have hB := natDegree_BP n
  have hA := natDegree_AP_le n k
  rw [natDegree_pow, hB]
  have h1 := natDegree_derivative_le (AP n k)
  have h2 := natDegree_derivative_le (BP n)
  have h3 := natDegree_mul_le (p := (AP n k).derivative) (q := BP n)
  have h4 := natDegree_mul_le (p := AP n k) (q := (BP n).derivative)
  have h5 := natDegree_sub_le ((AP n k).derivative * BP n) (AP n k * (BP n).derivative)
  omega

end Zeta2L2Chi3

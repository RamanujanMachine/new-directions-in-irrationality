/-
# Valuation bounds for `Δ_n` (helper for `DeltaVal`)

* the decomposition `v_q(Δ_n) = n v_q(C₀) + v_q(g(n)/g(0)) + Σ m v_q((β)_{An})`;
* the valuation mass of `g(n)/g(0)` is `O(log n)`;
* the small-prime bounds `v_2 ≥ 18n - O(log n)`, `v_3 ≥ 27n - O(log n)`,
  `v_p ≥ -O(log n / log p + 1)` (`p ≥ 5`).
-/
import Zeta2L2Chi3.Arith.DeltaG
import Zeta2L2Chi3.Arith.DeltaFam

open Finset

namespace Zeta2L2Chi3.Arith

open Zeta2L2Chi3

lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-! ### Decomposition of `v_q(Δ_n)` -/

lemma gamma_prod_ne (n : ℕ) :
    (gammaF.map (fun fm => (rf (fm.1.be) (fm.1.la * n)) ^ fm.2)).prod ≠ 0 := by
  refine List.prod_ne_zero fun h0 => ?_
  obtain ⟨fm, hfm, h⟩ := List.mem_map.1 h0
  exact zpow_ne_zero _ (rf_ne_zero fm.1 (gammaF_good fm hfm).2.2.1 _) h

lemma val_Delta (q : ℕ) [Fact q.Prime] (n : ℕ) :
    (padicValRat q (Δ n) : ℝ) = n * padicValRat q C0X + padicValRat q (gfunX n / gfunX 0) +
      (gammaF.map fun fm => (fm.2 : ℝ) * padicValRat q (rf fm.1.be (fm.1.la * n))).sum := by
  have hC : C0X ≠ 0 := by norm_num [C0X]
  have hg : gfunX n / gfunX 0 ≠ 0 := div_ne_zero (gfunX_pos n).ne' (gfunX_pos 0).ne'
  rw [Delta_gammaX, padicValRat.mul (mul_ne_zero (pow_ne_zero _ hC) hg) (gamma_prod_ne n),
    padicValRat.mul (pow_ne_zero _ hC) hg, padicValRat.pow,
    padicValRat_list_prod q _ (fun x hx => by
      obtain ⟨fm, hfm, rfl⟩ := List.mem_map.1 hx
      exact zpow_ne_zero _ (rf_ne_zero fm.1 (gammaF_good fm hfm).2.2.1 _)), List.map_map]
  push_cast
  congr 1
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro fm _
  simp [padicValRat.zpow]

lemma val_C0_two : padicValRat 2 C0X = 8 := by
  rw [show C0X = ((2 ^ 8 * 3 ^ 30 : ℕ) : ℚ) by norm_num [C0X], padicValRat.of_nat,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by
      intro h; exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num))]
  norm_num

lemma val_C0_three : padicValRat 3 C0X = 30 := by
  rw [show C0X = ((2 ^ 8 * 3 ^ 30 : ℕ) : ℚ) by norm_num [C0X], padicValRat.of_nat,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by
      intro h; exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num))]
  norm_num

lemma val_C0_big (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) : padicValRat p C0X = 0 := by
  rw [show C0X = ((2 ^ 8 * 3 ^ 30 : ℕ) : ℚ) by norm_num [C0X], padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd]
  · rfl
  · intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp.out h); omega
    · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp.out h); omega

/-! ### The valuation mass of `g(n)/g(0)` -/

lemma sum_vq_nat_le (a : ℕ) (ha : 0 < a) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (padicValNat q a : ℝ) * Real.log q ≤ Real.log a := by
  have hT : ∀ q ∈ S ∪ a.primeFactors, q.Prime := by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact hS q h
    · exact Nat.prime_of_mem_primeFactors h
  have key := log_eq_sum_padicValRat (a : ℚ) (by exact_mod_cast ha) (S ∪ a.primeFactors) hT
    (by simp) (by simp)
  have hcast : (((a : ℚ)) : ℝ) = (a : ℝ) := by push_cast; rfl
  rw [hcast] at key
  rw [key]
  have hv : ∀ q ∈ S ∪ a.primeFactors, (padicValRat q (a : ℚ) : ℝ) * Real.log q =
      (padicValNat q a : ℝ) * Real.log q := by
    intro q _; rw [padicValRat.of_nat, Int.cast_natCast]
  rw [Finset.sum_congr rfl hv]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun q hq _ =>
    mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (hT q hq).one_lt.le)))

lemma mass_div (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, |(padicValRat q ((a : ℚ) / b) : ℝ)| * Real.log q ≤ Real.log a + Real.log b := by
  have h1 := sum_vq_nat_le a ha S hS
  have h2 := sum_vq_nat_le b hb S hS
  calc _ ≤ ∑ q ∈ S, ((padicValNat q a : ℝ) * Real.log q + (padicValNat q b : ℝ) * Real.log q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        haveI := Fact.mk (hS q hq)
        rw [padicValRat.div (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'),
          padicValRat.of_nat, padicValRat.of_nat]
        have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (hS q hq).one_lt.le)
        simp only [Int.cast_sub, Int.cast_natCast]
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ hl
        have h3 : (0 : ℝ) ≤ padicValNat q a := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ padicValNat q b := Nat.cast_nonneg _
        rw [abs_le]; constructor <;> linarith
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add h1 h2

def NNg (n : ℕ) : ℕ := (8 * n + 1) * (9 * n + 1) * (15 * n + 2) * (20 * n + 3) * (24 * n + 1) ^ 2
def DDg (n : ℕ) : ℕ := (2 * n + 1) * (3 * n + 1) ^ 2 * (6 * n + 1) * (8 * n + 3) * (9 * n + 2) *
  (10 * n + 3) * (12 * n + 1) * (15 * n + 1) * (15 * n + 4) * (18 * n + 1) ^ 2 * (24 * n + 5) *
  (30 * n + 7)

lemma NNg_pos (n : ℕ) : 0 < NNg n := by unfold NNg; positivity
lemma DDg_pos (n : ℕ) : 0 < DDg n := by unfold DDg; positivity

lemma gfun_ratio (n : ℕ) : gfunX n / gfunX 0 = ((420 * NNg n : ℕ) : ℚ) / (DDg n : ℕ) := by
  have hD : (DDg n : ℚ) ≠ 0 := by exact_mod_cast (DDg_pos n).ne'
  have h1 : gfunX n = 3936600 * (NNg n : ℚ) / (DDg n : ℚ) := by
    simp only [gfunX, NNg, DDg]; push_cast; ring
  have h0 : gfunX 0 = 3936600 * 6 / 2520 := by norm_num [gfunX]
  rw [h1, h0]
  push_cast
  field_simp
  ring

lemma NNg_le (n : ℕ) : 420 * NNg n ≤ 420 * 37 ^ 6 * (n + 1) ^ 6 := by
  have : NNg n ≤ (37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) *
      (37 * (n + 1)) ^ 2 := by
    unfold NNg; gcongr <;> omega
  calc 420 * NNg n ≤ 420 * ((37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) *
      (37 * (n + 1)) ^ 2) := Nat.mul_le_mul_left _ this
    _ = _ := by ring

lemma DDg_le (n : ℕ) : DDg n ≤ 37 ^ 14 * (n + 1) ^ 14 := by
  have : DDg n ≤ (37 * (n + 1)) * (37 * (n + 1)) ^ 2 * (37 * (n + 1)) * (37 * (n + 1)) *
      (37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) * (37 * (n + 1)) *
      (37 * (n + 1)) ^ 2 * (37 * (n + 1)) * (37 * (n + 1)) := by
    unfold DDg; gcongr <;> omega
  calc DDg n ≤ _ := this
    _ = _ := by ring

lemma log_le_of_nat_le (a c k n : ℕ) (ha : 0 < a) (hc : 0 < c) (h : a ≤ c * (n + 1) ^ k) :
    Real.log a ≤ Real.log c + k * Real.log (n + 1) := by
  have h' : (a : ℝ) ≤ c * ((n : ℝ) + 1) ^ k := by exact_mod_cast h
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc Real.log a ≤ Real.log (c * ((n : ℝ) + 1) ^ k) :=
        Real.log_le_log (by exact_mod_cast ha) h'
    _ = _ := by rw [Real.log_mul hc'.ne' (pow_pos hn k).ne', Real.log_pow]

/-- the mass bound, with an explicit nonnegative constant -/
lemma gfunX_mass : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∑ q ∈ S, |(padicValRat q (gfunX n / gfunX 0) : ℝ)| * Real.log q ≤ C * Real.log (n + 1) := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Real.log ((420 * 37 ^ 6 : ℕ) : ℝ) + Real.log ((37 ^ 14 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hK : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ Real.log ((420 * 37 ^ 6 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log ((37 ^ 14 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K / Real.log 2 + 20, by positivity, fun n hn S hS => ?_⟩
  rw [gfun_ratio]
  have hm := mass_div (420 * NNg n) (DDg n) (by have := NNg_pos n; omega) (DDg_pos n) S hS
  have ha := log_le_of_nat_le _ _ 6 n (by have := NNg_pos n; omega) (by norm_num) (NNg_le n)
  have hb := log_le_of_nat_le _ _ 14 n (DDg_pos n) (by norm_num) (DDg_le n)
  simp only [Nat.cast_ofNat] at ha hb
  have hn2 : Real.log 2 ≤ Real.log (n + 1) :=
    Real.log_le_log (by norm_num) (by have : (1 : ℝ) ≤ n := (by exact_mod_cast hn); linarith)
  have hKl : K ≤ K / Real.log 2 * Real.log (n + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hn2 hK
  linarith

lemma gfunX_val_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ q : ℕ, q.Prime →
    |(padicValRat q (gfunX n / gfunX 0) : ℝ)| * Real.log q ≤ C * Real.log (n + 1) := by
  obtain ⟨C, hC, h⟩ := gfunX_mass
  refine ⟨C, hC, fun n hn q hq => ?_⟩
  simpa using h n hn {q} (by simpa using hq)

/-! ### The truncation level `K = ⌊log_q (72 n)⌋ + 1` -/

lemma lt_pow_K (q n : ℕ) (hq : 1 < q) : 72 * n < q ^ (Nat.log q (72 * n) + 1) :=
  Nat.lt_pow_succ_log_self hq _

lemma K_le (q n : ℕ) (hq : 1 < q) (hn : 1 ≤ n) :
    ((Nat.log q (72 * n) + 1 : ℕ) : ℝ) ≤ Real.log (72 * n) / Real.log q + 1 := by
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hpow : q ^ Nat.log q (72 * n) ≤ 72 * n := Nat.pow_log_le_self q (by omega)
  have h1 : (Nat.log q (72 * n) : ℝ) * Real.log q ≤ Real.log (72 * n) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  push_cast
  have : (Nat.log q (72 * n) : ℝ) ≤ Real.log (72 * n) / Real.log q := by
    rw [le_div_iff₀ hlq]; exact h1
  linarith

/-! ### Lower bounds for the gamma part -/

/-- per-family lower bound for `m v_q((β)_{An})` -/
noncomputable def LBt (q K n : ℕ) (t : ℕ × ℕ × ℤ) : ℝ :=
  if q ∣ t.1 then (t.2.2 : ℝ) * (-(((t.2.1 * n : ℕ) : ℝ) * padicValNat q t.1))
  else (t.2.2 : ℝ) * (((t.2.1 * n : ℕ) : ℝ) * Gs q K) - K

def gammaD : List (ℕ × ℕ × ℤ) :=
  [(3, 12, -1), (1, 8, 1), (3, 5, -1), (3, 8, 1), (1, 6, -1), (1, 5, 1), (6, 4, 1), (2, 9, -1),
   (3, 6, 1), (3, 5, 1), (3, 4, -1)]

lemma gammaF_proj : gammaF.map (fun fm => (fm.1.be.den, fm.1.la, fm.2)) = gammaD := by
  decide +kernel

lemma gamma_lower (q : ℕ) [Fact q.Prime] (n : ℕ) :
    (gammaD.map (LBt q (Nat.log q (72 * n) + 1) n)).sum ≤
      (gammaF.map fun fm => (fm.2 : ℝ) * padicValRat q (rf fm.1.be (fm.1.la * n))).sum := by
  rw [← gammaF_proj, List.map_map]
  apply list_sum_map_le
  intro fm hfm
  have hgood := gammaF_good fm hfm
  have hpm := gammaF_pm fm hfm
  simp only [Function.comp, LBt]
  split_ifs with hd
  · rw [fam_exact q fm.1 hgood n hd]
  · have := fam_dev q fm.1 hgood n _ (lt_pow_K q n (Fact.out : q.Prime).one_lt) hd
    rw [abs_le] at this
    obtain ⟨t1, t2⟩ := this
    push_cast at t1 t2 ⊢
    rcases hpm with h | h <;> rw [h] <;> push_cast <;> linarith

lemma pv22 : padicValNat 2 2 = 1 := padicValNat_self
lemma pv33 : padicValNat 3 3 = 1 := padicValNat_self
lemma pv26 : padicValNat 2 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), pv22,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
lemma pv36 : padicValNat 3 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num), pv33,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

lemma gammaD_two (n K : ℕ) : (gammaD.map (LBt 2 K n)).sum =
    5 * (n : ℝ) + 5 * ((n : ℝ) * Gs 2 K) - 9 * K := by
  simp only [gammaD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LBt]
  norm_num [pv22, pv26]
  ring

lemma gammaD_three (n K : ℕ) : (gammaD.map (LBt 3 K n)).sum =
    -2 * (n : ℝ) - 2 * ((n : ℝ) * Gs 3 K) - 4 * K := by
  simp only [gammaD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LBt]
  norm_num [pv33, pv36]
  ring

lemma gammaD_big (p : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) (n K : ℕ) :
    (gammaD.map (LBt p K n)).sum = -11 * (K : ℝ) := by
  have h1 : ¬ p ∣ 1 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h6 : ¬ p ∣ 6 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 by simpa using h) with h | h
    · exact h2 h
    · exact h3 h
  simp only [gammaD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LBt, h1, h2, h3, h6,
    ite_false]
  push_cast
  ring

theorem padicValRat_DeltaX (n p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hbig : 144 * n + 24 < p ^ 2) :
    padicValRat p (Δ n) = padicValRat p (gfunX n / gfunX 0) +
      (gammaF.map (fun fm => fm.2 * ((fm.1.hi (p % 6)).floorAt n p 0 -
        (fm.1.lo (p % 6)).floorAt n p 0))).sum := by
  have hC : C0X ≠ 0 := by norm_num [C0X]
  have hg : gfunX n / gfunX 0 ≠ 0 := div_ne_zero (gfunX_pos n).ne' (gfunX_pos 0).ne'
  rw [Delta_gammaX, padicValRat.mul (mul_ne_zero (pow_ne_zero _ hC) hg) (gamma_prod_ne n),
    padicValRat.mul (pow_ne_zero _ hC) hg, padicValRat.pow, val_C0_big p hp5, mul_zero, zero_add,
    padicValRat_list_prod p _ (fun x hx => by
      obtain ⟨fm, hfm, rfl⟩ := List.mem_map.1 hx
      exact zpow_ne_zero _ (rf_ne_zero fm.1 (gammaF_good fm hfm).2.2.1 _)), List.map_map]
  congr 2
  apply List.map_congr_left
  intro fm hfm
  simp only [Function.comp, padicValRat.zpow]
  rw [fam_count fm.1 (gammaF_good fm hfm) n p hp5 hbig]

/-! ### The small-prime bounds -/

lemma log_facts (n : ℕ) (hn : 2 ≤ n) :
    Real.log 2 ≤ Real.log n ∧ Real.log (n + 1) ≤ 2 * Real.log n ∧
      Real.log (72 * n) = Real.log 72 + Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.log_le_log (by norm_num) hn', ?_, ?_⟩
  · rw [show (2 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith)
  · rw [Real.log_mul (by norm_num) (by positivity)]

theorem delta_val_twoX : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    18 * (n : ℝ) - C * Real.log n ≤ padicValRat 2 (Δ n) := by
  obtain ⟨C1, hC1, hg⟩ := gfunX_val_bound
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.log 72 / Real.log 2 := ⟨_, rfl⟩
  have hB : 0 ≤ B := hBdef ▸ div_nonneg (Real.log_nonneg (by norm_num)) hl2.le
  refine ⟨(2 * C1 + 23 + 9 * B) / Real.log 2, fun n hn => ?_⟩
  obtain ⟨hL, hL1, hL72⟩ := log_facts n hn
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.log n / Real.log 2 := ⟨_, rfl⟩
  have hA : 1 ≤ A := by rw [hAdef, le_div_iff₀ hl2]; linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = Nat.log 2 (72 * n) + 1 := ⟨_, rfl⟩
  rw [val_Delta, val_C0_two]
  have hsum := gamma_lower 2 n
  rw [← hKdef, gammaD_two] at hsum
  have hgn := hg n (by omega) 2 Nat.prime_two
  push_cast at hgn
  have hvg : -(2 * C1) * A ≤ (padicValRat 2 (gfunX n / gfunX 0) : ℝ) := by
    have h1 := neg_abs_le (padicValRat 2 (gfunX n / gfunX 0) : ℝ)
    have h2 : |(padicValRat 2 (gfunX n / gfunX 0) : ℝ)| * Real.log 2 ≤ 2 * C1 * Real.log n := by
      have := mul_le_mul_of_nonneg_left hL1 hC1
      linarith
    have h3 : |(padicValRat 2 (gfunX n / gfunX 0) : ℝ)| ≤ 2 * C1 * A := by
      rw [show 2 * C1 * A = 2 * C1 * Real.log n / Real.log 2 by rw [hAdef]; ring,
        le_div_iff₀ hl2]
      exact h2
    linarith
  have hK := K_le 2 n (by norm_num) (by omega)
  simp only [Nat.cast_ofNat] at hK
  rw [← hKdef, hL72, add_div, ← hBdef, ← hAdef] at hK
  have hpow : (72 * n : ℝ) < 2 ^ K := by
    have := lt_pow_K 2 n (by norm_num)
    rw [← hKdef] at this
    exact_mod_cast this
  have hnG : (n : ℝ) - 1 ≤ (n : ℝ) * Gs 2 K := by
    have hp : (0 : ℝ) < 2 ^ K := by positivity
    have h1 : (n : ℝ) / 2 ^ K ≤ 1 := (div_le_one hp).2 (by linarith)
    rw [Gs_eq 2 (by norm_num) K]
    have h2 : (n : ℝ) * ((1 - 1 / 2 ^ K) / (2 - 1)) = n - n / 2 ^ K := by ring
    rw [h2]; linarith
  have hBA : B ≤ B * A := le_mul_of_one_le_right hB hA
  have hCeq : (2 * C1 + 23 + 9 * B) / Real.log 2 * Real.log n =
      2 * C1 * A + 23 * A + 9 * (B * A) := by
    rw [hAdef]; field_simp
  rw [hCeq]
  push_cast at hsum ⊢
  linarith

theorem delta_val_threeX : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    27 * (n : ℝ) - C * Real.log n ≤ padicValRat 3 (Δ n) := by
  obtain ⟨C1, hC1, hg⟩ := gfunX_val_bound
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.log 72 / Real.log 2 := ⟨_, rfl⟩
  have hB : 0 ≤ B := hBdef ▸ div_nonneg (Real.log_nonneg (by norm_num)) hl2.le
  refine ⟨(2 * C1 + 8 + 4 * B) / Real.log 2, fun n hn => ?_⟩
  obtain ⟨hL, hL1, hL72⟩ := log_facts n hn
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.log n / Real.log 2 := ⟨_, rfl⟩
  have hA : 1 ≤ A := by rw [hAdef, le_div_iff₀ hl2]; linarith
  have hlnn : 0 ≤ Real.log n := by linarith
  have hA3 : Real.log n / Real.log 3 ≤ A := hAdef ▸ div_le_div_of_nonneg_left hlnn hl2 hl3
  have hB3 : Real.log 72 / Real.log 3 ≤ B :=
    hBdef ▸ div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hl2 hl3
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = Nat.log 3 (72 * n) + 1 := ⟨_, rfl⟩
  rw [val_Delta, val_C0_three]
  have hsum := gamma_lower 3 n
  rw [← hKdef, gammaD_three] at hsum
  have hgn := hg n (by omega) 3 Nat.prime_three
  push_cast at hgn
  have hvg : -(2 * C1) * A ≤ (padicValRat 3 (gfunX n / gfunX 0) : ℝ) := by
    have h1 := neg_abs_le (padicValRat 3 (gfunX n / gfunX 0) : ℝ)
    have h2 : |(padicValRat 3 (gfunX n / gfunX 0) : ℝ)| * Real.log 2 ≤ 2 * C1 * Real.log n := by
      have := mul_le_mul_of_nonneg_left hL1 hC1
      have := mul_le_mul_of_nonneg_left hl3 (abs_nonneg (padicValRat 3 (gfunX n / gfunX 0) : ℝ))
      linarith
    have h3 : |(padicValRat 3 (gfunX n / gfunX 0) : ℝ)| ≤ 2 * C1 * A := by
      rw [show 2 * C1 * A = 2 * C1 * Real.log n / Real.log 2 by rw [hAdef]; ring,
        le_div_iff₀ hl2]
      exact h2
    linarith
  have hK := K_le 3 n (by norm_num) (by omega)
  simp only [Nat.cast_ofNat] at hK
  rw [← hKdef, hL72, add_div] at hK
  have hnG : (n : ℝ) * Gs 3 K ≤ (n : ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_left (Gs_le 3 (by norm_num) K) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h2 : (n : ℝ) * (1 / (3 - 1)) = n / 2 := by ring
    linarith
  have hBA : B ≤ B * A := le_mul_of_one_le_right hB hA
  have hCeq : (2 * C1 + 8 + 4 * B) / Real.log 2 * Real.log n =
      2 * C1 * A + 8 * A + 4 * (B * A) := by
    rw [hAdef]; field_simp
  rw [hCeq]
  push_cast at hsum ⊢
  linarith

theorem delta_val_smallX : ∃ C : ℝ, ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p →
    -C * (Real.log n / Real.log p + 1) ≤ padicValRat p (Δ n) := by
  obtain ⟨C1, hC1, hg⟩ := gfunX_val_bound
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Real.log 72 / Real.log 2 := ⟨_, rfl⟩
  have hB : 0 ≤ B := hBdef ▸ div_nonneg (Real.log_nonneg (by norm_num)) hl2.le
  refine ⟨2 * C1 + 11 + 11 * B, fun n p hn hp hp5 => ?_⟩
  haveI := Fact.mk hp
  obtain ⟨hL, hL1, hL72⟩ := log_facts n hn
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlp2 : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Real.log n / Real.log p := ⟨_, rfl⟩
  have hA : 0 ≤ A := hAdef ▸ div_nonneg (by linarith) hlp.le
  have hBp : Real.log 72 / Real.log p ≤ B :=
    hBdef ▸ div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hl2 hlp2
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = Nat.log p (72 * n) + 1 := ⟨_, rfl⟩
  rw [val_Delta, val_C0_big p hp5, ← hAdef]
  have hsum := gamma_lower p n
  rw [← hKdef, gammaD_big p hp5 hp] at hsum
  have hgn := hg n (by omega) p hp
  have hvg : -(2 * C1) * A ≤ (padicValRat p (gfunX n / gfunX 0) : ℝ) := by
    have h1 := neg_abs_le (padicValRat p (gfunX n / gfunX 0) : ℝ)
    have h2 : |(padicValRat p (gfunX n / gfunX 0) : ℝ)| * Real.log p ≤ 2 * C1 * Real.log n := by
      have := mul_le_mul_of_nonneg_left hL1 hC1
      linarith
    have h3 : |(padicValRat p (gfunX n / gfunX 0) : ℝ)| ≤ 2 * C1 * A := by
      rw [show 2 * C1 * A = 2 * C1 * Real.log n / Real.log p by rw [hAdef]; ring,
        le_div_iff₀ hlp]
      exact h2
    linarith
  have hK := K_le p n hp.one_lt (by omega)
  rw [← hKdef, hL72, add_div, ← hAdef] at hK
  have hBA : 0 ≤ B * A := mul_nonneg hB hA
  push_cast at hsum ⊢
  linarith

end Zeta2L2Chi3.Arith

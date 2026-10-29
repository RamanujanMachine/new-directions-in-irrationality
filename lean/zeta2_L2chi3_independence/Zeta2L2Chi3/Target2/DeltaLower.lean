/-
# Lower bound for `log Δ_n`

From `Δ_n = C₀ⁿ (g(n)/g(0)) ∏ ((β)_{An})^m` (`Delta_gamma`), the elementary Stirling bounds for
rising factorials (`Stirling.lean`), `Σ m A = 0` and `log C₀ + Σ m A log A = 32 log 2 + 5 log 5`:
`log Δ_n ≥ n (32 log 2 + 5 log 5) - C (log (13 n + 1) + 1)`.
-/
import Zeta2L2Chi3.Arith.DeltaVal
import Zeta2L2Chi3.Target2.PhiNum

namespace Zeta2L2Chi3.Arith

open Real Finset Filter

lemma rf_cast_real (β : ℚ) (N : ℕ) : ((rf β N : ℚ) : ℝ) = ∏ i ∈ range N, ((β : ℝ) + i) := by
  simp [rf]

lemma rf_pos_rat (β : ℚ) (hβ : 0 < β) (N : ℕ) : 0 < rf β N :=
  prod_pos fun i _ => by positivity

/-- `K β = |log β| + |LF β|` -/
noncomputable def Kc (β : ℝ) : ℝ := |Real.log β| + |LF β|

lemma Kc_nonneg (β : ℝ) : 0 ≤ Kc β := by unfold Kc; positivity

lemma log_rf_close (β : ℝ) (h0 : 0 < β) (h1 : β ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    |Real.log (∏ i ∈ range N, (β + i)) - LF N| ≤ Real.log (N + 1) + 1 + Kc β := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu := log_prod_upper β h0 N
  have hl := log_prod_lower' β h0 N hN
  have c1 := LF_close (X := β + N) (Y := N) (c := 1) (M := N + 1) (by linarith) (by linarith)
    (by rw [show β + N - N = β by ring, abs_of_pos h0]; exact h1) (by linarith) (by linarith)
    (by linarith)
  have c2 := LF_close (X := β + N - 1) (Y := N) (c := 1) (M := N + 1) (by linarith) (by linarith)
    (by rw [show β + N - 1 - N = β - 1 by ring, abs_le]; constructor <;> linarith) (by linarith)
    (by linarith) (by linarith)
  unfold Kc
  rw [abs_le] at c1 c2 ⊢
  have a1 := le_abs_self (Real.log β)
  have a2 := neg_abs_le (Real.log β)
  have a3 := le_abs_self (LF β)
  have a4 := neg_abs_le (LF β)
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2]

lemma log_list_prod (L : List (Fam × ℤ)) (n : ℕ) (hL : ∀ fm ∈ L, 0 < fm.1.be) :
    Real.log ((((L.map (fun fm => (rf fm.1.be (fm.1.la * n)) ^ fm.2)).prod : ℚ) : ℝ)) =
      (L.map (fun fm => (fm.2 : ℝ) * Real.log (((rf fm.1.be (fm.1.la * n) : ℚ) : ℝ)))).sum ∧
    0 < (L.map (fun fm => (rf fm.1.be (fm.1.la * n)) ^ fm.2)).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun fm h => hL fm (List.mem_cons_of_mem _ h))
    have ha := rf_pos_rat a.1.be (hL a (List.mem_cons_self)) (a.1.la * n)
    have hz : 0 < rf a.1.be (a.1.la * n) ^ a.2 := zpow_pos ha _
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨?_, mul_pos hz ih2⟩
    rw [Rat.cast_mul, Real.log_mul (by exact_mod_cast hz.ne') (by exact_mod_cast ih2.ne'), ih1,
      Rat.cast_zpow, Real.log_zpow]

/-- termwise main part -/
noncomputable def mainT (n : ℕ) (fm : Fam × ℤ) : ℝ :=
  (fm.2 : ℝ) * ((fm.1.la : ℝ) * n * Real.log n + n * LF fm.1.la)

lemma gamma_facts : ∀ fm ∈ gammaF, (0 < fm.1.be ∧ fm.1.be ≤ 1) ∧ (1 ≤ fm.1.la ∧ fm.1.la ≤ 12) ∧
    (fm.2 = 1 ∨ fm.2 = -1) := by
  simp only [gammaF, List.mem_cons, List.not_mem_nil, or_false]
  rintro fm (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> (try norm_num)

lemma dl_term_lower (n : ℕ) (hn : 1 ≤ n) (fm : Fam × ℤ) (hfm : fm ∈ gammaF) :
    mainT n fm - (Real.log (13 * n + 1) + 1 + Kc fm.1.be) ≤
      (fm.2 : ℝ) * Real.log (((rf fm.1.be (fm.1.la * n) : ℚ) : ℝ)) := by
  obtain ⟨⟨hb0, hb1⟩, ⟨hA1, hA12⟩, hm⟩ := gamma_facts fm hfm
  have hb0' : (0 : ℝ) < fm.1.be := by exact_mod_cast hb0
  have hb1' : (fm.1.be : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hN : 1 ≤ fm.1.la * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h := log_rf_close (fm.1.be : ℝ) hb0' hb1' (fm.1.la * n) hN
  rw [← rf_cast_real] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hLF : LF ((fm.1.la * n : ℕ) : ℝ) = (fm.1.la : ℝ) * n * Real.log n + n * LF fm.1.la := by
    push_cast
    rw [mul_comm (fm.1.la : ℝ) n, LF_mul n _ hn0]
  rw [hLF] at h
  have hlog : Real.log (((fm.1.la * n : ℕ) : ℝ) + 1) ≤ Real.log (13 * n + 1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    have : (fm.1.la : ℝ) ≤ 12 := by exact_mod_cast hA12
    nlinarith
  unfold mainT
  rw [abs_le] at h
  rcases hm with hm | hm <;> rw [hm] <;> push_cast <;> linarith [h.1, h.2]

lemma gamma_sum_main (n : ℕ) :
    (gammaF.map (mainT n)).sum = n * (24 * Real.log 2 - 30 * Real.log 3 + 5 * Real.log 5) := by
  simp only [gammaF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mainT, LF]
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  push_cast
  rw [l4, l6, l8, l9, l12]
  ring

lemma gamma_sum_err (n : ℕ) :
    (gammaF.map (fun fm => Real.log (13 * n + 1) + 1 + Kc fm.1.be)).sum =
      11 * (Real.log (13 * n + 1) + 1) + (gammaF.map (fun fm => Kc fm.1.be)).sum := by
  simp only [gammaF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

lemma gamma_sumK_nonneg : 0 ≤ (gammaF.map (fun fm => Kc fm.1.be)).sum := by
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨fm, -, rfl⟩ := List.mem_map.1 hx
  exact Kc_nonneg _

lemma gfun_lower (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (3 * (13 * n + 1)) ^ 14 ≤ ((gfun n : ℚ) : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold gfun
  push_cast
  set x : ℝ := (n : ℝ)
  set T : ℝ := 3 * (13 * x + 1) with hT
  have hden : (2 * x + 1) * (3 * x + 1) ^ 2 * (6 * x + 1) * (8 * x + 3) * (9 * x + 2) * (10 * x + 3) *
      (12 * x + 1) * (15 * x + 1) * (15 * x + 4) * (18 * x + 1) ^ 2 * (24 * x + 5) * (30 * x + 7) ≤
      T * T ^ 2 * T * T * T * T * T * T * T * T ^ 2 * T * T := by
    gcongr <;> linarith
  have hnum : 1 ≤ 3936600 * (8 * x + 1) * (9 * x + 1) * (15 * x + 2) * (20 * x + 3) * (24 * x + 1) ^ 2 := by
    have h1 : 1 ≤ (8 * x + 1) * (9 * x + 1) := by nlinarith
    have h2 : 1 ≤ (8 * x + 1) * (9 * x + 1) * (15 * x + 2) := by nlinarith
    have h3 : 1 ≤ (8 * x + 1) * (9 * x + 1) * (15 * x + 2) * (20 * x + 3) := by nlinarith
    have h4 : 1 ≤ (24 * x + 1) ^ 2 := by nlinarith
    nlinarith
  have hT14 : T * T ^ 2 * T * T * T * T * T * T * T * T ^ 2 * T * T = T ^ 14 := by ring
  rw [hT14] at hden
  have hTpos : 0 < T ^ 14 := by positivity
  have hdpos : 0 < (2 * x + 1) * (3 * x + 1) ^ 2 * (6 * x + 1) * (8 * x + 3) * (9 * x + 2) * (10 * x + 3) *
      (12 * x + 1) * (15 * x + 1) * (15 * x + 4) * (18 * x + 1) ^ 2 * (24 * x + 5) * (30 * x + 7) := by
    positivity
  rw [div_le_div_iff₀ hTpos hdpos]
  nlinarith

lemma log_gratio_lower (n : ℕ) (hn : 1 ≤ n) :
    -14 * Real.log (13 * n + 1) - 9400 ≤ Real.log (((gfun n / gfun 0 : ℚ) : ℝ)) := by
  have hg0 : ((gfun 0 : ℚ) : ℝ) = 65610 / 7 := by
    have : gfun 0 = 65610 / 7 := by norm_num [gfun]
    rw [this]; push_cast; ring
  have hgpos : (0 : ℝ) < ((gfun n : ℚ) : ℝ) := by exact_mod_cast gfun_pos n
  have hl := gfun_lower n hn
  have hT : (0 : ℝ) < 3 * (13 * n + 1) := by positivity
  rw [Rat.cast_div, hg0, Real.log_div hgpos.ne' (by norm_num)]
  have h1 := Real.log_le_log (by positivity) hl
  rw [one_div, Real.log_inv, Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h1
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h4 : Real.log (65610 / 7 : ℝ) ≤ 9372 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 65610 / 7 by norm_num); linarith
  push_cast at h1
  linarith

theorem log_Delta_bound : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    n * (32 * Real.log 2 + 5 * Real.log 5) - C * (Real.log (13 * n + 1) + 1) ≤ Real.log (Δ n : ℝ) := by
  refine ⟨9400 + 14 + 11 + (gammaF.map (fun fm => Kc fm.1.be)).sum, fun n hn => ?_⟩
  have hbe : ∀ fm ∈ gammaF, 0 < fm.1.be := fun fm h => (gamma_facts fm h).1.1
  obtain ⟨hlogP, hP⟩ := log_list_prod gammaF n hbe
  have hC0 : (C0 : ℝ) = 2 ^ 8 * 3 ^ 30 := by unfold C0; push_cast; ring
  have hg : (0 : ℚ) < gfun n / gfun 0 := div_pos (gfun_pos n) (gfun_pos 0)
  rw [Delta_gamma n, Rat.cast_mul, Rat.cast_mul,
    Real.log_mul (by exact_mod_cast (mul_pos (pow_pos (by norm_num [C0]) n) hg).ne')
      (by exact_mod_cast hP.ne'),
    Real.log_mul (by push_cast; rw [hC0]; positivity) (by exact_mod_cast hg.ne'), hlogP]
  have hlC0 : Real.log (((C0 ^ n : ℚ)) : ℝ) = n * (8 * Real.log 2 + 30 * Real.log 3) := by
    push_cast
    rw [hC0, Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hlC0]
  have hsum : (gammaF.map (fun fm => mainT n fm - (Real.log (13 * n + 1) + 1 + Kc fm.1.be))).sum ≤
      (gammaF.map (fun fm => (fm.2 : ℝ) * Real.log (((rf fm.1.be (fm.1.la * n) : ℚ) : ℝ)))).sum :=
    List.sum_le_sum (fun fm hfm => dl_term_lower n hn fm hfm)
  have hsplit : (gammaF.map (fun fm => mainT n fm - (Real.log (13 * n + 1) + 1 + Kc fm.1.be))).sum =
      (gammaF.map (mainT n)).sum -
        (gammaF.map (fun fm => Real.log (13 * n + 1) + 1 + Kc fm.1.be)).sum := by
    simp only [gammaF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  rw [hsplit, gamma_sum_main, gamma_sum_err] at hsum
  have hgr := log_gratio_lower n hn
  have hK := gamma_sumK_nonneg
  have hl0 : 0 ≤ Real.log (13 * n + 1) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ n from n.cast_nonneg])
  nlinarith

theorem log_Delta_lower' : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (30227899 / 10 ^ 6 - ε) * n ≤ Real.log (Δ n : ℝ) := by
  intro ε hε
  obtain ⟨C, hC⟩ := log_Delta_bound
  filter_upwards [eventually_log_small C ε 13 1 hε (by norm_num) (by norm_num), eventually_ge_atTop 1]
    with n h1 hn
  have h := hC n hn
  have hs := sigma_lower
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

end Zeta2L2Chi3.Arith

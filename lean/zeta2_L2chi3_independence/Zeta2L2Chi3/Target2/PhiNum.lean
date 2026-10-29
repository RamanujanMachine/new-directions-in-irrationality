/-
# The saddle exponent `φ` and the numerical constants

`φ(y) = Σ ± z log z` over the linear forms `y+12, y+6, y+5 | 2(y+2), 2y, 10-y, y+1, 8-y` is the
exponential rate of the double-pole weight `N(k)/D_k(k)` at `k = y n`.  We prove
* `φ` is monotone on `[0, Y]`, `Y = 6.1302 < y* ≈ 6.1302067` (`φ' = log ρ`, `ρ ≥ 1` there);
* `φ(6.13) ≥ 32.9081395`, `φ(4.4) ≤ 31.2`;
* `σ_det = 32 log 2 + 5 log 5 > 30.227899`.
-/
import Zeta2L2Chi3.Target2.Stirling
import Zeta2L2Chi3.Numerics

namespace Zeta2L2Chi3.Arith

open Real Finset Filter

/-- `z log z` -/
noncomputable def xl (z : ℝ) : ℝ := z * Real.log z

/-- the saddle exponent -/
noncomputable def phi (y : ℝ) : ℝ :=
  xl (y + 12) + xl (y + 6) + xl (y + 5) - 2 * xl (y + 2) - 2 * xl y - xl (10 - y) - xl (y + 1) -
    xl (8 - y)

lemma phi_eq_LF (y : ℝ) : phi y = LF (y + 12) + LF (y + 6) + LF (y + 5) - 2 * LF (y + 2) - 2 * LF y -
    LF (10 - y) - LF (y + 1) - LF (8 - y) := by
  unfold phi xl LF; ring

lemma continuous_xl : Continuous xl := Real.continuous_mul_log

lemma continuous_phi : Continuous phi := by
  have h := continuous_xl
  unfold phi
  refine ((((((((h.comp (continuous_id.add continuous_const)).add
    (h.comp (continuous_id.add continuous_const))).add
    (h.comp (continuous_id.add continuous_const))).sub
    (continuous_const.mul (h.comp (continuous_id.add continuous_const)))).sub
    (continuous_const.mul h)).sub (h.comp (continuous_const.sub continuous_id))).sub
    (h.comp (continuous_id.add continuous_const))).sub (h.comp (continuous_const.sub continuous_id)))

lemma xl_hasDerivAt {z : ℝ} (hz : z ≠ 0) : HasDerivAt xl (Real.log z + 1) z :=
  Real.hasDerivAt_mul_log hz

lemma xl_add_hasDerivAt (c y : ℝ) (h : y + c ≠ 0) :
    HasDerivAt (fun y => xl (y + c)) (Real.log (y + c) + 1) y := by
  have h2 : HasDerivAt (fun y => y + c) 1 y := (hasDerivAt_id y).add_const c
  have := (xl_hasDerivAt h).comp y h2
  simpa [Function.comp_def] using this

lemma xl_sub_hasDerivAt (c y : ℝ) (h : c - y ≠ 0) :
    HasDerivAt (fun y => xl (c - y)) (-(Real.log (c - y) + 1)) y := by
  have h2 : HasDerivAt (fun y => c - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub c
  have := (xl_hasDerivAt h).comp y h2
  simpa [Function.comp_def] using this

lemma phi_hasDerivAt (y : ℝ) (h0 : 0 < y) (h8 : y < 8) :
    HasDerivAt phi (Real.log (y + 12) + Real.log (y + 6) + Real.log (y + 5) + Real.log (10 - y) +
      Real.log (8 - y) - 2 * Real.log (y + 2) - 2 * Real.log y - Real.log (y + 1)) y := by
  have d1 := xl_add_hasDerivAt 12 y (by linarith)
  have d2 := xl_add_hasDerivAt 6 y (by linarith)
  have d3 := xl_add_hasDerivAt 5 y (by linarith)
  have d4 := xl_add_hasDerivAt 2 y (by linarith)
  have d5 := xl_hasDerivAt (z := y) (by linarith)
  have d6 := xl_sub_hasDerivAt 10 y (by linarith)
  have d7 := xl_add_hasDerivAt 1 y (by linarith)
  have d8 := xl_sub_hasDerivAt 8 y (by linarith)
  have := ((((((d1.add d2).add d3).sub (d4.const_mul 2)).sub (d5.const_mul 2)).sub d6).sub d7).sub d8
  convert this using 1
  · funext z
    simp only [Pi.add_apply, Pi.sub_apply]
    unfold phi
    ring
  · ring

/-- the upper end of the monotonicity interval (just below `y* = 6.13020674…`) -/
noncomputable def Ytop : ℝ := 30651 / 5000

lemma phi_deriv_nonneg (y : ℝ) (h0 : 0 < y) (hY : y < Ytop) :
    0 ≤ Real.log (y + 12) + Real.log (y + 6) + Real.log (y + 5) + Real.log (10 - y) +
      Real.log (8 - y) - 2 * Real.log (y + 2) - 2 * Real.log y - Real.log (y + 1) := by
  unfold Ytop at hY
  have hnum : Real.log (y + 12) + Real.log (y + 6) + Real.log (y + 5) + Real.log (10 - y) +
      Real.log (8 - y) = Real.log ((y + 12) * (y + 6) * (y + 5) * (10 - y) * (8 - y)) := by
    have a1 : 0 < y + 12 := by linarith
    have a2 : 0 < y + 6 := by linarith
    have a3 : 0 < y + 5 := by linarith
    have a4 : 0 < 10 - y := by linarith
    have a5 : 0 < 8 - y := by linarith
    rw [Real.log_mul (mul_pos (mul_pos (mul_pos a1 a2) a3) a4).ne' a5.ne',
      Real.log_mul (mul_pos (mul_pos a1 a2) a3).ne' a4.ne', Real.log_mul (mul_pos a1 a2).ne' a3.ne',
      Real.log_mul a1.ne' a2.ne']
  have hden : 2 * Real.log (y + 2) + 2 * Real.log y + Real.log (y + 1) =
      Real.log ((y + 2) ^ 2 * y ^ 2 * (y + 1)) := by
    rw [Real.log_mul, Real.log_mul, Real.log_pow, Real.log_pow] <;> first | positivity | push_cast; ring
  have hle : (y + 2) ^ 2 * y ^ 2 * (y + 1) ≤ (y + 12) * (y + 6) * (y + 5) * (10 - y) * (8 - y) := by
    have e : (y + 12) * (y + 6) * (y + 5) * (10 - y) * (8 - y) - (y + 2) ^ 2 * y ^ 2 * (y + 1) =
      180 * (160 + 36 * y - 4 * y ^ 2 - y ^ 3) := by ring
    have hg : 0 ≤ 160 + 36 * y - 4 * y ^ 2 - y ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg h0.le h0.le) (sub_nonneg.2 hY.le),
        mul_nonneg h0.le (sub_nonneg.2 hY.le), sub_nonneg.2 hY.le]
    linarith
  have := Real.log_le_log (by positivity) hle
  linarith

theorem phi_monotoneOn : MonotoneOn phi (Set.Icc 0 Ytop) := by
  have hY8 : Ytop < 8 := by unfold Ytop; norm_num
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 Ytop) continuous_phi.continuousOn
  · intro y hy
    rw [interior_Icc] at hy
    exact (phi_hasDerivAt y hy.1 (hy.2.trans hY8)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    rw [(phi_hasDerivAt y hy.1 (hy.2.trans hY8)).deriv]
    exact phi_deriv_nonneg y hy.1 hy.2

/-! ### Rigorous log brackets -/

theorem log_bracket (z : ℚ) (a m : ℕ) (lo hi : ℚ) (hz : 2 ^ a ≤ z)
    (hlo : lo ≤ a * (693147180559945 / 10 ^ 15) + logS m ((z / 2 ^ a - 1) / (z / 2 ^ a + 1)))
    (hhi : a * (693147180559946 / 10 ^ 15) + logS m ((z / 2 ^ a - 1) / (z / 2 ^ a + 1)) +
      logTail m ((z / 2 ^ a - 1) / (z / 2 ^ a + 1)) ≤ hi) :
    (lo : ℝ) ≤ Real.log (z : ℝ) ∧ Real.log (z : ℝ) ≤ hi := by
  have hpos : (0 : ℚ) < 2 ^ a := by positivity
  have hu : 1 ≤ z / 2 ^ a := by rw [le_div_iff₀ hpos]; simpa using hz
  have h := log_bounds_of (z / 2 ^ a) hu m _ rfl
  have hz0 : (0 : ℝ) < z := by
    have : (0 : ℚ) < z := lt_of_lt_of_le hpos hz
    exact_mod_cast this
  have hsplit : Real.log (z : ℝ) = Real.log (((z / 2 ^ a : ℚ) : ℝ)) + a * Real.log 2 := by
    push_cast
    rw [Real.log_div hz0.ne' (by positivity), Real.log_pow]
    ring
  have h2 := log_two_bounds
  have hlo' := (Rat.cast_le (K := ℝ)).2 hlo
  have hhi' := (Rat.cast_le (K := ℝ)).2 hhi
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at hlo'
  rw [Rat.cast_add, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at hhi'
  have c1 : (((693147180559945 / 10 ^ 15 : ℚ)) : ℝ) = 693147180559945 / 10 ^ 15 := by push_cast; ring
  have c2 : (((693147180559946 / 10 ^ 15 : ℚ)) : ℝ) = 693147180559946 / 10 ^ 15 := by push_cast; ring
  rw [c1] at hlo'
  rw [c2] at hhi'
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  rw [hsplit]
  constructor
  · nlinarith [h.1, h2.1]
  · nlinarith [h.2, h2.2]

theorem phi_a_lower : (329081395 / 10 ^ 7 : ℝ) ≤ phi (613 / 100) := by
  have h1 := log_bracket (1813 / 100) 4 20 (28975680247666 / 10 ^ 13) (28975680247669 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h2 := log_bracket (1213 / 100) 3 20 (24956817229558 / 10 ^ 13) (24956817229561 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h3 := log_bracket (1113 / 100) 3 20 (24096441652873 / 10 ^ 13) (24096441652876 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h4 := log_bracket (813 / 100) 3 20 (20955609235596 / 10 ^ 13) (20955609235599 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h5 := log_bracket (613 / 100) 2 20 (18131947499480 / 10 ^ 13) (18131947499483 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h6 := log_bracket (387 / 100) 1 20 (13532545070415 / 10 ^ 13) (13532545070418 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h7 := log_bracket (713 / 100) 2 20 (19643112344261 / 10 ^ 13) (19643112344264 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h8 := log_bracket (187 / 100) 0 20 (6259384308663 / 10 ^ 13) (6259384308666 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  push_cast at h1 h2 h3 h4 h5 h6 h7 h8
  unfold phi xl
  rw [show (613 / 100 : ℝ) + 12 = 1813 / 100 by norm_num, show (613 / 100 : ℝ) + 6 = 1213 / 100 by norm_num,
    show (613 / 100 : ℝ) + 5 = 1113 / 100 by norm_num, show (613 / 100 : ℝ) + 2 = 813 / 100 by norm_num,
    show (10 : ℝ) - 613 / 100 = 387 / 100 by norm_num, show (613 / 100 : ℝ) + 1 = 713 / 100 by norm_num,
    show (8 : ℝ) - 613 / 100 = 187 / 100 by norm_num]
  linarith [h1.1, h2.1, h3.1, h4.2, h5.2, h6.2, h7.2, h8.2]

theorem phi_b_upper : phi (22 / 5) ≤ 312 / 10 := by
  have h1 := log_bracket (82 / 5) 4 20 (27972813348300 / 10 ^ 13) (27972813348303 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h2 := log_bracket (52 / 5) 3 20 (23418058061472 / 10 ^ 13) (23418058061475 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h3 := log_bracket (47 / 5) 3 20 (22407096892758 / 10 ^ 13) (22407096892761 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h4 := log_bracket (32 / 5) 2 20 (18562979903655 / 10 ^ 13) (18562979903658 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h5 := log_bracket (22 / 5) 2 20 (14816045409241 / 10 ^ 13) (14816045409244 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h6 := log_bracket (28 / 5) 2 20 (17227665977410 / 10 ^ 13) (17227665977413 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h7 := log_bracket (27 / 5) 2 20 (16863989535701 / 10 ^ 13) (16863989535704 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  have h8 := log_bracket (18 / 5) 1 20 (12809338454619 / 10 ^ 13) (12809338454622 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  push_cast at h1 h2 h3 h4 h5 h6 h7 h8
  unfold phi xl
  rw [show (22 / 5 : ℝ) + 12 = 82 / 5 by norm_num, show (22 / 5 : ℝ) + 6 = 52 / 5 by norm_num,
    show (22 / 5 : ℝ) + 5 = 47 / 5 by norm_num, show (22 / 5 : ℝ) + 2 = 32 / 5 by norm_num,
    show (10 : ℝ) - 22 / 5 = 28 / 5 by norm_num, show (22 / 5 : ℝ) + 1 = 27 / 5 by norm_num,
    show (8 : ℝ) - 22 / 5 = 18 / 5 by norm_num]
  linarith [h1.2, h2.2, h3.2, h4.1, h5.1, h6.1, h7.1, h8.1]

theorem sigma_lower : (30227899 / 10 ^ 6 : ℝ) < 32 * Real.log 2 + 5 * Real.log 5 := by
  have h5 := log_bracket 5 2 20 (16094379124340 / 10 ^ 13) (16094379124343 / 10 ^ 13)
    (by norm_num) (by decide +kernel) (by decide +kernel)
  push_cast at h5
  have h2 := log_two_bounds
  linarith [h5.1, h2.1]

end Zeta2L2Chi3.Arith

/-
# The forward presentation: explicit rational coefficients and the large-prime bound

`fvecQ n` is the forward vector written with explicit rational partial-fraction coefficients
(double-pole coefficients `a_k = k^j N(k)/D_k(k)`, simple coefficients from the logarithmic
derivative, the explicit polynomial part, signed harmonic sums and Bernoulli polynomials).
For a prime `p ≥ 7` with `p² > 144n + 24`, `v_p(a_k) ≥ h(k mod p) + 2`, `v_p(b_k) ≥ h + 1`, the
harmonic sums cost at most `2` resp. `1`, and the polynomial part, Bernoulli terms and `K(n)` are
`p`-integral, so `v_p(f_n) ≥ min(0, min_r h(r))` (ARITHMETIC_ARGUMENT §5, (5.1)).
-/
import Zeta2L2Chi3.Arith.Family
import Zeta2L2Chi3.Arith.FwdRat
import Zeta2L2Chi3.Arith.FwdLarge2
import Zeta2L2Chi3.Arith.FwdSmallR
import Zeta2L2Chi3.FAssembly

namespace Zeta2L2Chi3.Arith

/-- the explicit rational forward vector (see `FwdRat.lean`: `fvecE` is built from the explicit
partial-fraction coefficients `aQ`, `bQ` (`FwdExplicit.lean`), the polynomial parts `qQ`
(`FwdPoly.lean`), the rational harmonic sums `HsigQ`, `ζ(-i, x)` (`zQ`) and `K(n) e₀` (`KQ`)) -/
noncomputable def fvecQ (n : ℕ) : Fin 3 → ℚ := fvecE n

theorem fvec_rat (n : ℕ) (i : Fin 3) : fvec n i = ((fvecQ n i : ℚ) : ℝ) := fvec_eq_cast n i

theorem fvecQ_eq (n : ℕ) (i : Fin 3) : fvecQ n i = (35 / 1944 : ℚ) * (Δ n)⁻¹ * w n i := by
  have h := (fvec_rat n i).symm.trans (fvec_eq n i)
  exact_mod_cast h

/-- the minimum packet excess of the forward kernel over all residue classes -/
def hminF (n p : ℕ) : ℤ :=
  ((List.range p).map (fun r => fwdH (fun E => ((endpts (fwdZ ++ fwdP) (p % 6))[E]!).floorAt n p r))).foldr min 0

theorem fwd_foldr_min_le (l : List ℤ) : ∀ x ∈ l, l.foldr min 0 ≤ x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih x hx)

theorem fwd_foldr_min_nonpos (l : List ℤ) : l.foldr min 0 ≤ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => exact (min_le_right _ _).trans ih

theorem hminF_le (n p r : ℕ) (hr : r < p) : hminF n p ≤ hF n p r :=
  fwd_foldr_min_le _ _ (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩)

theorem fwd_val (n p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hbig : 144 * n + 24 < p ^ 2) (i : Fin 3) :
    VGe p (min 0 (hminF n p)) (fvecQ n i) := by
  have hp5 : 5 ≤ p := by omega
  have key := fvecE_vge (p := p) n (min 0 (hminF n p)) (-2) (-1) 0 0
    (fun k => hF n p (k % p).toNat + 2) (fun k => hF n p (k % p).toNat + 1)
    (fun j _ k hk => aQ_vge hp5 n j hbig k hk) (fun j _ k hk => bQ_vge hp5 n j hbig k hk)
    (fun k hk m hm0 hm1 ρ hρ => ⟨by simpa using HsigQ_large hp5 n hbig k hk m hm0 hm1 ρ hρ 2,
      by simpa using HsigQ_large hp5 n hbig k hk m hm0 hm1 ρ hρ 1⟩)
    (fun j _ x hx => by simpa using UQ_vge le_rfl (six_large hp5) n j x hx)
    (fun j => KQ_vge (six_large hp5) n j)
    (fun k _ => by
      have := hminF_le n p _ (class_of (p := p) k).1
      have := min_le_right 0 (hminF n p)
      refine ⟨by omega, by omega, by omega⟩)
    (min_le_left _ _) i
  simpa [fvecQ] using key

/-- `p = 2`: Legendre counting (integer zeros `10n`, third zeros `6n`, half zeros `-3n`,
integer poles `-19n`) -/
theorem fwd_val_two : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, fvecQ n i ≠ 0 →
    -6 * (n : ℝ) - C * Real.log n ≤ padicValRat 2 (fvecQ n i) := by
  refine ⟨160, fun n hn i h0 => ?_⟩
  have h := fvecE_val_real 2 n hn i h0
  rw [lam_two] at h
  have hl := log_ge_half n hn
  have hl2 := Real.log_two_gt_d9
  have hX : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  show _ ≤ (padicValRat 2 (fvecE n i) : ℝ)
  push_cast at h
  linarith

/-- `p = 3`: contributions `5n, -6n, 3n/2, -19n/2` -/
theorem fwd_val_three : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ i, fvecQ n i ≠ 0 →
    -9 * (n : ℝ) - C * Real.log n ≤ padicValRat 3 (fvecQ n i) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨100, fun n hn i h0 => ?_⟩
  have h := fvecE_val_real 3 n hn i h0
  rw [lam_three] at h
  have hl := log_ge_half n hn
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := Real.exp_one_lt_d9; linarith
  have hX : Real.log n / Real.log 3 ≤ Real.log n :=
    div_le_self (by linarith) hl3.le
  show _ ≤ (padicValRat 3 (fvecE n i) : ℝ)
  push_cast at h
  linarith

/-- small primes: the linear terms cancel level by level -/
theorem fwd_val_small : ∃ C : ℝ, ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p → ∀ i, fvecQ n i ≠ 0 →
    -C * (Real.log n / Real.log p + 1) ≤ padicValRat p (fvecQ n i) := by
  refine ⟨80, fun n p hn hp hp5 i h0 => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have h := fvecE_val_real p n hn i h0
  rw [lam_ge_five p hp5] at h
  have hl := log_ge_half n hn
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hX : 0 ≤ Real.log n / Real.log p := div_nonneg (by linarith) hlp.le
  show _ ≤ (padicValRat p (fvecE n i) : ℝ)
  push_cast at h
  linarith

end Zeta2L2Chi3.Arith

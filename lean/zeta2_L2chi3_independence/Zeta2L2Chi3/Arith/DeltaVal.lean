/-
# The normalization scalar `Δ_n` : gamma factorization and valuations

`Δ_n = ∏_{j<n} det Q(j) = C₀ⁿ (g(n)/g(0)) ∏_{(A,β,m)} ((β)_{An})^m`, `C₀ = 2⁸ 3³⁰`, with the
explicit rational function `g` (ARITHMETIC_ARGUMENT §4).  For a prime `p ≥ 5` with
`p² > 144n + 24` each factor of `(β)_{An}` has valuation `≤ 1`, so `v_p((β)_{An})` is the number of
members of the family `β + i` in the residue class `0`, i.e. a difference of endpoint floors.
-/
import Zeta2L2Chi3.Arith.Family
import Zeta2L2Chi3.Matrices
import Zeta2L2Chi3.Dual
import Zeta2L2Chi3.Arith.DeltaBounds

namespace Zeta2L2Chi3.Arith

def C0 : ℚ := 2 ^ 8 * 3 ^ 30

/-- the rational function `g(n)` -/
def gfun (n : ℕ) : ℚ :=
  3936600 * (8 * n + 1) * (9 * n + 1) * (15 * n + 2) * (20 * n + 3) * (24 * n + 1) ^ 2 /
  ((2 * n + 1) * (3 * n + 1) ^ 2 * (6 * n + 1) * (8 * n + 3) * (9 * n + 2) * (10 * n + 3) *
    (12 * n + 1) * (15 * n + 1) * (15 * n + 4) * (18 * n + 1) ^ 2 * (24 * n + 5) * (30 * n + 7))

theorem gfun_pos (n : ℕ) : 0 < gfun n := gfunX_pos n

theorem Delta_gamma (n : ℕ) :
    Δ n = C0 ^ n * (gfun n / gfun 0) *
      (gammaF.map (fun fm => (rf (fm.1.be) (fm.1.la * n)) ^ fm.2)).prod := Delta_gammaX n

theorem padicValRat_Delta (n p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hbig : 144 * n + 24 < p ^ 2) :
    padicValRat p (Δ n) = padicValRat p (gfun n / gfun 0) +
      (gammaF.map (fun fm => fm.2 * ((fm.1.hi (p % 6)).floorAt n p 0 - (fm.1.lo (p % 6)).floorAt n p 0))).sum :=
  padicValRat_DeltaX n p hp5 hbig

/-- the total valuation mass of `g(n)/g(0)` is `O(log n)` -/
theorem gfun_mass : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∑ q ∈ S, |(padicValRat q (gfun n / gfun 0) : ℝ)| * Real.log q ≤ C * Real.log (n + 1) := by
  obtain ⟨C, -, h⟩ := gfunX_mass
  exact ⟨C, h⟩

theorem Delta_ne_zero (n : ℕ) : Δ n ≠ 0 := det_W_ne n

theorem delta_val_two : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → 18 * (n : ℝ) - C * Real.log n ≤ padicValRat 2 (Δ n) :=
  delta_val_twoX

theorem delta_val_three : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → 27 * (n : ℝ) - C * Real.log n ≤ padicValRat 3 (Δ n) :=
  delta_val_threeX

theorem delta_val_small : ∃ C : ℝ, ∀ n p : ℕ, 2 ≤ n → p.Prime → 5 ≤ p →
    -C * (Real.log n / Real.log p + 1) ≤ padicValRat p (Δ n) :=
  delta_val_smallX

end Zeta2L2Chi3.Arith

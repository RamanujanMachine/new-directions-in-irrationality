import Zeta2L2Chi3.Dual

/-!
# Shift identities for the numerator and denominator of `F_n`

Pochhammer splitting identities relating `FNum (n+1)`, `FDen (n+1)` to `FNum n`, `FDen n`
(the `n`-shift) and `FNum n (s-1)`, `FDen n (s-1)` to `FNum n s`, `FDen n s` (the `s`-shift).
-/

namespace Zeta2L2Chi3

open Finset

section rfLemmas

variable {R : Type*} [CommRing R]

lemma rf_add (x : R) (a b : ℕ) : rf x (a + b) = rf x a * rf (x + a) b := by
  unfold rf
  rw [prod_range_add]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  push_cast; ring

lemma rf_succ' (x : R) (m : ℕ) : rf x (m + 1) = x * rf (x + 1) m := by
  unfold rf
  rw [prod_range_succ', mul_comm]
  simp only [Nat.cast_zero, add_zero]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  push_cast; ring

lemma rf_succ (x : R) (m : ℕ) : rf x (m + 1) = rf x m * (x + m) := by
  unfold rf
  rw [prod_range_succ]

lemma rf_one (x : R) : rf x 1 = x := by
  simp [rf]

lemma rf_shift (x : R) (m : ℕ) : rf (x + 1) m * x = rf x m * (x + m) := by
  rw [← rf_succ, rf_succ']
  ring

lemma rf_two (x : R) (m : ℕ) : rf x (m + 2) = x * (x + 1) * rf (x + 2) m := by
  rw [rf_succ', rf_succ']
  have : x + 1 + 1 = x + 2 := by ring
  rw [this]
  ring

end rfLemmas

variable {K : Type*} [Field K]

/-- the ten-plus-nine new numerator factors -/
def rnumA (n : ℕ) (s : K) : K :=
  (∏ i ∈ range 10, (s + 10 * n + 2 + i)) * (s - n) * ∏ i ∈ range 8, (s + 8 * n + 2 + i)

def rdenS (n : ℕ) (s : K) : K :=
  (∏ i ∈ range 12, (12 * n + 2 + i - s)) * (∏ i ∈ range 6, (6 * n + 7 / 3 + i - s)) *
    ∏ i ∈ range 5, (5 * n + 5 / 2 + i - s)

theorem FNum_succ (n : ℕ) (s : K) : FNum (n + 1) s = FNum n s * rnumA n s := by
  unfold FNum rnumA
  have h1 : rf (s + 1) (10 * (n + 1) + 1) =
      rf (s + 1) (10 * n + 1) * ∏ i ∈ range 10, (s + 10 * n + 2 + i) := by
    rw [show 10 * (n + 1) + 1 = (10 * n + 1) + 10 by ring, rf_add]
    congr 1
    unfold rf
    refine prod_congr rfl fun i _ => ?_
    push_cast; ring
  have h2 : rf (s + 1 - ((n + 1 : ℕ) : K)) (9 * (n + 1) + 1) =
      (s - n) * rf (s + 1 - n) (9 * n + 1) * ∏ i ∈ range 8, (s + 8 * n + 2 + i) := by
    rw [show 9 * (n + 1) + 1 = (1 + (9 * n + 1)) + 8 by ring, rf_add, rf_add _ 1 (9 * n + 1),
      rf_one]
    have b : rf (s + 1 - ((n + 1 : ℕ) : K) + ((1 : ℕ) : K)) (9 * n + 1) =
        rf (s + 1 - n) (9 * n + 1) := by
      congr 1; push_cast; ring
    have c : rf (s + 1 - ((n + 1 : ℕ) : K) + ((1 + (9 * n + 1) : ℕ) : K)) 8 =
        ∏ i ∈ range 8, (s + 8 * n + 2 + i) := by
      unfold rf
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [b, c]
    push_cast; ring
  rw [h1, h2]
  ring

theorem FDen_succ [CharZero K] (n : ℕ) (s : K) :
    FDen (n + 1) s * ((2 * n - s) * (2 * n + 1 - s) * (2 * n + 1 / 2 - s) * (2 * n + 3 / 2 - s)) =
      FDen n s * rdenS n s := by
  unfold FDen rdenS
  have hA : rf (2 * ((n + 1 : ℕ) : K) - s) (10 * (n + 1) + 2) * ((2 * n - s) * (2 * n + 1 - s)) =
      rf (2 * n - s) (10 * n + 2) * ∏ i ∈ range 12, (12 * n + 2 + i - s) := by
    have e1 := rf_two (2 * (n : K) - s) (10 * (n + 1) + 2)
    have e2 : rf (2 * (n : K) - s) (10 * (n + 1) + 2 + 2) =
        rf (2 * (n : K) - s) (10 * n + 2) * rf (2 * (n : K) - s + ((10 * n + 2 : ℕ) : K)) 12 := by
      rw [show 10 * (n + 1) + 2 + 2 = (10 * n + 2) + 12 by ring, rf_add]
    have e3 : 2 * ((n + 1 : ℕ) : K) - s = 2 * (n : K) - s + 2 := by push_cast; ring
    have e4 : rf (2 * (n : K) - s + ((10 * n + 2 : ℕ) : K)) 12 =
        ∏ i ∈ range 12, (12 * (n : K) + 2 + i - s) := by
      unfold rf
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e3, ← e4]
    linear_combination e2 - e1
  have hB : rf (1 / 3 - s) (6 * (n + 1) + 2) =
      rf (1 / 3 - s) (6 * n + 2) * ∏ i ∈ range 6, (6 * (n : K) + 7 / 3 + i - s) := by
    rw [show 6 * (n + 1) + 2 = (6 * n + 2) + 6 by ring, rf_add]
    congr 1
    unfold rf
    refine prod_congr rfl fun i _ => ?_
    push_cast; ring
  have hC : rf (2 * ((n + 1 : ℕ) : K) + 1 / 2 - s) (3 * (n + 1) + 2) *
      ((2 * n + 1 / 2 - s) * (2 * n + 3 / 2 - s)) =
      rf (2 * n + 1 / 2 - s) (3 * n + 2) * ∏ i ∈ range 5, (5 * (n : K) + 5 / 2 + i - s) := by
    have e1 := rf_two (2 * (n : K) + 1 / 2 - s) (3 * (n + 1) + 2)
    have e2 : rf (2 * (n : K) + 1 / 2 - s) (3 * (n + 1) + 2 + 2) =
        rf (2 * (n : K) + 1 / 2 - s) (3 * n + 2) *
          rf (2 * (n : K) + 1 / 2 - s + ((3 * n + 2 : ℕ) : K)) 5 := by
      rw [show 3 * (n + 1) + 2 + 2 = (3 * n + 2) + 5 by ring, rf_add]
    have e3 : 2 * ((n + 1 : ℕ) : K) + 1 / 2 - s = 2 * (n : K) + 1 / 2 - s + 2 := by
      push_cast; ring
    have e4 : rf (2 * (n : K) + 1 / 2 - s + ((3 * n + 2 : ℕ) : K)) 5 =
        ∏ i ∈ range 5, (5 * (n : K) + 5 / 2 + i - s) := by
      unfold rf
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e3, ← e4]
    linear_combination e2 - e1
  rw [hB]
  linear_combination
    (rf (1 / 3 - s) (6 * n + 2) * ∏ i ∈ range 6, (6 * (n : K) + 7 / 3 + i - s)) *
      (rf (2 * ((n + 1 : ℕ) : K) + 1 / 2 - s) (3 * (n + 1) + 2) *
        ((2 * n + 1 / 2 - s) * (2 * n + 3 / 2 - s))) * hA +
    (rf (2 * n - s) (10 * n + 2) * ∏ i ∈ range 12, (12 * (n : K) + 2 + i - s)) *
      (rf (1 / 3 - s) (6 * n + 2) * ∏ i ∈ range 6, (6 * (n : K) + 7 / 3 + i - s)) * hC

theorem FNum_shift (n : ℕ) (s : K) :
    FNum n (s - 1) * ((s + 10 * n + 1) * (s + 8 * n + 1)) = FNum n s * (s * (s - n)) := by
  unfold FNum
  have a1 : s - 1 + 1 = s := by ring
  rw [a1]
  have e1 := rf_shift s (10 * n + 1)
  have e2 := rf_shift (s - n) (9 * n + 1)
  have b : s - (n : K) + 1 = s + 1 - n := by ring
  rw [b] at e2
  have c1 : s + ((10 * n + 1 : ℕ) : K) = s + 10 * n + 1 := by push_cast; ring
  have c2 : s - (n : K) + ((9 * n + 1 : ℕ) : K) = s + 8 * n + 1 := by push_cast; ring
  rw [c1] at e1
  rw [c2] at e2
  linear_combination
    -(rf (s + 1 - n) (9 * n + 1) * (s - n)) * e1 - (rf s (10 * n + 1) * (s + 10 * n + 1)) * e2

theorem FDen_shift [CharZero K] (n : ℕ) (s : K) :
    FDen n (s - 1) * ((2 * n - s) * (1 / 3 - s) * (2 * n + 1 / 2 - s)) =
      FDen n s * ((12 * n + 2 - s) * (6 * n + 7 / 3 - s) * (5 * n + 5 / 2 - s)) := by
  unfold FDen
  have a1 : 2 * (n : K) - (s - 1) = 2 * n - s + 1 := by ring
  have a2 : (1 / 3 : K) - (s - 1) = 1 / 3 - s + 1 := by ring
  have a3 : 2 * (n : K) + 1 / 2 - (s - 1) = 2 * n + 1 / 2 - s + 1 := by ring
  rw [a1, a2, a3]
  have e1 := rf_shift (2 * (n : K) - s) (10 * n + 2)
  have e2 := rf_shift ((1 / 3 : K) - s) (6 * n + 2)
  have e3 := rf_shift (2 * (n : K) + 1 / 2 - s) (3 * n + 2)
  have c1 : 2 * (n : K) - s + ((10 * n + 2 : ℕ) : K) = 12 * n + 2 - s := by push_cast; ring
  have c2 : (1 / 3 : K) - s + ((6 * n + 2 : ℕ) : K) = 6 * n + 7 / 3 - s := by push_cast; ring
  have c3 : 2 * (n : K) + 1 / 2 - s + ((3 * n + 2 : ℕ) : K) = 5 * n + 5 / 2 - s := by
    push_cast; ring
  rw [c1] at e1
  rw [c2] at e2
  rw [c3] at e3
  linear_combination
    (rf (1 / 3 - s + 1) (6 * n + 2) * (1 / 3 - s) *
      rf (2 * n + 1 / 2 - s + 1) (3 * n + 2) * (2 * n + 1 / 2 - s)) * e1 +
    (rf (2 * n - s) (10 * n + 2) * (12 * n + 2 - s) *
      rf (2 * n + 1 / 2 - s + 1) (3 * n + 2) * (2 * n + 1 / 2 - s)) * e2 +
    (rf (2 * n - s) (10 * n + 2) * (12 * n + 2 - s) *
      rf (1 / 3 - s) (6 * n + 2) * (6 * n + 7 / 3 - s)) * e3

end Zeta2L2Chi3

/-
# Telescoping certificates for the dual transport: structure of the checked identities

For each column `k ∈ {0,1,2}` the certificate is a bivariate integer polynomial
`N_k(n, s)` (data in `Cert0/1/2.lean`) such that, with

* `U(s) = rden(s-1) A(s-1)`, `V(s) = B(s-1) rden(s)`,
* `rnum, rden, A, B` the explicit products of linear factors below,
* `Q̃_{jk} = Data.Qnum j k`, `D_Q = Data.Qden` (so `Q_{jk} = Q̃_{jk}/D_Q`),

the identity
`N_k(s) U(s) - V(s) N_k(s-1) = 12 (3n+1) [D_Q s^k rnum(s) + rden(s) ∑_j Q̃_{jk} s^j] U(s)`
holds identically in `n, s`.  It is checked (in scaled integer form) by `PE.check`.
-/
import Zeta2L2Chi3.Dual

open Finset

namespace Zeta2L2Chi3

/-! ### Integer-scaled factor lists -/

/-- `rden` scaled by `K₀ = 3⁶·2⁵`. -/
def rdenInt : List PE :=
  (List.range 12).map (fun i => linPE (2 + i) 12 (-1)) ++
  (List.range 6).map (fun i => linPE (7 + 3 * i) 18 (-3)) ++
  (List.range 5).map (fun i => linPE (5 + 2 * i) 10 (-2))

/-- `rnum` scaled by `4`. -/
def rnumInt : List PE :=
  (List.range 10).map (fun i => linPE (2 + i) 10 1) ++ [linPE 0 (-1) 1] ++
  (List.range 8).map (fun i => linPE (2 + i) 8 1) ++
  [linPE 0 2 (-1), linPE 1 2 (-1), linPE 1 4 (-2), linPE 3 4 (-2)]

/-- `A(s) = (s+10n+2)(s+8n+2)(12n+1-s)(6n+4/3-s)(5n+3/2-s)`, scaled by `6`. -/
def AInt : List PE := [linPE 2 10 1, linPE 2 8 1, linPE 1 12 (-1), linPE 4 18 (-3), linPE 3 10 (-2)]

/-- `B(s) = (s+1)(s+1-n)(2n-1-s)(-2/3-s)(2n-1/2-s)`, scaled by `6`. -/
def BInt : List PE := [linPE 1 0 1, linPE 1 (-1) 1, linPE (-1) 2 (-1), linPE (-2) 0 (-3), linPE (-1) 4 (-2)]

def K0 : ℤ := 3 ^ 6 * 2 ^ 5

/-- `s^k` -/
def spowPE : ℕ → PE
  | 0 => PE.lit [[1]]
  | k + 1 => PE.mul (PE.lit [[0], [1]]) (spowPE k)

/-- `∑_j Q̃_{jk} s^j` -/
def sumQPE (k : Fin 3) : PE :=
  PE.add (PE.add (PE.lit [Data.Qnum 0 k]) (PE.mul (PE.lit [Data.Qnum 1 k]) (spowPE 1)))
    (PE.mul (PE.lit [Data.Qnum 2 k]) (spowPE 2))

/-- The checked identity (integer form). -/
def certPE (k : Fin 3) (Nc : PE) : PE :=
  let Ui := PE.mul (PE.shift (prodPE rdenInt)) (PE.shift (prodPE AInt))
  let Vi := PE.mul (PE.shift (prodPE BInt)) (prodPE rdenInt)
  PE.sub (PE.mul (PE.lit [[4 * K0]]) (PE.sub (PE.mul Nc Ui) (PE.mul Vi (PE.shift Nc))))
    (PE.mul (PE.mul (PE.mul (PE.lit [[12]]) (linPE 1 3 0))
      (PE.add (PE.mul (PE.mul (PE.mul (PE.lit [[K0]]) (PE.lit [Data.Qden])) (spowPE k))
          (prodPE rnumInt))
        (PE.mul (PE.mul (PE.lit [[4]]) (prodPE rdenInt)) (sumQPE k)))) Ui)

/-! ### Semantic products -/

variable {R : Type*} [Field R]

/-- `rden(n,s)` with rational coefficients. -/
def rdenR (n s : R) : R :=
  (∏ i ∈ range 12, (12 * n + 2 + i - s)) * (∏ i ∈ range 6, (6 * n + 7 / 3 + i - s)) *
    ∏ i ∈ range 5, (5 * n + 5 / 2 + i - s)

def rnumR (n s : R) : R :=
  (∏ i ∈ range 10, (s + 10 * n + 2 + i)) * (s - n) * (∏ i ∈ range 8, (s + 8 * n + 2 + i)) *
    ((2 * n - s) * (2 * n + 1 - s) * (2 * n + 1 / 2 - s) * (2 * n + 3 / 2 - s))

def AR (n s : R) : R := (s + 10 * n + 2) * (s + 8 * n + 2) * (12 * n + 1 - s) * (6 * n + 4 / 3 - s) *
  (5 * n + 3 / 2 - s)

def BR (n s : R) : R := (s + 1) * (s + 1 - n) * (2 * n - 1 - s) * (-2 / 3 - s) * (2 * n - 1 / 2 - s)

lemma val_spowPE (k : ℕ) (n s : R) : (spowPE k).val n s = s ^ k := by
  induction k with
  | zero => simp [spowPE, PE.val, litVal, hornerR]
  | succ k ih => simp [spowPE, PE.val, litVal, hornerR, ih, pow_succ]; ring

lemma val_rdenInt [CharZero R] (n s : R) : (prodPE rdenInt).val n s = (K0 : R) * rdenR n s := by
  simp only [val_prodPE, rdenInt, List.map_append, List.map_map, List.prod_append]
  simp [rdenR, K0, List.range_succ, Finset.prod_range_succ, Function.comp_def]
  ring

lemma val_rnumInt [CharZero R] (n s : R) : (prodPE rnumInt).val n s = 4 * rnumR n s := by
  simp only [val_prodPE, rnumInt, List.map_append, List.map_map, List.prod_append]
  simp [rnumR, List.range_succ, Finset.prod_range_succ, Function.comp_def]
  ring

lemma val_AInt [CharZero R] (n s : R) : (prodPE AInt).val n s = 6 * AR n s := by
  simp [AInt, AR]; ring

lemma val_BInt [CharZero R] (n s : R) : (prodPE BInt).val n s = 6 * BR n s := by
  simp [BInt, BR]; ring

lemma val_sumQPE (k : Fin 3) (n s : R) :
    (sumQPE k).val n s = hornerR (Data.Qnum 0 k) n + hornerR (Data.Qnum 1 k) n * s +
      hornerR (Data.Qnum 2 k) n * s ^ 2 := by
  simp [sumQPE, PE.val, litVal, val_spowPE]

/-- **The certificate identity**, in rational form, from a successful check. -/
theorem cert_identity [CharZero R] (k : Fin 3) (Nc : PE) (B : ℤ) (h : (certPE k Nc).check B)
    (n s : R) :
    Nc.val n s * (rdenR n (s - 1) * AR n (s - 1)) - BR n (s - 1) * rdenR n s * Nc.val n (s - 1) =
      12 * (3 * n + 1) * (hornerR Data.Qden n * s ^ (k : ℕ) * rnumR n s +
        rdenR n s * (hornerR (Data.Qnum 0 k) n + hornerR (Data.Qnum 1 k) n * s +
          hornerR (Data.Qnum 2 k) n * s ^ 2)) * (rdenR n (s - 1) * AR n (s - 1)) := by
  have key := PE.eq_zero_of_check _ B h n s
  simp only [certPE, PE.val, val_rdenInt, val_AInt, val_BInt, val_rnumInt, val_sumQPE,
    val_spowPE, val_linPE] at key
  simp only [litVal, hornerR] at key
  have hK : (K0 : R) ≠ 0 := by norm_num [K0]
  have h24 : (24 : R) * K0 ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hK)
  apply mul_left_cancel₀ h24
  push_cast at key ⊢
  linear_combination key

end Zeta2L2Chi3

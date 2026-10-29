/-
# Telescoping certificates for the forward (5F4) transport: structure of the checked identities

`R_n(t) = (t+2n+1)_{10n+1} (t+4/3)_{6n+1} (t+2n+3/2)_{3n+1} / [(t-10n-1)_{10n+2} (t-8n-1)_{9n+2}]`.
With `R_{n+1} = R_n · rnum / rden` and `R_n(t-1) As(t) = R_n(t) Bs(t)`, the certificate `N_j(n,t)`
satisfies, for `U(t) = rden(t-1) As(t)`, `V(t) = Bs(t) rden(t)`,

`N_j(t) U(t) - V(t) N_j(t-1) = [c_num D_M t^j rnum(t) - c_den rden(t) ∑_l M̃_{lj} t^l] U(t)`

identically in `(n, t)`, where `M = M̃ / D_M` and `c = c_num / c_den`.
Hence `G_j = R_n N_j / (c_num D_M rden)` gives `t^j R_{n+1} - c⁻¹ ∑_l M_{lj} t^l R_n = G_j(t) - G_j(t-1)`.
-/
import Zeta2L2Chi3.CertDefs

open Finset

namespace Zeta2L2Chi3

/-! ### Integer-scaled factor lists (linear forms `c₀ + a n + b t`) -/

/-- `rnum = ∏_{i<12} (t+12n+2+i) ∏_{i<6} (t+6n+7/3+i) ∏_{i<5} (t+5n+5/2+i)`, scaled by `3⁶ 2⁵` -/
def frnumInt : List PE :=
  (List.range 12).map (fun i => linPE (2 + i) 12 1) ++
  (List.range 6).map (fun i => linPE (7 + 3 * i) 18 3) ++
  (List.range 5).map (fun i => linPE (5 + 2 * i) 10 2)

/-- `rden = (t+2n+1)(t+2n+2)(t+2n+3/2)(t+2n+5/2) ∏_{i<10}(t-10n-11+i) ∏_{i<8}(t-8n-9+i) (t+n+1)`,
scaled by `2²` -/
def frdenInt : List PE :=
  [linPE 1 2 1, linPE 2 2 1, linPE 3 4 2, linPE 5 4 2] ++
  (List.range 10).map (fun i => linPE (-11 + i) (-10) 1) ++
  (List.range 8).map (fun i => linPE (-9 + i) (-8) 1) ++ [linPE 1 1 1]

/-- `Bs = (t+2n)(t+1/3)(t+2n+1/2) t (t+n)`, scaled by `6` -/
def fBsInt : List PE := [linPE 0 2 1, linPE 1 0 3, linPE 1 4 2, linPE 0 0 1, linPE 0 1 1]

/-- `As = (t+12n+1)(t+6n+4/3)(t+5n+3/2)(t-10n-2)(t-8n-2)`, scaled by `6` -/
def fAsInt : List PE := [linPE 1 12 1, linPE 4 18 3, linPE 3 10 2, linPE (-2) (-10) 1, linPE (-2) (-8) 1]

def fK1 : ℤ := 3 ^ 6 * 2 ^ 5

/-- `∑_l M̃_{lj} t^l` -/
def sumMPE (j : Fin 4) : PE :=
  PE.add (PE.add (PE.add (PE.lit [Data.Mnum 0 j]) (PE.mul (PE.lit [Data.Mnum 1 j]) (spowPE 1)))
    (PE.mul (PE.lit [Data.Mnum 2 j]) (spowPE 2))) (PE.mul (PE.lit [Data.Mnum 3 j]) (spowPE 3))

/-- The checked forward identity (integer form):
`4 fK1 (N U_i - V_i N(t-1)) = 4 [fK1 c_num D_M t^j rnum_i - 4·... ]` — see `fcert_identity`. -/
def fcertPE (j : Fin 4) (L : ℤ) (Nc : PE) : PE :=
  let Ui := PE.mul (PE.shift (prodPE frdenInt)) (prodPE fAsInt)
  let Vi := PE.mul (prodPE fBsInt) (prodPE frdenInt)
  PE.sub (PE.mul (PE.lit [[4 * fK1]]) (PE.sub (PE.mul Nc Ui) (PE.mul Vi (PE.shift Nc))))
    (PE.mul (PE.mul (PE.lit [[L]]) (PE.sub
        (PE.mul (PE.mul (PE.mul (PE.mul (PE.lit [[4]]) (PE.lit [Data.cnum 0 0])) (PE.lit [Data.Mden]))
          (spowPE j)) (prodPE frnumInt))
        (PE.mul (PE.mul (PE.mul (PE.lit [[fK1]]) (PE.lit [Data.cden])) (prodPE frdenInt)) (sumMPE j))))
      Ui)

end Zeta2L2Chi3

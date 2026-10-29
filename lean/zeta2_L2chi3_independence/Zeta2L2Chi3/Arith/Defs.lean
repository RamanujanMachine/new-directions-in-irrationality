/-
# Arithmetic content bound: shared definitions

Computable data shared by the forward and dual prime-by-prime bounds.

* `VGe p k x` : `x ∈ p^k ℤ_(p)`.
* `Fam` : arithmetic families `c + i` (`i < len`) of zeros or poles, with `c = al n + be`,
  `len = la n + mu`.  For a prime `p ≡ e (mod 6)` and `d = den be`, `kinv d e` is the
  `k ∈ [0,d)` with `d ∣ k p + 1`; the family has two *endpoints* `A = a n + b p + c`
  (`lo`: `a = al`, `b = be k`, `c = be - 1`; `hi`: `a = al + la`, `b = be k`, `c = be + mu - 1`).
* For a residue `r ∈ [0,p)` the endpoint floors `F_E = ⌊(A_E - r)/p⌋` determine the packet of the
  family in the class of `r`: its members are `r + p T` with `T ∈ (F_lo, F_hi] - be k`.
* `PType` : a packet type (T-values of zeros, labelled T-values of poles, `jmin`), its residues
  `R`, harmonic values `Hq`, vectors `V j` and weighted generators `gens`.
-/
import Mathlib

namespace Zeta2L2Chi3.Arith

/-! ### p-adic valuation predicate -/

/-- `x ∈ p^k ℤ_(p)` -/
def VGe (p : ℕ) (k : ℤ) (x : ℚ) : Prop := x = 0 ∨ k ≤ padicValRat p x

/-! ### Families and endpoints -/

/-- an arithmetic family `c + i`, `i < len`, `c = al n + be`, `len = la n + mu` -/
structure Fam where
  al : ℤ
  be : ℚ
  la : ℕ
  mu : ℕ
deriving DecidableEq, Repr, Inhabited

def Fam.c (f : Fam) (n : ℕ) : ℚ := f.al * n + f.be
def Fam.len (f : Fam) (n : ℕ) : ℕ := f.la * n + f.mu

/-- `k ∈ [0,d)` with `d ∣ k e + 1` (so `d ∣ k p + 1` for `p ≡ e (mod 6)`, `d ∣ 6`) -/
def kinv (d e : ℕ) : ℕ := ((List.range d).find? (fun k => (k * e + 1) % d = 0)).getD 0

/-- an endpoint `A = a n + b p + c` -/
structure Endpt where
  a : ℤ
  b : ℚ
  c : ℚ
deriving DecidableEq, Repr, Inhabited

def Fam.shift (f : Fam) (e : ℕ) : ℚ := f.be * kinv f.be.den e
def Fam.lo (f : Fam) (e : ℕ) : Endpt := ⟨f.al, f.shift e, f.be - 1⟩
def Fam.hi (f : Fam) (e : ℕ) : Endpt := ⟨f.al + f.la, f.shift e, f.be + f.mu - 1⟩

/-- the (integer) value of an endpoint at `(n, p)` -/
def Endpt.val (E : Endpt) (n p : ℕ) : ℚ := E.a * n + E.b * p + E.c

/-- the endpoint floor `⌊(A_E - r)/p⌋` -/
def Endpt.floorAt (E : Endpt) (n p r : ℕ) : ℤ := ⌊(E.val n p - r) / p⌋

/-- the T-values `(Flo, Fhi] + sh` -/
def run (Flo Fhi : ℤ) (sh : ℚ) : List ℚ :=
  (List.range (Fhi - Flo).toNat).map (fun m => ((Flo + 1 + m : ℤ) : ℚ) + sh)

/-! ### The two presentations -/

/-- dual zeros: `-(10n+1) … -1` and `-(8n+1) … n-1` -/
def dualZ : List Fam := [⟨-10, -1, 10, 1⟩, ⟨-8, -1, 9, 1⟩]
/-- dual poles (labels 0, 1, 2): `2n … 12n+1`, `1/3 … 6n+4/3`, `2n+1/2 … 5n+3/2` -/
def dualP : List Fam := [⟨2, 0, 10, 2⟩, ⟨0, 1 / 3, 6, 2⟩, ⟨2, 1 / 2, 3, 2⟩]
/-- forward zeros: `-(12n+1) … -(2n+1)`, `-6n-4/3 … -4/3`, `-5n-3/2 … -2n-3/2` -/
def fwdZ : List Fam := [⟨-12, -1, 10, 1⟩, ⟨-6, -4 / 3, 6, 1⟩, ⟨-5, -3 / 2, 3, 1⟩]
/-- forward poles: `0 … 10n+1`, `-n … 8n+1` -/
def fwdP : List Fam := [⟨0, 0, 10, 2⟩, ⟨-1, 0, 9, 2⟩]
/-- the gamma factorization of `Δ_n`: `(β)_{An}^m` -/
def gammaF : List (Fam × ℤ) :=
  [(⟨0, 2 / 3, 12, 0⟩, -1), (⟨0, 1, 8, 0⟩, 1), (⟨0, 1 / 3, 5, 0⟩, -1), (⟨0, 1 / 3, 8, 0⟩, 1),
   (⟨0, 1, 6, 0⟩, -1), (⟨0, 1, 5, 0⟩, 1), (⟨0, 1 / 6, 4, 0⟩, 1), (⟨0, 1 / 2, 9, 0⟩, -1),
   (⟨0, 2 / 3, 6, 0⟩, 1), (⟨0, 2 / 3, 5, 0⟩, 1), (⟨0, 1 / 3, 4, 0⟩, -1)]

/-- endpoints of a list of families, `lo, hi, lo, hi, …` -/
def endpts (fs : List Fam) (e : ℕ) : List Endpt := fs.flatMap (fun f => [f.lo e, f.hi e])

/-! ### Packet types -/

/-- a packet type: T-values of zeros, T-values of poles with labels (0 int, 1 third, 2 half),
and `jmin` (1 for the residue class `r = 0`, else 0) -/
structure PType where
  zs : List ℚ
  ps : List (ℚ × ℕ)
  jmin : ℕ
deriving DecidableEq, Repr, Inhabited

def PType.h (t : PType) : ℤ := (t.zs.length : ℤ) - t.ps.length

/-- residue of the monic packet kernel `∏(T-a)/∏(T-b)` at the pole `b` -/
def PType.R (t : PType) (b : ℚ) : ℚ :=
  (t.zs.map (fun a => b - a)).prod / ((t.ps.filter (fun q => q.1 ≠ b)).map (fun q => b - q.1)).prod

/-- `H(b) = ∑_{0 < u ≤ b, u ≡ b (mod 1)} u⁻²` -/
def Hq (b : ℚ) : ℚ := ((List.range ⌈b⌉.toNat).map (fun i => 1 / (b - i) ^ 2)).sum

/-- the vector `V_j = (-∑ R_b b^j H(b), ∑_third R_b b^j, ∑_half R_b b^j, ∑_all R_b b^j)` -/
def PType.V (t : PType) (j : ℕ) : Fin 4 → ℚ := fun c =>
  match c with
  | 0 => -(t.ps.map (fun q => t.R q.1 * q.1 ^ j * Hq q.1)).sum
  | 1 => ((t.ps.filter (fun q => q.2 = 1)).map (fun q => t.R q.1 * q.1 ^ j)).sum
  | 2 => ((t.ps.filter (fun q => q.2 = 2)).map (fun q => t.R q.1 * q.1 ^ j)).sum
  | 3 => (t.ps.map (fun q => t.R q.1 * q.1 ^ j)).sum

/-- Taylor truncation order -/
def Jt : ℕ := 5

/-- weight of the regular harmonic (constant-row) generator -/
def PType.regW (t : PType) : ℤ := min (t.h + 1 + max (t.jmin : ℤ) (-t.h - 1)) (t.h + 2 + t.jmin) + 2

def unitVec (k : Fin 4) : Fin 4 → ℚ := fun i => if i = k then 1 else 0

/-- the weighted generators of a packet type -/
def PType.gens (t : PType) : List (ℤ × (Fin 4 → ℚ)) :=
  if t.ps = [] then [] else
  ((List.range (Jt + 1 - t.jmin)).map (fun i => (t.h + 1 + (t.jmin + i : ℕ), t.V (t.jmin + i)))) ++
  [(t.regW, unitVec 0)] ++ (List.finRange 4).map (fun k => (t.h + Jt + 2, unitVec k))

/-- the dual packet type from the ten endpoint floors (family order of `dualZ ++ dualP`) -/
def mkDualType (e : ℕ) (F : ℕ → ℤ) (jmin : ℕ) : PType where
  zs := run (F 0) (F 1) (-(dualZ[0]!).shift e) ++ run (F 2) (F 3) (-(dualZ[1]!).shift e)
  ps := (run (F 4) (F 5) (-(dualP[0]!).shift e)).map (·, 0) ++
        (run (F 6) (F 7) (-(dualP[1]!).shift e)).map (·, 1) ++
        (run (F 8) (F 9) (-(dualP[2]!).shift e)).map (·, 2)
  jmin := jmin

/-- the actual dual packet type of the residue class `r` -/
def dualTypeAt (n p r : ℕ) : PType :=
  mkDualType (p % 6) (fun E => ((endpts (dualZ ++ dualP) (p % 6))[E]!).floorAt n p r) (if r = 0 then 1 else 0)

/-- forward packet excess `h = #zeros - #poles` from the ten endpoint floors (`fwdZ ++ fwdP`) -/
def fwdH (F : ℕ → ℤ) : ℤ := (F 1 - F 0) + (F 3 - F 2) + (F 5 - F 4) - (F 7 - F 6) - (F 9 - F 8)

end Zeta2L2Chi3.Arith

/-
# The finite chamber checkers (computable)

For a cell `(e, lo, hi)` (an open interval of `x - L`, `x = n/p`, between consecutive walls),
an interior point `x0` and a lift `L`, put `x* = L + x0`.

* `qstar E x*` predicts `⌊A_E / p⌋`, `keyOf E x*` predicts the position of `ρ_E = A_E mod p`.
* The sets `S_r = {E : ρ_E < r}` are among `candSets`: `∅` and `D_F = {E : ρ_E ≤ ρ_F}` (`ρ_F ≠ p-1`).
* The packet of the class `r` has floors `F_E = q_E - [E ∈ S_r]`.
* Forward bound: `min(0, min_S h(S)) + Σ m (q_hi - q_lo)` (gamma factorization of `Δ_n`).
* Dual bound: generators of all candidate packet types are described by `Desc` (known coordinates
  and the relation `c₁ + c₂ = c₃`), the total coordinate is eliminated with a pivot, and the
  three projected 2×2 minors are bounded from the descriptor classification.
-/
import Zeta2L2Chi3.Arith.Defs

namespace Zeta2L2Chi3.Arith

/-- fractional part -/
def fracQ (x : ℚ) : ℚ := x - ⌊x⌋

/-- predicted `⌊A_E / p⌋` at `x` (for `p` large and `n/p` in the cell) -/
def qstar (E : Endpt) (x : ℚ) : ℤ :=
  if fracQ (E.a * x + E.b) = 0 then ⌊E.a * x + E.b⌋ + (if 0 ≤ E.c then 0 else -1)
  else ⌊E.a * x + E.b⌋

/-- predicted position of `ρ_E / p` (lexicographic: fractional part, then `c / p`) -/
def keyOf (E : Endpt) (x : ℚ) : ℚ × ℚ :=
  let f := fracQ (E.a * x + E.b)
  if f = 0 then (if 0 ≤ E.c then (0, E.c) else (1, E.c)) else (f, E.c)

def keyLe (k₁ k₂ : ℚ × ℚ) : Bool := decide (k₁.1 < k₂.1) || (decide (k₁.1 = k₂.1) && decide (k₁.2 ≤ k₂.2))

/-- `ρ_E = p - 1` -/
def isTop1 (E : Endpt) (x : ℚ) : Bool := decide (fracQ (E.a * x + E.b) = 0) && decide (E.c = -1)

/-- candidate sets `S` (as membership lists): `∅` and `D_F` for `ρ_F ≠ p - 1` -/
def candSets (Es : List Endpt) (x : ℚ) : List (List Bool) :=
  (Es.map fun _ => false) ::
    (Es.filter (fun F => !isTop1 F x)).map (fun F => Es.map (fun E => keyLe (keyOf E x) (keyOf F x)))

/-- floors of the packet for the set `S` -/
def floorsOf (Es : List Endpt) (x : ℚ) (S : List Bool) : ℕ → ℤ := fun i =>
  qstar (Es[i]!) x - (if S.getD i false then 1 else 0)

/-! ### Forward bound -/

def detProfile (e : ℕ) (x : ℚ) : ℤ :=
  (gammaF.map (fun fm => fm.2 * (qstar (fm.1.hi e) x - qstar (fm.1.lo e) x))).sum

def fwdCellBound (e : ℕ) (x : ℚ) : ℤ :=
  let Es := endpts (fwdZ ++ fwdP) e
  min 0 (((candSets Es x).map (fun S => fwdH (floorsOf Es x S))).foldr min 0) + detProfile e x

/-! ### Dual bound: descriptors -/

/-- a vector in `ℚ⁴` with known coordinates; `rel` asserts `v₁ + v₂ = v₃` -/
structure Desc where
  co : Fin 4 → Option ℚ
  rel : Bool

instance : Inhabited Desc := ⟨⟨fun _ => none, false⟩⟩

def exactDesc (v : Fin 4 → ℚ) : Desc := ⟨fun k => some (v k), false⟩

/-- value-free descriptor of `V_j` -/
def structDesc (t : PType) (j : ℕ) : Desc where
  co := fun c => match c with
    | 0 => if t.ps.all (fun q => decide (q.1 ≤ 0)) then some 0 else none
    | 1 => if t.ps.any (fun q => q.2 = 1) then none else some 0
    | 2 => if t.ps.any (fun q => q.2 = 2) then none else some 0
    | 3 => if t.h + j ≤ -2 then some 0 else if t.h + j = -1 then some 1 else none
  rel := !t.ps.any (fun q => q.2 = 0)

/-- descriptors parallel to `PType.gens` -/
def PType.descs (t : PType) (exact : Bool) : List (ℤ × Desc) :=
  if t.ps = [] then [] else
  ((List.range (Jt + 1 - t.jmin)).map (fun i => (t.h + 1 + (t.jmin + i : ℕ),
      if exact then exactDesc (t.V (t.jmin + i)) else structDesc t (t.jmin + i)))) ++
  [(t.regW, exactDesc (unitVec 0))] ++ (List.finRange 4).map (fun k => (t.h + Jt + 2, exactDesc (unitVec k)))

/-- a vector in `ℚ³` (after elimination) with known coordinates; `rel` asserts `v₁ + v₂ = 0` -/
structure Desc3 where
  co : Fin 3 → Option ℚ
  rel : Bool

def zeroDesc3 : Desc3 := ⟨fun _ => some 0, false⟩

/-- descriptor of `v - (v₃ / s) v⁰` (first three coordinates), `s = v⁰₃` -/
def elimDesc (d0 : Desc) (s : ℚ) (d : Desc) : Desc3 :=
  match d.co 3 with
  | some a =>
    if a = 0 then ⟨fun k => d.co k.castSucc, d.rel⟩
    else ⟨fun k => match d.co k.castSucc, d0.co k.castSucc with
      | some c, some b => some (c - a * b / s)
      | _, _ => none, false⟩
  | none => ⟨fun k => match d0.co k.castSucc with
      | some b => if b = 0 then d.co k.castSucc else none
      | none => none, false⟩

/-- projection classification -/
inductive Cls
  | zero
  | dir (u v : ℚ)
  | unk
deriving Inhabited

def classify (d : Desc3) (i j : Fin 3) (th : Bool) : Cls :=
  match d.co i, d.co j with
  | some x, some y => if x = 0 ∧ y = 0 then .zero else .dir x y
  | some x, none => if x = 0 then .dir 0 1 else (if th && d.rel then .dir 1 (-1) else .unk)
  | none, some y => if y = 0 then .dir 1 0 else (if th && d.rel then .dir 1 (-1) else .unk)
  | none, none => if th && d.rel then .dir 1 (-1) else .unk

def Cls.isZero : Cls → Bool
  | .zero => true
  | _ => false

/-- `c` is known to lie in the span of `(u, v)` -/
def Cls.inSpan (c : Cls) (u v : ℚ) : Bool :=
  match c with
  | .zero => true
  | .dir x y => decide (u * y - v * x = 0)
  | .unk => false

def bigW : ℤ := 1000000

/-- minimum weight over a list (default `bigW`) -/
def minW (l : List ℤ) : ℤ := l.foldr min bigW

/-- lower bound for the projected minor `(i, j)` from weighted descriptors: `w₁ + w₂`, where `w₁`
is the least weight of a generator not known to project to zero and `w₂` the least weight of a
generator (other than the first of weight `w₁`) not known to lie on the line of that first one -/
def projBound (G : List (ℤ × Desc3)) (i j : Fin 3) (th : Bool) : ℤ :=
  let nz := (G.map (fun g => (g.1, classify g.2 i j th))).filter (fun c => !c.2.isZero)
  let w1 := minW (nz.map (·.1))
  match nz.findIdx? (fun c => decide (c.1 = w1)) with
  | none => 2 * bigW
  | some idx =>
    let first : ℤ × Cls := nz[idx]!
    let rest := nz.eraseIdx idx
    match first.2 with
    | .dir u v => w1 + minW ((rest.filter (fun c => !c.2.inSpan u v)).map (·.1))
    | _ => w1 + minW (rest.map (·.1))

/-- all candidate dual packet types with their exact-evaluation flags -/
def dualCandTypes (e : ℕ) (x : ℚ) : List PType :=
  let Es := endpts (dualZ ++ dualP) e
  (candSets Es x).flatMap (fun S =>
    if S.all (· = false) then [mkDualType e (floorsOf Es x S) 1, mkDualType e (floorsOf Es x S) 0]
    else [mkDualType e (floorsOf Es x S) 0])

/-- the dual bound for a list of packet types; `ex i t` selects exact evaluation of the `i`-th type `t` -/
def dualBoundOf (Ts : List PType) (ex : ℕ → PType → Bool) : ℤ :=
  let G : List (ℤ × Desc) := (Ts.zipIdx).flatMap (fun ti => ti.1.descs (ex ti.2 ti.1))
  let isPiv : ℤ × Desc → Bool := fun g => match g.2.co 3 with
    | some s => decide (g.1 = 0 ∧ (s = 1 ∨ s = -1))
    | none => false
  let allKnown : Desc → Bool := fun d => (List.finRange 4).all (fun k => (d.co k).isSome)
  let pidx? := match G.findIdx? (fun g => isPiv g && allKnown g.2) with
    | some i => some i
    | none => G.findIdx? isPiv
  let G3 : List (ℤ × Desc3) := match pidx? with
    | some pidx =>
      let piv := G[pidx]!
      let s := (piv.2.co 3).getD 1
      G.mapIdx (fun i g => (g.1, if i = pidx then zeroDesc3 else elimDesc piv.2 s g.2))
    | none => G.map (fun g => (g.1, ⟨fun k => g.2.co k.castSucc, false⟩))
  min (projBound G3 1 2 true) (min (projBound G3 0 1 false - 2) (projBound G3 0 2 false - 2))

/-- the dual cell bound -/
def dualCellBound (e : ℕ) (x : ℚ) (ex : ℕ → PType → Bool) : ℤ := dualBoundOf (dualCandTypes e x) ex

/-! ### Cells -/

/-- no integer lies strictly between `u` and `v` -/
def noIntBetween (u v : ℚ) : Bool := decide (max u v ≤ (⌊min u v⌋ : ℚ) + 1)

/-- the open cell `(lo, hi)` contains `x0` and no wall of the endpoints `Es`:
no `a_E x + b_E` and no `(a_E - a_F) x + (b_E - b_F)` (`a_E ≠ a_F`) crosses an integer -/
def wallFree (Es : List Endpt) (lo hi x0 : ℚ) : Bool :=
  decide (lo < x0) && decide (x0 < hi) &&
  Es.all (fun E => decide (E.a = 0) || noIntBetween (E.a * lo + E.b) (E.a * hi + E.b)) &&
  Es.all (fun E => Es.all (fun F => decide (E.a = F.a) ||
    noIntBetween ((E.a - F.a) * lo + (E.b - F.b)) ((E.a - F.a) * hi + (E.b - F.b))))

/-- single-endpoint wall conditions only -/
def wallFree1 (Es : List Endpt) (lo hi x0 : ℚ) : Bool :=
  decide (lo < x0) && decide (x0 < hi) &&
  Es.all (fun E => decide (E.a = 0) || noIntBetween (E.a * lo + E.b) (E.a * hi + E.b))

/-- all endpoints used for the residue class `e` (dual, forward, gamma) -/
def allEndpts (e : ℕ) : List Endpt :=
  endpts (dualZ ++ dualP) e ++ endpts (fwdZ ++ fwdP) e ++ endpts (gammaF.map (·.1)) e

end Zeta2L2Chi3.Arith

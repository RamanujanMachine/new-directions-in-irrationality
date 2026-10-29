/-
# The forward/dual pairing identity `M(n) K(n+1) Q(n)ᵀ = c(n) K(n)` (ALG03)

Checked as a polynomial identity in one variable `s = n + 1` (all matrices evaluated at `s - 1`
via `PE.shift`), after clearing the denominators `D_M`, `D_Q`, `c_den`, and the constant
denominators of `K`.
-/
import Zeta2L2Chi3.Forward
import Zeta2L2Chi3.NV

open Finset

namespace Zeta2L2Chi3

/-- a polynomial in the second variable `s` -/
def litS (l : List ℤ) : PE := PE.lit (l.map fun c => [c])

lemma litS_val {R : Type*} [CommRing R] (l : List ℤ) (x s : R) : (litS l).val x s = hornerR l s := by
  simp only [litS, PE.val]
  induction l with
  | nil => simp [litVal, hornerR]
  | cons c cs ih => simp [litVal, hornerR, ih]

/-- finite sums of expressions -/
def sumPE : List PE → PE
  | [] => PE.lit [[0]]
  | e :: es => PE.add e (sumPE es)

lemma val_sumPE {R : Type*} [CommRing R] (l : List PE) (x s : R) :
    (sumPE l).val x s = (l.map fun e => e.val x s).sum := by
  induction l with
  | nil => simp [sumPE, PE.val, litVal, hornerR]
  | cons e es ih => simp [sumPE, PE.val, ih]

/-- common integer multiple of the `K` denominators -/
def KL : ℤ := 6

/-- `(KL / Kden_{lm}) · Knum_{lm}(s)` -/
def KsPE (l : Fin 4) (m : Fin 3) : PE := PE.mul (PE.lit [[KL / Data.Kden l m]]) (litS (Data.Knum l m))

/-- entry `(i, j)` of `c_den M̃(s-1) K̃(s) Q̃(s-1)ᵀ - c_num(s-1) D_M(s-1) D_Q(s-1) K̃(s-1)` -/
def alg03PE (i : Fin 4) (j : Fin 3) : PE :=
  PE.sub
    (PE.mul (PE.shift (litS Data.cden))
      (sumPE ((List.finRange 4).flatMap fun l => (List.finRange 3).map fun m =>
        PE.mul (PE.mul (PE.shift (litS (Data.Mnum i l))) (KsPE l m)) (PE.shift (litS (Data.Qnum j m))))))
    (PE.mul (PE.mul (PE.mul (PE.shift (litS (Data.cnum 0 0))) (PE.shift (litS Data.Mden)))
      (PE.shift (litS Data.Qden))) (PE.shift (KsPE i j)))

theorem alg03_check : ∀ i : Fin 4, ∀ j : Fin 3, (alg03PE i j).check (10 ^ 330) := by decide +kernel

end Zeta2L2Chi3

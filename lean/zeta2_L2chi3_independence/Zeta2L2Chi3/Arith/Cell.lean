/-
# Chambers: the residue-class structure is constant on a wall-free cell

For `p` large, `p ≡ e (mod 6)` and `n = L p + n'` with `n'/p` in a wall-free cell (with margin),
the endpoint floors of every residue class `r < p` are `q*_E - [E ∈ S]` for a candidate set `S`
computed at an interior point `x* = L + x0`.
-/
import Zeta2L2Chi3.Arith.Checker
import Zeta2L2Chi3.Arith.Family
import Zeta2L2Chi3.Arith.CellAux

namespace Zeta2L2Chi3.Arith

/-- `⌊(A - r)/p⌋ = ⌊A/p⌋ - [A mod p < r]` -/
theorem floor_split (A : ℤ) (p r : ℕ) (hp : 0 < p) (hr : r < p) :
    ⌊((A : ℚ) - r) / p⌋ = A / (p : ℤ) - (if A % (p : ℤ) < r then 1 else 0) :=
  CellAux.floor_split' A p r hp hr

theorem cell_floors (e : ℕ) (Es : List Endpt) (lo hi x0 : ℚ) (hw : wallFree Es lo hi x0 = true)
    (hint : ∀ E ∈ Es, ∀ n p : ℕ, p % 6 = e → ∃ z : ℤ, E.val n p = z) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p r : ℕ, P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → r < p →
      ∃ S ∈ candSets Es (L + x0),
        (∀ i < Es.length, (Es[i]!).floorAt n p r = floorsOf Es (L + x0) S i) ∧
        (r = 0 → S = Es.map (fun _ => false)) :=
  CellAux.cell_floors' e Es lo hi x0 hw hint L

/-! ### Corollaries -/

/-- at `r = 0` every endpoint floor is the predicted `q*` -/
theorem cell_floors_zero (e : ℕ) (Es : List Endpt) (lo hi x0 : ℚ)
    (hw : wallFree Es lo hi x0 = true)
    (hint : ∀ E ∈ Es, ∀ n p : ℕ, p % 6 = e → ∃ z : ℤ, E.val n p = z) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p →
      ∀ E ∈ Es, E.floorAt n p 0 = qstar E (L + x0) := by
  obtain ⟨P0, K, h⟩ := cell_floors e Es lo hi x0 hw hint L
  refine ⟨max P0 1, K, fun n p hP hpe h1 h2 E hE => ?_⟩
  obtain ⟨S, -, hfl, hr0⟩ := h n p 0 (le_of_max_le_left hP) hpe h1 h2
    (lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hP))
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hE
  have := hfl i hi
  rw [getElem!_pos Es i hi] at this
  rw [this, hr0 rfl]
  unfold floorsOf
  simp [List.getD_eq_getElem?_getD, getElem!_pos Es i hi]

theorem endpts_hint (fs : List Fam) (hfs : ∀ f ∈ fs, f.be.den ∣ 6) (e : ℕ) (he : e = 1 ∨ e = 5) :
    ∀ E ∈ endpts fs e, ∀ n p : ℕ, p % 6 = e → ∃ z : ℤ, E.val n p = z := by
  intro E hE n p hpe
  simp only [endpts, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hE
  obtain ⟨f, hf, rfl | rfl⟩ := hE
  · exact Fam.lo_val_int f (hfs f hf) e he p n hpe
  · exact Fam.hi_val_int f (hfs f hf) e he p n hpe

theorem mkDualType_congr (e : ℕ) (F G : ℕ → ℤ) (j : ℕ) (h : ∀ i < 10, F i = G i) :
    mkDualType e F j = mkDualType e G j := by
  simp only [mkDualType, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
    h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num),
    h 7 (by norm_num), h 8 (by norm_num), h 9 (by norm_num)]

theorem fwdH_congr (F G : ℕ → ℤ) (h : ∀ i < 10, F i = G i) : fwdH F = fwdH G := by
  simp only [fwdH, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
    h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num),
    h 7 (by norm_num), h 8 (by norm_num), h 9 (by norm_num)]

theorem foldr_min_le {l : List ℤ} {x : ℤ} (hx : x ∈ l) : l.foldr min 0 ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

theorem dual_den : ∀ f ∈ dualZ ++ dualP, f.be.den ∣ 6 := by decide +kernel
theorem fwd_den : ∀ f ∈ fwdZ ++ fwdP, f.be.den ∣ 6 := by decide +kernel
theorem gamma_den : ∀ f ∈ gammaF.map (·.1), f.be.den ∣ 6 := by decide +kernel

/-- every dual packet type of a residue class is a candidate type -/
theorem dualType_mem_cand (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hw : wallFree (endpts (dualZ ++ dualP) e) lo hi x0 = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p r : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → r < p →
      dualTypeAt n p r ∈ dualCandTypes e (L + x0) := by
  obtain ⟨P0, K, h⟩ := cell_floors e (endpts (dualZ ++ dualP) e) lo hi x0 hw
    (endpts_hint _ dual_den e he) L
  refine ⟨P0, K, fun n p r _ hP hpe h1 h2 hr => ?_⟩
  obtain ⟨S, hS, hfl, hr0⟩ := h n p r hP hpe h1 h2 hr
  have hlen : (endpts (dualZ ++ dualP) e).length = 10 := rfl
  unfold dualTypeAt dualCandTypes
  rw [hpe, mkDualType_congr e _ (floorsOf (endpts (dualZ ++ dualP) e) (L + x0) S) _
    (fun i hi => hfl i (by rw [hlen]; exact hi))]
  refine List.mem_flatMap.2 ⟨S, hS, ?_⟩
  by_cases hr0' : r = 0
  · subst hr0'
    rw [hr0 rfl]
    simp
  · rw [ite_eq_right hr0']
    split_ifs <;> simp

/-- forward: the minimum over residue classes is at least the candidate minimum -/
theorem fwdH_ge_cand (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hw : wallFree (endpts (fwdZ ++ fwdP) e) lo hi x0 = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p r : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → r < p →
      ((candSets (endpts (fwdZ ++ fwdP) e) (L + x0)).map
          (fun S => fwdH (floorsOf (endpts (fwdZ ++ fwdP) e) (L + x0) S))).foldr min 0
        ≤ fwdH (fun E => ((endpts (fwdZ ++ fwdP) e)[E]!).floorAt n p r) := by
  obtain ⟨P0, K, h⟩ := cell_floors e (endpts (fwdZ ++ fwdP) e) lo hi x0 hw
    (endpts_hint _ fwd_den e he) L
  refine ⟨P0, K, fun n p r _ hP hpe h1 h2 hr => ?_⟩
  obtain ⟨S, hS, hfl, -⟩ := h n p r hP hpe h1 h2 hr
  have hlen : (endpts (fwdZ ++ fwdP) e).length = 10 := rfl
  rw [fwdH_congr _ (floorsOf (endpts (fwdZ ++ fwdP) e) (L + x0) S)
    (fun i hi => hfl i (by rw [hlen]; exact hi))]
  exact foldr_min_le (List.mem_map.2 ⟨S, hS, rfl⟩)

/-- gamma factor counts at r = 0 -/
theorem gamma_counts (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hw : wallFree (endpts (gammaF.map (·.1)) e) lo hi x0 = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p →
      ∀ fm ∈ gammaF, (fm.1.hi e).floorAt n p 0 - (fm.1.lo e).floorAt n p 0
        = qstar (fm.1.hi e) (L + x0) - qstar (fm.1.lo e) (L + x0) := by
  obtain ⟨P0, K, h⟩ := cell_floors_zero e _ lo hi x0 hw (endpts_hint _ gamma_den e he) L
  refine ⟨P0, K, fun n p _ hP hpe h1 h2 fm hfm => ?_⟩
  have hmem : fm.1 ∈ gammaF.map (·.1) := List.mem_map.2 ⟨fm, hfm, rfl⟩
  have hlo : fm.1.lo e ∈ endpts (gammaF.map (·.1)) e :=
    List.mem_flatMap.2 ⟨fm.1, hmem, by simp⟩
  have hhi : fm.1.hi e ∈ endpts (gammaF.map (·.1)) e :=
    List.mem_flatMap.2 ⟨fm.1, hmem, by simp⟩
  rw [h n p hP hpe h1 h2 _ hlo, h n p hP hpe h1 h2 _ hhi]

/-- `cell_floors_zero` with only the single-endpoint wall conditions -/
theorem cell_floors_zero1 (e : ℕ) (Es : List Endpt) (lo hi x0 : ℚ)
    (hw : wallFree1 Es lo hi x0 = true)
    (hint : ∀ E ∈ Es, ∀ n p : ℕ, p % 6 = e → ∃ z : ℤ, E.val n p = z) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p →
      ∀ E ∈ Es, E.floorAt n p 0 = qstar E (L + x0) :=
  CellAux.cell_floors_zero1' e Es lo hi x0 hw hint L

/-- gamma factor counts at r = 0 (single-endpoint wall conditions only) -/
theorem gamma_counts1 (e : ℕ) (he : e = 1 ∨ e = 5) (lo hi x0 : ℚ)
    (hw : wallFree1 (endpts (gammaF.map (·.1)) e) lo hi x0 = true) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, p.Prime → P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p →
      ∀ fm ∈ gammaF, (fm.1.hi e).floorAt n p 0 - (fm.1.lo e).floorAt n p 0
        = qstar (fm.1.hi e) (L + x0) - qstar (fm.1.lo e) (L + x0) := by
  obtain ⟨P0, K, h⟩ := cell_floors_zero1 e _ lo hi x0 hw (endpts_hint _ gamma_den e he) L
  refine ⟨P0, K, fun n p _ hP hpe h1 h2 fm hfm => ?_⟩
  have hmem : fm.1 ∈ gammaF.map (·.1) := List.mem_map.2 ⟨fm, hfm, rfl⟩
  have hlo : fm.1.lo e ∈ endpts (gammaF.map (·.1)) e :=
    List.mem_flatMap.2 ⟨fm.1, hmem, by simp⟩
  have hhi : fm.1.hi e ∈ endpts (gammaF.map (·.1)) e :=
    List.mem_flatMap.2 ⟨fm.1, hmem, by simp⟩
  rw [h n p hP hpe h1 h2 _ hlo, h n p hP hpe h1 h2 _ hhi]

end Zeta2L2Chi3.Arith

/-
# Auxiliary machinery for Lemma A, part 2: the class decomposition

The class-`r` row vector is `Σ_j φ_j p^{h+1+j} V_j + br · e₀ + Σ_c rem_c · e_c` with `p`-integral
`φ_j`, `br ∈ p^{regW} ℤ_(p)` and `rem_c ∈ p^{h+Jt+2} ℤ_(p)`.
-/
import Zeta2L2Chi3.Arith.LemmaAAux

namespace Zeta2L2Chi3.Arith
namespace LA

/-- hypotheses on the zero/pole data -/
structure Hyp (p : ℕ) (Z : List ℚ) (P : List Rec) : Prop where
  hZd : ∀ z ∈ Z, ¬ p ∣ z.den
  hPd : ∀ q ∈ P, ¬ p ∣ q.1.den
  hnd : (P.map Prod.fst).Nodup
  hdiff : ∀ q ∈ P, ∀ q' ∈ P, q.1 ≠ q'.1 → padicValRat p (q.1 - q'.1) ≤ 1
  hH : ∀ q ∈ P, ∀ m : ℕ, (m : ℚ) < q.1 → padicValRat p (q.1 - m) ≤ 1
  hw : ∀ q ∈ P, ∀ r, r < p → cls p r q.1 = true →
    VGe p 1 (q.2.2 - Hq (Tv p r q.1) / (p : ℚ) ^ 2 - Gsq r)

theorem vec_apply (a : Fin 6 → ℚ) (v : Fin 6 → Fin 4 → ℚ) (b : ℚ) (d : Fin 4 → ℚ) (i : Fin 4) :
    (∑ j : Fin 6, a j • v j + b • unitVec 0 + ∑ c : Fin 4, d c • unitVec c) i =
      ∑ j : Fin 6, a j * v j i + (if i = 0 then b else 0) + d i := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVec,
    Fin.sum_univ_four]
  fin_cases i <;> simp

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem vge_pow_p (m : ℕ) : VGe p m ((p : ℚ) ^ m) := by
  have := VGe.zpow (p := p) (m : ℤ); rwa [zpow_natCast] at this

theorem term_vge {a b : ℚ} (ha : VGe p 0 a) (hb : VGe p 0 b) (j : ℕ) :
    VGe p j (a * (p : ℚ) ^ j * b ^ j) := by
  have := (ha.mul (vge_pow_p j)).mul (hb.pow j)
  simpa using this

theorem vge_one : VGe p 0 (1 : ℚ) := by simpa using VGe.natCast (p := p) 1

theorem ind_vge (c : ℕ) (q : Rec) : VGe p 0 (ind c q) := by
  unfold ind; split_ifs
  · exact vge_one
  · exact VGe.zero 0

theorem class_decomp (Z : List ℚ) (P : List Rec) (H : Hyp p Z P) (r k jmin : ℕ) (hr : r < p)
    (hk : 1 ≤ k) (hj : jmin = if r = 0 then 1 else 0) :
    ∃ (φ : Fin 6 → ℚ) (br : ℚ) (rem : Fin 4 → ℚ),
      (∀ j, VGe p 0 (φ j)) ∧ (jmin = 1 → φ 0 = 0) ∧ VGe p (typ p Z P r jmin).regW br ∧
      (∀ c, VGe p ((typ p Z P r jmin).h + Jt + 2) (rem c)) ∧
      rowVec p Z P k (P.filter (fun q => cls p r q.1)) =
        ∑ j : Fin 6, (φ j * (p : ℚ) ^ ((typ p Z P r jmin).h + 1 + ((j : ℕ) : ℤ))) •
          (typ p Z P r jmin).V j + br • unitVec 0 + ∑ c : Fin 4, rem c • unitVec c := by
  set t := typ p Z P r jmin with ht
  set Pr := P.filter (fun q => cls p r q.1) with hPr
  have hp0 := p_ne_zero' (p := p)
  have hjm : jmin ≤ 1 := by rw [hj]; split_ifs <;> simp
  have htj : t.jmin = jmin := rfl
  obtain ⟨u, hTay, hu0⟩ := Phi_taylor (p := p) Z P r k hk H.hZd H.hPd
  have hu0' : jmin = 1 → u 0 = 0 := fun h => hu0 (by
    by_contra hr0; rw [hj, if_neg hr0] at h; exact absurd h (by norm_num))
  set Φ := Phi p Z P r k with hΦ
  have memP : ∀ q ∈ Pr, q ∈ P ∧ cls p r q.1 = true := fun q hq => List.mem_filter.mp hq
  have hb : ∀ q ∈ Pr, VGe p 0 (Tv p r q.1) := fun q hq =>
    Tv_int (H.hPd q (memP q hq).1) (memP q hq).2
  have hR : ∀ q ∈ Pr, VGe p 0 (t.R (Tv p r q.1)) := fun q hq =>
    R_int Z P r jmin H.hZd H.hPd H.hdiff q (memP q hq).1 (memP q hq).2
  have hvq : ∀ q ∈ Pr, vres Z P q.1 * q.1 ^ k =
      (p : ℚ) ^ (t.h + 1) * t.R (Tv p r q.1) * Φ (Tv p r q.1) := fun q hq =>
    vres_mul_pow Z P r jmin k H.hnd q (memP q hq).1 (memP q hq).2
  have hE : ∀ q ∈ Pr, VGe p 6 (Φ (Tv p r q.1) -
      ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * Tv p r q.1 ^ (j : ℕ)) := fun q hq =>
    (hTay.2 _ (hb q hq)).2
  have hΦ0 : ∀ q ∈ Pr, VGe p jmin (Φ (Tv p r q.1)) := by
    intro q hq
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hjm with h0 | h1
    · rw [h0]; exact (hTay.2 _ (hb q hq)).1
    · rw [h1]
      have hs : VGe p 1 (∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * Tv p r q.1 ^ (j : ℕ)) := by
        apply VGe.finset_sum; intro j _
        by_cases hj0 : (j : ℕ) = 0
        · have : j = 0 := Fin.ext hj0
          subst this; rw [hu0' h1]; simp only [zero_mul]; exact VGe.zero 1
        · exact (term_vge (hTay.1 j) (hb q hq) (j : ℕ)).mono (by omega)
      have := ((hE q hq).mono (by norm_num : (1 : ℤ) ≤ 6)).add hs
      simpa using this
  -- the vectors `V_j` as sums over the class poles
  have hV0 : ∀ j : ℕ, t.V j 0 =
      (Pr.map (fun q => (-Hq (Tv p r q.1)) * (t.R (Tv p r q.1) * Tv p r q.1 ^ j))).sum := by
    intro j
    simp only [PType.V, ht, typ, List.map_map]
    rw [← neg_one_mul, ← sum_map_mul_left']
    congr 1; apply List.map_congr_left; intro q _; simp only [Function.comp]; ring
  have hVc : ∀ c : ℕ, ∀ j : ℕ, ((t.ps.filter (fun q => q.2 = c)).map
      (fun q => t.R q.1 * q.1 ^ j)).sum =
      (Pr.map (fun q => ind c q * (t.R (Tv p r q.1) * Tv p r q.1 ^ j))).sum := by
    intro c j
    rw [show t.ps = Pr.map (fun q => (Tv p r q.1, q.2.1)) from rfl, List.filter_map,
      List.map_map, sum_map_filter]
    congr 1; apply List.map_congr_left; intro q _
    simp only [Function.comp, ind]
    split_ifs <;> simp_all
  have hV1 : ∀ j : ℕ, t.V j 1 =
      (Pr.map (fun q => ind 1 q * (t.R (Tv p r q.1) * Tv p r q.1 ^ j))).sum := fun j => hVc 1 j
  have hV2 : ∀ j : ℕ, t.V j 2 =
      (Pr.map (fun q => ind 2 q * (t.R (Tv p r q.1) * Tv p r q.1 ^ j))).sum := fun j => hVc 2 j
  have hV3 : ∀ j : ℕ, t.V j 3 =
      (Pr.map (fun q => (1 : ℚ) * (t.R (Tv p r q.1) * Tv p r q.1 ^ j))).sum := by
    intro j
    simp only [PType.V, ht, typ, List.map_map, one_mul]
    rfl
  -- the expansion of a weighted row sum
  have hS : ∀ G : Rec → ℚ, (Pr.map (fun q => G q * (vres Z P q.1 * q.1 ^ k))).sum =
      ∑ j : Fin 6, (u j * (p : ℚ) ^ (t.h + 1 + ((j : ℕ) : ℤ))) *
        (Pr.map (fun q => G q * (t.R (Tv p r q.1) * Tv p r q.1 ^ (j : ℕ)))).sum +
      (Pr.map (fun q => G q * ((p : ℚ) ^ (t.h + 1) * t.R (Tv p r q.1) *
        (Φ (Tv p r q.1) - ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * Tv p r q.1 ^ (j : ℕ))))).sum := by
    intro G
    rw [List.map_congr_left (fun q hq => congrArg (G q * ·) (hvq q hq))]
    exact expand Pr G (fun q => t.R (Tv p r q.1)) (fun q => Tv p r q.1) u Φ (t.h + 1)
  set remG : (Rec → ℚ) → ℚ := fun G => (Pr.map (fun q => G q * ((p : ℚ) ^ (t.h + 1) *
      t.R (Tv p r q.1) * (Φ (Tv p r q.1) -
        ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * Tv p r q.1 ^ (j : ℕ))))).sum with hremG
  have hrem : ∀ G : Rec → ℚ, (∀ q ∈ Pr, VGe p 0 (G q)) → VGe p (t.h + Jt + 2) (remG G) := by
    intro G hG
    apply VGe.list_sum; intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    have := (hG q hq).mul ((((VGe.zpow (p := p) (t.h + 1)).mul (hR q hq)).mul (hE q hq)))
    exact this.mono (by simp only [Jt]; push_cast; omega)
  set δ : Rec → ℚ := fun q => q.2.2 - Hq (Tv p r q.1) / (p : ℚ) ^ 2 - Gsq r with hδ
  set Y : ℚ := ∑ j : Fin 6, (u j * (p : ℚ) ^ (t.h + 1 + ((j : ℕ) : ℤ))) * t.V j 3 with hY
  set br : ℚ := (-(p : ℚ) ^ 2 * Gsq r) * (Y + remG (fun _ => 1)) +
    (-(p : ℚ) ^ 2) * (Pr.map (fun q => δ q * (vres Z P q.1 * q.1 ^ k))).sum with hbr
  refine ⟨u, br, ![remG (fun q => -Hq (Tv p r q.1)), remG (ind 1), remG (ind 2), remG (fun _ => 1)],
    hTay.1, hu0', ?_, ?_, ?_⟩
  · -- the regular harmonic bracket
    have hndt : (t.ps.map Prod.fst).Nodup := by
      have e : t.ps.map Prod.fst = (Pr.map Prod.fst).map (Tv p r) := by
        simp [ht, typ, List.map_map, Function.comp_def, hPr]
      rw [e]
      exact (H.hnd.sublist ((List.filter_sublist).map _)).map (fun a b h => Tv_inj.mp h)
    have hYv : VGe p (t.h + 1 + max (jmin : ℤ) (-t.h - 1)) Y := by
      apply VGe.finset_sum; intro j _
      by_cases h1 : t.h + ((j : ℕ) : ℤ) ≤ -2
      · rw [PType.V3_low t hndt (j : ℕ) h1, mul_zero]; exact VGe.zero _
      by_cases h2 : (j : ℕ) < jmin
      · have hj1 : jmin = 1 := by omega
        have : j = 0 := Fin.ext (by omega)
        subst this; rw [hu0' hj1, zero_mul, zero_mul]; exact VGe.zero _
      have hV : VGe p 0 (t.V j 3) := by
        rw [hV3]; apply VGe.list_sum; intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
        have := vge_one.mul ((hR q hq).mul ((hb q hq).pow (j : ℕ)))
        simpa using this
      have := ((hTay.1 j).mul (VGe.zpow (p := p) (t.h + 1 + ((j : ℕ) : ℤ)))).mul hV
      exact this.mono (by
        have : max (jmin : ℤ) (-t.h - 1) ≤ ((j : ℕ) : ℤ) := max_le (by omega) (by omega)
        omega)
    have hrem1 := hrem (fun _ => 1) (fun _ _ => vge_one)
    have hP1 : VGe p t.regW ((-(p : ℚ) ^ 2 * Gsq r) * (Y + remG (fun _ => 1))) := by
      have hsum : VGe p (min (t.h + 1 + max (jmin : ℤ) (-t.h - 1)) (t.h + 2 + jmin))
          (Y + remG (fun _ => 1)) :=
        (hYv.mono (min_le_left _ _)).add (hrem1.mono (by
          have := min_le_right (t.h + 1 + max (jmin : ℤ) (-t.h - 1)) (t.h + 2 + jmin)
          simp only [Jt]; push_cast; omega))
      have hc : VGe p 2 (-(p : ℚ) ^ 2 * Gsq r) := by
        have := (vge_pow_p (p := p) 2).neg.mul (Gsq_int (p := p) hr)
        simpa using this
      have := hc.mul hsum
      unfold PType.regW; rw [htj]
      exact this.mono (by omega)
    have hP2 : VGe p t.regW ((-(p : ℚ) ^ 2) *
        (Pr.map (fun q => δ q * (vres Z P q.1 * q.1 ^ k))).sum) := by
      have hsum : VGe p (1 + (t.h + 1 + 0 + jmin))
          (Pr.map (fun q => δ q * (vres Z P q.1 * q.1 ^ k))).sum := by
        apply VGe.list_sum; intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
        rw [hvq q hq]
        exact (H.hw q (memP q hq).1 r hr (memP q hq).2).mul
          (((VGe.zpow (p := p) (t.h + 1)).mul (hR q hq)).mul (hΦ0 q hq))
      have hc : VGe p 2 (-(p : ℚ) ^ 2) := by
        have := (vge_pow_p (p := p) 2).neg
        simpa using this
      have := hc.mul hsum
      unfold PType.regW; rw [htj]
      exact this.mono (by
        have := min_le_right (t.h + 1 + max (jmin : ℤ) (-t.h - 1)) (t.h + 2 + jmin)
        omega)
    exact hP1.add hP2
  · intro c
    fin_cases c
    · exact hrem _ (fun q hq => (Hq_int (H.hPd q (memP q hq).1) (memP q hq).2
        (H.hH q (memP q hq).1)).neg)
    · exact hrem _ (fun q _ => ind_vge 1 q)
    · exact hrem _ (fun q _ => ind_vge 2 q)
    · exact hrem _ (fun _ _ => vge_one)
  · funext i
    rw [vec_apply]
    have h0 := hS (fun q => -Hq (Tv p r q.1))
    have h1 := hS (ind 1)
    have h2 := hS (ind 2)
    have h3 := hS (fun _ => 1)
    beta_reduce at h0 h1 h2 h3
    fin_cases i
    · -- coordinate 0
      have h0a : (p : ℚ) ^ 2 * -(Pr.map (fun q => vres Z P q.1 * q.2.2 * q.1 ^ k)).sum =
          (Pr.map (fun q => -Hq (Tv p r q.1) * (vres Z P q.1 * q.1 ^ k))).sum +
          (-(p : ℚ) ^ 2 * Gsq r) * (Pr.map (fun q => 1 * (vres Z P q.1 * q.1 ^ k))).sum +
          (-(p : ℚ) ^ 2) * (Pr.map (fun q => δ q * (vres Z P q.1 * q.1 ^ k))).sum := by
        rw [← sum_map_mul_left', ← sum_map_mul_left', ← sum_map_add', ← sum_map_add',
          mul_neg, ← neg_mul, ← sum_map_mul_left']
        congr 1; apply List.map_congr_left; intro q _
        simp only [hδ]; field_simp; ring
      simp only [rowVec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, if_true]
      rw [h0a, h0, h3, hbr, hY]
      simp only [hV0, hV3, remG]
      ring
    · simp only [rowVec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h1]
      simp only [hV1, remG]
      simp
    · simp only [rowVec]
      rw [h2]
      simp only [remG]
      simp
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      exact (hV2 j).symm
    · simp only [rowVec]
      rw [show (Pr.map (fun q => vres Z P q.1 * q.1 ^ k)) =
        (Pr.map (fun q => 1 * (vres Z P q.1 * q.1 ^ k))) by simp, h3]
      simp only [remG]
      simp
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      exact ((hV3 j).trans (by simp)).symm

end

end LA
end Zeta2L2Chi3.Arith

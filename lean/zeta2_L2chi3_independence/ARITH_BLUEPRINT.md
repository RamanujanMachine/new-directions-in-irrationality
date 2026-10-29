# Arithmetic blueprint (content lower bound, RateHyp.content)

Goal: `∀ ε > 0, ∀ᶠ n, exp((β-ε)n) ≤ cont(w_n)` with β = -13335/10000 (true value ≈ -1.3334588;
the δ>1e-4 criterion needs β > -1.333673 given the spectral rates).

`log cont(w_n) = ∑_p v_p(cont w_n) log p`, `v_p(cont w) = min_i v_p(w_i)` (Content.lean: `w = cont · prim`,
`prim` primitive).  Lower bounds per prime p:

| regime | bound on v_p(cont w_n) | source |
|---|---|---|
| p > 40n+10 | ≥ 0 | dual formula, all denominators < p |
| 5 ≤ p, p² > 132n+30, x=n/p in a cell (e,L,a,b), away from walls, p ∉ E | ≥ max(Fwd, Dual) | packet lemmas + chamber data |
| same range, near a wall or p ∈ E or p | g(n) | ≥ -K₀ | crude |
| 5 ≤ p ≤ √(132n+30) | ≥ -K₁ (log(Cn)/log p + 1) | Legendre counting |
| p = 2, 3 | ≥ 12n - K log n, 18n - K log n | Legendre counting |

## Families (unified)
A family is an arithmetic progression of points `c + i` (`0 ≤ i < len`), `c = α n + γ` rational with
denominator d ∈ {1,2,3}.  For prime p ≥ 5 and residue r ∈ [0,p): `i_f(r) ∈ [0,p)` with `c + i_f ≡ r`,
`count_f(r) = #{i < len : i ≡ i_f(r)}`, T-values `T_f0(r) + k` (`k < count`), `T_f0 = (c + i_f - r)/p`.
* forward (R_n): zeros `-(2n+1)…-(12n+1)`, `-4/3 - i (i ≤ 6n)`, `-(2n+3/2) - i (i ≤ 3n)`;
  poles `0…10n+1`, `-n…8n+1` (two families ⇒ double poles on the overlap).
* dual (F_n): zeros `-1…-(10n+1)`, `n-1…-(8n+1)`; poles int `2n…12n+1`, third `1/3…6n+4/3`,
  half `2n+1/2…5n+3/2`.

## FWD-VAL (forward packet lemma)
For p ≥ 5, p² > 132n+30: `v_p(cont f_n) ≥ min(0, min_r h(r))`, `h(r) = Σ_zero count - Σ_pole count`.
Proof: `a_k` = double-pole coefficient: `v_p(a_k) ≥ h(k mod p) + 2`, `v_p(b_k) ≥ h+1`;
`v_p(H^{(2)}) ≥ -2`, `v_p(H^{(1)}) ≥ -1`; polynomial part p-integral (division by monic integer poly);
P_n p-integral.  Then `v_p(cont w_n) ≥ that + v_p(Δ_n)` by (3.1).

## DELTA-VAL
`Δ_n = ∏_{j<n} det Q(j)`, `det Q(j) = QdetConst ∏ (a j + b)^{e} / (5³ ∏ (a j + b)^3 over QdenLin)`;
`v_p(∏_{j<n} (aj+b)) = #{j<n : p | aj+b}` when p² > a n + b, p ∤ a.

## DUAL-VAL (lattice lemma), see PROOF.txt §6 and positive_delta_certificate.py `vectors`, `cell`
Lemma A: each class contribution ∈ Λ(type(r)).  Lemma B: Λ monotone in the type list.
Lemma C: both columns ∈ Λ(L) ∩ {total = 0} and p ∉ E(L) ⇒ minors ≥ algorithm bound.
Lemma D (coverage): type(r) ∈ enumerate(cell) for all r, when x is away from walls.
Computation: 4029 distinct packet types, residues via interval recurrences (O(points + poles·families)).

## SUM
PNT in APs (WeakPNT_AP, q = 6) on finitely many cells for L ≤ L₁, Chebyshev tail for L > L₁,
periodicity of the forward profile in L ≥ 1, o(n) losses for walls/small primes/exceptional primes.

## NUM
β via rational witnesses: finite density (exact rational), tail Σ_{L≥20} via T_M bounds, log 2, log 3.

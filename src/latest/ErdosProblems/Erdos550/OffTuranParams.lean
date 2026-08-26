import Mathlib
import ErdosProblems.Erdos550.TuranArithmetic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative parameter-chase lemmas for the direct off-Turán embedding

These are the real-arithmetic steps of the off-Turán embedding proof.
They formalise the paper's numeric bookkeeping:

* `avgdeg_after_cleaning` — subtracting the Szemerédi cleaning loss from the raw
  average degree (`d̄(Gᵇ) ≥ n + 200ηN`, loss `< 100ηN`  ⟹  `d̄(Gᵇ*) ≥ n + 100ηN`);
* `matched_cluster_excess` — the mass outside the matching, `(ηℓ+2)·s ≤ 2ηN`;
* `head_degree_lower` — the head cluster degrees `D_X, D_Y ≥ n + 78ηN`;
* `lambda_feasible` — nonemptiness of the split interval for `λ` (`eq:lambdacap`),
  the ratio bookkeeping that balances the two head loads.

They discharge the numeric side-conditions when assembling the
regularity data, the heavy head edge (`Erdos550.exists_dense_regular_pair_in_family`)
and the regular matching into the tree-embedding engine.
-/

namespace Erdos550

/-- **Average degree after cleaning.**  If the raw average degree is at least
`base + 200ηN` and the Szemerédi cleaning loses less than `100ηN`, the cleaned
graph still has average degree at least `base + 100ηN`. -/
lemma avgdeg_after_cleaning (base η N loss davg : ℝ)
    (hraw : base + 200 * η * N ≤ davg) (hloss : loss < 100 * η * N) :
    base + 100 * η * N ≤ davg - loss := by
  linarith

/-- **Matched-cluster excess.**  With `ℓ` clusters of size `s` (`ℓs ≤ N`,
`m₀·s ≤ N`) and `2 ≤ η·m₀`, the total size of the `≤ ηℓ + 2` clusters outside a
maximal matching is at most `2ηN`. -/
lemma matched_cluster_excess (η ℓ s N m₀ : ℝ)
    (hℓs : ℓ * s ≤ N) (hm : m₀ * s ≤ N) (hηm : 2 ≤ η * m₀)
    (hη : 0 ≤ η) (hs : 0 ≤ s) :
    (η * ℓ + 2) * s ≤ 2 * η * N := by
  have h2s : 2 * s ≤ η * N := by
    have : 2 * s ≤ η * m₀ * s := by nlinarith
    nlinarith
  nlinarith

/-- **Head degree lower bound.**  A heavy cluster degree `D ≥ base + 80ηN`, minus
the matched-cluster excess `≤ 2ηN`, is still at least `base + 78ηN`. -/
lemma head_degree_lower (base η N D excess : ℝ)
    (hD : base + 80 * η * N ≤ D) (hexcess : excess ≤ 2 * η * N) :
    base + 78 * η * N ≤ D - excess := by
  linarith

/-- **Feasible split interval for `λ`.**  If `(x+margin)/D_X + (y+margin)/D_Y < 1`
with positive denominators and nonnegative numerators, then there is `λ ∈ [0,1]`
with `(x+margin)/D_X ≤ λ ≤ 1 − (y+margin)/D_Y`; equivalently
`λ·D_X ≥ x+margin` and `(1−λ)·D_Y ≥ y+margin`. -/
lemma lambda_feasible (Dx Dy x y margin : ℝ) (hDx : 0 < Dx) (hDy : 0 < Dy)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hm : 0 ≤ margin)
    (hsum : (x + margin) / Dx + (y + margin) / Dy < 1) :
    ∃ lam : ℝ, (x + margin) / Dx ≤ lam ∧ lam ≤ 1 - (y + margin) / Dy ∧
      0 ≤ lam ∧ lam ≤ 1 := by
  refine ⟨(x + margin) / Dx, le_refl _, by linarith, by positivity, ?_⟩
  have : (y + margin) / Dy ≥ 0 := by positivity
  linarith

/-- The multiplicative form of `lambda_feasible`: from `λ` in the feasible
interval, `λ·D_X ≥ x + margin` and `(1−λ)·D_Y ≥ y + margin`. -/
lemma lambda_caps (Dx Dy x y margin lam : ℝ) (hDx : 0 < Dx) (hDy : 0 < Dy)
    (hlo : (x + margin) / Dx ≤ lam) (hhi : lam ≤ 1 - (y + margin) / Dy) :
    x + margin ≤ lam * Dx ∧ y + margin ≤ (1 - lam) * Dy := by
  constructor
  · rw [div_le_iff₀ hDx] at hlo; linarith
  · have h2 : (y + margin) / Dy ≤ 1 - lam := by linarith
    rw [div_le_iff₀ hDy] at h2; linarith

open Finset in
/-- **Turán gap bound (`eq:alphaQ`).**  For `q ≥ 1` and `p ≥ 4q²`, the number of
non-edges an independent-set-graph must avoid, `C(p,2) − t_q(p)`, is at least
`p²/(4q)`.  This is the quantitative core of `α(Q) < ηℓ`: a would-be independent
set of `p = ηℓ` clusters has more than `ε ℓ²` "good" (regular) pairs, since
`p²/(4q) = η²ℓ²/(4q) > ε ℓ²` for the chosen `ε`. -/
lemma turan_gap_lower (q p : ℕ) (hq : 1 ≤ q) (hp : 4 * q ^ 2 ≤ p) :
    (p.choose 2 : ℝ) - (turanEdges q p : ℝ) ≥ (p : ℝ) ^ 2 / (4 * q) := by
  have hqr : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hpr : (4:ℝ)*(q:ℝ)^2 ≤ (p:ℝ) := by exact_mod_cast hp
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hchoose : (p.choose 2 : ℝ) = (p:ℝ)*((p:ℝ)-1)/2 := by rw [Nat.cast_choose_two]
  have ht := turanEdges_le q p hq
  have ht' : 2*(q:ℝ)*(turanEdges q p) ≤ ((q:ℝ)-1)*(p:ℝ)^2 + 2*(q:ℝ)*(q:ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_left ht (by linarith : (0:ℝ) ≤ 2*(q:ℝ))
    calc 2*(q:ℝ)*(turanEdges q p) ≤ 2*(q:ℝ)*(((q:ℝ)-1)/(2*(q:ℝ))*(p:ℝ)^2+(q:ℝ)^2) := hmul
      _ = ((q:ℝ)-1)*(p:ℝ)^2 + 2*(q:ℝ)*(q:ℝ)^2 := by field_simp
  rw [hchoose, ge_iff_le, div_le_iff₀ (by positivity : (0:ℝ) < 4*(q:ℝ))]
  have hpp : (0:ℝ) ≤ (p:ℝ) := by positivity
  nlinarith [ht', hpr, hqr, mul_nonneg hpp (by linarith : (0:ℝ) ≤ (p:ℝ) - 4*(q:ℝ)^2), mul_pos hqpos hqpos]

end Erdos550

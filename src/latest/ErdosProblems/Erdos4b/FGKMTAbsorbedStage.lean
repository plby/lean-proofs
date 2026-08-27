/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsorptionError

/-! # A genuine reweighted stage with all numerical error hypotheses discharged -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]
  [DecidableEq I] [DecidableEq α]

theorem transitionContainmentMass_absorbed (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {P : α → ℝ} {κ δ D S z : ℝ}
    (hscale : F.StageAbsorptionBounds e κ D S) (hκ1 : κ ≤ 1)
    (hz : 0 < z) (hsmall : S ^ 3 * z ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ z ^ 60)
    (hI : 0 < Fintype.card I)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (heV : e ⊆ F.vertices)
    (hcodeg : ∀ v ∈ e, ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hdegree : ∀ v ∈ e, F.degree v ≤ D * P v)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ z ^ 30 * survivalProduct P A)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ δ / Real.sqrt (Fintype.card I)) :
    |F.transitionContainmentMass P ρ W (z ^ 10) e - survivalProduct (F.nextSurvival P) e| ≤
      z ^ 3 * survivalProduct (F.nextSurvival P) e := by
  have hκ0 := hscale.kappa_pos
  have hhalf := absorption_half_bounds hscale.scale_ge hz.le hsmall
  have hstage := F.transitionContainmentMass_scalar_error hκ0 hκ1 hP0 hP1 ρ W hρ hρsum
    e heV hδ0 hcodeg (pow_nonneg hz.le _) hhalf.1 (pow_pos hz _) hhalf.2
    (pow_pos hz 5) (pow_pos hz 5) (by positivity) hscale.degree_nonneg hdegree hcor hcap
    (F.testSetHitBound_absorbed e hscale hz.le hsmall hδ0 hδ hI)
    (F.testSetProduct_small e hscale hz.le hsmall hδ0 hδ hI)
  have hprod : 0 ≤ survivalProduct (F.nextSurvival P) e :=
    (survivalProduct_pos (fun v hv => F.nextSurvival_pos
      (hκ0.trans_le (hP0 v (heV hv))))).le
  exact hstage.trans (mul_le_mul_of_nonneg_right
    (F.stageRelativeError_absorbed e hscale hz hsmall hδ0 hδ hI) hprod)

end

end Erdos4b.FGKMT.FiniteEdgeFamily

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsorbedStage
import ErdosProblems.Erdos4b.FGKMTCoveringScale
import ErdosProblems.Erdos4b.FGKMTCoveringTolerance

/-! # One-stage covering estimate under the source smallness condition -/

namespace Erdos4b.FGKMT

noncomputable section

def coveringThreshold (δ : ℝ) (j : ℕ) : ℝ := coveringRoot (coveringTolerance δ j) ^ 10

theorem coveringThreshold_pos {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    0 < coveringThreshold δ j := pow_pos (coveringRoot_pos (coveringTolerance_pos hδ j)) _

theorem coveringThreshold_le_half {δ S : ℝ} (hδ : 0 < δ) (hS : 256 ≤ S)
    {j : ℕ} (hj : 1 ≤ j) (hsmall : δ ≤ (1 / S) ^ (10 ^ (j + 2))) :
    coveringThreshold δ j ≤ 1 / 2 := by
  have hz := covering_stage_root_conditions hδ hS hj hsmall
  exact (absorption_half_bounds hS hz.1.le hz.2.2.2.1).2

namespace FiniteEdgeFamily

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]
  [DecidableEq I] [DecidableEq α]

theorem transitionContainmentMass_covering_error (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {P : α → ℝ} {A j : ℕ} {κ δ D : ℝ}
    (hA : 1 ≤ A) (hD : 1 ≤ D) (hj : 1 ≤ j) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hsmall : δ ≤ (1 / coveringScale A D κ) ^ (10 ^ (j + 2)))
    (hsize : e.card + 2 * F.rank ≤ A) (hI : 0 < Fintype.card I)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (heV : e ⊆ F.vertices)
    (hcodeg : ∀ v ∈ e, ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hdegree : ∀ v ∈ e, F.degree v ≤ D * P v)
    (hcor : ∀ B ⊆ F.vertices, B.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W B - survivalProduct P B| ≤
        coveringTolerance δ j * survivalProduct P B)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ δ / Real.sqrt (Fintype.card I)) :
    |F.transitionContainmentMass P ρ W (coveringThreshold δ j) e -
      survivalProduct (F.nextSurvival P) e| ≤
        coveringTolerance δ (j + 1) * survivalProduct (F.nextSurvival P) e := by
  let z := coveringRoot (coveringTolerance δ j)
  have hscale := F.stageAbsorptionBounds_coveringScale e hA hD hκ0 hκ1 hsize
  have hz := covering_stage_root_conditions hδ hscale.scale_ge hj hsmall
  have hcor' (B : Finset α) (hBV : B ⊆ F.vertices) (hB : B.card ≤ e.card + 2 * F.rank) :
      |containmentMass ρ W B - survivalProduct P B| ≤ z ^ 30 * survivalProduct P B := by
    rw [show z ^ 30 = coveringTolerance δ j from hz.2.1]
    exact hcor B hBV hB
  have hstage := F.transitionContainmentMass_absorbed e hscale hκ1 hz.1 hz.2.2.2.1
    hδ.le hz.2.2.2.2 hI hP0 hP1 ρ W hρ hρsum heV hcodeg hdegree hcor' hcap
  change |F.transitionContainmentMass P ρ W (z ^ 10) e - survivalProduct (F.nextSurvival P) e| ≤
    coveringTolerance δ (j + 1) * survivalProduct (F.nextSurvival P) e
  rw [← hz.2.2.1]
  exact hstage

end FiniteEdgeFamily

end

end Erdos4b.FGKMT

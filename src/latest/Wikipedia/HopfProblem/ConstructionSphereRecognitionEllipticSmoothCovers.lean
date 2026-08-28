import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothFormula
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothCovering
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticHolomorphic

/-!
# The actual two complex covers of the elliptic product comparison

Both maps use the original period-torus and finite-quotient atlases.
Their real local diffeomorphisms are obtained only by restricting scalars
in these same charts.  The full product is not used to define an atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

open Elliptic SpecialPeriods

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel
local notation "IR" => modelWithCornersSelf ℝ FamilyModel

/-- The actual fixed-period affine surface projection has holomorphic inverse branches. -/
theorem surfaceProject_isLocalDiffeomorph (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    IsLocalDiffeomorph I₂ I₂ ω (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact CoveringQuotient.project_isLocalDiffeomorph
    (FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) p.val.Torus)
    (affineAction_holomorphic j p v hv.1)

variable {j : Kind} (D : Equivariant.Data j)

local instance vectorProductChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance surfaceProductChartedSpace : ChartedSpace FamilyModel
    (Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j)) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂)
    (Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j)))

theorem fillingCover_surjective : Function.Surjective (fillingCover D) :=
  (D.quotient_surjective j.twist (mainTwist_admissible j)).comp
    D.periods.quotientMap_surjective

theorem centralCover_surjective : Function.Surjective (centralCover D) := by
  rintro ⟨s, y⟩
  obtain ⟨x, rfl⟩ := surfaceProjection_surjective j D.centralPeriod j.twist
    (mainTwist_admissible j) y
  obtain ⟨z, rfl⟩ := D.centralPeriod.val.lattice.mkQ_surjective x
  exact ⟨(s, z), rfl⟩

/-- The original varying-period vector covering followed by the finite covering. -/
theorem fillingCover_isLocalDiffeomorph :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    IsLocalDiffeomorph IF IF ω (fillingCover D) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace j.twist (mainTwist_admissible j)
  intro p
  exact (D.periods.quotientMap_isLocalDiffeomorph p).comp
    (K := IF) (P := D.Space j.twist (mainTwist_admissible j))
    (Threefold.VerticalAction.Elliptic.quotient_isLocalDiffeomorph D j.twist
      (mainTwist_admissible j) (D.periods.quotientMap p))

/-- The central surface vector cover, with the original disc factor left unchanged. -/
theorem centralCover_isLocalDiffeomorph : IsLocalDiffeomorph IF IF ω (centralCover D) := by
  have hl := discreteProject_isLocalDiffeomorph D.centralPeriod.val.lattice ω
  have hs := surfaceProject_isLocalDiffeomorph j D.centralPeriod j.twist
    (mainTwist_admissible j)
  have hc : IsLocalDiffeomorph I₂ I₂ ω
      (fun z => surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
        (D.centralPeriod.val.lattice.mkQ z)) :=
    fun z => (hl z).comp (K := I₂)
      (P := Surface j D.centralPeriod j.twist (mainTwist_admissible j))
      (hs (D.centralPeriod.val.lattice.mkQ z))
  rw [modelWithCornersSelf_prod]
  exact isLocalDiffeomorph_prodLeft 𝓘(ℂ, ℂ) (B := Disc) hc

/-- Restriction of scalars in the unchanged varying-period and filling charts. -/
theorem fillingCover_real_isLocalDiffeomorph :
    letI := D.chartedSpace j.twist (mainTwist_admissible j)
    IsLocalDiffeomorph IR IR ω (fillingCover D) := by
  let := D.chartedSpace j.twist (mainTwist_admissible j)
  exact CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex
    (fillingCover_isLocalDiffeomorph D)

/-- Restriction of scalars in the unchanged disc and central-surface charts. -/
theorem centralCover_real_isLocalDiffeomorph :
    IsLocalDiffeomorph IR IR ω (centralCover D) :=
  CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex
    (centralCover_isLocalDiffeomorph D)

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

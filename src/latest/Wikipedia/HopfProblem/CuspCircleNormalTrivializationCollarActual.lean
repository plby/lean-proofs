import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarProduct

/-!
# The actual real-analytic annular collar in the original threefold

The literal radial annulus is inserted into the already verified native
standard normal chart. Its image is an actual open subset of the unchanged
threefold. The zero-parameter slice is exactly the preexisting boundary
parametrization of the true ambient frontier.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

open SpecialPeriods SpecialPeriods.Threefold

local notation "IS" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, Space)
local notation "IB" => ModelWithCorners.prod (𝓡 2) (𝓡 3)
local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

/-- The annular standard-product map is a genuine local diffeomorphism in the native atlases. -/
theorem standardProductMap_isLocalDiffeomorph :
    IsLocalDiffeomorph domainModel IS ω standardProductMap := by
  intro p
  exact (standardAnnulusDiffeomorph.isLocalDiffeomorph p).comp
    (K := IS) (P := StandardOpenNormalProduct)
    (OpenRestriction.isLocalDiffeomorph_subtypeVal IS (n := ω)
      standardAnnulus (standardAnnulusDiffeomorph p))

/-- The unchanged standard normal chart evaluated at the literal radial collar point. -/
def actualMap (p : Domain) : Threefold.Space :=
  standardNeighborhoodDiffeomorph (standardProductMap p)

/-- Local real-analytic invertibility is proved in the original global threefold atlas. -/
theorem actualMap_isLocalDiffeomorph : IsLocalDiffeomorph domainModel IX ω actualMap := by
  intro p
  have h := (standardProductMap_isLocalDiffeomorph p).comp
    (K := IX) (P := fixedCurveNeighborhood)
    (standardNeighborhoodDiffeomorph.isLocalDiffeomorph (standardProductMap p))
  exact h.comp (K := IX) (P := Threefold.Space)
    (OpenRestriction.isLocalDiffeomorph_subtypeVal IX (n := ω)
      fixedCurveNeighborhood (standardNeighborhoodDiffeomorph (standardProductMap p)))

theorem actualMap_contMDiff : ContMDiff domainModel IX ω actualMap :=
  actualMap_isLocalDiffeomorph.contMDiff

theorem actualMap_injective : Function.Injective actualMap := by
  intro p q hpq
  apply standardAnnulusDiffeomorph.injective
  apply Subtype.ext
  apply standardNeighborhoodDiffeomorph.injective
  apply Subtype.ext
  exact hpq

/-- The genuine open annular collar image in the original threefold. -/
def actualCollarNeighborhood : TopologicalSpace.Opens Threefold.Space :=
  actualMap_isLocalDiffeomorph.image

@[simp] theorem actualCollarNeighborhood_coe :
    (actualCollarNeighborhood : Set Threefold.Space) = range actualMap := rfl

/-- The actual collar map with codomain restricted to its proved open image. -/
def actualIntoCollar (p : Domain) : actualCollarNeighborhood :=
  ⟨actualMap p, mem_range_self p⟩

theorem actualIntoCollar_isLocalDiffeomorph :
    IsLocalDiffeomorph domainModel IX ω actualIntoCollar :=
  OpenRestriction.isLocalDiffeomorph_codRestrictOpens domainModel IX
    actualMap_isLocalDiffeomorph actualCollarNeighborhood (fun p => mem_range_self p)

theorem actualIntoCollar_bijective : Function.Bijective actualIntoCollar := by
  constructor
  · intro p q h
    exact actualMap_injective
      (congrArg (fun x : actualCollarNeighborhood => (x : Threefold.Space)) h)
  · rintro ⟨x, p, rfl⟩
    exact ⟨p, rfl⟩

/-- The genuine real-analytic standard-boundary collar in the original global smooth structure. -/
def actualCollarDiffeomorph :
    Diffeomorph domainModel IX Domain actualCollarNeighborhood ω :=
  actualIntoCollar_isLocalDiffeomorph.diffeomorphOfBijective actualIntoCollar_bijective

@[simp] theorem actualCollarDiffeomorph_coe (p : Domain) :
    (actualCollarDiffeomorph p : Threefold.Space) = actualMap p := rfl

theorem actualCollarNeighborhood_subset_normalNeighborhood :
    (actualCollarNeighborhood : Set Threefold.Space) ⊆ fixedCurveNeighborhood := by
  rintro x ⟨p, rfl⟩
  exact (standardNeighborhoodDiffeomorph (standardProductMap p)).property

/-- The center of the collar is the exact original standard boundary map. -/
theorem actualMap_zeroParameter (p : StandardNormalBoundary) :
    actualMap (p, zeroParameter) = standardBoundaryMap p := by
  unfold actualMap
  rw [standardProductMap_zeroParameter]
  exact (standardClosedDiskMap_eq_open_chart (standardBoundaryIntoClosedDisk p)).symm

/-- The zero collar slice parametrizes the actual topological frontier, not an auxiliary level. -/
theorem actualMap_zeroParameter_range :
    range (fun p : StandardNormalBoundary => actualMap (p, zeroParameter)) =
      frontier closedDiskNeighborhood := by
  have h : (fun p : StandardNormalBoundary => actualMap (p, zeroParameter)) =
      standardBoundaryMap := funext actualMap_zeroParameter
  rw [h, standardBoundaryMap_range]

/-- Every point of the genuine frontier is covered by this native analytic collar. -/
theorem frontier_subset_actualCollarNeighborhood :
    frontier closedDiskNeighborhood ⊆ actualCollarNeighborhood := by
  rw [← standardBoundaryMap_range]
  rintro x ⟨p, rfl⟩
  exact ⟨(p, zeroParameter), actualMap_zeroParameter p⟩

/-- The exact boundary parametrization is real analytic in the native standard sphere atlases. -/
theorem standardBoundaryMap_contMDiff : ContMDiff IB IX ω standardBoundaryMap := by
  have h : (fun p : StandardNormalBoundary => actualMap (p, zeroParameter)) =
      standardBoundaryMap := funext actualMap_zeroParameter
  rw [← h]
  exact actualMap_contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

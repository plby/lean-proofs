import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardBoundary
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardNeighborhood

/-!
# The standard sphere-product collar inside the original unit-ball domain

The domain is the literal standard boundary `S² × S³` times an open
interval. Radial coordinates and native open-subtype maps identify it
real analytically with the actual annular open subset of `S² × B⁴`.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

/-- The original standard sphere-product boundary times the collar interval. -/
abbrev Domain := StandardNormalBoundary × interval

/-- The native product model of the boundary and real interval. -/
abbrev domainModel :=
  ModelWithCorners.prod (ModelWithCorners.prod (𝓡 2) (𝓡 3)) 𝓘(ℝ, ℝ)

local notation "I₄" => 𝓘(ℝ, Space)
local notation "IS" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, Space)

/-- Each point of the radial annulus lies in the literal open unit four-ball. -/
theorem annulus_mem_unitBall (x : annulus) :
    (x : Space) ∈ Radial.ballOpen (E := Space) 1 := by
  change (x : Space) ∈ ball (0 : Space) 1
  rw [mem_ball, dist_zero_right]
  exact (annulus_norm_bounds x).2.trans (by norm_num)

/-- The same annulus, as a genuine open subset of the original unit ball. -/
def annulusInUnitBall : TopologicalSpace.Opens (Radial.ballOpen (E := Space) 1) :=
  ⟨{x | (x : Space) ∈ annulus}, annulus.isOpen.preimage continuous_subtype_val⟩

/-- Native open-subtype reassociation; the ambient Euclidean point is unchanged. -/
def annulusUnitBallDiffeomorph :
    Diffeomorph I₄ I₄ annulus annulusInUnitBall ω where
  toEquiv := {
    toFun := fun x => ⟨⟨x.val, annulus_mem_unitBall x⟩, x.property⟩
    invFun := fun x => ⟨x.val.val, x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  contMDiff_toFun := by
    intro x
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact contMDiff_subtype_val x
  contMDiff_invFun := by
    intro x
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (contMDiff_subtype_val.comp contMDiff_subtype_val) x

@[simp] theorem annulusUnitBallDiffeomorph_coe (x : annulus) :
    ((annulusUnitBallDiffeomorph x).val : Space) = x := rfl

@[simp] theorem annulusUnitBallDiffeomorph_symm_coe (x : annulusInUnitBall) :
    ((annulusUnitBallDiffeomorph.symm x) : Space) = x.val := rfl

/-- The actual annular open subset of the literal standard normal product. -/
def standardAnnulus : TopologicalSpace.Opens StandardOpenNormalProduct :=
  ProductOpen.domain (M := RealSphere.UnitTwoSphere) annulusInUnitBall

@[simp] theorem mem_standardAnnulus (p : StandardOpenNormalProduct) :
    p ∈ standardAnnulus ↔
      (1 / 4 : ℝ) < ‖(p.2 : Space)‖ ∧ ‖(p.2 : Space)‖ < (3 / 4 : ℝ) := Iff.rfl

/-- The native boundary-product reassociation followed by genuine radial coordinates. -/
def productRadialDiffeomorph :
    Diffeomorph domainModel IS Domain (RealSphere.UnitTwoSphere × annulus) ω where
  toEquiv := (Equiv.prodAssoc RealSphere.UnitTwoSphere Sphere interval).trans
    ((Equiv.refl RealSphere.UnitTwoSphere).prodCongr radialDiffeomorph.toEquiv)
  contMDiff_toFun := by
    have h : ContMDiff domainModel
        (ModelWithCorners.prod (𝓡 3) 𝓘(ℝ, ℝ)) ω
        (fun p : Domain => (p.1.2, p.2)) :=
      (contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd
    exact (contMDiff_fst.comp contMDiff_fst).prodMk (radialDiffeomorph.contMDiff.comp h)
  contMDiff_invFun := by
    have h : ContMDiff IS (ModelWithCorners.prod (𝓡 3) 𝓘(ℝ, ℝ)) ω
        (fun p : RealSphere.UnitTwoSphere × annulus => radialDiffeomorph.symm p.2) :=
      radialDiffeomorph.symm.contMDiff.comp contMDiff_snd
    exact (contMDiff_fst.prodMk (contMDiff_fst.comp h)).prodMk (contMDiff_snd.comp h)

@[simp] theorem productRadialDiffeomorph_apply (p : Domain) :
    productRadialDiffeomorph p = (p.1.1, radialDiffeomorph (p.1.2, p.2)) := rfl

/-- The Euclidean annulus is placed in the actual standard-product open submanifold. -/
def productAnnulusDiffeomorph :
    Diffeomorph IS IS (RealSphere.UnitTwoSphere × annulus) standardAnnulus ω :=
  (productDiffeomorph (Diffeomorph.refl (𝓡 2) RealSphere.UnitTwoSphere ω)
    annulusUnitBallDiffeomorph).trans
      (ProductOpen.diffeomorph (𝓡 2) I₄ ω annulusInUnitBall).symm

/-- A genuine native analytic standard collar onto the actual annular product domain. -/
def standardAnnulusDiffeomorph :
    Diffeomorph domainModel IS Domain standardAnnulus ω :=
  productRadialDiffeomorph.trans productAnnulusDiffeomorph

/-- The exact standard-product point of the radial collar. -/
def standardProductMap (p : Domain) : StandardOpenNormalProduct :=
  standardAnnulusDiffeomorph p

@[simp] theorem standardProductMap_fst (p : Domain) :
    (standardProductMap p).1 = p.1.1 := rfl

@[simp] theorem standardProductMap_snd_coe (p : Domain) :
    ((standardProductMap p).2 : Space) = radialScale p.2 • (p.1.2 : Space) := rfl

@[simp] theorem norm_standardProductMap_snd (p : Domain) :
    ‖((standardProductMap p).2 : Space)‖ = radialScale p.2 :=
  norm_forward (p.1.2, p.2)

/-- The zero collar slice is literally the same half-scaled standard boundary vector. -/
theorem standardProductMap_zeroParameter (p : StandardNormalBoundary) :
    standardProductMap (p, zeroParameter) =
      standardClosedIntoOpen (standardBoundaryIntoClosedDisk p) := by
  apply Prod.ext
  · rw [standardProductMap_fst]
    rfl
  · apply Subtype.ext
    rw [standardProductMap_snd_coe]
    change radialScale (zeroParameter : ℝ) • (p.2 : Space) =
      (1 / 2 : ℝ) • (p.2 : Space)
    rw [zeroParameter_coe, radialScale_zero]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

import Wikipedia.HopfProblem.EllipticHigherHomologyRetraction
import Wikipedia.HopfProblem.EllipticEquivariantCentralSpecial

/-!
# Every-degree homology maps for the actual special elliptic fillings

The constructed special period families instantiate the actual central
inclusion, finite torus covering, and radial retraction.  Their induced
integral singular homology maps commute in every degree.  No period
family or homotopy-equivalence hypothesis is supplied to these results.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic SingularMayerVietoris PeriodTorusHigherHomology

/-- The literal central torus of the constructed special local periods. -/
abbrev SpecialCentralPeriodTorus (j : Kind) := (specialLocalData j).centralPeriod.val.Torus

/-- The original finite torus covering of the special central surface. -/
def specialCentralPeriodCover (j : Kind) :
    C(SpecialCentralPeriodTorus j, SpecialCentralSurface j) :=
  HigherHomology.periodCover j (specialLocalData j).centralPeriod j.twist
    (mainTwist_admissible j)

theorem specialCentralPeriodCover_isCoveringMap (j : Kind) :
    IsCoveringMap (specialCentralPeriodCover j) :=
  HigherHomology.periodCover_isCoveringMap j (specialLocalData j).centralPeriod
    j.twist (mainTwist_admissible j)

/-- The actual covering has the source's exact finite degree. -/
theorem specialCentralPeriodCover_fibre_card (j : Kind) (s : SpecialCentralSurface j) :
    Nat.card (specialCentralPeriodCover j ⁻¹' {s}) = j.order :=
  surfaceProjection_fibre_card j (specialLocalData j).centralPeriod
    j.twist (mainTwist_admissible j) s

/-- The actual central inclusion induces an integral singular-homology
isomorphism in every degree. -/
def specialCentralSurfaceHomologyEquiv (j : Kind) (n : ℕ) :
    SingularHomology (SpecialCentralSurface j) n ≃ₗ[ℤ]
      SingularHomology (SpecialFullFilling j) n :=
  HigherHomology.centralSurfaceHomologyEquiv (specialLocalData j)
    j.twist (mainTwist_admissible j) n

@[simp] theorem specialCentralSurfaceHomologyEquiv_toLinearMap (j : Kind) (n : ℕ) :
    (specialCentralSurfaceHomologyEquiv j n).toLinearMap =
      singularHomologyMap (specialCentralSurfaceIntoFilling j) n := rfl

@[simp] theorem specialCentralSurfaceHomologyEquiv_symm_apply (j : Kind) (n : ℕ)
    (a : SingularHomology (SpecialFullFilling j) n) :
    (specialCentralSurfaceHomologyEquiv j n).symm a =
      singularHomologyMap (specialCentralSurfaceRetraction j) n a := rfl

theorem specialCentralInclusion_homology_bijective (j : Kind) (n : ℕ) :
    Function.Bijective (singularHomologyMap (specialCentralSurfaceIntoFilling j) n) :=
  (specialCentralSurfaceHomologyEquiv j n).bijective

/-- The native special central surface and literal reduced fibre have
the same actual singular homology through their specified homeomorphism. -/
def specialCentralFibreHomologyEquiv (j : Kind) (n : ℕ) :
    SingularHomology (SpecialCentralSurface j) n ≃ₗ[ℤ]
      SingularHomology (SpecialCentralFibre j) n :=
  homeomorphHomologyEquiv ((specialLocalData j).centralFibreHomeomorph
    j.twist (mainTwist_admissible j)) n

/-- The literal map from the original special period torus into its full filling. -/
def specialPeriodTorusIntoFilling (j : Kind) :
    C(SpecialCentralPeriodTorus j, SpecialFullFilling j) :=
  HigherHomology.periodTorusIntoFilling (specialLocalData j)
    j.twist (mainTwist_admissible j)

/-- The finite covering and central inclusion commute on the actual
singular homology maps, in particular in degrees two, three, and four. -/
theorem specialCentralSurfaceHomologyEquiv_periodCover (j : Kind) (n : ℕ)
    (a : SingularHomology (SpecialCentralPeriodTorus j) n) :
    specialCentralSurfaceHomologyEquiv j n
      (singularHomologyMap (specialCentralPeriodCover j) n a) =
        singularHomologyMap (specialPeriodTorusIntoFilling j) n a :=
  HigherHomology.centralSurfaceHomologyEquiv_periodCover (specialLocalData j)
    j.twist (mainTwist_admissible j) n a

theorem specialPeriodTorusIntoFilling_homology_ker (j : Kind) (n : ℕ) :
    LinearMap.ker (singularHomologyMap (specialPeriodTorusIntoFilling j) n) =
      LinearMap.ker (singularHomologyMap (specialCentralPeriodCover j) n) :=
  HigherHomology.periodTorusIntoFilling_homology_ker (specialLocalData j)
    j.twist (mainTwist_admissible j) n

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

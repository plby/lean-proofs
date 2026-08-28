import Wikipedia.HopfProblem.SpecialPeriodsEllipticFilling
import Wikipedia.HopfProblem.EllipticEquivariantCentralManifold
import Wikipedia.HopfProblem.EllipticEquivariantCentralCanonical
import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalContinuous
import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologyGroups
import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologyHomology

/-!
# The actual special elliptic central surfaces

The constructed special local periods instantiate the genuine central
surface and fibre constructions. The fibre atlas consists of ambient
immersion slices. The actual inclusion induces the deformation retraction
and the fundamental- and singular-homology equivalences. Its geometric
normal bundle and the surface's native canonical bundle have the exact
orders prescribed by the two actual elliptic stabilizers.

No period family, local comparison, atlas identification, or bundle
existence is an input to these specializations.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

/-- The native finite affine quotient of the actual special central
period torus, with the source's original twist. -/
abbrev SpecialCentralSurface (j : Kind) :=
  Surface j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)

/-- The literal central fibre of the actual special full filling. -/
abbrev SpecialCentralFibre (j : Kind) :=
  specialFullFillingProjection j ⁻¹' {Elliptic.discZero}

def specialCentralInclusion (j : Kind) : SpecialCentralSurface j → SpecialFullFilling j :=
  (specialLocalData j).centralFibreInclusion j.twist (mainTwist_admissible j)

theorem specialCentralInclusion_isClosedEmbedding (j : Kind) :
    IsClosedEmbedding (specialCentralInclusion j) :=
  (specialLocalData j).centralFibreInclusion_isClosedEmbedding j.twist (mainTwist_admissible j)

theorem specialCentralInclusion_isImmersionOfComplement (j : Kind) :
    letI := specialFullFillingChartedSpace j
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (specialCentralInclusion j) :=
  (specialLocalData j).centralFibreInclusion_isImmersionOfComplement
    j.twist (mainTwist_admissible j)

theorem specialCentralInclusion_range (j : Kind) :
    range (specialCentralInclusion j) = specialFullFillingProjection j ⁻¹' {Elliptic.discZero} :=
  (specialLocalData j).range_centralFibreInclusion j.twist (mainTwist_admissible j)

@[instance_reducible] def specialCentralFibreChartedSpace (j : Kind) :
    ChartedSpace ComplexPlane₂ (SpecialCentralFibre j) :=
  (specialLocalData j).centralFibreChartedSpace j.twist (mainTwist_admissible j)

theorem specialCentralFibre_isManifold (j : Kind) :
    letI := specialCentralFibreChartedSpace j
    IsManifold I₂ ω (SpecialCentralFibre j) :=
  (specialLocalData j).centralFibre_isManifold j.twist (mainTwist_admissible j)

/-- The actual surface is biholomorphic to the actual reduced central
fibre, with its ambient-induced atlas. -/
def specialCentralFibreBiholomorph (j : Kind) :
    letI := specialCentralFibreChartedSpace j
    Diffeomorph I₂ I₂ (SpecialCentralSurface j) (SpecialCentralFibre j) ω :=
  (specialLocalData j).centralFibreBiholomorph j.twist (mainTwist_admissible j)

@[simp] theorem specialCentralFibreBiholomorph_coe (j : Kind) (x : SpecialCentralSurface j) :
    letI := specialCentralFibreChartedSpace j
    (specialCentralFibreBiholomorph j x : SpecialFullFilling j) = specialCentralInclusion j x :=
  rfl

/-- Both directions of the special fibre atlas are actual restrictions
of maximal-atlas charts of the supplied special filling. -/
theorem specialCentralFibre_charts_are_ambient_slices (j : Kind) (x : SpecialCentralFibre j) :
    letI := specialFullFillingChartedSpace j
    letI := specialCentralFibreChartedSpace j
    ∃ c : OpenPartialHomeomorph (SpecialFullFilling j) FamilyModel,
      ∃ L : (ComplexPlane₂ × ℂ) ≃L[ℂ] FamilyModel,
        c ∈ IsManifold.maximalAtlas I₃ ω (SpecialFullFilling j) ∧
        (chartAt ComplexPlane₂ x).source = Subtype.val ⁻¹' c.source ∧
        (∀ y ∈ (chartAt ComplexPlane₂ x).source,
          c (y : SpecialFullFilling j) = L (chartAt ComplexPlane₂ x y, 0)) ∧
        (∀ z ∈ (chartAt ComplexPlane₂ x).target,
          ((chartAt ComplexPlane₂ x).symm z : SpecialFullFilling j) = c.symm (L (z, 0))) :=
  (specialLocalData j).centralFibre_charts_are_ambient_slices
    j.twist (mainTwist_admissible j) x

def specialCentralSurfaceIntoFilling (j : Kind) :
    ContinuousMap (SpecialCentralSurface j) (SpecialFullFilling j) :=
  (specialLocalData j).surfaceIntoFilling j.twist (mainTwist_admissible j)

@[simp] theorem specialCentralSurfaceIntoFilling_apply (j : Kind)
    (x : SpecialCentralSurface j) :
    specialCentralSurfaceIntoFilling j x = specialCentralInclusion j x := rfl

def specialCentralSurfaceRetraction (j : Kind) :
    ContinuousMap (SpecialFullFilling j) (SpecialCentralSurface j) :=
  (specialLocalData j).fillingSurfaceRetraction j.twist (mainTwist_admissible j)

/-- The actual central inclusion is a strong deformation retract. -/
def specialCentralSurfaceStrongDeformationRetraction (j : Kind) :
    (ContinuousMap.id (SpecialFullFilling j)).HomotopyRel
      ((specialCentralSurfaceIntoFilling j).comp (specialCentralSurfaceRetraction j))
      (range (specialCentralSurfaceIntoFilling j)) :=
  (specialLocalData j).fillingSurfaceStrongDeformationRetraction
    j.twist (mainTwist_admissible j)

def specialCentralSurfaceFundamentalGroupEquiv (j : Kind) (a : SpecialCentralSurface j) :
    FundamentalGroup (SpecialCentralSurface j) a ≃*
      FundamentalGroup (SpecialFullFilling j) (specialCentralInclusion j a) :=
  (specialLocalData j).fillingSurfaceFundamentalGroupEquiv j.twist (mainTwist_admissible j) a

@[simp] theorem specialCentralSurfaceFundamentalGroupEquiv_toMonoidHom
    (j : Kind) (a : SpecialCentralSurface j) :
    (specialCentralSurfaceFundamentalGroupEquiv j a).toMonoidHom =
      FundamentalGroup.map (specialCentralSurfaceIntoFilling j) a := rfl

def specialCentralSurfaceSingularH1Equiv (j : Kind) (a : SpecialCentralSurface j) :
    FirstHurewicz.SingularH1 (SpecialCentralSurface j) ≃ₗ[ℤ]
      FirstHurewicz.SingularH1 (SpecialFullFilling j) :=
  (specialLocalData j).centralSurfaceSingularH1Equiv j.twist (mainTwist_admissible j) a

/-- This is Mathlib's actual induced singular homology map of the
displayed central inclusion. -/
theorem specialCentralSurfaceSingularH1Equiv_toLinearMap (j : Kind)
    (a : SpecialCentralSurface j) :
    (specialCentralSurfaceSingularH1Equiv j a).toLinearMap =
      FirstHurewicz.inducedHomology (specialCentralSurfaceIntoFilling j) :=
  (specialLocalData j).centralSurfaceSingularH1Equiv_toLinearMap
    j.twist (mainTwist_admissible j) a

theorem specialFullFilling_singularH1_finrank (j : Kind) :
    Module.finrank ℤ (FirstHurewicz.SingularH1 (SpecialFullFilling j)) = 2 :=
  (specialLocalData j).fillingSingularH1_finrank j.twist (mainTwist_admissible j)

/-- The actual canonical bundle, through its native two-covector atlas. -/
abbrev specialCentralCanonicalBundle (j : Kind) :=
  Equivariant.Data.CentralCanonical.bundle (specialLocalData j) j.twist (mainTwist_admissible j)

/-- The actual geometric normal bundle, constructed from the differential
of the actual central inclusion. -/
abbrev specialCentralNormalBundle (j : Kind) :=
  Equivariant.Data.NormalBundle.core (specialLocalData j) j.twist (mainTwist_admissible j)

/-- The literal normal tangent quotient in the actual special filling atlas. -/
abbrev SpecialCentralNormalFibre (j : Kind) (x : SpecialCentralSurface j) :=
  letI := specialFullFillingChartedSpace j
  FamilyModel ⧸ (mfderiv I₂ I₃ (specialCentralInclusion j) x).range

/-- The analytic normal bundle's fibre is continuously and complex-linearly
identified with the actual normal tangent quotient, with its quotient topology. -/
def specialCentralNormalFibreIdentification (j : Kind) (x : SpecialCentralSurface j) :
    (specialCentralNormalBundle j).Fiber x ≃L[ℂ] SpecialCentralNormalFibre j x :=
  Equivariant.Data.NormalBundle.fibreIdentificationContinuous
    (specialLocalData j) j.twist (mainTwist_admissible j) x

theorem specialCentralCanonical_power_trivial_iff (j : Kind) (n : ℕ) :
    Nonempty ((Equivariant.Data.CentralCanonical.powerData (specialLocalData j)
      j.twist (mainTwist_admissible j) n).AnalyticTrivialization I₂) ↔ j.order ∣ n :=
  Equivariant.Data.CentralCanonical.power_analyticTrivialization_iff
    (specialLocalData j) j.twist (mainTwist_admissible j) n

theorem specialCentralNormal_power_trivial_iff (j : Kind) (n : ℕ) :
    Nonempty ((Equivariant.Data.NormalBundle.powerData (specialLocalData j)
      j.twist (mainTwist_admissible j) n).AnalyticTrivialization I₂) ↔ j.order ∣ n :=
  Equivariant.Data.NormalBundle.power_analyticTrivialization_iff
    (specialLocalData j) j.twist (mainTwist_admissible j) n

/-- Both actual geometric line bundles are nontrivial; their least
positive trivial tensor power is the indicated elliptic order. -/
theorem specialCentralBundles_nontrivial (j : Kind) :
    ¬ Nonempty ((Equivariant.Data.CentralCanonical.data (specialLocalData j)
      j.twist (mainTwist_admissible j)).AnalyticTrivialization I₂) ∧
    ¬ Nonempty ((Equivariant.Data.NormalBundle.data (specialLocalData j)
      j.twist (mainTwist_admissible j)).AnalyticTrivialization I₂) :=
  ⟨Equivariant.Data.CentralCanonical.not_analytically_trivial
      (specialLocalData j) j.twist (mainTwist_admissible j),
    Equivariant.Data.NormalBundle.not_analytically_trivial
      (specialLocalData j) j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

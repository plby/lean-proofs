import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingGlobal
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality

/-!
# Comparing a degree-one connecting class with literal resolution lifts

A morphism from a genuine short exact sheaf complex to the first short
exact sequence of an augmented resolution gives the actual naturality
square for the degree-one connecting map. Literal local lifts of a global
section through the second sequence identify the other side by the
already constructed Čech extension. The overlap convention is the later
lift minus the earlier lift, with no assumed equality of cohomology classes.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ExponentialChernComparison

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} {ι : Type} {U : ι → Opens X}
  (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact)
  (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
  (φ : S ⟶ R.first) (c : CechOneCocycle S.X₃ U)
  (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
  (σ : Section R.complex.X₃ ⊤) (t : ∀ i : ι, Section R.complex.X₂ (U i))
  (hp : ∀ i : ι, R.complex.g.hom.app (op (U i)) (t i) =
    res R.complex.X₃ le_top σ)
  (hdiff : ∀ i j : ι,
    res R.complex.X₂ inf_le_right (t j) - res R.complex.X₂ inf_le_left (t i) =
      R.second.f.hom.app (op (U i ⊓ U j))
        ((HolomorphicPicard.Cech.mapCocycle φ.τ₃ c).value i j))

include t hp hdiff in
/-- Literal local lifts through the second resolution sequence identify
the coefficient image of the actual degree-one connecting class with the
actual double connecting class of the prescribed global section. -/
theorem map_connecting_classOf_eq_globalConnectingTwo :
    CategoryTheory.Sheaf.H.map φ.τ₁ 2
        (connecting (unitSheaf X) hS 1 (classOf c hU)) =
      R.globalConnectingTwo σ := by
  have hc :=
    PeriodFamilyHolomorphicCohomology.CechConnecting.classOf_eq_connecting_globalSection
      R.second R.second_shortExact (HolomorphicPicard.Cech.mapCocycle φ.τ₃ c)
      hU σ t hp hdiff
  have hn := connecting_naturality (unitSheaf X) hS R.first_shortExact φ 1
    (classOf c hU)
  change connecting (unitSheaf X) R.first_shortExact 1
      (CategoryTheory.Sheaf.H.map φ.τ₃ 1 (classOf c hU)) =
    CategoryTheory.Sheaf.H.map φ.τ₁ 2
      (connecting (unitSheaf X) hS 1 (classOf c hU)) at hn
  rw [classOf_naturality] at hn
  exact hn.symm.trans
    (congrArg (connecting (unitSheaf X) R.first_shortExact 1) hc)

include t hp hdiff in
/-- Under the actual termwise acyclicity needed for the resolution
comparison, the same class maps to the ordinary cokernel class of the
literal global section. -/
theorem h2Iso_map_connecting_classOf
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    R.h2Iso.hom (CategoryTheory.Sheaf.H.map φ.τ₁ 2
        (connecting (unitSheaf X) hS 1 (classOf c hU))) =
      cokernel.π R.globalComplex.g σ := by
  rw [map_connecting_classOf_eq_globalConnectingTwo S hS R φ c hU σ t hp hdiff]
  exact ConcreteCategory.congr_hom R.h2Iso_connecting σ

end Wikipedia.HopfProblem.ExponentialChernComparison

import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingClass
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingDegreeZero
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionRepresentatives

/-!
# Čech lifts of literal global sections give the original connecting map

The actual degree-zero global-section comparison identifies the integer
map associated to a literal section. The original extension comparison
therefore agrees with the genuine connecting homomorphism
on that original global section, including for an augmented resolution.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} {ι : Type} {U : ι → Opens X}

/-- A literal global section lifted on the original cover gives its
actual Ext connecting class through the original degree-zero comparison. -/
theorem classOf_eq_connecting_globalSection
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact)
    (c : CechOneCocycle S.X₁ U) (hU : ∀ x : X, ∃ j : ι, x ∈ U j)
    (s : Section S.X₃ ⊤) (t : ∀ j : ι, Section S.X₂ (U j))
    (hp : ∀ j : ι, S.g.hom.app (op (U j)) (t j) = res S.X₃ le_top s)
    (hdiff : ∀ j k : ι, res S.X₂ inf_le_right (t k) - res S.X₂ inf_le_left (t j) =
      S.f.hom.app (op (U j ⊓ U k)) (c.value j k)) :
    classOf c hU = connecting (unitSheaf X) hS 0 ((h0GlobalIso S.X₃).inv s) := by
  have hc := classOf_eq_connecting S c hU (globalSectionMorphism S.X₃ s) t
    (fun j => (hp j).trans (globalSectionMorphism_degreeOne S.X₃ s (U j)).symm)
    hdiff hS
  exact hc.trans (congrArg
    (fun e : Ext.{0} (unitSheaf X) S.X₃ 0 => e.comp hS.extClass (zero_add 1))
    (h0GlobalIso_inv_eq_mk₀ S.X₃ s).symm)

/-- The same literal local lifts compute the original first connecting
map of the actual augmented resolution, on its actual kernel section. -/
theorem classOf_eq_globalConnectingOne
    (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
    (c : CechOneCocycle R.F U) (hU : ∀ x : X, ∃ j : ι, x ∈ U j)
    (k : (globalSectionsFunctor X).obj R.K)
    (t : ∀ j : ι, Section R.complex.X₁ (U j))
    (hp : ∀ j : ι, R.toK.hom.app (op (U j)) (t j) = res R.K le_top k)
    (hdiff : ∀ j l : ι,
      res R.complex.X₁ inf_le_right (t l) - res R.complex.X₁ inf_le_left (t j) =
        R.ι.hom.app (op (U j ⊓ U l)) (c.value j l)) :
    classOf c hU = R.globalConnectingOne k :=
  classOf_eq_connecting_globalSection R.first R.first_shortExact c hU k t hp hdiff

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenSupportHomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCohomology
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Original integral cohomology excision and extension from open subsets

The actual relative chain terms are free. Integral excision is therefore
a chain homotopy equivalence, and its original integral cochain dual is
a quasi-isomorphism. Its inverse on cohomology gives extension to the
actual image support. Support compatibility descends this extension to
the original compact-support directed limits.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCochainTransport

open SingularCohomologyFree

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- The actual dual of a quasi-isomorphism of projective chain complexes is a quasi-isomorphism. -/
theorem dualMap_quasiIso_of_projective [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (dualMap f) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  rw [← he]
  exact (dualHomotopyEquiv e).quasiIso_hom

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCochainTransport

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenSupport

open SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere SupportedRelativeHomology
open IntegralSupportedCohomology (Cohomology extend extendCochain)

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Restriction is precomposition by the original integral inclusion of pairs. -/
def restrictionMap (K : Set U) : IntegralSupportedCohomology.complex (imageSupport U K) ⟶
    IntegralSupportedCohomology.complex K := dualMap (inclusionChain U K)

theorem restrictionMap_extend {K L : Set U} (h : K ⊆ L) :
    extendCochain (Set.image_mono h) ≫ restrictionMap U L =
      restrictionMap U K ≫ extendCochain h := by
  exact (dualMap_comp (inclusionChain U L)
    (restrictChain (ModuleCat.of ℤ ℤ) (Set.image_mono h))).symm.trans
      ((congrArg dualMap (inclusionChain_restrict U h)).trans
        (dualMap_comp (restrictChain (ModuleCat.of ℤ ℤ) h) (inclusionChain U K)))

theorem restriction_extend {K L : Set U} (h : K ⊆ L) (p : ℕ)
    (a : Cohomology (imageSupport U K) p) :
    (HomologicalComplex.homologyMap (restrictionMap U L) p).hom (extend (Set.image_mono h) p a) =
      extend h p ((HomologicalComplex.homologyMap (restrictionMap U K) p).hom a) := by
  have he := congrArg (fun f => HomologicalComplex.homologyMap f p) (restrictionMap_extend U h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun f => f.hom a) he

variable [T2Space X]

/-- Excision for the original integral cochain pullback, using proved freeness of both complexes. -/
theorem restrictionMap_quasiIso (hU : IsOpen U) (K : Set U) (hK : IsCompact K) :
    QuasiIso (restrictionMap U K) := by
  let (n : ℕ) : Projective ((Complex (ModuleCat.of ℤ ℤ) K).X n) := by
    let : Module.Free ℤ ((Complex (ModuleCat.of ℤ ℤ) K).X n) :=
      RelativeSingularHomology.chains_free Kᶜ n
    infer_instance
  let (n : ℕ) : Projective ((Complex (ModuleCat.of ℤ ℤ) (imageSupport U K)).X n) := by
    let : Module.Free ℤ ((Complex (ModuleCat.of ℤ ℤ) (imageSupport U K)).X n) :=
      RelativeSingularHomology.chains_free (imageSupport U K)ᶜ n
    infer_instance
  let := inclusionChain_quasiIso U hU K hK
  exact IntegralCochainTransport.dualMap_quasiIso_of_projective (inclusionChain U K)

/-- The original cohomology restriction is an equivalence on this actual compact support. -/
def restrictionEquiv (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ) :
    Cohomology (imageSupport U K) p ≃ₗ[ℤ] Cohomology K p := by
  let := restrictionMap_quasiIso U hU K hK
  exact (isoOfQuasiIsoAt (restrictionMap U K) p).toLinearEquiv

theorem restrictionEquiv_toLinearMap (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ) :
    (restrictionEquiv U hU K hK p).toLinearMap =
      (HomologicalComplex.homologyMap (restrictionMap U K) p).hom := rfl

def extension (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ) :
    Cohomology K p →ₗ[ℤ] Cohomology (imageSupport U K) p :=
  (restrictionEquiv U hU K hK p).symm.toLinearMap

theorem restriction_extension (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ)
    (a : Cohomology K p) : restrictionEquiv U hU K hK p (extension U hU K hK p a) = a :=
  (restrictionEquiv U hU K hK p).apply_symm_apply a

theorem extension_restriction (hU : IsOpen U) (K : Set U) (hK : IsCompact K) (p : ℕ)
    (a : Cohomology (imageSupport U K) p) :
    extension U hU K hK p (restrictionEquiv U hU K hK p a) = a :=
  (restrictionEquiv U hU K hK p).symm_apply_apply a

/-- Inverse excision preserves the original support-extension maps. -/
theorem extension_extend (hU : IsOpen U) {K L : Set U} (h : K ⊆ L)
    (hK : IsCompact K) (hL : IsCompact L) (p : ℕ) (a : Cohomology K p) :
    extend (Set.image_mono h) p (extension U hU K hK p a) =
      extension U hU L hL p (extend h p a) := by
  apply (restrictionEquiv U hU L hL p).injective
  exact (restriction_extend U h p (extension U hU K hK p a)).trans
    ((congrArg (extend h p) (restriction_extension U hU K hK p a)).trans
      (restriction_extension U hU L hL p (extend h p a)).symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenSupport

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (U : Set X) (hU : IsOpen U) (p : ℕ)

def imageCompact (K : Compacts U) : Compacts X :=
  ⟨IntegralOpenSupport.imageSupport U (K : Set U), K.isCompact.image continuous_subtype_val⟩

def inclusionComponent (K : Compacts U) : Component U p K →ₗ[ℤ] Cohomology X p :=
  (of X p (imageCompact U K)).comp
    (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p)

theorem inclusionComponent_transition (K L : Compacts U) (h : K ≤ L) (a : Component U p K) :
    inclusionComponent U hU p L (transition U p K L h a) = inclusionComponent U hU p K a := by
  change of X p (imageCompact U L)
    (IntegralOpenSupport.extension U hU (L : Set U) L.isCompact p
      (IntegralSupportedCohomology.extend h p a)) = _
  rw [← IntegralOpenSupport.extension_extend U hU h K.isCompact L.isCompact p a]
  exact of_transition X p (K := imageCompact U K) (L := imageCompact U L)
    (show imageCompact U K ≤ imageCompact U L from Set.image_mono h)
    (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a)

/-- The map on actual compact-support cohomology induced by an open inclusion. -/
def inclusion : Cohomology U p →ₗ[ℤ] Cohomology X p :=
  lift U p (inclusionComponent U hU p) (inclusionComponent_transition U hU p)

theorem inclusion_of (K : Compacts U) (a : Component U p K) :
    inclusion U hU p (of U p K a) = of X p (imageCompact U K)
      (IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearHomologyExact
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionHomology

/-!
# Categorical homology of the actual Fourier Dolbeault complex

Exactness of the actual mean sequence supplies left homology data for
Mathlib's existing short complex.  Its actual homology object is thus
complex-linearly isomorphic to the two constant coefficients.  The formulas
retain the canonical cycle map, literal Haar means, and constant representatives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

open CuspNormalization.SheafCohomologyResolution

/-- The actual kernel and the proved exact mean quotient give genuine homology data. -/
def leftHomologyData (p : PeriodDomain) : (complex p).LeftHomologyData :=
  @leftHomologyDataOfExact (ModuleCat ℂ) _ _ (complex p)
    (ModuleCat.of ℂ (closedPairs p)) (ModuleCat.of ℂ (Fin 2 → ℂ))
    (ModuleCat.ofHom (closedInclusion p)) (ModuleCat.ofHom (differentialToClosed p))
    (ModuleCat.ofHom (closedMean p)) (closedKernelComplex p).zero
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      rfl)
    (closedMeanComplex p).zero (closedKernelComplex_exact p) (closedMeanComplex_exact p)
    (closedInclusion_mono p) (closedMean_epi p)

/-- Mathlib's actual homology object is the two-dimensional constant coefficient space. -/
def homologyIso (p : PeriodDomain) : (complex p).homology ≅ ModuleCat.of ℂ (Fin 2 → ℂ) :=
  (leftHomologyData p).homologyIso

/-- The actual homology class of a closed pair. -/
def homologyClass (p : PeriodDomain) :
    ModuleCat.of ℂ (closedPairs p) ⟶ (complex p).homology :=
  (leftHomologyData p).cyclesIso.inv ≫ (complex p).homologyπ

/-- On a closed representative the isomorphism is exactly its componentwise Haar mean. -/
theorem homologyIso_class (p : PeriodDomain) :
    homologyClass p ≫ (homologyIso p).hom = ModuleCat.ofHom (closedMean p) := by
  let h := leftHomologyData p
  have he : h.cyclesIso.inv ≫ (complex p).homologyπ ≫ h.homologyIso.hom = h.π := by
    rw [h.homologyπ_comp_homologyIso_hom, Iso.inv_hom_id_assoc]
  exact he

theorem homologyIso_class_apply (p : PeriodDomain) (a : closedPairs p) :
    (homologyIso p).hom (homologyClass p a) = pairMean a.val :=
  congrArg (fun f : ModuleCat.of ℂ (closedPairs p) ⟶ ModuleCat.of ℂ (Fin 2 → ℂ) => f a)
    (homologyIso_class p)

/-- Compatibility with the canonical cycle inclusion and homology projection, independently
of the explicit kernel parametrization used to construct the isomorphism. -/
theorem homologyIso_π (p : PeriodDomain) :
    (complex p).homologyπ ≫ (homologyIso p).hom =
      (complex p).iCycles ≫ ModuleCat.ofHom pairMean := by
  let h := leftHomologyData p
  let m : (complex p).X₂ ⟶ h.H := ModuleCat.ofHom pairMean
  have hm : h.π = h.i ≫ m := rfl
  have he : (complex p).homologyπ ≫ h.homologyIso.hom = (complex p).iCycles ≫ m := by
    rw [h.homologyπ_comp_homologyIso_hom, hm, ← Category.assoc, h.cyclesIso_hom_comp_i]
  exact he

/-- The inverse sends a pair of scalars to the class of its actual constant coefficient pair. -/
theorem homologyIso_inv (p : PeriodDomain) :
    (homologyIso p).inv = ModuleCat.ofHom (closedConstantPair p) ≫ homologyClass p := by
  apply (cancel_mono (homologyIso p).hom).mp
  rw [Iso.inv_hom_id, Category.assoc, homologyIso_class]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact (closedMean_constantPair p c).symm

theorem homologyIso_inv_apply (p : PeriodDomain) (c : Fin 2 → ℂ) :
    (homologyIso p).inv c = homologyClass p (closedConstantPair p c) :=
  congrArg (fun f : ModuleCat.of ℂ (Fin 2 → ℂ) ⟶ (complex p).homology => f c)
    (homologyIso_inv p)

/-- A homology class vanishes exactly when the literal Haar means of its representative do. -/
theorem homologyClass_eq_zero_iff (p : PeriodDomain) (a : closedPairs p) :
    homologyClass p a = 0 ↔ pairMean a.val = 0 := by
  rw [← (homologyIso p).toLinearEquiv.map_eq_zero_iff]
  change (homologyIso p).hom (homologyClass p a) = 0 ↔ pairMean a.val = 0
  rw [homologyIso_class_apply]

theorem homology_finrank (p : PeriodDomain) : Module.finrank ℂ (complex p).homology = 2 :=
  (homologyIso p).toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun ℂ)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

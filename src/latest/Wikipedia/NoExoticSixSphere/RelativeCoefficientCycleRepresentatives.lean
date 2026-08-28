import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Actual relative cycles with arbitrary coefficient modules

The degreewise quotient is surjective and its kernel is exactly the image
of the actual subspace inclusion. This describes cycle representatives
and boundary witnesses without replacing the native relative complex.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

/-- The original projection in a specified degree. -/
abbrev quotientMap (U : Set X) (n : ℕ) :
    CoefficientChains.Chains A X n →ₗ[ℤ] (complex A U).X n :=
  ((projection A U).f n).hom

theorem quotientMap_surjective (U : Set X) (n : ℕ) :
    Function.Surjective (quotientMap A U n) := by
  have := (sequence_shortExact A U).epi_g
  exact (ModuleCat.epi_iff_surjective _).mp
    (inferInstanceAs (Epi ((sequence A U).g.f n)))

/-- Vanishing relatively means being the image of an actual subspace chain. -/
theorem quotientMap_eq_zero_iff (U : Set X) (n : ℕ)
    (c : CoefficientChains.Chains A X n) :
    quotientMap A U n c = 0 ↔
      ∃ d : CoefficientChains.Chains A U n, ((inclusion A U).f n).hom d = c := by
  have h := (sequence_shortExact A U).exact.map
    (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)
  have he : LinearMap.range ((inclusion A U).f n).hom =
      LinearMap.ker (quotientMap A U n) := h.moduleCat_range_eq_ker
  change c ∈ LinearMap.ker (quotientMap A U n) ↔ _
  rw [← he]
  rfl

theorem boundary_quotientMap (U : Set X) (i j : ℕ)
    (c : CoefficientChains.Chains A X i) :
    ((complex A U).d i j).hom (quotientMap A U i c) =
      quotientMap A U j (((coefficientComplex A X).d i j).hom c) :=
  congrArg (fun f => ModuleCat.Hom.hom f c) ((projection A U).comm i j)

/-- Ambient chains represent every original relative homology class. -/
theorem exists_cycle_representative (U : Set X) (n : ℕ) (a : (complex A U).homology n) :
    ∃ c : CoefficientChains.Chains A X n,
      ∃ hc : ((complex A U).d n (n - 1)).hom (quotientMap A U n c) = 0,
        ModuleHomology.cycleClass (complex A U) n
          (ModuleHomology.mkCycle (complex A U) n (quotientMap A U n c) hc) = a := by
  obtain ⟨z, hz⟩ := ModuleHomology.cycleClass_surjective (complex A U) n a
  obtain ⟨c, hc⟩ := quotientMap_surjective A U n z.1
  have hc' : ((complex A U).d n (n - 1)).hom (quotientMap A U n c) = 0 := by
    rw [hc]
    exact ModuleHomology.cycle_condition (complex A U) n z
  refine ⟨c, hc', ?_⟩
  have he : ModuleHomology.mkCycle (complex A U) n (quotientMap A U n c) hc' = z :=
    Subtype.ext hc
  exact (congrArg (ModuleHomology.cycleClass (complex A U) n) he).trans hz

end NoExoticSixSphere.RelativeCoefficients

namespace NoExoticSixSphere.SupportedRelativeHomology

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

/-- Restriction is the identity on the ambient chain representative. -/
theorem restrictChain_quotientMap {K L : Set X} (h : K ⊆ L) (n : ℕ)
    (c : CoefficientChains.Chains A X n) :
    ((restrictChain A h).f n).hom (RelativeCoefficients.quotientMap A Lᶜ n c) =
      RelativeCoefficients.quotientMap A Kᶜ n c := by
  have he := RelativeCoefficients.projection_mapChain A (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hy hx => hy (h hx))
  rw [RelativeCoefficients.spaceMap_id, Category.id_comp] at he
  exact congrArg (fun f => (f.f n).hom c) he

end NoExoticSixSphere.SupportedRelativeHomology

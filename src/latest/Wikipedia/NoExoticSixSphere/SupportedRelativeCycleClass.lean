import Wikipedia.NoExoticSixSphere.RelativeCoefficientCycleRepresentatives

/-!
# Classes of original ambient relative cycles

These formulas retain the original ambient representative under support
restriction. Relative null-homology is expressed by an actual ambient
boundary whose difference from the original representative is supported
in the complement.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

/-- The original class represented by this specified ambient relative cycle. -/
def relativeClass (U : Set X) (n : ℕ) (c : CoefficientChains.Chains A X n)
    (hc : ((complex A U).d n (n - 1)).hom (quotientMap A U n c) = 0) :
    (complex A U).homology n :=
  ModuleHomology.cycleClass (complex A U) n
    (ModuleHomology.mkCycle (complex A U) n (quotientMap A U n c) hc)

/-- Actual relative null-homology has an ambient boundary witness. -/
theorem relativeClass_eq_zero_iff (U : Set X) (n : ℕ)
    (c : CoefficientChains.Chains A X n)
    (hc : ((complex A U).d n (n - 1)).hom (quotientMap A U n c) = 0) :
    relativeClass A U n c hc = 0 ↔
      ∃ b : CoefficientChains.Chains A X (n + 1),
        quotientMap A U n (c - ((coefficientComplex A X).d (n + 1) n).hom b) = 0 := by
  rw [relativeClass, ModuleHomology.cycleClass_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨d, hd⟩ := quotientMap_surjective A U (n + 1) b
    refine ⟨d, ?_⟩
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact hb.symm.trans ((congrArg ((complex A U).d (n + 1) n).hom hd).symm.trans
      (boundary_quotientMap A U (n + 1) n d))
  · rintro ⟨b, hb⟩
    refine ⟨quotientMap A U (n + 1) b, ?_⟩
    rw [map_sub, sub_eq_zero] at hb
    exact (boundary_quotientMap A U (n + 1) n b).trans hb.symm

end NoExoticSixSphere.RelativeCoefficients

namespace NoExoticSixSphere.SupportedRelativeHomology

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

/-- The same ambient representative remains a cycle when support is restricted. -/
theorem relativeCycle_restrict {K L : Set X} (h : K ⊆ L) (n : ℕ)
    (c : CoefficientChains.Chains A X n)
    (hc : ((Complex A L).d n (n - 1)).hom
      (RelativeCoefficients.quotientMap A Lᶜ n c) = 0) :
    ((Complex A K).d n (n - 1)).hom (RelativeCoefficients.quotientMap A Kᶜ n c) = 0 := by
  let z := ModuleHomology.mkCycle (Complex A L) n
    (RelativeCoefficients.quotientMap A Lᶜ n c) hc
  have hz := ModuleHomology.cycle_condition (Complex A K) n
    (ModuleHomology.mapCycles (restrictChain A h) n z)
  simpa only [ModuleHomology.mapCycles_val, z, ModuleHomology.mkCycle_val,
    restrictChain_quotientMap] using hz

/-- Restriction of the original relative class retains its ambient representative. -/
theorem restrict_relativeClass {K L : Set X} (h : K ⊆ L) (n : ℕ)
    (c : CoefficientChains.Chains A X n)
    (hc : ((Complex A L).d n (n - 1)).hom
      (RelativeCoefficients.quotientMap A Lᶜ n c) = 0) :
    restrict A h n (RelativeCoefficients.relativeClass A Lᶜ n c hc) =
      RelativeCoefficients.relativeClass A Kᶜ n c (relativeCycle_restrict A h n c hc) := by
  change (HomologicalComplex.homologyMap (restrictChain A h) n).hom
    (ModuleHomology.cycleClass (Complex A L) n _) = _
  rw [ModuleHomology.homologyMap_cycleClass]
  apply congrArg (ModuleHomology.cycleClass (Complex A K) n)
  apply Subtype.ext
  exact (ModuleHomology.mapCycles_val (restrictChain A h) n _).trans
    (restrictChain_quotientMap A h n c)

end NoExoticSixSphere.SupportedRelativeHomology

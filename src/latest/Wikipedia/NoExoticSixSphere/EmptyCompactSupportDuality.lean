import Wikipedia.NoExoticSixSphere.CompactSupportDualityGluing
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedHomology

/-!
# Original compact-support cap duality on an empty space

There are no singular simplices in an empty space, so the actual
coefficient chains and cochains vanish. Their genuine cycle classes
and the original compact-to-absolute cohomology equivalence give the
vanishing used for empty members and intersections of open covers.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere

variable (X : Type) [TopologicalSpace X] [IsEmpty X]

/-- Native finite-coefficient homology of an empty space is zero in every degree. -/
theorem empty_modHomology_subsingleton (p k : ℕ) : Subsingleton (ModHomology p X k) := by
  let := CoefficientChains.empty_subsingleton (ModuleCat.of ℤ (ZMod p)) X k
  exact (ModuleHomology.cycleClass_surjective (modComplex p X) k).subsingleton

/-- Actual mod-two cohomology of an empty space is zero in every degree. -/
theorem empty_modTwoCohomology_subsingleton (p : ℕ) :
    Subsingleton (ModTwoCapProduct.Cohomology X p) := by
  let := CoefficientChains.empty_subsingleton (ModuleCat.of ℤ ℤ) X p
  let : Subsingleton ((ModTwoCapProduct.cochainComplex X).X p) := by
    refine ⟨fun a b => ?_⟩
    change FirstHurewicz.Chains X p →+ ZMod 2 at a b
    apply AddMonoidHom.ext
    intro c
    have hc : c = 0 :=
      (CoefficientChains.empty_subsingleton (ModuleCat.of ℤ ℤ) X p).elim c 0
    rw [hc, map_zero, map_zero]
  have hs := SingularCohomologyFree.cocycleClass_surjective (ModTwoCapProduct.cochainComplex X) p
  exact hs.subsingleton

/-- The genuine compact-support group of an empty space is zero, by its absolute comparison. -/
theorem CompactSupportCohomology.empty_subsingleton (p : ℕ) :
    Subsingleton (CompactSupportCohomology.Cohomology X p) := by
  let := empty_modTwoCohomology_subsingleton X p
  exact (CompactSupportCohomology.absoluteEquiv X p).injective.subsingleton

namespace CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  [T2Space X] [ChartedSpace E X]

/-- The actual cap-duality property holds on any empty charted space. -/
theorem duality_of_isEmpty : Duality (E := E) n X := by
  refine ⟨?_, fun p _ => CompactSupportCohomology.empty_subsingleton X p⟩
  intro p q h
  let := CompactSupportCohomology.empty_subsingleton X p
  let := empty_modHomology_subsingleton X 2 q
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

end CompactSupportCapMap
end NoExoticSixSphere

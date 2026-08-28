import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCongruenceCharts

/-! # The smooth atlas on the actual symmetric determinant-one matrix space -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.LocalLogarithm

open RealSymmetricMixing

/-- Fix the norm topology on the model before specializing to matrices. -/
abbrev NormedChartedSpace (E : Type*) [NormedAddCommGroup E]
    (M : Type*) [TopologicalSpace M] := ChartedSpace E M

instance chartedSpace (N : Type*) [Fintype N] [DecidableEq N] :
    NormedChartedSpace (DirectionSpace N) (SpecialSpace N) where
  atlas := range atPoint
  chartAt := atPoint
  mem_chart_source := mem_atPoint_source
  chart_mem_atlas B := ⟨B, rfl⟩

instance isManifold (N : Type*) [Fintype N] [DecidableEq N] :
    IsManifold 𝓘(ℝ, DirectionSpace N) ∞ (SpecialSpace N) :=
  isManifold_of_contDiffOn 𝓘(ℝ, DirectionSpace N) ∞ (SpecialSpace N) (by
    rintro _ _ ⟨B, rfl⟩ ⟨C, rfl⟩
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using!
        contDiffOn_transition B C)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.LocalLogarithm

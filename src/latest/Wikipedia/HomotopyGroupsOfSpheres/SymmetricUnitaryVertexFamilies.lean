import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexSpace

/-! # Smooth families in the actual finite symmetric determinant-one vertex manifold -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f : M → Space N m} {x : M}

local instance directionSelfChart :
    LocalLogarithm.NormedChartedSpace
      (RealSymmetricMixing.DirectionSpace N) (RealSymmetricMixing.DirectionSpace N) :=
  chartedSpaceSelf _

local instance familyModelSelfChart :
    LocalLogarithm.NormedChartedSpace (Model N m) (Model N m) := chartedSpaceSelf _

theorem contMDiffAt_iff_coordinatewise :
    ContMDiffAt I 𝓘(ℝ, Model N m) ∞ f x ↔
      ∀ i : Fin m, ContMDiffAt I 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞
        (fun y ↦ f y i) x := by
  constructor
  · intro hf i
    exact (contMDiff_eval (N := N) i).contMDiffAt.comp x hf
  · intro hf
    apply (contMDiffAt_iff_target_of_mem_source
      (I := I) (I' := 𝓘(ℝ, Model N m)) (f := f)
      (mem_atVertices_source (f x))).mpr
    refine ⟨continuousAt_pi.mpr (fun i ↦ (hf i).continuousAt), ?_⟩
    change ContMDiffAt I 𝓘(ℝ, Model N m) ∞ (fun y ↦ atVertices (f x) (f y)) x
    apply contMDiffAt_pi_space.mpr
    intro i
    have hchart : ContMDiffAt 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N)
        𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞
        (LocalLogarithm.atPoint (f x i)) (f x i) := by
      simpa only [] using! (contMDiffAt_extChartAt
        (I := 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N)) (n := ∞) (x := f x i))
    simpa only [] using! hchart.comp (f := fun y ↦ f y i)
      (g := LocalLogarithm.atPoint (f x i)) x (hf i)

theorem contMDiff_iff_coordinatewise :
    ContMDiff I 𝓘(ℝ, Model N m) ∞ f ↔
      ∀ i : Fin m, ContMDiff I 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞
        (fun y ↦ f y i) := by
  constructor
  · intro hf i x
    exact contMDiffAt_iff_coordinatewise.mp (hf x) i
  · intro hf x
    exact contMDiffAt_iff_coordinatewise.mpr (fun i ↦ hf i x)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace

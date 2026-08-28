import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryAtlas

/-! # Smoothness in the symmetric unitary atlas and in ambient matrix coordinates -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open RealSymmetricMixing LocalLogarithm

namespace Smoothness

variable {N : Type*} [Fintype N] [DecidableEq N]

local instance matrixSelfChart :
    NormedChartedSpace (Matrix N N ℂ) (Matrix N N ℂ) := chartedSpaceSelf _

local instance directionSelfChart :
    NormedChartedSpace (DirectionSpace N) (DirectionSpace N) := chartedSpaceSelf _

theorem contMDiff_matrix :
    ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, Matrix N N ℂ) ∞ (matrix (N := N)) := by
  intro B
  rw [contMDiffAt_iff_source]
  let U := (frame B).val.val
  have hs : ContDiff ℝ ∞ (fun A : DirectionSpace N ↦
      U * matrix (exponential A) * U.transpose) :=
    (contDiff_const.mul contDiff_exponential_matrix).mul contDiff_const
  change ContMDiffWithinAt 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, Matrix N N ℂ) ∞
    (fun A : DirectionSpace N ↦ U * matrix (exponential A) * U.transpose) (range id) _
  rw [range_id, contMDiffWithinAt_univ]
  simpa only [] using! hs.contMDiff.contMDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → SpecialSpace N} {x : M}

theorem contMDiffAt_iff_chart :
    ContMDiffAt I 𝓘(ℝ, DirectionSpace N) ∞ f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(ℝ, DirectionSpace N) ∞
        (fun y ↦ atPoint (f x) (f y)) x :=
  contMDiffAt_iff_target_of_mem_source
    (I' := 𝓘(ℝ, DirectionSpace N)) (n := ∞) (f := f) (mem_atPoint_source (f x))

theorem contMDiffAt_of_matrix
    (h : ContMDiffAt I 𝓘(ℝ, Matrix N N ℂ) ∞ (fun y ↦ matrix (f y)) x) :
    ContMDiffAt I 𝓘(ℝ, DirectionSpace N) ∞ f x := by
  have hf : ContinuousAt f x := tendsto_subtype_rng.mpr
    (tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr h.continuousAt))
  apply contMDiffAt_iff_chart.mpr
  refine ⟨hf, ?_⟩
  let V := ((frame (f x)).val⁻¹).val
  have hv : ContDiff ℝ ∞ (fun Q : Matrix N N ℂ ↦ V * Q * V.transpose) :=
    (contDiff_const.mul contDiff_id).mul contDiff_const
  have hv' : ContMDiffAt 𝓘(ℝ, Matrix N N ℂ) 𝓘(ℝ, Matrix N N ℂ) ∞
      (fun Q : Matrix N N ℂ ↦ V * Q * V.transpose) (matrix (f x)) := by
    simpa only [] using! hv.contMDiff.contMDiffAt (x := matrix (f x))
  have hm : ContMDiffAt I 𝓘(ℝ, Matrix N N ℂ) ∞
      (fun y ↦ V * matrix (f y) * V.transpose) x :=
    hv'.comp x h
  have hloc : matrix ((translation (f x)).symm (f x)) ∈
      (ComplexMatrixLocalLogarithm.exponentialChart N).target := by
    rw [translation_symm_self]
    exact ComplexMatrixLocalLogarithm.one_mem_target
  have hc : ContDiffAt ℝ ∞ (coordinates (N := N))
      (matrix ((translation (f x)).symm (f x))) :=
    (contDiffOn_coordinates (N := N)).contDiffAt
      ((ComplexMatrixLocalLogarithm.exponentialChart N).open_target.mem_nhds hloc)
  have hc' : ContMDiffAt 𝓘(ℝ, Matrix N N ℂ) 𝓘(ℝ, DirectionSpace N) ∞
      (coordinates (N := N)) (V * matrix (f x) * V.transpose) := by
    simpa only [] using! hc.contMDiffAt
  exact hc'.comp (f := fun y ↦ V * matrix (f y) * V.transpose)
    (g := coordinates (N := N)) x hm

theorem contMDiffAt_iff_matrix :
    ContMDiffAt I 𝓘(ℝ, DirectionSpace N) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Matrix N N ℂ) ∞ (fun y ↦ matrix (f y)) x :=
  ⟨fun h ↦ (contMDiff_matrix (N := N)).contMDiffAt.comp x h, contMDiffAt_of_matrix⟩

theorem contMDiff_iff_matrix :
    ContMDiff I 𝓘(ℝ, DirectionSpace N) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Matrix N N ℂ) ∞ (fun y ↦ matrix (f y)) := by
  simp only [ContMDiff, contMDiffAt_iff_matrix]

end Smoothness

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

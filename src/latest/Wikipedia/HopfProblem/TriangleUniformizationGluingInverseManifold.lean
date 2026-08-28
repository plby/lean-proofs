import Wikipedia.HopfProblem.TriangleUniformizationGluingInverse
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Holomorphic inverses in the existing complex curve atlases

A holomorphic homeomorphism between complex one-dimensional manifolds has
a holomorphic inverse.  The proof uses charts from the given atlases and
the planar inverse theorem, so no manifold structure is transported along
the homeomorphism.
-/

noncomputable section

open Set ChartedSpace IsManifold
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ℂ M] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N]

/-- A holomorphic homeomorphism of complex curves has a holomorphic inverse
with respect to the already specified manifold structures. -/
theorem contMDiff_symm_of_contMDiff (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm := by
  intro y
  let c : OpenPartialHomeomorph ℂ ℂ :=
    ((chartAt ℂ (e.symm y)).symm.trans e.toOpenPartialHomeomorph).trans (chartAt ℂ y)
  have hc : DifferentiableOn ℂ c c.source := by
    intro z hz
    have hz₁ : z ∈ (chartAt ℂ (e.symm y)).target := hz.1.1
    have hz₂ : e ((chartAt ℂ (e.symm y)).symm z) ∈ (chartAt ℂ y).source := hz.2
    have h₁ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (e.symm y)).symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (e.symm y)) hz₁
    have h₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y)
        (e ((chartAt ℂ (e.symm y)).symm z)) :=
      contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas y) hz₂
    exact ((h₂.comp z ((he _).comp z h₁)).contDiffAt.differentiableAt
      (by simp)).differentiableWithinAt
  have hy : (chartAt ℂ y) y ∈ c.target := by
    refine ⟨(chartAt ℂ y).map_source (mem_chart_source ℂ y), ?_⟩
    change (chartAt ℂ y).symm ((chartAt ℂ y) y) ∈ (univ : Set N) ∧
      e.symm ((chartAt ℂ y).symm ((chartAt ℂ y) y)) ∈ (chartAt ℂ (e.symm y)).source
    rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    exact ⟨mem_univ _, mem_chart_source ℂ _⟩
  have hinv : ContDiffAt ℂ ω c.symm ((chartAt ℂ y) y) :=
    ((differentiableOn_symm_of_differentiableOn c hc).contDiffOn c.open_target).contDiffAt
      (c.open_target.mem_nhds hy)
  change ContDiffAt ℂ ω
    ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) at hinv
  apply contMDiffAt_iff.mpr
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, range_id,
    contDiffWithinAt_univ] using hinv

/-- Bundle a holomorphic homeomorphism as a biholomorphism without changing
either of the prescribed complex curve atlases. -/
def biholomorphOfHomeomorph (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) M N ω where
  toEquiv := e.toEquiv
  contMDiff_toFun := he
  contMDiff_invFun := contMDiff_symm_of_contMDiff e he

@[simp] theorem biholomorphOfHomeomorph_apply (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) (x : M) :
    biholomorphOfHomeomorph e he x = e x := rfl

@[simp] theorem biholomorphOfHomeomorph_symm_apply (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) (y : N) :
    (biholomorphOfHomeomorph e he).symm y = e.symm y := rfl

@[simp] theorem biholomorphOfHomeomorph_toHomeomorph (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e) :
    (biholomorphOfHomeomorph e he).toHomeomorph = e := by
  ext x
  rfl

end Wikipedia.HopfProblem.TriangleUniformizationGluing

import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackCoordinates

/-!
# Analyticity of genuine chart derivatives

The coordinate derivative of a holomorphic map is holomorphic on the natural
overlap of its source and target charts.  This follows by differentiating the
actual analytic coordinate expression on its open domain, then composing with
the source chart.  Its determinant is consequently holomorphic as well.
No independent derivative or determinant regularity is assumed.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "Iᴸ" => modelWithCornersSelf ℂ (Model →L[ℂ] Model)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold I ω M] [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- The derivative of the actual coordinate expression is holomorphic on
the natural source-and-target chart overlap. -/
theorem chartDerivative_holomorphicOn (f : M → N) (i : atlas Model M)
    (j : atlas Model N) (hf : ContMDiff I I ω f) :
    ContMDiffOn I Iᴸ ω (chartDerivative f i j)
      (i.val.source ∩ f ⁻¹' j.val.source) := by
  have hi : ContMDiffOn I I ω i.val.symm i.val.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas i.property)
  have hj : ContMDiffOn I I ω j.val j.val.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas j.property)
  let D : Set Model := i.val.target ∩ (f ∘ i.val.symm) ⁻¹' j.val.source
  have hfi : ContMDiffOn I I ω (f ∘ i.val.symm) i.val.target :=
    hf.comp_contMDiffOn hi
  have hD : IsOpen D :=
    hfi.continuousOn.isOpen_inter_preimage i.val.open_target j.val.open_source
  have hcoord : ContMDiffOn I I ω (j.val ∘ f ∘ i.val.symm) D := hj.comp' hfi
  have hd : ContDiffOn ℂ ω (fderiv ℂ (j.val ∘ f ∘ i.val.symm)) D :=
    hcoord.contDiffOn.fderiv_of_isOpen hD (by simp)
  have hsource : ContMDiffOn I I ω i.val (i.val.source ∩ f ⁻¹' j.val.source) :=
    (contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas i.property)).mono inter_subset_left
  refine hd.contMDiffOn.comp hsource ?_
  intro x hx
  refine ⟨i.val.map_source hx.1, ?_⟩
  change f (i.val.symm (i.val x)) ∈ j.val.source
  rw [i.val.left_inv hx.1]
  exact hx.2

/-- The genuine chart Jacobian is holomorphic, because the determinant is
an analytic polynomial on the space of continuous endomorphisms. -/
theorem chartDeterminant_holomorphicOn (f : M → N) (i : atlas Model M)
    (j : atlas Model N) (hf : ContMDiff I I ω f) :
    ContMDiffOn I I₁ ω (chartDeterminant f i j)
      (i.val.source ∩ f ⁻¹' j.val.source) :=
  Atlas.determinant_contDiff.contMDiff.comp_contMDiffOn
    (chartDerivative_holomorphicOn f i j hf)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

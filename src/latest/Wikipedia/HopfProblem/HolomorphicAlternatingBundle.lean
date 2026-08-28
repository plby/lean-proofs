import Wikipedia.HopfProblem.HolomorphicAlternatingMaps
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The genuine holomorphic bundle of alternating maps

Mathlib's topological alternating-map bundle retains its original total
space and trivializations. Analyticity of its actual coordinate changes
upgrades that bundle to a holomorphic vector bundle in finite dimensions.
In particular this applies to alternating covectors on the native tangent
bundle of the constructed threefold.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAlternatingBundle

variable {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  {IB : ModelWithCorners ℂ EB HB}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [FiniteDimensional ℂ F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [FiniteDimensional ℂ F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [ContMDiffVectorBundle ω F₁ E₁ IB] [ContMDiffVectorBundle ω F₂ E₂ IB]
  (p : ℕ)

open Pretrivialization in
/-- The original alternating-bundle coordinate change is holomorphic. -/
theorem coordChange_holomorphic
    (e₁ e₁' : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B))
    (e₂ e₂' : Trivialization F₂ (TotalSpace.proj : TotalSpace F₂ E₂ → B))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(ℂ, (F₁ [⋀^Fin p]→L[ℂ] F₂) →L[ℂ] (F₁ [⋀^Fin p]→L[ℂ] F₂)) ω
      (continuousAlternatingMapCoordChange ℂ (Fin p) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr,
    ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · exact (ContinuousLinearMap.compContinuousAlternatingMapCLM
      (ι := Fin p) ℂ F₁ F₂ F₂).contMDiff.comp_contMDiffOn
        ((contMDiffOn_coordChangeL (IB := IB) (n := ω) e₂ e₂').mono
          (by mfld_set_tac))
  · exact (HolomorphicAlternatingMaps.pullback_contDiff F₁ F₂ p F₁).contMDiff
      |>.comp_contMDiffOn
        ((contMDiffOn_coordChangeL (IB := IB) (n := ω) e₁' e₁).mono
          (by mfld_set_tac))

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul ℂ (E₂ x)]

instance prebundle_isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle ℂ (Fin p) F₁ E₁ F₂ E₂).IsContMDiff IB ω where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨Pretrivialization.continuousAlternatingMapCoordChange ℂ (Fin p) e₁ e₁' e₂ e₂',
      coordChange_holomorphic p e₁ e₁' e₂ e₂',
      Pretrivialization.continuousAlternatingMapCoordChange_apply⟩

/-- The actual alternating-map bundle, with its existing topology, is holomorphic. -/
instance contMDiffVectorBundle :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin p]→L[ℂ] F₂)
      (fun x => E₁ x [⋀^Fin p]→L[ℂ] E₂ x) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle ℂ (Fin p) F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end Wikipedia.HopfProblem.HolomorphicAlternatingBundle

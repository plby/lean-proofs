import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Native smooth local inverses used in the Morse lemma

The smooth inverse-function theorem first gives an actual local
homeomorphism. Continuity of the derivative keeps it invertible on a
smaller open neighborhood. The original map and its genuine inverse are
therefore smooth throughout their actual domains, so they form a native
partial diffeomorphism. Smoothness is `C∞`, not real analyticity.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual smooth map with invertible derivative has a genuine native
smooth partial diffeomorphism on a neighborhood inside its original domain.
Its forward function is exactly the original function, even outside the
chosen source set. -/
theorem exists_partialDiffeomorph_of_contDiffOn
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    (a : E) (ha : a ∈ U) (f' : E ≃L[ℝ] F)
    (hderiv : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      a ∈ e.source ∧ e.source ⊆ U ∧ ∀ x : E, e x = f x := by
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hU.mem_nhds ha)
  have hdc : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds ha)
  have hinv : {x : E | ∃ l : E ≃L[ℝ] F, (l : E →L[ℝ] F) = fderiv ℝ f x} ∈ 𝓝 a := by
    have hn := f'.nhds
    rw [← hderiv.fderiv] at hn
    exact hdc.preimage_mem_nhds hn
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hinv)
  let e : OpenPartialHomeomorph E F :=
    (hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W
  have heW : e.source ⊆ W := by
    intro x hx
    change x ∈ ((hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W).source at hx
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen] at hx
    exact hx.2
  have heU : e.source ⊆ U := fun x hx => (hWsub (heW hx)).1
  have hae : a ∈ e.source := by
    change a ∈ ((hfa.toOpenPartialHomeomorph f hderiv (by simp)).restr W).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hWopen]
    exact ⟨hfa.mem_toOpenPartialHomeomorph_source hderiv (by simp), haW⟩
  refine ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }, hae, heU, fun _ => rfl⟩
  · change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f e.source
    exact (hf.mono heU).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    intro y hy
    have hxW := heW (e.map_target hy)
    obtain ⟨hxU, l, hl⟩ := hWsub hxW
    have hfx : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (hU.mem_nhds hxU)
    have hdx : HasFDerivAt f (l : E →L[ℝ] F) (e.symm y) := by
      rw [hl]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    exact (e.contDiffAt_symm hy hdx hfx).contDiffWithinAt

/-- The globally smooth specialization uses no separately supplied local
inverse or inverse-smoothness assumption. -/
theorem exists_partialDiffeomorph_of_contDiff
    {f : E → F} (hf : ContDiff ℝ ∞ f) (a : E) (f' : E ≃L[ℝ] F)
    (hderiv : HasFDerivAt f (f' : E →L[ℝ] F) a) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞,
      a ∈ e.source ∧ ∀ x : E, e x = f x := by
  obtain ⟨e, ha, _, he⟩ := exists_partialDiffeomorph_of_contDiffOn
    isOpen_univ hf.contDiffOn a (mem_univ a) f' hderiv
  exact ⟨e, ha, he⟩

end Wikipedia.HopfProblem.SmoothMorseLemma

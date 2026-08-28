import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Analytic.Order

/-! # Countability of zeros of actual holomorphic functions on the upper half-plane -/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

/-- A nonzero holomorphic function on the actual upper half-plane has
a countable zero set, by analytic isolated zeros and second countability. -/
theorem upperHalfPlane_holomorphic_zero_set_countable {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ∃ z : ℍ, f z ≠ 0) :
    Set.Countable {z : ℍ | f z = 0} := by
  obtain ⟨a, ha⟩ := hne
  let F : ℂ → ℂ := f ∘ ofComplex
  have hF : AnalyticOnNhd ℂ F upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp
      (hf.mdifferentiable (by simp))).analyticOnNhd isOpen_upperHalfPlaneSet
  have hconn : IsConnected upperHalfPlaneSet := by
    simpa only [image_univ, range_coe] using
      (isConnected_univ (α := ℍ)).image ((↑) : ℍ → ℂ) continuous_coe.continuousOn
  have ha' : F (a : ℂ) ≠ 0 := by simpa only [F, Function.comp_apply, ofComplex_apply] using ha
  have hz := hF.preimage_zero_mem_codiscreteWithin ha' a.im_pos hconn
  have hd : IsDiscrete ((F ⁻¹' {0}) ∩ upperHalfPlaneSet) :=
    isDiscrete_of_codiscreteWithin (by simpa only [preimage_compl] using hz)
  let := isDiscrete_iff_discreteTopology.mp hd
  have hc : Countable {z : ℂ // z ∈ (F ⁻¹' {0}) ∩ upperHalfPlaneSet} :=
    separableSpace_iff_countable.mp inferInstance
  have hs : Set.Countable ((F ⁻¹' {0}) ∩ upperHalfPlaneSet) := Set.countable_coe_iff.mp hc
  apply (hs.preimage coe_injective).mono
  intro z hz
  refine ⟨?_, z.im_pos⟩
  simpa only [F, mem_preimage, mem_singleton_iff, mem_ofPred_eq,
    Function.comp_apply, ofComplex_apply] using hz

end Wikipedia.HopfProblem

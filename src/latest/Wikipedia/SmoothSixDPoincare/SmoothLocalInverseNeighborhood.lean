import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# A smooth inverse on a single open neighborhood

Smoothness at one point, by itself, does not give one neighborhood on which
all differentiability orders hold. Here the forward map is globally smooth.
Continuity of its derivative gives a neighborhood of invertible derivatives,
and the local inverse is smooth at every point of the corresponding target.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_inverse_neighborhood (g : OpenPartialHomeomorph E F)
    (hg : ContDiff ℝ ∞ g) {x : E} (hx : x ∈ g.source)
    (hd : (fderiv ℝ g x).IsInvertible) :
    ∃ V : Set F, IsOpen V ∧ g x ∈ V ∧ V ⊆ g.target ∧ ContDiffOn ℝ ∞ g.symm V := by
  obtain ⟨e, he⟩ := hd
  have hmaps : {L : E →L[ℝ] F | L.IsInvertible} ∈ 𝓝 (fderiv ℝ g x) := by
    change {L : E →L[ℝ] F | ∃ e : E ≃L[ℝ] F, ↑e = L} ∈ 𝓝 (fderiv ℝ g x)
    rw [← he]
    exact e.nhds
  have hinv : {y : E | (fderiv ℝ g y).IsInvertible} ∈ 𝓝 x :=
    (hg.continuous_fderiv (by simp)).continuousAt.preimage_mem_nhds hmaps
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hinv
  refine ⟨g.target ∩ g.symm ⁻¹' U, g.isOpen_inter_preimage_symm hU,
    ⟨g.map_source hx, ?_⟩, inter_subset_left, ?_⟩
  · simpa only [mem_preimage, g.left_inv hx] using hxU
  · intro y hy
    obtain ⟨e', he'⟩ := hUsub hy.2
    have hder : HasFDerivAt g (e' : E →L[ℝ] F) (g.symm y) := by
      rw [he']
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (g.contDiffAt_symm hy.1 hder hg.contDiffAt).contDiffWithinAt

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

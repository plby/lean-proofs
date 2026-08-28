import Wikipedia.SmoothSixDPoincare.NativeLocalDegreeNeighborhood

/-! # Native regularity from an actual smooth coordinate chart -/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.NativeRegularityFromChart

variable {D E F H M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  (c : PartialDiffeomorph 𝓘(ℝ, D) I D M ∞) {z : D} (hz : z ∈ c.source)
  {f : M → F}

include hz

theorem contMDiffAt_of_comp (hf : ContDiffAt ℝ ∞ (f ∘ c) z) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ f (c z) := by
  have hci : ContMDiffAt I 𝓘(ℝ, D) ∞ c.symm (c z) :=
    c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds (c.map_source hz))
  have hf' : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, F) ∞ (f ∘ c) (c.symm (c z)) := by
    have he : c.symm (c z) = z := c.left_inv hz
    rw [he]
    exact hf.contMDiffAt
  apply (hf'.comp (c z) hci).congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds (c.map_source hz)] with y hy
  exact (congrArg f (c.right_inv hy)).symm

theorem isInvertible_mfderiv_of_comp (hf : ContDiffAt ℝ ∞ (f ∘ c) z)
    (A : D ≃L[ℝ] F) (hA : HasFDerivAt (f ∘ c) A.toContinuousLinearMap z) :
    (mfderiv I 𝓘(ℝ, F) f (c z)).IsInvertible := by
  have hfn := contMDiffAt_of_comp c hz hf
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, D) I ∞ c z := ⟨c, hz, Set.eqOn_refl _ _⟩
  let C := hloc.mfderivToContinuousLinearEquiv (by simp)
  have hchain := mfderiv_comp z (hfn.mdifferentiableAt (by simp))
    (c.mdifferentiableAt (by simp) hz)
  rw [mfderiv_eq_fderiv, hA.fderiv] at hchain
  refine ⟨C.symm.trans A, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change A (C.symm v) = mfderiv I 𝓘(ℝ, F) f (c z) v
  calc
    _ = mfderiv I 𝓘(ℝ, F) f (c z) (C (C.symm v)) :=
      congrArg (fun L : D →L[ℝ] F ↦ L (C.symm v)) hchain
    _ = _ := by rw [C.apply_symm_apply]

end Wikipedia.HomotopyGroupsOfSpheres.NativeRegularityFromChart

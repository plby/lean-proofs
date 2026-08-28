import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Finite sums of actual vector-valued manifold differentials -/

open scoped Manifold

namespace NoExoticSixSphere

variable {E H X F : Type*} {ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mvfderiv_finset_sum (s : Finset ι) (f : ι → X → F) (x : X)
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, F) (f i) x) :
    mvfderiv I (∑ i ∈ s, f i) x = ∑ i ∈ s, mvfderiv I (f i) x := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert i s hi ih =>
      intro hf
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, MDifferentiableAt I 𝓘(ℝ, F) (f j) x :=
        fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        mvfderiv_add hfi (MDifferentiableAt.sum hfs), ih hfs]

end NoExoticSixSphere

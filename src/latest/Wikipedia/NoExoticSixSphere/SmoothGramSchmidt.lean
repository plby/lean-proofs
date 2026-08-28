import Wikipedia.NoExoticSixSphere.ContinuousGramSchmidt
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth Gram--Schmidt at an independent frame

Only independence at the point in question is needed. Each preceding
orthogonalized column is nonzero there, so its normalization and the next
projection coefficient are smooth near that point.
-/

noncomputable section

open InnerProductSpace
open scoped ContDiff

namespace NoExoticSixSphere

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
  {x : X} (f : X → ι → E)

theorem contDiffAt_gramSchmidt (hf : ∀ i, ContDiffAt ℝ ∞ (fun y ↦ f y i) x)
    (hi : LinearIndependent ℝ (f x)) (i : ι) :
    ContDiffAt ℝ ∞ (fun y ↦ gramSchmidt ℝ (f y) i) x := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : (fun y ↦ gramSchmidt ℝ (f y) i) = fun y ↦ f y i -
        ∑ j ∈ Finset.Iio i,
          (inner ℝ (gramSchmidt ℝ (f y) j) (f y i) /
            ‖gramSchmidt ℝ (f y) j‖ ^ 2) • gramSchmidt ℝ (f y) j := by
      funext y
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (f y) i).symm
    rw [he]
    apply (hf i).sub
    apply ContDiffAt.sum
    intro j hj
    have hg := ih j (Finset.mem_Iio.mp hj)
    have hn : gramSchmidt ℝ (f x) j ≠ 0 := gramSchmidt_ne_zero j hi
    have hnorm := (contDiffAt_norm ℝ hn).comp x hg
    exact ((hg.inner ℝ (hf i)).div (hnorm.pow 2)
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))).smul hg

theorem contDiffAt_gramSchmidtNormed (hf : ∀ i, ContDiffAt ℝ ∞ (fun y ↦ f y i) x)
    (hi : LinearIndependent ℝ (f x)) (i : ι) :
    ContDiffAt ℝ ∞ (fun y ↦ gramSchmidtNormed ℝ (f y) i) x := by
  have hg := contDiffAt_gramSchmidt f hf hi i
  have hn : gramSchmidt ℝ (f x) i ≠ 0 := gramSchmidt_ne_zero i hi
  have hnorm := (contDiffAt_norm ℝ hn).comp x hg
  exact (hnorm.inv (norm_ne_zero_iff.mpr hn)).smul hg

end NoExoticSixSphere

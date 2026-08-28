import Wikipedia.NoExoticSixSphere.HemisphereClutching
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Continuous orthonormalization of independent frames

Gram--Schmidt is continuous on the locus of independent frames: every division
is by the norm of a nonzero orthogonalized vector. This is the analytic part of
reducing a general-linear-group homotopy problem to an orthogonal-group problem.
No homotopy-group computation is asserted here.
-/

open InnerProductSpace Module

namespace NoExoticSixSphere

variable {X E ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- Orthogonalization varies continuously for a continuous family of independent frames. -/
theorem continuous_gramSchmidt (f : X → ι → E) (hf : ∀ i, Continuous (fun x ↦ f x i))
    (hi : ∀ x, LinearIndependent ℝ (f x)) (i : ι) :
    Continuous (fun x ↦ gramSchmidt ℝ (f x) i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have heq : (fun x ↦ gramSchmidt ℝ (f x) i) = fun x ↦ f x i -
        ∑ j ∈ Finset.Iio i,
          (inner ℝ (gramSchmidt ℝ (f x) j) (f x i) /
            ‖gramSchmidt ℝ (f x) j‖ ^ 2) • gramSchmidt ℝ (f x) j := by
      funext x
      exact eq_sub_of_add_eq (gramSchmidt_def'' ℝ (f x) i).symm
    rw [heq]
    apply (hf i).sub
    apply continuous_finsetSum
    intro j hj
    have hc := ih j (Finset.mem_Iio.mp hj)
    exact ((hc.inner (hf i)).div (hc.norm.pow 2)
      (fun x ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hi x))))).smul hc

/-- Normalizing Gram--Schmidt remains continuous on the independent-frame locus. -/
theorem continuous_gramSchmidtNormed (f : X → ι → E) (hf : ∀ i, Continuous (fun x ↦ f x i))
    (hi : ∀ x, LinearIndependent ℝ (f x)) (i : ι) :
    Continuous (fun x ↦ gramSchmidtNormed ℝ (f x) i) := by
  have hc := continuous_gramSchmidt f hf hi i
  exact (hc.norm.inv₀
    (fun x ↦ norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i (hi x)))).smul hc

/-- The diagonal inner product in unnormalized Gram--Schmidt is its squared norm. -/
theorem inner_gramSchmidt_diagonal (f : ι → E) (i : ι) :
    inner ℝ (gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖ ^ 2 := by
  rw [gramSchmidt_def'' ℝ f i, inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hz : ∑ j ∈ Finset.Iio i,
      inner ℝ (gramSchmidt ℝ f i)
        ((inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖ ^ 2) •
          gramSchmidt ℝ f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [real_inner_smul_right,
      gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.mp hj).ne', mul_zero]
  rw [hz, add_zero]

/-- The normalized diagonal inner product is positive for independent input frames. -/
theorem inner_gramSchmidtNormed_diagonal_pos (f : ι → E)
    (hi : LinearIndependent ℝ f) (i : ι) :
    0 < inner ℝ (gramSchmidtNormed ℝ f i) (f i) := by
  rw [gramSchmidtNormed, real_inner_smul_left, inner_gramSchmidt_diagonal]
  have hn : 0 < ‖gramSchmidt ℝ f i‖ :=
    norm_pos_iff.mpr (gramSchmidt_ne_zero i hi)
  exact mul_pos (inv_pos.mpr hn) (pow_pos hn 2)

/-- The Gram--Schmidt orthonormal basis is pointwise continuous for independent frames. -/
theorem continuous_gramSchmidtOrthonormalBasis [Fintype ι] [FiniteDimensional ℝ E]
    (hd : finrank ℝ E = Fintype.card ι) (f : X → ι → E)
    (hf : ∀ i, Continuous (fun x ↦ f x i)) (hi : ∀ x, LinearIndependent ℝ (f x)) (i : ι) :
    Continuous (fun x ↦ gramSchmidtOrthonormalBasis hd (f x) i) := by
  have heq : (fun x ↦ gramSchmidtOrthonormalBasis hd (f x) i) =
      fun x ↦ gramSchmidtNormed ℝ (f x) i := by
    funext x
    apply gramSchmidtOrthonormalBasis_apply
    apply norm_ne_zero_iff.mp
    rw [gramSchmidtNormed_unit_length i (hi x)]
    exact one_ne_zero
  rw [heq]
  exact continuous_gramSchmidtNormed f hf hi i

end NoExoticSixSphere

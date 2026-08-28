import Wikipedia.NoExoticSixSphere.OrthogonalExponential
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Hilbert--Schmidt quadratic form on actual operators

This is a positive-definite, smooth quadratic form invariant under left and
right orthogonal multiplication. It is not installed as an inner-product
instance for the operator norm, which is a different norm.
-/

open scoped ContDiff

namespace NoExoticSixSphere.HilbertSchmidt

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ}

noncomputable def innerForm (A B : Vector n →L[ℝ] Vector n) : ℝ :=
  ∑ i : Fin n, inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
    (B (EuclideanSpace.basisFun (Fin n) ℝ i))

noncomputable def squareNorm (A : Vector n →L[ℝ] Vector n) : ℝ := innerForm A A

theorem innerForm_comm (A B : Vector n →L[ℝ] Vector n) : innerForm A B = innerForm B A := by
  unfold innerForm
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

theorem innerForm_add_right (A B C : Vector n →L[ℝ] Vector n) :
    innerForm A (B + C) = innerForm A B + innerForm A C := by
  simp [innerForm, inner_add_right, Finset.sum_add_distrib]

theorem innerForm_add_left (A B C : Vector n →L[ℝ] Vector n) :
    innerForm (A + B) C = innerForm A C + innerForm B C := by
  rw [innerForm_comm, innerForm_add_right, innerForm_comm C A, innerForm_comm C B]

theorem innerForm_smul_right (r : ℝ) (A B : Vector n →L[ℝ] Vector n) :
    innerForm A (r • B) = r * innerForm A B := by
  simp [innerForm, inner_smul_right, Finset.mul_sum]

theorem innerForm_smul_left (r : ℝ) (A B : Vector n →L[ℝ] Vector n) :
    innerForm (r • A) B = r * innerForm A B := by
  rw [innerForm_comm, innerForm_smul_right, innerForm_comm B A]

theorem squareNorm_smul (r : ℝ) (A : Vector n →L[ℝ] Vector n) :
    squareNorm (r • A) = r ^ 2 * squareNorm A := by
  rw [squareNorm, innerForm_smul_left, innerForm_smul_right]
  change r * (r * innerForm A A) = r ^ 2 * innerForm A A
  ring

theorem squareNorm_add (A B : Vector n →L[ℝ] Vector n) :
    squareNorm (A + B) = squareNorm A + 2 * innerForm A B + squareNorm B := by
  rw [squareNorm, innerForm_add_left, innerForm_add_right, innerForm_add_right,
    innerForm_comm B A]
  unfold squareNorm
  ring

theorem squareNorm_eq_sum (A : Vector n →L[ℝ] Vector n) :
    squareNorm A = ∑ i : Fin n, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
  simp only [squareNorm, innerForm, real_inner_self_eq_norm_sq]

theorem squareNorm_nonneg (A : Vector n →L[ℝ] Vector n) : 0 ≤ squareNorm A := by
  rw [squareNorm_eq_sum]
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem squareNorm_eq_zero_iff (A : Vector n →L[ℝ] Vector n) : squareNorm A = 0 ↔ A = 0 := by
  constructor
  · intro hA
    rw [squareNorm_eq_sum] at hA
    have hp := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
        sq_nonneg ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖)).mp hA
    have hl : A.toLinearMap = 0 := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      have hz := hp i (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hl x
  · rintro rfl
    simp [squareNorm_eq_sum]

theorem sum_inner_eq_trace (b : OrthonormalBasis (Fin n) ℝ (Vector n))
    (A B : Vector n →L[ℝ] Vector n) :
    (∑ i, inner ℝ (A (b i)) (B (b i))) =
      LinearMap.trace ℝ (Vector n) (A.adjoint.comp B).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  exact (ContinuousLinearMap.adjoint_inner_right A (b i) (B (b i))).symm

theorem innerForm_eq_trace (A B : Vector n →L[ℝ] Vector n) :
    innerForm A B = LinearMap.trace ℝ (Vector n) (A.adjoint.comp B).toLinearMap :=
  sum_inner_eq_trace (EuclideanSpace.basisFun (Fin n) ℝ) A B

theorem innerForm_left (a : OrthogonalOperators n) (A B : Vector n →L[ℝ] Vector n) :
    innerForm (a.1.1.comp A) (a.1.1.comp B) = innerForm A B := by
  unfold innerForm
  apply Finset.sum_congr rfl
  intro i _
  exact (toEquiv a).inner_map_map _ _

theorem innerForm_right (a : OrthogonalOperators n) (A B : Vector n →L[ℝ] Vector n) :
    innerForm (A.comp a.1.1) (B.comp a.1.1) = innerForm A B := by
  have h := sum_inner_eq_trace ((EuclideanSpace.basisFun (Fin n) ℝ).map (toEquiv a)) A B
  rw [← innerForm_eq_trace] at h
  exact h

theorem squareNorm_left (a : OrthogonalOperators n) (A : Vector n →L[ℝ] Vector n) :
    squareNorm (a.1.1.comp A) = squareNorm A := innerForm_left a A A

theorem squareNorm_right (a : OrthogonalOperators n) (A : Vector n →L[ℝ] Vector n) :
    squareNorm (A.comp a.1.1) = squareNorm A := innerForm_right a A A

theorem contDiff_innerForm :
    ContDiff ℝ ∞ (fun p : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
      innerForm p.1 p.2) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_fst.clm_apply contDiff_const).inner ℝ
    (contDiff_snd.clm_apply contDiff_const)

theorem contDiff_squareNorm : ContDiff ℝ ∞ (squareNorm (n := n)) :=
  ContDiff.comp (f := fun A : Vector n →L[ℝ] Vector n ↦ (A, A))
    (g := fun p : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
      innerForm p.1 p.2)
    (contDiff_innerForm (n := n)) (contDiff_id.prodMk contDiff_id)

theorem continuous_innerForm_comp {X : Type*} [TopologicalSpace X]
    {A B : X → Vector n →L[ℝ] Vector n} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x ↦ innerForm (A x) (B x)) :=
  Continuous.comp
    (g := fun p : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
      innerForm p.1 p.2) (f := fun x ↦ (A x, B x))
    (contDiff_innerForm (n := n)).continuous (hA.prodMk hB)

end NoExoticSixSphere.HilbertSchmidt

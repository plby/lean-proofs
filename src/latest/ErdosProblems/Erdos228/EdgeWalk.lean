/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import ErdosProblems.Erdos228.CompactEndpoint
import ErdosProblems.Erdos228.GaussianWalk
import ErdosProblems.Erdos228.ProjectionWalk

/-!
# The Lovett--Meka partial-colouring principle

This file proves the finite-dimensional partial-colouring principle used by
the BBMST construction.  We use a projected Rademacher edge walk and a
deterministic exponential potential.  This is the discrete analogue of the
Gaussian edge walk: averaging over the next sign vector proves that at least
one next step simultaneously makes enough Euclidean progress and preserves
all exponential discrepancy potentials.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace Erdos228.EdgeWalk

open Erdos228.Discrepancy Erdos228.GaussianWalk Erdos228.ProjectionWalk

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Regard a finite real family as a vector in Euclidean space. -/
abbrev toWalk (v : I → ℝ) : WalkSpace I := WithLp.toLp 2 v

theorem l2Norm_sq (v : I → ℝ) :
    l2Norm v ^ 2 = ∑ i, v i ^ 2 := by
  rw [l2Norm, sq_sqrt]
  positivity

theorem norm_walkSpace_sq (v : WalkSpace I) :
    ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem l2Norm_eq_norm (v : I → ℝ) : l2Norm v = ‖toWalk v‖ := by
  rw [l2Norm, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

theorem dot_eq_inner (x v : I → ℝ) :
    dot x v = inner ℝ (toWalk v) (toWalk x) := by
  simp [dot, toWalk, EuclideanSpace.inner_eq_star_dotProduct,
    RCLike.star_def, dotProduct, mul_comm]

/-! ## Normalized constraints and active faces -/

/-- The unit normal associated to a nonzero discrepancy vector. -/
def normalizedConstraint (v : I → ℝ) : WalkSpace I :=
  (l2Norm v)⁻¹ • toWalk v

theorem norm_normalizedConstraint_le_one (v : I → ℝ) :
    ‖normalizedConstraint v‖ ≤ 1 := by
  by_cases hv : l2Norm v = 0
  · simp [normalizedConstraint, hv]
  · rw [normalizedConstraint, norm_smul, Real.norm_eq_abs,
      abs_inv, l2Norm_eq_norm]
    have hnorm : ‖toWalk v‖ ≠ 0 := by
      rw [← l2Norm_eq_norm]
      exact hv
    rw [abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

theorem norm_normalizedConstraint_eq_one {v : I → ℝ}
    (hv : 0 < l2Norm v) : ‖normalizedConstraint v‖ = 1 := by
  rw [normalizedConstraint, norm_smul, Real.norm_eq_abs, abs_inv,
    l2Norm_eq_norm]
  have hnorm : ‖toWalk v‖ ≠ 0 := by
    rw [← l2Norm_eq_norm]
    exact hv.ne'
  rw [abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

/-- The normalized discrepancy of `x` from the starting point. -/
def normalizedDiscrepancy (v : I → ℝ) (x₀ : I → ℝ)
    (x : WalkSpace I) : ℝ :=
  inner ℝ (normalizedConstraint v) (x - toWalk x₀)

theorem normalizedDiscrepancy_mul_l2Norm {v : I → ℝ}
    (hv : 0 < l2Norm v) (x₀ : I → ℝ) (x : WalkSpace I) :
    normalizedDiscrepancy v x₀ x * l2Norm v =
      dot (fun i ↦ x i - x₀ i) v := by
  calc
    normalizedDiscrepancy v x₀ x * l2Norm v =
        inner ℝ (toWalk v) (x - toWalk x₀) := by
      rw [normalizedDiscrepancy, normalizedConstraint, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hv.ne']
    _ = inner ℝ (toWalk v) (toWalk (fun i ↦ x i - x₀ i)) := by
      congr 1
    _ = dot (fun i ↦ x i - x₀ i) v :=
      (dot_eq_inner _ _).symm

/-- Coordinates within `delta` of a face of the cube. -/
def activeCoordinates [DecidableEq I] (delta : ℝ) (x : WalkSpace I) : Finset I :=
  Finset.univ.filter fun i ↦ 1 - delta ≤ |x i|

/-- Nonzero discrepancy rows within `delta` of their allowed boundary. -/
def activeDiscrepancies [DecidableEq J] (delta : ℝ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : Finset J :=
  Finset.univ.filter fun j ↦
    0 < l2Norm (v j) ∧ c j - delta ≤ |normalizedDiscrepancy (v j) x₀ x|

@[simp] theorem mem_activeCoordinates [DecidableEq I]
    {delta : ℝ} {x : WalkSpace I} {i : I} :
    i ∈ activeCoordinates delta x ↔ 1 - delta ≤ |x i| := by
  simp [activeCoordinates]

@[simp] theorem mem_activeDiscrepancies [DecidableEq J]
    {delta : ℝ} {v : J → I → ℝ} {x₀ : I → ℝ} {c : J → ℝ}
    {x : WalkSpace I} {j : J} :
    j ∈ activeDiscrepancies delta v x₀ c x ↔
      0 < l2Norm (v j) ∧
        c j - delta ≤ |normalizedDiscrepancy (v j) x₀ x| := by
  simp [activeDiscrepancies]

/-! ## One projected Rademacher step -/

/-- A product sample regarded as a Euclidean vector. -/
def sampleVector (omega : I → ℝ) : WalkSpace I := toWalk omega

/-- Moving the orthogonal projection from the random vector to the test
vector turns the projected functional into an ordinary weighted sum. -/
def projectedCoefficients (K : Submodule ℝ (WalkSpace I))
    (v : WalkSpace I) : I → ℝ := fun i ↦ K.starProjection v i

theorem inner_starProjection_sample_eq_sum
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) (omega : I → ℝ) :
    inner ℝ v (K.starProjection (sampleVector omega)) =
      ∑ i, projectedCoefficients K v i * omega i := by
  rw [real_inner_comm, K.inner_starProjection_left_eq_right, real_inner_comm]
  simp [PiLp.inner_apply, projectedCoefficients, sampleVector, toWalk, mul_comm]

theorem measurable_inner_starProjection_sample
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    Measurable (fun omega : I → ℝ ↦
      inner ℝ v (K.starProjection (sampleVector omega))) := by
  rw [show (fun omega : I → ℝ ↦
      inner ℝ v (K.starProjection (sampleVector omega))) =
      (fun omega ↦ ∑ i, projectedCoefficients K v i * omega i) by
    funext omega
    exact inner_starProjection_sample_eq_sum K v omega]
  fun_prop

theorem integrable_exp_inner_starProjection_sample
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) (t : ℝ) :
    Integrable (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampleVector omega))))
      (rademacherProduct I) := by
  rw [show (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampleVector omega)))) =
      (fun omega ↦ exp (t * ∑ i, projectedCoefficients K v i * omega i)) by
    funext omega
    rw [inner_starProjection_sample_eq_sum]]
  exact (hasSubgaussianMGF_weightedRademacherSum I
    (projectedCoefficients K v)).integrable_exp_mul t

theorem sum_projectedCoefficients_sq
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    ∑ i, projectedCoefficients K v i ^ 2 = ‖K.starProjection v‖ ^ 2 := by
  simpa [projectedCoefficients, EuclideanSpace.norm_sq_eq]

theorem sum_projectedCoefficients_sq_le
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    ∑ i, projectedCoefficients K v i ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [sum_projectedCoefficients_sq]
  nlinarith [norm_nonneg (K.starProjection v), norm_nonneg v,
    K.norm_starProjection_apply_le v]

/-- The projected-Rademacher one-step MGF estimate. -/
theorem integral_exp_inner_starProjection_sample_le
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) (t : ℝ) :
    ∫ omega : I → ℝ,
        exp (t * inner ℝ v (K.starProjection (sampleVector omega)))
      ∂(rademacherProduct I) ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  rw [show (fun omega : I → ℝ ↦
      exp (t * inner ℝ v (K.starProjection (sampleVector omega)))) =
      (fun omega ↦ exp (t * ∑ i, projectedCoefficients K v i * omega i)) by
    funext omega
    rw [inner_starProjection_sample_eq_sum]]
  have hmgf := (hasSubgaussianMGF_weightedRademacherSum I
    (projectedCoefficients K v)).mgf_le t
  rw [mgf] at hmgf
  let q : I → ℝ≥0 := fun i ↦ ⟨projectedCoefficients K v i ^ 2,
    sq_nonneg (projectedCoefficients K v i)⟩
  let variance : ℝ≥0 := ∑ i, q i
  change (∫ omega : I → ℝ,
      exp (t * ∑ i, projectedCoefficients K v i * omega i)
    ∂(rademacherProduct I)) ≤ exp ((variance : ℝ) * t ^ 2 / 2) at hmgf
  have hcoe : (variance : ℝ) = ∑ i, projectedCoefficients K v i ^ 2 := by
    calc
      (variance : ℝ) = ↑(∑ i, q i) := rfl
      _ = ∑ i, (q i : ℝ) := by
        simpa using NNReal.coe_sum Finset.univ q
      _ = ∑ i, projectedCoefficients K v i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
  calc
    ∫ omega : I → ℝ,
        exp (t * ∑ i, projectedCoefficients K v i * omega i)
      ∂(rademacherProduct I) ≤
        exp ((variance : ℝ) * t ^ 2 / 2) := hmgf
    _ ≤ exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
      apply exp_le_exp.mpr
      rw [hcoe]
      nlinarith [sum_projectedCoefficients_sq_le K v, sq_nonneg t]

theorem memLp_id_rademacherMeasure : MemLp id 2 rademacherMeasure := by
  exact memLp_of_bounded ae_mem_Icc_rademacherMeasure
    measurable_id.aestronglyMeasurable 2

theorem memLp_weighted_rademacher_coord (a : I → ℝ) (i : I) :
    MemLp (fun omega : I → ℝ ↦ a i * omega i) 2 (rademacherProduct I) := by
  exact (memLp_id_rademacherMeasure.comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : I ↦ rademacherMeasure) i)).const_mul (a i)

theorem integral_weighted_rademacher_sum (a : I → ℝ) :
    ∫ omega, (∑ i, a i * omega i) ∂rademacherProduct I = 0 := by
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul]
    have hmap : (rademacherProduct I).map (fun omega : I → ℝ ↦ omega i) =
        rademacherMeasure := by
      unfold rademacherProduct
      exact (measurePreserving_eval (μ := fun _ : I ↦ rademacherMeasure) i).map_eq
    rw [← integral_map (μ := rademacherProduct I) (f := fun x : ℝ ↦ x)
      (measurable_pi_apply i).aemeasurable measurable_id.aestronglyMeasurable, hmap]
    rw [integral_id_rademacherMeasure]
    ring
  · intro i hi
    exact (memLp_weighted_rademacher_coord a i).integrable (by norm_num)

theorem integral_inner_starProjection_sample_eq_zero
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    ∫ omega, inner ℝ v (K.starProjection (sampleVector omega))
      ∂rademacherProduct I = 0 := by
  simp_rw [inner_starProjection_sample_eq_sum]
  exact integral_weighted_rademacher_sum (projectedCoefficients K v)

theorem memLp_weighted_rademacher_sum (a : I → ℝ) :
    MemLp (fun omega : I → ℝ ↦ ∑ i, a i * omega i) 2
      (rademacherProduct I) := by
  have h := memLp_finsetSum Finset.univ
    (fun i _ ↦ memLp_weighted_rademacher_coord a i)
  simpa only [Finset.sum_apply] using h

theorem integral_sq_weighted_rademacher_sum (a : I → ℝ) :
    ∫ omega, (∑ i, a i * omega i) ^ 2 ∂rademacherProduct I = ∑ i, a i ^ 2 := by
  have hvar : Var[fun omega : I → ℝ ↦ ∑ i, a i * omega i;
      rademacherProduct I] = ∑ i, a i ^ 2 := by
    have hfun : (fun omega : I → ℝ ↦ ∑ i, a i * omega i) =
        ∑ i, fun omega : I → ℝ ↦ a i * omega i := by
      funext omega
      simp
    rw [hfun]
    unfold rademacherProduct
    rw [variance_sum_pi]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [variance_const_mul]
      have hid : Var[id; rademacherMeasure] = 1 := by
        rw [variance_eq_sub memLp_id_rademacherMeasure]
        simp only [Pi.pow_apply, id_eq, integral_id_rademacherMeasure, sub_zero]
        have hsq : (fun x : ℝ ↦ x ^ 2) =ᵐ[rademacherMeasure] fun _ ↦ 1 := by
          filter_upwards [ae_abs_eq_one_rademacherMeasure] with x hx
          rw [← sq_abs, hx]
          norm_num
        rw [integral_congr_ae hsq]
        simp
      change a i ^ 2 * Var[id; rademacherMeasure] = a i ^ 2
      rw [hid, mul_one]
    · intro i
      exact memLp_id_rademacherMeasure.const_mul (a i)
  rw [← hvar]
  rw [variance_of_integral_eq_zero]
  · exact (Finset.measurable_fun_sum Finset.univ fun i _ ↦
      measurable_const.mul (measurable_pi_apply i)).aemeasurable
  · exact integral_weighted_rademacher_sum a

theorem norm_sq_starProjection_eq_sum_inner_sq
    (K : Submodule ℝ (WalkSpace I)) (omega : I → ℝ) :
    ‖K.starProjection (sampleVector omega)‖ ^ 2 =
      ∑ k : Fin (Module.finrank ℝ K),
        inner ℝ ((stdOrthonormalBasis ℝ K k : K) : WalkSpace I)
          (sampleVector omega) ^ 2 := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let y : K := ⟨K.starProjection (sampleVector omega),
    K.starProjection_apply_mem (sampleVector omega)⟩
  change ‖y‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq y, ← b.sum_inner_mul_inner y y]
  apply Finset.sum_congr rfl
  intro k hk
  have hproj : inner ℝ (b k) y =
      inner ℝ ((b k : K) : WalkSpace I) (sampleVector omega) := by
    change inner ℝ (b k) (K.orthogonalProjectionOnto (sampleVector omega)) = _
    exact K.inner_orthogonalProjectionOnto_eq_of_mem_left (b k) (sampleVector omega)
  have hcomm : inner ℝ y (b k) = inner ℝ (b k) y :=
    (real_inner_comm y (b k)).symm
  rw [hcomm, hproj]
  ring

theorem integral_norm_sq_starProjection (K : Submodule ℝ (WalkSpace I)) :
    ∫ omega, ‖K.starProjection (sampleVector omega)‖ ^ 2
      ∂rademacherProduct I = (Module.finrank ℝ K : ℝ) := by
  simp_rw [norm_sq_starProjection_eq_sum_inner_sq K]
  rw [integral_finsetSum]
  · have hsquare (w : WalkSpace I) :
        ∫ omega, inner ℝ w (sampleVector omega) ^ 2 ∂rademacherProduct I = ‖w‖ ^ 2 := by
      simp_rw [show ∀ omega, inner ℝ w (sampleVector omega) =
          ∑ i, w i * omega i by
        intro omega
        simp [PiLp.inner_apply, sampleVector, toWalk, mul_comm]]
      rw [integral_sq_weighted_rademacher_sum]
      exact (EuclideanSpace.real_norm_sq_eq w).symm
    simp_rw [hsquare]
    calc
      (∑ k : Fin (Module.finrank ℝ K),
          ‖((stdOrthonormalBasis ℝ K k : K) : WalkSpace I)‖ ^ 2) =
          ∑ _k : Fin (Module.finrank ℝ K), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        change ‖stdOrthonormalBasis ℝ K k‖ ^ 2 = 1
        rw [OrthonormalBasis.norm_eq_one]
        norm_num
      _ = (Module.finrank ℝ K : ℝ) := by simp
  · intro k hk
    have hmem : MemLp
        (fun omega ↦ inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) (sampleVector omega))
        2 (rademacherProduct I) := by
      simp_rw [show ∀ omega, inner ℝ
          ((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) (sampleVector omega) =
          ∑ i, (((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) i) * omega i by
        intro omega
        simp [PiLp.inner_apply, sampleVector, toWalk, mul_comm]]
      exact memLp_weighted_rademacher_sum _
    exact hmem.integrable_sq

/-! ## The edge step and its exponential potential -/

variable [DecidableEq I] [DecidableEq J]

/-- The permitted-increment subspace at a state. -/
def edgeSubspace (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) : Submodule ℝ (WalkSpace I) :=
  tightIncrementSubspace (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x)

/-- One projected sign increment. -/
def edgeIncrement (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) : WalkSpace I :=
  (edgeSubspace delta v x₀ c x).starProjection (sampleVector omega)

/-- One edge-walk update. -/
def edgeStep (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) : WalkSpace I :=
  x + gamma • edgeIncrement delta v x₀ c x omega

theorem edgeIncrement_mem (delta : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    edgeIncrement delta v x₀ c x omega ∈ edgeSubspace delta v x₀ c x := by
  exact (edgeSubspace delta v x₀ c x).starProjection_apply_mem _

theorem edgeIncrement_apply_eq_zero_of_active
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    {i : I} (hi : i ∈ activeCoordinates delta x) :
    edgeIncrement delta v x₀ c x omega i = 0 := by
  exact (mem_tightIncrementSubspace_iff
    (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x) _).1
      (edgeIncrement_mem delta v x₀ c x omega) |>.1 i hi

theorem inner_edgeIncrement_eq_zero_of_active
    (delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ)
    {j : J} (hj : j ∈ activeDiscrepancies delta v x₀ c x) :
    inner ℝ (normalizedConstraint (v j))
      (edgeIncrement delta v x₀ c x omega) = 0 := by
  exact (mem_tightIncrementSubspace_iff
    (fun j ↦ normalizedConstraint (v j))
    (activeCoordinates delta x) (activeDiscrepancies delta v x₀ c x) _).1
      (edgeIncrement_mem delta v x₀ c x omega) |>.2 j hj

theorem norm_edgeIncrement_le (delta : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    ‖edgeIncrement delta v x₀ c x omega‖ ≤ ‖sampleVector omega‖ := by
  exact (edgeSubspace delta v x₀ c x).norm_starProjection_apply_le _

/-- Every point in the support of the Rademacher product has squared
Euclidean norm equal to the ambient dimension. -/
theorem norm_sampleVector_sq_of_signs {omega : I → ℝ}
    (homega : ∀ i, |omega i| = 1) :
    ‖sampleVector omega‖ ^ 2 = Fintype.card I := by
  rw [norm_walkSpace_sq]
  simp only [sampleVector, toWalk, PiLp.toLp_apply]
  calc
    ∑ i, omega i ^ 2 = ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      nlinarith [sq_abs (omega i), homega i]
    _ = Fintype.card I := by simp

theorem norm_sampleVector_le_sqrt_card {omega : I → ℝ}
    (homega : ∀ i, |omega i| = 1) :
    ‖sampleVector omega‖ ≤ sqrt (Fintype.card I) := by
  have hsq := norm_sampleVector_sq_of_signs homega
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

theorem normalizedDiscrepancy_edgeStep
    (delta gamma : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) (j : J) :
    normalizedDiscrepancy (v j) x₀ (edgeStep delta gamma v x₀ c x omega) =
      normalizedDiscrepancy (v j) x₀ x +
        gamma * inner ℝ (normalizedConstraint (v j))
          (edgeIncrement delta v x₀ c x omega) := by
  rw [normalizedDiscrepancy, normalizedDiscrepancy, edgeStep]
  have hsub : x + gamma • edgeIncrement delta v x₀ c x omega - toWalk x₀ =
      (x - toWalk x₀) + gamma • edgeIncrement delta v x₀ c x omega := by
    abel
  rw [hsub, inner_add_right, inner_smul_right]

/-- The exponential weight from the Lovett--Meka entropy budget. -/
def entropyWeight (a : ℝ) : ℝ := exp (-a ^ 2 / 16)

/-- One side of the compensated exponential potential for a row. -/
def signedRowPotential (sigma gamma : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  entropyWeight a *
    exp (sigma * (a / 5) * y - (a / 5) ^ 2 * gamma ^ 2 * t / 2)

/-- The two-sided row potential. -/
def rowPotential (gamma : ℝ) (t : ℕ) (a y : ℝ) : ℝ :=
  signedRowPotential 1 gamma t a y + signedRowPotential (-1) gamma t a y

/-- Sum of the row potentials. -/
def discrepancyPotential (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : ℝ :=
  ∑ j, rowPotential gamma t (c j) (normalizedDiscrepancy (v j) x₀ x)

/-- Euclidean progress minus five times the exponential discrepancy
potential.  The factor five is the total variance budget of the walk. -/
def edgeScore (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : ℝ :=
  ‖x‖ ^ 2 - 5 * discrepancyPotential gamma t v x₀ c x

theorem discrepancyPotential_zero (gamma : ℝ) (v : J → I → ℝ)
    (x₀ : I → ℝ) (c : J → ℝ) :
    discrepancyPotential gamma 0 v x₀ c (toWalk x₀) =
      2 * ∑ j, entropyWeight (c j) := by
  simp [discrepancyPotential, rowPotential, signedRowPotential,
    normalizedDiscrepancy, entropyWeight, Finset.mul_sum, two_mul]

theorem signedRowPotential_nonneg (sigma gamma : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ signedRowPotential sigma gamma t a y := by
  exact mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))

theorem rowPotential_nonneg (gamma : ℝ) (t : ℕ) (a y : ℝ) :
    0 ≤ rowPotential gamma t a y :=
  add_nonneg (signedRowPotential_nonneg _ _ _ _ _)
    (signedRowPotential_nonneg _ _ _ _ _)

theorem discrepancyPotential_nonneg (gamma : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) : 0 ≤ discrepancyPotential gamma t v x₀ c x := by
  exact Finset.sum_nonneg fun j hj ↦ rowPotential_nonneg _ _ _ _

theorem integral_signedRowPotential_step_le
    (sigma gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) (j : J) (hsigma : sigma ^ 2 = 1) :
    ∫ omega,
        signedRowPotential sigma gamma (t + 1) (c j)
          (normalizedDiscrepancy (v j) x₀
            (edgeStep delta gamma v x₀ c x omega))
      ∂rademacherProduct I ≤
        signedRowPotential sigma gamma t (c j)
          (normalizedDiscrepancy (v j) x₀ x) := by
  let S := edgeSubspace delta v x₀ c x
  let w := normalizedConstraint (v j)
  let a := c j / 5
  let y := normalizedDiscrepancy (v j) x₀ x
  let q := sigma * a * gamma
  let base := sigma * a * y - a ^ 2 * gamma ^ 2 * t / 2 -
    a ^ 2 * gamma ^ 2 / 2
  let B := entropyWeight (c j) * exp base
  have hrewrite (omega : I → ℝ) :
      signedRowPotential sigma gamma (t + 1) (c j)
          (normalizedDiscrepancy (v j) x₀
            (edgeStep delta gamma v x₀ c x omega)) =
        B * exp (q * inner ℝ w (S.starProjection (sampleVector omega))) := by
    rw [normalizedDiscrepancy_edgeStep]
    unfold signedRowPotential
    change entropyWeight (c j) * exp _ =
      (entropyWeight (c j) * exp base) * exp _
    calc
      entropyWeight (c j) * exp _ =
          entropyWeight (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (sampleVector omega)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, a, y, q, S, w, edgeIncrement]
        push_cast
        ring
      _ = (entropyWeight (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (sampleVector omega))) := by
        ring
  simp_rw [hrewrite]
  rw [integral_const_mul]
  have hB : 0 ≤ B := mul_nonneg (le_of_lt (exp_pos _)) (le_of_lt (exp_pos _))
  calc
    B * ∫ omega, exp (q * inner ℝ w (S.starProjection (sampleVector omega)))
        ∂rademacherProduct I ≤ B * exp (q ^ 2 * ‖w‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left
        (integral_exp_inner_starProjection_sample_le S w q) hB
    _ ≤ B * exp (q ^ 2 / 2) := by
      gcongr
      have hwSq : ‖w‖ ^ 2 ≤ 1 := by
        nlinarith [mul_self_le_mul_self (norm_nonneg w)
          (norm_normalizedConstraint_le_one (v j))]
      nlinarith [hwSq, sq_nonneg q]
    _ = signedRowPotential sigma gamma t (c j) y := by
      dsimp only [B, base, q, a]
      unfold signedRowPotential
      rw [mul_assoc, ← exp_add]
      congr 2
      push_cast
      nlinarith

theorem integrable_signedRowPotential_step
    (sigma gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) (j : J) :
    Integrable (fun omega ↦
      signedRowPotential sigma gamma (t + 1) (c j)
        (normalizedDiscrepancy (v j) x₀
          (edgeStep delta gamma v x₀ c x omega)))
      (rademacherProduct I) := by
  let S := edgeSubspace delta v x₀ c x
  let w := normalizedConstraint (v j)
  let q := sigma * (c j / 5) * gamma
  let base := sigma * (c j / 5) * normalizedDiscrepancy (v j) x₀ x -
    (c j / 5) ^ 2 * gamma ^ 2 * t / 2 -
    (c j / 5) ^ 2 * gamma ^ 2 / 2
  let B := entropyWeight (c j) * exp base
  have heq : (fun omega ↦
      signedRowPotential sigma gamma (t + 1) (c j)
        (normalizedDiscrepancy (v j) x₀
          (edgeStep delta gamma v x₀ c x omega))) =
      (fun omega ↦ B * exp (q * inner ℝ w
        (S.starProjection (sampleVector omega)))) := by
    funext omega
    rw [normalizedDiscrepancy_edgeStep]
    unfold signedRowPotential
    change entropyWeight (c j) * exp _ =
      (entropyWeight (c j) * exp base) * exp _
    calc
      entropyWeight (c j) * exp _ =
          entropyWeight (c j) *
            (exp base * exp (q * inner ℝ w
              (S.starProjection (sampleVector omega)))) := by
        congr 1
        rw [← exp_add]
        congr 1
        dsimp only [base, q, S, w, edgeIncrement]
        push_cast
        ring
      _ = (entropyWeight (c j) * exp base) *
          exp (q * inner ℝ w (S.starProjection (sampleVector omega))) := by
        ring
  rw [heq]
  exact (integrable_exp_inner_starProjection_sample S w q).const_mul B

theorem integral_rowPotential_step_le
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) (j : J) :
    ∫ omega,
        rowPotential gamma (t + 1) (c j)
          (normalizedDiscrepancy (v j) x₀
            (edgeStep delta gamma v x₀ c x omega))
      ∂rademacherProduct I ≤
        rowPotential gamma t (c j)
          (normalizedDiscrepancy (v j) x₀ x) := by
  unfold rowPotential
  rw [integral_add]
  · exact add_le_add
      (integral_signedRowPotential_step_le 1 gamma delta t v x₀ c x j (by norm_num))
      (integral_signedRowPotential_step_le (-1) gamma delta t v x₀ c x j (by norm_num))
  · exact integrable_signedRowPotential_step 1 gamma delta t v x₀ c x j
  · exact integrable_signedRowPotential_step (-1) gamma delta t v x₀ c x j

theorem integrable_discrepancyPotential_step
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    Integrable (fun omega ↦ discrepancyPotential gamma (t + 1) v x₀ c
      (edgeStep delta gamma v x₀ c x omega)) (rademacherProduct I) := by
  unfold discrepancyPotential
  exact integrable_finset_sum Finset.univ fun j hj ↦
    integrable_signedRowPotential_step 1 gamma delta t v x₀ c x j |>.add
      (integrable_signedRowPotential_step (-1) gamma delta t v x₀ c x j)

theorem integral_discrepancyPotential_step_le
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    ∫ omega, discrepancyPotential gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x omega)
      ∂rademacherProduct I ≤ discrepancyPotential gamma t v x₀ c x := by
  unfold discrepancyPotential
  rw [integral_finsetSum]
  exact Finset.sum_le_sum fun j hj ↦
    integral_rowPotential_step_le gamma delta t v x₀ c x j
  intro j hj
  exact (integrable_signedRowPotential_step 1 gamma delta t v x₀ c x j).add
    (integrable_signedRowPotential_step (-1) gamma delta t v x₀ c x j)

theorem integrable_inner_starProjection_sample
    (K : Submodule ℝ (WalkSpace I)) (v : WalkSpace I) :
    Integrable (fun omega ↦ inner ℝ v (K.starProjection (sampleVector omega)))
      (rademacherProduct I) := by
  simp_rw [inner_starProjection_sample_eq_sum]
  exact (memLp_weighted_rademacher_sum (projectedCoefficients K v)).integrable
    (by norm_num)

theorem integrable_norm_sq_starProjection
    (K : Submodule ℝ (WalkSpace I)) :
    Integrable (fun omega ↦ ‖K.starProjection (sampleVector omega)‖ ^ 2)
      (rademacherProduct I) := by
  simp_rw [norm_sq_starProjection_eq_sum_inner_sq K]
  exact integrable_finset_sum Finset.univ fun k hk ↦
    ((memLp_weighted_rademacher_sum
      (fun i ↦ (((stdOrthonormalBasis ℝ K k : K) : WalkSpace I) i))).integrable_sq.congr
        (Filter.Eventually.of_forall fun omega ↦ by
          congr 1
          simp [PiLp.inner_apply, sampleVector, toWalk, mul_comm]))

theorem norm_edgeStep_sq
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) (omega : I → ℝ) :
    ‖edgeStep delta gamma v x₀ c x omega‖ ^ 2 = ‖x‖ ^ 2 +
      2 * gamma * inner ℝ x (edgeIncrement delta v x₀ c x omega) +
      gamma ^ 2 * ‖edgeIncrement delta v x₀ c x omega‖ ^ 2 := by
  rw [edgeStep, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [mul_pow, sq_abs]
  ring

theorem integral_norm_edgeStep_sq
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) :
    ∫ omega, ‖edgeStep delta gamma v x₀ c x omega‖ ^ 2
      ∂rademacherProduct I = ‖x‖ ^ 2 +
        gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) := by
  simp_rw [norm_edgeStep_sq]
  have hconst : Integrable (fun _omega : I → ℝ ↦ ‖x‖ ^ 2)
      (rademacherProduct I) := integrable_const _
  have hlinear : Integrable (fun omega : I → ℝ ↦
      2 * gamma * inner ℝ x (edgeIncrement delta v x₀ c x omega))
      (rademacherProduct I) :=
    (integrable_inner_starProjection_sample
      (edgeSubspace delta v x₀ c x) x).const_mul (2 * gamma)
  have hquadratic : Integrable (fun omega : I → ℝ ↦
      gamma ^ 2 * ‖edgeIncrement delta v x₀ c x omega‖ ^ 2)
      (rademacherProduct I) :=
    (integrable_norm_sq_starProjection
      (edgeSubspace delta v x₀ c x)).const_mul (gamma ^ 2)
  have hzero : ∫ omega,
      inner ℝ x (edgeIncrement delta v x₀ c x omega)
        ∂rademacherProduct I = 0 := by
    exact integral_inner_starProjection_sample_eq_zero
      (edgeSubspace delta v x₀ c x) x
  have hsquare : ∫ omega,
      ‖edgeIncrement delta v x₀ c x omega‖ ^ 2
        ∂rademacherProduct I =
        (Module.finrank ℝ (edgeSubspace delta v x₀ c x) : ℝ) := by
    exact integral_norm_sq_starProjection (edgeSubspace delta v x₀ c x)
  have hmeasure : (rademacherProduct I).real Set.univ = 1 := by
    rw [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [integral_add]
  · rw [integral_add]
    · rw [integral_const, integral_const_mul,
    hzero, mul_zero, integral_const_mul, hsquare]
      rw [hmeasure]
      simp only [mul_one, add_zero]
      ring
    · exact hconst
    · exact hlinear
  · exact hconst.add hlinear
  · exact hquadratic

theorem integrable_norm_edgeStep_sq
    (gamma delta : ℝ) (v : J → I → ℝ) (x₀ : I → ℝ)
    (c : J → ℝ) (x : WalkSpace I) :
    Integrable (fun omega ↦ ‖edgeStep delta gamma v x₀ c x omega‖ ^ 2)
      (rademacherProduct I) := by
  simp_rw [norm_edgeStep_sq]
  exact (integrable_const _).add
    ((integrable_inner_starProjection_sample
      (edgeSubspace delta v x₀ c x) x).const_mul (2 * gamma)) |>.add
        ((integrable_norm_sq_starProjection
          (edgeSubspace delta v x₀ c x)).const_mul (gamma ^ 2))

theorem integrable_edgeScore_step
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    Integrable (fun omega ↦ edgeScore gamma (t + 1) v x₀ c
      (edgeStep delta gamma v x₀ c x omega)) (rademacherProduct I) := by
  unfold edgeScore
  exact (integrable_norm_edgeStep_sq gamma delta v x₀ c x).sub
    ((integrable_discrepancyPotential_step gamma delta t v x₀ c x).const_mul 5)

theorem integral_edgeScore_step_ge
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    edgeScore gamma t v x₀ c x +
        gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) ≤
      ∫ omega, edgeScore gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x omega) ∂rademacherProduct I := by
  rw [edgeScore]
  simp_rw [edgeScore]
  rw [integral_sub, integral_const_mul, integral_norm_edgeStep_sq]
  · have hp := integral_discrepancyPotential_step_le gamma delta t v x₀ c x
    linarith
  · exact integrable_norm_edgeStep_sq gamma delta v x₀ c x
  · exact (integrable_discrepancyPotential_step gamma delta t v x₀ c x).const_mul 5

theorem measure_not_signs_eq_zero :
    rademacherProduct I {omega | ¬ ∀ i, |omega i| = 1} = 0 := by
  rw [← ae_iff]
  simpa only [Set.mem_setOf_eq, not_not] using
    (ae_forall_abs_eq_one_rademacherProduct I)

/-- At each state an actual sign vector realizes at least the average
increase in the score. -/
theorem exists_sign_edgeScore_step
    (gamma delta : ℝ) (t : ℕ)
    (v : J → I → ℝ) (x₀ : I → ℝ) (c : J → ℝ)
    (x : WalkSpace I) :
    ∃ omega : I → ℝ, (∀ i, |omega i| = 1) ∧
      edgeScore gamma t v x₀ c x +
          gamma ^ 2 * Module.finrank ℝ (edgeSubspace delta v x₀ c x) ≤
        edgeScore gamma (t + 1) v x₀ c
          (edgeStep delta gamma v x₀ c x omega) := by
  let N : Set (I → ℝ) := {omega | ¬ ∀ i, |omega i| = 1}
  obtain ⟨omega, homegaN, homega⟩ :=
    exists_notMem_null_integral_le
      (μ := rademacherProduct I)
      (f := fun omega ↦ edgeScore gamma (t + 1) v x₀ c
        (edgeStep delta gamma v x₀ c x omega))
      (integrable_edgeScore_step gamma delta t v x₀ c x)
      (show rademacherProduct I N = 0 by exact measure_not_signs_eq_zero)
  refine ⟨omega, ?_, (integral_edgeScore_step_ge gamma delta t v x₀ c x).trans homega⟩
  simpa only [N, Set.mem_setOf_eq, not_not] using homegaN

end Erdos228.EdgeWalk

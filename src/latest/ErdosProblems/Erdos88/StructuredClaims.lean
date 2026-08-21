/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.GaussianNonuniform
import ErdosProblems.Erdos88.StructuredClaim122Conditioned
import ErdosProblems.Erdos88.StructuredMixture
import ErdosProblems.Erdos88.StructuredTypical
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A common structured witness for Claims 12.1 and 12.2

The product-slice estimate and the shift-moment estimate must be applied to
the same small-RLCD bucket decomposition.  This module packages that common
witness, avoiding an invalid combination of two independently chosen
existential decompositions.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius Topology

namespace Erdos88.GaussianQuadratic

open BooleanSlices

attribute [local instance] Classical.propDecidable

/-- On the central frequency range, a Rademacher linear form has the
Gaussian characteristic-function envelope dictated by its squared
Euclidean coefficient norm. -/
lemma norm_finCharFun_rademacherLinear_le_gaussian
    {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    (hsmall : ∀ i, |t * a i| ≤ Real.pi / 2) :
    ‖Fourier.finCharFun (Fin n → Bool)
        (fun xi ↦ ∑ i, a i * Fourier.rademacherSign (xi i)) t‖ ≤
      Real.exp (-(vectorSqNorm a / Real.pi ^ 2) * t ^ 2) := by
  rw [Fourier.norm_finCharFun_rademacher_linear]
  calc
    (∏ i, |Real.cos (t * a i)|) ≤
        ∏ i, Real.exp (-((t * a i) / Real.pi) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact abs_nonneg _
      · intro i hi
        exact Fourier.abs_cos_le_exp_neg_sq_div_pi_sq (hsmall i)
    _ = Real.exp (∑ i, -((t * a i) / Real.pi) ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(vectorSqNorm a / Real.pi ^ 2) * t ^ 2) := by
      congr 1
      unfold vectorSqNorm
      rw [Finset.sum_neg_distrib]
      calc
        -∑ i, (t * a i / Real.pi) ^ 2 =
            -∑ i, (t ^ 2 / Real.pi ^ 2) * a i ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          field_simp [ne_of_gt Real.pi_pos]
        _ = -((∑ i, a i ^ 2) / Real.pi ^ 2) * t ^ 2 := by
          rw [← Finset.mul_sum]
          ring

/-- A direct Esseen bound for a finite Rademacher linear form.  This is the
Fourier substitute for the Berry--Esseen interval estimate used as (12.7)
in the source: at any radius dominating the largest coefficient, interval
mass is at most a constant times `eps / ‖a‖₂`. -/
theorem smallBall_rademacherLinear_le
    {n : ℕ} (a : Fin n → ℝ) {eps : ℝ}
    (heps : 0 < eps) (hvar : 0 < vectorSqNorm a)
    (hscale : ∀ i, 4 * |a i| ≤ eps * Real.pi) (x : ℝ) :
    Esseen.smallBall
        (Esseen.finiteUniformLaw (Fin n → Bool)
          (fun xi ↦ ∑ i, a i * Fourier.rademacherSign (xi i)))
        eps x ≤
      2 * eps * Real.sqrt
        (Real.pi / (vectorSqNorm a / Real.pi ^ 2)) := by
  let mu := Esseen.finiteUniformLaw (Fin n → Bool)
    (fun xi ↦ ∑ i, a i * Fourier.rademacherSign (xi i))
  let beta := vectorSqNorm a / Real.pi ^ 2
  have hbeta : 0 < beta := div_pos hvar (sq_pos_of_pos Real.pi_pos)
  have hends : -(2 / eps) ≤ 2 / eps := by
    have htwo : 0 < 2 / eps := div_pos (by norm_num) heps
    linarith
  have hchar : ∀ t ∈ Set.Icc (-(2 / eps)) (2 / eps),
      ‖MeasureTheory.charFun mu t‖ ≤ Real.exp (-beta * t ^ 2) := by
    intro t ht
    dsimp only [mu]
    rw [Esseen.charFun_finiteUniformLaw]
    apply norm_finCharFun_rademacherLinear_le_gaussian
    intro i
    have htAbs : |t| ≤ 2 / eps := by
      rw [abs_le]
      exact ht
    rw [abs_mul]
    calc
      |t| * |a i| ≤ (2 / eps) * |a i| :=
        mul_le_mul_of_nonneg_right htAbs (abs_nonneg _)
      _ ≤ Real.pi / 2 := by
        rw [show (2 / eps) * |a i| = (2 * |a i|) / eps by ring]
        apply (div_le_iff₀ heps).2
        nlinarith [hscale i]
  have hcharInt :
      (∫ t in -(2 / eps)..(2 / eps), ‖MeasureTheory.charFun mu t‖) ≤
        ∫ t in -(2 / eps)..(2 / eps), Real.exp (-beta * t ^ 2) := by
    apply intervalIntegral.integral_mono_on hends
      ((continuous_norm.comp MeasureTheory.continuous_charFun).intervalIntegrable _ _)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)
    exact hchar
  have hgaussInt :
      (∫ t in -(2 / eps)..(2 / eps), Real.exp (-beta * t ^ 2)) ≤
        ∫ t : ℝ, Real.exp (-beta * t ^ 2) := by
    rw [intervalIntegral.integral_of_le hends]
    exact MeasureTheory.integral_mono_measure
      MeasureTheory.Measure.restrict_le_self
      (Filter.Eventually.of_forall fun t ↦ (Real.exp_pos _).le)
      (integrable_exp_neg_mul_sq hbeta)
  have hesseen := Esseen.esseen_4_7 mu heps x
  calc
    Esseen.smallBall mu eps x ≤
        2 * eps *
          (∫ t in -(2 / eps)..(2 / eps), ‖MeasureTheory.charFun mu t‖) :=
      hesseen
    _ ≤ 2 * eps *
        (∫ t in -(2 / eps)..(2 / eps), Real.exp (-beta * t ^ 2)) := by
      gcongr
    _ ≤ 2 * eps * (∫ t : ℝ, Real.exp (-beta * t ^ 2)) := by
      gcongr
    _ = 2 * eps * Real.sqrt
        (Real.pi / (vectorSqNorm a / Real.pi ^ 2)) := by
      rw [integral_gaussian]

/-- The bucket projection of an arbitrary subset depends only on its bucket
count vector. -/
lemma delta_signOfSet_eq_productSliceDelta_bucketCounts
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (S : Finset (Fin n)) :
    Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose)
        (signOfSet S) =
      productSliceDelta P hbucket.choose
        (fun j ↦ (bucketCounts P S j).val) := by
  let T : ProductSlicePoint P (fun j ↦ (bucketCounts P S j).val) :=
    ⟨S, by
      rw [mem_productBooleanSlice]
      intro j
      rfl⟩
  exact delta_signOfSet_eq_productSliceDelta P hbucket
    (fun j ↦ (bucketCounts P S j).val) T

/-- The linear shift associated with a bucket-count vector. -/
noncomputable def countVectorLinearShift
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) (ell : BucketCountVector P) : ℝ :=
  (1 / 2 : ℝ) *
    (y ⬝ᵥ productSliceDelta P hbucket.choose (fun j ↦ (ell j).val))

/-- Coefficients of the independent Rademacher linear form represented by
the first count-vector shift. -/
noncomputable def countVectorLinearCoefficient
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ (1 / 2 : ℝ) *
    (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) i

lemma countVectorLinearShift_bucketCounts_eq
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) (S : Finset (Fin n)) :
  countVectorLinearShift P hbucket y (bucketCounts P S) =
      ∑ i, countVectorLinearCoefficient P hbucket y i * signOfSet S i := by
  rw [countVectorLinearShift,
    ← delta_signOfSet_eq_productSliceDelta_bucketCounts]
  rw [bucketShiftLinear_eq]
  unfold countVectorLinearCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma vectorSqNorm_countVectorLinearCoefficient
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) :
    vectorSqNorm (countVectorLinearCoefficient P hbucket y) =
      (1 / 4 : ℝ) * vectorSqNorm
        (bucketProjectionMatrix P.bucket hbucket.choose *ᵥ y) := by
  unfold vectorSqNorm countVectorLinearCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Positive graph edge density supplies the cubic squared norm of the
Rademacher coefficients in the first count-vector shift. -/
lemma countVectorLinearCoefficient_graph_sqNorm_lower
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
    (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3) ≤
      vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c)) := by
  let y := GraphQuadratic.graphEffectiveLinear G c
  have hsumc : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ ↦ hc0 i
  have hsum : A * (n : ℝ) ^ 2 ≤ ∑ i, y i := by
    rw [GraphQuadratic.sum_graphEffectiveLinear]
    exact hedge.trans (by linarith)
  rw [vectorSqNorm_countVectorLinearCoefficient]
  exact mul_le_mul_of_nonneg_left
    (sum_sq_bucketProjectionMatrix_mulVec_lower hn P hbucket y hA hsum)
    (by norm_num)

/-- The graph-effective first-shift coefficients are pointwise at most half
the natural `(H+1)n` graph scale. -/
lemma countVectorLinearCoefficient_graph_abs_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H : ℝ) (hH : 0 ≤ H)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (i : Fin n) :
    |countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c) i| ≤
      ((H + 1) * (n : ℝ)) / 2 := by
  let y := GraphQuadratic.graphEffectiveLinear G c
  let scale := (H + 1) * (n : ℝ)
  have hscale : 0 ≤ scale := mul_nonneg (by linarith) (by positivity)
  have hy0 : ∀ j, 0 ≤ y j := by
    intro j
    exact add_nonneg (hc0 j) (div_nonneg (by positivity) (by norm_num))
  have hyB : ∀ j, y j ≤ scale := by
    intro j
    have hdegNat : G.degree j ≤ n :=
      Nat.le_of_lt (by simpa using G.degree_lt_card_verts j)
    have hdeg : (G.degree j : ℝ) ≤ n := by exact_mod_cast hdegNat
    dsimp only [y, scale, GraphQuadratic.graphEffectiveLinear]
    nlinarith [hcH j]
  have hQ := abs_bucketProjectionMatrix_mulVec_le_of_nonneg
    P hbucket y hscale hy0 hyB i
  unfold countVectorLinearCoefficient
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  dsimp only [scale] at hQ
  nlinarith

/-- Exact identification of an interval event for the count-vector linear
shift with the corresponding event for an independent Rademacher linear
form. -/
lemma countVectorMass_linearShift_interval_eq_finProbability
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) (eps x : ℝ) :
    countVectorMass P (fun ell ↦
        |countVectorLinearShift P hbucket y ell - x| ≤ eps) =
      Fourier.finProbability (Fin n → Bool) (fun xi ↦
        |∑ i, countVectorLinearCoefficient P hbucket y i *
            Fourier.rademacherSign (xi i) - x| ≤ eps) := by
  rw [countVectorMass_eq_uniformProbability]
  let g : (Fin n → ℝ) → ℝ := fun z ↦
    if |∑ i, countVectorLinearCoefficient P hbucket y i * z i - x| ≤ eps
    then 1 else 0
  have hcube := rademacherExpectation_eq_uniformFinset (n := n) g
  have hsign (xi : Fin n → Bool) :
      (fun i ↦ Fourier.rademacherSign (xi i)) =
        (fun i ↦ Invariance.rademacherSign (xi i)) := by
    funext i
    cases xi i <;> rfl
  unfold Invariance.rademacherExpectation Invariance.finiteExpectation at hcube
  unfold BooleanSlices.uniformExpectation at hcube
  rw [Fintype.expect_eq_sum_div_card] at hcube
  dsimp only [g] at hcube
  have hsignVal (xi : Fin n → Bool) (i : Fin n) :
      Fourier.rademacherSign (xi i) =
        Invariance.rademacherSign (xi i) := congrFun (hsign xi) i
  simp_rw [← hsignVal] at hcube
  simp_rw [← countVectorLinearShift_bucketCounts_eq P hbucket y] at hcube
  simpa only [Concentration.uniformProbability, Fourier.finProbability,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one] using hcube.symm

/-- Source-shaped interval estimate (12.7) for the first count-vector
shift.  It is proved directly from Esseen and the product-cosine formula. -/
theorem countVectorMass_linearShift_interval_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) {eps : ℝ}
    (heps : 0 < eps)
    (hvar : 0 < vectorSqNorm (countVectorLinearCoefficient P hbucket y))
    (hscale : ∀ i,
      4 * |countVectorLinearCoefficient P hbucket y i| ≤ eps * Real.pi)
    (x : ℝ) :
    countVectorMass P (fun ell ↦
        |countVectorLinearShift P hbucket y ell - x| ≤ eps) ≤
      2 * eps * Real.sqrt
        (Real.pi /
          (vectorSqNorm (countVectorLinearCoefficient P hbucket y) /
            Real.pi ^ 2)) := by
  rw [countVectorMass_linearShift_interval_eq_finProbability]
  rw [← Esseen.smallBall_finiteUniformLaw]
  exact smallBall_rademacherLinear_le
    (countVectorLinearCoefficient P hbucket y) heps hvar hscale x

/-- The source interval form of (12.7).  The independent Rademacher
representation gives a bound proportional to the interval length. -/
theorem countVectorMass_linearShift_Icc_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) {a b : ℝ} (hab : a < b)
    (hvar : 0 < vectorSqNorm (countVectorLinearCoefficient P hbucket y))
    (hscale : ∀ i,
      8 * |countVectorLinearCoefficient P hbucket y i| ≤
        (b - a) * Real.pi) :
    countVectorMass P (fun ell ↦
        a ≤ countVectorLinearShift P hbucket y ell ∧
          countVectorLinearShift P hbucket y ell ≤ b) ≤
      (b - a) * Real.sqrt
        (Real.pi /
          (vectorSqNorm (countVectorLinearCoefficient P hbucket y) /
            Real.pi ^ 2)) := by
  let eps := (b - a) / 2
  let x := (a + b) / 2
  have heps : 0 < eps := by
    dsimp only [eps]
    linarith
  have hscale' : ∀ i,
      4 * |countVectorLinearCoefficient P hbucket y i| ≤ eps * Real.pi := by
    intro i
    calc
      4 * |countVectorLinearCoefficient P hbucket y i| =
          (1 / 2 : ℝ) *
            (8 * |countVectorLinearCoefficient P hbucket y i|) := by ring
      _ ≤ (1 / 2 : ℝ) * ((b - a) * Real.pi) :=
        mul_le_mul_of_nonneg_left (hscale i) (by norm_num)
      _ = eps * Real.pi := by
        dsimp only [eps]
        ring
  have hevent :
      (fun ell ↦ a ≤ countVectorLinearShift P hbucket y ell ∧
          countVectorLinearShift P hbucket y ell ≤ b) =
        (fun ell ↦
          |countVectorLinearShift P hbucket y ell - x| ≤ eps) := by
    funext ell
    apply propext
    rw [abs_le]
    dsimp only [x, eps]
    constructor
    · rintro ⟨hleft, hright⟩
      constructor <;> linarith
    · rintro ⟨hleft, hright⟩
      constructor <;> linarith
  rw [hevent]
  have hbound := countVectorMass_linearShift_interval_le
    P hbucket y heps hvar hscale' x
  convert hbound using 1
  all_goals dsimp only [eps]; ring

/-- Graph-effective form of (12.7).  Positive edge density gives the
nondegenerate coefficient norm, while the natural graph scale gives the
central-frequency hypothesis. -/
theorem countVectorMass_graphLinearShift_Icc_le
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A : ℝ) (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    {a b : ℝ} (hab : a < b)
    (hwidth : 4 * ((H + 1) * (n : ℝ)) ≤ (b - a) * Real.pi) :
    countVectorMass P (fun ell ↦
        a ≤ countVectorLinearShift P hbucket
              (GraphQuadratic.graphEffectiveLinear G c) ell ∧
          countVectorLinearShift P hbucket
              (GraphQuadratic.graphEffectiveLinear G c) ell ≤ b) ≤
      (b - a) * Real.sqrt
        (Real.pi /
          (vectorSqNorm (countVectorLinearCoefficient P hbucket
              (GraphQuadratic.graphEffectiveLinear G c)) /
            Real.pi ^ 2)) := by
  have hlower := countVectorLinearCoefficient_graph_sqNorm_lower
    hn P hbucket G c hA.le hc0 hedge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpositive : 0 < (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3) := by
    positivity
  have hvar : 0 < vectorSqNorm (countVectorLinearCoefficient P hbucket
      (GraphQuadratic.graphEffectiveLinear G c)) := hpositive.trans_le hlower
  apply countVectorMass_linearShift_Icc_le P hbucket
    (GraphQuadratic.graphEffectiveLinear G c) hab hvar
  intro i
  have hcoeff := countVectorLinearCoefficient_graph_abs_le
    P hbucket G c H hH hc0 hcH i
  linarith

/-- The preceding graph interval estimate with its cubic density lower
bound substituted explicitly into the denominator. -/
theorem countVectorMass_graphLinearShift_Icc_le_density
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A : ℝ) (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    {a b : ℝ} (hab : a < b)
    (hwidth : 4 * ((H + 1) * (n : ℝ)) ≤ (b - a) * Real.pi) :
    countVectorMass P (fun ell ↦
        a ≤ countVectorLinearShift P hbucket
              (GraphQuadratic.graphEffectiveLinear G c) ell ∧
          countVectorLinearShift P hbucket
              (GraphQuadratic.graphEffectiveLinear G c) ell ≤ b) ≤
      (b - a) * Real.sqrt
        (Real.pi /
          (((1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3)) /
            Real.pi ^ 2)) := by
  have hbase := countVectorMass_graphLinearShift_Icc_le
    hn P hbucket G c H A hH hA hc0 hcH hedge hab hwidth
  have hlower := countVectorLinearCoefficient_graph_sqNorm_lower
    hn P hbucket G c hA.le hc0 hedge
  let lower : ℝ := (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3)
  let mass : ℝ := vectorSqNorm (countVectorLinearCoefficient P hbucket
    (GraphQuadratic.graphEffectiveLinear G c))
  have hlowerPos : 0 < lower := by
    dsimp only [lower]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hmassPos : 0 < mass := hlowerPos.trans_le (by
    simpa only [lower, mass] using hlower)
  have hden : lower / Real.pi ^ 2 ≤ mass / Real.pi ^ 2 := by
    exact div_le_div_of_nonneg_right
      (by simpa only [lower, mass] using hlower) (sq_nonneg Real.pi)
  have hfrac : Real.pi / (mass / Real.pi ^ 2) ≤
      Real.pi / (lower / Real.pi ^ 2) := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le
      (div_pos hlowerPos (sq_pos_of_pos Real.pi_pos)) hden
  have hsqrt := Real.sqrt_le_sqrt hfrac
  apply hbase.trans
  exact mul_le_mul_of_nonneg_left hsqrt (sub_nonneg.mpr hab.le)

/-- Exact normalization of the density denominator to the source
`n^(-3/2)` scale. -/
lemma densityIntervalSqrt_eq_scale (A n : ℝ) (hA : 0 < A) (hn : 0 < n) :
    Real.sqrt
        (Real.pi / (((1 / 4 : ℝ) * (A ^ 2 * n ^ 3)) / Real.pi ^ 2)) =
      (2 * Real.pi * Real.sqrt Real.pi / A) * n ^ (-(3 : ℝ) / 2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  have hrpow : (n ^ (-(3 : ℝ) / 2)) ^ 2 = n ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    norm_num
  rw [mul_pow, hrpow, Real.rpow_neg hn.le]
  rw [show n ^ (3 : ℝ) = n ^ (3 : ℕ) from Real.rpow_natCast n 3]
  field_simp [hA.ne', hn.ne', Real.pi_ne_zero]
  ring_nf
  rw [Real.sq_sqrt Real.pi_pos.le]

/-- Fully normalized graph-effective interval estimate: its probability is
`O((b-a)n^(-3/2))` with an explicit constant. -/
theorem countVectorMass_graphLinearShift_Icc_le_scale
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A : ℝ) (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    {a b : ℝ} (hab : a < b)
    (hwidth : 4 * ((H + 1) * (n : ℝ)) ≤ (b - a) * Real.pi) :
    countVectorMass P (fun ell ↦
        a ≤ countVectorLinearShift P hbucket
              (GraphQuadratic.graphEffectiveLinear G c) ell ∧
          countVectorLinearShift P hbucket
              (GraphQuadratic.graphEffectiveLinear G c) ell ≤ b) ≤
      (2 * Real.pi * Real.sqrt Real.pi / A) *
        (b - a) * scale n (-(3 : ℝ) / 2) := by
  have hbase := countVectorMass_graphLinearShift_Icc_le_density
    hn P hbucket G c H A hH hA hc0 hcH hedge hab hwidth
  rw [densityIntervalSqrt_eq_scale A n hA (by exact_mod_cast hn)] at hbase
  change _ ≤ (2 * Real.pi * Real.sqrt Real.pi / A) *
    (b - a) * Real.rpow (n : ℝ) (-(3 : ℝ) / 2)
  change _ ≤ (b - a) * ((2 * Real.pi * Real.sqrt Real.pi / A) *
    Real.rpow (n : ℝ) (-(3 : ℝ) / 2)) at hbase
  exact hbase.trans_eq (by ring)

/-- Covered-graph specialization of the normalized interval estimate.  This
is the exact outer count-vector law occurring after remainder conditioning. -/
theorem conditionedCountVectorMass_linearShift_Icc_le_scale
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (H A : ℝ) (hq : 0 < Fintype.card D.Covered)
    (hH : 0 ≤ H) (hA : 0 < A)
    (hc : ∀ i, 0 ≤ D.conditionedCoveredCoefficient G c O i ∧
      D.conditionedCoveredCoefficient G c O i ≤
        H * (Fintype.card D.Covered : ℝ))
    (hedge : A * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      ((D.finCoveredGraph G).edgeFinset.card : ℝ))
    {a b : ℝ} (hab : a < b)
    (hwidth : 4 * (H + 1) * (Fintype.card D.Covered : ℝ) ≤
      (b - a) * Real.pi) :
    countVectorMass D.finCoveredPartition (fun ell ↦
        a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G c O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G c O)) ell ≤ b) ≤
      (2 * Real.pi * Real.sqrt Real.pi / A) * (b - a) *
        scale (Fintype.card D.Covered) (-(3 : ℝ) / 2) := by
  apply countVectorMass_graphLinearShift_Icc_le_scale hq
    D.finCoveredPartition hbucket (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O) H A hH hA
      (fun i ↦ (hc i).1) (fun i ↦ (hc i).2) hedge hab
  simpa only [mul_assoc] using hwidth

/-- Exact count-vector disintegration of any observable of the projected
Rademacher vector.  This is the probability-space conversion needed to feed
Claim 12.2 into the same mixture used by Claim 12.1. -/
lemma finExpectation_delta_eq_sum_countVector
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (Phi : (Fin n → ℝ) → ℝ) :
    Fourier.finExpectation (Fin n → Bool) (fun xi ↦
        Phi (Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose)
          (fun i ↦ Fourier.rademacherSign (xi i)))) =
      ∑ ell : BucketCountVector P,
        (Fintype.card
            (ProductSlicePoint P (fun j ↦ (ell j).val)) : ℝ) /
            Fintype.card (Finset (Fin n)) *
          Phi (productSliceDelta P hbucket.choose
            (fun j ↦ (ell j).val)) := by
  let g : (Fin n → ℝ) → ℝ := fun x ↦
    Phi (Structured.delta
      (bucketProjectionMatrix P.bucket hbucket.choose) x)
  have hcube := rademacherExpectation_eq_uniformFinset (n := n) g
  have hsign (xi : Fin n → Bool) :
      (fun i ↦ Fourier.rademacherSign (xi i)) =
        (fun i ↦ Invariance.rademacherSign (xi i)) := by
    funext i
    cases xi i <;> rfl
  have hsum :
      (∑ xi : Fin n → Bool,
        Phi (Structured.delta
          (bucketProjectionMatrix P.bucket hbucket.choose)
          (fun i ↦ Fourier.rademacherSign (xi i)))) =
      ∑ xi : Fin n → Bool,
        g (fun i ↦ Invariance.rademacherSign (xi i)) := by
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [hsign xi]
  have hcube' :
      Fourier.finExpectation (Fin n → Bool) (fun xi ↦
          Phi (Structured.delta
            (bucketProjectionMatrix P.bucket hbucket.choose)
            (fun i ↦ Fourier.rademacherSign (xi i)))) =
        Concentration.uniformExpectation (fun S : Finset (Fin n) ↦
          Phi (Structured.delta
            (bucketProjectionMatrix P.bucket hbucket.choose)
            (signOfSet S))) := by
    rw [Fourier.finExpectation, hsum, Concentration.uniformExpectation]
    unfold Invariance.rademacherExpectation Invariance.finiteExpectation at hcube
    unfold BooleanSlices.uniformExpectation at hcube
    rw [Fintype.expect_eq_sum_div_card] at hcube
    simpa only [g] using hcube
  rw [hcube', uniformExpectation_eq_sum_countVector P]
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  rw [Concentration.uniformExpectation]
  have hpoint (S : ProductSlicePoint P (fun j ↦ (ell j).val)) :
      Structured.delta (bucketProjectionMatrix P.bucket hbucket.choose)
          (signOfSet S.1) =
        productSliceDelta P hbucket.choose (fun j ↦ (ell j).val) :=
    delta_signOfSet_eq_productSliceDelta P hbucket
      (fun j ↦ (ell j).val) S
  simp_rw [hpoint]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  have hcard :
      (Fintype.card
        (ProductSlicePoint P (fun j ↦ (ell j).val)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card
        (ProductSlicePoint P (fun j ↦ (ell j).val)) ≠ 0)
  field_simp

/-- The sum of the squared quadratic and variance shifts associated with a
bucket-count vector. -/
noncomputable def countVectorShiftMoment
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P) : ℝ :=
  let d := productSliceDelta P hbucket.choose (fun j ↦ (ell j).val)
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let M := RobustRank.graphAdjacencyMatrix G
  ((1 / 8 : ℝ) * (d ⬝ᵥ (M *ᵥ d))) ^ 2 +
    ∑ i, ((1 / 4 : ℝ) *
      (Structured.centeredProjection Q *ᵥ (M *ᵥ d)) i) ^ 2

lemma countVectorShiftMoment_nonneg
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P) :
    0 ≤ countVectorShiftMoment P hbucket G ell := by
  unfold countVectorShiftMoment
  exact add_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun i hi ↦ sq_nonneg _)

/-- The quadratic contribution to the conditional center shift. -/
noncomputable def countVectorQuadraticShift
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P) : ℝ :=
  let d := productSliceDelta P hbucket.choose (fun j ↦ (ell j).val)
  (1 / 8 : ℝ) *
    (d ⬝ᵥ (RobustRank.graphAdjacencyMatrix G *ᵥ d))

/-- The extra centered linear coefficient created by the bucket-count
shift.  Its squared norm is the second summand in Claim 12.2. -/
noncomputable def countVectorResidualShift
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P) : Fin n → ℝ :=
  let d := productSliceDelta P hbucket.choose (fun j ↦ (ell j).val)
  fun i ↦ (1 / 4 : ℝ) *
    (Structured.centeredProjection
      (bucketProjectionMatrix P.bucket hbucket.choose) *ᵥ
        (RobustRank.graphAdjacencyMatrix G *ᵥ d)) i

lemma countVectorShiftMoment_eq
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P) :
    countVectorShiftMoment P hbucket G ell =
      countVectorQuadraticShift P hbucket G ell ^ 2 +
        vectorSqNorm (countVectorResidualShift P hbucket G ell) := by
  rfl

lemma sq_countVectorQuadraticShift_le_shiftMoment
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P) :
    countVectorQuadraticShift P hbucket G ell ^ 2 ≤
      countVectorShiftMoment P hbucket G ell := by
  rw [countVectorShiftMoment_eq]
  have hres : 0 ≤ vectorSqNorm (countVectorResidualShift P hbucket G ell) := by
    unfold vectorSqNorm
    positivity
  linarith

lemma abs_countVectorQuadraticShift_le_of_shiftMoment_le_sq
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (ell : BucketCountVector P)
    {T : ℝ} (hT : 0 ≤ T)
    (hmoment : countVectorShiftMoment P hbucket G ell ≤ T ^ 2) :
    |countVectorQuadraticShift P hbucket G ell| ≤ T := by
  apply (sq_le_sq₀ (abs_nonneg _) hT).mp
  rw [sq_abs]
  exact (sq_countVectorQuadraticShift_le_shiftMoment P hbucket G ell).trans
    hmoment

/-- A quadratic displacement bounded by half the buffer cannot destroy the
geometric distance supplied by the buffered linear cell. -/
lemma half_abs_linear_sub_center_sub_buffer_le_abs_shifted
    {L center qshift buffer : ℝ}
    (hqshift : |qshift| ≤ buffer / 2) :
    |L - center| / 2 - buffer / 2 ≤ |center - L - qshift| := by
  have htri : |L - center| ≤ |center - L - qshift| + |qshift| := by
    calc
      |L - center| = |-(center - L - qshift) - qshift| := by congr 1 <;> ring
      _ ≤ |-(center - L - qshift)| + |-qshift| := abs_add_le _ _
      _ = |center - L - qshift| + |qshift| := by simp only [abs_neg]
  have hx : 0 ≤ |center - L - qshift| := abs_nonneg _
  have hbuffer : 0 ≤ buffer := by
    nlinarith [abs_nonneg qshift]
  nlinarith

/-- The Claim 12.1 coefficient at count vector `ell` is the coefficient at
zero bucket shift plus the residual-shift vector measured by Claim 12.2. -/
lemma wStar_eq_base_add_countVectorResidualShift
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    (ell : BucketCountVector P) :
    Structured.wStar
        (bucketProjectionMatrix P.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix G) y
        (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val)) =
      Structured.wStar
          (bucketProjectionMatrix P.bucket hbucket.choose)
          (RobustRank.graphAdjacencyMatrix G) y 0 +
        countVectorResidualShift P hbucket G ell := by
  funext i
  simp only [Structured.wStar, countVectorResidualShift,
    Pi.add_apply, Pi.smul_apply, Matrix.mulVec_zero, smul_zero, add_zero,
    Matrix.mulVec_add, Matrix.mulVec_smul]
  ring

/-- Squared Euclidean norm of a sum, in the form used to compare the
conditional Claim 12.1 scale to the Claim 12.2 shift moment. -/
lemma vectorSqNorm_add_le_two {n : ℕ} (u v : Fin n → ℝ) :
    vectorSqNorm (u + v) ≤
      2 * vectorSqNorm u + 2 * vectorSqNorm v := by
  unfold vectorSqNorm
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i - v i)]

/-- Deterministic scale comparison underlying the dyadic use of Claims
12.1 and 12.2.  The conditional variance proxy is controlled by twice its
zero-shift value plus twice the Claim 12.2 shift moment. -/
lemma claim121ScaleSq_le_base_add_shiftMoment
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    (ell : BucketCountVector P) :
    let F := bucketCenteredAdjacency P.bucket hbucket.choose G
    let f0 := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y 0
    let f := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y
      (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val))
    2 * frobeniusSq F + vectorSqNorm f ≤
      2 * (2 * frobeniusSq F + vectorSqNorm f0) +
        2 * countVectorShiftMoment P hbucket G ell := by
  dsimp only
  rw [wStar_eq_base_add_countVectorResidualShift P hbucket G y ell]
  have hvec := vectorSqNorm_add_le_two
    (Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y 0)
    (countVectorResidualShift P hbucket G ell)
  have hfrob : 0 ≤ frobeniusSq
      (bucketCenteredAdjacency P.bucket hbucket.choose G) :=
    Finset.sum_nonneg fun i hi ↦
      Finset.sum_nonneg fun j hj ↦ sq_nonneg _
  rw [countVectorShiftMoment_eq]
  have hquad : 0 ≤ countVectorQuadraticShift P hbucket G ell ^ 2 :=
    sq_nonneg _
  linarith

/-- Reverse deterministic scale comparison.  The zero-shift coefficient is
the conditional coefficient minus the same residual vector, so the identical
two-square inequality works in the other direction. -/
lemma baseScaleSq_le_claim121Scale_add_shiftMoment
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    (ell : BucketCountVector P) :
    let F := bucketCenteredAdjacency P.bucket hbucket.choose G
    let f0 := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y 0
    let f := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y
      (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val))
    2 * frobeniusSq F + vectorSqNorm f0 ≤
      2 * (2 * frobeniusSq F + vectorSqNorm f) +
        2 * countVectorShiftMoment P hbucket G ell := by
  dsimp only
  rw [wStar_eq_base_add_countVectorResidualShift P hbucket G y ell]
  let u := Structured.wStar
    (bucketProjectionMatrix P.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix G) y 0
  let v := countVectorResidualShift P hbucket G ell
  have hvec := vectorSqNorm_add_le_two (u + v) (-v)
  have hcancel : (u + v) + (-v) = u := by
    funext i
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have hneg : vectorSqNorm (-v) = vectorSqNorm v := by
    unfold vectorSqNorm
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.neg_apply]
    ring
  rw [hcancel, hneg] at hvec
  have hfrob : 0 ≤ frobeniusSq
      (bucketCenteredAdjacency P.bucket hbucket.choose G) :=
    Finset.sum_nonneg fun i hi ↦
      Finset.sum_nonneg fun j hj ↦ sq_nonneg _
  rw [countVectorShiftMoment_eq]
  have hquad : 0 ≤ countVectorQuadraticShift P hbucket G ell ^ 2 :=
    sq_nonneg _
  simpa only [u, v] using (show
    2 * frobeniusSq (bucketCenteredAdjacency P.bucket hbucket.choose G) +
        vectorSqNorm u ≤
      2 * (2 * frobeniusSq
          (bucketCenteredAdjacency P.bucket hbucket.choose G) +
        vectorSqNorm (u + v)) +
          2 * (countVectorQuadraticShift P hbucket G ell ^ 2 +
            vectorSqNorm v) by
      linarith)

/-- Elementary two-scale dichotomy used in Step 7 of Section 12.  If the
current scale is not controlled by the shift moment, it is within a factor
two of the zero-shift scale. -/
lemma nonnegative_scale_dichotomy {sigma sigma0 W : ℝ}
    (hsigma : 0 ≤ sigma) (hsigma0 : 0 ≤ sigma0) (hW : 0 ≤ W)
    (hforward : sigma ^ 2 ≤ 2 * sigma0 ^ 2 + 2 * W)
    (hback : sigma0 ^ 2 ≤ 2 * sigma ^ 2 + 2 * W) :
    sigma ≤ 2 * Real.sqrt W ∨
      (sigma0 / 2 ≤ sigma ∧ sigma ≤ 2 * sigma0) := by
  by_cases hsmall : sigma ≤ 2 * Real.sqrt W
  · exact Or.inl hsmall
  · right
    have hsqrt : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW
    have hlarge : 4 * W < sigma ^ 2 := by
      have hlt : 2 * Real.sqrt W < sigma := lt_of_not_ge hsmall
      have hsquare : (2 * Real.sqrt W) ^ 2 < sigma ^ 2 :=
        (sq_lt_sq₀ (by positivity) hsigma).2 hlt
      nlinarith
    constructor
    · nlinarith [sq_nonneg (sigma0 - 2 * sigma)]
    · nlinarith [sq_nonneg (sigma - 2 * sigma0)]

/-- The actual Claim 12.1 proxy scale obeys the Section 12 dichotomy: it is
either controlled by the Claim 12.2 shift moment, or comparable to its
zero-count value. -/
lemma claim121Scale_dichotomy
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    (ell : BucketCountVector P) :
    let F := bucketCenteredAdjacency P.bucket hbucket.choose G
    let f0 := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y 0
    let f := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix G) y
      (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val))
    let sigma0 := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f0)
    let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
    sigma ≤ 2 * Real.sqrt (countVectorShiftMoment P hbucket G ell) ∨
      (sigma0 / 2 ≤ sigma ∧ sigma ≤ 2 * sigma0) := by
  dsimp only
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  let f0 := Structured.wStar
    (bucketProjectionMatrix P.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix G) y 0
  let f := Structured.wStar
    (bucketProjectionMatrix P.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix G) y
    (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val))
  have hF : 0 ≤ frobeniusSq F :=
    Finset.sum_nonneg fun i hi ↦ Finset.sum_nonneg fun j hj ↦ sq_nonneg _
  have hf0 : 0 ≤ vectorSqNorm f0 := by
    unfold vectorSqNorm
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  have hf : 0 ≤ vectorSqNorm f := by
    unfold vectorSqNorm
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  have hbase0 : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f0 := by positivity
  have hbase : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by positivity
  have hW := countVectorShiftMoment_nonneg P hbucket G ell
  apply nonnegative_scale_dichotomy (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hW
  · rw [Real.sq_sqrt hbase, Real.sq_sqrt hbase0]
    simpa only [F, f0, f] using
      claim121ScaleSq_le_base_add_shiftMoment P hbucket G y ell
  · rw [Real.sq_sqrt hbase0, Real.sq_sqrt hbase]
    simpa only [F, f0, f] using
      baseScaleSq_le_claim121Scale_add_shiftMoment P hbucket G y ell

/-- The Frobenius-only base scale shared by the two shift-dominated
branches. -/
noncomputable def claim121FrobeniusBase
    {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (2 * frobeniusSq F)

lemma claim121FrobeniusBase_sq {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℝ) :
    claim121FrobeniusBase F ^ 2 = 2 * frobeniusSq F := by
  unfold claim121FrobeniusBase
  rw [Real.sq_sqrt]
  unfold frobeniusSq
  positivity

lemma frobenius_norm_le_claim121FrobeniusBase {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℝ) :
    ‖F‖ ≤ claim121FrobeniusBase F := by
  have hF : 0 ≤ frobeniusSq F := by
    unfold frobeniusSq
    positivity
  apply (sq_le_sq₀ (norm_nonneg F)
    (Real.sqrt_nonneg (2 * frobeniusSq F))).mp
  rw [Real.sq_sqrt (by positivity),
    frobenius_norm_sq_eq_frobeniusSq]
  linarith

lemma claim121FrobeniusBase_le_scale {n : ℕ}
    (F : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    claim121FrobeniusBase F ≤
      Real.sqrt (2 * frobeniusSq F + vectorSqNorm f) := by
  have hF : 0 ≤ frobeniusSq F := by
    unfold frobeniusSq
    positivity
  have hf : 0 ≤ vectorSqNorm f := by
    unfold vectorSqNorm
    positivity
  exact Real.sqrt_le_sqrt (by linarith)

/-- The actual conditional Claim 12.1 scale at a count vector. -/
noncomputable def countVectorClaim121Scale
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (ell : BucketCountVector D.finCoveredPartition) : ℝ :=
  Real.sqrt
    (2 * frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)) +
      vectorSqNorm (Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O))
        (productSliceDelta D.finCoveredPartition hbucket.choose
          (fun j ↦ (ell j).val))))

/-- The zero-count conditional Claim 12.1 scale. -/
noncomputable def zeroCountClaim121Scale
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket) : ℝ :=
  Real.sqrt
    (2 * frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)) +
      vectorSqNorm (Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) 0))

/-- The deterministic geometry needed by the four-way average, in the
actual count-vector variables of one remainder conditioning. -/
lemma countVectorClaim121Scale_geometry
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (ell : BucketCountVector D.finCoveredPartition) :
    let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
      hbucket.choose (D.finCoveredGraph G)
    claim121FrobeniusBase F ≤
        countVectorClaim121Scale D G cvec O hbucket ell ∧
      (countVectorClaim121Scale D G cvec O hbucket ell ≤
          2 * Real.sqrt (countVectorShiftMoment D.finCoveredPartition
            hbucket (D.finCoveredGraph G) ell) ∨
        (zeroCountClaim121Scale D G cvec O hbucket / 2 ≤
            countVectorClaim121Scale D G cvec O hbucket ell ∧
          countVectorClaim121Scale D G cvec O hbucket ell ≤
            2 * zeroCountClaim121Scale D G cvec O hbucket)) := by
  dsimp only
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose (D.finCoveredGraph G)
  let f := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
    (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G cvec O))
    (productSliceDelta D.finCoveredPartition hbucket.choose
      (fun j ↦ (ell j).val))
  constructor
  · simpa only [F, f, countVectorClaim121Scale] using
      claim121FrobeniusBase_le_scale F f
  · simpa only [F, f, countVectorClaim121Scale, zeroCountClaim121Scale]
      using claim121Scale_dichotomy D.finCoveredPartition hbucket
        (D.finCoveredGraph G)
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell

/-- The centered adjacency norm fits both dyadic base scales used in the
four-way partition. -/
lemma conditionedClaim121_norm_bounds
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket) :
    let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
      hbucket.choose (D.finCoveredGraph G)
    ‖F‖ ≤ 16 * claim121FrobeniusBase F ∧
      ‖F‖ ≤ 8 * zeroCountClaim121Scale D G cvec O hbucket := by
  dsimp only
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose (D.finCoveredGraph G)
  let f0 := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
    (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G cvec O)) 0
  have hnorm : ‖F‖ ≤ claim121FrobeniusBase F :=
    frobenius_norm_le_claim121FrobeniusBase F
  have hbaseNonneg : 0 ≤ claim121FrobeniusBase F := by
    unfold claim121FrobeniusBase
    positivity
  have hzero : claim121FrobeniusBase F ≤
      zeroCountClaim121Scale D G cvec O hbucket := by
    simpa only [F, f0, zeroCountClaim121Scale] using
      claim121FrobeniusBase_le_scale F f0
  constructor <;> nlinarith

/-- Typical remainder degrees control the zero-count `wStar` without any
near-balance hypothesis.  This is the coefficient certificate needed to
bound the cutoff scale in the exceptional-residual argument. -/
lemma hasKSSSBalancedCoefficients_conditionedCovered_zero
    {n k : ℕ} {d0 : Fin n → ℝ} {rho t delta : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (hd0 : d0 = GraphQuadratic.graphEffectiveLinear G cvec)
    (O : Finset (Fin n))
    (htypical : ∀ i : Fin (Fintype.card D.Covered),
      |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
        (AKSGraph.degreeInto G (D.finCoveredEquiv i).1 D.remainder : ℝ) / 2| ≤ t)
    (hrho : 0 ≤ rho) (ht : 0 ≤ t)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (hbound : rho + t ≤
      scale (Fintype.card D.Covered) (1 / 2 + 3 * delta)) :
    HasKSSSBalancedCoefficients delta D.finCoveredPartition
      (Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) 0)
      (bucketCenteredAdjacency D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)) := by
  let P := D.finCoveredPartition
  let M := RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G)
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G cvec O)
  let a : Fin (Fintype.card D.BlockIndex) → ℝ :=
    fun j ↦ D.blockCenter (D.finBlockEquiv j)
  apply hasKSSSBalancedCoefficients_wStar_of_bounds delta P hbucket
    (D.finCoveredGraph G) y 0
  intro i
  have hraw := abs_wStar_le_of_close_bucketConstant P hbucket M y 0 a
    (add_nonneg hrho ht) (by norm_num : (0 : ℝ) ≤ 0)
    (by
      intro u v
      classical
      simp only [M, RobustRank.graphAdjacencyMatrix]
      split <;> norm_num)
    (by
      intro u
      exact D.conditionedCovered_close_to_blockCenter G cvec hd0 O
        htypical u)
    (by intro u; simp) i
  have hraw' : |Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose) M y 0 i| ≤
      rho + t := by
    simpa only [add_zero, Nat.cast_ofNat, mul_zero, zero_div] using hraw
  exact hraw'.trans (by
    simpa only [P, M, y] using hbound)

/-- The robust Frobenius lower bound supplies a common linear lower bound
for both fixed scales in the four-way partition. -/
lemma sqrt_mul_le_claim121_fixedScales_of_frobenius
    {n k : ℕ} {d0 : Fin n → ℝ} {rho rhoF : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (hrhoF : 0 ≤ rhoF)
    (hFrob : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G))) :
    let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
      hbucket.choose (D.finCoveredGraph G)
    Real.sqrt rhoF * (Fintype.card D.Covered : ℝ) ≤
        claim121FrobeniusBase F ∧
      Real.sqrt rhoF * (Fintype.card D.Covered : ℝ) ≤
        zeroCountClaim121Scale D G cvec O hbucket := by
  dsimp only
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose (D.finCoveredGraph G)
  let f0 := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
    (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G cvec O)) 0
  have hq : 0 ≤ (Fintype.card D.Covered : ℝ) := by positivity
  have hFnonneg : 0 ≤ frobeniusSq F := by
    unfold frobeniusSq
    positivity
  have hf0Nonneg : 0 ≤ vectorSqNorm f0 := by
    unfold vectorSqNorm
    positivity
  have hzeroBase : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f0 := by
    positivity
  have hzero : Real.sqrt rhoF * (Fintype.card D.Covered : ℝ) ≤
      Real.sqrt (2 * frobeniusSq F + vectorSqNorm f0) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hrhoF, Real.sq_sqrt hzeroBase]
    have hFrob' : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
        frobeniusSq F := by simpa only [F] using hFrob
    nlinarith
  have hfrobSq : claim121FrobeniusBase F ^ 2 = 2 * frobeniusSq F :=
    claim121FrobeniusBase_sq F
  have hleftNonneg : 0 ≤
      Real.sqrt rhoF * (Fintype.card D.Covered : ℝ) := by positivity
  have hrightNonneg : 0 ≤ claim121FrobeniusBase F := by
    unfold claim121FrobeniusBase
    positivity
  have hleftSq :
      (Real.sqrt rhoF * (Fintype.card D.Covered : ℝ)) ^ 2 ≤
        claim121FrobeniusBase F ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrhoF, hfrobSq]
    nlinarith [hFrob]
  constructor
  · exact (sq_le_sq₀ hleftNonneg hrightNonneg).mp hleftSq
  · simpa only [F, f0, zeroCountClaim121Scale] using hzero

/-- Four-way partition used in Step 7.  In each half of the deterministic
scale dichotomy, compare the shift moment to the relevant base scale.  The
low half is handled by fixed comparable cells and the high half by the
dyadic Claim 12.2 summation. -/
lemma claim121_scale_four_way
    {sigma sigma0 frobBase W : ℝ}
    (hdichotomy : sigma ≤ 2 * Real.sqrt W ∨
      (sigma0 / 2 ≤ sigma ∧ sigma ≤ 2 * sigma0)) :
    (sigma ≤ 2 * Real.sqrt W ∧ W ≤ frobBase ^ 2) ∨
      (sigma ≤ 2 * Real.sqrt W ∧ frobBase ^ 2 ≤ W) ∨
      ((sigma0 / 2 ≤ sigma ∧ sigma ≤ 2 * sigma0) ∧ W ≤ sigma0 ^ 2) ∨
      ((sigma0 / 2 ≤ sigma ∧ sigma ≤ 2 * sigma0) ∧ sigma0 ^ 2 ≤ W) := by
  rcases hdichotomy with hshift | hcomp
  · rcases le_total W (frobBase ^ 2) with hlow | hhigh
    · exact Or.inl ⟨hshift, hlow⟩
    · exact Or.inr (Or.inl ⟨hshift, hhigh⟩)
  · rcases le_total W (sigma0 ^ 2) with hlow | hhigh
    · exact Or.inr (Or.inr (Or.inl ⟨hcomp, hlow⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hcomp, hhigh⟩))

/-- Weighted union bound for a four-way partition.  The branch predicates
may overlap; nonnegativity makes the overlap harmless. -/
lemma weighted_if_le_sum_four
    {D : Type*} [Fintype D]
    (weight cond : D → ℝ) (Good E₁ E₂ E₃ E₄ : D → Prop)
    (hweight : ∀ d, 0 ≤ weight d) (hcond : ∀ d, 0 ≤ cond d)
    (hcover : ∀ d, Good d → E₁ d ∨ E₂ d ∨ E₃ d ∨ E₄ d) :
    ∑ d, weight d * (if Good d then cond d else 0) ≤
      (∑ d, weight d * (if E₁ d then cond d else 0)) +
      (∑ d, weight d * (if E₂ d then cond d else 0)) +
      (∑ d, weight d * (if E₃ d then cond d else 0)) +
      (∑ d, weight d * (if E₄ d then cond d else 0)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hc := hcond d
  have ht : 0 ≤ weight d * cond d := mul_nonneg (hweight d) hc
  have hterm (E : D → Prop) :
      0 ≤ weight d * (if E d then cond d else 0) := by
    by_cases hE : E d
    · simpa only [hE, if_true] using ht
    · simp only [hE, if_false, mul_zero]
      exact le_rfl
  by_cases hgood : Good d
  · rw [if_pos hgood]
    rcases hcover d hgood with h1 | h2 | h3 | h4
    · rw [if_pos h1]
      nlinarith [hterm E₂, hterm E₃, hterm E₄]
    · rw [if_pos h2]
      nlinarith [hterm E₁, hterm E₃, hterm E₄]
    · rw [if_pos h3]
      nlinarith [hterm E₁, hterm E₂, hterm E₄]
    · rw [if_pos h4]
      nlinarith [hterm E₁, hterm E₂, hterm E₃]
  · rw [if_neg hgood]
    nlinarith [hterm E₁, hterm E₂, hterm E₃, hterm E₄]

/-- A Frobenius lower bound gives the linear-in-order lower bound for the
zero-count Claim 12.1 scale used to choose a fixed admissible interval
width in the Section 12 averaging argument. -/
lemma sqrt_mul_le_zeroCountScale_of_frobenius
    {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (f0 : Fin n → ℝ)
    {rho q : ℝ} (hrho : 0 ≤ rho) (hq : 0 ≤ q)
    (hFrob : rho * q ^ 2 ≤ frobeniusSq F) :
    Real.sqrt rho * q ≤
      Real.sqrt (2 * frobeniusSq F + vectorSqNorm f0) := by
  have hF : 0 ≤ frobeniusSq F :=
    Finset.sum_nonneg fun i hi ↦
      Finset.sum_nonneg fun j hj ↦ sq_nonneg _
  have hf0 : 0 ≤ vectorSqNorm f0 := by
    unfold vectorSqNorm
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  have hbase : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f0 := by
    positivity
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hq)
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hrho, Real.sq_sqrt hbase]
  nlinarith

/-- The fixed enlargement factor dictated by the coefficient bound turns
the preceding scale lower bound into the central-frequency admissibility
condition for the count-vector interval estimate. -/
lemma countVector_interval_width_of_zeroCountScale
    {H rho q sigma0 : ℝ} (hH : 0 < H) (hrho : 0 < rho)
    (hlower : Real.sqrt rho * q ≤ sigma0) :
    4 * ((2 * H + 1) + 1) * q ≤
      (4 * ((2 * H + 1) + 1) /
          (Real.pi * Real.sqrt rho) * sigma0) * Real.pi := by
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  calc
    4 * ((2 * H + 1) + 1) * q =
        (4 * ((2 * H + 1) + 1) /
          (Real.pi * Real.sqrt rho) *
            (Real.sqrt rho * q)) * Real.pi := by
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hsqrt]
    _ ≤ (4 * ((2 * H + 1) + 1) /
          (Real.pi * Real.sqrt rho) * sigma0) * Real.pi := by
      gcongr

/-- The source-shaped crude consequence of the nonuniform Claim 12.1
bound: once the fixed window radius is below the conditional scale, the
conditional probability is `O(1 / sigma)` plus the Fourier-comparison
error. -/
lemma claim121_nonuniform_rhs_le_crude
    {q : ℕ} {B eta sigma x : ℝ} (hB : 0 ≤ B) (heta : 0 < eta)
    (hsigma : 0 < sigma) (hBsigma : B ≤ sigma) :
    Esseen.relativeEsseenConstant *
        (B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) +
          B * scale q (-6 / 5 : ℝ)) ≤
      Esseen.relativeEsseenConstant *
        (((B + B / eta) / sigma) + B * scale q (-6 / 5 : ℝ)) := by
  have hden : 0 < x ^ 2 + sigma ^ 2 := by positivity
  have hsigmaSq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hfirst : B ^ 2 / (x ^ 2 + sigma ^ 2) ≤ B / sigma := by
    calc
      B ^ 2 / (x ^ 2 + sigma ^ 2) ≤ B ^ 2 / sigma ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg B) hsigmaSq
          (by nlinarith [sq_nonneg x])
      _ ≤ B / sigma := by
        apply (div_le_div_iff₀ hsigmaSq hsigma).2
        have hprod := mul_nonneg hB (sub_nonneg.mpr hBsigma)
        nlinarith
  have hexp : Real.exp (-eta * |x| / (2 * sigma)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnum : -eta * |x| ≤ 0 := by
      have := mul_nonneg heta.le (abs_nonneg x)
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  have hcoeff : 0 ≤ B / (eta * sigma) := by positivity
  have hsecond :
      (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
        (B / eta) / sigma := by
    calc
      (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
          (B / (eta * sigma)) * 1 :=
        mul_le_mul_of_nonneg_left hexp hcoeff
      _ = (B / eta) / sigma := by ring
  apply mul_le_mul_of_nonneg_left _ Esseen.relativeEsseenConstant_nonneg
  calc
    B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) +
          B * scale q (-6 / 5 : ℝ) ≤
        B / sigma + (B / eta) / sigma +
          B * scale q (-6 / 5 : ℝ) := by
      gcongr
    _ = ((B + B / eta) / sigma) +
          B * scale q (-6 / 5 : ℝ) := by ring

/-- Monotonicity of the count-vector law. -/
lemma countVectorMass_mono
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) {E F : BucketCountVector P → Prop}
    (hEF : ∀ ell, E ell → F ell) :
    countVectorMass P E ≤ countVectorMass P F := by
  rw [countVectorMass_eq_uniformProbability,
    countVectorMass_eq_uniformProbability]
  exact Concentration.uniformProbability_mono fun S hS ↦
    hEF (bucketCounts P S) hS

/-- Union bound for the count-vector law. -/
lemma countVectorMass_union_le
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (E F : BucketCountVector P → Prop) :
    countVectorMass P (fun ell ↦ E ell ∨ F ell) ≤
      countVectorMass P E + countVectorMass P F := by
  unfold countVectorMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ell hell
  let w : ℝ :=
    (Fintype.card (ProductSlicePoint P (fun k ↦ (ell k).val)) : ℝ) /
      Fintype.card (Finset α)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  by_cases hE : E ell <;> by_cases hF : F ell <;>
    simp only [hE, hF, or_self, false_or, or_false, if_true, if_false] <;>
      linarith

/-- The explicit atom weight in the count-vector law. -/
noncomputable def countVectorWeight
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : BucketCountVector P) : ℝ :=
  (Fintype.card
      (ProductSlicePoint P (fun k ↦ (ell k).val)) : ℝ) /
    Fintype.card (Finset α)

lemma countVectorWeight_nonneg
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (ell : BucketCountVector P) :
    0 ≤ countVectorWeight P ell := by
  unfold countVectorWeight
  positivity

/-- Exact finite-mixture union bound which retains the conditional
probability on the good count vectors.  A window point is charged either to
its good conditional atom, to a bad count vector, or to a residual event on
the full Boolean cube. -/
lemma countVector_weighted_event_le_good_add_bad_add_residual
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (Window Residual : Finset α → Prop)
    (Good Bad : BucketCountVector P → Prop)
    (hsplit : ∀ S : Finset α, Window S →
      Good (bucketCounts P S) ∨ Bad (bucketCounts P S) ∨ Residual S) :
    (∑ ell : BucketCountVector P,
        countVectorWeight P ell *
          Concentration.uniformProbability
            (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦
              Window S.1)) ≤
      (∑ ell : BucketCountVector P,
        countVectorWeight P ell *
          (if Good ell then
            Concentration.uniformProbability
              (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦
                Window S.1)
          else 0)) +
        countVectorMass P Bad +
        Concentration.uniformProbability Residual := by
  let pWindow : BucketCountVector P → ℝ := fun ell ↦
    Concentration.uniformProbability
      (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ Window S.1)
  let pResidual : BucketCountVector P → ℝ := fun ell ↦
    Concentration.uniformProbability
      (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ Residual S.1)
  have hpoint (ell : BucketCountVector P) :
      countVectorWeight P ell * pWindow ell ≤
        countVectorWeight P ell * (if Good ell then pWindow ell else 0) +
          countVectorWeight P ell * (if Bad ell then 1 else 0) +
          countVectorWeight P ell * pResidual ell := by
    have hw := countVectorWeight_nonneg P ell
    have hpWindowNonneg := Concentration.uniformProbability_nonneg
      (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ Window S.1)
    have hpResidualNonneg := Concentration.uniformProbability_nonneg
      (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ Residual S.1)
    by_cases hGood : Good ell
    · simp only [hGood, if_true]
      have hbadIndicator :
          0 ≤ (if Bad ell then (1 : ℝ) else 0) := by
        split <;> norm_num
      calc
        countVectorWeight P ell * pWindow ell ≤
            countVectorWeight P ell * pWindow ell +
              countVectorWeight P ell *
                (if Bad ell then 1 else 0) :=
          le_add_of_nonneg_right (mul_nonneg hw hbadIndicator)
        _ ≤ (countVectorWeight P ell * pWindow ell +
              countVectorWeight P ell *
                (if Bad ell then 1 else 0)) +
              countVectorWeight P ell * pResidual ell :=
          le_add_of_nonneg_right (mul_nonneg hw hpResidualNonneg)
    · by_cases hBad : Bad ell
      · have hpOne := Concentration.uniformProbability_le_one
          (fun S : ProductSlicePoint P (fun k ↦ (ell k).val) ↦ Window S.1)
        simp only [hGood, hBad, if_false, if_true, mul_zero]
        dsimp only [pWindow, pResidual]
        have hmul := mul_le_mul_of_nonneg_left hpOne hw
        nlinarith [mul_nonneg hw hpResidualNonneg]
      · have hsub : ∀ S : ProductSlicePoint P (fun k ↦ (ell k).val),
            Window S.1 → Residual S.1 := by
          intro S hS
          have hcounts : bucketCounts P S.1 = ell := by
            funext k
            apply Fin.ext
            exact (mem_productBooleanSlice P
              (fun k ↦ (ell k).val) S.1).mp S.2 k
          rcases hsplit S.1 hS with hG | hB | hR
          · exact False.elim (hGood (by simpa only [hcounts] using hG))
          · exact False.elim (hBad (by simpa only [hcounts] using hB))
          · exact hR
        have hp := Concentration.uniformProbability_mono hsub
        simp only [hGood, hBad, if_false, mul_zero, zero_add]
        exact mul_le_mul_of_nonneg_left hp hw
  have hsum :
      (∑ ell : BucketCountVector P,
          countVectorWeight P ell * pWindow ell) ≤
        ∑ ell : BucketCountVector P,
          (countVectorWeight P ell *
              (if Good ell then pWindow ell else 0) +
            countVectorWeight P ell *
              (if Bad ell then 1 else 0) +
            countVectorWeight P ell * pResidual ell) := by
    apply Finset.sum_le_sum
    intro ell hell
    exact hpoint ell
  have hbad :
      (∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Bad ell then 1 else 0)) =
        countVectorMass P Bad := by
    unfold countVectorMass
    apply Finset.sum_congr rfl
    intro ell hell
    by_cases h : Bad ell <;>
      simp [h, countVectorWeight]
  have hres :
      (∑ ell : BucketCountVector P,
        countVectorWeight P ell * pResidual ell) =
        Concentration.uniformProbability Residual := by
    simpa only [countVectorWeight, pResidual] using
      (uniformProbability_eq_sum_countVector P Residual).symm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hbad, hres] at hsum
  simpa only [pWindow] using hsum

lemma countVectorMass_eq_sum_filter_countVectorWeight
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (E : BucketCountVector P → Prop) :
    countVectorMass P E =
      ∑ ell : BucketCountVector P with E ell, countVectorWeight P ell := by
  classical
  unfold countVectorMass countVectorWeight
  rw [Finset.sum_filter]

lemma sum_countVectorWeight_eq_one
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) :
    ∑ ell : BucketCountVector P, countVectorWeight P ell = 1 := by
  have h := countVectorMass_eq_uniformProbability P (fun _ ↦ True)
  rw [countVectorMass_eq_sum_filter_countVectorWeight] at h
  simpa only [Finset.filter_true, Concentration.uniformProbability,
    Finset.filter_true, Finset.card_univ, Nat.cast_ofNat,
    div_self (by positivity : (Fintype.card (Finset α) : ℝ) ≠ 0)] using h

/-- Index of the unit-width annulus around a real center. -/
noncomputable def absoluteCellIndex (center width x : ℝ) : ℕ :=
  Nat.floor (|x - center| / width)

/-- An absolute-distance cell is covered by two intervals of the original
width, one on either side of the center. -/
lemma countVectorMass_absoluteCellIndex_le_two
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L : BucketCountVector P → ℝ)
    {center width A : ℝ} (hwidth : 0 < width)
    (hinterval : ∀ a : ℝ,
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ a + width) ≤ A)
    (j : ℕ) :
    countVectorMass P (fun ell ↦
      absoluteCellIndex center width (L ell) = j) ≤ 2 * A := by
  let leftA : ℝ := center - ((j : ℝ) + 1) * width
  let rightA : ℝ := center + (j : ℝ) * width
  have hsubset : ∀ ell,
      absoluteCellIndex center width (L ell) = j →
        (leftA ≤ L ell ∧ L ell ≤ leftA + width) ∨
        (rightA ≤ L ell ∧ L ell ≤ rightA + width) := by
    intro ell hj
    let z : ℝ := L ell - center
    have hz0 : 0 ≤ |z| / width := div_nonneg (abs_nonneg z) hwidth.le
    have hlo : (j : ℝ) ≤ |z| / width := by
      rw [← hj]
      exact Nat.floor_le hz0
    have hhi : |z| / width < (j : ℝ) + 1 := by
      rw [← hj]
      exact Nat.lt_floor_add_one _
    have hlo' : (j : ℝ) * width ≤ |z| :=
      (le_div_iff₀ hwidth).mp hlo
    have hhi' : |z| < ((j : ℝ) + 1) * width :=
      (div_lt_iff₀ hwidth).mp hhi
    by_cases hz : 0 ≤ z
    · right
      rw [abs_of_nonneg hz] at hlo' hhi'
      dsimp only [z, rightA] at hlo' hhi' ⊢
      constructor <;> linarith
    · left
      have hz' : z < 0 := lt_of_not_ge hz
      rw [abs_of_neg hz'] at hlo' hhi'
      dsimp only [z, leftA] at hlo' hhi' ⊢
      constructor <;> linarith
  calc
    countVectorMass P (fun ell ↦
        absoluteCellIndex center width (L ell) = j) ≤
      countVectorMass P (fun ell ↦
          (leftA ≤ L ell ∧ L ell ≤ leftA + width) ∨
          (rightA ≤ L ell ∧ L ell ≤ rightA + width)) :=
        countVectorMass_mono P hsubset
    _ ≤ countVectorMass P (fun ell ↦
          leftA ≤ L ell ∧ L ell ≤ leftA + width) +
        countVectorMass P (fun ell ↦
          rightA ≤ L ell ∧ L ell ≤ rightA + width) :=
      countVectorMass_union_le P _ _
    _ ≤ A + A := add_le_add (hinterval leftA) (hinterval rightA)
    _ = 2 * A := by ring

/-- Absolute-distance cell index after discarding a fixed central buffer. -/
noncomputable def bufferedAbsoluteCellIndex
    (center buffer width x : ℝ) : ℕ :=
  Nat.floor (max (|x - center| - buffer) 0 / width)

lemma bufferedAbsoluteCellIndex_mul_width_le
    {center buffer width x : ℝ} (hwidth : 0 < width) :
    (bufferedAbsoluteCellIndex center buffer width x : ℝ) * width ≤
      max (|x - center| - buffer) 0 := by
  have hu0 : 0 ≤ max (|x - center| - buffer) 0 := le_max_right _ _
  have hfloor : (bufferedAbsoluteCellIndex center buffer width x : ℝ) ≤
      max (|x - center| - buffer) 0 / width := by
    exact Nat.floor_le (div_nonneg hu0 hwidth.le)
  exact (le_div_iff₀ hwidth).mp hfloor

/-- A buffered cell index still gives a geometric lower bound after a
deterministic centering error of half the buffer.  This is the form used in
the comparable-scale part of Step 7. -/
lemma bufferedAbsoluteCellIndex_mul_width_div_two_le_abs
    {center buffer width L x : ℝ} (hwidth : 0 < width)
    (hcenter : |L - center| / 2 - buffer / 2 ≤ |x|) :
    (bufferedAbsoluteCellIndex center buffer width L : ℝ) * width / 2 ≤
      |x| := by
  have hidx := bufferedAbsoluteCellIndex_mul_width_le
    (center := center) (buffer := buffer) (width := width) (x := L) hwidth
  by_cases hbuf : 0 ≤ |L - center| - buffer
  · rw [max_eq_left hbuf] at hidx
    nlinarith
  · have hbuf' : |L - center| - buffer ≤ 0 := le_of_not_ge hbuf
    rw [max_eq_right hbuf'] at hidx
    have habs : 0 ≤ |x| := abs_nonneg x
    nlinarith

/-- Every buffered cell has uniformly bounded mass: the central cell is one
interval, while every later cell is the union of two intervals of the base
width. -/
lemma countVectorMass_bufferedAbsoluteCellIndex_le
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L : BucketCountVector P → ℝ)
    {center buffer width rate : ℝ}
    (hbuffer : 0 ≤ buffer) (hwidth : 0 < width) (hrate : 0 ≤ rate)
    (hinterval : ∀ a b : ℝ, width ≤ b - a →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a))
    (j : ℕ) :
    countVectorMass P (fun ell ↦
      bufferedAbsoluteCellIndex center buffer width (L ell) = j) ≤
      2 * rate * (buffer + width) := by
  rcases j.eq_zero_or_pos with rfl | hj
  · have hsubset : ∀ ell,
        bufferedAbsoluteCellIndex center buffer width (L ell) = 0 →
          center - (buffer + width) ≤ L ell ∧
          L ell ≤ center + (buffer + width) := by
      intro ell hell
      let u : ℝ := max (|L ell - center| - buffer) 0
      change Nat.floor (u / width) = 0 at hell
      have hupp : u / width < (0 : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one (u / width)
        rw [hell] at h
        simpa only [Nat.cast_zero] using h
      have hupp' : u < width := by
        have h := (div_lt_iff₀ hwidth).mp hupp
        simpa using h
      have habs : |L ell - center| < buffer + width := by
        have hle : |L ell - center| - buffer ≤ u := le_max_left _ _
        linarith
      rw [abs_lt] at habs
      constructor <;> linarith
    calc
      countVectorMass P (fun ell ↦
          bufferedAbsoluteCellIndex center buffer width (L ell) = 0) ≤
        countVectorMass P (fun ell ↦
          center - (buffer + width) ≤ L ell ∧
          L ell ≤ center + (buffer + width)) :=
        countVectorMass_mono P hsubset
      _ ≤ rate * ((center + (buffer + width)) -
          (center - (buffer + width))) := hinterval _ _ (by nlinarith)
      _ = 2 * rate * (buffer + width) := by ring
  · let leftA : ℝ := center - (buffer + ((j : ℝ) + 1) * width)
    let rightA : ℝ := center + buffer + (j : ℝ) * width
    have hsubset : ∀ ell,
        bufferedAbsoluteCellIndex center buffer width (L ell) = j →
          (leftA ≤ L ell ∧ L ell ≤ leftA + width) ∨
          (rightA ≤ L ell ∧ L ell ≤ rightA + width) := by
      intro ell hell
      let z : ℝ := L ell - center
      let u : ℝ := max (|z| - buffer) 0
      have hu0 : 0 ≤ u := le_max_right _ _
      have hlo : (j : ℝ) ≤ u / width := by
        rw [← hell]
        exact Nat.floor_le (div_nonneg hu0 hwidth.le)
      have hhi : u / width < (j : ℝ) + 1 := by
        rw [← hell]
        exact Nat.lt_floor_add_one _
      have hlo' : (j : ℝ) * width ≤ u := (le_div_iff₀ hwidth).mp hlo
      have hhi' : u < ((j : ℝ) + 1) * width :=
        (div_lt_iff₀ hwidth).mp hhi
      have huPos : 0 < u := lt_of_lt_of_le
        (mul_pos (by exact_mod_cast hj) hwidth) hlo'
      have hzbuf : 0 ≤ |z| - buffer := by
        by_contra hneg
        have : u = 0 := by
          dsimp only [u]
          rw [max_eq_right (le_of_not_ge hneg)]
        linarith
      have hu : u = |z| - buffer := by
        dsimp only [u]
        rw [max_eq_left hzbuf]
      rw [hu] at hlo' hhi'
      by_cases hz : 0 ≤ z
      · right
        rw [abs_of_nonneg hz] at hlo' hhi'
        dsimp only [z, rightA] at hlo' hhi' ⊢
        constructor <;> linarith
      · left
        have hz' : z < 0 := lt_of_not_ge hz
        rw [abs_of_neg hz'] at hlo' hhi'
        dsimp only [z, leftA] at hlo' hhi' ⊢
        constructor <;> linarith
    have hleftMass : countVectorMass P (fun ell ↦
        leftA ≤ L ell ∧ L ell ≤ leftA + width) ≤ rate * width := by
      have hw : width ≤ leftA + width - leftA := by
        rw [show leftA + width - leftA = width by ring]
      convert hinterval leftA (leftA + width) hw using 1 <;> ring
    have hrightMass : countVectorMass P (fun ell ↦
        rightA ≤ L ell ∧ L ell ≤ rightA + width) ≤ rate * width := by
      have hw : width ≤ rightA + width - rightA := by
        rw [show rightA + width - rightA = width by ring]
      convert hinterval rightA (rightA + width) hw using 1 <;> ring
    calc
      countVectorMass P (fun ell ↦
          bufferedAbsoluteCellIndex center buffer width (L ell) = j) ≤
        countVectorMass P (fun ell ↦
          (leftA ≤ L ell ∧ L ell ≤ leftA + width) ∨
          (rightA ≤ L ell ∧ L ell ≤ rightA + width)) :=
        countVectorMass_mono P hsubset
      _ ≤ countVectorMass P (fun ell ↦
            leftA ≤ L ell ∧ L ell ≤ leftA + width) +
          countVectorMass P (fun ell ↦
            rightA ≤ L ell ∧ L ell ≤ rightA + width) :=
        countVectorMass_union_le P _ _
      _ ≤ rate * width + rate * width :=
        add_le_add hleftMass hrightMass
      _ ≤ 2 * rate * (buffer + width) := by
        nlinarith [mul_nonneg hrate hbuffer]

/-- Predicate-restricted buffered-cell estimate.  It is used in the
shift-dominated branch with `R` the fixed Claim 12.2 moment threshold for
one dyadic level. -/
lemma countVectorMass_and_bufferedAbsoluteCellIndex_le
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L : BucketCountVector P → ℝ)
    (R : BucketCountVector P → Prop)
    {center buffer width rate : ℝ}
    (hbuffer : 0 ≤ buffer) (hwidth : 0 < width) (hrate : 0 ≤ rate)
    (hinterval : ∀ a b : ℝ, width ≤ b - a →
      countVectorMass P (fun ell ↦ R ell ∧ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a))
    (j : ℕ) :
    countVectorMass P (fun ell ↦ R ell ∧
      bufferedAbsoluteCellIndex center buffer width (L ell) = j) ≤
      2 * rate * (buffer + width) := by
  rcases j.eq_zero_or_pos with rfl | hj
  · have hsubset : ∀ ell,
        R ell ∧ bufferedAbsoluteCellIndex center buffer width (L ell) = 0 →
          R ell ∧ center - (buffer + width) ≤ L ell ∧
            L ell ≤ center + (buffer + width) := by
      intro ell hell
      refine ⟨hell.1, ?_⟩
      let u : ℝ := max (|L ell - center| - buffer) 0
      have hcell := hell.2
      change Nat.floor (u / width) = 0 at hcell
      have hupp : u / width < (0 : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one (u / width)
        rw [hcell] at h
        simpa only [Nat.cast_zero] using h
      have hupp' : u < width := by
        have h := (div_lt_iff₀ hwidth).mp hupp
        simpa using h
      have habs : |L ell - center| < buffer + width := by
        have hle : |L ell - center| - buffer ≤ u := le_max_left _ _
        linarith
      rw [abs_lt] at habs
      constructor <;> linarith
    calc
      countVectorMass P (fun ell ↦ R ell ∧
          bufferedAbsoluteCellIndex center buffer width (L ell) = 0) ≤
        countVectorMass P (fun ell ↦ R ell ∧
          center - (buffer + width) ≤ L ell ∧
          L ell ≤ center + (buffer + width)) :=
        countVectorMass_mono P hsubset
      _ ≤ rate * ((center + (buffer + width)) -
          (center - (buffer + width))) := hinterval _ _ (by nlinarith)
      _ = 2 * rate * (buffer + width) := by ring
  · let leftA : ℝ := center - (buffer + ((j : ℝ) + 1) * width)
    let rightA : ℝ := center + buffer + (j : ℝ) * width
    have hsubset : ∀ ell,
        R ell ∧ bufferedAbsoluteCellIndex center buffer width (L ell) = j →
          (R ell ∧ leftA ≤ L ell ∧ L ell ≤ leftA + width) ∨
          (R ell ∧ rightA ≤ L ell ∧ L ell ≤ rightA + width) := by
      intro ell hell
      let z : ℝ := L ell - center
      let u : ℝ := max (|z| - buffer) 0
      have hu0 : 0 ≤ u := le_max_right _ _
      have hlo : (j : ℝ) ≤ u / width := by
        rw [← hell.2]
        exact Nat.floor_le (div_nonneg hu0 hwidth.le)
      have hhi : u / width < (j : ℝ) + 1 := by
        rw [← hell.2]
        exact Nat.lt_floor_add_one _
      have hlo' : (j : ℝ) * width ≤ u := (le_div_iff₀ hwidth).mp hlo
      have hhi' : u < ((j : ℝ) + 1) * width :=
        (div_lt_iff₀ hwidth).mp hhi
      have huPos : 0 < u := lt_of_lt_of_le
        (mul_pos (by exact_mod_cast hj) hwidth) hlo'
      have hzbuf : 0 ≤ |z| - buffer := by
        by_contra hneg
        have : u = 0 := by
          dsimp only [u]
          rw [max_eq_right (le_of_not_ge hneg)]
        linarith
      have hu : u = |z| - buffer := by
        dsimp only [u]
        rw [max_eq_left hzbuf]
      rw [hu] at hlo' hhi'
      by_cases hz : 0 ≤ z
      · right
        refine ⟨hell.1, ?_⟩
        rw [abs_of_nonneg hz] at hlo' hhi'
        dsimp only [z, rightA] at hlo' hhi' ⊢
        constructor <;> linarith
      · left
        refine ⟨hell.1, ?_⟩
        have hz' : z < 0 := lt_of_not_ge hz
        rw [abs_of_neg hz'] at hlo' hhi'
        dsimp only [z, leftA] at hlo' hhi' ⊢
        constructor <;> linarith
    have hleftMass : countVectorMass P (fun ell ↦
        R ell ∧ leftA ≤ L ell ∧ L ell ≤ leftA + width) ≤
        rate * width := by
      have hw : width ≤ leftA + width - leftA := by
        rw [show leftA + width - leftA = width by ring]
      convert hinterval leftA (leftA + width) hw using 1 <;> ring
    have hrightMass : countVectorMass P (fun ell ↦
        R ell ∧ rightA ≤ L ell ∧ L ell ≤ rightA + width) ≤
        rate * width := by
      have hw : width ≤ rightA + width - rightA := by
        rw [show rightA + width - rightA = width by ring]
      convert hinterval rightA (rightA + width) hw using 1 <;> ring
    calc
      countVectorMass P (fun ell ↦ R ell ∧
          bufferedAbsoluteCellIndex center buffer width (L ell) = j) ≤
        countVectorMass P (fun ell ↦
          (R ell ∧ leftA ≤ L ell ∧ L ell ≤ leftA + width) ∨
          (R ell ∧ rightA ≤ L ell ∧ L ell ≤ rightA + width)) :=
        countVectorMass_mono P hsubset
      _ ≤ countVectorMass P (fun ell ↦
            R ell ∧ leftA ≤ L ell ∧ L ell ≤ leftA + width) +
          countVectorMass P (fun ell ↦
            R ell ∧ rightA ≤ L ell ∧ L ell ≤ rightA + width) :=
        countVectorMass_union_le P _ _
      _ ≤ rate * width + rate * width :=
        add_le_add hleftMass hrightMass
      _ ≤ 2 * rate * (buffer + width) := by
        nlinarith [mul_nonneg hrate hbuffer]

/-- A moderate absolute linear-shift region has the interval mass predicted
by `(12.7)`.  The predicate may impose additional restrictions. -/
lemma countVectorMass_subset_abs_sub_le
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L : BucketCountVector P → ℝ)
    (Good : BucketCountVector P → Prop)
    {center width radius rate : ℝ} (hwidth : width ≤ 2 * radius)
    (hGood : ∀ ell, Good ell → |L ell - center| ≤ radius)
    (hinterval : ∀ a b : ℝ, width ≤ b - a →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a)) :
    countVectorMass P Good ≤ 2 * rate * radius := by
  calc
    countVectorMass P Good ≤ countVectorMass P (fun ell ↦
        center - radius ≤ L ell ∧ L ell ≤ center + radius) := by
      apply countVectorMass_mono P
      intro ell hgood
      have habs := hGood ell hgood
      rw [abs_le] at habs
      constructor <;> linarith
    _ ≤ rate * ((center + radius) - (center - radius)) :=
      hinterval _ _ (by nlinarith)
    _ = 2 * rate * radius := by ring

/-- The Frobenius lower bound selects an admissible fixed multiple of the
zero-count scale as the cell width, and `(12.7)` then bounds every such
absolute-distance cell. -/
lemma countVectorMass_zeroCountScale_absoluteCell_le
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    {q : ℕ} (hq : 0 < q) (P : BucketPartition α κ)
    (L : BucketCountVector P → ℝ)
    {H rho Cmass : ℝ} (hH : 0 < H) (hrho : 0 < rho)
    (F : Matrix (Fin q) (Fin q) ℝ) (f0 : Fin q → ℝ)
    (hFrob : rho * (q : ℝ) ^ 2 ≤ frobeniusSq F)
    (hmass : ∀ a b : ℝ, a < b →
      4 * ((2 * H + 1) + 1) * (q : ℝ) ≤ (b - a) * Real.pi →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        Cmass * (b - a) * scale q (-(3 : ℝ) / 2)) :
    let sigma0 := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f0)
    let width := 4 * ((2 * H + 1) + 1) /
      (Real.pi * Real.sqrt rho) * sigma0
    ∀ center : ℝ, ∀ j : ℕ,
      countVectorMass P (fun ell ↦
        absoluteCellIndex center width (L ell) = j) ≤
      2 * (Cmass * width * scale q (-(3 : ℝ) / 2)) := by
  let sigma0 := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f0)
  let width := 4 * ((2 * H + 1) + 1) /
    (Real.pi * Real.sqrt rho) * sigma0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlower : Real.sqrt rho * (q : ℝ) ≤ sigma0 := by
    exact sqrt_mul_le_zeroCountScale_of_frobenius F f0
      hrho.le hqR.le hFrob
  have hsigma0 : 0 < sigma0 := lt_of_lt_of_le
    (mul_pos (Real.sqrt_pos.2 hrho) hqR) hlower
  have hwidthPos : 0 < width := by
    dsimp only [width]
    positivity
  have hwidthAdmissible :
      4 * ((2 * H + 1) + 1) * (q : ℝ) ≤ width * Real.pi := by
    dsimp only [width]
    exact countVector_interval_width_of_zeroCountScale hH hrho hlower
  change ∀ center : ℝ, ∀ j : ℕ,
    countVectorMass P (fun ell ↦
      absoluteCellIndex center width (L ell) = j) ≤
    2 * (Cmass * width * scale q (-(3 : ℝ) / 2))
  intro center j
  apply countVectorMass_absoluteCellIndex_le_two P L hwidthPos
  intro a
  have h := hmass a (a + width) (by linarith) (by
    convert hwidthAdmissible using 1 <;> ring)
  convert h using 1 <;> ring

/-- Finite cell summation against an arbitrary nonnegative summable
envelope. -/
lemma sum_weight_mul_summable_index_le
    {D : Type*} [Fintype D] (weight : D → ℝ) (idx : D → ℕ)
    (kernel : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hkernel : ∀ j, 0 ≤ kernel j) (hsum : Summable kernel)
    (hmass : ∀ j : ℕ, ∑ d : D with idx d = j, weight d ≤ A) :
    ∑ d : D, weight d * kernel (idx d) ≤ A * ∑' j, kernel j := by
  classical
  let J : Finset ℕ := Finset.univ.image idx
  have hmaps : ∀ d ∈ (Finset.univ : Finset D), idx d ∈ J := by
    intro d hd
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
  have hdecomp :
      ∑ d : D, weight d * kernel (idx d) =
        ∑ j ∈ J, kernel j *
          (∑ d : D with idx d = j, weight d) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun d : D ↦ weight d * kernel (idx d))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdj : idx d = j := (Finset.mem_filter.mp hd).2
    rw [hdj]
    ring
  rw [hdecomp]
  calc
    ∑ j ∈ J, kernel j * (∑ d : D with idx d = j, weight d) ≤
        ∑ j ∈ J, kernel j * A := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmass j) (hkernel j)
    _ = A * ∑ j ∈ J, kernel j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ A * ∑' j, kernel j := by
      exact mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum J (fun j hj ↦ hkernel j)) hA

/-- Fiber-dependent form of summable-index bookkeeping.  This is the
double-cell engine used in the shift-dominated branch of Step 7. -/
lemma sum_weight_mul_index_le_tsum_fiberBound
    {D J : Type*} [Fintype D] [Countable J] [DecidableEq J]
    (weight : D → ℝ) (idx : D → J)
    (fiberBound kernel : J → ℝ)
    (hbound : ∀ j, 0 ≤ fiberBound j)
    (hkernel : ∀ j, 0 ≤ kernel j)
    (hsum : Summable (fun j ↦ fiberBound j * kernel j))
    (hmass : ∀ j : J, ∑ d : D with idx d = j, weight d ≤ fiberBound j) :
    ∑ d : D, weight d * kernel (idx d) ≤
      ∑' j : J, fiberBound j * kernel j := by
  classical
  let S : Finset J := Finset.univ.image idx
  have hmaps : ∀ d ∈ (Finset.univ : Finset D), idx d ∈ S := by
    intro d hd
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
  have hdecomp :
      ∑ d : D, weight d * kernel (idx d) =
        ∑ j ∈ S, kernel j *
          (∑ d : D with idx d = j, weight d) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun d : D ↦ weight d * kernel (idx d))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdj : idx d = j := (Finset.mem_filter.mp hd).2
    rw [hdj]
    ring
  rw [hdecomp]
  calc
    ∑ j ∈ S, kernel j *
          (∑ d : D with idx d = j, weight d) ≤
        ∑ j ∈ S, fiberBound j * kernel j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [mul_comm (fiberBound j)]
      exact mul_le_mul_of_nonneg_left (hmass j) (hkernel j)
    _ ≤ ∑' j : J, fiberBound j * kernel j :=
      hsum.sum_le_tsum S (fun j hj ↦ mul_nonneg (hbound j) (hkernel j))

/-- Weighted conditional form of summation against any nonnegative
summable cell envelope. -/
lemma weighted_summable_cell_bound
    {D : Type*} [Fintype D]
    (weight cond : D → ℝ) (idx : D → ℕ) (kernel : ℕ → ℝ)
    {A P c sigma err : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hsigma : 0 < sigma)
    (herr : 0 ≤ err) (hkernel : ∀ j, 0 ≤ kernel j)
    (hsum : Summable kernel)
    (hweight : ∀ d, 0 ≤ weight d)
    (htotal : ∑ d, weight d ≤ P)
    (hmass : ∀ j : ℕ, ∑ d : D with idx d = j, weight d ≤ A)
    (hcond : ∀ d, cond d ≤ c * (kernel (idx d) / sigma + err)) :
    ∑ d, weight d * cond d ≤
      c * (A * (∑' j, kernel j) / sigma + P * err) := by
  have hcells := sum_weight_mul_summable_index_le
    weight idx kernel hA hkernel hsum hmass
  calc
    ∑ d, weight d * cond d ≤
        ∑ d, weight d * (c * (kernel (idx d) / sigma + err)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hcond d) (hweight d)
    _ = ∑ d, c *
          (weight d * kernel (idx d) / sigma + weight d * err) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = c * ∑ d,
          (weight d * kernel (idx d) / sigma + weight d * err) := by
      rw [Finset.mul_sum]
    _ = c * ((∑ d, weight d * kernel (idx d)) / sigma +
          (∑ d, weight d) * err) := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
    _ ≤ c * (A * (∑' j, kernel j) / sigma + P * err) := by
      apply mul_le_mul_of_nonneg_left _ hc
      gcongr

/-- Finite cell summation against a geometric envelope.  This is the
algebraic core of the `j`-cell summation in Step 7: a uniform mass bound on
every cell cancels the conditional scale, while the geometric decay sums to
a fixed constant. -/
lemma sum_weight_mul_geometric_index_le
    {D : Type*} [Fintype D] (weight : D → ℝ) (idx : D → ℕ)
    {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) (hr1 : r < 1)
    (hmass : ∀ j : ℕ,
      ∑ d : D with idx d = j, weight d ≤ A) :
    ∑ d : D, weight d * r ^ idx d ≤ A * (1 - r)⁻¹ := by
  classical
  let J : Finset ℕ := Finset.univ.image idx
  have hmaps : ∀ d ∈ (Finset.univ : Finset D), idx d ∈ J := by
    intro d hd
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
  have hdecomp :
      ∑ d : D, weight d * r ^ idx d =
        ∑ j ∈ J, r ^ j * (∑ d : D with idx d = j, weight d) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun d : D ↦ weight d * r ^ idx d)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdj : idx d = j := (Finset.mem_filter.mp hd).2
    rw [hdj]
    ring
  rw [hdecomp]
  calc
    ∑ j ∈ J, r ^ j * (∑ d : D with idx d = j, weight d) ≤
        ∑ j ∈ J, r ^ j * A := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmass j) (pow_nonneg hr j)
    _ = A * ∑ j ∈ J, r ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ A * ∑' j : ℕ, r ^ j := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact (summable_geometric_of_lt_one hr hr1).sum_le_tsum J
        (fun j hj ↦ pow_nonneg hr j)
    _ = A * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr hr1]

/-- Weighted conditional form of the comparable-scale cell summation. -/
lemma weighted_geometric_cell_bound
    {D : Type*} [Fintype D]
    (weight cond : D → ℝ) (idx : D → ℕ)
    {A P c r sigma err : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hr1 : r < 1) (hsigma : 0 < sigma)
    (herr : 0 ≤ err)
    (hweight : ∀ d, 0 ≤ weight d)
    (htotal : ∑ d, weight d ≤ P)
    (hmass : ∀ j : ℕ, ∑ d : D with idx d = j, weight d ≤ A)
    (hcond : ∀ d, cond d ≤ c * (r ^ idx d / sigma + err)) :
    ∑ d, weight d * cond d ≤
      c * (A * (1 - r)⁻¹ / sigma + P * err) := by
  have hgeom := sum_weight_mul_geometric_index_le
    weight idx hA hr hr1 hmass
  calc
    ∑ d, weight d * cond d ≤
        ∑ d, weight d * (c * (r ^ idx d / sigma + err)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hcond d) (hweight d)
    _ = ∑ d, c * (weight d * r ^ idx d / sigma + weight d * err) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = c * ∑ d, (weight d * r ^ idx d / sigma + weight d * err) := by
      rw [Finset.mul_sum]
    _ = c * ((∑ d, weight d * r ^ idx d) / sigma +
          (∑ d, weight d) * err) := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
    _ ≤ c * (A * (1 - r)⁻¹ / sigma + P * err) := by
      apply mul_le_mul_of_nonneg_left _ hc
      gcongr

/-- On a comparable conditional scale, the Cauchy and exponential terms in
Claim 12.1 are dominated by a fixed summable kernel of the buffered cell
index.  The harmless hypothesis `1 ≤ sigma0` is available in Step 7 from
the robust Frobenius lower bound. -/
lemma claim121_comparable_cell_kernel_bound
    {B eta sigma0 sigma kappa x : ℝ} {j : ℕ}
    (hB : 0 ≤ B) (heta : 0 < eta) (hsigma0 : 1 ≤ sigma0)
    (hsigmaLower : sigma0 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 2 * sigma0) (hkappa : 0 < kappa)
    (hx : (j : ℝ) * kappa * sigma0 / 2 ≤ |x|) :
    B ^ 2 / (x ^ 2 + sigma ^ 2) +
        (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
      ((4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1) +
          (2 * B / eta) * Real.exp (-eta * kappa * (j : ℝ) / 8)) /
        sigma0 := by
  have hsigma0Pos : 0 < sigma0 := lt_of_lt_of_le zero_lt_one hsigma0
  have hsigma : 0 < sigma := lt_of_lt_of_le
    (div_pos hsigma0Pos (by norm_num)) hsigmaLower
  have hj : 0 ≤ (j : ℝ) := by positivity
  have hkappa0 : 0 ≤ kappa := hkappa.le
  have hbase : 0 < kappa ^ 2 * (j : ℝ) ^ 2 + 1 := by positivity
  have hxSq : ((j : ℝ) * kappa * sigma0 / 2) ^ 2 ≤ x ^ 2 := by
    have hx0 : 0 ≤ (j : ℝ) * kappa * sigma0 / 2 := by positivity
    have := sq_le_sq₀ hx0 (abs_nonneg x) |>.2 hx
    simpa only [sq_abs] using this
  have hsigmaSq : (sigma0 / 2) ^ 2 ≤ sigma ^ 2 := by
    exact sq_le_sq₀ (by positivity) hsigma.le |>.2 hsigmaLower
  have hden : sigma0 * (kappa ^ 2 * (j : ℝ) ^ 2 + 1) ≤
      4 * (x ^ 2 + sigma ^ 2) := by
    have hsigmaSq' : sigma0 ≤ sigma0 ^ 2 := by nlinarith
    have hbase0 : 0 ≤ kappa ^ 2 * (j : ℝ) ^ 2 + 1 := hbase.le
    have hmul := mul_le_mul_of_nonneg_right hsigmaSq' hbase0
    nlinarith [hxSq, hsigmaSq]
  have hdenPos : 0 < x ^ 2 + sigma ^ 2 := by positivity
  have htargetDenPos : 0 <
      (kappa ^ 2 * (j : ℝ) ^ 2 + 1) * sigma0 :=
    mul_pos hbase hsigma0Pos
  have hrat : B ^ 2 / (x ^ 2 + sigma ^ 2) ≤
      ((4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1)) / sigma0 := by
    rw [div_div]
    apply (div_le_div_iff₀ hdenPos htargetDenPos).2
    have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith [mul_le_mul_of_nonneg_left hden hBsq]
  have hprod : (j : ℝ) * kappa * sigma ≤ 4 * |x| := by
    have hmul := mul_le_mul_of_nonneg_left hsigmaUpper
      (mul_nonneg hj hkappa0)
    nlinarith
  have hexpArg : eta * kappa * (j : ℝ) / 8 ≤
      eta * |x| / (2 * sigma) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsigma)).2
    have hmul := mul_le_mul_of_nonneg_left hprod heta.le
    nlinarith
  have hexp : Real.exp (-eta * |x| / (2 * sigma)) ≤
      Real.exp (-eta * kappa * (j : ℝ) / 8) := by
    apply Real.exp_le_exp.mpr
    calc
      -eta * |x| / (2 * sigma) =
          -(eta * |x| / (2 * sigma)) := by ring
      _ ≤ -(eta * kappa * (j : ℝ) / 8) := neg_le_neg hexpArg
      _ = -eta * kappa * (j : ℝ) / 8 := by ring
  have hcoef : B / (eta * sigma) ≤ (2 * B / eta) / sigma0 := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos heta hsigma)
      (mul_pos heta hsigma0Pos)).2
    nlinarith [mul_le_mul_of_nonneg_left hsigmaLower hB]
  have hexpTerm :
      (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
        ((2 * B / eta) * Real.exp (-eta * kappa * (j : ℝ) / 8)) /
          sigma0 := by
    calc
      (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
          ((2 * B / eta) / sigma0) *
            Real.exp (-eta * |x| / (2 * sigma)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ ≤ ((2 * B / eta) / sigma0) *
            Real.exp (-eta * kappa * (j : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((2 * B / eta) *
            Real.exp (-eta * kappa * (j : ℝ) / 8)) / sigma0 := by ring
  calc
    B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
        ((4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1)) / sigma0 +
          ((2 * B / eta) * Real.exp (-eta * kappa * (j : ℝ) / 8)) /
            sigma0 := add_le_add hrat hexpTerm
    _ = ((4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1) +
          (2 * B / eta) * Real.exp (-eta * kappa * (j : ℝ) / 8)) /
        sigma0 := by ring

/-- The explicit summable envelope produced by the comparable-scale
Claim 12.1 estimate. -/
noncomputable def claim121ComparableCellKernel
    (B eta kappa : ℝ) (j : ℕ) : ℝ :=
  (4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1) +
    (2 * B / eta) * Real.exp (-eta * kappa * (j : ℝ) / 8)

/-- A fixed lower scale and a possibly larger dyadic upper scale still give
the same summable spatial kernel if the linear cells are enlarged in
proportion to the upper scale. -/
lemma claim121_bounded_scale_cell_kernel_bound
    {B eta base S sigma x : ℝ} {j : ℕ}
    (hB : 0 ≤ B) (heta : 0 < eta) (hbase : 1 ≤ base)
    (hS : 1 ≤ S) (hsigmaLower : base ≤ sigma)
    (hsigmaUpper : sigma ≤ S * base)
    (hx : (j : ℝ) * (4 * S * base) / 2 ≤ |x|) :
    B ^ 2 / (x ^ 2 + sigma ^ 2) +
        (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
      claim121ComparableCellKernel B eta 1 j / base := by
  have hbasePos : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  have hSPos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hsigma : 0 < sigma := hbasePos.trans_le hsigmaLower
  have hj : 0 ≤ (j : ℝ) := by positivity
  have hjbase : 0 ≤ (j : ℝ) * base := mul_nonneg hj hbasePos.le
  have hlinear : (j : ℝ) * base ≤ |x| := by
    have hfactor : (1 : ℝ) ≤ 2 * S := by linarith
    have hmul := mul_le_mul_of_nonneg_left hfactor hjbase
    calc
      (j : ℝ) * base ≤ ((j : ℝ) * base) * (2 * S) := by
        simpa only [mul_one] using hmul
      _ = (j : ℝ) * (4 * S * base) / 2 := by ring
      _ ≤ |x| := hx
  have hxSq : ((j : ℝ) * base) ^ 2 ≤ x ^ 2 := by
    have := sq_le_sq₀ hjbase (abs_nonneg x) |>.2 hlinear
    simpa only [sq_abs] using this
  have hsigmaSq : base ^ 2 ≤ sigma ^ 2 :=
    sq_le_sq₀ hbasePos.le hsigma.le |>.2 hsigmaLower
  have hbaseSq : base ≤ base ^ 2 := by nlinarith
  have hden : base * ((j : ℝ) ^ 2 + 1) ≤ x ^ 2 + sigma ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hbaseSq
      (show 0 ≤ (j : ℝ) ^ 2 + 1 by positivity)]
  have hdenPos : 0 < x ^ 2 + sigma ^ 2 := by positivity
  have htargetDenPos : 0 < ((j : ℝ) ^ 2 + 1) * base := by positivity
  have hrat : B ^ 2 / (x ^ 2 + sigma ^ 2) ≤
      ((4 * B ^ 2) / ((j : ℝ) ^ 2 + 1)) / base := by
    rw [div_div]
    apply (div_le_div_iff₀ hdenPos htargetDenPos).2
    have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith [mul_le_mul_of_nonneg_left hden hBsq]
  have hprod : (j : ℝ) * sigma ≤ 4 * |x| := by
    have hmul := mul_le_mul_of_nonneg_left hsigmaUpper hj
    have hx' : 2 * ((j : ℝ) * (S * base)) ≤ |x| := by
      nlinarith [hx]
    nlinarith
  have hexpArg : eta * (j : ℝ) / 8 ≤ eta * |x| / (2 * sigma) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hsigma)).2
    have hmul := mul_le_mul_of_nonneg_left hprod heta.le
    nlinarith
  have hexp : Real.exp (-eta * |x| / (2 * sigma)) ≤
      Real.exp (-eta * (j : ℝ) / 8) := by
    apply Real.exp_le_exp.mpr
    calc
      -eta * |x| / (2 * sigma) =
          -(eta * |x| / (2 * sigma)) := by ring
      _ ≤ -(eta * (j : ℝ) / 8) := neg_le_neg hexpArg
      _ = -eta * (j : ℝ) / 8 := by ring
  have hcoef : B / (eta * sigma) ≤ (2 * B / eta) / base := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos heta hsigma)
      (mul_pos heta hbasePos)).2
    have hdenom := mul_le_mul_of_nonneg_left hsigmaLower heta.le
    have hscaled := mul_le_mul_of_nonneg_left hdenom hB
    have hpos : 0 ≤ B * (eta * sigma) := by positivity
    nlinarith
  have hexpTerm :
      (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
        ((2 * B / eta) * Real.exp (-eta * (j : ℝ) / 8)) / base := by
    calc
      (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
          ((2 * B / eta) / base) *
            Real.exp (-eta * |x| / (2 * sigma)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ ≤ ((2 * B / eta) / base) *
            Real.exp (-eta * (j : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((2 * B / eta) * Real.exp (-eta * (j : ℝ) / 8)) / base := by
        ring
  unfold claim121ComparableCellKernel
  simp only [one_pow, one_mul, mul_one]
  calc
    B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) * Real.exp (-eta * |x| / (2 * sigma)) ≤
        ((4 * B ^ 2) / ((j : ℝ) ^ 2 + 1)) / base +
          ((2 * B / eta) * Real.exp (-eta * (j : ℝ) / 8)) / base :=
      add_le_add hrat hexpTerm
    _ = ((4 * B ^ 2) / ((j : ℝ) ^ 2 + 1) +
          (2 * B / eta) * Real.exp (-eta * (j : ℝ) / 8)) / base := by
      ring

lemma claim121ComparableCellKernel_nonneg
    {B eta kappa : ℝ} (hB : 0 ≤ B) (heta : 0 < eta) (j : ℕ) :
    0 ≤ claim121ComparableCellKernel B eta kappa j := by
  unfold claim121ComparableCellKernel
  positivity

lemma summable_claim121ComparableCellKernel
    {B eta kappa : ℝ} (heta : 0 < eta) (hkappa : 0 < kappa) :
    Summable (claim121ComparableCellKernel B eta kappa) := by
  have hp : Summable (fun n : ℕ ↦
      (4 * B ^ 2 / kappa ^ 2) * (1 / (n : ℝ) ^ 2)) :=
    ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)).mul_left _
  have hp' : Summable (fun n : ℕ ↦
      (4 * B ^ 2 / kappa ^ 2) * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hshift := hp.comp_injective (i := fun n : ℕ ↦ n + 1) (by
      intro a b hab
      exact Nat.add_right_cancel hab)
    change Summable (fun n : ℕ ↦
      (4 * B ^ 2 / kappa ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) at hshift
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hrat : Summable (fun j : ℕ ↦
      (4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1)) := by
    apply (summable_nat_add_iff 1).mp
    refine hp'.of_norm_bounded (fun n ↦ ?_)
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hk2 : 0 < kappa ^ 2 := sq_pos_of_pos hkappa
    have hnum : 0 ≤ 4 * B ^ 2 := by positivity
    apply (div_le_iff₀ (by positivity :
      0 < kappa ^ 2 * ((n : ℝ) + 1) ^ 2 + 1)).2
    field_simp
    nlinarith [sq_nonneg B]
  have hexp : Summable (fun j : ℕ ↦
      Real.exp (-eta * kappa * (j : ℝ) / 8)) := by
    have h := Real.summable_exp_nat_mul_iff.mpr
      (show -eta * kappa / 8 < 0 by
        nlinarith [mul_pos heta hkappa])
    convert h using 1
    funext j
    congr 1
    ring
  change Summable (fun j : ℕ ↦
    (4 * B ^ 2) / (kappa ^ 2 * (j : ℝ) ^ 2 + 1) +
      (2 * B / eta) * Real.exp (-eta * kappa * (j : ℝ) / 8))
  exact hrat.add (hexp.mul_left (2 * B / eta))

/-- Some dyadic power of two dominates every real scale once the base scale
is positive.  This is the existence input for the concrete stopping level
used in the shift-dominated part of Step 7. -/
private lemma exists_claim121_dyadic_level (base z : ℝ) (hbase : 0 < base) :
    ∃ i : ℕ, z < (2 : ℝ) ^ (i + 1) * base := by
  obtain ⟨N, hN⟩ := exists_nat_gt (z / base)
  have hNpow : (N : ℝ) < (2 : ℝ) ^ N := by
    exact_mod_cast Nat.lt_two_pow_self
  refine ⟨N, ?_⟩
  have hz : z < (N : ℝ) * base := by
    exact (div_lt_iff₀ hbase).mp hN
  calc
    z < (N : ℝ) * base := hz
    _ < (2 : ℝ) ^ N * base :=
      mul_lt_mul_of_pos_right hNpow hbase
    _ < (2 : ℝ) ^ (N + 1) * base := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]

/-- The first dyadic level whose next power of two exceeds `z / base`.
The fallback branch is never used when `base > 0`. -/
noncomputable def claim121DyadicLevel (base z : ℝ) : ℕ :=
  if h : ∃ i : ℕ, z < (2 : ℝ) ^ (i + 1) * base then Nat.find h else 0

/-- Dyadic level of a nonnegative Claim 12.2 shift moment. -/
noncomputable def claim121ShiftDyadicLevel (base W : ℝ) : ℕ :=
  claim121DyadicLevel base (Real.sqrt W)

/-- Spatial cell at the scale of the dyadic shift level.  The buffer
absorbs the quadratic center shift and the width is four times larger,
leaving the fixed kernel used by `weighted_claim121_bounded_scale_double_cells`. -/
noncomputable def claim121ShiftSpatialCell
    (center base W L : ℝ) : ℕ :=
  let s := (2 : ℝ) ^ claim121ShiftDyadicLevel base W * base
  bufferedAbsoluteCellIndex center (4 * s) (16 * s) L

lemma claim121DyadicLevel_upper {base z : ℝ} (hbase : 0 < base) :
    z < (2 : ℝ) ^ (claim121DyadicLevel base z + 1) * base := by
  let hex := exists_claim121_dyadic_level base z hbase
  rw [claim121DyadicLevel, dif_pos hex]
  exact Nat.find_spec hex

lemma claim121DyadicLevel_lower {base z : ℝ} (hbase : 0 < base)
    (hz : base ≤ z) :
    (2 : ℝ) ^ claim121DyadicLevel base z * base ≤ z := by
  let hex := exists_claim121_dyadic_level base z hbase
  rw [claim121DyadicLevel, dif_pos hex]
  let i := Nat.find hex
  change (2 : ℝ) ^ i * base ≤ z
  rcases i.eq_zero_or_pos with hzero | hi
  · rw [hzero]
    simpa using hz
  · obtain ⟨k, hik⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have hk : k < Nat.find hex := by
      dsimp only [i] at hik
      omega
    have hnot := Nat.find_min hex hk
    rw [hik]
    exact le_of_not_gt hnot

/-- On a shift-dominated outcome, the concrete stopping level supplies the
fixed threshold to which Claim 12.2 is applied. -/
lemma claim121DyadicLevel_sqrt_sq_lower {base W : ℝ}
    (hbase : 0 < base) (hW : 0 ≤ W) (hbaseSq : base ^ 2 ≤ W) :
    ((2 : ℝ) ^ claim121DyadicLevel base (Real.sqrt W) * base) ^ 2 ≤ W := by
  have hbaseSqrt : base ≤ Real.sqrt W := by
    apply (sq_le_sq₀ hbase.le (Real.sqrt_nonneg W)).mp
    rw [Real.sq_sqrt hW]
    exact hbaseSq
  have hlower := claim121DyadicLevel_lower hbase hbaseSqrt
  have hscaleNonneg : 0 ≤
      (2 : ℝ) ^ claim121DyadicLevel base (Real.sqrt W) * base := by
    positivity
  have hsqrt := Real.sq_sqrt hW
  nlinarith

/-- The same stopping level converts `sigma ≤ 2√W` into exactly the scale
upper bound expected by the two-index Claim 12.1 summation. -/
lemma claim121DyadicLevel_scale_upper {base W sigma : ℝ}
    (hbase : 0 < base) (hsigma : sigma ≤ 2 * Real.sqrt W) :
    sigma ≤
      (4 * (2 : ℝ) ^ claim121DyadicLevel base (Real.sqrt W)) * base := by
  have hu := claim121DyadicLevel_upper
    (z := Real.sqrt W) hbase
  rw [pow_succ] at hu
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (claim121DyadicLevel base (Real.sqrt W))]

/-- The quadratic center shift is absorbed by half of the dyadic buffer.
This is the concrete bridge from the first summand in Claim 12.2 to the
buffered spatial cells. -/
lemma abs_le_two_mul_dyadic_of_sq_le {base W qshift : ℝ}
    (hbase : 0 < base) (hW : 0 ≤ W) (hq : qshift ^ 2 ≤ W) :
    |qshift| ≤
      2 * ((2 : ℝ) ^ claim121DyadicLevel base (Real.sqrt W) * base) := by
  have hqSqrt : |qshift| ≤ Real.sqrt W := by
    apply (sq_le_sq₀ (abs_nonneg qshift) (Real.sqrt_nonneg W)).mp
    rw [sq_abs, Real.sq_sqrt hW]
    exact hq
  have hu := claim121DyadicLevel_upper
    (z := Real.sqrt W) hbase
  rw [pow_succ] at hu
  nlinarith

/-- Abstract two-index summation for the shift-dominated branch.  A dyadic
Claim 12.2 mass bound contributes `2⁻ⁱ`, while the nonuniform Claim 12.1
bound contributes the summable spatial kernel. -/
lemma weighted_claim121_bounded_scale_double_cells
    {D : Type*} [Fintype D]
    (weight cond sigma x : D → ℝ) (level cell : D → ℕ)
    {A P c B eta base err : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (heta : 0 < eta) (hbase : 1 ≤ base) (herr : 0 ≤ err)
    (hweight : ∀ d, 0 ≤ weight d)
    (htotal : ∑ d, weight d ≤ P)
    (hmass : ∀ p : ℕ × ℕ,
      ∑ d : D with (level d, cell d) = p, weight d ≤
        A * (1 / 2 : ℝ) ^ p.1)
    (hsigmaLower : ∀ d, base ≤ sigma d)
    (hsigmaUpper : ∀ d,
      sigma d ≤ (4 * (2 : ℝ) ^ level d) * base)
    (hx : ∀ d,
      (cell d : ℝ) *
          (4 * (4 * (2 : ℝ) ^ level d) * base) / 2 ≤ |x d|)
    (hcond : ∀ d, cond d ≤ c *
      (B ^ 2 / (x d ^ 2 + sigma d ^ 2) +
        (B / (eta * sigma d)) *
          Real.exp (-eta * |x d| / (2 * sigma d)) + B * err)) :
    ∑ d, weight d * cond d ≤
      c * (((∑' p : ℕ × ℕ,
          (A * (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2) / base) +
        P * (B * err)) := by
  let fiberBound : ℕ × ℕ → ℝ := fun p ↦ A * (1 / 2 : ℝ) ^ p.1
  let kernel : ℕ × ℕ → ℝ := fun p ↦
    claim121ComparableCellKernel B eta 1 p.2
  have hgeom : Summable (fun i : ℕ ↦ (1 / 2 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hspatial := summable_claim121ComparableCellKernel
    (B := B) heta (by norm_num : (0 : ℝ) < 1)
  have hprod : Summable (fun p : ℕ × ℕ ↦
      (1 / 2 : ℝ) ^ p.1 * claim121ComparableCellKernel B eta 1 p.2) :=
    hgeom.mul_of_nonneg hspatial
      (fun i ↦ pow_nonneg (by norm_num) i)
      (claim121ComparableCellKernel_nonneg hB heta)
  have hsum : Summable (fun p : ℕ × ℕ ↦ fiberBound p * kernel p) := by
    have hscaled := hprod.mul_left A
    exact hscaled.congr (fun p ↦ by
      dsimp only [fiberBound, kernel]
      ring)
  have hmain :
      ∑ d : D, weight d * kernel (level d, cell d) ≤
        ∑' p : ℕ × ℕ, fiberBound p * kernel p := by
    exact sum_weight_mul_index_le_tsum_fiberBound weight
      (fun d ↦ (level d, cell d)) fiberBound kernel
      (fun p ↦ by dsimp only [fiberBound]; positivity)
      (fun p ↦ claim121ComparableCellKernel_nonneg hB heta p.2)
      hsum hmass
  have hpoint : ∀ d,
      B ^ 2 / (x d ^ 2 + sigma d ^ 2) +
          (B / (eta * sigma d)) *
            Real.exp (-eta * |x d| / (2 * sigma d)) ≤
        kernel (level d, cell d) / base := by
    intro d
    dsimp only [kernel]
    exact claim121_bounded_scale_cell_kernel_bound hB heta hbase
      (by
        have hp : (1 : ℝ) ≤ (2 : ℝ) ^ level d :=
          one_le_pow₀ (n := level d) (by norm_num)
        nlinarith)
      (hsigmaLower d) (hsigmaUpper d) (hx d)
  calc
    ∑ d, weight d * cond d ≤
        ∑ d, weight d * (c *
          (kernel (level d, cell d) / base + B * err)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (hweight d)
      apply (hcond d).trans
      apply mul_le_mul_of_nonneg_left _ hc
      simpa only [add_comm] using add_le_add_right (hpoint d) (B * err)
    _ = ∑ d, c * (weight d * kernel (level d, cell d) / base +
          weight d * (B * err)) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = c * ∑ d, (weight d * kernel (level d, cell d) / base +
          weight d * (B * err)) := by
      rw [Finset.mul_sum]
    _ = c * ((∑ d, weight d * kernel (level d, cell d)) / base +
          (∑ d, weight d) * (B * err)) := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
    _ ≤ c * ((∑' p : ℕ × ℕ, fiberBound p * kernel p) / base +
          P * (B * err)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      gcongr
    _ = c * (((∑' p : ℕ × ℕ,
          (A * (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2) / base) +
        P * (B * err)) := by rfl

/-- The two-index envelope factors into the geometric level sum and the
one-dimensional spatial kernel. -/
lemma tsum_claim121_dyadic_cell_kernel
    {A B eta : ℝ} (hB : 0 ≤ B) (heta : 0 < eta) :
    ∑' p : ℕ × ℕ,
        (A * (1 / 2 : ℝ) ^ p.1) *
          claim121ComparableCellKernel B eta 1 p.2 =
      2 * A * (∑' j : ℕ, claim121ComparableCellKernel B eta 1 j) := by
  have hgeom : Summable (fun i : ℕ ↦ (1 / 2 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hspatial := summable_claim121ComparableCellKernel
    (B := B) heta (by norm_num : (0 : ℝ) < 1)
  have hprod : Summable (fun p : ℕ × ℕ ↦
      (1 / 2 : ℝ) ^ p.1 * claim121ComparableCellKernel B eta 1 p.2) :=
    hgeom.mul_of_nonneg hspatial
      (fun i ↦ pow_nonneg (by norm_num) i)
      (claim121ComparableCellKernel_nonneg hB heta)
  have hfactor := hgeom.tsum_mul_tsum hspatial hprod
  have hgeomSum : (∑' i : ℕ, (1 / 2 : ℝ) ^ i) = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc
    (∑' p : ℕ × ℕ, (A * (1 / 2 : ℝ) ^ p.1) *
        claim121ComparableCellKernel B eta 1 p.2) =
      A * (∑' p : ℕ × ℕ, (1 / 2 : ℝ) ^ p.1 *
        claim121ComparableCellKernel B eta 1 p.2) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro p
          ring
    _ = A * ((∑' i : ℕ, (1 / 2 : ℝ) ^ i) *
        (∑' j : ℕ, claim121ComparableCellKernel B eta 1 j)) := by
          rw [hfactor]
    _ = 2 * A * (∑' j : ℕ,
        claim121ComparableCellKernel B eta 1 j) := by rw [hgeomSum]; ring

/-- The robust Frobenius scale turns the remaining `√q / base²` factor
into the target `q⁻³ᐟ²` rate. -/
lemma sqrt_card_div_sq_le_scale_neg_three_halves
    {q : ℕ} (hq : 0 < q) {rho base : ℝ} (hrho : 0 < rho)
    (hbaseSq : 2 * rho * (q : ℝ) ^ 2 ≤ base ^ 2) :
    Real.sqrt q / base ^ 2 ≤
      (1 / (2 * rho)) * scale q (-(3 : ℝ) / 2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htargetPos : 0 < 2 * rho * (q : ℝ) ^ 2 := by positivity
  have hbaseSqPos : 0 < base ^ 2 := htargetPos.trans_le hbaseSq
  have hinv : 1 / base ^ 2 ≤ 1 / (2 * rho * (q : ℝ) ^ 2) :=
    one_div_le_one_div_of_le htargetPos hbaseSq
  have hratio : Real.sqrt q / (q : ℝ) ^ 2 =
      scale q (-(3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (q : ℝ) ^ (1 / 2 : ℝ) / (q : ℝ) ^ 2 =
          (q : ℝ) ^ ((1 / 2 : ℝ) - 2) := by
        simpa only [Real.rpow_two] using
          (Real.rpow_sub hqR (1 / 2 : ℝ) 2).symm
      _ = scale q (-(3 : ℝ) / 2) := by
        norm_num [scale]
  calc
    Real.sqrt q / base ^ 2 = Real.sqrt q * (1 / base ^ 2) := by ring
    _ ≤ Real.sqrt q * (1 / (2 * rho * (q : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg q)
    _ = (1 / (2 * rho)) * (Real.sqrt q / (q : ℝ) ^ 2) := by
      field_simp
    _ = (1 / (2 * rho)) * scale q (-(3 : ℝ) / 2) := by rw [hratio]

/-- Numerical normalization of the high-shift main term.  After factoring
the double cell series, the robust Frobenius lower bound supplies the exact
`q⁻³ᐟ²` rate. -/
lemma claim121_shift_dominated_main_le
    {q : ℕ} (hq : 0 < q) {rho K B eta base : ℝ}
    (hrho : 0 < rho) (hK : 0 ≤ K) (hB : 0 ≤ B) (heta : 0 < eta)
    (hbase : 0 < base)
    (hbaseSq : 2 * rho * (q : ℝ) ^ 2 ≤ base ^ 2) :
    (∑' p : ℕ × ℕ,
        (((40 * K * Real.sqrt q / base) * (1 / 2 : ℝ) ^ p.1) *
          claim121ComparableCellKernel B eta 1 p.2)) / base ≤
      (40 * K / rho *
        (∑' j : ℕ, claim121ComparableCellKernel B eta 1 j)) *
          scale q (-(3 : ℝ) / 2) := by
  let S : ℝ := ∑' j : ℕ, claim121ComparableCellKernel B eta 1 j
  have hS : 0 ≤ S := tsum_nonneg fun j ↦
    claim121ComparableCellKernel_nonneg hB heta j
  have hratio := sqrt_card_div_sq_le_scale_neg_three_halves
    hq hrho hbaseSq
  have hfactor := tsum_claim121_dyadic_cell_kernel
    (A := 40 * K * Real.sqrt q / base) hB heta
  rw [hfactor]
  dsimp only [S] at hS ⊢
  calc
    (2 * (40 * K * Real.sqrt q / base) *
        (∑' j : ℕ, claim121ComparableCellKernel B eta 1 j)) / base =
      (80 * K * (∑' j : ℕ,
        claim121ComparableCellKernel B eta 1 j)) *
          (Real.sqrt q / base ^ 2) := by
            field_simp [ne_of_gt hbase]
            ring
    _ ≤ (80 * K * (∑' j : ℕ,
        claim121ComparableCellKernel B eta 1 j)) *
          ((1 / (2 * rho)) * scale q (-(3 : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left hratio
      positivity
    _ = (40 * K / rho *
        (∑' j : ℕ, claim121ComparableCellKernel B eta 1 j)) *
          scale q (-(3 : ℝ) / 2) := by ring

/-- Count-vector wrapper for the high-shift part of Step 7.  The concrete
dyadic level and buffered spatial cell are built internally; the caller
only supplies the Claim 12.2 fiber mass estimate and the pointwise
nonuniform Claim 12.1 bound. -/
lemma countVector_weighted_claim121_shift_dominated_cells
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (L W qshift cond sigma x : BucketCountVector P → ℝ)
    (Good : BucketCountVector P → Prop)
    {A Pgood c B eta base center err : ℝ}
    (hA : 0 ≤ A) (hPgood : 0 ≤ Pgood) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (heta : 0 < eta) (hbase : 1 ≤ base) (herr : 0 ≤ err)
    (hW : ∀ ell, 0 ≤ W ell)
    (hgoodMass : countVectorMass P Good ≤ Pgood)
    (hgoodW : ∀ ell, Good ell → base ^ 2 ≤ W ell)
    (hmass : ∀ i j : ℕ,
      countVectorMass P (fun ell ↦
          base ^ 2 ≤ W ell ∧ claim121ShiftDyadicLevel base (W ell) = i ∧
            claim121ShiftSpatialCell center base (W ell) (L ell) = j) ≤
        A * (1 / 2 : ℝ) ^ i)
    (hqshift : ∀ ell, qshift ell ^ 2 ≤ W ell)
    (hsigmaLower : ∀ ell, Good ell → base ≤ sigma ell)
    (hsigmaUpper : ∀ ell, Good ell →
      sigma ell ≤ 2 * Real.sqrt (W ell))
    (hx : ∀ ell, Good ell → x ell = center - L ell - qshift ell)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Good ell then cond ell else 0) ≤
      c * (((∑' p : ℕ × ℕ,
          (A * (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2) / base) +
        Pgood * (B * err)) := by
  classical
  let level : BucketCountVector P → ℕ := fun ell ↦
    claim121ShiftDyadicLevel base (W ell)
  let cell : BucketCountVector P → ℕ := fun ell ↦
    claim121ShiftSpatialCell center base (W ell) (L ell)
  let weight' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then countVectorWeight P ell else 0
  let cond' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then cond ell else 0
  let sigma' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then sigma ell else base
  let x' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then x ell else
      (cell ell : ℝ) *
        (4 * (4 * (2 : ℝ) ^ level ell) * base) / 2
  have hbasePos : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  have hweight : ∀ ell, 0 ≤ weight' ell := by
    intro ell
    by_cases hgood : Good ell
    · simp only [weight', hgood, if_true]
      exact countVectorWeight_nonneg P ell
    · simp only [weight', hgood, if_false]
      exact le_rfl
  have htotal : ∑ ell, weight' ell ≤ Pgood := by
    have heq : (∑ ell, weight' ell) = countVectorMass P Good := by
      rw [countVectorMass_eq_sum_filter_countVectorWeight]
      rw [Finset.sum_filter]
    rw [heq]
    exact hgoodMass
  have hmass' : ∀ p : ℕ × ℕ,
      ∑ ell : BucketCountVector P with (level ell, cell ell) = p,
          weight' ell ≤ A * (1 / 2 : ℝ) ^ p.1 := by
    intro p
    have heq :
        (∑ ell : BucketCountVector P with (level ell, cell ell) = p,
            weight' ell) =
          countVectorMass P (fun ell ↦
            Good ell ∧ level ell = p.1 ∧ cell ell = p.2) := by
      rw [countVectorMass_eq_sum_filter_countVectorWeight,
        Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hgood : Good ell
      · simp only [weight', hgood, if_true, level, cell]
        by_cases hp : (claim121ShiftDyadicLevel base (W ell),
            claim121ShiftSpatialCell center base (W ell) (L ell)) = p
        · have hp1 : claim121ShiftDyadicLevel base (W ell) = p.1 :=
            congrArg Prod.fst hp
          have hp2 : claim121ShiftSpatialCell center base (W ell) (L ell) =
              p.2 := congrArg Prod.snd hp
          simp only [hp, hp1, hp2, and_self, if_true]
        · have hnot : ¬(claim121ShiftDyadicLevel base (W ell) = p.1 ∧
              claim121ShiftSpatialCell center base (W ell) (L ell) = p.2) := by
            intro hpair
            exact hp (Prod.ext hpair.1 hpair.2)
          simp only [hp, hnot, and_false, if_false]
      · simp only [weight', hgood, if_false, false_and]
        split <;> rfl
    rw [heq]
    calc
      countVectorMass P (fun ell ↦
          Good ell ∧ level ell = p.1 ∧ cell ell = p.2) ≤
        countVectorMass P (fun ell ↦
          base ^ 2 ≤ W ell ∧
            claim121ShiftDyadicLevel base (W ell) = p.1 ∧
            claim121ShiftSpatialCell center base (W ell) (L ell) = p.2) := by
          apply countVectorMass_mono P
          intro ell hell
          exact ⟨hgoodW ell hell.1, hell.2.1, hell.2.2⟩
      _ ≤ A * (1 / 2 : ℝ) ^ p.1 := hmass p.1 p.2
  have hsigmaLower' : ∀ ell, base ≤ sigma' ell := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [sigma', hgood, if_true] using hsigmaLower ell hgood
    · simp only [sigma', hgood, if_false]
      exact le_rfl
  have hsigmaUpper' : ∀ ell,
      sigma' ell ≤ (4 * (2 : ℝ) ^ level ell) * base := by
    intro ell
    by_cases hgood : Good ell
    · simp only [sigma', hgood, if_true]
      simpa only [level, claim121ShiftDyadicLevel] using
        claim121DyadicLevel_scale_upper hbasePos (hsigmaUpper ell hgood)
    · simp only [sigma', hgood, if_false]
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ level ell :=
        one_le_pow₀ (n := level ell) (by norm_num)
      nlinarith
  have hx' : ∀ ell,
      (cell ell : ℝ) * (4 * (4 * (2 : ℝ) ^ level ell) * base) / 2 ≤
        |x' ell| := by
    intro ell
    by_cases hgood : Good ell
    · simp only [x', hgood, if_true]
      let s : ℝ := (2 : ℝ) ^ level ell * base
      have hq : |qshift ell| ≤ 2 * s := by
        simpa only [s, level, claim121ShiftDyadicLevel] using
          abs_le_two_mul_dyadic_of_sq_le hbasePos (hW ell) (hqshift ell)
      have hcenter : |L ell - center| / 2 - (4 * s) / 2 ≤ |x ell| := by
        rw [hx ell hgood]
        exact half_abs_linear_sub_center_sub_buffer_le_abs_shifted
          (by simpa only [show (4 * s) / 2 = 2 * s by ring] using hq)
      have hgeo := bufferedAbsoluteCellIndex_mul_width_div_two_le_abs
        (center := center) (buffer := 4 * s) (width := 16 * s)
        (x := x ell) (L := L ell) (by dsimp only [s]; positivity) hcenter
      convert hgeo using 1 <;>
        dsimp only [cell, claim121ShiftSpatialCell, level,
          claim121ShiftDyadicLevel, s] <;> ring
    · simp only [x', hgood, if_false]
      rw [abs_of_nonneg]
      positivity
  have hcond' : ∀ ell, cond' ell ≤ c *
      (B ^ 2 / (x' ell ^ 2 + sigma' ell ^ 2) +
        (B / (eta * sigma' ell)) *
          Real.exp (-eta * |x' ell| / (2 * sigma' ell)) + B * err) := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [cond', sigma', x', hgood, if_true] using hcond ell hgood
    · simp only [cond', sigma', x', hgood, if_false]
      apply mul_nonneg hc
      positivity
  have hsum := weighted_claim121_bounded_scale_double_cells
    (A := A) (P := Pgood) (c := c) (B := B) (eta := eta)
    (base := base) (err := err)
    weight' cond' sigma' x' level cell hA hc hB heta hbase herr
    hweight htotal hmass' hsigmaLower' hsigmaUpper' hx' hcond'
  calc
    ∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Good ell then cond ell else 0) =
      ∑ ell : BucketCountVector P, weight' ell * cond' ell := by
        apply Finset.sum_congr rfl
        intro ell hell
        by_cases hgood : Good ell <;>
          simp only [weight', cond', hgood, if_true, if_false, mul_zero,
            zero_mul]
    _ ≤ c * (((∑' p : ℕ × ℕ,
          (A * (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2) / base) +
        Pgood * (B * err)) := hsum

/-- The full weighted comparable-scale cell estimate.  It packages the
pointwise nonuniform Claim 12.1 bound with the summable cell kernel, leaving
only the mass of each buffered cell and the total mass to its caller. -/
lemma weighted_claim121_comparable_cells
    {D : Type*} [Fintype D]
    (weight cond sigma x : D → ℝ) (idx : D → ℕ)
    {A P c B eta sigma0 kappa err : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (heta : 0 < eta) (hsigma0 : 1 ≤ sigma0) (hkappa : 0 < kappa)
    (herr : 0 ≤ err)
    (hweight : ∀ d, 0 ≤ weight d)
    (htotal : ∑ d, weight d ≤ P)
    (hmass : ∀ j : ℕ, ∑ d : D with idx d = j, weight d ≤ A)
    (hsigmaLower : ∀ d, sigma0 / 2 ≤ sigma d)
    (hsigmaUpper : ∀ d, sigma d ≤ 2 * sigma0)
    (hx : ∀ d, (idx d : ℝ) * kappa * sigma0 / 2 ≤ |x d|)
    (hcond : ∀ d, cond d ≤ c *
      (B ^ 2 / (x d ^ 2 + sigma d ^ 2) +
        (B / (eta * sigma d)) *
          Real.exp (-eta * |x d| / (2 * sigma d)) + B * err)) :
    ∑ d, weight d * cond d ≤
      c * (A * (∑' j, claim121ComparableCellKernel B eta kappa j) /
          sigma0 + P * (B * err)) := by
  apply weighted_summable_cell_bound weight cond idx
    (claim121ComparableCellKernel B eta kappa)
    hA hc (lt_of_lt_of_le zero_lt_one hsigma0) (mul_nonneg hB herr)
    (claim121ComparableCellKernel_nonneg hB heta)
    (summable_claim121ComparableCellKernel heta hkappa)
    hweight htotal hmass
  intro d
  apply (hcond d).trans
  apply mul_le_mul_of_nonneg_left _ hc
  have hkernel := claim121_comparable_cell_kernel_bound hB heta hsigma0
    (hsigmaLower d) (hsigmaUpper d) hkappa (hx d)
  change
    B ^ 2 / (x d ^ 2 + sigma d ^ 2) +
          (B / (eta * sigma d)) *
            Real.exp (-eta * |x d| / (2 * sigma d)) + B * err ≤
      claim121ComparableCellKernel B eta kappa (idx d) / sigma0 + B * err
  simpa only [claim121ComparableCellKernel, add_comm] using
    (add_le_add_right hkernel (B * err))

/-- Count-vector specialization of the comparable-scale Step 7 sum.  The
interval-mass hypothesis is `(12.7)`, the buffered centering hypothesis
absorbs the deterministic quadratic displacement, and all count vectors
whose Claim 12.1 scale is comparable to `sigma0` are summed together. -/
lemma countVector_weighted_claim121_comparable_cells
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L cond sigma x : BucketCountVector P → ℝ)
    {center buffer rate c B eta sigma0 kappa err : ℝ}
    (hbuffer : 0 ≤ buffer) (hrate : 0 ≤ rate)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (heta : 0 < eta)
    (hsigma0 : 1 ≤ sigma0) (hkappa : 0 < kappa) (herr : 0 ≤ err)
    (hinterval : ∀ a b : ℝ, kappa * sigma0 ≤ b - a →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a))
    (hsigmaLower : ∀ ell, sigma0 / 2 ≤ sigma ell)
    (hsigmaUpper : ∀ ell, sigma ell ≤ 2 * sigma0)
    (hcenter : ∀ ell,
      |L ell - center| / 2 - buffer / 2 ≤ |x ell|)
    (hcond : ∀ ell, cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector P, countVectorWeight P ell * cond ell ≤
      c * ((2 * rate * (buffer + kappa * sigma0)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) / sigma0 +
        B * err) := by
  have hsigma0Pos : 0 < sigma0 := lt_of_lt_of_le zero_lt_one hsigma0
  have hwidth : 0 < kappa * sigma0 := mul_pos hkappa hsigma0Pos
  have hsum := weighted_claim121_comparable_cells
    (A := 2 * rate * (buffer + kappa * sigma0)) (P := 1)
    (countVectorWeight P) cond sigma x
    (fun ell ↦ bufferedAbsoluteCellIndex center buffer
      (kappa * sigma0) (L ell))
    (by positivity) hc hB heta hsigma0 hkappa herr
    (countVectorWeight_nonneg P)
    (by rw [sum_countVectorWeight_eq_one P])
    (fun j ↦ by
      have hmass := countVectorMass_bufferedAbsoluteCellIndex_le
        (center := center) P L
        hbuffer hwidth hrate hinterval j
      rw [countVectorMass] at hmass
      rw [Finset.sum_filter]
      unfold countVectorWeight
      convert hmass using 1
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hcell : bufferedAbsoluteCellIndex center buffer
          (kappa * sigma0) (L ell) = j <;>
        simp only [hcell, if_true, if_false])
    hsigmaLower hsigmaUpper
    (fun ell ↦ by
      simpa only [mul_assoc] using
        (bufferedAbsoluteCellIndex_mul_width_div_two_le_abs
          hwidth (hcenter ell))) hcond
  simpa only [one_mul] using hsum

/-- Predicate-restricted version of the comparable-scale count-vector sum.
Outside `Good` the conditional contribution is zero; auxiliary scale and
center functions are filled in canonically so the same global cell mass
bound applies without any subtype bookkeeping. -/
lemma countVector_weighted_claim121_comparable_cells_on
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L cond sigma x : BucketCountVector P → ℝ)
    (Good : BucketCountVector P → Prop)
    {center buffer rate c B eta sigma0 kappa err : ℝ}
    (hbuffer : 0 ≤ buffer) (hrate : 0 ≤ rate)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (heta : 0 < eta)
    (hsigma0 : 1 ≤ sigma0) (hkappa : 0 < kappa) (herr : 0 ≤ err)
    (hinterval : ∀ a b : ℝ, kappa * sigma0 ≤ b - a →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a))
    (hsigmaLower : ∀ ell, Good ell → sigma0 / 2 ≤ sigma ell)
    (hsigmaUpper : ∀ ell, Good ell → sigma ell ≤ 2 * sigma0)
    (hcenter : ∀ ell, Good ell →
      |L ell - center| / 2 - buffer / 2 ≤ |x ell|)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Good ell then cond ell else 0) ≤
      c * ((2 * rate * (buffer + kappa * sigma0)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) / sigma0 +
        B * err) := by
  classical
  let cond' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then cond ell else 0
  let sigma' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then sigma ell else sigma0
  let x' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then x ell else
      max (|L ell - center| / 2 - buffer / 2) 0
  have hsigmaLower' : ∀ ell, sigma0 / 2 ≤ sigma' ell := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [sigma', if_pos hgood] using hsigmaLower ell hgood
    · simp only [sigma', if_neg hgood]
      nlinarith
  have hsigmaUpper' : ∀ ell, sigma' ell ≤ 2 * sigma0 := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [sigma', if_pos hgood] using hsigmaUpper ell hgood
    · simp only [sigma', if_neg hgood]
      nlinarith
  have hcenter' : ∀ ell,
      |L ell - center| / 2 - buffer / 2 ≤ |x' ell| := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [x', if_pos hgood] using hcenter ell hgood
    · simp only [x', if_neg hgood]
      have hz : 0 ≤ max (|L ell - center| / 2 - buffer / 2) 0 :=
        le_max_right _ _
      have habs : |max (|L ell - center| / 2 - buffer / 2) 0| =
          max (|L ell - center| / 2 - buffer / 2) 0 := abs_of_nonneg hz
      rw [habs]
      exact le_max_left _ _
  have hcond' : ∀ ell, cond' ell ≤ c *
      (B ^ 2 / (x' ell ^ 2 + sigma' ell ^ 2) +
        (B / (eta * sigma' ell)) *
          Real.exp (-eta * |x' ell| / (2 * sigma' ell)) + B * err) := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [cond', sigma', x', if_pos hgood] using hcond ell hgood
    · simp only [cond', sigma', x', if_neg hgood]
      have hsigma0Pos : 0 < sigma0 := lt_of_lt_of_le zero_lt_one hsigma0
      apply mul_nonneg hc
      positivity
  have hsum := countVector_weighted_claim121_comparable_cells
    P L cond' sigma' x' hbuffer hrate hc hB heta hsigma0 hkappa herr
    hinterval hsigmaLower' hsigmaUpper' hcenter' hcond'
  simpa only [cond'] using hsum

/-- Mass-sensitive predicate restriction.  This is the form needed for the
Fourier-comparison error in Step 7: the error is charged only against the
moderate linear-shift region, not against the whole count-vector law. -/
lemma countVector_weighted_claim121_comparable_cells_on_mass
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (L cond sigma x : BucketCountVector P → ℝ)
    (Good : BucketCountVector P → Prop)
    {center buffer rate c B eta sigma0 kappa err Pgood : ℝ}
    (hbuffer : 0 ≤ buffer) (hrate : 0 ≤ rate)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (heta : 0 < eta)
    (hsigma0 : 1 ≤ sigma0) (hkappa : 0 < kappa) (herr : 0 ≤ err)
    (hinterval : ∀ a b : ℝ, kappa * sigma0 ≤ b - a →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a))
    (hgoodMass : countVectorMass P Good ≤ Pgood)
    (hsigmaLower : ∀ ell, Good ell → sigma0 / 2 ≤ sigma ell)
    (hsigmaUpper : ∀ ell, Good ell → sigma ell ≤ 2 * sigma0)
    (hcenter : ∀ ell, Good ell →
      |L ell - center| / 2 - buffer / 2 ≤ |x ell|)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Good ell then cond ell else 0) ≤
      c * ((2 * rate * (buffer + kappa * sigma0)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) / sigma0 +
        Pgood * (B * err)) := by
  classical
  let weight' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then countVectorWeight P ell else 0
  let cond' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then cond ell else 0
  let sigma' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then sigma ell else sigma0
  let x' : BucketCountVector P → ℝ := fun ell ↦
    if Good ell then x ell else
      max (|L ell - center| / 2 - buffer / 2) 0
  have hsigma0Pos : 0 < sigma0 := lt_of_lt_of_le zero_lt_one hsigma0
  have hwidth : 0 < kappa * sigma0 := mul_pos hkappa hsigma0Pos
  have hweight : ∀ ell, 0 ≤ weight' ell := by
    intro ell
    by_cases hgood : Good ell
    · simp only [weight', hgood, if_true]
      exact countVectorWeight_nonneg P ell
    · simp only [weight', hgood, if_false]
      exact le_rfl
  have htotal : ∑ ell, weight' ell ≤ Pgood := by
    have heq : (∑ ell, weight' ell) = countVectorMass P Good := by
      rw [countVectorMass]
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hgood : Good ell <;>
        simp only [weight', countVectorWeight, hgood, if_true, if_false]
    rw [heq]
    exact hgoodMass
  have hmass : ∀ j : ℕ,
      ∑ ell : BucketCountVector P with
          bufferedAbsoluteCellIndex center buffer
            (kappa * sigma0) (L ell) = j, weight' ell ≤
        2 * rate * (buffer + kappa * sigma0) := by
    intro j
    have hfull := countVectorMass_bufferedAbsoluteCellIndex_le
      (center := center) P L hbuffer hwidth hrate hinterval j
    rw [countVectorMass] at hfull
    calc
      (∑ ell : BucketCountVector P with
          bufferedAbsoluteCellIndex center buffer
            (kappa * sigma0) (L ell) = j, weight' ell) ≤
          ∑ ell : BucketCountVector P with
            bufferedAbsoluteCellIndex center buffer
              (kappa * sigma0) (L ell) = j,
              countVectorWeight P ell := by
        apply Finset.sum_le_sum
        intro ell hell
        by_cases hgood : Good ell
        · simp only [weight', hgood, if_true]
          exact le_rfl
        · simp only [weight', hgood, if_false]
          exact countVectorWeight_nonneg P ell
      _ ≤ 2 * rate * (buffer + kappa * sigma0) := by
        rw [Finset.sum_filter]
        unfold countVectorWeight
        convert hfull using 1
        apply Finset.sum_congr rfl
        intro ell hell
        by_cases hcell : bufferedAbsoluteCellIndex center buffer
            (kappa * sigma0) (L ell) = j <;>
          simp only [hcell, if_true, if_false]
  have hsigmaLower' : ∀ ell, sigma0 / 2 ≤ sigma' ell := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [sigma', if_pos hgood] using hsigmaLower ell hgood
    · simp only [sigma', if_neg hgood]
      nlinarith
  have hsigmaUpper' : ∀ ell, sigma' ell ≤ 2 * sigma0 := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [sigma', if_pos hgood] using hsigmaUpper ell hgood
    · simp only [sigma', if_neg hgood]
      nlinarith
  have hcenter' : ∀ ell,
      |L ell - center| / 2 - buffer / 2 ≤ |x' ell| := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [x', if_pos hgood] using hcenter ell hgood
    · simp only [x', if_neg hgood]
      have hz : 0 ≤ max (|L ell - center| / 2 - buffer / 2) 0 :=
        le_max_right _ _
      have habs : |max (|L ell - center| / 2 - buffer / 2) 0| =
          max (|L ell - center| / 2 - buffer / 2) 0 := abs_of_nonneg hz
      rw [habs]
      exact le_max_left _ _
  have hcond' : ∀ ell, cond' ell ≤ c *
      (B ^ 2 / (x' ell ^ 2 + sigma' ell ^ 2) +
        (B / (eta * sigma' ell)) *
          Real.exp (-eta * |x' ell| / (2 * sigma' ell)) + B * err) := by
    intro ell
    by_cases hgood : Good ell
    · simpa only [cond', sigma', x', if_pos hgood] using hcond ell hgood
    · simp only [cond', sigma', x', if_neg hgood]
      apply mul_nonneg hc
      positivity
  have hsum := weighted_claim121_comparable_cells
    (A := 2 * rate * (buffer + kappa * sigma0)) (P := Pgood)
    weight' cond' sigma' x'
    (fun ell ↦ bufferedAbsoluteCellIndex center buffer
      (kappa * sigma0) (L ell))
    (by positivity) hc hB heta hsigma0 hkappa herr hweight htotal hmass
    hsigmaLower' hsigmaUpper'
    (fun ell ↦ by
      simpa only [mul_assoc] using
        (bufferedAbsoluteCellIndex_mul_width_div_two_le_abs
          hwidth (hcenter' ell))) hcond'
  calc
    ∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Good ell then cond ell else 0) =
        ∑ ell : BucketCountVector P, weight' ell * cond' ell := by
      apply Finset.sum_congr rfl
      intro ell hell
      by_cases hgood : Good ell <;>
        simp only [weight', cond', hgood, if_true, if_false, mul_zero,
          zero_mul]
    _ ≤ c * ((2 * rate * (buffer + kappa * sigma0)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) / sigma0 +
        Pgood * (B * err)) := hsum

/-- Low-shift specialization of the comparable-cell estimate.  The bound
`W ≤ base²` absorbs the quadratic center displacement into a buffer of
width `2*base`; all remaining hypotheses are the source's interval-mass and
conditional Claim 12.1 estimates. -/
lemma countVector_weighted_claim121_low_shift_cells
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (L W qshift cond sigma x : BucketCountVector P → ℝ)
    (Good : BucketCountVector P → Prop)
    {center rate c B eta base kappa err Pgood : ℝ}
    (hrate : 0 ≤ rate) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (heta : 0 < eta) (hbase : 1 ≤ base) (hkappa : 0 < kappa)
    (herr : 0 ≤ err)
    (hinterval : ∀ a b : ℝ, kappa * base ≤ b - a →
      countVectorMass P (fun ell ↦ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a))
    (hgoodMass : countVectorMass P Good ≤ Pgood)
    (hW : ∀ ell, 0 ≤ W ell)
    (hgoodW : ∀ ell, Good ell → W ell ≤ base ^ 2)
    (hqshift : ∀ ell, qshift ell ^ 2 ≤ W ell)
    (hsigmaLower : ∀ ell, Good ell → base / 2 ≤ sigma ell)
    (hsigmaUpper : ∀ ell, Good ell → sigma ell ≤ 2 * base)
    (hx : ∀ ell, Good ell → x ell = center - L ell - qshift ell)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector P,
        countVectorWeight P ell * (if Good ell then cond ell else 0) ≤
      c * ((2 * rate * (2 * base + kappa * base)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) / base +
        Pgood * (B * err)) := by
  have hbasePos : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  apply countVector_weighted_claim121_comparable_cells_on_mass
    (center := center) (buffer := 2 * base) (rate := rate)
    (c := c) (B := B) (eta := eta) (sigma0 := base)
    (kappa := kappa) (err := err) (Pgood := Pgood)
    P L cond sigma x Good
  · positivity
  · exact hrate
  · exact hc
  · exact hB
  · exact heta
  · exact hbase
  · exact hkappa
  · exact herr
  · exact hinterval
  · exact hgoodMass
  · exact hsigmaLower
  · exact hsigmaUpper
  · intro ell hell
    have hqSq : qshift ell ^ 2 ≤ base ^ 2 :=
      (hqshift ell).trans (hgoodW ell hell)
    have hq : |qshift ell| ≤ base := by
      apply (sq_le_sq₀ (abs_nonneg _) hbasePos.le).mp
      simpa only [sq_abs] using hqSq
    rw [hx ell hell]
    exact half_abs_linear_sub_center_sub_buffer_le_abs_shifted
      (by simpa only [show (2 * base) / 2 = base by ring] using hq)
  · exact hcond

/-- The balanced coefficient hypotheses give the source's uniform upper
bound on every conditional Claim 12.1 scale. -/
lemma claim121Scale_le_of_balancedCoefficients
    {n m : ℕ} {delta : ℝ} (hn : 1 ≤ n) (hdelta : 0 ≤ delta)
    (P : BucketPartition (Fin n) (Fin m)) (f : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ)
    (hcoeff : HasKSSSBalancedCoefficients delta P f F) :
    Real.sqrt (2 * frobeniusSq F + vectorSqNorm f) ≤
      2 * scale n (1 + 3 * delta) := by
  have hnpos : 0 < n := by omega
  have htarget := gaussianVarianceTarget_le_ksss delta hdelta hn f F
    hcoeff.2.1 hcoeff.2.2.1
  have hscaleSq : scale n (2 + 6 * delta) =
      scale n (1 + 3 * delta) ^ 2 := by
    rw [scale_sq (Nat.zero_le n)]
    congr 1
    ring
  apply Structured.sigma_upper_bound (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (scale_nonneg n _))
  rw [Real.sq_sqrt (by
    exact add_nonneg
      (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i hi ↦
          Finset.sum_nonneg fun j hj ↦ sq_nonneg _))
      (Finset.sum_nonneg fun i hi ↦ sq_nonneg _))]
  calc
    2 * frobeniusSq F + vectorSqNorm f ≤
        3 * scale n (2 + 6 * delta) := htarget
    _ = 3 * scale n (1 + 3 * delta) ^ 2 := by rw [hscaleSq]
    _ ≤ (2 * scale n (1 + 3 * delta)) ^ 2 := by
      nlinarith [sq_nonneg (scale n (1 + 3 * delta))]

/-- Exact second moment of an affine plus symmetric diagonal-free
Rademacher quadratic, in the recursive polynomial representation consumed
by the Bonami tail estimate. -/
lemma cubePoly_quadratic_mean_two_eq_gaussianTarget
    {n : ℕ} (a : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    RademacherHypercontractivity.CubePoly.mean
        (RademacherHypercontractivity.CubePoly.quadraticPoly 0 a F) 2 =
      vectorSqNorm a + 2 * frobeniusSq F := by
  classical
  open RademacherHypercontractivity.CubePoly in
    let e : (Fin n → Bool) ≃ Finset (Fin n) := boolFunEquivFinset
    have hsign (xi : Fin n → Bool) :
        (fun i ↦ Fourier.rademacherSign (xi i)) = signOfSet (e xi) := by
      funext i
      cases hxi : xi i <;>
        simp [e, boolFunEquivFinset, signOfSet,
          Fourier.rademacherSign, hxi]
    have hsum :
        (∑ xi : Fin n → Bool,
          eval (quadraticPoly 0 a F) xi ^ 2) =
        ∑ S : Finset (Fin n), (sliceQuadratic 0 a F S) ^ 2 := by
      calc
        (∑ xi : Fin n → Bool,
            eval (quadraticPoly 0 a F) xi ^ 2) =
            ∑ xi : Fin n → Bool, (sliceQuadratic 0 a F (e xi)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro xi hxi
          rw [eval_quadraticPoly]
          have hsign' (i : Fin n) :
              Fourier.rademacherSign (xi i) = signOfSet (e xi) i :=
            congrFun (hsign xi) i
          simp_rw [hsign']
          simp only [sliceQuadratic, quadraticPolynomial, linearPart,
            quadraticPart, zero_add]
          congr 1
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ S : Finset (Fin n), (sliceQuadratic 0 a F S) ^ 2 :=
          e.sum_comp fun S ↦ (sliceQuadratic 0 a F S) ^ 2
    rw [RademacherHypercontractivity.CubePoly.mean, hsum,
      Fintype.card_congr e, ← Fintype.expect_eq_sum_div_card]
    change BooleanSlices.uniformExpectation
      (fun S : Finset (Fin n) ↦ (sliceQuadratic 0 a F S) ^ 2) = _
    have hvar := rademacher_sliceQuadratic_variance_symmetric 0 a F hF
    rw [uniformVariance, rademacher_sliceQuadratic_mean] at hvar
    have htrace : trace F = 0 := by
      unfold trace
      exact Finset.sum_eq_zero fun i hi ↦ hdiag i
    have hdiagSum : ∑ i, F i i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by rw [hdiag i, zero_pow (by norm_num)]
    simpa only [zero_add, htrace, sub_zero, hdiagSum, mul_zero,
      sub_zero, add_comm] using hvar

/-- High-moment tail for an affine plus symmetric diagonal-free quadratic
on the finite Rademacher cube, with the exact variance proxy appearing in
Section 12. -/
lemma finProbability_affineQuadratic_tail_mul_pow_le
    {n r : ℕ} (a : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0)
    {T : ℝ} (hT : 0 < T) :
    Fourier.finProbability (Fin n → Bool) (fun xi ↦
        T ≤ |∑ i, a i * Fourier.rademacherSign (xi i) +
          ∑ i, ∑ j, F i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j)|) *
        T ^ (2 ^ (r + 1)) ≤
      9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 r *
        (vectorSqNorm a + 2 * frobeniusSq F) ^ (2 ^ r) := by
  let p := RademacherHypercontractivity.CubePoly.quadraticPoly 0 a F
  have hp : RademacherHypercontractivity.CubePoly.DegreeLE 2 p :=
    RademacherHypercontractivity.CubePoly.degreeLE_quadraticPoly 0 a F
  have htail :=
    RademacherHypercontractivity.CubePoly.finProbability_abs_eval_mul_pow_le
      p hp r hT
  rw [cubePoly_quadratic_mean_two_eq_gaussianTarget a F hF hdiag] at htail
  simpa only [p,
    RademacherHypercontractivity.CubePoly.eval_quadraticPoly, zero_add]
    using htail

/-- The residual after removing the bucket-projected linear shift is an
affine plus quadratic Rademacher polynomial with the exact coefficients
used in the source's Step 7 tail estimate. -/
lemma structuredResidual_eq_affineQuadratic
    {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Structured.IsOrthogonalProjection Q)
    (E : ℝ) (y x : Fin n → ℝ) :
    Structured.structuredQuadratic E M y x - E -
        (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q x) =
      ∑ i, ((1 / 2 : ℝ) *
          (Structured.centeredProjection Q *ᵥ y) i) * x i +
        ∑ i, ∑ j, ((1 / 8 : ℝ) * M i j) * x i * x j := by
  have hy : y ⬝ᵥ x = y ⬝ᵥ Structured.delta Q x +
      (Structured.centeredProjection Q *ᵥ y) ⬝ᵥ x := by
    calc
      y ⬝ᵥ x = y ⬝ᵥ
          (Structured.delta Q x + Structured.residual Q x) := by
        rw [Structured.delta_add_residual]
      _ = y ⬝ᵥ Structured.delta Q x +
          y ⬝ᵥ Structured.residual Q x := by rw [dotProduct_add]
      _ = y ⬝ᵥ Structured.delta Q x +
          (Structured.centeredProjection Q *ᵥ y) ⬝ᵥ x := by
        rw [Structured.residual,
          Structured.dot_centeredProjection Q hQ]
  rw [Structured.structuredQuadratic, hy]
  have hlinear :
      (Structured.centeredProjection Q *ᵥ y) ⬝ᵥ x =
        ∑ i, (Structured.centeredProjection Q *ᵥ y) i * x i := rfl
  have hquad : x ⬝ᵥ (M *ᵥ x) =
      ∑ i, ∑ j, x i * M i j * x j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hlinearScale :
      (1 / 2 : ℝ) *
          (∑ i, (Structured.centeredProjection Q *ᵥ y) i * x i) =
        ∑ i, ((1 / 2 : ℝ) *
          (Structured.centeredProjection Q *ᵥ y) i) * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hquadScale :
      (1 / 8 : ℝ) * (∑ i, ∑ j, x i * M i j * x j) =
        ∑ i, ∑ j, ((1 / 8 : ℝ) * M i j) * x i * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hlinear, hquad]
  calc
    E + (1 / 2 : ℝ) *
          (y ⬝ᵥ Structured.delta Q x +
            ∑ i, (Structured.centeredProjection Q *ᵥ y) i * x i) +
          (1 / 8 : ℝ) * (∑ i, ∑ j, x i * M i j * x j) - E -
        (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q x) =
        (1 / 2 : ℝ) *
            (∑ i, (Structured.centeredProjection Q *ᵥ y) i * x i) +
          (1 / 8 : ℝ) * (∑ i, ∑ j, x i * M i j * x j) := by ring
    _ = ∑ i, ((1 / 2 : ℝ) *
          (Structured.centeredProjection Q *ᵥ y) i) * x i +
        ∑ i, ∑ j, ((1 / 8 : ℝ) * M i j) * x i * x j := by
      rw [hlinearScale, hquadScale]

/-- Bonami tail for the actual structured residual
`X - E - E_shift(1)`. -/
lemma finProbability_structuredResidual_tail_mul_pow_le
    {n r : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Structured.IsOrthogonalProjection Q)
    (hM : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0)
    (E : ℝ) (y : Fin n → ℝ) {T : ℝ} (hT : 0 < T) :
    Fourier.finProbability (Fin n → Bool) (fun xi ↦
        T ≤ |Structured.structuredQuadratic E M y
              (fun i ↦ Fourier.rademacherSign (xi i)) - E -
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
              (fun i ↦ Fourier.rademacherSign (xi i)))|) *
        T ^ (2 ^ (r + 1)) ≤
      9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 r *
        ((1 / 4 : ℝ) * vectorSqNorm
            (Structured.centeredProjection Q *ᵥ y) +
          (1 / 32 : ℝ) * frobeniusSq M) ^ (2 ^ r) := by
  let a : Fin n → ℝ := fun i ↦
    (1 / 2 : ℝ) * (Structured.centeredProjection Q *ᵥ y) i
  let F : Fin n → Fin n → ℝ := fun i j ↦ (1 / 8 : ℝ) * M i j
  have hF : ∀ i j, F i j = F j i := by
    intro i j
    dsimp only [F]
    rw [hM]
  have hFdiag : ∀ i, F i i = 0 := by
    intro i
    simp only [F, hdiag, mul_zero]
  have htail := finProbability_affineQuadratic_tail_mul_pow_le
    (r := r) a F hF hFdiag hT
  have hpoint (xi : Fin n → Bool) :
      Structured.structuredQuadratic E M y
            (fun i ↦ Fourier.rademacherSign (xi i)) - E -
          (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
            (fun i ↦ Fourier.rademacherSign (xi i))) =
        ∑ i, a i * Fourier.rademacherSign (xi i) +
          ∑ i, ∑ j, F i j * Fourier.rademacherSign (xi i) *
            Fourier.rademacherSign (xi j) := by
    simpa only [a, F] using structuredResidual_eq_affineQuadratic
      Q M hQ E y (fun i ↦ Fourier.rademacherSign (xi i))
  have haNorm : vectorSqNorm a =
      (1 / 4 : ℝ) * vectorSqNorm
        (Structured.centeredProjection Q *ᵥ y) := by
    unfold vectorSqNorm
    dsimp only [a]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hFNorm : frobeniusSq F =
      (1 / 64 : ℝ) * frobeniusSq M := by
    unfold frobeniusSq
    dsimp only [F]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hpoint]
  rw [haNorm, hFNorm] at htail
  convert htail using 1 <;> ring

/-- At zero count shift, the linear part of the structured residual has
exactly one quarter of the squared norm of the unscaled centered vector. -/
lemma vectorSqNorm_wStar_zero
    {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    vectorSqNorm (Structured.wStar Q M y 0) =
      (1 / 4 : ℝ) * vectorSqNorm
        (Structured.centeredProjection Q *ᵥ y) := by
  unfold Structured.wStar vectorSqNorm
  simp only [Matrix.mulVec_zero, smul_zero, add_zero, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The zero-one adjacency matrix of an `n`-vertex graph has squared
Frobenius norm at most `n²`. -/
lemma frobeniusSq_graphAdjacencyMatrix_le_card_sq
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    frobeniusSq (RobustRank.graphAdjacencyMatrix G) ≤ (n : ℝ) ^ 2 := by
  have h := frobeniusSq_le (RobustRank.graphAdjacencyMatrix G) 1
    (by norm_num) (by
      intro i j
      rcases RobustRank.graphAdjacencyMatrix_isBinary G i j with hij | hij <;>
        rw [hij] <;> norm_num)
  simpa using h

/-- A robust Frobenius lower bound on the centered quadratic matrix absorbs
the original adjacency contribution in the Step 7 residual variance. -/
lemma residualVarianceProxy_le_baseVariance
    {n : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (F M : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hFrob : rho * (n : ℝ) ^ 2 ≤ frobeniusSq F)
    (hM : frobeniusSq M ≤ (n : ℝ) ^ 2) :
    v + (1 / 32 : ℝ) * frobeniusSq M ≤
      (1 + 1 / (32 * rho)) * (2 * frobeniusSq F + v) := by
  have hFnonneg : 0 ≤ frobeniusSq F := by
    unfold frobeniusSq
    positivity
  have hnrho : (n : ℝ) ^ 2 ≤ (1 / rho) * frobeniusSq F := by
    calc
      (n : ℝ) ^ 2 ≤ frobeniusSq F / rho :=
        (le_div_iff₀ hrho).2 (by nlinarith [hFrob])
      _ = (1 / rho) * frobeniusSq F := by ring
  have hMbound : (1 / 32 : ℝ) * frobeniusSq M ≤
      (1 / (32 * rho)) * frobeniusSq F := by
    calc
      (1 / 32 : ℝ) * frobeniusSq M ≤
          (1 / 32 : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hM (by norm_num)
      _ ≤ (1 / 32 : ℝ) * ((1 / rho) * frobeniusSq F) :=
        mul_le_mul_of_nonneg_left hnrho (by norm_num)
      _ = (1 / (32 * rho)) * frobeniusSq F := by field_simp
  have hcoef : 0 ≤ 1 / (32 * rho) := by positivity
  calc
    v + (1 / 32 : ℝ) * frobeniusSq M ≤
        v + (1 / (32 * rho)) * frobeniusSq F := by linarith
    _ ≤ (1 + 1 / (32 * rho)) * (2 * frobeniusSq F + v) := by
      nlinarith [mul_nonneg hcoef hv, mul_nonneg hcoef hFnonneg]

/-- Source-shaped absorption of the actual structured residual variance by
the zero-count Claim 12.1 scale. -/
lemma structuredResidualVarianceProxy_le_baseVariance
    {n : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (Q F : Matrix (Fin n) (Fin n) ℝ) (G : SimpleGraph (Fin n))
    (y : Fin n → ℝ)
    (hFrob : rho * (n : ℝ) ^ 2 ≤ frobeniusSq F) :
    (1 / 4 : ℝ) * vectorSqNorm
          (Structured.centeredProjection Q *ᵥ y) +
        (1 / 32 : ℝ) * frobeniusSq
          (RobustRank.graphAdjacencyMatrix G) ≤
      (1 + 1 / (32 * rho)) *
        (2 * frobeniusSq F + vectorSqNorm
          (Structured.wStar Q (RobustRank.graphAdjacencyMatrix G) y 0)) := by
  rw [vectorSqNorm_wStar_zero]
  exact residualVarianceProxy_le_baseVariance hrho F
    (RobustRank.graphAdjacencyMatrix G)
    ((1 / 4 : ℝ) * vectorSqNorm
      (Structured.centeredProjection Q *ᵥ y))
    (mul_nonneg (by norm_num) (by unfold vectorSqNorm; positivity)) hFrob
    (frobeniusSq_graphAdjacencyMatrix_le_card_sq G)

/-- A fixed 64th-moment Bonami estimate after cancelling the residual
standard-deviation scale. -/
lemma finProbability_structuredResidual_tail_mul_cutoff_pow_le
    {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Structured.IsOrthogonalProjection Q)
    (hM : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0)
    (E : ℝ) (y : Fin n → ℝ) {sigma R K : ℝ}
    (hsigma : 0 < sigma) (hR : 0 < R)
    (hproxy :
      (1 / 4 : ℝ) * vectorSqNorm
          (Structured.centeredProjection Q *ᵥ y) +
        (1 / 32 : ℝ) * frobeniusSq M ≤ K * sigma ^ 2) :
    Fourier.finProbability (Fin n → Bool) (fun xi ↦
        sigma * R ≤ |Structured.structuredQuadratic E M y
              (fun i ↦ Fourier.rademacherSign (xi i)) - E -
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
              (fun i ↦ Fourier.rademacherSign (xi i)))|) *
        R ^ 64 ≤
      9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        K ^ 32 := by
  let V : ℝ :=
    (1 / 4 : ℝ) * vectorSqNorm
        (Structured.centeredProjection Q *ᵥ y) +
      (1 / 32 : ℝ) * frobeniusSq M
  have hV : 0 ≤ V := by
    dsimp only [V]
    unfold vectorSqNorm frobeniusSq
    positivity
  have htail := finProbability_structuredResidual_tail_mul_pow_le
    (r := 5) Q M hQ hM hdiag E y (mul_pos hsigma hR)
  norm_num only [Nat.reduceAdd, Nat.reducePow] at htail
  have hVpow : V ^ 32 ≤ (K * sigma ^ 2) ^ 32 :=
    pow_le_pow_left₀ hV hproxy 32
  have htail' :
      Fourier.finProbability (Fin n → Bool) (fun xi ↦
          sigma * R ≤ |Structured.structuredQuadratic E M y
                (fun i ↦ Fourier.rademacherSign (xi i)) - E -
              (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
                (fun i ↦ Fourier.rademacherSign (xi i)))|) *
          (sigma * R) ^ 64 ≤
        9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
          (K * sigma ^ 2) ^ 32 := by
    exact htail.trans (mul_le_mul_of_nonneg_left hVpow (by positivity))
  have hsigmaPow : 0 < sigma ^ 64 := pow_pos hsigma 64
  apply (mul_le_mul_iff_of_pos_right hsigmaPow).mp
  convert htail' using 1
  · rfl
  · ring
  · ring

/-- Choosing a small fixed polynomial enlargement of the residual scale
turns the fixed Bonami moment into a `q⁻¹⁶⁄⁵` tail. -/
lemma finProbability_structuredResidual_polynomial_tail_le
    {n q : ℕ} (hq : 0 < q)
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Structured.IsOrthogonalProjection Q)
    (hM : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0)
    (E : ℝ) (y : Fin n → ℝ) {sigma K : ℝ}
    (hsigma : 0 < sigma)
    (hproxy :
      (1 / 4 : ℝ) * vectorSqNorm
          (Structured.centeredProjection Q *ᵥ y) +
        (1 / 32 : ℝ) * frobeniusSq M ≤ K * sigma ^ 2) :
    Fourier.finProbability (Fin n → Bool) (fun xi ↦
        sigma * scale q (1 / 20 : ℝ) ≤
          |Structured.structuredQuadratic E M y
              (fun i ↦ Fourier.rademacherSign (xi i)) - E -
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
              (fun i ↦ Fourier.rademacherSign (xi i)))|) ≤
      (9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        K ^ 32) * scale q (-16 / 5 : ℝ) := by
  have hR : 0 < scale q (1 / 20 : ℝ) := scale_pos hq _
  have hmul := finProbability_structuredResidual_tail_mul_cutoff_pow_le
    Q M hQ hM hdiag E y hsigma hR hproxy
  have hpow : scale q (1 / 20 : ℝ) ^ 64 =
      scale q (16 / 5 : ℝ) := by
    unfold scale
    convert (Real.rpow_mul_natCast (x := (q : ℝ))
      (by positivity) (1 / 20 : ℝ) 64).symm using 1 <;> norm_num
  rw [hpow] at hmul
  have hscalePos : 0 < scale q (16 / 5 : ℝ) := scale_pos hq _
  apply (mul_le_mul_iff_of_pos_right hscalePos).mp
  calc
    Fourier.finProbability (Fin n → Bool) (fun xi ↦
        sigma * scale q (1 / 20 : ℝ) ≤
          |Structured.structuredQuadratic E M y
              (fun i ↦ Fourier.rademacherSign (xi i)) - E -
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
              (fun i ↦ Fourier.rademacherSign (xi i)))|) *
        scale q (16 / 5 : ℝ) ≤
      9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        K ^ 32 := hmul
    _ = ((9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        K ^ 32) * scale q (-16 / 5 : ℝ)) *
          scale q (16 / 5 : ℝ) := by
      rw [mul_assoc, scale_mul hq]
      norm_num [scale]

/-- The Step 7 far-residual estimate in the source variables.  The robust
Frobenius lower bound makes the original adjacency contribution comparable
to the zero-count Claim 12.1 scale, after which the fixed Bonami moment gives
the stronger `q⁻¹⁶⁄⁵` decay. -/
lemma finProbability_graphStructuredResidual_polynomial_tail_le
    {q : ℕ} (hq : 0 < q) {rho : ℝ} (hrho : 0 < rho)
    (Q F : Matrix (Fin q) (Fin q) ℝ) (G : SimpleGraph (Fin q))
    (hQ : Structured.IsOrthogonalProjection Q) (E : ℝ) (y : Fin q → ℝ)
    (hFrob : rho * (q : ℝ) ^ 2 ≤ frobeniusSq F) :
    let sigma := Real.sqrt
      (2 * frobeniusSq F + vectorSqNorm
        (Structured.wStar Q (RobustRank.graphAdjacencyMatrix G) y 0))
    Fourier.finProbability (Fin q → Bool) (fun xi ↦
        sigma * scale q (1 / 20 : ℝ) ≤
          |Structured.structuredQuadratic E
              (RobustRank.graphAdjacencyMatrix G) y
              (fun i ↦ Fourier.rademacherSign (xi i)) - E -
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q
              (fun i ↦ Fourier.rademacherSign (xi i)))|) ≤
      (9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        (1 + 1 / (32 * rho)) ^ 32) * scale q (-16 / 5 : ℝ) := by
  let M := RobustRank.graphAdjacencyMatrix G
  let sigma := Real.sqrt
    (2 * frobeniusSq F + vectorSqNorm (Structured.wStar Q M y 0))
  have hqRpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hFpos : 0 < frobeniusSq F := by
    exact lt_of_lt_of_le (mul_pos hrho (sq_pos_of_pos hqRpos)) hFrob
  have hbaseNonneg : 0 ≤
      2 * frobeniusSq F + vectorSqNorm (Structured.wStar Q M y 0) := by
    unfold vectorSqNorm
    positivity
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    have hnorm : 0 ≤ vectorSqNorm (Structured.wStar Q M y 0) := by
      unfold vectorSqNorm
      positivity
    exact Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hFpos) hnorm)
  have hproxyRaw := structuredResidualVarianceProxy_le_baseVariance
    hrho Q F G y hFrob
  have hproxy :
      (1 / 4 : ℝ) * vectorSqNorm
          (Structured.centeredProjection Q *ᵥ y) +
        (1 / 32 : ℝ) * frobeniusSq M ≤
      (1 + 1 / (32 * rho)) * sigma ^ 2 := by
    dsimp only [M] at hproxyRaw ⊢
    rw [show sigma ^ 2 =
        2 * frobeniusSq F + vectorSqNorm
          (Structured.wStar Q (RobustRank.graphAdjacencyMatrix G) y 0) by
      dsimp only [sigma, M]
      exact Real.sq_sqrt hbaseNonneg]
    exact hproxyRaw
  have hMsymm : ∀ i j, M i j = M j i := by
    intro i j
    have h := congrFun (congrFun (graphAdjacencyMatrix_transpose G) i) j
    exact h.symm
  have hMdiag : ∀ i, M i i = 0 := by
    intro i
    exact RobustRank.graphAdjacencyMatrix_diag G i
  simpa only [M] using
    (finProbability_structuredResidual_polynomial_tail_le hq Q M hQ
      hMsymm hMdiag E y hsigma hproxy)

/-- The positive-coordinate-set presentation and the Boolean-function
presentation of a Rademacher event have the same normalized probability. -/
lemma uniformProbability_signOfSet_eq_finProbability
    {q : ℕ} (A : (Fin q → ℝ) → Prop) :
    Concentration.uniformProbability
        (fun S : Finset (Fin q) ↦ A (signOfSet S)) =
      Fourier.finProbability (Fin q → Bool)
        (fun xi ↦ A (fun i ↦ Fourier.rademacherSign (xi i))) := by
  let e : (Fin q → Bool) ≃ Finset (Fin q) := boolFunEquivFinset
  have hsign (xi : Fin q → Bool) :
      signOfSet (e xi) = fun i ↦ Fourier.rademacherSign (xi i) := by
    funext i
    cases hxi : xi i <;>
      simp [e, boolFunEquivFinset, signOfSet,
        Fourier.rademacherSign, hxi]
  calc
    Concentration.uniformProbability
        (fun S : Finset (Fin q) ↦ A (signOfSet S)) =
        Concentration.uniformProbability
          (fun xi : Fin q → Bool ↦ A (signOfSet (e xi))) :=
      (RLCD.BucketDecomposition.uniformProbability_equiv e
        (fun S : Finset (Fin q) ↦ A (signOfSet S))).symm
    _ = Concentration.uniformProbability
          (fun xi : Fin q → Bool ↦
            A (fun i ↦ Fourier.rademacherSign (xi i))) := by
      congr 1
      funext xi
      rw [hsign]
    _ = Fourier.finProbability (Fin q → Bool)
          (fun xi ↦ A (fun i ↦ Fourier.rademacherSign (xi i))) :=
      (BoundedWindowAnalytic.finProbability_eq_uniformProbability _).symm

/-- Set-valued form of the Step 7 far-residual estimate.  This is the exact
law used after conditioning the covered coordinates by their bucket-count
vector. -/
lemma uniformProbability_graphStructuredResidual_polynomial_tail_le
    {q : ℕ} (hq : 0 < q) {rho : ℝ} (hrho : 0 < rho)
    (Q F : Matrix (Fin q) (Fin q) ℝ) (G : SimpleGraph (Fin q))
    (hQ : Structured.IsOrthogonalProjection Q) (E : ℝ) (y : Fin q → ℝ)
    (hFrob : rho * (q : ℝ) ^ 2 ≤ frobeniusSq F) :
    let sigma := Real.sqrt
      (2 * frobeniusSq F + vectorSqNorm
        (Structured.wStar Q (RobustRank.graphAdjacencyMatrix G) y 0))
    Concentration.uniformProbability (fun S : Finset (Fin q) ↦
        sigma * scale q (1 / 20 : ℝ) ≤
          |Structured.structuredQuadratic E
              (RobustRank.graphAdjacencyMatrix G) y (signOfSet S) - E -
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q (signOfSet S))|) ≤
      (9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        (1 + 1 / (32 * rho)) ^ 32) * scale q (-16 / 5 : ℝ) := by
  dsimp only
  let sigma := Real.sqrt
    (2 * frobeniusSq F + vectorSqNorm
      (Structured.wStar Q (RobustRank.graphAdjacencyMatrix G) y 0))
  have htail := finProbability_graphStructuredResidual_polynomial_tail_le
    hq hrho Q F G hQ E y hFrob
  dsimp only at htail
  let A : (Fin q → ℝ) → Prop := fun x ↦
    sigma * scale q (1 / 20 : ℝ) ≤
      |Structured.structuredQuadratic E
          (RobustRank.graphAdjacencyMatrix G) y x - E -
        (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q x)|
  rw [uniformProbability_signOfSet_eq_finProbability A]
  simpa only [A, sigma] using htail

/-- Exact decomposition of the deterministic conditional center into its
zero-count part, the linear count shift, and the quadratic count shift. -/
lemma conditionalShift_eq_base_add_countVectorShifts
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (E : ℝ) (y : Fin n → ℝ)
    (ell : BucketCountVector P) :
    Structured.conditionalShift E
        (RobustRank.graphAdjacencyMatrix G) y
        (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val)) =
      E + countVectorLinearShift P hbucket y ell +
        countVectorQuadraticShift P hbucket G ell := by
  rfl

/-- Pointwise version of the conditioning bridge.  Unlike the older
uniform wrapper, this asks Claim 12.1 only at the translated target that is
actually used by the ambient window event. -/
lemma conditionedProductSlice_window_upper_of_claim121_at
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (ell : Fin (Fintype.card D.BlockIndex) → ℕ)
    [Nonempty (ProductSlicePoint D.finCoveredPartition ell)]
    {B K x : ℝ}
    (hupper :
      let Gc := D.finCoveredGraph G
      let cc := D.conditionedCoveredCoefficient G cvec O
      let E := GraphQuadratic.graphSliceConstant Gc
        (Probability.perturbedEdgePolynomial G e0 cvec O) cc
      let y := GraphQuadratic.graphEffectiveLinear Gc cc
      let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose Gc
      let f := Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix Gc) y
        (productSliceDelta D.finCoveredPartition hbucket.choose ell)
      let shift := Structured.conditionalShift E
        (RobustRank.graphAdjacencyMatrix Gc) y
        (productSliceDelta D.finCoveredPartition hbucket.choose ell) + trace F
      Esseen.smallBall
          (Esseen.finiteUniformLaw
            (ProductSlicePoint D.finCoveredPartition ell)
            (productSliceQuadratic D.finCoveredPartition ell
              (-trace F) f F)) B (x - shift) ≤ K) :
    Concentration.uniformProbability
        (fun S : ProductSlicePoint D.finCoveredPartition ell ↦
          |Probability.perturbedEdgePolynomial G e0 cvec
              (O ∪ D.finCoveredSubsetImage S.1) - x| ≤ B) ≤ K := by
  classical
  let Gc := D.finCoveredGraph G
  let cc := D.conditionedCoveredCoefficient G cvec O
  let E := GraphQuadratic.graphSliceConstant Gc
    (Probability.perturbedEdgePolynomial G e0 cvec O) cc
  let y := GraphQuadratic.graphEffectiveLinear Gc cc
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose Gc
  let f := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta D.finCoveredPartition hbucket.choose ell)
  let shift := Structured.conditionalShift E
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta D.finCoveredPartition hbucket.choose ell) + trace F
  have hpoly (S : ProductSlicePoint D.finCoveredPartition ell) :
      Probability.perturbedEdgePolynomial G e0 cvec
          (O ∪ D.finCoveredSubsetImage S.1) =
        shift + productSliceQuadratic D.finCoveredPartition ell
          (-trace F) f F S := by
    have hconditioned :=
      (D.sliceQuadratic_conditionedCovered_eq G e0 cvec hO S.1).symm
    have hslice :=
      sliceQuadratic_graph_eq_shift_add_productSlice_counts
        D.finCoveredPartition hbucket ell Gc
          (Probability.perturbedEdgePolynomial G e0 cvec O) cc S
    exact hconditioned.trans (by
      simpa only [Gc, cc, E, y, F, f, shift, add_assoc] using hslice)
  have hevent :
      (fun S : ProductSlicePoint D.finCoveredPartition ell ↦
        |Probability.perturbedEdgePolynomial G e0 cvec
            (O ∪ D.finCoveredSubsetImage S.1) - x| ≤ B) =
      (fun S ↦
        |productSliceQuadratic D.finCoveredPartition ell
            (-trace F) f F S - (x - shift)| ≤ B) := by
    funext S
    rw [hpoly S]
    congr 2 <;> ring
  rw [hevent]
  change Fourier.finProbability
      (ProductSlicePoint D.finCoveredPartition ell)
        (fun S ↦
          |productSliceQuadratic D.finCoveredPartition ell
              (-trace F) f F S - (x - shift)| ≤ B) ≤ K
  rw [← Esseen.smallBall_finiteUniformLaw]
  simpa only [Gc, cc, E, y, F, f, shift] using hupper

/-- The conditional ambient window probability at one covered count
vector. -/
noncomputable def conditionedCountVectorWindowProbability
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    (O : Finset (Fin n)) (B target : ℝ)
    (ell : BucketCountVector D.finCoveredPartition) : ℝ :=
  Concentration.uniformProbability
    (fun S : ProductSlicePoint D.finCoveredPartition
        (fun j ↦ (ell j).val) ↦
      |Probability.perturbedEdgePolynomial G e0 cvec
          (O ∪ D.finCoveredSubsetImage S.1) - target| ≤ B)

/-- The translated center occurring in the centered product-slice law. -/
noncomputable def conditionedCountVectorBaseCenter
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (target : ℝ) : ℝ :=
  target -
    GraphQuadratic.graphSliceConstant (D.finCoveredGraph G)
      (Probability.perturbedEdgePolynomial G e0 cvec O)
      (D.conditionedCoveredCoefficient G cvec O) -
    trace (bucketCenteredAdjacency D.finCoveredPartition.bucket
      hbucket.choose (D.finCoveredGraph G))

/-- The center fed to the pointwise nonuniform Claim 12.1 estimate at one
count vector. -/
noncomputable def conditionedCountVectorTargetOffset
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (target : ℝ) (ell : BucketCountVector D.finCoveredPartition) : ℝ :=
  conditionedCountVectorBaseCenter D G e0 cvec O hbucket target -
    countVectorLinearShift D.finCoveredPartition hbucket
      (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
        (D.conditionedCoveredCoefficient G cvec O)) ell -
    countVectorQuadraticShift D.finCoveredPartition hbucket
      (D.finCoveredGraph G) ell

/-- Near-balanced count vectors whose projected linear shift lies in the
moderate region used in Step 7.  The center omits `trace F`, because this is
the form for which failure of the moderate condition forces the full
structured residual to be large. -/
def conditionedCountVectorGood
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (delta target radius : ℝ)
    (ell : BucketCountVector D.finCoveredPartition) : Prop :=
  IsNearBalanced delta D.finCoveredPartition (fun j ↦ (ell j).val) ∧
    |countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell -
      (target - GraphQuadratic.graphSliceConstant (D.finCoveredGraph G)
        (Probability.perturbedEdgePolynomial G e0 cvec O)
        (D.conditionedCoveredCoefficient G cvec O))| ≤ radius

lemma conditionedCountVectorWindowProbability_nonneg
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    (O : Finset (Fin n)) (B target : ℝ)
    (ell : BucketCountVector D.finCoveredPartition) :
    0 ≤ conditionedCountVectorWindowProbability
      D G e0 cvec O B target ell := by
  unfold conditionedCountVectorWindowProbability
  exact Concentration.uniformProbability_nonneg _

/-- A conditioned Claim 12.1 certificate bounds the actual ambient window
probability at each near-balanced count vector, with exactly the scale and
translated center used by the four-way average. -/
lemma conditionedCountVectorWindowProbability_le_of_claim121
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {delta B eta : ℝ}
    (hclaim : ∀ ell : Fin (Fintype.card D.BlockIndex) → ℕ,
      IsNearBalanced delta D.finCoveredPartition ell →
      ∃ hleft : Nonempty (ProductSlicePoint D.finCoveredPartition ell),
        letI := hleft
        let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
          hbucket.choose (D.finCoveredGraph G)
        let f := Structured.wStar
          (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
          (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G cvec O))
          (productSliceDelta D.finCoveredPartition hbucket.choose ell)
        let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
        0 < sigma ∧ ∀ z : ℝ,
          Esseen.smallBall
              (Esseen.finiteUniformLaw
                (ProductSlicePoint D.finCoveredPartition ell)
                (productSliceQuadratic D.finCoveredPartition ell
                  (-trace F) f F)) B z ≤
            Esseen.relativeEsseenConstant *
              (B ^ 2 / (z ^ 2 + sigma ^ 2) +
                (B / (eta * sigma)) *
                  Real.exp (-eta * |z| / (2 * sigma)) +
                B * scale (Fintype.card D.Covered) (-6 / 5 : ℝ)))
    (ell : BucketCountVector D.finCoveredPartition)
    (hbalanced : IsNearBalanced delta D.finCoveredPartition
      (fun j ↦ (ell j).val)) (target : ℝ) :
    conditionedCountVectorWindowProbability D G e0 cvec O B target ell ≤
      Esseen.relativeEsseenConstant *
        (B ^ 2 /
            (conditionedCountVectorTargetOffset
                D G e0 cvec O hbucket target ell ^ 2 +
              countVectorClaim121Scale D G cvec O hbucket ell ^ 2) +
          (B / (eta *
              countVectorClaim121Scale D G cvec O hbucket ell)) *
            Real.exp (-eta *
              |conditionedCountVectorTargetOffset
                D G e0 cvec O hbucket target ell| /
              (2 * countVectorClaim121Scale
                D G cvec O hbucket ell)) +
          B * scale (Fintype.card D.Covered) (-6 / 5 : ℝ)) := by
  obtain ⟨hleft, hsigma, hupper⟩ :=
    hclaim (fun j ↦ (ell j).val) hbalanced
  letI := hleft
  let Gc := D.finCoveredGraph G
  let cc := D.conditionedCoveredCoefficient G cvec O
  let E := GraphQuadratic.graphSliceConstant Gc
    (Probability.perturbedEdgePolynomial G e0 cvec O) cc
  let y := GraphQuadratic.graphEffectiveLinear Gc cc
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose Gc
  let dvec := productSliceDelta D.finCoveredPartition hbucket.choose
    (fun j ↦ (ell j).val)
  let f := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix Gc) y dvec
  let shift := Structured.conditionalShift E
    (RobustRank.graphAdjacencyMatrix Gc) y dvec + trace F
  have hshift : target - shift =
      conditionedCountVectorTargetOffset
        D G e0 cvec O hbucket target ell := by
    have hdecomp := conditionalShift_eq_base_add_countVectorShifts
      D.finCoveredPartition hbucket Gc E y ell
    dsimp only [shift, dvec]
    rw [hdecomp]
    dsimp only [conditionedCountVectorTargetOffset,
      conditionedCountVectorBaseCenter, Gc, cc, E, y, F]
    ring
  have hpoint := hupper (target - shift)
  have hpoint' :
      Esseen.smallBall
          (Esseen.finiteUniformLaw
            (ProductSlicePoint D.finCoveredPartition
              (fun j ↦ (ell j).val))
            (productSliceQuadratic D.finCoveredPartition
              (fun j ↦ (ell j).val) (-trace F) f F))
          B (conditionedCountVectorTargetOffset
            D G e0 cvec O hbucket target ell) ≤
        Esseen.relativeEsseenConstant *
          (B ^ 2 /
              (conditionedCountVectorTargetOffset
                  D G e0 cvec O hbucket target ell ^ 2 +
                countVectorClaim121Scale D G cvec O hbucket ell ^ 2) +
            (B / (eta *
                countVectorClaim121Scale D G cvec O hbucket ell)) *
              Real.exp (-eta *
                |conditionedCountVectorTargetOffset
                  D G e0 cvec O hbucket target ell| /
                (2 * countVectorClaim121Scale
                  D G cvec O hbucket ell)) +
            B * scale (Fintype.card D.Covered) (-6 / 5 : ℝ)) := by
    rw [hshift] at hpoint
    simpa only [Gc, cc, y, F, f, dvec, countVectorClaim121Scale]
      using hpoint
  have hbridge :
      Esseen.smallBall
          (Esseen.finiteUniformLaw
            (ProductSlicePoint D.finCoveredPartition
              (fun j ↦ (ell j).val))
            (productSliceQuadratic D.finCoveredPartition
              (fun j ↦ (ell j).val) (-trace F) f F))
          B (target - shift) ≤
        Esseen.relativeEsseenConstant *
          (B ^ 2 /
              (conditionedCountVectorTargetOffset
                  D G e0 cvec O hbucket target ell ^ 2 +
                countVectorClaim121Scale D G cvec O hbucket ell ^ 2) +
            (B / (eta *
                countVectorClaim121Scale D G cvec O hbucket ell)) *
              Real.exp (-eta *
                |conditionedCountVectorTargetOffset
                  D G e0 cvec O hbucket target ell| /
                (2 * countVectorClaim121Scale
                  D G cvec O hbucket ell)) +
            B * scale (Fintype.card D.Covered) (-6 / 5 : ℝ)) := by
    simpa only [hshift] using hpoint'
  have hambient := conditionedProductSlice_window_upper_of_claim121_at
    D G e0 cvec hO hbucket (fun j ↦ (ell j).val)
      (x := target) hbridge
  simpa only [conditionedCountVectorWindowProbability] using hambient

/-- Count-vector form of conditioned Claim 12.2, with precisely the weights
appearing in the structured law of total probability. -/
theorem conditionedClaim122Bound_countVector
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {K : ℝ} (hclaim : ConditionedClaim122Bound D G c O hbucket K) :
    ∀ a b : ℝ,
      ‖bucketCenteredAdjacency D.finCoveredPartition.bucket hbucket.choose
          (D.finCoveredGraph G)‖ ≤ b - a →
      ∑ ell : BucketCountVector D.finCoveredPartition,
        (Fintype.card
            (ProductSlicePoint D.finCoveredPartition
              (fun j ↦ (ell j).val)) : ℝ) /
            Fintype.card (Finset (Fin (Fintype.card D.Covered))) *
          (if a ≤ countVectorLinearShift D.finCoveredPartition hbucket
                (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                  (D.conditionedCoveredCoefficient G c O)) ell ∧
              countVectorLinearShift D.finCoveredPartition hbucket
                (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                  (D.conditionedCoveredCoefficient G c O)) ell ≤ b then
            countVectorShiftMoment D.finCoveredPartition hbucket
              (D.finCoveredGraph G) ell
          else 0) ≤
        K * Real.sqrt (Fintype.card D.Covered) * (b - a) := by
  intro a b hab
  have hraw := hclaim a b hab
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G c O)
  let Phi : (Fin (Fintype.card D.Covered) → ℝ) → ℝ := fun d ↦
    if a ≤ (1 / 2 : ℝ) * (y ⬝ᵥ d) ∧
        (1 / 2 : ℝ) * (y ⬝ᵥ d) ≤ b then
      ((1 / 8 : ℝ) *
        (d ⬝ᵥ (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G) *ᵥ d))) ^ 2 +
      ∑ i, ((1 / 4 : ℝ) *
        (Structured.centeredProjection
            (bucketProjectionMatrix D.finCoveredPartition.bucket
              hbucket.choose) *ᵥ
          (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G) *ᵥ d)) i) ^ 2
    else 0
  have hmix := finExpectation_delta_eq_sum_countVector
    D.finCoveredPartition hbucket Phi
  have hraw' :
      Fourier.finExpectation (Fin (Fintype.card D.Covered) → Bool)
          (fun xi ↦ Phi (Structured.delta
            (bucketProjectionMatrix D.finCoveredPartition.bucket
              hbucket.choose)
            (fun i ↦ Fourier.rademacherSign (xi i)))) ≤
        K * Real.sqrt (Fintype.card D.Covered) * (b - a) := by
    simpa only [Phi, y, bucketShiftResidualMatrix, Structured.delta,
      Matrix.mulVec_mulVec] using hraw
  rw [hmix] at hraw'
  simpa only [Phi, y, countVectorLinearShift, countVectorShiftMoment,
    bucketShiftResidualMatrix, Structured.delta, Matrix.mulVec_mulVec]
    using hraw'

/-- Markov consequence of Claim 12.2 in the actual count-vector law.  It
controls simultaneous membership in a linear-shift interval and a large
quadratic/variance shift. -/
theorem countVectorMass_largeShiftMoment_interval_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {K : ℝ} (hclaim : ConditionedClaim122Bound D G c O hbucket K)
    (a b T : ℝ) (hT : 0 < T)
    (hab : ‖bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose (D.finCoveredGraph G)‖ ≤ b - a) :
    countVectorMass D.finCoveredPartition (fun ell ↦
        a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G c O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G c O)) ell ≤ b ∧
          T ≤ countVectorShiftMoment D.finCoveredPartition hbucket
            (D.finCoveredGraph G) ell) ≤
      (K * Real.sqrt (Fintype.card D.Covered) * (b - a)) / T := by
  let P := D.finCoveredPartition
  let E : BucketCountVector P → ℝ := fun ell ↦
    countVectorLinearShift P hbucket
      (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
        (D.conditionedCoveredCoefficient G c O)) ell
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
  have hmoment := conditionedClaim122Bound_countVector
    D G c O hbucket hclaim a b hab
  have hmarkov :
      T * countVectorMass P (fun ell ↦
          a ≤ E ell ∧ E ell ≤ b ∧ T ≤ W ell) ≤
        ∑ ell : BucketCountVector P,
          (Fintype.card
              (ProductSlicePoint P (fun j ↦ (ell j).val)) : ℝ) /
              Fintype.card (Finset (Fin (Fintype.card D.Covered))) *
            (if a ≤ E ell ∧ E ell ≤ b then W ell else 0) := by
    rw [countVectorMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ell hell
    let weight : ℝ :=
      (Fintype.card
          (ProductSlicePoint P (fun j ↦ (ell j).val)) : ℝ) /
        Fintype.card (Finset (Fin (Fintype.card D.Covered)))
    have hweight : 0 ≤ weight := by
      dsimp only [weight]
      positivity
    by_cases hE : a ≤ E ell ∧ E ell ≤ b ∧ T ≤ W ell
    · have hinterval : a ≤ E ell ∧ E ell ≤ b :=
        ⟨hE.1, hE.2.1⟩
      simp only [if_pos hE, if_pos hinterval]
      change T * weight ≤ weight * W ell
      rw [mul_comm T weight]
      exact mul_le_mul_of_nonneg_left hE.2.2 hweight
    · simp only [if_neg hE]
      by_cases hinterval : a ≤ E ell ∧ E ell ≤ b
      · rw [if_pos hinterval]
        simpa only [mul_zero, weight, W] using
          mul_nonneg hweight
            (countVectorShiftMoment_nonneg P hbucket
              (D.finCoveredGraph G) ell)
      · rw [if_neg hinterval]
        simpa only [zero_mul, mul_zero, weight] using
          mul_nonneg hweight le_rfl
  apply (le_div_iff₀ hT).2
  calc
    countVectorMass P (fun ell ↦
        a ≤ E ell ∧ E ell ≤ b ∧ T ≤ W ell) * T =
        T * countVectorMass P (fun ell ↦
          a ≤ E ell ∧ E ell ≤ b ∧ T ≤ W ell) := by ring
    _ ≤ ∑ ell : BucketCountVector P,
          (Fintype.card
              (ProductSlicePoint P (fun j ↦ (ell j).val)) : ℝ) /
              Fintype.card (Finset (Fin (Fintype.card D.Covered))) *
            (if a ≤ E ell ∧ E ell ≤ b then W ell else 0) := hmarkov
    _ ≤ K * Real.sqrt (Fintype.card D.Covered) * (b - a) := by
      simpa only [P, E, W] using hmoment

/-- Claim 12.2 gives the exact geometric mass decay of every concrete
`(dyadic shift level, spatial cell)` fiber.  This is the missing
source-facing mass hypothesis of
`weighted_claim121_bounded_scale_double_cells`. -/
theorem countVectorMass_claim121ShiftDyadicCell_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {K base center : ℝ} (hK : 0 ≤ K) (hbase : 0 < base)
    (hFnorm : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ 16 * base)
    (hclaim : ConditionedClaim122Bound D G c O hbucket K)
    (i j : ℕ) :
    let P := D.finCoveredPartition
    let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O)
    let L : BucketCountVector P → ℝ := fun ell ↦
      countVectorLinearShift P hbucket y ell
    let W : BucketCountVector P → ℝ := fun ell ↦
      countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
    countVectorMass P (fun ell ↦
        base ^ 2 ≤ W ell ∧ claim121ShiftDyadicLevel base (W ell) = i ∧
          claim121ShiftSpatialCell center base (W ell) (L ell) = j) ≤
      (40 * K * Real.sqrt (Fintype.card D.Covered) / base) *
        (1 / 2 : ℝ) ^ i := by
  dsimp only
  let P := D.finCoveredPartition
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G c O)
  let L : BucketCountVector P → ℝ := fun ell ↦
    countVectorLinearShift P hbucket y ell
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
  let s : ℝ := (2 : ℝ) ^ i * base
  let buffer : ℝ := 4 * s
  let width : ℝ := 16 * s
  let R : BucketCountVector P → Prop := fun ell ↦ s ^ 2 ≤ W ell
  let rate : ℝ := K * Real.sqrt (Fintype.card D.Covered) / s ^ 2
  have hs : 0 < s := by dsimp only [s]; positivity
  have hbuffer : 0 ≤ buffer := by dsimp only [buffer]; positivity
  have hwidth : 0 < width := by dsimp only [width]; positivity
  have hrate : 0 ≤ rate := by dsimp only [rate]; positivity
  have hinterval : ∀ a b : ℝ, width ≤ b - a →
      countVectorMass P (fun ell ↦ R ell ∧ a ≤ L ell ∧ L ell ≤ b) ≤
        rate * (b - a) := by
    intro a b hab
    have hnormWidth : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ b - a := by
      apply hFnorm.trans
      apply (show 16 * base ≤ width from ?_).trans hab
      dsimp only [width, s]
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ i :=
        one_le_pow₀ (n := i) (by norm_num)
      nlinarith
    have hraw := countVectorMass_largeShiftMoment_interval_le
      D G c O hbucket hclaim a b (s ^ 2) (sq_pos_of_pos hs) hnormWidth
    calc
      countVectorMass P (fun ell ↦ R ell ∧ a ≤ L ell ∧ L ell ≤ b) =
          countVectorMass P (fun ell ↦
            a ≤ L ell ∧ L ell ≤ b ∧ s ^ 2 ≤ W ell) := by
        apply congrArg (countVectorMass P)
        funext ell
        simp only [R, and_assoc, and_left_comm, and_comm]
      _ ≤ (K * Real.sqrt (Fintype.card D.Covered) * (b - a)) /
          s ^ 2 := by
        simpa only [P, L, W, y] using hraw
      _ = rate * (b - a) := by
        dsimp only [rate]
        ring
  have hcell := countVectorMass_and_bufferedAbsoluteCellIndex_le
    (center := center) P L R hbuffer hwidth hrate hinterval j
  have hsubset : ∀ ell : BucketCountVector P,
      base ^ 2 ≤ W ell ∧ claim121ShiftDyadicLevel base (W ell) = i ∧
          claim121ShiftSpatialCell center base (W ell) (L ell) = j →
        R ell ∧ bufferedAbsoluteCellIndex center buffer width (L ell) = j := by
    intro ell hell
    have hW : 0 ≤ W ell := by
      dsimp only [W]
      exact countVectorShiftMoment_nonneg P hbucket (D.finCoveredGraph G) ell
    have hthreshold := claim121DyadicLevel_sqrt_sq_lower hbase hW hell.1
    have hlevel : claim121DyadicLevel base (Real.sqrt (W ell)) = i := by
      simpa only [claim121ShiftDyadicLevel] using hell.2.1
    rw [hlevel] at hthreshold
    refine ⟨?_, ?_⟩
    · simpa only [R, s] using hthreshold
    · simpa only [claim121ShiftSpatialCell, claim121ShiftDyadicLevel,
        hlevel, buffer, width, s] using hell.2.2
  calc
    countVectorMass P (fun ell ↦
        base ^ 2 ≤ W ell ∧ claim121ShiftDyadicLevel base (W ell) = i ∧
          claim121ShiftSpatialCell center base (W ell) (L ell) = j) ≤
      countVectorMass P (fun ell ↦ R ell ∧
        bufferedAbsoluteCellIndex center buffer width (L ell) = j) :=
      countVectorMass_mono P hsubset
    _ ≤ 2 * rate * (buffer + width) := hcell
    _ = (40 * K * Real.sqrt (Fintype.card D.Covered) / base) *
        (1 / 2 : ℝ) ^ i := by
      dsimp only [rate, buffer, width, s]
      have hp : 0 < (2 : ℝ) ^ i := pow_pos (by norm_num) i
      have hhalf : (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ i = 1 := by
        rw [← mul_pow]
        norm_num
      field_simp
      calc
        2 * K * Real.sqrt (Fintype.card D.Covered) * (4 + 16) =
            K * Real.sqrt (Fintype.card D.Covered) * 40 := by ring
        _ = K * Real.sqrt (Fintype.card D.Covered) * 40 *
            ((1 / 2 : ℝ) ^ i * (2 : ℝ) ^ i) := by rw [hhalf]; ring
        _ = K * Real.sqrt (Fintype.card D.Covered) *
            (2 : ℝ) ^ i * 40 * (1 / 2 : ℝ) ^ i := by ring

/-- Fully instantiated high-shift Claim 12.1/12.2 summation on one
structured decomposition.  All dyadic levels, spatial cells, and their
geometric mass estimates are discharged internally. -/
theorem countVector_weighted_claim121_shift_dominated
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (cond sigma x : BucketCountVector D.finCoveredPartition → ℝ)
    (Good : BucketCountVector D.finCoveredPartition → Prop)
    {K base center Pgood c B eta err : ℝ}
    (hK : 0 ≤ K) (hbase : 1 ≤ base) (hPgood : 0 ≤ Pgood)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (heta : 0 < eta) (herr : 0 ≤ err)
    (hFnorm : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ 16 * base)
    (hclaim : ConditionedClaim122Bound D G cvec O hbucket K)
    (hgoodMass : countVectorMass D.finCoveredPartition Good ≤ Pgood)
    (hgoodW : ∀ ell, Good ell → base ^ 2 ≤
      countVectorShiftMoment D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell)
    (hsigmaLower : ∀ ell, Good ell → base ≤ sigma ell)
    (hsigmaUpper : ∀ ell, Good ell → sigma ell ≤
      2 * Real.sqrt (countVectorShiftMoment D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell))
    (hx : ∀ ell, Good ell → x ell = center -
      countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell -
      countVectorQuadraticShift D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then cond ell else 0) ≤
      c * (((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt (Fintype.card D.Covered) / base) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / base) +
        Pgood * (B * err)) := by
  let P := D.finCoveredPartition
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G cvec O)
  let L : BucketCountVector P → ℝ := fun ell ↦
    countVectorLinearShift P hbucket y ell
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
  let qshift : BucketCountVector P → ℝ := fun ell ↦
    countVectorQuadraticShift P hbucket (D.finCoveredGraph G) ell
  have hbasePos : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  apply countVector_weighted_claim121_shift_dominated_cells
    (A := 40 * K * Real.sqrt (Fintype.card D.Covered) / base)
    (Pgood := Pgood) (c := c) (B := B) (eta := eta)
    (base := base) (center := center) (err := err)
    P L W qshift cond sigma x Good
  · positivity
  · exact hPgood
  · exact hc
  · exact hB
  · exact heta
  · exact hbase
  · exact herr
  · intro ell
    dsimp only [W]
    exact countVectorShiftMoment_nonneg P hbucket (D.finCoveredGraph G) ell
  · simpa only [P] using hgoodMass
  · intro ell hell
    simpa only [P, W] using hgoodW ell hell
  · intro i j
    simpa only [P, L, W, y] using
      countVectorMass_claim121ShiftDyadicCell_le D G cvec O hbucket hK
        hbasePos hFnorm hclaim i j
  · intro ell
    dsimp only [qshift, W]
    exact sq_countVectorQuadraticShift_le_shiftMoment
      P hbucket (D.finCoveredGraph G) ell
  · intro ell hell
    simpa only [P] using hsigmaLower ell hell
  · intro ell hell
    simpa only [P, W] using hsigmaUpper ell hell
  · intro ell hell
    simpa only [P, L, W, qshift, y] using hx ell hell
  · intro ell hell
    simpa only [P] using hcond ell hell

/-- Fully instantiated low-shift summation on one structured
decomposition.  This is the companion to
`countVector_weighted_claim121_shift_dominated` for the two fixed-scale
branches of the four-way partition. -/
theorem countVector_weighted_claim121_low_shift
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (cond sigma x : BucketCountVector D.finCoveredPartition → ℝ)
    (Good : BucketCountVector D.finCoveredPartition → Prop)
    {center rate c B eta base kappa err Pgood : ℝ}
    (hrate : 0 ≤ rate) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (heta : 0 < eta) (hbase : 1 ≤ base) (hkappa : 0 < kappa)
    (herr : 0 ≤ err)
    (hinterval : ∀ a b : ℝ, kappa * base ≤ b - a →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        rate * (b - a))
    (hgoodMass : countVectorMass D.finCoveredPartition Good ≤ Pgood)
    (hgoodW : ∀ ell, Good ell →
      countVectorShiftMoment D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell ≤ base ^ 2)
    (hsigmaLower : ∀ ell, Good ell → base / 2 ≤ sigma ell)
    (hsigmaUpper : ∀ ell, Good ell → sigma ell ≤ 2 * base)
    (hx : ∀ ell, Good ell → x ell = center -
      countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell -
      countVectorQuadraticShift D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then cond ell else 0) ≤
      c * ((2 * rate * (2 * base + kappa * base)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) / base +
        Pgood * (B * err)) := by
  let P := D.finCoveredPartition
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G cvec O)
  let L : BucketCountVector P → ℝ := fun ell ↦
    countVectorLinearShift P hbucket y ell
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
  let qshift : BucketCountVector P → ℝ := fun ell ↦
    countVectorQuadraticShift P hbucket (D.finCoveredGraph G) ell
  apply countVector_weighted_claim121_low_shift_cells
    (center := center) (rate := rate) (c := c) (B := B) (eta := eta)
    (base := base) (kappa := kappa) (err := err) (Pgood := Pgood)
    P L W qshift cond sigma x Good
  · exact hrate
  · exact hc
  · exact hB
  · exact heta
  · exact hbase
  · exact hkappa
  · exact herr
  · simpa only [P, L, y] using hinterval
  · simpa only [P] using hgoodMass
  · intro ell
    dsimp only [W]
    exact countVectorShiftMoment_nonneg P hbucket (D.finCoveredGraph G) ell
  · intro ell hell
    simpa only [P, W] using hgoodW ell hell
  · intro ell
    dsimp only [qshift, W]
    exact sq_countVectorQuadraticShift_le_shiftMoment
      P hbucket (D.finCoveredGraph G) ell
  · intro ell hell
    simpa only [P] using hsigmaLower ell hell
  · intro ell hell
    simpa only [P] using hsigmaUpper ell hell
  · intro ell hell
    simpa only [P, L, qshift, y] using hx ell hell
  · intro ell hell
    simpa only [P] using hcond ell hell

/-- The four source branches of the count-vector averaging argument,
assembled from the fixed-scale and dyadic summation lemmas.  The statement
keeps the two admissible interval estimates separate: later applications
use Claim 12.2 at the Frobenius scale and at the zero-count scale. -/
theorem countVector_weighted_claim121_four_way
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (cond sigma x : BucketCountVector D.finCoveredPartition → ℝ)
    (Good : BucketCountVector D.finCoveredPartition → Prop)
    {K center rateF rate0 c B eta err Pgood
      frobBase sigma0 kappaF kappa0 : ℝ}
    (hK : 0 ≤ K) (hrateF : 0 ≤ rateF) (hrate0 : 0 ≤ rate0)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (heta : 0 < eta)
    (herr : 0 ≤ err) (hPgood : 0 ≤ Pgood)
    (hfrobBase : 1 ≤ frobBase) (hsigma0 : 2 ≤ sigma0)
    (hkappaF : 0 < kappaF) (hkappa0 : 0 < kappa0)
    (hFnormF : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ 16 * frobBase)
    (hFnorm0 : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ 8 * sigma0)
    (hclaim : ConditionedClaim122Bound D G cvec O hbucket K)
    (hintervalF : ∀ a b : ℝ, kappaF * frobBase ≤ b - a →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        rateF * (b - a))
    (hinterval0 : ∀ a b : ℝ, kappa0 * sigma0 ≤ b - a →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        rate0 * (b - a))
    (hgoodMass : countVectorMass D.finCoveredPartition Good ≤ Pgood)
    (hcondNonneg : ∀ ell, 0 ≤ cond ell)
    (hfrobLower : ∀ ell, Good ell → frobBase ≤ sigma ell)
    (hscale : ∀ ell, Good ell →
      sigma ell ≤ 2 * Real.sqrt
          (countVectorShiftMoment D.finCoveredPartition hbucket
            (D.finCoveredGraph G) ell) ∨
        (sigma0 / 2 ≤ sigma ell ∧ sigma ell ≤ 2 * sigma0))
    (hx : ∀ ell, Good ell → x ell = center -
      countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell -
      countVectorQuadraticShift D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 + sigma ell ^ 2) +
        (B / (eta * sigma ell)) *
          Real.exp (-eta * |x ell| / (2 * sigma ell)) + B * err)) :
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then cond ell else 0) ≤
      c * ((2 * rateF * (2 * frobBase + kappaF * frobBase)) *
          (∑' j, claim121ComparableCellKernel B eta kappaF j) /
            frobBase + Pgood * (B * err)) +
      c * (((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt (Fintype.card D.Covered) / frobBase) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / frobBase) +
        Pgood * (B * err)) +
      c * ((2 * rate0 * (2 * sigma0 + kappa0 * sigma0)) *
          (∑' j, claim121ComparableCellKernel B eta kappa0 j) /
            sigma0 + Pgood * (B * err)) +
      c * (((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt (Fintype.card D.Covered) /
                (sigma0 / 2)) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2)) +
        Pgood * (B * err)) := by
  let P := D.finCoveredPartition
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
  let E₁ : BucketCountVector P → Prop := fun ell ↦
    Good ell ∧ sigma ell ≤ 2 * Real.sqrt (W ell) ∧
      W ell ≤ frobBase ^ 2
  let E₂ : BucketCountVector P → Prop := fun ell ↦
    Good ell ∧ sigma ell ≤ 2 * Real.sqrt (W ell) ∧
      frobBase ^ 2 ≤ W ell
  let E₃ : BucketCountVector P → Prop := fun ell ↦
    Good ell ∧ (sigma0 / 2 ≤ sigma ell ∧ sigma ell ≤ 2 * sigma0) ∧
      W ell ≤ sigma0 ^ 2
  let E₄ : BucketCountVector P → Prop := fun ell ↦
    Good ell ∧ (sigma0 / 2 ≤ sigma ell ∧ sigma ell ≤ 2 * sigma0) ∧
      sigma0 ^ 2 ≤ W ell
  have hcover : ∀ ell : BucketCountVector P, Good ell →
      E₁ ell ∨ E₂ ell ∨ E₃ ell ∨ E₄ ell := by
    intro ell hell
    have hfour := claim121_scale_four_way
      (frobBase := frobBase) (hscale ell hell)
    rcases hfour with h1 | h2 | h3 | h4
    · exact Or.inl ⟨hell, h1⟩
    · exact Or.inr (Or.inl ⟨hell, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hell, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hell, h4⟩))
  have hunion := weighted_if_le_sum_four
    (countVectorWeight P) cond Good E₁ E₂ E₃ E₄
    (countVectorWeight_nonneg P) hcondNonneg hcover
  have hmass (E : BucketCountVector P → Prop)
      (hsub : ∀ ell, E ell → Good ell) :
      countVectorMass P E ≤ Pgood :=
    (countVectorMass_mono P hsub).trans (by simpa only [P] using hgoodMass)
  have hWnonneg (ell : BucketCountVector P) : 0 ≤ W ell := by
    dsimp only [W, P]
    exact countVectorShiftMoment_nonneg D.finCoveredPartition hbucket
      (D.finCoveredGraph G) ell
  have h₁ := countVector_weighted_claim121_low_shift
    D G cvec O hbucket cond sigma x E₁
    (center := center) (rate := rateF) (c := c) (B := B) (eta := eta)
    (base := frobBase) (kappa := kappaF) (err := err)
    (Pgood := Pgood) hrateF hc hB heta hfrobBase hkappaF herr
    hintervalF
    (hmass E₁ (by intro ell hell; exact hell.1))
    (by intro ell hell; simpa only [P, W] using hell.2.2)
    (by
      intro ell hell
      have hf : frobBase ≤ sigma ell := hfrobLower ell hell.1
      linarith)
    (by
      intro ell hell
      have hsqrtSq : (Real.sqrt (W ell)) ^ 2 = W ell :=
        Real.sq_sqrt (hWnonneg ell)
      have hWle : W ell ≤ frobBase ^ 2 := hell.2.2
      have hfrobNonneg : 0 ≤ frobBase := by linarith
      have hsqrt : Real.sqrt (W ell) ≤ frobBase := by
        nlinarith [Real.sqrt_nonneg (W ell)]
      exact hell.2.1.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))
    (by intro ell hell; exact hx ell hell.1)
    (by intro ell hell; exact hcond ell hell.1)
  have h₂ := countVector_weighted_claim121_shift_dominated
    D G cvec O hbucket cond sigma x E₂
    (K := K) (base := frobBase) (center := center) (Pgood := Pgood)
    (c := c) (B := B) (eta := eta) (err := err)
    hK hfrobBase hPgood hc hB heta herr hFnormF hclaim
    (hmass E₂ (by intro ell hell; exact hell.1))
    (by intro ell hell; simpa only [P, W] using hell.2.2)
    (by intro ell hell; exact hfrobLower ell hell.1)
    (by intro ell hell; simpa only [P, W] using hell.2.1)
    (by intro ell hell; exact hx ell hell.1)
    (by intro ell hell; exact hcond ell hell.1)
  have h₃ := countVector_weighted_claim121_low_shift
    D G cvec O hbucket cond sigma x E₃
    (center := center) (rate := rate0) (c := c) (B := B) (eta := eta)
    (base := sigma0) (kappa := kappa0) (err := err)
    (Pgood := Pgood) hrate0 hc hB heta (by linarith) hkappa0 herr
    hinterval0
    (hmass E₃ (by intro ell hell; exact hell.1))
    (by intro ell hell; simpa only [P, W] using hell.2.2)
    (by intro ell hell; exact hell.2.1.1)
    (by intro ell hell; exact hell.2.1.2)
    (by intro ell hell; exact hx ell hell.1)
    (by intro ell hell; exact hcond ell hell.1)
  have h₄ := countVector_weighted_claim121_shift_dominated
    D G cvec O hbucket cond sigma x E₄
    (K := K) (base := sigma0 / 2) (center := center) (Pgood := Pgood)
    (c := c) (B := B) (eta := eta) (err := err)
    hK (by linarith) hPgood hc hB heta herr (by nlinarith [hFnorm0]) hclaim
    (hmass E₄ (by intro ell hell; exact hell.1))
    (by
      intro ell hell
      have hs0 : 0 ≤ sigma0 := by linarith
      have hs0sq : (sigma0 / 2) ^ 2 ≤ sigma0 ^ 2 := by nlinarith
      exact hs0sq.trans hell.2.2)
    (by intro ell hell; exact hell.2.1.1)
    (by
      intro ell hell
      have hsqrtSq : (Real.sqrt (W ell)) ^ 2 = W ell :=
        Real.sq_sqrt (hWnonneg ell)
      have hWlower : sigma0 ^ 2 ≤ W ell := hell.2.2
      have hsigma0Nonneg : 0 ≤ sigma0 := by linarith
      have hsqrt : sigma0 ≤ Real.sqrt (W ell) := by
        nlinarith [Real.sqrt_nonneg (W ell)]
      exact hell.2.1.2.trans
        (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))
    (by intro ell hell; exact hx ell hell.1)
    (by intro ell hell; exact hcond ell hell.1)
  calc
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then cond ell else 0) ≤
        (∑ ell : BucketCountVector P,
          countVectorWeight P ell *
            (@ite ℝ (E₁ ell) (Classical.propDecidable _) (cond ell) 0)) +
        (∑ ell : BucketCountVector P,
          countVectorWeight P ell *
            (@ite ℝ (E₂ ell) (Classical.propDecidable _) (cond ell) 0)) +
        (∑ ell : BucketCountVector P,
          countVectorWeight P ell *
            (@ite ℝ (E₃ ell) (Classical.propDecidable _) (cond ell) 0)) +
        (∑ ell : BucketCountVector P,
          countVectorWeight P ell *
            (@ite ℝ (E₄ ell) (Classical.propDecidable _) (cond ell) 0)) := by
      simpa only [P] using hunion
    _ ≤ c * ((2 * rateF * (2 * frobBase + kappaF * frobBase)) *
          (∑' j, claim121ComparableCellKernel B eta kappaF j) /
            frobBase + Pgood * (B * err)) +
        c * (((∑' p : ℕ × ℕ,
            (((40 * K * Real.sqrt (Fintype.card D.Covered) / frobBase) *
                (1 / 2 : ℝ) ^ p.1) *
              claim121ComparableCellKernel B eta 1 p.2)) / frobBase) +
          Pgood * (B * err)) +
        c * ((2 * rate0 * (2 * sigma0 + kappa0 * sigma0)) *
            (∑' j, claim121ComparableCellKernel B eta kappa0 j) /
              sigma0 + Pgood * (B * err)) +
        c * (((∑' p : ℕ × ℕ,
            (((40 * K * Real.sqrt (Fintype.card D.Covered) /
                  (sigma0 / 2)) *
                (1 / 2 : ℝ) ^ p.1) *
              claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2)) +
          Pgood * (B * err)) := by
      exact add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄

/-- Numerical simplification of the four explicit branch bounds.  The two
fixed-scale terms are exactly constant multiples of the interval-mass rate;
the two dyadic terms use the robust Frobenius lower scale.  The Fourier
comparison error is deliberately left multiplied by the mass `Pgood` of
the moderate region. -/
lemma claim121_four_branch_bound_le_scale
    {q : ℕ} (hq : 0 < q)
    {rho K Cmass c B eta kappa frobBase sigma0 Pgood err : ℝ}
    (hrho : 0 < rho) (hK : 0 ≤ K) (hCmass : 0 ≤ Cmass)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (heta : 0 < eta)
    (hfrobBase : 0 < frobBase) (hsigma0 : 0 < sigma0)
    (hbaseFSq : 2 * rho * (q : ℝ) ^ 2 ≤ frobBase ^ 2)
    (hbase0Sq : 2 * (rho / 4) * (q : ℝ) ^ 2 ≤ (sigma0 / 2) ^ 2) :
    c * ((2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
          (2 * frobBase + kappa * frobBase)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) /
            frobBase + Pgood * (B * err)) +
      c * (((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / frobBase) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / frobBase) +
        Pgood * (B * err)) +
      c * ((2 * (Cmass * scale q (-(3 : ℝ) / 2)) *
          (2 * sigma0 + kappa * sigma0)) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) /
            sigma0 + Pgood * (B * err)) +
      c * (((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / (sigma0 / 2)) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2)) +
        Pgood * (B * err)) ≤
      c * ((4 * Cmass * (2 + kappa) *
            (∑' j, claim121ComparableCellKernel B eta kappa j) +
          200 * K / rho *
            (∑' j, claim121ComparableCellKernel B eta 1 j)) *
          scale q (-(3 : ℝ) / 2) +
        4 * Pgood * (B * err)) := by
  let Sk : ℝ := ∑' j, claim121ComparableCellKernel B eta kappa j
  let S1 : ℝ := ∑' j, claim121ComparableCellKernel B eta 1 j
  let rate : ℝ := Cmass * scale q (-(3 : ℝ) / 2)
  let Perr : ℝ := Pgood * (B * err)
  have hlowF :
      (2 * rate * (2 * frobBase + kappa * frobBase)) * Sk /
          frobBase + Perr =
        2 * Cmass * (2 + kappa) * Sk *
          scale q (-(3 : ℝ) / 2) + Perr := by
    dsimp only [rate]
    field_simp [hfrobBase.ne']
  have hlow0 :
      (2 * rate * (2 * sigma0 + kappa * sigma0)) * Sk /
          sigma0 + Perr =
        2 * Cmass * (2 + kappa) * Sk *
          scale q (-(3 : ℝ) / 2) + Perr := by
    dsimp only [rate]
    field_simp [hsigma0.ne']
  have hhighFraw := claim121_shift_dominated_main_le hq hrho hK hB heta
    hfrobBase hbaseFSq
  have hhighF :
      c * ((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / frobBase) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / frobBase + Perr) ≤
        c * ((40 * K / rho * S1) * scale q (-(3 : ℝ) / 2) + Perr) := by
    apply mul_le_mul_of_nonneg_left _ hc
    simpa only [S1, add_comm] using
      add_le_add_right hhighFraw Perr
  have hrho4 : 0 < rho / 4 := by positivity
  have hsigmaHalf : 0 < sigma0 / 2 := by positivity
  have hhigh0raw := claim121_shift_dominated_main_le hq hrho4 hK hB heta
    hsigmaHalf hbase0Sq
  have hhigh0 :
      c * ((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / (sigma0 / 2)) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2) +
          Perr) ≤
        c * ((160 * K / rho * S1) * scale q (-(3 : ℝ) / 2) +
          Perr) := by
    apply mul_le_mul_of_nonneg_left _ hc
    calc
      (∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / (sigma0 / 2)) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2) +
          Perr ≤
        (40 * K / (rho / 4) * S1) * scale q (-(3 : ℝ) / 2) +
          Perr := by
            simpa only [S1, add_comm] using
              add_le_add_right hhigh0raw Perr
      _ = (160 * K / rho * S1) * scale q (-(3 : ℝ) / 2) +
          Perr := by
            congr 2
            field_simp [hrho.ne']
            ring
  change
    c * ((2 * rate * (2 * frobBase + kappa * frobBase)) * Sk /
          frobBase + Perr) +
      c * ((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / frobBase) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / frobBase + Perr) +
      c * ((2 * rate * (2 * sigma0 + kappa * sigma0)) * Sk /
          sigma0 + Perr) +
      c * ((∑' p : ℕ × ℕ,
          (((40 * K * Real.sqrt q / (sigma0 / 2)) *
              (1 / 2 : ℝ) ^ p.1) *
            claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2) +
          Perr) ≤ _
  rw [hlowF, hlow0]
  calc
    c * (2 * Cmass * (2 + kappa) * Sk *
          scale q (-(3 : ℝ) / 2) + Perr) +
        c * ((∑' p : ℕ × ℕ,
            (((40 * K * Real.sqrt q / frobBase) *
                (1 / 2 : ℝ) ^ p.1) *
              claim121ComparableCellKernel B eta 1 p.2)) / frobBase + Perr) +
        c * (2 * Cmass * (2 + kappa) * Sk *
          scale q (-(3 : ℝ) / 2) + Perr) +
        c * ((∑' p : ℕ × ℕ,
            (((40 * K * Real.sqrt q / (sigma0 / 2)) *
                (1 / 2 : ℝ) ^ p.1) *
              claim121ComparableCellKernel B eta 1 p.2)) / (sigma0 / 2) +
          Perr) ≤
        c * (2 * Cmass * (2 + kappa) * Sk *
          scale q (-(3 : ℝ) / 2) + Perr) +
        c * ((40 * K / rho * S1) * scale q (-(3 : ℝ) / 2) + Perr) +
        c * (2 * Cmass * (2 + kappa) * Sk *
          scale q (-(3 : ℝ) / 2) + Perr) +
        c * ((160 * K / rho * S1) * scale q (-(3 : ℝ) / 2) +
          Perr) := by
      exact add_le_add (add_le_add (add_le_add le_rfl hhighF) le_rfl) hhigh0
    _ = c * ((4 * Cmass * (2 + kappa) * Sk +
          200 * K / rho * S1) * scale q (-(3 : ℝ) / 2) +
        4 * Perr) := by
      field_simp [hrho.ne']
      ring
    _ = c * ((4 * Cmass * (2 + kappa) *
            (∑' j, claim121ComparableCellKernel B eta kappa j) +
          200 * K / rho *
            (∑' j, claim121ComparableCellKernel B eta 1 j)) *
          scale q (-(3 : ℝ) / 2) +
        4 * Pgood * (B * err)) := by
      simp only [Sk, S1, Perr]
      ring

/-- The normalized output of the four-way Claim 12.1/12.2 average. -/
noncomputable def claim121FourWayNormalizedBound
    (q : ℕ) (rho K Cmass c B eta kappa Pgood err : ℝ) : ℝ :=
  c * ((4 * Cmass * (2 + kappa) *
          (∑' j, claim121ComparableCellKernel B eta kappa j) +
        200 * K / rho *
          (∑' j, claim121ComparableCellKernel B eta 1 j)) *
        scale q (-(3 : ℝ) / 2) +
      4 * Pgood * (B * err))

/-- Source-variable form of the complete conditional four-way averaging
step.  A single robust Frobenius lower bound simultaneously makes both
fixed cell widths admissible, supplies both dyadic scale inequalities, and
normalizes the result to `q⁻³ᐟ²`. -/
theorem conditionedCountVector_weighted_claim121_four_way_le_scale
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (cvec : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (cond x : BucketCountVector D.finCoveredPartition → ℝ)
    (Good : BucketCountVector D.finCoveredPartition → Prop)
    {rhoF H K Cmass center c B eta err Pgood : ℝ}
    (hq : 0 < Fintype.card D.Covered)
    (hrhoF : 0 < rhoF) (hH : 0 < H) (hK : 0 ≤ K)
    (hCmass : 0 ≤ Cmass) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (heta : 0 < eta) (herr : 0 ≤ err) (hPgood : 0 ≤ Pgood)
    (hlarge : 2 ≤ Real.sqrt rhoF * (Fintype.card D.Covered : ℝ))
    (hFrob : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)))
    (hclaim : ConditionedClaim122Bound D G cvec O hbucket K)
    (hmass : ∀ a b : ℝ, a < b →
      4 * ((2 * H + 1) + 1) * (Fintype.card D.Covered : ℝ) ≤
        (b - a) * Real.pi →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        Cmass * (b - a) *
          scale (Fintype.card D.Covered) (-(3 : ℝ) / 2))
    (hgoodMass : countVectorMass D.finCoveredPartition Good ≤ Pgood)
    (hcondNonneg : ∀ ell, 0 ≤ cond ell)
    (hx : ∀ ell, Good ell → x ell = center -
      countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell -
      countVectorQuadraticShift D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell)
    (hcond : ∀ ell, Good ell → cond ell ≤ c *
      (B ^ 2 / (x ell ^ 2 +
          countVectorClaim121Scale D G cvec O hbucket ell ^ 2) +
        (B / (eta * countVectorClaim121Scale D G cvec O hbucket ell)) *
          Real.exp (-eta * |x ell| /
            (2 * countVectorClaim121Scale D G cvec O hbucket ell)) +
        B * err)) :
    let kappa := 4 * ((2 * H + 1) + 1) /
      (Real.pi * Real.sqrt rhoF)
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then cond ell else 0) ≤
      claim121FourWayNormalizedBound (Fintype.card D.Covered)
        rhoF K Cmass c B eta kappa Pgood err := by
  dsimp only
  let q := Fintype.card D.Covered
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose (D.finCoveredGraph G)
  let frobBase := claim121FrobeniusBase F
  let sigma0 := zeroCountClaim121Scale D G cvec O hbucket
  let sigma : BucketCountVector D.finCoveredPartition → ℝ :=
    countVectorClaim121Scale D G cvec O hbucket
  let kappa := 4 * ((2 * H + 1) + 1) /
    (Real.pi * Real.sqrt rhoF)
  let rate := Cmass * scale q (-(3 : ℝ) / 2)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    positivity
  have hfixed := sqrt_mul_le_claim121_fixedScales_of_frobenius
    D G cvec O hbucket hrhoF.le hFrob
  have hfixedF : Real.sqrt rhoF * (q : ℝ) ≤ frobBase := by
    simpa only [q, F, frobBase] using hfixed.1
  have hfixed0 : Real.sqrt rhoF * (q : ℝ) ≤ sigma0 := by
    simpa only [q, sigma0] using hfixed.2
  have hfrobOne : 1 ≤ frobBase := by linarith
  have hsigmaTwo : 2 ≤ sigma0 := by linarith
  have hfrobPos : 0 < frobBase := lt_of_lt_of_le zero_lt_one hfrobOne
  have hsigma0Pos : 0 < sigma0 := lt_of_lt_of_le (by norm_num) hsigmaTwo
  have hnorms := conditionedClaim121_norm_bounds D G cvec O hbucket
  have hnormF : ‖F‖ ≤ 16 * frobBase := by
    simpa only [F, frobBase] using hnorms.1
  have hnorm0 : ‖F‖ ≤ 8 * sigma0 := by
    simpa only [F, sigma0] using hnorms.2
  have hinterval (base : ℝ)
      (hlower : Real.sqrt rhoF * (q : ℝ) ≤ base) :
      ∀ a b : ℝ, kappa * base ≤ b - a →
        countVectorMass D.finCoveredPartition (fun ell ↦
            a ≤ countVectorLinearShift D.finCoveredPartition hbucket
                (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                  (D.conditionedCoveredCoefficient G cvec O)) ell ∧
            countVectorLinearShift D.finCoveredPartition hbucket
                (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                  (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
          rate * (b - a) := by
    intro a b hab
    have hbasePos : 0 < base :=
      lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 hrhoF) hqR) hlower
    have habPos : 0 < b - a :=
      lt_of_lt_of_le (mul_pos hkappa hbasePos) hab
    have hadmiss := countVector_interval_width_of_zeroCountScale
      hH hrhoF hlower
    have hwidth :
        4 * ((2 * H + 1) + 1) * (q : ℝ) ≤ (b - a) * Real.pi := by
      apply hadmiss.trans
      apply mul_le_mul_of_nonneg_right hab Real.pi_pos.le
    have hm := hmass a b (by linarith) (by simpa only [q] using hwidth)
    calc
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
          Cmass * (b - a) * scale q (-(3 : ℝ) / 2) := by
            simpa only [q] using hm
      _ = rate * (b - a) := by
        dsimp only [rate]
        ring
  have hgeometry (ell : BucketCountVector D.finCoveredPartition) :=
    countVectorClaim121Scale_geometry D G cvec O hbucket ell
  have hfour := countVector_weighted_claim121_four_way
    D G cvec O hbucket cond sigma x Good
    (K := K) (center := center) (rateF := rate) (rate0 := rate)
    (c := c) (B := B) (eta := eta) (err := err) (Pgood := Pgood)
    (frobBase := frobBase) (sigma0 := sigma0)
    (kappaF := kappa) (kappa0 := kappa)
    hK
    (by
      dsimp only [rate]
      exact mul_nonneg hCmass (scale_nonneg q _))
    (by
      dsimp only [rate]
      exact mul_nonneg hCmass (scale_nonneg q _))
    hc hB heta herr hPgood hfrobOne hsigmaTwo hkappa hkappa
    (by simpa only [F] using hnormF) (by simpa only [F] using hnorm0)
    hclaim (hinterval frobBase hfixedF) (hinterval sigma0 hfixed0)
    hgoodMass hcondNonneg
    (by
      intro ell hell
      simpa only [F, frobBase, sigma] using (hgeometry ell).1)
    (by
      intro ell hell
      simpa only [q, sigma0, sigma] using (hgeometry ell).2)
    hx (by intro ell hell; simpa only [sigma] using hcond ell hell)
  have hFSq : 2 * rhoF * (q : ℝ) ^ 2 ≤ frobBase ^ 2 := by
    rw [show frobBase ^ 2 = 2 * frobeniusSq F by
      dsimp only [frobBase]
      exact claim121FrobeniusBase_sq F]
    have hFrob' : rhoF * (q : ℝ) ^ 2 ≤ frobeniusSq F := by
      simpa only [q, F] using hFrob
    nlinarith
  have hsigmaSq : sigma0 ^ 2 =
      2 * frobeniusSq F + vectorSqNorm (Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) 0) := by
    dsimp only [sigma0, zeroCountClaim121Scale, F]
    rw [Real.sq_sqrt]
    unfold frobeniusSq vectorSqNorm
    positivity
  have h0Sq : 2 * (rhoF / 4) * (q : ℝ) ^ 2 ≤
      (sigma0 / 2) ^ 2 := by
    have hf0Nonneg : 0 ≤ vectorSqNorm (Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) 0) := by
      unfold vectorSqNorm
      positivity
    have hFrob' : rhoF * (q : ℝ) ^ 2 ≤ frobeniusSq F := by
      simpa only [q, F] using hFrob
    have hsigmaLower : 2 * rhoF * (q : ℝ) ^ 2 ≤ sigma0 ^ 2 := by
      rw [hsigmaSq]
      nlinarith
    nlinarith
  have hnumeric := claim121_four_branch_bound_le_scale
    (kappa := kappa) (Pgood := Pgood) (err := err)
    hq hrhoF hK hCmass hc hB heta hfrobPos hsigma0Pos hFSq h0Sq
  exact hfour.trans (by
    simpa only [q, F, frobBase, sigma0, kappa, rate,
      claim121FourWayNormalizedBound] using hnumeric)

/-- Positive-bucket-count form of the unconditional nonuniform upper half of
Claim 12.1. -/
theorem exists_eventual_productSlice_claim121_nonuniform_upper_threshold_pos
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ B : ℝ, B0 ≤ B →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {m : ℕ}, 0 < m →
          ∀ (P : BucketPartition (Fin n) (Fin m))
            (ell : Fin m → ℕ) (G : SimpleGraph (Fin n))
            (f : Fin n → ℝ)
            (hbucket : RobustRank.HasEqualBuckets P.bucket),
            IsKSSSPartition delta P → IsNearBalanced delta P ell →
            HasKSSSBalancedCoefficients delta P f
              (bucketCenteredAdjacency P.bucket hbucket.choose G) →
            RamseyFree C G →
            ∃ hleft : Nonempty (ProductSlicePoint P ell),
              letI := hleft
              let F := bucketCenteredAdjacency P.bucket hbucket.choose G
              let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
              0 < sigma ∧ ∀ x : ℝ,
                Esseen.smallBall
                    (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                      (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                  Esseen.relativeEsseenConstant *
                    (B ^ 2 / (x ^ 2 + sigma ^ 2) +
                      (B / (eta * sigma)) *
                        Real.exp (-eta * |x| / (2 * sigma)) +
                      B * scale n (-6 / 5 : ℝ)) := by
  obtain ⟨B0, hB0, eta, heta, hetaOne, hbase⟩ :=
    exists_eventual_productSlice_claim121_nonuniform_upper_threshold_unconditional
      C delta hC hdelta hdeltaSmall
  refine ⟨B0, hB0, eta, heta, hetaOne, ?_⟩
  intro B hB
  filter_upwards [hbase B hB] with n hbaseN
  intro m hm P ell G f hbucket hpart hbalanced hcoeff hRamsey
  cases m with
  | zero => omega
  | succ K =>
      exact hbaseN P ell G f hbucket hpart hbalanced hcoeff hRamsey

theorem exists_eventual_productSlice_claim121_nonuniform_upper_pos
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B : ℝ, 0 < B ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {m : ℕ}, 0 < m →
          ∀ (P : BucketPartition (Fin n) (Fin m))
            (ell : Fin m → ℕ) (G : SimpleGraph (Fin n))
            (f : Fin n → ℝ)
            (hbucket : RobustRank.HasEqualBuckets P.bucket),
            IsKSSSPartition delta P → IsNearBalanced delta P ell →
            HasKSSSBalancedCoefficients delta P f
              (bucketCenteredAdjacency P.bucket hbucket.choose G) →
            RamseyFree C G →
            ∃ hleft : Nonempty (ProductSlicePoint P ell),
              letI := hleft
              let F := bucketCenteredAdjacency P.bucket hbucket.choose G
              let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
              0 < sigma ∧ ∀ x : ℝ,
                Esseen.smallBall
                    (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                      (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                  Esseen.relativeEsseenConstant *
                    (B ^ 2 / (x ^ 2 + sigma ^ 2) +
                      (B / (eta * sigma)) *
                        Real.exp (-eta * |x| / (2 * sigma)) +
                      B * scale n (-6 / 5 : ℝ)) := by
  obtain ⟨B, hB, eta, heta, hetaOne, hbase⟩ :=
    exists_eventual_productSlice_claim121_nonuniform_upper_unconditional
      C delta hC hdelta hdeltaSmall
  refine ⟨B, hB, eta, heta, hetaOne, ?_⟩
  filter_upwards [hbase] with n hbaseN
  intro m hm P ell G f hbucket hpart hbalanced hcoeff hRamsey
  cases m with
  | zero => omega
  | succ K =>
      exact hbaseN P ell G f hbucket hpart hbalanced hcoeff hRamsey

/-- The nonuniform Claim 12.1 estimate after fixing a remainder subset. -/
def ConditionedClaim121NonuniformUpper
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (delta B eta : ℝ) : Prop :=
  ∀ ell : Fin (Fintype.card D.BlockIndex) → ℕ,
    IsNearBalanced delta D.finCoveredPartition ell →
    ∃ hleft : Nonempty (ProductSlicePoint D.finCoveredPartition ell),
      letI := hleft
      let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose (D.finCoveredGraph G)
      let f := Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O))
        (productSliceDelta D.finCoveredPartition hbucket.choose ell)
      let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
      0 < sigma ∧ ∀ x : ℝ,
        Esseen.smallBall
            (Esseen.finiteUniformLaw
              (ProductSlicePoint D.finCoveredPartition ell)
              (productSliceQuadratic D.finCoveredPartition ell
                (-trace F) f F)) B x ≤
          Esseen.relativeEsseenConstant *
            (B ^ 2 / (x ^ 2 + sigma ^ 2) +
              (B / (eta * sigma)) *
                Real.exp (-eta * |x| / (2 * sigma)) +
              B * scale (Fintype.card D.Covered) (-6 / 5 : ℝ))

/-- The contribution of the near-balanced, moderate-linear-shift count
vectors is controlled by the normalized four-way Claim 12.1 average.  The
mass of this region is obtained directly from the source interval estimate,
so the only remaining inputs are the conditioned Claim 12.1/12.2
certificates and the robust Frobenius lower bound. -/
theorem conditionedCountVector_good_window_average_le_scale
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {delta B eta rhoF H K Cmass target radius : ℝ}
    (hq : 0 < Fintype.card D.Covered)
    (hrhoF : 0 < rhoF) (hH : 0 < H) (hK : 0 ≤ K)
    (hCmass : 0 ≤ Cmass) (hB : 0 ≤ B) (heta : 0 < eta)
    (hradius : 0 ≤ radius)
    (hlarge : 2 ≤ Real.sqrt rhoF * (Fintype.card D.Covered : ℝ))
    (hFrob : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)))
    (hclaim121 : ConditionedClaim121NonuniformUpper
      D G cvec O hbucket delta B eta)
    (hclaim122 : ConditionedClaim122Bound D G cvec O hbucket K)
    (hmass : ∀ a b : ℝ, a < b →
      4 * ((2 * H + 1) + 1) * (Fintype.card D.Covered : ℝ) ≤
        (b - a) * Real.pi →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        Cmass * (b - a) *
          scale (Fintype.card D.Covered) (-(3 : ℝ) / 2))
    (hwidth :
      (4 * ((2 * H + 1) + 1) /
          (Real.pi * Real.sqrt rhoF)) *
          zeroCountClaim121Scale D G cvec O hbucket ≤ 2 * radius) :
    let q := Fintype.card D.Covered
    let kappa := 4 * ((2 * H + 1) + 1) /
      (Real.pi * Real.sqrt rhoF)
    let rate := Cmass * scale q (-(3 : ℝ) / 2)
    let Good := conditionedCountVectorGood
      D G e0 cvec O hbucket delta target radius
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then
            conditionedCountVectorWindowProbability
              D G e0 cvec O B target ell else 0) ≤
      claim121FourWayNormalizedBound q rhoF K Cmass
        Esseen.relativeEsseenConstant B eta kappa
        (2 * rate * radius) (scale q (-6 / 5 : ℝ)) := by
  dsimp only
  let q := Fintype.card D.Covered
  let sigma0 := zeroCountClaim121Scale D G cvec O hbucket
  let kappa := 4 * ((2 * H + 1) + 1) /
    (Real.pi * Real.sqrt rhoF)
  let rate := Cmass * scale q (-(3 : ℝ) / 2)
  let Good := conditionedCountVectorGood
    D G e0 cvec O hbucket delta target radius
  let cond : BucketCountVector D.finCoveredPartition → ℝ :=
    conditionedCountVectorWindowProbability D G e0 cvec O B target
  let x : BucketCountVector D.finCoveredPartition → ℝ :=
    conditionedCountVectorTargetOffset D G e0 cvec O hbucket target
  let center := conditionedCountVectorBaseCenter
    D G e0 cvec O hbucket target
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    positivity
  have hfixed := sqrt_mul_le_claim121_fixedScales_of_frobenius
    D G cvec O hbucket hrhoF.le hFrob
  have hsigmaLower : Real.sqrt rhoF * (q : ℝ) ≤ sigma0 := by
    simpa only [q, sigma0] using hfixed.2
  have hsigmaPos : 0 < sigma0 :=
    lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 hrhoF) hqR) hsigmaLower
  have hrate : 0 ≤ rate := by
    dsimp only [rate]
    exact mul_nonneg hCmass (scale_nonneg q _)
  have hinterval : ∀ a b : ℝ, kappa * sigma0 ≤ b - a →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        rate * (b - a) := by
    intro a b hab
    have habPos : 0 < b - a :=
      lt_of_lt_of_le (mul_pos hkappa hsigmaPos) hab
    have hadmiss := countVector_interval_width_of_zeroCountScale
      hH hrhoF hsigmaLower
    have hsource :
        4 * ((2 * H + 1) + 1) * (q : ℝ) ≤
          (b - a) * Real.pi := by
      apply hadmiss.trans
      apply mul_le_mul_of_nonneg_right hab Real.pi_pos.le
    have hm := hmass a b (by linarith) (by simpa only [q] using hsource)
    calc
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
          Cmass * (b - a) * scale q (-(3 : ℝ) / 2) := by
            simpa only [q] using hm
      _ = rate * (b - a) := by
        dsimp only [rate]
        ring
  have hgoodMass : countVectorMass D.finCoveredPartition Good ≤
      2 * rate * radius := by
    apply countVectorMass_subset_abs_sub_le
      D.finCoveredPartition
      (fun ell ↦ countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G cvec O)) ell)
      Good (width := kappa * sigma0)
      (center := target - GraphQuadratic.graphSliceConstant
        (D.finCoveredGraph G)
        (Probability.perturbedEdgePolynomial G e0 cvec O)
        (D.conditionedCoveredCoefficient G cvec O))
      (radius := radius) (rate := rate)
    · simpa only [kappa, sigma0] using hwidth
    · intro ell hell
      exact hell.2
    · exact hinterval
  have hmain := conditionedCountVector_weighted_claim121_four_way_le_scale
    D G cvec O hbucket cond x Good hq hrhoF hH hK hCmass
    Esseen.relativeEsseenConstant_nonneg hB heta
    (scale_nonneg q _) (by positivity) hlarge hFrob hclaim122 hmass
    hgoodMass
    (by
      intro ell
      exact conditionedCountVectorWindowProbability_nonneg
        D G e0 cvec O B target ell)
    (by
      intro ell hell
      rfl)
    (by
      intro ell hell
      exact conditionedCountVectorWindowProbability_le_of_claim121
        D G e0 cvec hO hbucket hclaim121 ell hell.1 target)
  simpa only [q, sigma0, kappa, rate, Good, cond, x, center] using hmain

/-- For a fixed remainder conditioning, the entire covered-coordinate
window probability splits into the good Claim 12.1 contribution, the mass
of non-near-balanced count vectors, and the far structured residual.  The
last term is bounded by the fixed 64th-moment Bonami estimate. -/
theorem conditionedCountVector_window_average_le_good_add_bad_tail
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {delta B target rhoF : ℝ}
    (hq : 0 < Fintype.card D.Covered) (hrhoF : 0 < rhoF)
    (hFrob : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G))) :
    let q := Fintype.card D.Covered
    let sigma0 := zeroCountClaim121Scale D G cvec O hbucket
    let radius := B + sigma0 * scale q (1 / 20 : ℝ)
    let Good := conditionedCountVectorGood
      D G e0 cvec O hbucket delta target radius
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability
            D G e0 cvec O B target ell ≤
      (∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          (if Good ell then
            conditionedCountVectorWindowProbability
              D G e0 cvec O B target ell else 0)) +
        countVectorMass D.finCoveredPartition (fun ell ↦
          ¬ IsNearBalanced delta D.finCoveredPartition
            (fun j ↦ (ell j).val)) +
        (9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
          (1 + 1 / (32 * rhoF)) ^ 32) * scale q (-16 / 5 : ℝ) := by
  dsimp only
  let q := Fintype.card D.Covered
  let P := D.finCoveredPartition
  let Gc := D.finCoveredGraph G
  let cc := D.conditionedCoveredCoefficient G cvec O
  let E := GraphQuadratic.graphSliceConstant Gc
    (Probability.perturbedEdgePolynomial G e0 cvec O) cc
  let y := GraphQuadratic.graphEffectiveLinear Gc cc
  let Q := bucketProjectionMatrix P.bucket hbucket.choose
  let F := bucketCenteredAdjacency P.bucket hbucket.choose Gc
  let sigma0 := zeroCountClaim121Scale D G cvec O hbucket
  let T := sigma0 * scale q (1 / 20 : ℝ)
  let radius := B + T
  let Good := conditionedCountVectorGood
    D G e0 cvec O hbucket delta target radius
  let Bad : BucketCountVector P → Prop := fun ell ↦
    ¬ IsNearBalanced delta P (fun j ↦ (ell j).val)
  let Window : Finset (Fin q) → Prop := fun S ↦
    |Probability.perturbedEdgePolynomial G e0 cvec
        (O ∪ D.finCoveredSubsetImage S) - target| ≤ B
  let Residual : Finset (Fin q) → Prop := fun S ↦
    T ≤ |Structured.structuredQuadratic E
        (RobustRank.graphAdjacencyMatrix Gc) y (signOfSet S) - E -
      (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q (signOfSet S))|
  have hsplit : ∀ S : Finset (Fin q), Window S →
      Good (bucketCounts P S) ∨ Bad (bucketCounts P S) ∨ Residual S := by
    intro S hWindow
    by_cases hbalanced : IsNearBalanced delta P
        (fun j ↦ (bucketCounts P S j).val)
    · by_cases hResidual : Residual S
      · exact Or.inr (Or.inr hResidual)
      · left
        refine ⟨hbalanced, ?_⟩
        have hX : Probability.perturbedEdgePolynomial G e0 cvec
              (O ∪ D.finCoveredSubsetImage S) =
            Structured.structuredQuadratic E
              (RobustRank.graphAdjacencyMatrix Gc) y (signOfSet S) := by
          calc
            Probability.perturbedEdgePolynomial G e0 cvec
                (O ∪ D.finCoveredSubsetImage S) =
                sliceQuadratic E (GraphQuadratic.graphSliceLinear Gc cc)
                  (GraphQuadratic.graphSliceMatrix Gc) S :=
              (D.sliceQuadratic_conditionedCovered_eq
                G e0 cvec hO S).symm
            _ = Structured.structuredQuadratic E
                  (RobustRank.graphAdjacencyMatrix Gc) y (signOfSet S) := by
              simpa only [sliceQuadratic, E, y, Gc, cc] using
                GraphQuadratic.sliceQuadratic_graph_eq_structuredQuadratic
                  Gc (Probability.perturbedEdgePolynomial G e0 cvec O)
                    cc (signOfSet S)
        have hL : countVectorLinearShift P hbucket y
              (bucketCounts P S) =
            (1 / 2 : ℝ) * (y ⬝ᵥ Structured.delta Q (signOfSet S)) := by
          rw [countVectorLinearShift,
            ← delta_signOfSet_eq_productSliceDelta_bucketCounts]
        have hResidualLt :
            |Structured.structuredQuadratic E
                (RobustRank.graphAdjacencyMatrix Gc) y (signOfSet S) - E -
              (1 / 2 : ℝ) *
                (y ⬝ᵥ Structured.delta Q (signOfSet S))| < T :=
          lt_of_not_ge hResidual
        have htriangle := abs_sub
          (Probability.perturbedEdgePolynomial G e0 cvec
            (O ∪ D.finCoveredSubsetImage S) - target)
          (Probability.perturbedEdgePolynomial G e0 cvec
            (O ∪ D.finCoveredSubsetImage S) - E -
              countVectorLinearShift P hbucket y (bucketCounts P S))
        have hResidualAmbient :
            |Probability.perturbedEdgePolynomial G e0 cvec
                (O ∪ D.finCoveredSubsetImage S) - E -
              countVectorLinearShift P hbucket y (bucketCounts P S)| ≤ T := by
          rw [hX, hL]
          exact hResidualLt.le
        have hmoderate :=
          htriangle.trans (add_le_add hWindow hResidualAmbient)
        dsimp only [Good, conditionedCountVectorGood, radius]
        change |countVectorLinearShift P hbucket y (bucketCounts P S) -
            (target - E)| ≤ B + T
        rw [show countVectorLinearShift P hbucket y (bucketCounts P S) -
              (target - E) =
            (Probability.perturbedEdgePolynomial G e0 cvec
                (O ∪ D.finCoveredSubsetImage S) - target) -
              (Probability.perturbedEdgePolynomial G e0 cvec
                (O ∪ D.finCoveredSubsetImage S) - E -
                countVectorLinearShift P hbucket y (bucketCounts P S)) by
          ring]
        exact hmoderate
    · exact Or.inr (Or.inl hbalanced)
  have hmix := countVector_weighted_event_le_good_add_bad_add_residual
    P Window Residual Good Bad hsplit
  have hQ : Structured.IsOrthogonalProjection Q := by
    dsimp only [Q, P]
    exact bucketProjectionMatrix_isOrthogonalProjection
      D.finCoveredPartition.bucket hbucket
  have htail := uniformProbability_graphStructuredResidual_polynomial_tail_le
    hq hrhoF Q F Gc hQ E y (by simpa only [q, F, P, Gc] using hFrob)
  dsimp only at htail
  have htail' : Concentration.uniformProbability Residual ≤
      (9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
        (1 + 1 / (32 * rhoF)) ^ 32) * scale q (-16 / 5 : ℝ) := by
    simpa only [Residual, T, sigma0, zeroCountClaim121Scale,
      q, Q, P, Gc, F, y] using htail
  have hcombined := hmix.trans (add_le_add le_rfl htail')
  simpa only [q, P, Gc, cc, E, y, Q, F, sigma0, T, radius,
    Good, Bad, Window, Residual,
    conditionedCountVectorWindowProbability] using hcombined

/-- Complete fixed-remainder structured upper bound.  It combines the
normalized four-way Claim 12.1 average with the count-vector and residual
exceptional events, leaving only their explicit probabilities for the
eventual asymptotic bookkeeping. -/
theorem conditionedCountVector_window_average_le_scale_add_bad_tail
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {delta B eta rhoF H K Cmass target : ℝ}
    (hq : 0 < Fintype.card D.Covered)
    (hrhoF : 0 < rhoF) (hH : 0 < H) (hK : 0 ≤ K)
    (hCmass : 0 ≤ Cmass) (hB : 0 ≤ B) (heta : 0 < eta)
    (hlarge : 2 ≤ Real.sqrt rhoF * (Fintype.card D.Covered : ℝ))
    (hFrob : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)))
    (hclaim121 : ConditionedClaim121NonuniformUpper
      D G cvec O hbucket delta B eta)
    (hclaim122 : ConditionedClaim122Bound D G cvec O hbucket K)
    (hmass : ∀ a b : ℝ, a < b →
      4 * ((2 * H + 1) + 1) * (Fintype.card D.Covered : ℝ) ≤
        (b - a) * Real.pi →
      countVectorMass D.finCoveredPartition (fun ell ↦
          a ≤ countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ∧
          countVectorLinearShift D.finCoveredPartition hbucket
              (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
                (D.conditionedCoveredCoefficient G cvec O)) ell ≤ b) ≤
        Cmass * (b - a) *
          scale (Fintype.card D.Covered) (-(3 : ℝ) / 2))
    (hwidth :
      (4 * ((2 * H + 1) + 1) /
          (Real.pi * Real.sqrt rhoF)) *
          zeroCountClaim121Scale D G cvec O hbucket ≤
        2 * (B + zeroCountClaim121Scale D G cvec O hbucket *
          scale (Fintype.card D.Covered) (1 / 20 : ℝ))) :
    let q := Fintype.card D.Covered
    let sigma0 := zeroCountClaim121Scale D G cvec O hbucket
    let radius := B + sigma0 * scale q (1 / 20 : ℝ)
    let kappa := 4 * ((2 * H + 1) + 1) /
      (Real.pi * Real.sqrt rhoF)
    let rate := Cmass * scale q (-(3 : ℝ) / 2)
    ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability
            D G e0 cvec O B target ell ≤
      claim121FourWayNormalizedBound q rhoF K Cmass
          Esseen.relativeEsseenConstant B eta kappa
          (2 * rate * radius) (scale q (-6 / 5 : ℝ)) +
        countVectorMass D.finCoveredPartition (fun ell ↦
          ¬ IsNearBalanced delta D.finCoveredPartition
            (fun j ↦ (ell j).val)) +
        (9 ^ RademacherHypercontractivity.CubePoly.bonamiExponent 2 5 *
          (1 + 1 / (32 * rhoF)) ^ 32) * scale q (-16 / 5 : ℝ) := by
  dsimp only
  let q := Fintype.card D.Covered
  let sigma0 := zeroCountClaim121Scale D G cvec O hbucket
  let radius := B + sigma0 * scale q (1 / 20 : ℝ)
  let kappa := 4 * ((2 * H + 1) + 1) /
    (Real.pi * Real.sqrt rhoF)
  let rate := Cmass * scale q (-(3 : ℝ) / 2)
  let Good := conditionedCountVectorGood
    D G e0 cvec O hbucket delta target radius
  have hradius : 0 ≤ radius := by
    dsimp only [radius]
    exact add_nonneg hB
      (mul_nonneg (Real.sqrt_nonneg _) (scale_nonneg q _))
  have hgood := conditionedCountVector_good_window_average_le_scale
    D G e0 cvec hO hbucket hq hrhoF hH hK hCmass hB heta hradius
    hlarge hFrob hclaim121 hclaim122 hmass
    (target := target)
    (by simpa only [q, sigma0, radius, kappa] using hwidth)
  have hsplit := conditionedCountVector_window_average_le_good_add_bad_tail
    D G e0 cvec hO hbucket hq hrhoF hFrob
    (delta := delta) (B := B) (target := target)
  have hcombined := hsplit.trans
    (add_le_add (add_le_add hgood le_rfl) le_rfl)
  simpa only [q, sigma0, radius, kappa, rate, Good] using hcombined

/-- Claims 12.1 and 12.2 on one and the same structured decomposition.
The Claim 12.1 conclusion is required only for remainder conditionings with
the simultaneous degree control supplied by `StructuredTypical`; Claim 12.2
holds for every actual remainder subset. -/
theorem exists_eventual_graphEffective_smallRLCD_common_claims_threshold
    (C gamma : ℝ) (hC : 0 < C)
    (hgamma : 0 < gamma) (hgammaSmall : gamma < 3 / 800) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ H L : ℝ, 0 < H → 1 ≤ L →
      ∃ Adens : ℝ, 0 < Adens ∧ ∃ rhoF : ℝ, 0 < rhoF ∧
      ∃ Dshift : ℝ, 0 < Dshift ∧
        ∀ B : ℝ, B0 ≤ B →
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ (G : SimpleGraph (Fin n)) (c : Fin n → ℝ),
            RamseyFree C G →
            (∀ i, 0 ≤ c i ∧ c i ≤ H * (n : ℝ)) →
            RLCD.regularizedLCD L gamma
                (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n →
            ∃ D : RLCD.BucketDecomposition
                (GraphQuadratic.graphEffectiveLinear G c)
                (RLCD.smallRLCDBucketCard n gamma)
                ((n : ℝ) ^ ((1 : ℝ) / 2 + 4 * gamma)),
              (D.remainder.card : ℝ) ≤ scale n (1 - gamma) ∧
              IsKSSSPartition (2 * gamma) D.finCoveredPartition ∧
              ∃ hbucket : RobustRank.HasEqualBuckets
                  D.finCoveredPartition.bucket,
                RamseyFree (2 * C) (D.finCoveredGraph G) ∧
                rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
                  frobeniusSq (bucketCenteredAdjacency
                    D.finCoveredPartition.bucket hbucket.choose
                    (D.finCoveredGraph G)) ∧
                ∀ (O : Finset (Fin n)), O ⊆ D.remainder →
                  (∀ i, 0 ≤ D.conditionedCoveredCoefficient G c O i ∧
                    D.conditionedCoveredCoefficient G c O i ≤
                      (2 * H + 1) * (Fintype.card D.Covered : ℝ)) ∧
                  ConditionedClaim122Bound D G c O hbucket Dshift ∧
                  ((∀ i : Fin (Fintype.card D.Covered),
                      |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1 O : ℝ) -
                        (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
                          D.remainder : ℝ) / 2| ≤ Real.sqrt n) →
                    ConditionedClaim121NonuniformUpper D G c O hbucket
                      (2 * gamma) B eta) ∧
                  ∀ a b : ℝ, a < b →
                    4 * ((2 * H + 1) + 1) *
                        (Fintype.card D.Covered : ℝ) ≤
                      (b - a) * Real.pi →
                    countVectorMass D.finCoveredPartition (fun ell ↦
                        a ≤ countVectorLinearShift D.finCoveredPartition
                              hbucket
                              (GraphQuadratic.graphEffectiveLinear
                                (D.finCoveredGraph G)
                                (D.conditionedCoveredCoefficient G c O)) ell ∧
                          countVectorLinearShift D.finCoveredPartition
                              hbucket
                              (GraphQuadratic.graphEffectiveLinear
                                (D.finCoveredGraph G)
                                (D.conditionedCoveredCoefficient G c O)) ell ≤ b) ≤
                      (2 * Real.pi * Real.sqrt Real.pi / Adens) * (b - a) *
                        scale (Fintype.card D.Covered) (-(3 : ℝ) / 2) := by
  have hgamma4 : gamma < 1 / 4 := hgammaSmall.trans (by norm_num)
  obtain ⟨B0, hB0, eta, heta, hetaOne, h121Threshold⟩ :=
    exists_eventual_productSlice_claim121_nonuniform_upper_threshold_pos
      (2 * C) (2 * gamma) (mul_pos (by norm_num) hC)
      (mul_pos (by norm_num) hgamma) (by linarith)
  refine ⟨B0, hB0, eta, heta, hetaOne, ?_⟩
  intro H L hH hL
  obtain ⟨Dshift, hDshift, h122Event⟩ :=
    exists_eventual_bucketShiftMoment_graph_claim122
      (2 * C) (2 * H + 1) (2 * gamma)
      (mul_pos (by norm_num) hC) (by linarith)
      (mul_pos (by norm_num) hgamma) (by linarith)
  obtain ⟨Adens, hAdens, NAdens, hDensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower
      (2 * C) (mul_pos (by norm_num) hC)
  obtain ⟨rhoF, hrhoF, Nrob, hRob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      (2 * C) (2 * gamma) 0 (mul_pos (by norm_num) hC)
      (mul_pos (by norm_num) hgamma) (by linarith)
  obtain ⟨N122, h122⟩ := Filter.eventually_atTop.1 h122Event
  have hstruct :=
    LinearLCDCancellation.eventually_graphEffective_smallRLCD_structuredData
      C H gamma L hC hH hgamma hgamma4 hL
  have htypical :=
    eventually_conditionedCovered_hasKSSSBalancedCoefficients gamma hgamma
  have hgrowth := eventually_const_le_scale 2 gamma hgamma
  refine ⟨Adens, hAdens, rhoF, hrhoF, Dshift, hDshift, ?_⟩
  intro B hB0B
  obtain ⟨N121, h121⟩ :=
    Filter.eventually_atTop.1 (h121Threshold B hB0B)
  filter_upwards [hstruct, htypical, hgrowth,
      Filter.eventually_ge_atTop
        (max 4 (2 * max Nrob (max NAdens (max N121 N122))))] with
      n hstructN htypicalN hgrowthN hn
  intro G c hRamsey hc hsmall
  obtain ⟨D, hrem, hpart, hbucket, hcoveredRamsey⟩ :=
    hstructN G c hRamsey hc hsmall
  have hnpos : 0 < n := by omega
  have hscaleHalf : scale n (1 - gamma) ≤ (n : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      scale n (1 - gamma) * 2 ≤
          scale n (1 - gamma) * scale n gamma :=
        mul_le_mul_of_nonneg_left hgrowthN (scale_nonneg n _)
      _ = scale n ((1 - gamma) + gamma) := scale_mul hnpos _ _
      _ = (n : ℝ) := by
        rw [show (1 - gamma) + gamma = (1 : ℝ) by ring]
        exact Real.rpow_one _
  have hremHalf : (D.remainder.card : ℝ) ≤ (n : ℝ) / 2 :=
    hrem.trans hscaleHalf
  have hcardNat : D.remainder.card + Fintype.card D.Covered = n := by
    simpa only [Fintype.card_fin] using D.remainder_card_add_card_covered
  have hcard : (D.remainder.card : ℝ) +
      (Fintype.card D.Covered : ℝ) = (n : ℝ) := by
    exact_mod_cast hcardNat
  have hqHalf : (n : ℝ) / 2 ≤ (Fintype.card D.Covered : ℝ) := by
    linarith
  have hqpos : 0 < Fintype.card D.Covered := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    exact_mod_cast (lt_of_lt_of_le (half_pos hnR) hqHalf)
  have hmpos : 0 < Fintype.card D.BlockIndex := by
    rw [D.card_covered] at hqpos
    have hblocks : 0 < D.blocks.card := Nat.pos_of_mul_pos_right hqpos
    simpa only [D.card_blockIndex] using hblocks
  have hN121 : N121 ≤ Fintype.card D.Covered := by
    have hthreshold : 2 * N121 ≤ n := by
      have hNall : N121 ≤ max NAdens (max N121 N122) :=
        (le_max_left N121 N122).trans (le_max_right NAdens _)
      have hNall' : N121 ≤ max Nrob (max NAdens (max N121 N122)) :=
        hNall.trans (le_max_right Nrob _)
      exact (Nat.mul_le_mul_left 2 hNall').trans
        ((le_max_right 4 (2 * max Nrob (max NAdens (max N121 N122)))).trans hn)
    have hthresholdR : (N121 : ℝ) ≤ (n : ℝ) / 2 := by
      have hthresholdR' : ((2 * N121 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hthreshold
      push_cast at hthresholdR'
      linarith
    exact_mod_cast hthresholdR.trans hqHalf
  have hN122 : N122 ≤ Fintype.card D.Covered := by
    have hthreshold : 2 * N122 ≤ n := by
      have hNall : N122 ≤ max NAdens (max N121 N122) :=
        (le_max_right N121 N122).trans (le_max_right NAdens _)
      have hNall' : N122 ≤ max Nrob (max NAdens (max N121 N122)) :=
        hNall.trans (le_max_right Nrob _)
      exact (Nat.mul_le_mul_left 2 hNall').trans
        ((le_max_right 4 (2 * max Nrob (max NAdens (max N121 N122)))).trans hn)
    have hthresholdR : (N122 : ℝ) ≤ (n : ℝ) / 2 := by
      have hthresholdR' : ((2 * N122 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hthreshold
      push_cast at hthresholdR'
      linarith
    exact_mod_cast hthresholdR.trans hqHalf
  have hNAdens : NAdens ≤ Fintype.card D.Covered := by
    have hthreshold : 2 * NAdens ≤ n := by
      have hNall : NAdens ≤ max Nrob (max NAdens (max N121 N122)) :=
        (le_max_left NAdens (max N121 N122)).trans (le_max_right Nrob _)
      exact (Nat.mul_le_mul_left 2 hNall).trans
        ((le_max_right 4 (2 * max Nrob (max NAdens (max N121 N122)))).trans hn)
    have hthresholdR : (NAdens : ℝ) ≤ (n : ℝ) / 2 := by
      have hthresholdR' : ((2 * NAdens : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hthreshold
      push_cast at hthresholdR'
      linarith
    exact_mod_cast hthresholdR.trans hqHalf
  have hNrob : Nrob ≤ Fintype.card D.Covered := by
    have hthreshold : 2 * Nrob ≤ n := by
      exact (Nat.mul_le_mul_left 2 (le_max_left Nrob _)).trans
        ((le_max_right 4
          (2 * max Nrob (max NAdens (max N121 N122)))).trans hn)
    have hthresholdR : (Nrob : ℝ) ≤ (n : ℝ) / 2 := by
      have hthresholdR' : ((2 * Nrob : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hthreshold
      push_cast at hthresholdR'
      linarith
    exact_mod_cast hthresholdR.trans hqHalf
  have hrobF := hRob (Fintype.card D.Covered) hNrob
    (Fintype.card D.BlockIndex) D.finCoveredPartition.bucket
    (D.finCoveredGraph G) hmpos hpart.2.1 hpart.2.2 hbucket hcoveredRamsey
  have hFrob : rhoF * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      frobeniusSq (bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)) := by
    have hzero := hrobF (0 : Matrix (Fin (Fintype.card D.Covered))
      (Fin (Fintype.card D.Covered)) ℝ) (by simp)
    simpa only [sub_zero, frobenius_norm_sq_eq_frobeniusSq] using hzero
  refine ⟨D, hrem, hpart, hbucket, hcoveredRamsey, hFrob, ?_⟩
  intro O hO
  have hcoeffBounds := conditionedCoveredCoefficient_bounds D G c O hH.le
    (fun i ↦ (hc i).1) (fun i ↦ (hc i).2) hO hremHalf
  have h122D := h122 (Fintype.card D.Covered) hN122
    D.finCoveredPartition hbucket (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G c O) hmpos hpart.2.1 hpart.2.2
    hcoveredRamsey hcoeffBounds
  refine ⟨hcoeffBounds, ?_, ?_, ?_⟩
  · intro a b hab
    exact h122D a b hab
  · intro hdegree ell hbalanced
    have hcoeff := htypicalN G c D hremHalf hpart hbucket ell hbalanced O hdegree
    exact h121 (Fintype.card D.Covered) hN121 hmpos
      D.finCoveredPartition ell (D.finCoveredGraph G)
      (Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O))
        (productSliceDelta D.finCoveredPartition hbucket.choose ell))
      hbucket hpart hbalanced hcoeff hcoveredRamsey
  · intro a b hab hwidth
    have hedge := hDensity (Fintype.card D.Covered) hNAdens
      (D.finCoveredGraph G) hcoveredRamsey
    exact conditionedCountVectorMass_linearShift_Icc_le_scale
      D G c O hbucket (2 * H + 1) Adens hqpos (by linarith) hAdens
        hcoeffBounds hedge hab hwidth

end Erdos88.GaussianQuadratic

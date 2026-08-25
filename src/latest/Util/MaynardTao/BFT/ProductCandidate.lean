import Util.MaynardTao.BFT.ProductParameters
import ErdosProblems.Erdos6.LargeKCandidate
import BoundedGaps.Maynard.FaceDecomposition
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Measurability

/-!
# Parameterized product test functions for the Maynard sieve

This generalizes the product-density argument in
`ErdosProblems.Erdos6.LargeKCandidate` from its fixed dimension to the
elementary parameter family in `ProductParameters`.
-/

namespace MaynardBFT.Sieve

open MeasureTheory Set
open scoped BigOperators
open scoped Interval

noncomputable section

variable [P : Parameters]

/-- The number of shifts. -/
def largeK : ℕ := P.k

/-- The decay parameter in the one-dimensional product weight. -/
def largeA : ℝ := P.a

/-- The one-dimensional factor `u ↦ (1 + A u)⁻¹`. -/
def largeG (u : ℝ) : ℝ := (1 + largeA * u)⁻¹

/-- The product factor before truncation to Maynard's simplex. -/
def largeProduct (t : Fin largeK → ℝ) : ℝ :=
  ∏ i, largeG (largeK * t i)

/-- The product factor, extended by zero off Maynard's simplex. -/
noncomputable def largeCandidate (t : Fin largeK → ℝ) : ℝ := by
  classical
  exact if t ∈ BoundedGaps.Maynard.maynardSimplex largeK then
    largeProduct t else 0

theorem largeA_ge_1024 : 1024 ≤ largeA := P.large_a

theorem largeK_pos : 0 < largeK := by
  have h : 2 ≤ largeK := P.two_le_k
  omega

theorem largeK_ne_zero : largeK ≠ 0 := largeK_pos.ne'

theorem largeA_pos : 0 < largeA := by
  have h := largeA_ge_1024
  linarith

theorem largeG_pos {u : ℝ} (hu : 0 ≤ u) : 0 < largeG u := by
  unfold largeG
  apply inv_pos.mpr
  have hA := largeA_pos
  nlinarith

theorem largeG_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ largeG u :=
  (largeG_pos hu).le

theorem largeG_le_one {u : ℝ} (hu : 0 ≤ u) : largeG u ≤ 1 := by
  rw [largeG, inv_le_one₀]
  all_goals
    have hA := largeA_pos
    nlinarith

theorem measurable_largeG : Measurable largeG := by
  unfold largeG
  fun_prop

theorem measurable_largeProduct : Measurable largeProduct := by
  unfold largeProduct
  exact Finset.measurable_prod _ fun i _ =>
    measurable_largeG.comp (measurable_const.mul (measurable_pi_apply i))

theorem measurable_largeCandidate : Measurable largeCandidate := by
  classical
  unfold largeCandidate
  exact Measurable.ite
    (BoundedGaps.Maynard.maynardSimplex_measurable (k := largeK))
    measurable_largeProduct measurable_const

theorem largeCandidate_simplexSupported :
    BoundedGaps.Maynard.MaynardSimplexSupported largeK largeCandidate := by
  classical
  intro t ht
  simp [largeCandidate, ht]

theorem largeProduct_nonneg_of_mem_cube
    {t : Fin largeK → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCube largeK) :
    0 ≤ largeProduct t := by
  unfold largeProduct
  exact Finset.prod_nonneg fun i hi =>
    largeG_nonneg (mul_nonneg (by positivity)
      (ht i (Set.mem_univ i)).1)

theorem largeProduct_le_one_of_mem_cube
    {t : Fin largeK → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCube largeK) :
    largeProduct t ≤ 1 := by
  unfold largeProduct
  calc
    ∏ i : Fin largeK, largeG (largeK * t i) ≤
        ∏ _i : Fin largeK, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact largeG_nonneg (mul_nonneg (by positivity)
          (ht i (Set.mem_univ i)).1)
      · intro i hi
        exact largeG_le_one (mul_nonneg (by positivity)
          (ht i (Set.mem_univ i)).1)
    _ = 1 := Finset.prod_const_one

theorem largeCandidate_nonneg_of_mem_cube
    {t : Fin largeK → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCube largeK) :
    0 ≤ largeCandidate t := by
  classical
  unfold largeCandidate
  split_ifs
  · exact largeProduct_nonneg_of_mem_cube ht
  · exact le_rfl

theorem largeCandidate_le_one_of_mem_cube
    {t : Fin largeK → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCube largeK) :
    largeCandidate t ≤ 1 := by
  classical
  unfold largeCandidate
  split_ifs
  · exact largeProduct_le_one_of_mem_cube ht
  · norm_num

theorem largeCandidate_nonneg (t : Fin largeK → ℝ) :
    0 ≤ largeCandidate t := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex largeK
  · rw [largeCandidate, if_pos ht]
    exact largeProduct_nonneg_of_mem_cube ht.1
  · simp [largeCandidate, ht]

theorem largeCandidate_le_one (t : Fin largeK → ℝ) :
    largeCandidate t ≤ 1 := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex largeK
  · rw [largeCandidate, if_pos ht]
    exact largeProduct_le_one_of_mem_cube ht.1
  · simp [largeCandidate, ht]

theorem largeCandidate_norm_le_one (t : Fin largeK → ℝ) :
    ‖largeCandidate t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (largeCandidate_nonneg t)]
  exact largeCandidate_le_one t

theorem largeCandidate_sq_integrableOn :
    IntegrableOn (fun t : Fin largeK → ℝ => largeCandidate t ^ 2)
      (BoundedGaps.Maynard.maynardCube largeK) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCube largeK)
    (hs := BoundedGaps.Maynard.maynardCube_measurable largeK)
    (hsfinite := BoundedGaps.Maynard.maynardCube_measure_lt_top largeK)
    (f := fun t : Fin largeK → ℝ => largeCandidate t ^ 2)
    (measurable_largeCandidate.pow_const 2) 1 ?_
  intro t ht
  rw [norm_pow]
  simpa using pow_le_one₀ (n := 2) (norm_nonneg (largeCandidate t))
    (largeCandidate_norm_le_one t)

theorem measurable_insertCoordinate_left
    (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ) :
    Measurable (fun x : ℝ =>
      BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i = m
  · simp only [BoundedGaps.Maynard.maynardInsertCoordinate, dif_pos hi]
    exact measurable_id
  · simp [BoundedGaps.Maynard.maynardInsertCoordinate, hi]

theorem largeCandidate_face_integrableOn (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ) :
    IntegrableOn (fun x : ℝ => largeCandidate
      (BoundedGaps.Maynard.maynardInsertCoordinate m x t))
      (Set.Icc 0 1) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top)
    (f := fun x : ℝ => largeCandidate
      (BoundedGaps.Maynard.maynardInsertCoordinate m x t))
    (measurable_largeCandidate.comp (measurable_insertCoordinate_left m t)) 1 ?_
  intro x hx
  exact largeCandidate_norm_le_one _

def largeFaceJoint (m : Fin largeK) :
    ((BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ) × ℝ) → ℝ :=
  fun z => if z.2 ∈ Set.Icc (0 : ℝ) 1 then
    largeCandidate
      (BoundedGaps.Maynard.maynardInsertCoordinate m z.2 z.1) else 0

theorem largeFaceJoint_measurable (m : Fin largeK) :
    Measurable (largeFaceJoint m) := by
  have hinsert : Measurable
      (fun z : (BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ) × ℝ =>
        BoundedGaps.Maynard.maynardInsertCoordinate m z.2 z.1) := by
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i = m
    · simp only [BoundedGaps.Maynard.maynardInsertCoordinate, dif_pos hi]
      exact measurable_snd
    · let j : BoundedGaps.Maynard.maynardFaceIndex largeK m := ⟨i, hi⟩
      simpa [BoundedGaps.Maynard.maynardInsertCoordinate, hi, j,
        Function.comp_def] using
        ((measurable_pi_apply j).comp measurable_fst)
  unfold largeFaceJoint
  apply Measurable.ite (measurableSet_Icc.preimage measurable_snd)
  · exact measurable_largeCandidate.comp hinsert
  · exact measurable_const

theorem largeFaceInner_measurable (m : Fin largeK) :
    Measurable (fun t :
      BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ =>
      ∫ x in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) := by
  have hsm : StronglyMeasurable (fun t :
      BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ =>
      ∫ x : ℝ, largeFaceJoint m (t, x)) :=
    (largeFaceJoint_measurable m).stronglyMeasurable.integral_prod_right'
  have hm : Measurable (fun t :
      BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ =>
      ∫ x, largeFaceJoint m (t, x)) := hsm.measurable
  convert hm using 1
  funext t
  simp only [largeFaceJoint]
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [Set.indicator, hx]

theorem largeFaceInner_norm_le_one (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ) :
    ‖∫ x in Set.Icc (0 : ℝ) 1,
      largeCandidate
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)‖ ≤ 1 := by
  calc
    ‖∫ x in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)‖ ≤
      1 * volume.real (Set.Icc (0 : ℝ) 1) :=
        norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
          (fun x _ => largeCandidate_norm_le_one _)
    _ = 1 := by rw [Real.volume_real_Icc_of_le] <;> norm_num

theorem largeCandidate_face_integrand_integrableOn (m : Fin largeK) :
    IntegrableOn
      (fun t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ =>
        (∫ x in Set.Icc (0 : ℝ) 1,
          largeCandidate
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
      (BoundedGaps.Maynard.maynardCubeOf
        (BoundedGaps.Maynard.maynardFaceIndex largeK m)) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf
      (BoundedGaps.Maynard.maynardFaceIndex largeK m))
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top _)
    (f := fun t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ =>
      (∫ x in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
    ((largeFaceInner_measurable m).pow_const 2) 1 ?_
  intro t ht
  rw [norm_pow]
  simpa using pow_le_one₀ (n := 2) (norm_nonneg
    (∫ x in Set.Icc (0 : ℝ) 1,
      largeCandidate
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)))
    (largeFaceInner_norm_le_one m t)

theorem largeCandidate_admissible :
    BoundedGaps.Maynard.MaynardAdmissible largeK largeCandidate := by
  exact ⟨largeCandidate_simplexSupported, largeCandidate_sq_integrableOn,
    largeCandidate_face_integrableOn,
    largeCandidate_face_integrand_integrableOn⟩

/-! ## One-dimensional integral identities -/

/-- Antiderivative used for the square of an inverse affine function. -/
noncomputable def inverseAffineSquareAntiderivative (A K x : ℝ) : ℝ :=
  -(A * K)⁻¹ * (1 + A * K * x)⁻¹

theorem hasDerivAt_inverseAffineSquareAntiderivative
    {A K x : ℝ} (hA : 0 < A) (hK : 0 < K) (hx : 0 ≤ x) :
    HasDerivAt (inverseAffineSquareAntiderivative A K)
      ((1 + A * K * x)⁻¹ ^ 2) x := by
  have hden : 1 + A * K * x ≠ 0 := by positivity
  have hAK : A * K ≠ 0 := mul_ne_zero hA.ne' hK.ne'
  unfold inverseAffineSquareAntiderivative
  have haffine : HasDerivAt (fun y : ℝ => 1 + A * K * y) (A * K) x := by
    simpa only [id_eq, mul_one, mul_assoc] using
      ((hasDerivAt_id x).const_mul (A * K)).const_add 1
  have hinv := haffine.inv hden
  have hmul := hinv.const_mul (-(A * K)⁻¹)
  have hmul' : HasDerivAt
      (fun y : ℝ => -(A * K)⁻¹ * (1 + A * K * y)⁻¹)
      (-(A * K)⁻¹ * (-(A * K) / (1 + A * K * x) ^ 2)) x := by
    simpa only [Pi.inv_apply] using hmul
  have heq : -(A * K)⁻¹ * (-(A * K) / (1 + A * K * x) ^ 2) =
      (1 + A * K * x)⁻¹ ^ 2 := by
    field_simp [hAK, hden]
  rw [heq] at hmul'
  exact hmul'

theorem integral_inverseAffine_sq {A K : ℝ} (hA : 0 < A) (hK : 0 < K) :
    (∫ x : ℝ in (0 : ℝ)..1, (1 + A * K * x)⁻¹ ^ 2) =
      (1 + A * K)⁻¹ := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_inverseAffineSquareAntiderivative hA hK
      (by simpa using hx.1))]
  · unfold inverseAffineSquareAntiderivative
    have hAK : A * K ≠ 0 := mul_ne_zero hA.ne' hK.ne'
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    have hden : ∀ x ∈ [[(0 : ℝ), 1]], 1 + A * K * x ≠ 0 := by
      intro x hx
      have hx0 : 0 ≤ x := by simpa using hx.1
      positivity
    exact (((continuousOn_const.add
      (continuousOn_const.mul continuousOn_id)).inv₀ hden).pow 2)

theorem integral_largeG_sq_interval :
    (∫ x : ℝ in (0 : ℝ)..1, largeG ((largeK : ℝ) * x) ^ 2) =
      (1 + largeA * (largeK : ℝ))⁻¹ := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  simpa only [largeG, mul_assoc] using
    (integral_inverseAffine_sq largeA_pos hK)

theorem setIntegral_largeG_sq_Icc :
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      largeG ((largeK : ℝ) * x) ^ 2) =
      (1 + largeA * (largeK : ℝ))⁻¹ := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_largeG_sq_interval

/-- Antiderivative of an inverse affine function. -/
noncomputable def inverseAffineAntiderivative (A K x : ℝ) : ℝ :=
  (A * K)⁻¹ * Real.log (1 + A * K * x)

theorem hasDerivAt_inverseAffineAntiderivative
    {A K x : ℝ} (hA : 0 < A) (hK : 0 < K) (hx : 0 ≤ x) :
    HasDerivAt (inverseAffineAntiderivative A K)
      (1 + A * K * x)⁻¹ x := by
  have hden : 1 + A * K * x ≠ 0 := by positivity
  have hAK : A * K ≠ 0 := mul_ne_zero hA.ne' hK.ne'
  unfold inverseAffineAntiderivative
  have haffine : HasDerivAt (fun y : ℝ => 1 + A * K * y) (A * K) x := by
    simpa only [id_eq, mul_one, mul_assoc] using
      ((hasDerivAt_id x).const_mul (A * K)).const_add 1
  have hlog := (Real.hasDerivAt_log hden).comp x haffine
  have hmul := hlog.const_mul (A * K)⁻¹
  have hmul' : HasDerivAt
      (fun y : ℝ => (A * K)⁻¹ * Real.log (1 + A * K * y))
      ((A * K)⁻¹ * ((1 + A * K * x)⁻¹ * (A * K))) x := by
    simpa only [Function.comp_apply] using hmul
  have heq : (A * K)⁻¹ * ((1 + A * K * x)⁻¹ * (A * K)) =
      (1 + A * K * x)⁻¹ := by
    field_simp [hAK]
  rw [heq] at hmul'
  exact hmul'

theorem integral_inverseAffine {A K B : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hB : 0 ≤ B) :
    (∫ x : ℝ in (0 : ℝ)..B, (1 + A * K * x)⁻¹) =
      Real.log (1 + A * K * B) / (A * K) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_inverseAffineAntiderivative hA hK
      (by
        rcases Set.mem_uIcc.mp hx with hx | hx
        · exact hx.1
        · exact hB.trans hx.1))]
  · unfold inverseAffineAntiderivative
    simp [div_eq_mul_inv]
    ring
  · apply ContinuousOn.intervalIntegrable
    have hden : ∀ x ∈ [[(0 : ℝ), B]], 1 + A * K * x ≠ 0 := by
      intro x hx
      have hx0 : 0 ≤ x := by
        rcases Set.mem_uIcc.mp hx with hx | hx
        · exact hx.1
        · exact hB.trans hx.1
      positivity
    exact ((continuousOn_const.add
      (continuousOn_const.mul continuousOn_id)).inv₀ hden)

theorem integral_largeG_interval {B : ℝ} (hB : 0 ≤ B) :
    (∫ x : ℝ in (0 : ℝ)..B, largeG ((largeK : ℝ) * x)) =
      Real.log (1 + largeA * (largeK : ℝ) * B) /
        (largeA * (largeK : ℝ)) := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  simpa only [largeG, mul_assoc] using
    (integral_inverseAffine largeA_pos hK hB)

theorem setIntegral_largeG_Icc {B : ℝ} (hB : 0 ≤ B) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) B,
      largeG ((largeK : ℝ) * x)) =
      Real.log (1 + largeA * (largeK : ℝ) * B) /
        (largeA * (largeK : ℝ)) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hB]
  exact integral_largeG_interval hB

/-! ## Product-measure identities -/

def largeSquareDensity (x : ℝ) : ℝ :=
  largeG ((largeK : ℝ) * x) ^ 2

def largeBaseMass : ℝ :=
  (1 + largeA * (largeK : ℝ))⁻¹

theorem largeBaseMass_pos : 0 < largeBaseMass := by
  unfold largeBaseMass
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (mul_pos largeA_pos hK).le

theorem integral_largeSquareDensity_Icc :
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1, largeSquareDensity x) =
      largeBaseMass := by
  exact setIntegral_largeG_sq_Icc

theorem measurable_largeSquareDensity : Measurable largeSquareDensity := by
  unfold largeSquareDensity
  exact (measurable_largeG.comp
    (measurable_const.mul measurable_id)).pow_const 2

theorem largeSquareDensity_nonneg (x : ℝ) :
    0 ≤ largeSquareDensity x := by
  exact sq_nonneg _

theorem largeSquareDensity_le_one {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    largeSquareDensity x ≤ 1 := by
  unfold largeSquareDensity
  have hg0 : 0 ≤ largeG ((largeK : ℝ) * x) :=
    largeG_nonneg (mul_nonneg (Nat.cast_nonneg _) hx.1)
  have hg1 : largeG ((largeK : ℝ) * x) ≤ 1 :=
    largeG_le_one (mul_nonneg (Nat.cast_nonneg _) hx.1)
  nlinarith

theorem product_largeSquareDensity_integrableOn_cube
    (ι : Type*) [Fintype ι] :
    IntegrableOn (fun t : ι → ℝ => ∏ i, largeSquareDensity (t i))
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf ι)
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top ι)
    (f := fun t : ι → ℝ => ∏ i, largeSquareDensity (t i))
    (Finset.measurable_prod _ fun i _ =>
      measurable_largeSquareDensity.comp (measurable_pi_apply i)) 1 ?_
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      ∏ i : ι, largeSquareDensity (t i) ≤ ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact largeSquareDensity_nonneg _
        · intro i hi
          exact largeSquareDensity_le_one (ht i (Set.mem_univ i))
      _ = 1 := Finset.prod_const_one
  · exact Finset.prod_nonneg fun i hi => largeSquareDensity_nonneg _

theorem integral_product_largeSquareDensity_cube
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      ∏ i, largeSquareDensity (t i)) =
      largeBaseMass ^ Fintype.card ι := by
  unfold BoundedGaps.Maynard.maynardCubeOf
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi
    (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => Set.Icc (0 : ℝ) 1)]
  rw [MeasureTheory.integral_fintype_prod_eq_pow]
  exact congrArg (fun z : ℝ => z ^ Fintype.card ι)
    integral_largeSquareDensity_Icc

theorem largeProduct_sq_eq_density_product (t : Fin largeK → ℝ) :
    largeProduct t ^ 2 = ∏ i, largeSquareDensity (t i) := by
  unfold largeProduct largeSquareDensity
  rw [Finset.prod_pow]

theorem largeCandidate_sq_le_density_product
    (t : Fin largeK → ℝ) :
    largeCandidate t ^ 2 ≤ ∏ i, largeSquareDensity (t i) := by
  classical
  by_cases ht : t ∈ BoundedGaps.Maynard.maynardSimplex largeK
  · rw [largeCandidate, if_pos ht, largeProduct_sq_eq_density_product]
  · rw [largeCandidate, if_neg ht, zero_pow (by omega : 2 ≠ 0)]
    exact Finset.prod_nonneg fun i hi => largeSquareDensity_nonneg _

theorem maynardI_largeCandidate_le :
    BoundedGaps.Maynard.maynardI largeK largeCandidate ≤
      largeBaseMass ^ largeK := by
  unfold BoundedGaps.Maynard.maynardI
  calc
    (∫ t in BoundedGaps.Maynard.maynardCube largeK,
      largeCandidate t ^ 2) ≤
        ∫ t in BoundedGaps.Maynard.maynardCube largeK,
          ∏ i, largeSquareDensity (t i) := by
      apply setIntegral_mono_on largeCandidate_sq_integrableOn
        (product_largeSquareDensity_integrableOn_cube (Fin largeK))
        (BoundedGaps.Maynard.maynardCube_measurable largeK)
      intro t ht
      exact largeCandidate_sq_le_density_product t
    _ = largeBaseMass ^ largeK := by
      change (∫ t : Fin largeK → ℝ in
        BoundedGaps.Maynard.maynardCubeOf (Fin largeK),
          ∏ i, largeSquareDensity (t i)) = _
      simpa only [Fintype.card_fin] using
        (integral_product_largeSquareDensity_cube (Fin largeK))

/-! ## Explicit numerical estimates -/

theorem log_one_add_largeAK_lt :
    Real.log (1 + largeA * (largeK : ℝ)) < 3 * largeA / 8 :=
  P.upper_log

theorem log_large_face_cutoff_gt :
    largeA / 3 < Real.log (1 + largeA * (largeK : ℝ) * (1 / 8 : ℝ)) :=
  P.lower_log

theorem largeBaseMass_lt_inv_AK :
    largeBaseMass < (largeA * (largeK : ℝ))⁻¹ := by
  unfold largeBaseMass
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hAK : 0 < largeA * (largeK : ℝ) := mul_pos largeA_pos hK
  exact (inv_lt_inv₀ (by linarith) hAK).mpr (by linarith)

theorem half_inv_AK_lt_largeBaseMass :
    (2 * (largeA * (largeK : ℝ)))⁻¹ < largeBaseMass := by
  unfold largeBaseMass
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hAK : 0 < largeA * (largeK : ℝ) := mul_pos largeA_pos hK
  have hKone : (1 : ℝ) ≤ largeK := by
    exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr largeK_ne_zero)
  have hAKone : 1 < largeA * (largeK : ℝ) := by
    have hA := largeA_ge_1024
    nlinarith
  apply (inv_lt_inv₀ (mul_pos (by norm_num) hAK)
    (add_pos_of_pos_of_nonneg zero_lt_one hAK.le)).mpr
  linarith

def largeFirstMoment : ℝ :=
  ∫ x : ℝ in Set.Icc (0 : ℝ) 1, x * largeSquareDensity x

theorem largeFirstMoment_integrand_le {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x * largeSquareDensity x ≤
      (largeA * (largeK : ℝ))⁻¹ *
        largeG ((largeK : ℝ) * x) := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hc : 0 < largeA * (largeK : ℝ) := mul_pos largeA_pos hK
  have hgeneric : ∀ {c x : ℝ}, 0 < c → 0 ≤ x →
      x * (1 + c * x)⁻¹ ^ 2 ≤ c⁻¹ * (1 + c * x)⁻¹ := by
    intro c x hc hx
    have hy : 0 < 1 + c * x := by positivity
    have hxle : x ≤ c⁻¹ * (1 + c * x) := by
      have heq : c⁻¹ * (1 + c * x) = x + c⁻¹ := by
        field_simp [hc.ne']
        ring
      rw [heq]
      exact le_add_of_nonneg_right (inv_nonneg.mpr hc.le)
    calc
      x * (1 + c * x)⁻¹ ^ 2 ≤
          (c⁻¹ * (1 + c * x)) * (1 + c * x)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right hxle (sq_nonneg _)
      _ = c⁻¹ * (1 + c * x)⁻¹ := by
        field_simp [hy.ne', hc.ne']
  simpa only [largeSquareDensity, largeG, mul_assoc] using
    (hgeneric hc hx.1)

theorem largeFirstMoment_le :
    largeFirstMoment ≤
      Real.log (1 + largeA * (largeK : ℝ)) /
        (largeA ^ 2 * (largeK : ℝ) ^ 2) := by
  have hleft : IntegrableOn (fun x : ℝ => x * largeSquareDensity x)
      (Set.Icc (0 : ℝ) 1) := by
    refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
      (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
      (hsfinite := measure_Icc_lt_top)
      (f := fun x : ℝ => x * largeSquareDensity x)
      (measurable_id.mul measurable_largeSquareDensity) 1 ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · calc
        x * largeSquareDensity x ≤ 1 * largeSquareDensity x :=
          mul_le_mul_of_nonneg_right hx.2 (largeSquareDensity_nonneg x)
        _ ≤ 1 := by simpa using largeSquareDensity_le_one hx
    · exact mul_nonneg hx.1 (largeSquareDensity_nonneg x)
  have hright : IntegrableOn
      (fun x : ℝ => (largeA * (largeK : ℝ))⁻¹ *
        largeG ((largeK : ℝ) * x)) (Set.Icc (0 : ℝ) 1) := by
    refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
      (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
      (hsfinite := measure_Icc_lt_top)
      (f := fun x : ℝ => (largeA * (largeK : ℝ))⁻¹ *
        largeG ((largeK : ℝ) * x))
      (measurable_const.mul
        (measurable_largeG.comp (measurable_const.mul measurable_id))) 1 ?_
    intro x hx
    have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
    have hKone : (1 : ℝ) ≤ largeK := by
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr largeK_ne_zero)
    have hAK : 1 ≤ largeA * (largeK : ℝ) := by
      have hA := largeA_ge_1024
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hg := largeG_le_one
        (mul_nonneg (Nat.cast_nonneg largeK) hx.1)
      have hi : (largeA * (largeK : ℝ))⁻¹ ≤ 1 := by
        rw [inv_le_one₀]
        · exact hAK
        · positivity
      calc
        (largeA * (largeK : ℝ))⁻¹ *
            largeG ((largeK : ℝ) * x) ≤ 1 *
            largeG ((largeK : ℝ) * x) :=
          mul_le_mul_of_nonneg_right hi
            (largeG_nonneg (mul_nonneg (Nat.cast_nonneg largeK) hx.1))
        _ ≤ 1 := by
          rw [one_mul]
          exact hg
    · exact mul_nonneg (inv_nonneg.mpr (mul_nonneg largeA_pos.le hK.le))
        (largeG_nonneg (mul_nonneg (Nat.cast_nonneg largeK) hx.1))
  unfold largeFirstMoment
  calc
    (∫ x in Set.Icc (0 : ℝ) 1, x * largeSquareDensity x) ≤
        ∫ x in Set.Icc (0 : ℝ) 1,
          (largeA * (largeK : ℝ))⁻¹ *
            largeG ((largeK : ℝ) * x) := by
      exact setIntegral_mono_on hleft hright measurableSet_Icc
        (fun x hx => largeFirstMoment_integrand_le hx)
    _ = (largeA * (largeK : ℝ))⁻¹ *
        (Real.log (1 + largeA * (largeK : ℝ)) /
          (largeA * (largeK : ℝ))) := by
      rw [integral_const_mul, setIntegral_largeG_Icc (by norm_num : (0 : ℝ) ≤ 1)]
      simp only [mul_one]
    _ = Real.log (1 + largeA * (largeK : ℝ)) /
        (largeA ^ 2 * (largeK : ℝ) ^ 2) := by
      have hK : (largeK : ℝ) ≠ 0 := (Nat.cast_pos.mpr largeK_pos).ne'
      have hA : largeA ≠ 0 := largeA_pos.ne'
      have halgebra : ∀ {A K L : ℝ}, A ≠ 0 → K ≠ 0 →
          (A * K)⁻¹ * (L / (A * K)) = L / (A ^ 2 * K ^ 2) := by
        intro A K L hA hK
        field_simp [hA, hK]
      exact halgebra hA hK

theorem largeFirstMoment_lt_three_quarters :
    largeFirstMoment < (3 / (4 * (largeK : ℝ))) * largeBaseMass := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hA := largeA_pos
  have hlog := log_one_add_largeAK_lt
  have hm := largeFirstMoment_le
  have ha := half_inv_AK_lt_largeBaseMass
  have hpos : 0 < (3 / (4 * (largeK : ℝ))) := by positivity
  calc
    largeFirstMoment ≤
        Real.log (1 + largeA * (largeK : ℝ)) /
          (largeA ^ 2 * (largeK : ℝ) ^ 2) := hm
    _ < (3 * largeA / 8) / (largeA ^ 2 * (largeK : ℝ) ^ 2) :=
      div_lt_div_of_pos_right hlog (by positivity)
    _ = (3 / (4 * (largeK : ℝ))) *
        (2 * (largeA * (largeK : ℝ)))⁻¹ := by
      field_simp [hA.ne', hK.ne']
      ring
    _ < (3 / (4 * (largeK : ℝ))) * largeBaseMass :=
      mul_lt_mul_of_pos_left ha hpos

/-! ## A weighted product-moment identity -/

def largeProductDensity {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∏ i, largeSquareDensity (t i)

def largeCoordinateSum {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∑ i, t i

theorem integral_coordinate_mul_productDensity_cube
    {ι : Type*} [Fintype ι] (i : ι) :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      t i * largeProductDensity t) =
      largeFirstMoment * largeBaseMass ^ (Fintype.card ι - 1) := by
  classical
  let f : ι → ℝ → ℝ := fun j x =>
    if j = i then x * largeSquareDensity x else largeSquareDensity x
  have hpoint (t : ι → ℝ) :
      ∏ j, f j (t j) = t i * largeProductDensity t := by
    unfold largeProductDensity
    rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (t j))
      (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => largeSquareDensity (t j)) (Finset.mem_univ i)]
    have hrest :
        ∏ j ∈ Finset.univ.erase i, f j (t j) =
          ∏ j ∈ Finset.univ.erase i, largeSquareDensity (t j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [f, if_neg hji]
    rw [hrest]
    simp only [f, if_pos]
    ring
  have hintegrals : ∏ j : ι,
      ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      largeFirstMoment * largeBaseMass ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : ι => ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Finset.mem_univ i)]
    simp only [f, if_pos]
    rw [show (∫ x : ℝ,
        x * largeSquareDensity x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) =
        largeFirstMoment by rfl]
    congr 1
    calc
      ∏ j ∈ Finset.univ.erase i,
          ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
          ∏ _j ∈ Finset.univ.erase i, largeBaseMass := by
            apply Finset.prod_congr rfl
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            have hfj : f j = largeSquareDensity := by
              funext x
              simp only [f, if_neg hji]
            rw [hfj]
            exact integral_largeSquareDensity_Icc
      _ = largeBaseMass ^ (Fintype.card ι - 1) := by
        simp only [Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ]
  unfold BoundedGaps.Maynard.maynardCubeOf
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi
    (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => Set.Icc (0 : ℝ) 1)]
  rw [← hintegrals, ← MeasureTheory.integral_fintype_prod_eq_prod f]
  congr 1
  funext t
  exact (hpoint t).symm

theorem coordinate_mul_productDensity_integrableOn_cube
    {ι : Type*} [Fintype ι] (i : ι) :
    IntegrableOn (fun t : ι → ℝ => t i * largeProductDensity t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf ι)
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top ι)
    (f := fun t : ι → ℝ => t i * largeProductDensity t)
    ((measurable_pi_apply i).mul
      (Finset.measurable_prod _ fun j _ =>
        measurable_largeSquareDensity.comp (measurable_pi_apply j))) 1 ?_
  intro t ht
  have hti : 0 ≤ t i := (ht i (Set.mem_univ i)).1
  have hti1 : t i ≤ 1 := (ht i (Set.mem_univ i)).2
  have hprod0 : 0 ≤ largeProductDensity t := by
    unfold largeProductDensity
    exact Finset.prod_nonneg fun j hj => largeSquareDensity_nonneg _
  have hprod1 : largeProductDensity t ≤ 1 := by
    unfold largeProductDensity
    calc
      ∏ j : ι, largeSquareDensity (t j) ≤ ∏ _j : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro j hj
          exact largeSquareDensity_nonneg _
        · intro j hj
          exact largeSquareDensity_le_one (ht j (Set.mem_univ j))
      _ = 1 := Finset.prod_const_one
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hti hprod0)]
  nlinarith

theorem integral_coordinateSum_mul_productDensity_cube
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      largeCoordinateSum t * largeProductDensity t) =
      (Fintype.card ι : ℝ) * largeFirstMoment *
        largeBaseMass ^ (Fintype.card ι - 1) := by
  classical
  unfold largeCoordinateSum
  have hfun : (fun t : ι → ℝ =>
      (∑ i, t i) * largeProductDensity t) =
      (fun t : ι → ℝ => ∑ i, t i * largeProductDensity t) := by
    funext t
    simpa using
      (Finset.sum_mul Finset.univ (fun i : ι => t i)
        (largeProductDensity t))
  rw [hfun]
  change (∫ t : ι → ℝ,
      ∑ i, t i * largeProductDensity t
      ∂(volume.restrict (BoundedGaps.Maynard.maynardCubeOf ι))) = _
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_coordinate_mul_productDensity_cube]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · intro i hi
    exact coordinate_mul_productDensity_integrableOn_cube i

theorem measurable_largeCoordinateSum
    (ι : Type*) [Fintype ι] :
    Measurable (largeCoordinateSum : (ι → ℝ) → ℝ) := by
  unfold largeCoordinateSum
  exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

theorem largeProductDensity_nonneg
    {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    0 ≤ largeProductDensity t := by
  unfold largeProductDensity
  exact Finset.prod_nonneg fun i hi => largeSquareDensity_nonneg _

theorem productDensity_integrableOn_cube
    (ι : Type*) [Fintype ι] :
    IntegrableOn (largeProductDensity : (ι → ℝ) → ℝ)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  change IntegrableOn (fun t : ι → ℝ =>
    ∏ i, largeSquareDensity (t i))
    (BoundedGaps.Maynard.maynardCubeOf ι)
  exact product_largeSquareDensity_integrableOn_cube ι

theorem coordinateSum_mul_productDensity_integrableOn_cube
    (ι : Type*) [Fintype ι] :
    IntegrableOn (fun t : ι → ℝ =>
      largeCoordinateSum t * largeProductDensity t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  classical
  have hsum : IntegrableOn
      (fun t : ι → ℝ => ∑ i, t i * largeProductDensity t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
    exact integrable_finsetSum Finset.univ fun i hi =>
      coordinate_mul_productDensity_integrableOn_cube i
  have hfun : (fun t : ι → ℝ =>
      largeCoordinateSum t * largeProductDensity t) =
      (fun t : ι → ℝ => ∑ i, t i * largeProductDensity t) := by
    funext t
    unfold largeCoordinateSum
    simpa using
      (Finset.sum_mul Finset.univ (fun i : ι => t i)
        (largeProductDensity t))
  rw [hfun]
  exact hsum

theorem card_largeFaceIndex (m : Fin largeK) :
    Fintype.card (BoundedGaps.Maynard.maynardFaceIndex largeK m) =
      largeK - 1 := by
  let e : BoundedGaps.Maynard.maynardFaceIndex largeK m ≃
      {i : Fin largeK // ¬i = m} := Equiv.refl _
  have he := Fintype.card_congr e
  have hc := @Fintype.card_subtype_compl (Fin largeK) inferInstance
    (fun i : Fin largeK => i = m) inferInstance inferInstance
  calc
    Fintype.card (BoundedGaps.Maynard.maynardFaceIndex largeK m) =
        Fintype.card {i : Fin largeK // ¬i = m} := he
    _ = largeK - 1 := by
      simpa only [Fintype.card_fin, Fintype.card_subtype_eq,
        Finset.filter_eq, Finset.card_singleton] using hc

def largeGoodRegion (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  BoundedGaps.Maynard.maynardCubeOf ι ∩
    {t | largeCoordinateSum t ≤ (7 : ℝ) / 8}

theorem largeGoodRegion_measurable
    (ι : Type*) [Fintype ι] :
    MeasurableSet (largeGoodRegion ι) := by
  unfold largeGoodRegion
  exact (MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Icc)).inter
      (measurableSet_Iic.preimage (measurable_largeCoordinateSum ι))

theorem largeGoodRegion_subset_cube
    (ι : Type*) [Fintype ι] :
    largeGoodRegion ι ⊆ BoundedGaps.Maynard.maynardCubeOf ι := by
  intro t ht
  exact ht.1

theorem badRegion_productDensity_integral_le
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι,
      largeProductDensity t) ≤
      ((8 : ℝ) / 7) * (Fintype.card ι : ℝ) *
        largeFirstMoment * largeBaseMass ^ (Fintype.card ι - 1) := by
  have hleft : IntegrableOn
      (largeProductDensity : (ι → ℝ) → ℝ)
      (BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι) :=
    (productDensity_integrableOn_cube ι).mono_set Set.diff_subset
  have hright : IntegrableOn (fun t : ι → ℝ =>
      ((8 : ℝ) / 7) *
        (largeCoordinateSum t * largeProductDensity t))
      (BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι) :=
    by
      have hfull : IntegrableOn (fun t : ι → ℝ =>
          ((8 : ℝ) / 7) *
            (largeCoordinateSum t * largeProductDensity t))
          (BoundedGaps.Maynard.maynardCubeOf ι) :=
        (coordinateSum_mul_productDensity_integrableOn_cube ι).const_mul
          ((8 : ℝ) / 7)
      exact hfull.mono_set Set.diff_subset
  have hmeas : MeasurableSet
      (BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι) :=
    (MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc)).diff
        (largeGoodRegion_measurable ι)
  calc
    (∫ t : ι → ℝ in
        BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι,
        largeProductDensity t) ≤
        ∫ t : ι → ℝ in
          BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι,
          ((8 : ℝ) / 7) *
            (largeCoordinateSum t * largeProductDensity t) := by
      apply setIntegral_mono_on hleft hright hmeas
      intro t ht
      have hcube := ht.1
      have hnmem := ht.2
      have hsum : (7 : ℝ) / 8 < largeCoordinateSum t := by
        by_contra hnot
        have hle : largeCoordinateSum t ≤ (7 : ℝ) / 8 := le_of_not_gt hnot
        exact hnmem ⟨hcube, hle⟩
      have hd := largeProductDensity_nonneg t
      nlinarith
    _ ≤ ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
          ((8 : ℝ) / 7) *
            (largeCoordinateSum t * largeProductDensity t) := by
      have hfull : IntegrableOn (fun t : ι → ℝ =>
          ((8 : ℝ) / 7) *
            (largeCoordinateSum t * largeProductDensity t))
          (BoundedGaps.Maynard.maynardCubeOf ι) :=
        (coordinateSum_mul_productDensity_integrableOn_cube ι).const_mul
          ((8 : ℝ) / 7)
      apply setIntegral_mono_set hfull
      · exact (ae_restrict_mem (MeasurableSet.pi Set.countable_univ
          (fun _ _ => measurableSet_Icc))).mono (fun t ht =>
            mul_nonneg (by norm_num)
              (mul_nonneg (by
                unfold largeCoordinateSum
                exact Finset.sum_nonneg fun i hi =>
                  (ht i (Set.mem_univ i)).1)
                (largeProductDensity_nonneg t)))
      · exact Filter.Eventually.of_forall fun t ht => Set.diff_subset ht
    _ = ((8 : ℝ) / 7) * (Fintype.card ι : ℝ) *
        largeFirstMoment * largeBaseMass ^ (Fintype.card ι - 1) := by
      rw [integral_const_mul,
        integral_coordinateSum_mul_productDensity_cube]
      ring

theorem largeK_ge_two : 2 ≤ largeK := P.two_le_k

theorem weighted_bad_bound_lt_six_sevenths
    {K : ℕ} (hK2 : 2 ≤ K) {a b : ℝ} (ha : 0 < a)
    (hb : b < (3 / (4 * (K : ℝ))) * a) :
    ((8 : ℝ) / 7) * ((K - 1 : ℕ) : ℝ) * b *
        a ^ (K - 1 - 1) <
      ((6 : ℝ) / 7) * a ^ (K - 1) := by
  have hK : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  have hK1 : 1 ≤ K := by omega
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK1]
    norm_num
  have hratio : ((K - 1 : ℕ) : ℝ) *
      (3 / (4 * (K : ℝ))) < (3 : ℝ) / 4 := by
    rw [hcast]
    have hden : 0 < (4 : ℝ) * (K : ℝ) := mul_pos (by norm_num) hK
    rw [show ((K : ℝ) - 1) * (3 / (4 * (K : ℝ))) =
      (((K : ℝ) - 1) * 3) / (4 * (K : ℝ)) by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hfactor : 0 < ((8 : ℝ) / 7) *
      ((K - 1 : ℕ) : ℝ) * a ^ (K - 2) := by
    have hkminus : 0 < ((K - 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    positivity
  have hmoment := mul_lt_mul_of_pos_left hb hfactor
  have hpoweq : a ^ (K - 2) * a = a ^ (K - 1) := by
    have hexp : K - 1 = (K - 2) + 1 := by omega
    rw [hexp, pow_succ]
  have hratio_mul := mul_lt_mul_of_pos_right hratio
    (mul_pos (by norm_num : (0 : ℝ) < 8 / 7)
      (pow_pos ha (K - 1)))
  have hexp : K - 1 - 1 = K - 2 := by omega
  rw [hexp]
  calc
    ((8 : ℝ) / 7) * ((K - 1 : ℕ) : ℝ) * b * a ^ (K - 2) =
        (((8 : ℝ) / 7) * ((K - 1 : ℕ) : ℝ) *
          a ^ (K - 2)) * b := by ring
    _ < (((8 : ℝ) / 7) * ((K - 1 : ℕ) : ℝ) *
          a ^ (K - 2)) * ((3 / (4 * (K : ℝ))) * a) := hmoment
    _ = (((K - 1 : ℕ) : ℝ) * (3 / (4 * (K : ℝ)))) *
          (((8 : ℝ) / 7) * a ^ (K - 1)) := by
      rw [← hpoweq]
      ring
    _ < ((3 : ℝ) / 4) *
          (((8 : ℝ) / 7) * a ^ (K - 1)) := hratio_mul
    _ = ((6 : ℝ) / 7) * a ^ (K - 1) := by ring

theorem badFace_productDensity_integral_lt_six_sevenths
    (m : Fin largeK) :
    (∫ t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ in
      BoundedGaps.Maynard.maynardCubeOf
          (BoundedGaps.Maynard.maynardFaceIndex largeK m) \
        largeGoodRegion (BoundedGaps.Maynard.maynardFaceIndex largeK m),
      largeProductDensity t) <
      ((6 : ℝ) / 7) * largeBaseMass ^ (largeK - 1) := by
  let ι := BoundedGaps.Maynard.maynardFaceIndex largeK m
  have hbound := badRegion_productDensity_integral_le ι
  rw [card_largeFaceIndex m] at hbound
  exact hbound.trans_lt (weighted_bad_bound_lt_six_sevenths
    largeK_ge_two largeBaseMass_pos
      largeFirstMoment_lt_three_quarters)

theorem goodFace_productDensity_integral_gt_one_seventh
    (m : Fin largeK) :
    ((1 : ℝ) / 7) * largeBaseMass ^ (largeK - 1) <
      ∫ t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ in
        largeGoodRegion (BoundedGaps.Maynard.maynardFaceIndex largeK m),
        largeProductDensity t := by
  let ι := BoundedGaps.Maynard.maynardFaceIndex largeK m
  have hdiff := setIntegral_sdiff (largeGoodRegion_measurable ι)
    (productDensity_integrableOn_cube ι)
    (largeGoodRegion_subset_cube ι)
  have htotal := integral_product_largeSquareDensity_cube ι
  change (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
    largeProductDensity t) = _ at htotal
  rw [card_largeFaceIndex m] at htotal
  have hbad := badFace_productDensity_integral_lt_six_sevenths m
  change (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ largeGoodRegion ι,
      largeProductDensity t) < _ at hbad
  change ((1 : ℝ) / 7) * largeBaseMass ^ (largeK - 1) <
    ∫ t : ι → ℝ in largeGoodRegion ι, largeProductDensity t
  rw [htotal] at hdiff
  nlinarith [pow_pos largeBaseMass_pos (largeK - 1)]

/-! ## The inner face integral on the good region -/

theorem maynardInsertCoordinate_mem_simplex_of_pos
    {k : ℕ} (hk : 0 < k) (m : Fin k) (x : ℝ)
    (t : BoundedGaps.Maynard.maynardFaceIndex k m → ℝ)
    (hx : 0 ≤ x) (htnonneg : ∀ j, 0 ≤ t j)
    (htsum : x + ∑ j, t j ≤ 1) :
    BoundedGaps.Maynard.maynardInsertCoordinate m x t ∈
      BoundedGaps.Maynard.maynardSimplex k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have htface : t ∈ BoundedGaps.Maynard.maynardFaceSimplex m := by
    refine ⟨htnonneg, ?_⟩
    linarith
  rw [BoundedGaps.Maynard.insert_mem_simplex_iff m x t htface]
  exact ⟨hx, by linarith⟩

theorem prod_maynardInsertCoordinate_of_pos
    {k : ℕ} (hk : 0 < k) (m : Fin k) (x : ℝ)
    (t : BoundedGaps.Maynard.maynardFaceIndex k m → ℝ)
    (f : ℝ → ℝ) :
    (∏ i, f (BoundedGaps.Maynard.maynardInsertCoordinate m x t i)) =
      f x * ∏ j, f (t j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Fin.prod_univ_succAbove]
  rw [BoundedGaps.Maynard.maynardInsertCoordinate_at]
  rw [← (BoundedGaps.Maynard.faceIndexEquiv m).prod_comp (fun j => f (t j))]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [BoundedGaps.Maynard.maynardInsertCoordinate_off]
  congr 2
  exact Fin.succAbove_ne m i

def largeFaceProduct {ι : Type*} [Fintype ι] (t : ι → ℝ) : ℝ :=
  ∏ j, largeG ((largeK : ℝ) * t j)

theorem largeFaceProduct_sq_eq_productDensity
    {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    largeFaceProduct t ^ 2 = largeProductDensity t := by
  unfold largeFaceProduct largeProductDensity largeSquareDensity
  rw [Finset.prod_pow]

theorem largeFaceProduct_pos_of_mem_cube
    {ι : Type*} [Fintype ι] {t : ι → ℝ}
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    0 < largeFaceProduct t := by
  unfold largeFaceProduct
  apply Finset.prod_pos
  intro j hj
  exact largeG_pos (mul_nonneg (Nat.cast_nonneg _)
    (ht j (Set.mem_univ j)).1)

theorem largeCandidate_insert_eq_on_short_interval
    (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ)
    (ht : t ∈ largeGoodRegion
      (BoundedGaps.Maynard.maynardFaceIndex largeK m))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ)) :
    largeCandidate
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t) =
      largeG ((largeK : ℝ) * x) * largeFaceProduct t := by
  have htnonneg : ∀ j, 0 ≤ t j := fun j =>
    (ht.1 j (Set.mem_univ j)).1
  have hsum : x + ∑ j, t j ≤ 1 := by
    have hface := ht.2
    change largeCoordinateSum t ≤ (7 : ℝ) / 8 at hface
    change x + largeCoordinateSum t ≤ 1
    nlinarith [hx.2]
  have hsimp := maynardInsertCoordinate_mem_simplex_of_pos largeK_pos m x t
    hx.1 htnonneg hsum
  rw [largeCandidate, if_pos hsimp]
  unfold largeProduct
  have hp := prod_maynardInsertCoordinate_of_pos largeK_pos m x t
    (fun y : ℝ => largeG ((largeK : ℝ) * y))
  simpa only [largeFaceProduct] using hp

def largeShortMass : ℝ :=
  ∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 8 : ℝ),
    largeG ((largeK : ℝ) * x)

theorem largeShortMass_eq :
    largeShortMass =
      Real.log (1 + largeA * (largeK : ℝ) * (1 / 8 : ℝ)) /
        (largeA * (largeK : ℝ)) := by
  unfold largeShortMass
  exact setIntegral_largeG_Icc (by norm_num)

theorem inv_threeK_lt_largeShortMass :
    (3 * (largeK : ℝ))⁻¹ < largeShortMass := by
  rw [largeShortMass_eq]
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hden : 0 < largeA * (largeK : ℝ) := mul_pos largeA_pos hK
  calc
    (3 * (largeK : ℝ))⁻¹ =
        ((largeA : ℝ) / 3) / (largeA * (largeK : ℝ)) := by
      field_simp [largeA_pos.ne', hK.ne']
    _ < Real.log (1 + largeA * (largeK : ℝ) * (1 / 8 : ℝ)) /
        (largeA * (largeK : ℝ)) :=
      div_lt_div_of_pos_right log_large_face_cutoff_gt hden

theorem shortCandidateIntegral_eq
    (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ)
    (ht : t ∈ largeGoodRegion
      (BoundedGaps.Maynard.maynardFaceIndex largeK m)) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 8 : ℝ),
      largeCandidate
        (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) =
      largeFaceProduct t * largeShortMass := by
  calc
    (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 8 : ℝ),
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) =
        ∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 8 : ℝ),
          largeFaceProduct t * largeG ((largeK : ℝ) * x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) =
        largeFaceProduct t * largeG ((largeK : ℝ) * x)
      rw [largeCandidate_insert_eq_on_short_interval m t ht hx]
      ring
    _ = largeFaceProduct t * largeShortMass := by
      rw [integral_const_mul]
      rfl

theorem faceInnerIntegral_gt
    (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ)
    (ht : t ∈ largeGoodRegion
      (BoundedGaps.Maynard.maynardFaceIndex largeK m)) :
    largeFaceProduct t * (3 * (largeK : ℝ))⁻¹ <
      ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
  have hfacepos : 0 < largeFaceProduct t :=
    largeFaceProduct_pos_of_mem_cube ht.1
  have hshort := mul_lt_mul_of_pos_left inv_threeK_lt_largeShortMass hfacepos
  have hmono :
      (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 8 : ℝ),
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ≤
      ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t) := by
    apply setIntegral_mono_set (largeCandidate_face_integrableOn m t)
    · exact Filter.Eventually.of_forall fun x => largeCandidate_nonneg _
    · exact Filter.Eventually.of_forall fun x hx =>
        ⟨hx.1, hx.2.trans (by norm_num)⟩
  calc
    largeFaceProduct t * (3 * (largeK : ℝ))⁻¹ <
        largeFaceProduct t * largeShortMass := hshort
    _ = (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 8 : ℝ),
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) :=
      (shortCandidateIntegral_eq m t ht).symm
    _ ≤ _ := hmono

theorem faceInnerIntegral_sq_gt
    (m : Fin largeK)
    (t : BoundedGaps.Maynard.maynardFaceIndex largeK m → ℝ)
    (ht : t ∈ largeGoodRegion
      (BoundedGaps.Maynard.maynardFaceIndex largeK m)) :
    (9 * (largeK : ℝ) ^ 2)⁻¹ * largeProductDensity t <
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hfacepos : 0 < largeFaceProduct t :=
    largeFaceProduct_pos_of_mem_cube ht.1
  have hlowerpos : 0 < largeFaceProduct t * (3 * (largeK : ℝ))⁻¹ :=
    mul_pos hfacepos (inv_pos.mpr (mul_pos (by norm_num) hK))
  have hinner := faceInnerIntegral_gt m t ht
  have hsq :
      (largeFaceProduct t * (3 * (largeK : ℝ))⁻¹) ^ 2 <
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        largeCandidate
          (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    nlinarith
  calc
    (9 * (largeK : ℝ) ^ 2)⁻¹ * largeProductDensity t =
        (largeFaceProduct t * (3 * (largeK : ℝ))⁻¹) ^ 2 := by
      rw [← largeFaceProduct_sq_eq_productDensity]
      field_simp [hK.ne']
      ring
    _ < _ := hsq

theorem maynardJ_largeCandidate_gt (m : Fin largeK) :
    (63 * (largeK : ℝ) ^ 2)⁻¹ * largeBaseMass ^ (largeK - 1) <
      BoundedGaps.Maynard.maynardJ largeK m largeCandidate := by
  let ι := BoundedGaps.Maynard.maynardFaceIndex largeK m
  let c : ℝ := (9 * (largeK : ℝ) ^ 2)⁻¹
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hc : 0 < c := by
    unfold c
    positivity
  have hgood := goodFace_productDensity_integral_gt_one_seventh m
  change ((1 : ℝ) / 7) * largeBaseMass ^ (largeK - 1) <
    ∫ t : ι → ℝ in largeGoodRegion ι, largeProductDensity t at hgood
  have hscaled := mul_lt_mul_of_pos_left hgood hc
  have hdensityCube : IntegrableOn (fun t : ι → ℝ =>
      c * largeProductDensity t)
      (BoundedGaps.Maynard.maynardCubeOf ι) :=
    (productDensity_integrableOn_cube ι).const_mul c
  have hsquareCube : IntegrableOn
      (fun t : ι → ℝ =>
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          largeCandidate
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2)
      (BoundedGaps.Maynard.maynardCubeOf ι) :=
    largeCandidate_face_integrand_integrableOn m
  have hpointwise :
      (∫ t : ι → ℝ in largeGoodRegion ι,
        c * largeProductDensity t) ≤
      ∫ t : ι → ℝ in largeGoodRegion ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          largeCandidate
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    apply setIntegral_mono_on
      (hdensityCube.mono_set (largeGoodRegion_subset_cube ι))
      (hsquareCube.mono_set (largeGoodRegion_subset_cube ι))
      (largeGoodRegion_measurable ι)
    intro t ht
    exact (faceInnerIntegral_sq_gt m t ht).le
  have hsubset :
      (∫ t : ι → ℝ in largeGoodRegion ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          largeCandidate
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2) ≤
      ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          largeCandidate
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2 := by
    apply setIntegral_mono_set hsquareCube
    · exact Filter.Eventually.of_forall fun t => sq_nonneg _
    · exact Filter.Eventually.of_forall fun t ht =>
        largeGoodRegion_subset_cube ι ht
  unfold BoundedGaps.Maynard.maynardJ
  calc
    (63 * (largeK : ℝ) ^ 2)⁻¹ * largeBaseMass ^ (largeK - 1) =
        c * (((1 : ℝ) / 7) * largeBaseMass ^ (largeK - 1)) := by
      unfold c
      field_simp [hK.ne']
      ring
    _ < c * (∫ t : ι → ℝ in largeGoodRegion ι,
        largeProductDensity t) := hscaled
    _ = (∫ t : ι → ℝ in largeGoodRegion ι,
        c * largeProductDensity t) := by rw [integral_const_mul]
    _ ≤ (∫ t : ι → ℝ in largeGoodRegion ι,
        (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
          largeCandidate
            (BoundedGaps.Maynard.maynardInsertCoordinate m x t)) ^ 2) := hpointwise
    _ ≤ _ := hsubset

/-! ## Positivity of the denominator -/

def largeBoxWidth : ℝ := (2 * (largeK : ℝ))⁻¹

def largePositiveBox : Set (Fin largeK → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => largeBoxWidth)

theorem largeBoxWidth_pos : 0 < largeBoxWidth := by
  unfold largeBoxWidth
  exact inv_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr largeK_pos))

theorem largeBoxWidth_le_one : largeBoxWidth ≤ 1 := by
  unfold largeBoxWidth
  rw [inv_le_one₀]
  · have hK : (1 : ℝ) ≤ largeK :=
      Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr largeK_ne_zero)
    nlinarith
  · exact mul_pos (by norm_num) (Nat.cast_pos.mpr largeK_pos)

theorem largePositiveBox_volume_pos :
    0 < volume largePositiveBox := by
  unfold largePositiveBox
  rw [Real.volume_Icc_pi]
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (ENNReal.ofReal_pos.mpr (by
    simpa only [sub_zero] using largeBoxWidth_pos)).ne'

theorem largePositiveBox_subset_simplex :
    largePositiveBox ⊆ BoundedGaps.Maynard.maynardSimplex largeK := by
  intro t ht
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hcube : t ∈ BoundedGaps.Maynard.maynardCube largeK := by
    intro i hi
    exact ⟨ht.1 i, (ht.2 i).trans largeBoxWidth_le_one⟩
  refine ⟨hcube, ?_⟩
  have hsum : (∑ i, t i) ≤ ∑ _i : Fin largeK, largeBoxWidth := by
    exact Finset.sum_le_sum fun i hi => ht.2 i
  have hwidthsum : (∑ _i : Fin largeK, largeBoxWidth) = (1 : ℝ) / 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold largeBoxWidth
    field_simp [hK.ne']
  rw [hwidthsum] at hsum
  linarith

theorem largeCandidate_pos_on_largePositiveBox
    {t : Fin largeK → ℝ} (ht : t ∈ largePositiveBox) :
    0 < largeCandidate t := by
  have hsimp := largePositiveBox_subset_simplex ht
  rw [largeCandidate, if_pos hsimp]
  unfold largeProduct
  apply Finset.prod_pos
  intro i hi
  exact largeG_pos (mul_nonneg (Nat.cast_nonneg _) (ht.1 i))

theorem maynardI_largeCandidate_pos :
    0 < BoundedGaps.Maynard.maynardI largeK largeCandidate := by
  unfold BoundedGaps.Maynard.maynardI
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => sq_nonneg (largeCandidate t))
    largeCandidate_sq_integrableOn).2
  have hsubset : largePositiveBox ⊆
      Function.support (fun t : Fin largeK → ℝ => largeCandidate t ^ 2) ∩
        BoundedGaps.Maynard.maynardCube largeK := by
    intro t ht
    have hpos := largeCandidate_pos_on_largePositiveBox ht
    refine ⟨?_, (largePositiveBox_subset_simplex ht).1⟩
    exact pow_ne_zero 2 hpos.ne'
  exact largePositiveBox_volume_pos.trans_le (measure_mono hsubset)

/-! ## The explicit variational quotient -/

theorem sum_maynardJ_largeCandidate_gt :
    (largeK : ℝ) *
        ((63 * (largeK : ℝ) ^ 2)⁻¹ *
          largeBaseMass ^ (largeK - 1)) <
      ∑ m : Fin largeK,
        BoundedGaps.Maynard.maynardJ largeK m largeCandidate := by
  have huniv : (Finset.univ : Finset (Fin largeK)).Nonempty := by
    refine ⟨⟨0, largeK_pos⟩, Finset.mem_univ _⟩
  calc
    (largeK : ℝ) *
        ((63 * (largeK : ℝ) ^ 2)⁻¹ *
          largeBaseMass ^ (largeK - 1)) =
        ∑ _m : Fin largeK,
          (63 * (largeK : ℝ) ^ 2)⁻¹ *
            largeBaseMass ^ (largeK - 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ∑ m : Fin largeK,
        BoundedGaps.Maynard.maynardJ largeK m largeCandidate := by
      exact Finset.sum_lt_sum_of_nonempty huniv fun m hm =>
        maynardJ_largeCandidate_gt m

theorem explicit_ratio_lower_bound
    {K : ℕ} (hKpos : 0 < K) {a : ℝ} (ha : 0 < a)
    (haUpper : a < (1024 * (K : ℝ))⁻¹) :
    12 < ((K : ℝ) * ((63 * (K : ℝ) ^ 2)⁻¹ * a ^ (K - 1))) /
      a ^ K := by
  have hK : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hKpos.ne'
  have hpowe : a ^ K = a ^ (K - 1) * a := by
    have hexp : K = (K - 1) + 1 := by omega
    calc
      a ^ K = a ^ ((K - 1) + 1) := congrArg (fun n : ℕ => a ^ n) hexp
      _ = a ^ (K - 1) * a := pow_succ _ _
  have heq :
      ((K : ℝ) * ((63 * (K : ℝ) ^ 2)⁻¹ * a ^ (K - 1))) /
          a ^ K =
        (63 * (K : ℝ) * a)⁻¹ := by
    rw [hpowe]
    field_simp [hK.ne', ha.ne', pow_ne_zero _ ha.ne']
  rw [heq]
  have hsmall : 63 * (K : ℝ) * a < (1 : ℝ) / 12 := by
    calc
      63 * (K : ℝ) * a <
          63 * (K : ℝ) * (1024 * (K : ℝ))⁻¹ :=
        mul_lt_mul_of_pos_left haUpper (mul_pos (by norm_num) hK)
      _ = (63 : ℝ) / 1024 := by
        field_simp [hK.ne']
      _ < (1 : ℝ) / 12 := by norm_num
  have hden : 0 < 63 * (K : ℝ) * a := by positivity
  rw [inv_eq_one_div]
  exact (lt_div_iff₀ hden).2 (by nlinarith)

theorem maynardRatio_largeCandidate_gt_twelve :
    12 < BoundedGaps.Maynard.maynardRatio largeK largeCandidate := by
  let L : ℝ := (largeK : ℝ) *
    ((63 * (largeK : ℝ) ^ 2)⁻¹ *
      largeBaseMass ^ (largeK - 1))
  let S : ℝ := ∑ m : Fin largeK,
    BoundedGaps.Maynard.maynardJ largeK m largeCandidate
  let I : ℝ := BoundedGaps.Maynard.maynardI largeK largeCandidate
  have hL : 0 < L := by
    unfold L
    have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
    exact mul_pos hK (mul_pos
      (inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hK)))
      (pow_pos largeBaseMass_pos _))
  have hsum : L < S := by
    exact sum_maynardJ_largeCandidate_gt
  have hIpos : 0 < I := maynardI_largeCandidate_pos
  have hIle : I ≤ largeBaseMass ^ largeK := maynardI_largeCandidate_le
  have hnumeric : 12 < L / largeBaseMass ^ largeK := by
    unfold L
    apply explicit_ratio_lower_bound largeK_pos largeBaseMass_pos
    have hupper := largeBaseMass_lt_inv_AK
    have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
    apply hupper.trans_le
    exact (inv_le_inv₀ (mul_pos largeA_pos hK) (by positivity)).2
      (mul_le_mul_of_nonneg_right largeA_ge_1024 (Nat.cast_nonneg _))
  unfold BoundedGaps.Maynard.maynardRatio
  change 12 < S / I
  calc
    12 < L / largeBaseMass ^ largeK := hnumeric
    _ ≤ L / I := div_le_div_of_nonneg_left hL.le hIpos hIle
    _ < S / I := div_lt_div_of_pos_right hsum hIpos

end

end MaynardBFT.Sieve

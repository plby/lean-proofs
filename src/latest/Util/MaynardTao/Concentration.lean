/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Ratio

/-!
# Concentration for the inverse-affine product density

This is the quantitative replacement for the first-moment Markov bound in
the mirrored variable-dimensional development.  The coordinate variables are
independent under the product density, so their centered cross moments
vanish exactly and the variance is controlled by a one-dimensional second
moment.
-/

namespace MaynardTao

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

noncomputable def variableSecondMoment (K : ℕ) (A : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
    x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x

noncomputable def variableCoordinateMean (K : ℕ) (A : ℝ) : ℝ :=
  Erdos4.VariableMaynard.firstMoment K A /
    Erdos4.VariableMaynard.baseMass K A

theorem variableSecondMoment_integrand_le {K : ℕ} {A x : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x ≤
      (A * (K : ℝ))⁻¹ ^ 2 := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hc : 0 < A * (K : ℝ) := mul_pos hA hKR
  have hden : 0 < 1 + A * (K : ℝ) * x := by
    have hxprod : 0 ≤ A * (K : ℝ) * x :=
      mul_nonneg hc.le hx.1
    linarith
  unfold Erdos4.VariableMaynard.squareDensity Erdos4.VariableMaynard.factor
  have hxbound : x / (1 + A * (K : ℝ) * x) ≤
      (A * (K : ℝ))⁻¹ := by
    rw [div_le_iff₀ hden]
    have heq : (A * (K : ℝ))⁻¹ *
        (1 + A * (K : ℝ) * x) = x + (A * (K : ℝ))⁻¹ := by
      field_simp [hc.ne']
      ring
    rw [heq]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hc.le)
  have hxdiv0 : 0 ≤ x / (1 + A * (K : ℝ) * x) :=
    div_nonneg hx.1 hden.le
  have hsquare := pow_le_pow_left₀ hxdiv0 hxbound 2
  calc
    x ^ 2 * (1 + A * ((K : ℝ) * x))⁻¹ ^ 2 =
        (x / (1 + A * (K : ℝ) * x)) ^ 2 := by
      field_simp [hden.ne']
    _ ≤ _ := hsquare

theorem variableSecondMoment_le {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    variableSecondMoment K A ≤ (A * (K : ℝ))⁻¹ ^ 2 := by
  have hleft : IntegrableOn (fun x : ℝ =>
      x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x)
      (Set.Icc (0 : ℝ) 1) := by
    refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
      (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
      (hsfinite := measure_Icc_lt_top)
      (f := fun x : ℝ =>
        x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x)
      ((measurable_id.pow_const 2).mul
        (Erdos4.VariableMaynard.measurable_squareDensity K A)) 1 ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · calc
        x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x ≤
            1 * Erdos4.VariableMaynard.squareDensity K A x := by
          have hsq : x ^ 2 ≤ 1 := by
            nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
          exact mul_le_mul_of_nonneg_right
            hsq (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
        _ ≤ 1 := by
          simpa using Erdos4.VariableMaynard.squareDensity_le_one hA hx
    · exact mul_nonneg (sq_nonneg _) (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
  have hright : IntegrableOn (fun _ : ℝ => (A * (K : ℝ))⁻¹ ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    integrableOn_const measure_Icc_lt_top.ne
  unfold variableSecondMoment
  calc
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x) ≤
        ∫ _x : ℝ in Set.Icc (0 : ℝ) 1,
          (A * (K : ℝ))⁻¹ ^ 2 := by
      exact setIntegral_mono_on hleft hright measurableSet_Icc
        (fun x hx => variableSecondMoment_integrand_le hK hA hx)
    _ = (A * (K : ℝ))⁻¹ ^ 2 := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le] <;> norm_num

theorem variableCoordinateMean_mul_baseMass {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    variableCoordinateMean K A * Erdos4.VariableMaynard.baseMass K A =
      Erdos4.VariableMaynard.firstMoment K A := by
  unfold variableCoordinateMean
  exact div_mul_cancel₀ _
    (Erdos4.VariableMaynard.baseMass_pos hK hA).ne'

theorem variableCoordinateMean_nonneg {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    0 ≤ variableCoordinateMean K A := by
  unfold variableCoordinateMean
  apply div_nonneg
  · unfold Erdos4.VariableMaynard.firstMoment
    exact setIntegral_nonneg measurableSet_Icc fun x hx =>
      mul_nonneg hx.1 (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
  · exact (Erdos4.VariableMaynard.baseMass_pos hK hA).le

theorem variableFirstMoment_integrableOn {K : ℕ} {A : ℝ}
    (hA : 0 < A) :
    IntegrableOn (fun x : ℝ =>
      x * Erdos4.VariableMaynard.squareDensity K A x)
      (Set.Icc (0 : ℝ) 1) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top)
    (f := fun x : ℝ => x * Erdos4.VariableMaynard.squareDensity K A x)
    (measurable_id.mul (Erdos4.VariableMaynard.measurable_squareDensity K A)) 1 ?_
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      x * Erdos4.VariableMaynard.squareDensity K A x ≤
          1 * Erdos4.VariableMaynard.squareDensity K A x :=
        mul_le_mul_of_nonneg_right hx.2
          (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
      _ ≤ 1 := by
        simpa using Erdos4.VariableMaynard.squareDensity_le_one hA hx
  · exact mul_nonneg hx.1
      (Erdos4.VariableMaynard.squareDensity_nonneg K A x)

theorem variableSquareDensity_integrableOn {K : ℕ} {A : ℝ}
    (hA : 0 < A) :
    IntegrableOn (Erdos4.VariableMaynard.squareDensity K A)
      (Set.Icc (0 : ℝ) 1) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top)
    (f := Erdos4.VariableMaynard.squareDensity K A)
    (Erdos4.VariableMaynard.measurable_squareDensity K A) 1 ?_
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact Erdos4.VariableMaynard.squareDensity_le_one hA hx
  · exact Erdos4.VariableMaynard.squareDensity_nonneg K A x

noncomputable def variableCenteredDensity (K : ℕ) (A x : ℝ) : ℝ :=
  (x - variableCoordinateMean K A) *
    Erdos4.VariableMaynard.squareDensity K A x

theorem variableCenteredDensity_integral_eq_zero {K : ℕ} {A : ℝ}
    (hK : 0 < K) (hA : 0 < A) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      variableCenteredDensity K A x) = 0 := by
  have hfirst := variableFirstMoment_integrableOn (K := K) hA
  have hdensity := variableSquareDensity_integrableOn (K := K) hA
  have hconst := hdensity.const_mul (variableCoordinateMean K A)
  unfold variableCenteredDensity
  rw [show (fun x : ℝ =>
      (x - variableCoordinateMean K A) *
        Erdos4.VariableMaynard.squareDensity K A x) =
      (fun x : ℝ =>
        x * Erdos4.VariableMaynard.squareDensity K A x -
          variableCoordinateMean K A *
            Erdos4.VariableMaynard.squareDensity K A x) by
    funext x
    ring]
  rw [integral_sub hfirst hconst, integral_const_mul,
    show (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      x * Erdos4.VariableMaynard.squareDensity K A x) =
        Erdos4.VariableMaynard.firstMoment K A by rfl,
    Erdos4.VariableMaynard.integral_squareDensity_Icc hK hA,
    variableCoordinateMean_mul_baseMass hK hA]
  ring

noncomputable def variableCenteredSquareDensity (K : ℕ) (A x : ℝ) : ℝ :=
  (x - variableCoordinateMean K A) ^ 2 *
    Erdos4.VariableMaynard.squareDensity K A x

theorem variableCenteredSquareDensity_integrableOn {K : ℕ} {A : ℝ}
    (hA : 0 < A) :
    IntegrableOn (variableCenteredSquareDensity K A)
      (Set.Icc (0 : ℝ) 1) := by
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top)
    (f := variableCenteredSquareDensity K A)
    (((measurable_id.sub measurable_const).pow_const 2).mul
      (Erdos4.VariableMaynard.measurable_squareDensity K A))
    ((1 + |variableCoordinateMean K A|) ^ 2) ?_
  intro x hx
  unfold variableCenteredSquareDensity
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hdiff : |x - variableCoordinateMean K A| ≤
        1 + |variableCoordinateMean K A| := by
      calc
        |x - variableCoordinateMean K A| ≤
            |x| + |variableCoordinateMean K A| := by
          simpa using abs_sub_le x 0 (variableCoordinateMean K A)
        _ ≤ 1 + |variableCoordinateMean K A| := by
          rw [abs_of_nonneg hx.1]
          simpa [add_comm] using
            add_le_add_right hx.2 |variableCoordinateMean K A|
    calc
      (x - variableCoordinateMean K A) ^ 2 *
          Erdos4.VariableMaynard.squareDensity K A x ≤
          (1 + |variableCoordinateMean K A|) ^ 2 *
            Erdos4.VariableMaynard.squareDensity K A x := by
        exact mul_le_mul_of_nonneg_right
          (by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2)
          (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
      _ ≤ (1 + |variableCoordinateMean K A|) ^ 2 := by
        have hnonneg : 0 ≤ (1 + |variableCoordinateMean K A|) ^ 2 :=
          sq_nonneg _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Erdos4.VariableMaynard.squareDensity_le_one hA hx) hnonneg
  · exact mul_nonneg (sq_nonneg _)
      (Erdos4.VariableMaynard.squareDensity_nonneg K A x)

theorem variableCenteredSquareDensity_integral_le_secondMoment
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      variableCenteredSquareDensity K A x) ≤
      variableSecondMoment K A := by
  have hcenter := variableCenteredSquareDensity_integrableOn (K := K) hA
  have hsecond : IntegrableOn (fun x : ℝ =>
      x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x)
      (Set.Icc (0 : ℝ) 1) := by
    refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
      (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
      (hsfinite := measure_Icc_lt_top)
      (f := fun x : ℝ =>
        x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x)
      ((measurable_id.pow_const 2).mul
        (Erdos4.VariableMaynard.measurable_squareDensity K A)) 1 ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · have hsq : x ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
      calc
        x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x ≤
            1 * Erdos4.VariableMaynard.squareDensity K A x :=
          mul_le_mul_of_nonneg_right hsq
            (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
        _ ≤ 1 := by
          simpa using Erdos4.VariableMaynard.squareDensity_le_one hA hx
    · exact mul_nonneg (sq_nonneg _)
        (Erdos4.VariableMaynard.squareDensity_nonneg K A x)
  have hmean0 := variableCoordinateMean_nonneg hK hA
  have hfirst := variableFirstMoment_integrableOn (K := K) hA
  have hdensity := variableSquareDensity_integrableOn (K := K) hA
  have hconst := hdensity.const_mul (variableCoordinateMean K A)
  have hidentity :
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        variableCenteredSquareDensity K A x) =
        variableSecondMoment K A -
          variableCoordinateMean K A ^ 2 *
            Erdos4.VariableMaynard.baseMass K A := by
    unfold variableCenteredSquareDensity variableSecondMoment
    rw [show (fun x : ℝ =>
        (x - variableCoordinateMean K A) ^ 2 *
          Erdos4.VariableMaynard.squareDensity K A x) =
        (fun x : ℝ =>
          x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x -
            2 * variableCoordinateMean K A *
              (x * Erdos4.VariableMaynard.squareDensity K A x) +
            variableCoordinateMean K A ^ 2 *
              Erdos4.VariableMaynard.squareDensity K A x) by
      funext x
      ring]
    change (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
      (((fun x : ℝ =>
          x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x) -
        (fun x : ℝ => 2 * variableCoordinateMean K A *
          (x * Erdos4.VariableMaynard.squareDensity K A x))) +
        (fun x : ℝ => variableCoordinateMean K A ^ 2 *
          Erdos4.VariableMaynard.squareDensity K A x)) x) = _
    calc
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        (((fun x : ℝ =>
            x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x) -
          (fun x : ℝ => 2 * variableCoordinateMean K A *
            (x * Erdos4.VariableMaynard.squareDensity K A x))) +
          (fun x : ℝ => variableCoordinateMean K A ^ 2 *
            Erdos4.VariableMaynard.squareDensity K A x)) x) =
          (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x -
              2 * variableCoordinateMean K A *
                (x * Erdos4.VariableMaynard.squareDensity K A x)) +
            ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
              variableCoordinateMean K A ^ 2 *
                Erdos4.VariableMaynard.squareDensity K A x := by
        exact integral_add
          (hsecond.sub (hfirst.const_mul (2 * variableCoordinateMean K A)))
          (hdensity.const_mul (variableCoordinateMean K A ^ 2))
      _ = ((∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            x ^ 2 * Erdos4.VariableMaynard.squareDensity K A x) -
          ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            2 * variableCoordinateMean K A *
              (x * Erdos4.VariableMaynard.squareDensity K A x)) +
          ∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            variableCoordinateMean K A ^ 2 *
              Erdos4.VariableMaynard.squareDensity K A x := by
        rw [integral_sub hsecond
          (hfirst.const_mul (2 * variableCoordinateMean K A))]
      _ = variableSecondMoment K A -
          variableCoordinateMean K A ^ 2 *
            Erdos4.VariableMaynard.baseMass K A := by
        rw [integral_const_mul, integral_const_mul,
          show (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
            x * Erdos4.VariableMaynard.squareDensity K A x) =
              Erdos4.VariableMaynard.firstMoment K A by rfl,
          Erdos4.VariableMaynard.integral_squareDensity_Icc hK hA,
          ← variableCoordinateMean_mul_baseMass hK hA]
        unfold variableSecondMoment
        ring
  rw [hidentity]
  exact sub_le_self _ (mul_nonneg (sq_nonneg _)
    (Erdos4.VariableMaynard.baseMass_pos hK hA).le)

theorem integral_centeredCoordinate_mul_productDensity_cube_eq_zero
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    {ι : Type*} [Fintype ι] (i : ι) :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      (t i - variableCoordinateMean K A) *
        Erdos4.VariableMaynard.productDensity K A t) = 0 := by
  classical
  let f : ι → ℝ → ℝ := fun j x =>
    if j = i then variableCenteredDensity K A x
    else Erdos4.VariableMaynard.squareDensity K A x
  have hpoint (t : ι → ℝ) :
      ∏ j, f j (t j) =
        (t i - variableCoordinateMean K A) *
          Erdos4.VariableMaynard.productDensity K A t := by
    unfold Erdos4.VariableMaynard.productDensity
    rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (t j))
      (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => Erdos4.VariableMaynard.squareDensity K A (t j))
      (Finset.mem_univ i)]
    have hrest :
        ∏ j ∈ Finset.univ.erase i, f j (t j) =
          ∏ j ∈ Finset.univ.erase i,
            Erdos4.VariableMaynard.squareDensity K A (t j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [f, if_neg hji]
    rw [hrest]
    simp only [f, if_pos, variableCenteredDensity]
    ring
  have hintegrals : ∏ j : ι,
      ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : ι => ∫ x : ℝ, f j x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Finset.mem_univ i)]
    simp only [f, if_pos, variableCenteredDensity_integral_eq_zero hK hA,
      zero_mul]
  unfold BoundedGaps.Maynard.maynardCubeOf
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi
    (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => Set.Icc (0 : ℝ) 1)]
  calc
    (∫ t : ι → ℝ,
      (t i - variableCoordinateMean K A) *
        Erdos4.VariableMaynard.productDensity K A t
      ∂(Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1))) =
        ∫ t : ι → ℝ, ∏ j, f j (t j)
          ∂(Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      congr 1
      funext t
      exact (hpoint t).symm
    _ = ∏ j : ι,
        ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [MeasureTheory.integral_fintype_prod_eq_prod]
    _ = 0 := hintegrals

theorem integral_twoCenteredCoordinates_mul_productDensity_cube_eq_zero
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j) :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      ((t i - variableCoordinateMean K A) *
        (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t) = 0 := by
  classical
  let f : ι → ℝ → ℝ := fun a x =>
    if a = i then variableCenteredDensity K A x
    else if a = j then variableCenteredDensity K A x
    else Erdos4.VariableMaynard.squareDensity K A x
  have hpoint (t : ι → ℝ) :
      ∏ a, f a (t a) =
        ((t i - variableCoordinateMean K A) *
          (t j - variableCoordinateMean K A)) *
            Erdos4.VariableMaynard.productDensity K A t := by
    unfold Erdos4.VariableMaynard.productDensity
    rw [← Finset.mul_prod_erase Finset.univ (fun a => f a (t a))
      (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun a => Erdos4.VariableMaynard.squareDensity K A (t a))
      (Finset.mem_univ i)]
    have hjmem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i)
      (fun a => f a (t a)) hjmem]
    rw [← Finset.mul_prod_erase (Finset.univ.erase i)
      (fun a => Erdos4.VariableMaynard.squareDensity K A (t a)) hjmem]
    have hrest :
        ∏ a ∈ (Finset.univ.erase i).erase j, f a (t a) =
          ∏ a ∈ (Finset.univ.erase i).erase j,
            Erdos4.VariableMaynard.squareDensity K A (t a) := by
      apply Finset.prod_congr rfl
      intro a ha
      have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
      have haj : a ≠ j := (Finset.mem_erase.mp ha).1
      simp only [f, if_neg hai, if_neg haj]
    rw [hrest]
    simp [f, hij, hij.symm, variableCenteredDensity]
    ring
  have hintegrals : ∏ a : ι,
      ∫ x : ℝ, f a x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun a : ι => ∫ x : ℝ, f a x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Finset.mem_univ i)]
    simp only [f, if_pos, variableCenteredDensity_integral_eq_zero hK hA,
      zero_mul]
  unfold BoundedGaps.Maynard.maynardCubeOf
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi
    (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => Set.Icc (0 : ℝ) 1)]
  calc
    (∫ t : ι → ℝ,
      ((t i - variableCoordinateMean K A) *
        (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t
      ∂(Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1))) =
        ∫ t : ι → ℝ, ∏ a, f a (t a)
          ∂(Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      congr 1
      funext t
      exact (hpoint t).symm
    _ = ∏ a : ι,
        ∫ x : ℝ, f a x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [MeasureTheory.integral_fintype_prod_eq_prod]
    _ = 0 := hintegrals

theorem integral_centeredSquareCoordinate_mul_productDensity_cube_le
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    {ι : Type*} [Fintype ι] (i : ι) :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      (t i - variableCoordinateMean K A) ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t) ≤
      variableSecondMoment K A *
        Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1) := by
  classical
  let f : ι → ℝ → ℝ := fun j x =>
    if j = i then variableCenteredSquareDensity K A x
    else Erdos4.VariableMaynard.squareDensity K A x
  have hpoint (t : ι → ℝ) :
      ∏ j, f j (t j) =
        (t i - variableCoordinateMean K A) ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t := by
    unfold Erdos4.VariableMaynard.productDensity
    rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (t j))
      (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => Erdos4.VariableMaynard.squareDensity K A (t j))
      (Finset.mem_univ i)]
    have hrest :
        ∏ j ∈ Finset.univ.erase i, f j (t j) =
          ∏ j ∈ Finset.univ.erase i,
            Erdos4.VariableMaynard.squareDensity K A (t j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [f, if_neg hji]
    rw [hrest]
    simp only [f, if_pos, variableCenteredSquareDensity]
    ring
  have hintegrals : ∏ j : ι,
      ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        variableCenteredSquareDensity K A x) *
        Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j : ι => ∫ x : ℝ, f j x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (Finset.mem_univ i)]
    simp only [f, if_pos]
    congr 1
    calc
      ∏ j ∈ Finset.univ.erase i,
          ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
          ∏ _j ∈ Finset.univ.erase i,
            Erdos4.VariableMaynard.baseMass K A := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp only [f, if_neg hji]
        exact Erdos4.VariableMaynard.integral_squareDensity_Icc hK hA
      _ = Erdos4.VariableMaynard.baseMass K A ^
          (Fintype.card ι - 1) := by
        simp only [Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hvalue :
      (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
        (t i - variableCoordinateMean K A) ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t) =
      (∫ x : ℝ in Set.Icc (0 : ℝ) 1,
        variableCenteredSquareDensity K A x) *
        Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1) := by
    unfold BoundedGaps.Maynard.maynardCubeOf
    rw [MeasureTheory.volume_pi]
    rw [MeasureTheory.Measure.restrict_pi_pi
      (fun _ : ι => (volume : Measure ℝ))
      (fun _ : ι => Set.Icc (0 : ℝ) 1)]
    calc
      (∫ t : ι → ℝ,
        (t i - variableCoordinateMean K A) ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t
        ∂(Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1))) =
          ∫ t : ι → ℝ, ∏ j, f j (t j)
            ∂(Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        congr 1
        funext t
        exact (hpoint t).symm
      _ = ∏ j : ι,
          ∫ x : ℝ, f j x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        rw [MeasureTheory.integral_fintype_prod_eq_prod]
      _ = _ := hintegrals
  rw [hvalue]
  exact mul_le_mul_of_nonneg_right
    (variableCenteredSquareDensity_integral_le_secondMoment hK hA)
    (pow_nonneg (Erdos4.VariableMaynard.baseMass_pos hK hA).le _)

theorem centeredPair_mul_productDensity_integrableOn_cube
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    {ι : Type*} [Fintype ι] (i j : ι) :
    IntegrableOn (fun t : ι → ℝ =>
      ((t i - variableCoordinateMean K A) *
        (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  let C := 1 + |variableCoordinateMean K A|
  refine BoundedGaps.Maynard.maynard_integrableOn_of_measurable_bounded
    (s := BoundedGaps.Maynard.maynardCubeOf ι)
    (hs := MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc))
    (hsfinite := BoundedGaps.Maynard.maynardCubeOf_measure_lt_top ι)
    (f := fun t : ι → ℝ =>
      ((t i - variableCoordinateMean K A) *
        (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t)
    (((measurable_pi_apply i).sub measurable_const).mul
      ((measurable_pi_apply j).sub measurable_const) |>.mul
      (Finset.measurable_prod _ fun a _ =>
        (Erdos4.VariableMaynard.measurable_squareDensity K A).comp
          (measurable_pi_apply a)))
    (C ^ 2) ?_
  intro t ht
  have hcoord (a : ι) : |t a - variableCoordinateMean K A| ≤ C := by
    calc
      |t a - variableCoordinateMean K A| ≤
          |t a| + |variableCoordinateMean K A| := by
        simpa using abs_sub_le (t a) 0 (variableCoordinateMean K A)
      _ ≤ C := by
        dsimp [C]
        rw [abs_of_nonneg (ht a (Set.mem_univ a)).1]
        simpa [add_comm] using add_le_add_right
          (ht a (Set.mem_univ a)).2 |variableCoordinateMean K A|
  have hprod0 : 0 ≤ Erdos4.VariableMaynard.productDensity K A t :=
    Erdos4.VariableMaynard.productDensity_nonneg K A t
  have hprod1 : Erdos4.VariableMaynard.productDensity K A t ≤ 1 := by
    unfold Erdos4.VariableMaynard.productDensity
    calc
      ∏ a : ι, Erdos4.VariableMaynard.squareDensity K A (t a) ≤
          ∏ _a : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro a ha
          exact Erdos4.VariableMaynard.squareDensity_nonneg K A _
        · intro a ha
          exact Erdos4.VariableMaynard.squareDensity_le_one hA
            (ht a (Set.mem_univ a))
      _ = 1 := Finset.prod_const_one
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg hprod0]
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  calc
    |t i - variableCoordinateMean K A| *
        |t j - variableCoordinateMean K A| *
          Erdos4.VariableMaynard.productDensity K A t ≤
        C * C * Erdos4.VariableMaynard.productDensity K A t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hcoord i) (hcoord j) (abs_nonneg _) hC0) hprod0
    _ ≤ C * C * 1 := by
      exact mul_le_mul_of_nonneg_left hprod1 (mul_nonneg hC0 hC0)
    _ = C ^ 2 := by ring

theorem integral_centeredCoordinateSum_sq_mul_productDensity_cube_le
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (ι : Type*) [Fintype ι] :
    (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
      (∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t) ≤
      (Fintype.card ι : ℝ) * variableSecondMoment K A *
        Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1) := by
  classical
  let z : ι → (ι → ℝ) → ℝ := fun i t =>
    t i - variableCoordinateMean K A
  have hpoint (t : ι → ℝ) :
      (∑ i : ι, z i t) ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t =
        ∑ i : ι, ∑ j : ι,
          (z i t * z j t) *
            Erdos4.VariableMaynard.productDensity K A t := by
    unfold z
    rw [pow_two]
    calc
      ((∑ i : ι, (t i - variableCoordinateMean K A)) *
          ∑ j : ι, (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t =
        (∑ i : ι,
          (t i - variableCoordinateMean K A) *
            ∑ j : ι, (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t := by
        rw [Finset.sum_mul]
      _ = ∑ i : ι,
          ((t i - variableCoordinateMean K A) *
            ∑ j : ι, (t j - variableCoordinateMean K A)) *
              Erdos4.VariableMaynard.productDensity K A t := by
        rw [Finset.sum_mul]
      _ = ∑ i : ι, ∑ j : ι,
          ((t i - variableCoordinateMean K A) *
            (t j - variableCoordinateMean K A)) *
              Erdos4.VariableMaynard.productDensity K A t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.sum_mul]
  have hint (i j : ι) : IntegrableOn (fun t : ι → ℝ =>
      (z i t * z j t) * Erdos4.VariableMaynard.productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
    exact centeredPair_mul_productDensity_integrableOn_cube hA i j
  rw [show (fun t : ι → ℝ =>
      (∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t) =
      (fun t : ι → ℝ => ∑ i : ι, ∑ j : ι,
        (z i t * z j t) *
          Erdos4.VariableMaynard.productDensity K A t) by
    funext t
    exact hpoint t]
  rw [MeasureTheory.integral_finsetSum]
  · have hinner : ∀ i : ι,
        (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
          ∑ j : ι, (z i t * z j t) *
            Erdos4.VariableMaynard.productDensity K A t) =
          ∑ j : ι,
            ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
              (z i t * z j t) *
                Erdos4.VariableMaynard.productDensity K A t := by
          intro i
          rw [MeasureTheory.integral_finsetSum]
          intro j hj
          exact hint i j
    rw [show (∑ i : ι,
        ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
          ∑ j : ι, (z i t * z j t) *
            Erdos4.VariableMaynard.productDensity K A t) =
        ∑ i : ι, ∑ j : ι,
          ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
            (z i t * z j t) *
              Erdos4.VariableMaynard.productDensity K A t by
      apply Finset.sum_congr rfl
      intro i hi
      exact hinner i]
    calc
        ∑ i : ι, ∑ j : ι,
            ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
              (z i t * z j t) *
                Erdos4.VariableMaynard.productDensity K A t =
            ∑ i : ι,
              ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
                (z i t) ^ 2 *
                  Erdos4.VariableMaynard.productDensity K A t := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_eq_single i]
          · congr 1
            funext t
            unfold z
            ring
          · intro j hj hji
            unfold z
            exact integral_twoCenteredCoordinates_mul_productDensity_cube_eq_zero
              hK hA hji.symm
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ i))
        _ ≤ ∑ _i : ι,
            variableSecondMoment K A *
              Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          unfold z
          exact integral_centeredSquareCoordinate_mul_productDensity_cube_le
            hK hA i
        _ = (Fintype.card ι : ℝ) * variableSecondMoment K A *
            Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  · intro i hi
    exact integrable_finsetSum Finset.univ fun j hj => hint i j

theorem centeredCoordinateSum_sq_mul_productDensity_integrableOn_cube
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    (ι : Type*) [Fintype ι] :
    IntegrableOn (fun t : ι → ℝ =>
      (∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t)
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
  let z : ι → (ι → ℝ) → ℝ := fun i t =>
    t i - variableCoordinateMean K A
  have hpoint (t : ι → ℝ) :
      (∑ i : ι, z i t) ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t =
        ∑ i : ι, ∑ j : ι,
          (z i t * z j t) *
            Erdos4.VariableMaynard.productDensity K A t := by
    unfold z
    rw [pow_two]
    calc
      ((∑ i : ι, (t i - variableCoordinateMean K A)) *
          ∑ j : ι, (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t =
        (∑ i : ι,
          (t i - variableCoordinateMean K A) *
            ∑ j : ι, (t j - variableCoordinateMean K A)) *
          Erdos4.VariableMaynard.productDensity K A t := by
        rw [Finset.sum_mul]
      _ = ∑ i : ι,
          ((t i - variableCoordinateMean K A) *
            ∑ j : ι, (t j - variableCoordinateMean K A)) *
              Erdos4.VariableMaynard.productDensity K A t := by
        rw [Finset.sum_mul]
      _ = ∑ i : ι, ∑ j : ι,
          ((t i - variableCoordinateMean K A) *
            (t j - variableCoordinateMean K A)) *
              Erdos4.VariableMaynard.productDensity K A t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.sum_mul]
  rw [show (fun t : ι → ℝ =>
      (∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
        Erdos4.VariableMaynard.productDensity K A t) =
      (fun t : ι → ℝ => ∑ i : ι, ∑ j : ι,
        (z i t * z j t) *
          Erdos4.VariableMaynard.productDensity K A t) by
    funext t
    exact hpoint t]
  exact integrable_finsetSum Finset.univ fun i hi =>
    integrable_finsetSum Finset.univ fun j hj =>
      centeredPair_mul_productDensity_integrableOn_cube hA i j

/-- Chebyshev's inequality for the product density, expressed in the exact
unnormalized form used by the face integrals. -/
theorem badVariableGoodRegion_productDensity_integral_le
    {K : ℕ} {A q : ℝ} (hK : 0 < K) (hA : 0 < A)
    (ι : Type*) [Fintype ι]
    (hmean : (Fintype.card ι : ℝ) * variableCoordinateMean K A < q) :
    (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι,
      Erdos4.VariableMaynard.productDensity K A t) ≤
      (q - (Fintype.card ι : ℝ) * variableCoordinateMean K A)⁻¹ ^ 2 *
        ((Fintype.card ι : ℝ) * variableSecondMoment K A *
          Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1)) := by
  let d := q - (Fintype.card ι : ℝ) * variableCoordinateMean K A
  let V : (ι → ℝ) → ℝ := fun t =>
    (∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
      Erdos4.VariableMaynard.productDensity K A t
  have hd : 0 < d := by dsimp [d]; linarith
  have hdInv : 0 ≤ d⁻¹ ^ 2 := sq_nonneg _
  have hleft : IntegrableOn
      (Erdos4.VariableMaynard.productDensity K A : (ι → ℝ) → ℝ)
      (BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι) :=
    (Erdos4.VariableMaynard.productDensity_integrableOn_cube K A hA ι).mono_set
      Set.sdiff_subset
  have hVfull : IntegrableOn V
      (BoundedGaps.Maynard.maynardCubeOf ι) := by
    dsimp [V]
    exact centeredCoordinateSum_sq_mul_productDensity_integrableOn_cube hA ι
  have hVscaled : IntegrableOn (fun t => d⁻¹ ^ 2 * V t)
      (BoundedGaps.Maynard.maynardCubeOf ι) :=
    hVfull.const_mul (d⁻¹ ^ 2)
  have hright : IntegrableOn (fun t => d⁻¹ ^ 2 * V t)
      (BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι) :=
    hVscaled.mono_set Set.sdiff_subset
  have hmeas : MeasurableSet
      (BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι) :=
    (MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Icc)).diff
      (variableGoodRegion_measurable q ι)
  have hpoint : ∀ t ∈
      BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι,
      Erdos4.VariableMaynard.productDensity K A t ≤ d⁻¹ ^ 2 * V t := by
    intro t ht
    have hsum : q < Erdos4.VariableMaynard.coordinateSum t := by
      by_contra hnot
      exact ht.2 ⟨ht.1, le_of_not_gt hnot⟩
    have hcenter : d < ∑ i : ι,
        (t i - variableCoordinateMean K A) := by
      unfold Erdos4.VariableMaynard.coordinateSum at hsum
      dsimp [d]
      rw [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      linarith
    have hcenter0 : 0 ≤ ∑ i : ι,
        (t i - variableCoordinateMean K A) :=
      (hd.trans hcenter).le
    have hsquare : d ^ 2 ≤
        (∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 :=
      pow_le_pow_left₀ hd.le hcenter.le 2
    have hprod0 : 0 ≤ Erdos4.VariableMaynard.productDensity K A t :=
      Erdos4.VariableMaynard.productDensity_nonneg K A t
    have hmul := mul_le_mul_of_nonneg_right hsquare hprod0
    dsimp [V]
    have hdeq : d⁻¹ ^ 2 *
        ((∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t) =
        d⁻¹ ^ 2 * d ^ 2 *
          Erdos4.VariableMaynard.productDensity K A t +
        d⁻¹ ^ 2 *
          (((∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 - d ^ 2) *
            Erdos4.VariableMaynard.productDensity K A t) := by ring
    have hcancel : d⁻¹ ^ 2 * d ^ 2 = 1 := by
      field_simp [hd.ne']
    calc
      Erdos4.VariableMaynard.productDensity K A t =
          d⁻¹ ^ 2 * d ^ 2 *
            Erdos4.VariableMaynard.productDensity K A t := by
        rw [hcancel, one_mul]
      _ ≤ d⁻¹ ^ 2 *
          ((∑ i : ι, (t i - variableCoordinateMean K A)) ^ 2 *
            Erdos4.VariableMaynard.productDensity K A t) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul hdInv
  calc
    (∫ t : ι → ℝ in
      BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι,
      Erdos4.VariableMaynard.productDensity K A t) ≤
        ∫ t : ι → ℝ in
          BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι,
          d⁻¹ ^ 2 * V t :=
      setIntegral_mono_on hleft hright hmeas hpoint
    _ ≤ ∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
          d⁻¹ ^ 2 * V t := by
      apply setIntegral_mono_set hVscaled
      · exact Filter.Eventually.of_forall fun t =>
          mul_nonneg hdInv (by
            dsimp [V]
            exact mul_nonneg (sq_nonneg _)
              (Erdos4.VariableMaynard.productDensity_nonneg K A t))
      · exact Filter.Eventually.of_forall fun t ht => Set.sdiff_subset ht
    _ = d⁻¹ ^ 2 *
          (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
            V t) := by rw [integral_const_mul]
    _ ≤ d⁻¹ ^ 2 *
        ((Fintype.card ι : ℝ) * variableSecondMoment K A *
          Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (by
          dsimp [V]
          exact integral_centeredCoordinateSum_sq_mul_productDensity_cube_le
            hK hA ι) hdInv
    _ = _ := by rfl

theorem variableGoodRegion_productDensity_integral_gt_of_variance
    {K : ℕ} {A q γ : ℝ} (hK : 0 < K) (hA : 0 < A)
    (ι : Type*) [Fintype ι]
    (hmean : (Fintype.card ι : ℝ) * variableCoordinateMean K A < q)
    (hγ : 0 ≤ γ)
    (hvariance :
      (q - (Fintype.card ι : ℝ) * variableCoordinateMean K A)⁻¹ ^ 2 *
          ((Fintype.card ι : ℝ) * variableSecondMoment K A *
            Erdos4.VariableMaynard.baseMass K A ^ (Fintype.card ι - 1)) <
        (1 - γ) * Erdos4.VariableMaynard.baseMass K A ^ Fintype.card ι) :
    γ * Erdos4.VariableMaynard.baseMass K A ^ Fintype.card ι <
      ∫ t : ι → ℝ in variableGoodRegion q ι,
        Erdos4.VariableMaynard.productDensity K A t := by
  have hbad := badVariableGoodRegion_productDensity_integral_le
    hK hA ι hmean
  have hbad' :
      (∫ t : ι → ℝ in
        BoundedGaps.Maynard.maynardCubeOf ι \ variableGoodRegion q ι,
        Erdos4.VariableMaynard.productDensity K A t) <
      (1 - γ) * Erdos4.VariableMaynard.baseMass K A ^ Fintype.card ι :=
    hbad.trans_lt hvariance
  have hsubset : variableGoodRegion q ι ⊆
      BoundedGaps.Maynard.maynardCubeOf ι :=
    variableGoodRegion_subset_cube q ι
  have hsplit := setIntegral_sdiff (variableGoodRegion_measurable q ι)
    (Erdos4.VariableMaynard.productDensity_integrableOn_cube K A hA ι)
    hsubset
  have htotal := Erdos4.VariableMaynard.integral_product_squareDensity_cube
    hK hA ι
  change (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
    Erdos4.VariableMaynard.productDensity K A t) = _ at htotal
  rw [htotal] at hsplit
  linarith

theorem maynardRatio_variableCandidate_gt_of_concentration
    {K : ℕ} {A q δ γ : ℝ} (hK2 : 2 ≤ K) (hA : 0 < A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hqδ : q + δ ≤ 1)
    (hγ : 0 < γ)
    (hmean : ((K - 1 : ℕ) : ℝ) * variableCoordinateMean K A < q)
    (hvariance :
      (q - ((K - 1 : ℕ) : ℝ) * variableCoordinateMean K A)⁻¹ ^ 2 *
          (((K - 1 : ℕ) : ℝ) * variableSecondMoment K A *
            Erdos4.VariableMaynard.baseMass K A ^ (K - 1 - 1)) <
        (1 - γ) * Erdos4.VariableMaynard.baseMass K A ^ (K - 1)) :
    (K : ℝ) * γ * variableShortMass K A δ ^ 2 /
        Erdos4.VariableMaynard.baseMass K A <
      BoundedGaps.Maynard.maynardRatio K
        (Erdos4.VariableMaynard.candidate K A) := by
  apply maynardRatio_variableCandidate_gt_of_goodFaceMass hK2 hA
    hδ hδ1 hqδ hγ
  intro m
  have hcard : Fintype.card
      (BoundedGaps.Maynard.maynardFaceIndex K m) = K - 1 :=
    Erdos4.VariableMaynard.card_faceIndex m
  have hgood := variableGoodRegion_productDensity_integral_gt_of_variance
    (K := K) (A := A) (q := q) (γ := γ) (by omega) hA
    (BoundedGaps.Maynard.maynardFaceIndex K m) (by
      rw [hcard]
      exact hmean) hγ.le (by
      rw [hcard]
      exact hvariance)
  rw [hcard] at hgood
  exact hgood

end

end MaynardTao

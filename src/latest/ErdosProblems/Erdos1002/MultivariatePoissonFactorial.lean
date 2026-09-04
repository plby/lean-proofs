import ErdosProblems.Erdos1002.PoissonCompat
import ErdosProblems.Erdos1002.PoissonFactorialConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Multivariate Poisson convergence from mixed factorial moments

This file proves the finite-dimensional method of factorial moments used for
vectors of counts.  The proof is entirely discrete.  Rectangular
Bonferroni polynomials give upper and lower bounds for each joint atom;
convergence of their integrals follows by expanding a finite product into
mixed falling-factorial moments.
-/

open Finset Filter MeasureTheory Real Set Topology
open scoped BigOperators ENNReal NNReal Nat Topology

namespace Erdos1002

noncomputable section

namespace MultivariateFactorialMomentMethod

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- A mixed falling-factorial monomial. -/
def mixedDescFactorial (k x : ι → ℕ) : ℝ :=
  ∏ i, (x i).descFactorial (k i)

/-- The mixed falling-factorial moment of a law on a finite vector of counts. -/
def mixedFactorialMoment (μ : ProbabilityMeasure (ι → ℕ)) (k : ι → ℕ) : ℝ :=
  ∫ x, mixedDescFactorial k x ∂(μ : Measure (ι → ℕ))

/-- The zeroth mixed falling-factorial monomial is exactly one.  Keeping
this case explicit avoids applying positive-order tuple parametrizations
to the empty occurrence type. -/
@[simp] theorem mixedDescFactorial_zero (x : ι → ℕ) :
    mixedDescFactorial (fun _i ↦ 0) x = 1 := by
  unfold mixedDescFactorial
  simp

/-- Every probability law has zeroth mixed factorial moment one. -/
@[simp] theorem mixedFactorialMoment_zero
    (μ : ProbabilityMeasure (ι → ℕ)) :
    mixedFactorialMoment μ (fun _i ↦ 0) = 1 := by
  unfold mixedFactorialMoment
  simp

/-- The corresponding zeroth product of Poisson rates is also one. -/
@[simp] theorem prod_pow_zero (r : ι → ℝ) :
    (∏ i, r i ^ (0 : ℕ)) = 1 := by
  simp

/-- Extensional wrapper for a factorial order known coordinatewise to
vanish. -/
theorem mixedFactorialMoment_eq_one_of_forall_eq_zero
    (μ : ProbabilityMeasure (ι → ℕ)) (k : ι → ℕ)
    (hk : ∀ i, k i = 0) :
    mixedFactorialMoment μ k = 1 := by
  have hk0 : k = fun _i ↦ 0 := funext hk
  rw [hk0, mixedFactorialMoment_zero]

/-- The product of the coordinate Poisson probability measures. -/
def independentPoissonProbabilityMeasure (r : ι → ℝ≥0) :
    ProbabilityMeasure (ι → ℕ) :=
  ProbabilityMeasure.pi
    (fun i ↦ FactorialMomentMethod.poissonProbabilityMeasure (r i))

/-- The one-coordinate Bonferroni polynomial for the atom at `j`. -/
private def coordinateBonferroni (j K x : ℕ) : ℝ :=
  (x.choose j : ℝ) *
    ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * ((x - j).choose k : ℝ)

private lemma alternating_sum_choose_eq (y K : ℕ) (hy : 0 < y) :
    (∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (y.choose k : ℝ)) =
      (-1 : ℝ) ^ K * ((y - 1).choose K : ℝ) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := y - 1) (m := K)
  rw [Nat.sub_add_cancel hy] at h
  exact_mod_cast h

private lemma alternating_sum_choose_zero (K : ℕ) :
    (∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * ((0 : ℕ).choose k : ℝ)) = 1 := by
  rw [sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb0)]
    simp
  · simp

private lemma coordinateBonferroni_odd_le_indicator (j q x : ℕ) :
    coordinateBonferroni j (2 * q + 1) x ≤ if x = j then 1 else 0 := by
  rcases lt_trichotomy x j with hx | rfl | hx
  · simp [coordinateBonferroni, Nat.choose_eq_zero_of_lt hx, hx.ne]
  · simp [coordinateBonferroni, alternating_sum_choose_zero]
  · have hy : 0 < x - j := Nat.sub_pos_of_lt hx
    rw [if_neg hx.ne']
    rw [coordinateBonferroni, alternating_sum_choose_eq (x - j) (2 * q + 1) hy]
    simp only [ge_iff_le]
    positivity

private lemma indicator_le_coordinateBonferroni_even (j q x : ℕ) :
    (if x = j then 1 else 0) ≤ coordinateBonferroni j (2 * q) x := by
  rcases lt_trichotomy x j with hx | rfl | hx
  · simp [coordinateBonferroni, Nat.choose_eq_zero_of_lt hx, hx.ne]
  · simp [coordinateBonferroni, alternating_sum_choose_zero]
  · have hy : 0 < x - j := Nat.sub_pos_of_lt hx
    rw [if_neg hx.ne']
    rw [coordinateBonferroni, alternating_sum_choose_eq (x - j) (2 * q) hy]
    simp only [pow_mul, neg_one_sq, one_pow]
    positivity

private lemma coordinateBonferroni_even_nonneg (j q x : ℕ) :
    0 ≤ coordinateBonferroni j (2 * q) x := by
  have hif : 0 ≤ (if x = j then (1 : ℝ) else 0) := by positivity
  exact hif.trans
    (indicator_le_coordinateBonferroni_even j q x)

private lemma coordinateBonferroni_odd_le_even (j q x : ℕ) :
    coordinateBonferroni j (2 * q + 1) x ≤
      coordinateBonferroni j (2 * q) x :=
  (coordinateBonferroni_odd_le_indicator j q x).trans
    (indicator_le_coordinateBonferroni_even j q x)

private lemma choose_mul_choose_sub_eq_descFactorial_div (x j k : ℕ) :
    (x.choose j : ℝ) * ((x - j).choose k : ℝ) =
      (x.descFactorial (j + k) : ℝ) / ((j ! : ℝ) * (k ! : ℝ)) := by
  have hnat :
      (j ! * k !) * (x.choose j * (x - j).choose k) =
        x.descFactorial (j + k) := by
    calc
      (j ! * k !) * (x.choose j * (x - j).choose k) =
          (x - j).descFactorial k * x.descFactorial j := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          Nat.descFactorial_eq_factorial_mul_choose]
        ring
      _ = x.descFactorial (j + k) := by
        simpa using! Nat.descFactorial_mul_descFactorial
          (n := x) (k := j) (m := j + k) (Nat.le_add_right j k)
  have hreal :
      ((j ! : ℝ) * (k ! : ℝ)) *
          ((x.choose j : ℝ) * ((x - j).choose k : ℝ)) =
        (x.descFactorial (j + k) : ℝ) := by
    exact_mod_cast hnat
  field_simp
  nlinarith

private def atomCoefficient (j k : ι → ℕ) : ℝ :=
  ∏ i, ((-1 : ℝ) ^ (k i) / (((j i) ! : ℝ) * ((k i) ! : ℝ)))

private lemma coordinateBonferroni_eq_sum_descFactorial (j K x : ℕ) :
    coordinateBonferroni j K x =
      ∑ k ∈ range (K + 1),
        ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) *
          (x.descFactorial (j + k) : ℝ) := by
  rw [coordinateBonferroni, mul_sum]
  apply sum_congr rfl
  intro k _
  calc
    (x.choose j : ℝ) * ((-1 : ℝ) ^ k * ((x - j).choose k : ℝ)) =
        (-1 : ℝ) ^ k * ((x.choose j : ℝ) * ((x - j).choose k : ℝ)) := by ring
    _ = _ := by
      rw [choose_mul_choose_sub_eq_descFactorial_div]
      ring

/-- A product of coordinate Bonferroni polynomials with possibly different
truncation orders. -/
private def rectangularBonferroni (j K x : ι → ℕ) : ℝ :=
  ∏ i, coordinateBonferroni (j i) (K i) (x i)

private def truncationBox (K : ι → ℕ) : Finset (ι → ℕ) :=
  by
    classical
    exact Fintype.piFinset (fun i ↦ range (K i + 1))

private lemma rectangularBonferroni_eq_sum (j K x : ι → ℕ) :
    rectangularBonferroni j K x =
      ∑ k ∈ truncationBox K,
        atomCoefficient j k * mixedDescFactorial (j + k) x := by
  classical
  simp_rw [rectangularBonferroni, coordinateBonferroni_eq_sum_descFactorial]
  rw [Finset.prod_univ_sum]
  apply sum_congr rfl
  intro k hk
  rw [atomCoefficient, mixedDescFactorial]
  simp only [Pi.add_apply]
  rw [← Finset.prod_mul_distrib]

private lemma integrable_rectangularBonferroni
    (μ : Measure (ι → ℕ)) (j K : ι → ℕ)
    (hInt : ∀ k : ι → ℕ, Integrable (mixedDescFactorial k) μ) :
    Integrable (rectangularBonferroni j K) μ := by
  classical
  have hfun : rectangularBonferroni j K = fun x ↦
      ∑ k ∈ truncationBox K,
        atomCoefficient j k * mixedDescFactorial (j + k) x := by
    funext x
    exact rectangularBonferroni_eq_sum j K x
  rw [hfun]
  apply integrable_finset_sum
  intro k hk
  exact (hInt (j + k)).const_mul _

private lemma integral_rectangularBonferroni
    (μ : Measure (ι → ℕ)) (j K : ι → ℕ)
    (hInt : ∀ k : ι → ℕ, Integrable (mixedDescFactorial k) μ) :
    ∫ x, rectangularBonferroni j K x ∂μ =
      ∑ k ∈ truncationBox K,
        atomCoefficient j k * ∫ x, mixedDescFactorial (j + k) x ∂μ := by
  classical
  have hfun : rectangularBonferroni j K = fun x ↦
      ∑ k ∈ truncationBox K,
        atomCoefficient j k * mixedDescFactorial (j + k) x := by
    funext x
    exact rectangularBonferroni_eq_sum j K x
  rw [hfun, integral_finset_sum]
  · apply sum_congr rfl
    intro k hk
    exact integral_const_mul _ _
  · intro k hk
    exact (hInt (j + k)).const_mul _

private def rectangularLimit (r : ι → ℝ≥0) (j K : ι → ℕ) : ℝ :=
  ∑ k ∈ truncationBox K,
    atomCoefficient j k * ∏ i, (r i : ℝ) ^ (j i + k i)

private lemma tendsto_integral_rectangularBonferroni
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (r : ι → ℝ≥0)
    (j K : ι → ℕ)
    (hInt : ∀ n k, Integrable (mixedDescFactorial k)
      (μs n : Measure (ι → ℕ)))
    (hFac : ∀ k, Tendsto (fun n ↦ mixedFactorialMoment (μs n) k) atTop
      (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto
      (fun n ↦ ∫ x, rectangularBonferroni j K x ∂(μs n : Measure (ι → ℕ)))
      atTop (𝓝 (rectangularLimit r j K)) := by
  classical
  have hfun :
      (fun n ↦ ∫ x, rectangularBonferroni j K x ∂(μs n : Measure (ι → ℕ))) =
        fun n ↦ ∑ k ∈ truncationBox K,
          atomCoefficient j k * mixedFactorialMoment (μs n) (j + k) := by
    funext n
    exact integral_rectangularBonferroni (μs n : Measure (ι → ℕ)) j K (hInt n)
  rw [hfun]
  apply tendsto_finset_sum
  intro k hk
  exact (hFac (j + k)).const_mul _

private def coordinateAtomSeries (r : ℝ≥0) (j k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) * (r : ℝ) ^ (j + k)

private lemma hasSum_coordinateAtomSeries (r : ℝ≥0) (j : ℕ) :
    HasSum (coordinateAtomSeries r j) (poissonPMFReal r j) := by
  let c : ℝ := (r : ℝ) ^ j / (j ! : ℝ)
  have hbase := NormedSpace.expSeries_div_hasSum_exp (-(r : ℝ))
  have hscaled :
      HasSum (fun k : ℕ ↦ c * ((-(r : ℝ)) ^ k / (k ! : ℝ)))
        (c * NormedSpace.exp (-(r : ℝ))) := by
    exact HasSum.mul_left c hbase
  have hterms :
      HasSum (coordinateAtomSeries r j) (c * NormedSpace.exp (-(r : ℝ))) := by
    apply HasSum.congr_fun hscaled
    intro k
    unfold coordinateAtomSeries c
    rw [neg_pow, pow_add]
    field_simp
    ring
  convert! hterms using 1
  unfold c poissonPMFReal
  rw [← Real.exp_eq_exp_ℝ]
  ring

private lemma tendsto_coordinate_even (r : ℝ≥0) (j : ℕ) :
    Tendsto
      (fun q : ℕ ↦ ∑ k ∈ range (2 * q + 1), coordinateAtomSeries r j k)
      atTop (𝓝 (poissonPMFReal r j)) := by
  have hindex : Tendsto (fun q : ℕ ↦ 2 * q + 1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with q hq
    omega
  exact (hasSum_coordinateAtomSeries r j).tendsto_sum_nat.comp hindex

private lemma tendsto_coordinate_odd (r : ℝ≥0) (j : ℕ) :
    Tendsto
      (fun q : ℕ ↦ ∑ k ∈ range (2 * q + 2), coordinateAtomSeries r j k)
      atTop (𝓝 (poissonPMFReal r j)) := by
  have hindex : Tendsto (fun q : ℕ ↦ 2 * q + 2) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with q hq
    omega
  exact (hasSum_coordinateAtomSeries r j).tendsto_sum_nat.comp hindex

private lemma rectangularLimit_eq_prod (r : ι → ℝ≥0) (j K : ι → ℕ) :
    rectangularLimit r j K =
      ∏ i, ∑ k ∈ range (K i + 1), coordinateAtomSeries (r i) (j i) k := by
  classical
  rw [rectangularLimit, Finset.prod_univ_sum]
  apply sum_congr rfl
  intro k hk
  simp only [atomCoefficient, coordinateAtomSeries]
  rw [← Finset.prod_mul_distrib]

private def evenTruncation (q : ℕ) : ι → ℕ := fun _ ↦ 2 * q

private def oddAtTruncation (q : ℕ) (i : ι) : ι → ℕ :=
  by
    classical
    exact Function.update (evenTruncation q) i (2 * q + 1)

private def otherIndices (i : ι) : Finset ι := by
  classical
  exact Finset.univ.erase i

/-- The mass of the atom `j` under the independent Poisson product law. -/
def jointPoissonMass (r : ι → ℝ≥0) (j : ι → ℕ) : ℝ :=
  ∏ i, poissonPMFReal (r i) (j i)

private lemma tendsto_rectangularLimit_even (r : ι → ℝ≥0) (j : ι → ℕ) :
    Tendsto (fun q ↦ rectangularLimit r j (evenTruncation q)) atTop
      (𝓝 (jointPoissonMass r j)) := by
  classical
  simp_rw [rectangularLimit_eq_prod, evenTruncation]
  exact tendsto_finset_prod univ (fun i hi ↦ tendsto_coordinate_even (r i) (j i))

private lemma tendsto_rectangularLimit_oddAt
    (r : ι → ℝ≥0) (j : ι → ℕ) (i : ι) :
    Tendsto (fun q ↦ rectangularLimit r j (oddAtTruncation q i)) atTop
      (𝓝 (jointPoissonMass r j)) := by
  classical
  simp_rw [rectangularLimit_eq_prod]
  apply tendsto_finset_prod univ
  intro h hh
  by_cases hhi : h = i
  · subst h
    simpa [oddAtTruncation] using! tendsto_coordinate_odd (r i) (j i)
  · simpa [oddAtTruncation, hhi, evenTruncation] using!
      tendsto_coordinate_even (r h) (j h)

private def jointAtomIndicator (j x : ι → ℕ) : ℝ :=
  if x = j then 1 else 0

private def upperBonferroni (j : ι → ℕ) (q : ℕ) (x : ι → ℕ) : ℝ :=
  rectangularBonferroni j (evenTruncation q) x

private def oddAtBonferroni
    (j : ι → ℕ) (q : ℕ) (i : ι) (x : ι → ℕ) : ℝ :=
  rectangularBonferroni j (oddAtTruncation q i) x

private def lowerBonferroni (j : ι → ℕ) (q : ℕ) (x : ι → ℕ) : ℝ :=
  upperBonferroni j q x -
    ∑ i, (upperBonferroni j q x - oddAtBonferroni j q i x)

private lemma upperBonferroni_nonneg (j : ι → ℕ) (q : ℕ) (x : ι → ℕ) :
    0 ≤ upperBonferroni j q x := by
  classical
  apply Finset.prod_nonneg
  intro i hi
  exact coordinateBonferroni_even_nonneg (j i) q (x i)

private lemma upperBonferroni_eq_one (j : ι → ℕ) (q : ℕ) :
    upperBonferroni j q j = 1 := by
  classical
  apply Finset.prod_eq_one
  intro i hi
  simp [coordinateBonferroni, evenTruncation, alternating_sum_choose_zero]

private lemma oddAtBonferroni_eq_one (j : ι → ℕ) (q : ℕ) (i : ι) :
    oddAtBonferroni j q i j = 1 := by
  classical
  apply Finset.prod_eq_one
  intro h hh
  simp [oddAtTruncation, coordinateBonferroni, alternating_sum_choose_zero]

private lemma oddAtBonferroni_factor
    (j : ι → ℕ) (q : ℕ) (i : ι) (x : ι → ℕ) :
    oddAtBonferroni j q i x =
      coordinateBonferroni (j i) (2 * q + 1) (x i) *
        ∏ h ∈ otherIndices i,
          coordinateBonferroni (j h) (2 * q) (x h) := by
  classical
  rw [oddAtBonferroni, rectangularBonferroni,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [oddAtTruncation, Function.update_self]
  congr 1
  simp only [otherIndices, Finset.sdiff_singleton_eq_erase]
  apply prod_congr rfl
  intro h hh
  have hne : h ≠ i := by
    simpa [otherIndices] using! ne_of_mem_erase hh
  simp [hne, evenTruncation]

private lemma upperBonferroni_factor
    (j : ι → ℕ) (q : ℕ) (i : ι) (x : ι → ℕ) :
    upperBonferroni j q x =
      coordinateBonferroni (j i) (2 * q) (x i) *
        ∏ h ∈ otherIndices i,
          coordinateBonferroni (j h) (2 * q) (x h) := by
  classical
  rw [upperBonferroni, rectangularBonferroni,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [evenTruncation]
  rw [show (Finset.univ : Finset ι) \ {i} = otherIndices i by
    exact (Finset.sdiff_singleton_eq_erase i Finset.univ).trans rfl]

private lemma oddAtBonferroni_le_upper
    (j : ι → ℕ) (q : ℕ) (i : ι) (x : ι → ℕ) :
    oddAtBonferroni j q i x ≤ upperBonferroni j q x := by
  rw [oddAtBonferroni_factor, upperBonferroni_factor]
  exact mul_le_mul_of_nonneg_right
    (coordinateBonferroni_odd_le_even (j i) q (x i))
    (Finset.prod_nonneg fun h hh ↦
      coordinateBonferroni_even_nonneg (j h) q (x h))

private lemma jointAtomIndicator_le_upperBonferroni
    (j : ι → ℕ) (q : ℕ) (x : ι → ℕ) :
    jointAtomIndicator j x ≤ upperBonferroni j q x := by
  by_cases hx : x = j
  · subst x
    simp [jointAtomIndicator, upperBonferroni_eq_one]
  · simp [jointAtomIndicator, hx, upperBonferroni_nonneg]

private lemma lowerBonferroni_le_jointAtomIndicator
    (j : ι → ℕ) (q : ℕ) (x : ι → ℕ) :
    lowerBonferroni j q x ≤ jointAtomIndicator j x := by
  classical
  by_cases hx : x = j
  · subst x
    simp [lowerBonferroni, jointAtomIndicator, upperBonferroni_eq_one,
      oddAtBonferroni_eq_one]
  · have hex : ∃ i, x i ≠ j i := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    obtain ⟨i, hi⟩ := hex
    have hodd_nonpos : oddAtBonferroni j q i x ≤ 0 := by
      rw [oddAtBonferroni_factor]
      have hcoord : coordinateBonferroni (j i) (2 * q + 1) (x i) ≤ 0 := by
        simpa [hi] using! coordinateBonferroni_odd_le_indicator (j i) q (x i)
      exact mul_nonpos_of_nonpos_of_nonneg hcoord
        (Finset.prod_nonneg fun h hh ↦
          coordinateBonferroni_even_nonneg (j h) q (x h))
    have hcorrection :
        upperBonferroni j q x - oddAtBonferroni j q i x ≤
          ∑ h, (upperBonferroni j q x - oddAtBonferroni j q h x) := by
      simpa using!
        (Finset.single_le_sum
          (s := (Finset.univ : Finset ι))
          (f := fun h ↦ upperBonferroni j q x - oddAtBonferroni j q h x)
          (fun h hh ↦ sub_nonneg.mpr (oddAtBonferroni_le_upper j q h x))
          (Finset.mem_univ i))
    rw [jointAtomIndicator, if_neg hx, lowerBonferroni]
    linarith

private def upperLimit (r : ι → ℝ≥0) (j : ι → ℕ) (q : ℕ) : ℝ :=
  rectangularLimit r j (evenTruncation q)

private def oddAtLimit (r : ι → ℝ≥0) (j : ι → ℕ) (q : ℕ) (i : ι) : ℝ :=
  rectangularLimit r j (oddAtTruncation q i)

private def lowerLimit (r : ι → ℝ≥0) (j : ι → ℕ) (q : ℕ) : ℝ :=
  upperLimit r j q - ∑ i, (upperLimit r j q - oddAtLimit r j q i)

private lemma tendsto_upperLimit (r : ι → ℝ≥0) (j : ι → ℕ) :
    Tendsto (upperLimit r j) atTop (𝓝 (jointPoissonMass r j)) := by
  simpa [upperLimit] using! tendsto_rectangularLimit_even r j

private lemma tendsto_oddAtLimit
    (r : ι → ℝ≥0) (j : ι → ℕ) (i : ι) :
    Tendsto (fun q ↦ oddAtLimit r j q i) atTop (𝓝 (jointPoissonMass r j)) := by
  simpa [oddAtLimit] using! tendsto_rectangularLimit_oddAt r j i

private lemma tendsto_lowerLimit (r : ι → ℝ≥0) (j : ι → ℕ) :
    Tendsto (lowerLimit r j) atTop (𝓝 (jointPoissonMass r j)) := by
  have hu := tendsto_upperLimit r j
  have hc : Tendsto
      (fun q ↦ ∑ i, (upperLimit r j q - oddAtLimit r j q i)) atTop
      (𝓝 (∑ _i : ι, (jointPoissonMass r j - jointPoissonMass r j))) := by
    apply tendsto_finset_sum univ
    intro i hi
    exact hu.sub (tendsto_oddAtLimit r j i)
  simpa only [lowerLimit, sub_self, sum_const_zero, sub_zero] using! hu.sub hc

private lemma integrable_jointAtomIndicator
    (μ : Measure (ι → ℕ)) [IsFiniteMeasure μ] (j : ι → ℕ) :
    Integrable (jointAtomIndicator j) μ := by
  have hfun : jointAtomIndicator j =
      ({j} : Set (ι → ℕ)).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases h : x = j
    · subst x
      simp [jointAtomIndicator]
    · simp [jointAtomIndicator, h]
  rw [hfun]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_singleton j)

private lemma integral_jointAtomIndicator (μ : Measure (ι → ℕ)) (j : ι → ℕ) :
    ∫ x, jointAtomIndicator j x ∂μ = μ.real {j} := by
  have hfun : jointAtomIndicator j =
      ({j} : Set (ι → ℕ)).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases h : x = j
    · subst x
      simp [jointAtomIndicator]
    · simp [jointAtomIndicator, h]
  rw [hfun]
  simpa only [Pi.one_apply] using!
    (integral_indicator_one (μ := μ) (measurableSet_singleton j))

private lemma integrable_upperBonferroni
    (μ : Measure (ι → ℕ)) (j : ι → ℕ) (q : ℕ)
    (hInt : ∀ k : ι → ℕ, Integrable (mixedDescFactorial k) μ) :
    Integrable (upperBonferroni j q) μ := by
  exact integrable_rectangularBonferroni μ j (evenTruncation q) hInt

private lemma integrable_oddAtBonferroni
    (μ : Measure (ι → ℕ)) (j : ι → ℕ) (q : ℕ) (i : ι)
    (hInt : ∀ k : ι → ℕ, Integrable (mixedDescFactorial k) μ) :
    Integrable (oddAtBonferroni j q i) μ := by
  exact integrable_rectangularBonferroni μ j (oddAtTruncation q i) hInt

private lemma integrable_lowerBonferroni
    (μ : Measure (ι → ℕ)) (j : ι → ℕ) (q : ℕ)
    (hInt : ∀ k : ι → ℕ, Integrable (mixedDescFactorial k) μ) :
    Integrable (lowerBonferroni j q) μ := by
  apply (integrable_upperBonferroni μ j q hInt).sub
  apply integrable_finset_sum
  intro i hi
  exact (integrable_upperBonferroni μ j q hInt).sub
    (integrable_oddAtBonferroni μ j q i hInt)

private lemma integral_lowerBonferroni
    (μ : Measure (ι → ℕ)) (j : ι → ℕ) (q : ℕ)
    (hInt : ∀ k : ι → ℕ, Integrable (mixedDescFactorial k) μ) :
    ∫ x, lowerBonferroni j q x ∂μ =
      (∫ x, upperBonferroni j q x ∂μ) -
        ∑ i, ((∫ x, upperBonferroni j q x ∂μ) -
          ∫ x, oddAtBonferroni j q i x ∂μ) := by
  change (∫ x, upperBonferroni j q x -
      ∑ i, (upperBonferroni j q x - oddAtBonferroni j q i x) ∂μ) = _
  rw [integral_sub]
  · rw [integral_finset_sum]
    · apply congrArg ((∫ x, upperBonferroni j q x ∂μ) - ·)
      apply sum_congr rfl
      intro i hi
      rw [integral_sub]
      · exact integrable_upperBonferroni μ j q hInt
      · exact integrable_oddAtBonferroni μ j q i hInt
    · intro i hi
      exact (integrable_upperBonferroni μ j q hInt).sub
        (integrable_oddAtBonferroni μ j q i hInt)
  · exact integrable_upperBonferroni μ j q hInt
  · apply integrable_finset_sum
    intro i hi
    exact (integrable_upperBonferroni μ j q hInt).sub
      (integrable_oddAtBonferroni μ j q i hInt)

private lemma tendsto_integral_upperBonferroni
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (r : ι → ℝ≥0)
    (j : ι → ℕ) (q : ℕ)
    (hInt : ∀ n k, Integrable (mixedDescFactorial k)
      (μs n : Measure (ι → ℕ)))
    (hFac : ∀ k, Tendsto (fun n ↦ mixedFactorialMoment (μs n) k) atTop
      (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto (fun n ↦ ∫ x, upperBonferroni j q x ∂(μs n : Measure (ι → ℕ)))
      atTop (𝓝 (upperLimit r j q)) := by
  exact tendsto_integral_rectangularBonferroni μs r j (evenTruncation q) hInt hFac

private lemma tendsto_integral_oddAtBonferroni
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (r : ι → ℝ≥0)
    (j : ι → ℕ) (q : ℕ) (i : ι)
    (hInt : ∀ n k, Integrable (mixedDescFactorial k)
      (μs n : Measure (ι → ℕ)))
    (hFac : ∀ k, Tendsto (fun n ↦ mixedFactorialMoment (μs n) k) atTop
      (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto (fun n ↦ ∫ x, oddAtBonferroni j q i x ∂(μs n : Measure (ι → ℕ)))
      atTop (𝓝 (oddAtLimit r j q i)) := by
  exact tendsto_integral_rectangularBonferroni μs r j (oddAtTruncation q i) hInt hFac

private lemma tendsto_integral_lowerBonferroni
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (r : ι → ℝ≥0)
    (j : ι → ℕ) (q : ℕ)
    (hInt : ∀ n k, Integrable (mixedDescFactorial k)
      (μs n : Measure (ι → ℕ)))
    (hFac : ∀ k, Tendsto (fun n ↦ mixedFactorialMoment (μs n) k) atTop
      (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto (fun n ↦ ∫ x, lowerBonferroni j q x ∂(μs n : Measure (ι → ℕ)))
      atTop (𝓝 (lowerLimit r j q)) := by
  have hu := tendsto_integral_upperBonferroni μs r j q hInt hFac
  have hc : Tendsto
      (fun n ↦ ∑ i,
        ((∫ x, upperBonferroni j q x ∂(μs n : Measure (ι → ℕ))) -
          ∫ x, oddAtBonferroni j q i x ∂(μs n : Measure (ι → ℕ))))
      atTop (𝓝 (∑ i, (upperLimit r j q - oddAtLimit r j q i))) := by
    apply tendsto_finset_sum univ
    intro i hi
    exact hu.sub (tendsto_integral_oddAtBonferroni μs r j q i hInt hFac)
  have hfun :
      (fun n ↦ ∫ x, lowerBonferroni j q x ∂(μs n : Measure (ι → ℕ))) =
        fun n ↦ (∫ x, upperBonferroni j q x ∂(μs n : Measure (ι → ℕ))) -
          ∑ i, ((∫ x, upperBonferroni j q x ∂(μs n : Measure (ι → ℕ))) -
            ∫ x, oddAtBonferroni j q i x ∂(μs n : Measure (ι → ℕ))) := by
    funext n
    exact integral_lowerBonferroni (μs n : Measure (ι → ℕ)) j q (hInt n)
  rw [hfun]
  exact hu.sub hc

/-- Convergence of every mixed falling-factorial moment forces convergence
of every joint atom to the corresponding independent-Poisson mass. -/
theorem tendsto_real_singleton_of_mixedFactorialMoments
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (r : ι → ℝ≥0)
    (hInt : ∀ n k, Integrable (mixedDescFactorial k)
      (μs n : Measure (ι → ℕ)))
    (hFac : ∀ k, Tendsto (fun n ↦ mixedFactorialMoment (μs n) k) atTop
      (𝓝 (∏ i, (r i : ℝ) ^ (k i))))
    (j : ι → ℕ) :
    Tendsto (fun n ↦ (μs n : Measure (ι → ℕ)).real {j}) atTop
      (𝓝 (jointPoissonMass r j)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨qLower, hqLower⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_lowerLimit r j)) (ε / 4) hε4
  obtain ⟨qUpper, hqUpper⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_upperLimit r j)) (ε / 4) hε4
  let q := max qLower qUpper
  have hLowerLimit :
      dist (lowerLimit r j q) (jointPoissonMass r j) < ε / 4 :=
    hqLower q (le_max_left _ _)
  have hUpperLimit :
      dist (upperLimit r j q) (jointPoissonMass r j) < ε / 4 :=
    hqUpper q (le_max_right _ _)
  obtain ⟨nLower, hnLower⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_integral_lowerBonferroni μs r j q hInt hFac)) (ε / 4) hε4
  obtain ⟨nUpper, hnUpper⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_integral_upperBonferroni μs r j q hInt hFac)) (ε / 4) hε4
  refine ⟨max nLower nUpper, fun n hn ↦ ?_⟩
  have hnL := hnLower n (le_trans (le_max_left _ _) hn)
  have hnU := hnUpper n (le_trans (le_max_right _ _) hn)
  have hLower :
      (∫ x, lowerBonferroni j q x ∂(μs n : Measure (ι → ℕ))) ≤
        (μs n : Measure (ι → ℕ)).real {j} := by
    rw [← integral_jointAtomIndicator]
    exact integral_mono
      (integrable_lowerBonferroni (μs n : Measure (ι → ℕ)) j q (hInt n))
      (integrable_jointAtomIndicator (μs n : Measure (ι → ℕ)) j)
      (lowerBonferroni_le_jointAtomIndicator j q)
  have hUpper :
      (μs n : Measure (ι → ℕ)).real {j} ≤
        ∫ x, upperBonferroni j q x ∂(μs n : Measure (ι → ℕ)) := by
    rw [← integral_jointAtomIndicator]
    exact integral_mono
      (integrable_jointAtomIndicator (μs n : Measure (ι → ℕ)) j)
      (integrable_upperBonferroni (μs n : Measure (ι → ℕ)) j q (hInt n))
      (jointAtomIndicator_le_upperBonferroni j q)
  rw [Real.dist_eq] at hLowerLimit hUpperLimit hnL hnU ⊢
  rw [abs_lt] at hLowerLimit hUpperLimit hnL hnU ⊢
  constructor <;> linarith

private def finiteCountBox (m : ℕ) : Finset (ι → ℕ) := by
  classical
  exact Fintype.piFinset (fun _ ↦ range m)

/-- On a finite product of discrete count spaces, convergence of all joint
singleton masses implies weak convergence. -/
theorem tendsto_probabilityMeasure_pi_nat_of_real_singletons
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (μ : ProbabilityMeasure (ι → ℕ))
    (hPoint : ∀ j : ι → ℕ,
      Tendsto (fun n ↦ (μs n : Measure (ι → ℕ)).real {j}) atTop
        (𝓝 ((μ : Measure (ι → ℕ)).real {j}))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hFinReal (s : Finset (ι → ℕ)) :
      Tendsto (fun n ↦ (μs n : Measure (ι → ℕ)).real (s : Set (ι → ℕ))) atTop
        (𝓝 ((μ : Measure (ι → ℕ)).real (s : Set (ι → ℕ)))) := by
    simpa only [sum_measureReal_singleton] using!
      tendsto_finset_sum s (fun j hj ↦ hPoint j)
  have hFin (s : Finset (ι → ℕ)) :
      Tendsto (fun n ↦ (μs n : Measure (ι → ℕ)) (s : Set (ι → ℕ))) atTop
        (𝓝 ((μ : Measure (ι → ℕ)) (s : Set (ι → ℕ)))) := by
    apply (ENNReal.tendsto_toReal_iff
      (fun n ↦ measure_ne_top (μs n : Measure (ι → ℕ)) (s : Set (ι → ℕ)))
      (measure_ne_top (μ : Measure (ι → ℕ)) (s : Set (ι → ℕ)))).mp
    simpa only [measureReal_def] using! hFinReal s
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro G hG
  classical
  let t : ℕ → Finset (ι → ℕ) :=
    fun m ↦ (finiteCountBox m).filter (fun x ↦ x ∈ G)
  have htmono : Monotone (fun m ↦ (t m : Set (ι → ℕ))) := by
    intro a b hab x hx
    change x ∈ t a at hx
    change x ∈ t b
    rcases Finset.mem_filter.mp hx with ⟨hxa, hxG⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hxG⟩
    rw [finiteCountBox, Fintype.mem_piFinset] at hxa ⊢
    intro i
    exact Finset.mem_range.mpr
      ((Finset.mem_range.mp (hxa i)).trans_le hab)
  have htunion : (⋃ m, (t m : Set (ι → ℕ))) = G := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
      change x ∈ t m at hxm
      exact (Finset.mem_filter.mp hxm).2
    · intro hxG
      let m : ℕ := (∑ i, x i) + 1
      apply Set.mem_iUnion.mpr
      refine ⟨m, ?_⟩
      change x ∈ t m
      apply Finset.mem_filter.mpr
      refine ⟨?_, hxG⟩
      rw [finiteCountBox, Fintype.mem_piFinset]
      intro i
      apply Finset.mem_range.mpr
      have hle : x i ≤ ∑ h, x h := by
        simpa using!
          (Finset.single_le_sum
            (s := (Finset.univ : Finset ι)) (f := x)
            (fun h hh ↦ Nat.zero_le (x h)) (Finset.mem_univ i))
      exact hle.trans_lt (Nat.lt_succ_self _)
  have hfinite_le (m : ℕ) :
      (μ : Measure (ι → ℕ)) (t m : Set (ι → ℕ)) ≤
        liminf (fun n ↦ (μs n : Measure (ι → ℕ)) G) atTop := by
    rw [← (hFin (t m)).liminf_eq]
    apply Filter.liminf_le_liminf
      (Eventually.of_forall fun n ↦ measure_mono (by
        intro x hx
        change x ∈ t m at hx
        exact (Finset.mem_filter.mp hx).2))
  have hcont :
      Tendsto (fun m ↦ (μ : Measure (ι → ℕ)) (t m : Set (ι → ℕ))) atTop
        (𝓝 ((μ : Measure (ι → ℕ)) G)) := by
    simpa only [Function.comp_apply, htunion] using!
      (tendsto_measure_iUnion_atTop (μ := (μ : Measure (ι → ℕ))) htmono)
  exact le_of_tendsto hcont (Eventually.of_forall hfinite_le)

omit [Fintype ι] in
private lemma singleton_eq_pi_singletons (j : ι → ℕ) :
    ({j} : Set (ι → ℕ)) = Set.pi Set.univ (fun i ↦ ({j i} : Set ℕ)) := by
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_const]
  exact ⟨fun h i ↦ congrFun h i, fun h ↦ funext h⟩

private lemma independentPoisson_real_singleton
    (r : ι → ℝ≥0) (j : ι → ℕ) :
    (independentPoissonProbabilityMeasure r : Measure (ι → ℕ)).real {j} =
      jointPoissonMass r j := by
  rw [measureReal_def, singleton_eq_pi_singletons, independentPoissonProbabilityMeasure,
    ProbabilityMeasure.toMeasure_pi, Measure.pi_pi, ENNReal.toReal_prod]
  apply prod_congr rfl
  intro i hi
  rw [FactorialMomentMethod.poissonProbabilityMeasure]
  change (poissonMeasure (r i) {j i}).toReal = _
  rw [poissonMeasure_eq_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (j i))]
  change (ENNReal.ofReal (poissonPMFReal (r i) (j i))).toReal = _
  exact ENNReal.toReal_ofReal poissonPMFReal_nonneg

/-- **Finite-dimensional method of factorial moments.**

For every mixed order we assume genuine integrability and convergence of the
mixed falling-factorial moment.  The vector laws then converge weakly to the
finite product of independent Poisson laws with intensities `r i`.  No
uniform exponential-moment hypothesis is added. -/
theorem tendsto_independentPoisson_of_mixedFactorialMoments
    (μs : ℕ → ProbabilityMeasure (ι → ℕ)) (r : ι → ℝ≥0)
    (hInt : ∀ n k, Integrable (mixedDescFactorial k)
      (μs n : Measure (ι → ℕ)))
    (hFac : ∀ k, Tendsto (fun n ↦ mixedFactorialMoment (μs n) k) atTop
      (𝓝 (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto μs atTop (𝓝 (independentPoissonProbabilityMeasure r)) := by
  apply tendsto_probabilityMeasure_pi_nat_of_real_singletons
  intro j
  simpa only [independentPoisson_real_singleton] using!
    tendsto_real_singleton_of_mixedFactorialMoments μs r hInt hFac j

end MultivariateFactorialMomentMethod

end

end Erdos1002

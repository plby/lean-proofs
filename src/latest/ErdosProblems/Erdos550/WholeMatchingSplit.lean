import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Splitting whole regular-matching edges

For the direct off--Turán argument the two head classes are assigned disjoint
*whole edges* of the regular matching.  This avoids regularity inheritance for
random vertex slices.  The probabilistic choice below is a product of
Bernoulli coordinates; its two weighted sums have variance bounded by the sum
of the squared edge weights.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Erdos550

open Classical

section Coordinates

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def matchingBernoulliMeasure
    (p : NNReal) (hp : p ≤ 1) : Measure (κ → Bool) :=
  Measure.pi fun _ => (PMF.bernoulli p hp).toMeasure

noncomputable instance matchingBernoulliMeasure.instIsProbabilityMeasure
    (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (matchingBernoulliMeasure (κ := κ) p hp) := by
  unfold matchingBernoulliMeasure
  infer_instance

noncomputable def matchingCoordinate
    (w : κ → ℝ) (i : κ) : (κ → Bool) → ℝ :=
  fun ω => if ω i then w i else 0

noncomputable def matchingWeightSum
    (w : κ → ℝ) : (κ → Bool) → ℝ :=
  fun ω => ∑ i, matchingCoordinate w i ω

lemma matchingWeightSum_eq_sum (w : κ → ℝ) :
    matchingWeightSum w = ∑ i, matchingCoordinate w i := by
  funext ω
  simp [matchingWeightSum]

lemma integral_matchingCoordinate
    (p : NNReal) (hp : p ≤ 1) (w : κ → ℝ) (i : κ) :
    ∫ ω, matchingCoordinate w i ω ∂matchingBernoulliMeasure p hp =
      p.toReal * w i := by
  let μ : κ → Measure Bool :=
    fun _ => (PMF.bernoulli p hp).toMeasure
  have h := integral_comp_eval (μ := μ) (i := i)
    (f := fun b : Bool => if b then w i else 0) (by fun_prop)
  rw [PMF.integral_eq_sum] at h
  simpa [matchingBernoulliMeasure, matchingCoordinate, μ,
    PMF.bernoulli_apply] using! h

lemma matchingCoordinate_memLp_two
    (p : NNReal) (hp : p ≤ 1)
    (w : κ → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwM : ∀ i, w i ≤ M) (i : κ) :
    MemLp (matchingCoordinate w i) 2
      (matchingBernoulliMeasure p hp) := by
  have hM0 : 0 ≤ M := (hw0 i).trans (hwM i)
  apply memLp_of_bounded
    (a := 0) (b := M) (p := 2)
  · filter_upwards [] with ω
    simp only [matchingCoordinate]
    split <;> simp_all
  · fun_prop

lemma matchingWeightSum_memLp_two
    (p : NNReal) (hp : p ≤ 1)
    (w : κ → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwM : ∀ i, w i ≤ M) :
    MemLp (matchingWeightSum w) 2
      (matchingBernoulliMeasure p hp) := by
  rw [matchingWeightSum_eq_sum]
  apply memLp_finset_sum' Finset.univ
  intro i hi
  exact matchingCoordinate_memLp_two p hp w M hw0 hwM i

lemma integral_matchingWeightSum
    (p : NNReal) (hp : p ≤ 1)
    (w : κ → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwM : ∀ i, w i ≤ M) :
    ∫ ω, matchingWeightSum w ω ∂matchingBernoulliMeasure p hp =
      p.toReal * ∑ i, w i := by
  change (∫ ω, ∑ i, matchingCoordinate w i ω
      ∂matchingBernoulliMeasure p hp) =
    p.toReal * ∑ i, w i
  rw [integral_finset_sum]
  · simp_rw [integral_matchingCoordinate p hp w]
    rw [← Finset.mul_sum]
  · intro i hi
    exact (matchingCoordinate_memLp_two p hp w M hw0 hwM i).integrable
      (by norm_num)

lemma variance_matchingWeightSum_le
    (p : NNReal) (hp : p ≤ 1)
    (w : κ → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwM : ∀ i, w i ≤ M) :
    variance (matchingWeightSum w)
        (matchingBernoulliMeasure p hp) ≤
      (Fintype.card κ : ℝ) * (M / 2) ^ 2 := by
  let μ : κ → Measure Bool :=
    fun _ => (PMF.bernoulli p hp).toMeasure
  have hind :
      iIndepFun (fun i ω => matchingCoordinate w i ω)
        (matchingBernoulliMeasure p hp) := by
    simpa [matchingBernoulliMeasure, matchingCoordinate, μ] using!
      (iIndepFun_pi (μ := μ)
        (X := fun (i : κ) (b : Bool) => if b then w i else 0)
        (fun _ => (measurable_of_finite _).aemeasurable))
  have hmem : ∀ i ∈ (Finset.univ : Finset κ),
      MemLp (matchingCoordinate w i) 2
        (matchingBernoulliMeasure p hp) :=
    fun i _ => matchingCoordinate_memLp_two p hp w M hw0 hwM i
  have hpair : Set.Pairwise (↑(Finset.univ : Finset κ))
      (fun i j => matchingCoordinate w i ⟂ᵢ[
        matchingBernoulliMeasure p hp] matchingCoordinate w j) := by
    intro i hi j hj hij
    exact hind.indepFun hij
  rw [matchingWeightSum_eq_sum,
    IndepFun.variance_sum hmem hpair]
  calc
    (∑ i ∈ Finset.univ,
        variance (matchingCoordinate w i)
          (matchingBernoulliMeasure p hp))
        ≤ ∑ _i ∈ Finset.univ, (M / 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hM0 : 0 ≤ M := (hw0 i).trans (hwM i)
          have hbound : ∀ᵐ ω ∂matchingBernoulliMeasure p hp,
              matchingCoordinate w i ω ∈ Set.Icc 0 M := by
            filter_upwards [] with ω
            simp only [matchingCoordinate]
            split <;> simp_all
          have hvar := variance_le_sq_of_bounded
            (μ := matchingBernoulliMeasure p hp)
            (X := matchingCoordinate w i) hbound
            (hmem i hi).aemeasurable
          simpa only [sub_zero] using! hvar
    _ = (Fintype.card κ : ℝ) * (M / 2) ^ 2 := by
      simp

/-- Simultaneously split two bounded edge-weight systems by assigning each
matching edge wholly to one side.  The first side receives approximately the
`p`-fraction of its total weight, while the complementary edge family receives
approximately the `(1-p)`-fraction of the second total. -/
theorem exists_whole_matching_split
    (p : NNReal) (hp : p ≤ 1)
    (wX wY : κ → ℝ) (M t : ℝ)
    (hX0 : ∀ i, 0 ≤ wX i) (hXM : ∀ i, wX i ≤ M)
    (hY0 : ∀ i, 0 ≤ wY i) (hYM : ∀ i, wY i ≤ M)
    (ht : 0 < t)
    (hroom : (Fintype.card κ : ℝ) * M ^ 2 / 2 < t ^ 2) :
    ∃ K : Finset κ,
      |(∑ i ∈ K, wX i) - p.toReal * ∑ i, wX i| < t ∧
      |(∑ i ∈ Finset.univ \ K, wY i) -
          (1 - p.toReal) * ∑ i, wY i| < t := by
  let μ := matchingBernoulliMeasure (κ := κ) p hp
  let X := matchingWeightSum wX
  let Y := matchingWeightSum wY
  have hXmem : MemLp X 2 μ := by
    exact matchingWeightSum_memLp_two p hp wX M hX0 hXM
  have hYmem : MemLp Y 2 μ := by
    exact matchingWeightSum_memLp_two p hp wY M hY0 hYM
  have hEX : μ[X] = p.toReal * ∑ i, wX i := by
    exact integral_matchingWeightSum p hp wX M hX0 hXM
  have hEY : μ[Y] = p.toReal * ∑ i, wY i := by
    exact integral_matchingWeightSum p hp wY M hY0 hYM
  let Z : (κ → Bool) → ℝ := fun ω =>
    (X ω - μ[X]) ^ 2 + (Y ω - μ[Y]) ^ 2
  have hZint : Integrable Z μ := by
    apply Integrable.add
    · exact (hXmem.sub (memLp_const _)).integrable_sq
    · exact (hYmem.sub (memLp_const _)).integrable_sq
  obtain ⟨ω, hω⟩ := exists_le_integral hZint
  have hInt :
      ∫ z, Z z ∂μ =
        variance X μ + variance Y μ := by
    rw [show (∫ z, Z z ∂μ) =
        (∫ z, (X z - μ[X]) ^ 2 ∂μ) +
          ∫ z, (Y z - μ[Y]) ^ 2 ∂μ by
      apply integral_add
      · exact (hXmem.sub (memLp_const _)).integrable_sq
      · exact (hYmem.sub (memLp_const _)).integrable_sq]
    rw [← variance_eq_integral hXmem.aemeasurable,
      ← variance_eq_integral hYmem.aemeasurable]
  have hVarX := variance_matchingWeightSum_le
    p hp wX M hX0 hXM
  have hVarY := variance_matchingWeightSum_le
    p hp wY M hY0 hYM
  have hZlt : Z ω < t ^ 2 := by
    rw [hInt] at hω
    have hsum :
        variance X μ + variance Y μ ≤
          (Fintype.card κ : ℝ) * M ^ 2 / 2 := by
      dsimp only [X, Y, μ] at hVarX hVarY ⊢
      nlinarith [sq_nonneg (M / 2)]
    exact lt_of_le_of_lt (hω.trans hsum) hroom
  let K : Finset κ := Finset.univ.filter fun i => ω i
  have hsumX :
      X ω = ∑ i ∈ K, wX i := by
    change (∑ i, if ω i then wX i else 0) =
      ∑ i ∈ K, wX i
    simp [K, Finset.sum_filter]
  have hsumY :
      Y ω = ∑ i ∈ K, wY i := by
    change (∑ i, if ω i then wY i else 0) =
      ∑ i ∈ K, wY i
    simp [K, Finset.sum_filter]
  have hdevX : |X ω - μ[X]| < t := by
    have hs : (X ω - μ[X]) ^ 2 < t ^ 2 := by
      nlinarith [sq_nonneg (Y ω - μ[Y])]
    nlinarith [sq_nonneg (X ω - μ[X]), abs_nonneg (X ω - μ[X]),
      sq_abs (X ω - μ[X])]
  have hdevY : |Y ω - μ[Y]| < t := by
    have hs : (Y ω - μ[Y]) ^ 2 < t ^ 2 := by
      nlinarith [sq_nonneg (X ω - μ[X])]
    nlinarith [sq_nonneg (Y ω - μ[Y]), abs_nonneg (Y ω - μ[Y]),
      sq_abs (Y ω - μ[Y])]
  refine ⟨K, ?_, ?_⟩
  · simpa [hsumX, hEX] using! hdevX
  · have htotal :
        ∑ i ∈ Finset.univ \ K, wY i =
          (∑ i, wY i) - ∑ i ∈ K, wY i := by
      rw [← Finset.sum_sdiff (Finset.subset_univ K)]
      ring
    rw [htotal, ← hsumY]
    have heq :
        (∑ i, wY i) - Y ω -
            (1 - p.toReal) * ∑ i, wY i =
          -(Y ω - p.toReal * ∑ i, wY i) := by ring
    rw [heq, abs_neg]
    simpa [hEY] using! hdevY

end Coordinates

end Erdos550

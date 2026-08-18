import ErdosProblems.Erdos140.BohrEstimates
import ErdosProblems.Erdos140.LpOrthogonality

/-!
# Convolution versus autocorrelation on a narrow Bohr weight

This file assembles the two ingredients in the Kelley--Meka/Bloom--Sisask
convolution comparison: factor-two Bohr majorization and phase removal at an
even exponent.  The small-set hypothesis is quantitative: both smoothing
sets lie in `B_(eta)`, and coarse regularity is assumed on the full fourfold
shell `B_(rho ± 4 eta)`.
-/

open Finset Fintype Function
open scoped BigOperators NNReal

namespace Erdos140
namespace ConvolutionComparison

noncomputable section

open FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The spectrally nonnegative comparison weight
`(μ_C ○ μ_C) * (μ_D ○ μ_D)`, in counting-measure
normalization. -/
def comparisonWeight (C D : Finset G) : G → ℝ :=
  normalizedConvolution
    (normalizedDifferenceConvolution (normalizedIndicator C) (normalizedIndicator C))
    (normalizedDifferenceConvolution (normalizedIndicator D) (normalizedIndicator D))

theorem comparisonWeight_nonneg (C D : Finset G) (x : G) :
    0 ≤ comparisonWeight C D x := by
  apply normalizedConvolution_nonneg
  · exact normalizedDifferenceConvolution_nonneg
      (normalizedIndicator_nonneg C) (normalizedIndicator_nonneg C)
  · exact normalizedDifferenceConvolution_nonneg
      (normalizedIndicator_nonneg D) (normalizedIndicator_nonneg D)

theorem sum_comparisonWeight {C D : Finset G}
    (hC : C.Nonempty) (hD : D.Nonempty) :
    ∑ x : G, comparisonWeight C D x = 1 := by
  rw [comparisonWeight, sum_normalizedConvolution,
    sum_normalizedDifferenceConvolution, sum_normalizedDifferenceConvolution,
    sum_normalizedIndicator hC, sum_normalizedIndicator hD]
  norm_num

/-- An autocorrelation of a measure supported in `B_eta` is supported in
`B_(2 eta)`. -/
theorem differenceIndicator_support_two_mul
    {B : BohrData G} {eta : ℝ≥0} {C : Finset G}
    (hC : C.Nonempty) (hCsmall : C ⊆ (B.dilate eta).carrier)
    {x : G}
    (hx : normalizedDifferenceConvolution
      (normalizedIndicator C) (normalizedIndicator C) x ≠ 0) :
    x ∈ (B.dilate (2 * eta)).carrier := by
  by_contra hxout
  apply hx
  rw [normalizedDifferenceConvolution]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : normalizedIndicator C y = 0
  · simp [hy]
  have hyC : y ∈ C := (normalizedIndicator_ne_zero_iff hC y).mp hy
  by_cases hyx : normalizedIndicator C (y - x) = 0
  · simp [hyx]
  have hyxC : y - x ∈ C :=
    (normalizedIndicator_ne_zero_iff hC (y - x)).mp hyx
  have hmem := BohrData.sub_mem_dilate (hCsmall hyC) (hCsmall hyxC)
  have heq : y - (y - x) = x := by abel
  rw [heq] at hmem
  exact (hxout (by simpa [two_mul] using hmem)).elim

/-- Consequently the convolution of two such autocorrelations is supported
in the fourfold narrow dilate. -/
theorem comparisonWeight_support_four_mul
    {B : BohrData G} {eta : ℝ≥0} {C D : Finset G}
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    {x : G} (hx : comparisonWeight C D x ≠ 0) :
    x ∈ (B.dilate (4 * eta)).carrier := by
  by_contra hxout
  apply hx
  rw [comparisonWeight, normalizedConvolution]
  apply Finset.sum_eq_zero
  intro y _
  let cCorr := normalizedDifferenceConvolution
    (normalizedIndicator C) (normalizedIndicator C)
  let dCorr := normalizedDifferenceConvolution
    (normalizedIndicator D) (normalizedIndicator D)
  by_cases hy : cCorr y = 0
  · exact mul_eq_zero.mpr (Or.inl (by simpa [cCorr] using hy))
  by_cases hxy : dCorr (x - y) = 0
  · exact mul_eq_zero.mpr (Or.inr (by simpa [dCorr] using hxy))
  have hyB : y ∈ (B.dilate (2 * eta)).carrier :=
    differenceIndicator_support_two_mul hC hCsmall hy
  have hxyB : x - y ∈ (B.dilate (2 * eta)).carrier :=
    differenceIndicator_support_two_mul hD hDsmall hxy
  have hmem := BohrData.add_mem_dilate hyB hxyB
  have heq : y + (x - y) = x := by abel
  rw [heq] at hmem
  exact (hxout (by
    simpa [show (2 : ℝ≥0) * eta + 2 * eta = 4 * eta by ring] using hmem)).elim

/-- The comparison weight is a probability weight. -/
theorem comparisonWeight_isProbability
    {C D : Finset G} (hC : C.Nonempty) (hD : D.Nonempty) :
    (∀ x, 0 ≤ comparisonWeight C D x) ∧
      ∑ x : G, comparisonWeight C D x = 1 :=
  ⟨comparisonWeight_nonneg C D, sum_comparisonWeight hC hD⟩

/-! ## The factor-two averaging step -/

/-- Majorization by a smoothed probability weight costs exactly a factor two
once every translate of the inner weight satisfies the same moment bound. -/
theorem weightedMoment_le_two_of_majorization
    (mu outer nu h : G → ℝ) (R : ℝ)
    (houter_nonneg : ∀ x, 0 ≤ outer x)
    (houter_mass : ∑ x : G, outer x = 1)
    (hh : ∀ x, 0 ≤ h x)
    (hmajor : ∀ x, mu x ≤ 2 * normalizedConvolution outer nu x)
    (htranslate : ∀ t : G, ∑ x : G, nu (x - t) * h x ≤ R) :
    ∑ x : G, mu x * h x ≤ 2 * R := by
  calc
    ∑ x : G, mu x * h x ≤
        ∑ x : G, (2 * normalizedConvolution outer nu x) * h x := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (hmajor x) (hh x)
    _ = 2 * ∑ x : G, normalizedConvolution outer nu x * h x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ t : G, outer t * ∑ x : G, nu (x - t) * h x := by
      apply congrArg (fun z : ℝ ↦ 2 * z)
      simp only [normalizedConvolution]
      calc
        ∑ x : G, (∑ y : G, outer y * nu (x - y)) * h x =
            ∑ x : G, ∑ y : G, (outer y * nu (x - y)) * h x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
        _ = ∑ t : G, ∑ x : G, (outer t * nu (x - t)) * h x :=
          Finset.sum_comm
        _ = ∑ t : G, outer t * ∑ x : G, nu (x - t) * h x := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ ≤ 2 * ∑ t : G, outer t * R := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left (htranslate t) (houter_nonneg t)
      · norm_num
    _ = 2 * R := by rw [← Finset.sum_mul, houter_mass, one_mul]

/-- The Bohr-majorization part of convolution comparison, separated from the
Fourier phase-removal input.  The next theorem discharges `hphase` for every
positive even exponent. -/
theorem convolutionComparison_moment_of_phaseRemoval
    {B : BohrData G} {rho eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsCoarselyRegularAt rho (4 * eta))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (p : ℕ) (f : G → ℂ)
    (hphase : ∀ t : G,
      ∑ x : G, comparisonWeight C D (x - t) * ‖convolution f f x‖ ^ p ≤
        ∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p) :
    ∑ x : G, normalizedIndicator (B.dilate rho).carrier x *
        ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  let nu := comparisonWeight C D
  let outer := normalizedIndicator (B.dilate (rho + 4 * eta)).carrier
  apply weightedMoment_le_two_of_majorization
      (normalizedIndicator (B.dilate rho).carrier) outer nu
      (fun x ↦ ‖convolution f f x‖ ^ p)
      (∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p)
  · exact normalizedIndicator_nonneg _
  · exact sum_normalizedIndicator (B.dilate (rho + 4 * eta)).carrier_nonempty
  · intro x
    positivity
  · intro x
    exact normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
      hreg nu (comparisonWeight_nonneg C D) (sum_comparisonWeight hC hD)
      (fun t ht ↦ comparisonWeight_support_four_mul hC hD hCsmall hDsmall ht) x
  · exact hphase

/-- Rank-explicit specialization.  The numerical hypothesis says exactly
that the full fourfold support of the smoothing weight lies inside the
`1/(400 max(rank,1))` regularity window. -/
theorem convolutionComparison_moment_of_phaseRemoval_rankRegular
    {B : BohrData G} {eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (p : ℕ) (f : G → ℂ)
    (hphase : ∀ t : G,
      ∑ x : G, comparisonWeight C D (x - t) * ‖convolution f f x‖ ^ p ≤
        ∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p) :
    ∑ x : G, normalizedIndicator B.carrier x * ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  let nu := comparisonWeight C D
  let outer := normalizedIndicator (B.dilate (1 + 4 * eta)).carrier
  apply weightedMoment_le_two_of_majorization
      (normalizedIndicator B.carrier) outer nu
      (fun x ↦ ‖convolution f f x‖ ^ p)
      (∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p)
  · exact normalizedIndicator_nonneg _
  · exact sum_normalizedIndicator (B.dilate (1 + 4 * eta)).carrier_nonempty
  · intro x
    positivity
  · intro x
    exact normalizedIndicator_le_two_mul_convolution_of_rankRegular
      hreg (by positivity : 0 < (4 : ℝ≥0) * eta) hnarrow nu
      (comparisonWeight_nonneg C D) (sum_comparisonWeight hC hD)
      (fun t ht ↦ comparisonWeight_support_four_mul hC hD hCsmall hDsmall ht) x
  · exact hphase

/-- **Convolution comparison on a coarse regular Bohr shell.**  For every
positive even exponent, additive convolution on the central Bohr weight is
controlled, with the exact factor two, by autocorrelation on the fourfold
autocorrelation weight. -/
theorem convolutionComparison_moment
    {B : BohrData G} {rho eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsCoarselyRegularAt rho (4 * eta))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : p ≠ 0) (heven : Even p) (f : G → ℂ) :
    ∑ x : G, normalizedIndicator (B.dilate rho).carrier x *
        ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  apply convolutionComparison_moment_of_phaseRemoval hreg hC hD hCsmall hDsmall p f
  intro t
  apply LpOrthogonality.sum_translate_convolution_le_autocorrelation hp heven
      (comparisonWeight C D) (comparisonWeight_nonneg C D)
  · simpa only [comparisonWeight] using
      LpOrthogonality.spectrallyNonnegative_counting_autocorrelation_convolution
        (normalizedIndicator C) (normalizedIndicator D)

/-- Rank- and width-explicit form of `convolutionComparison_moment`.  This is
the form consumed by the balanced-restriction argument. -/
theorem convolutionComparison_moment_rankRegular
    {B : BohrData G} {eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : p ≠ 0) (heven : Even p) (f : G → ℂ) :
    ∑ x : G, normalizedIndicator B.carrier x * ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  apply convolutionComparison_moment_of_phaseRemoval_rankRegular
    hreg heta hnarrow hC hD hCsmall hDsmall p f
  intro t
  apply LpOrthogonality.sum_translate_convolution_le_autocorrelation hp heven
      (comparisonWeight C D) (comparisonWeight_nonneg C D)
  · simpa only [comparisonWeight] using
      LpOrthogonality.spectrallyNonnegative_counting_autocorrelation_convolution
        (normalizedIndicator C) (normalizedIndicator D)

#print axioms convolutionComparison_moment
#print axioms convolutionComparison_moment_rankRegular

end

end ConvolutionComparison
end Erdos140

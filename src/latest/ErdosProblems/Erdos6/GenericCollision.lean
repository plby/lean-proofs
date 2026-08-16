import ErdosProblems.Erdos6.GenericMoment
import BoundedGaps.Maynard.ConcreteSquarefreeMeanLimit

/-!
# Tuple-generic removal of coordinate collisions

The pre-sieved product model permits a prime to occur in two coordinates.
The actual Maynard divisor support excludes exactly those collisions.  Their
normalized reciprocal-totient mass is `o(1)` because every shared prime is
larger than the pre-sieve cutoff.
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

def tupleCollisionMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight H u

def normalizedTupleCollisionMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  tupleCollisionMoment H alpha f N / tupleNaturalScale H alpha N

theorem abs_tupleCollisionMoment_le_weight
    {H : Finset ℕ} {alpha : ℝ} {f : (H → ℝ) → ℝ} {N : ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hf : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H, |f x| ≤ 1) :
    |tupleCollisionMoment H alpha f N| ≤
      ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        BoundedGaps.Maynard.reciprocalTotientTupleWeight H u := by
  unfold tupleCollisionMoment
  calc
    _ ≤ ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        |f (tupleNormalizedLogPoint H alpha N u) *
          BoundedGaps.Maynard.reciprocalTotientTupleWeight H u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        BoundedGaps.Maynard.reciprocalTotientTupleWeight H u := by
      apply Finset.sum_le_sum
      intro u hu
      have huPre : u ∈ BoundedGaps.Maynard.preSievedSimplexTupleSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
        exact (Finset.mem_filter.mp hu).1
      have hpoint := tupleNormalizedLogPoint_mem_finiteSimplex hR huPre
      rw [abs_mul, abs_of_nonneg
        (show 0 ≤ BoundedGaps.Maynard.reciprocalTotientTupleWeight H u by
          unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
          positivity)]
      exact mul_le_of_le_one_left
        (by
          unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
          positivity)
        (hf _ hpoint)

theorem eventually_abs_normalizedTupleCollisionMoment_le
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ}
    (hf : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H, |f x| ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      |normalizedTupleCollisionMoment H alpha f N| ≤
        ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          (BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
              (BoundedGaps.Maynard.engelsmaMaynardModulus N)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            (BoundedGaps.Maynard.preSieveSingularSeries
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))) ^
            Fintype.card H := by
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have hscale := eventually_tupleNaturalScale_pos (H := H) halpha
  obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge 1
  filter_upwards [hR, hscale, eventually_ge_atTop (N₀ + 1)] with
      N hRN hscaleN hN
  have hDge : 1 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1) :=
    hN₀ (N - 1) (by omega)
  have hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1) :=
    lt_of_lt_of_le Nat.zero_lt_one hDge
  have hweight := BoundedGaps.Maynard.collisionWeightSum_le_explicit
    (H := H) (R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)) hD
  have hweight' :
      (∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        BoundedGaps.Maynard.reciprocalTotientTupleWeight H u) ≤
        ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
            (BoundedGaps.Maynard.engelsmaMaynardModulus N)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
              Fintype.card H *
          (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) := by
    simpa only [BoundedGaps.Maynard.engelsmaMaynardModulus] using hweight
  have hmoment := abs_tupleCollisionMoment_le_weight hRN hf
  have hbase : 0 <
      BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) := by
    exact mul_pos
      (BoundedGaps.Maynard.preSieveSingularSeries_pos _)
      (Real.log_pos (by exact_mod_cast hRN))
  have hbound : |normalizedTupleCollisionMoment H alpha f N| ≤
      (((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
        (BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
          (BoundedGaps.Maynard.engelsmaMaynardModulus N)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^
            Fintype.card H *
        (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ))) /
          tupleNaturalScale H alpha N := by
    unfold normalizedTupleCollisionMoment
    rw [abs_div, abs_of_pos hscaleN]
    exact (div_le_div_of_nonneg_right (hmoment.trans hweight') hscaleN.le)
  apply hbound.trans_eq
  unfold tupleNaturalScale
  rw [div_pow]
  ring

theorem tendsto_normalizedTupleCollisionMoment_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ}
    (hf : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H, |f x| ≤ 1) :
    Tendsto (fun N : ℕ => normalizedTupleCollisionMoment H alpha f N)
      atTop (nhds 0) := by
  have hratio :=
    BoundedGaps.Maynard.tendsto_engelsmaSquarefreeMean_div_leadingTerm_one
      halpha
  have hpow := hratio.pow (Fintype.card H)
  have hcutoff : Tendsto (fun N : ℕ =>
      (8 : ℝ) / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ))
      atTop (nhds 0) := by
    change Tendsto ((fun n : ℕ => (8 : ℝ) / (n : ℝ)) ∘
      (fun N : ℕ => BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
      atTop (nhds 0)
    exact (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).comp
      BoundedGaps.Maynard.tendsto_shifted_tripleLogCutoff
  have henvelope : Tendsto (fun N : ℕ =>
      ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
        (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
        (BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
            (BoundedGaps.Maynard.engelsmaMaynardModulus N)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))) ^
          Fintype.card H) atTop (nhds 0) := by
    have hcombined := hcutoff.mul hpow
    have hscaled := hcombined.const_mul
      ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ)
    simpa [mul_assoc] using hscaled
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  exact eventually_abs_normalizedTupleCollisionMoment_le halpha hf

end

end Erdos6.Maynard

import ErdosProblems.Erdos6.GenericOuterMoment

/-!
# Tuple-generic removal of outer-weight coordinate collisions
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

def tupleOuterCollisionMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.outerTupleWeight H
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) u

def normalizedTupleOuterCollisionMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  tupleOuterCollisionMoment H alpha f N / tupleNaturalScale H alpha N

def tupleOuterMaynardWeightedMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.outerTupleWeight H
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) u

def normalizedTupleOuterMaynardWeightedMoment (H : Finset ℕ) (alpha : ℝ)
    (f : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  tupleOuterMaynardWeightedMoment H alpha f N / tupleNaturalScale H alpha N

theorem tupleOuterWeightedMoment_eq_maynard_add_collision
    (H : Finset ℕ) (alpha : ℝ) (f : (H → ℝ) → ℝ) (N : ℕ) :
    tupleOuterWeightedMoment H alpha f N =
      tupleOuterMaynardWeightedMoment H alpha f N +
        tupleOuterCollisionMoment H alpha f N := by
  classical
  let S := BoundedGaps.Maynard.preSievedSimplexTupleSupport H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
  let P := fun u : H → ℕ =>
    Squarefree (BoundedGaps.Maynard.divisorTupleProduct H u)
  let g := fun u : H → ℕ =>
    f (tupleNormalizedLogPoint H alpha N u) *
      BoundedGaps.Maynard.outerTupleWeight H
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) u
  have hmay : BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) = S.filter P := by
    exact BoundedGaps.Maynard.maynardDivisorTupleSupport_eq_preSievedSimplex_filter
      H _ _
  have hcol : BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) =
        S.filter (fun u => ¬P u) := by
    rfl
  unfold tupleOuterWeightedMoment tupleOuterMaynardWeightedMoment
    tupleOuterCollisionMoment
  rw [hmay, hcol]
  exact (Finset.sum_filter_add_sum_filter_not S P g).symm

theorem normalizedTupleOuterMaynardWeightedMoment_eq_sub
    (H : Finset ℕ) (alpha : ℝ) (f : (H → ℝ) → ℝ) (N : ℕ) :
    normalizedTupleOuterMaynardWeightedMoment H alpha f N =
      normalizedTupleOuterWeightedMoment H alpha f N -
        normalizedTupleOuterCollisionMoment H alpha f N := by
  unfold normalizedTupleOuterMaynardWeightedMoment
    normalizedTupleOuterWeightedMoment normalizedTupleOuterCollisionMoment
  rw [tupleOuterWeightedMoment_eq_maynard_add_collision H alpha f N]
  ring

theorem abs_tupleOuterCollisionMoment_le_weight
    {H : Finset ℕ} {alpha : ℝ} {f : (H → ℝ) → ℝ} {N : ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hf : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H, |f x| ≤ 1) :
    |tupleOuterCollisionMoment H alpha f N| ≤
      ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        BoundedGaps.Maynard.outerTupleWeight H
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) u := by
  unfold tupleOuterCollisionMoment
  calc
    _ ≤ ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        |f (tupleNormalizedLogPoint H alpha N u) *
          BoundedGaps.Maynard.outerTupleWeight H
            (BoundedGaps.Maynard.engelsmaMaynardModulus N) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      have huPre := (Finset.mem_filter.mp hu).1
      have hpoint := tupleNormalizedLogPoint_mem_finiteSimplex hR huPre
      rw [abs_mul, abs_of_nonneg (outerTupleWeight_nonneg H
        (BoundedGaps.Maynard.engelsmaMaynardModulus N) u)]
      exact mul_le_of_le_one_left
        (outerTupleWeight_nonneg H
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) u) (hf _ hpoint)

theorem eventually_abs_normalizedTupleOuterCollisionMoment_le
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ}
    (hf : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H, |f x| ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      |normalizedTupleOuterCollisionMoment H alpha f N| ≤
        ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          (BoundedGaps.Maynard.maynardS2OuterSquarefreeMean
              (BoundedGaps.Maynard.engelsmaMaynardModulus N)
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            (BoundedGaps.Maynard.preSieveSingularSeries
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
              Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))) ^
            Fintype.card H := by
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have hscale := eventually_tupleNaturalScale_pos (H := H) halpha
  obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
  filter_upwards [hR, hscale, eventually_ge_atTop (N₀ + 1)] with
      N hRN hscaleN hN
  have hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1) :=
    hN₀ (N - 1) (by omega)
  have hweight := BoundedGaps.Maynard.outerCollisionWeightSum_le_explicit
    (H := H) (R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) hD
  have hmoment := abs_tupleOuterCollisionMoment_le_weight hRN hf
  have hbound : |normalizedTupleOuterCollisionMoment H alpha f N| ≤
      (((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
        (BoundedGaps.Maynard.maynardS2OuterSquarefreeMean
          (BoundedGaps.Maynard.engelsmaMaynardModulus N)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)) ^ Fintype.card H *
        (8 / (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ))) /
          tupleNaturalScale H alpha N := by
    unfold normalizedTupleOuterCollisionMoment
    rw [abs_div, abs_of_pos hscaleN]
    apply div_le_div_of_nonneg_right (hmoment.trans ?_) hscaleN.le
    simpa only [BoundedGaps.Maynard.engelsmaMaynardModulus] using hweight
  apply hbound.trans_eq
  unfold tupleNaturalScale
  rw [div_pow]
  ring

theorem tendsto_normalizedTupleOuterCollisionMoment_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ}
    (hf : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H, |f x| ≤ 1) :
    Tendsto (fun N : ℕ =>
      normalizedTupleOuterCollisionMoment H alpha f N) atTop (nhds 0) := by
  have hratio :=
    BoundedGaps.Maynard.tendsto_engelsmaS2OuterSquarefreeMean_fractionalRadius_nonneg
      halpha (show (0 : ℝ) ≤ 1 by norm_num)
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
        (BoundedGaps.Maynard.maynardS2OuterSquarefreeMean
            (BoundedGaps.Maynard.engelsmaMaynardModulus N)
            (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))) ^
          Fintype.card H)
      atTop (nhds 0) := by
    have hcombined := hcutoff.mul hpow
    have hscaled := hcombined.const_mul
      ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ)
    simpa [mul_assoc] using hscaled
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  exact eventually_abs_normalizedTupleOuterCollisionMoment_le halpha hf

theorem tendsto_normalizedTupleOuterMaynardWeightedMoment
    {H : Finset ℕ} (h0 : H) {alpha : ℝ} (halpha : 0 < alpha)
    {f : (H → ℝ) → ℝ} (hcont : Continuous f)
    (hfbounds : ∀ x ∈ BoundedGaps.Maynard.finiteSimplexOf H,
      0 ≤ f x ∧ f x ≤ 1) :
    Tendsto (fun N : ℕ =>
      normalizedTupleOuterMaynardWeightedMoment H alpha f N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf H, f t)) := by
  have hfull := tendsto_normalizedTupleOuterWeightedMoment h0 halpha
    hcont hfbounds
  have hcol := tendsto_normalizedTupleOuterCollisionMoment_zero halpha
    (fun x hx => by
      rw [abs_of_nonneg (hfbounds x hx).1]
      exact (hfbounds x hx).2)
  rw [show (fun N : ℕ =>
      normalizedTupleOuterMaynardWeightedMoment H alpha f N) =
      fun N => normalizedTupleOuterWeightedMoment H alpha f N -
        normalizedTupleOuterCollisionMoment H alpha f N by
    funext N
    exact normalizedTupleOuterMaynardWeightedMoment_eq_sub H alpha f N]
  simpa using hfull.sub hcol

end

end Erdos6.Maynard

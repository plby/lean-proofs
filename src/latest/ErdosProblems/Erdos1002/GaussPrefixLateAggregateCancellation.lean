import ErdosProblems.Erdos1002.GaussPrefixLateMeasurability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate recombination for the late marked-Fourier argument

The pointwise late-case ingredients are already available:

* replacement of an exact prefix factor by a frozen prefix factor;
* functional prefix--future mixing for that frozen factor;
* oscillatory cancellation after summing the prefix means.

What is not automatic is the order of the finite sums and absolute
values.  This file supplies the deterministic aggregate inequality which
keeps that order literal.  It also proves the polynomial-cardinality
versus geometric-mixing limit in a form adapted to a moving scale and a
possibly different, but linearly comparable, mixing gap.

No cancellation conclusion is assumed by either theorem.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixLateAggregateCancellationPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## The exact aggregate freezing--mixing inequality -/

/-- Number of pairs in a finite family presented as prefix fibers. -/
def nestedPairCount
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : Finset α) (futures : α → Finset β) : ℕ :=
  ∑ p ∈ prefixes, (futures p).card

/-- The absolute-summability inequality needed in the late case.

For every prefix/future pair, insert first a frozen joint term and then
the product of its prefix and future means.  The norm of the complete
exact sum is bounded by:

1. the **sum** of all freezing errors;
2. the number of pairs times the uniform mixing error;
3. the correctly factorized main term
   `Σ_p |prefixMean p| Σ_u |futureMean p u|`.

In particular, both error absolute values remain inside the finite
aggregate; no estimate of only the absolute value of their total sum is
substituted. -/
theorem norm_nested_sum_le_freezing_add_mixing_add_factorized
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : Finset α) (futures : α → Finset β)
    (exactTerm frozenJoint : α → β → ℂ)
    (prefixMean : α → ℂ) (futureMean : α → β → ℂ)
    {freezingError mixingError : ℝ}
    (hfreezing :
      ∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖exactTerm p u - frozenJoint p u‖ ≤ freezingError)
    (hmixing : ∀ p ∈ prefixes, ∀ u ∈ futures p,
      ‖frozenJoint p u - prefixMean p * futureMean p u‖ ≤
        mixingError) :
    ‖∑ p ∈ prefixes, ∑ u ∈ futures p, exactTerm p u‖ ≤
      freezingError +
        (nestedPairCount prefixes futures : ℝ) * mixingError +
        ∑ p ∈ prefixes,
          ‖prefixMean p‖ * ∑ u ∈ futures p, ‖futureMean p u‖ := by
  have hpoint (p : α) (u : β) :
      ‖exactTerm p u‖ ≤
        ‖exactTerm p u - frozenJoint p u‖ +
          ‖frozenJoint p u - prefixMean p * futureMean p u‖ +
          ‖prefixMean p * futureMean p u‖ := by
    have hdecomp :
        exactTerm p u =
          (exactTerm p u - frozenJoint p u) +
            (frozenJoint p u - prefixMean p * futureMean p u) +
            prefixMean p * futureMean p u := by
      ring
    conv_lhs => rw [hdecomp]
    exact norm_add₃_le
      (a := exactTerm p u - frozenJoint p u)
      (b := frozenJoint p u - prefixMean p * futureMean p u)
      (c := prefixMean p * futureMean p u)
  have hnorm :
      ‖∑ p ∈ prefixes, ∑ u ∈ futures p, exactTerm p u‖ ≤
        ∑ p ∈ prefixes, ∑ u ∈ futures p, ‖exactTerm p u‖ := by
    calc
      ‖∑ p ∈ prefixes, ∑ u ∈ futures p, exactTerm p u‖ ≤
          ∑ p ∈ prefixes,
            ‖∑ u ∈ futures p, exactTerm p u‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ prefixes,
            ∑ u ∈ futures p, ‖exactTerm p u‖ := by
        apply Finset.sum_le_sum
        intro p _hp
        exact norm_sum_le _ _
  have htermwise :
      (∑ p ∈ prefixes, ∑ u ∈ futures p, ‖exactTerm p u‖) ≤
        (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖exactTerm p u - frozenJoint p u‖) +
        (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖frozenJoint p u - prefixMean p * futureMean p u‖) +
        (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖prefixMean p * futureMean p u‖) := by
    calc
      (∑ p ∈ prefixes, ∑ u ∈ futures p, ‖exactTerm p u‖) ≤
          ∑ p ∈ prefixes, ∑ u ∈ futures p,
            (‖exactTerm p u - frozenJoint p u‖ +
              ‖frozenJoint p u - prefixMean p * futureMean p u‖ +
              ‖prefixMean p * futureMean p u‖) := by
        apply Finset.sum_le_sum
        intro p _hp
        apply Finset.sum_le_sum
        intro u _hu
        exact hpoint p u
      _ =
          (∑ p ∈ prefixes, ∑ u ∈ futures p,
            ‖exactTerm p u - frozenJoint p u‖) +
          (∑ p ∈ prefixes, ∑ u ∈ futures p,
            ‖frozenJoint p u - prefixMean p * futureMean p u‖) +
          (∑ p ∈ prefixes, ∑ u ∈ futures p,
            ‖prefixMean p * futureMean p u‖) := by
        simp_rw [Finset.sum_add_distrib]
  have hmixingSum :
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖frozenJoint p u - prefixMean p * futureMean p u‖) ≤
        (nestedPairCount prefixes futures : ℝ) * mixingError := by
    calc
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖frozenJoint p u - prefixMean p * futureMean p u‖) ≤
          ∑ p ∈ prefixes, ∑ _u ∈ futures p, mixingError := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro u hu
        exact hmixing p hp u hu
      _ = (nestedPairCount prefixes futures : ℝ) * mixingError := by
        simp only [Finset.sum_const, nsmul_eq_mul, nestedPairCount,
          Nat.cast_sum]
        rw [Finset.sum_mul]
  have hfactorized :
      (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖prefixMean p * futureMean p u‖) =
        ∑ p ∈ prefixes,
          ‖prefixMean p‖ * ∑ u ∈ futures p, ‖futureMean p u‖ := by
    apply Finset.sum_congr rfl
    intro p _hp
    simp_rw [norm_mul]
    rw [Finset.mul_sum]
  calc
    ‖∑ p ∈ prefixes, ∑ u ∈ futures p, exactTerm p u‖ ≤
        ∑ p ∈ prefixes, ∑ u ∈ futures p, ‖exactTerm p u‖ :=
      hnorm
    _ ≤
        (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖exactTerm p u - frozenJoint p u‖) +
        (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖frozenJoint p u - prefixMean p * futureMean p u‖) +
        (∑ p ∈ prefixes, ∑ u ∈ futures p,
          ‖prefixMean p * futureMean p u‖) :=
      htermwise
    _ ≤
        freezingError +
          (nestedPairCount prefixes futures : ℝ) * mixingError +
          (∑ p ∈ prefixes, ∑ u ∈ futures p,
            ‖prefixMean p * futureMean p u‖) := by
      exact add_le_add (add_le_add hfreezing hmixingSum) le_rfl
    _ =
        freezingError +
          (nestedPairCount prefixes futures : ℝ) * mixingError +
          ∑ p ∈ prefixes,
            ‖prefixMean p‖ * ∑ u ∈ futures p, ‖futureMean p u‖ := by
      rw [hfactorized]

/-! ## Polynomially many covariance errors at a moving linear gap -/

/-- A nested finite sum with polynomial cardinality is killed by the
explicit Gauss mixing rate whenever the ambient scale is bounded by a
fixed multiple of `gap + 1` and the gap tends to infinity.

This is the form needed after fixing `rho > 0`: the midpoint construction
provides `scale ≤ dilation * (gap + 1)`, while the canonical tuple count is
polynomial in `scale`. -/
theorem tendsto_nested_sum_zero_of_pairCount_le_scalePow_gaussMixingRate
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (z : ℕ → α → β → ℂ)
    (scale gap : ℕ → ℕ)
    (hgap : Tendsto gap atTop atTop)
    (dimension dilation : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hscale : ∀ᶠ N : ℕ in atTop,
      scale N ≤ dilation * (gap N + 1))
    (hcard : ∀ᶠ N : ℕ in atTop,
      nestedPairCount (prefixes N) (futures N) ≤
        scale N ^ dimension)
    (hbound : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
        ‖z N p u‖ ≤
          C * (527 / 540 : ℝ) ^ gap N) :
    Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u)
      atTop (nhds 0) := by
  let theta : ℝ := 540 / 527
  let gapSucc : ℕ → ℕ := fun N ↦ gap N + 1
  let upper : ℕ → ℝ := fun N ↦
    (C * (dilation : ℝ) ^ dimension * theta) *
      ((gapSucc N : ℝ) ^ dimension *
        (theta ^ gapSucc N)⁻¹)
  have htheta : 1 < theta := by
    dsimp only [theta]
    norm_num
  have hgapSucc : Tendsto gapSucc atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun N ↦ Nat.le_add_right (gap N) 1) hgap
  have hpoly :
      Tendsto
        (fun N ↦
          (gapSucc N : ℝ) ^ dimension *
            (theta ^ gapSucc N)⁻¹)
        atTop (nhds 0) := by
    have h :=
      (tendsto_natPower_mul_inverse_geometric
        dimension 1 (by omega) htheta).comp hgapSucc
    simpa only [one_mul] using! h
  have hupper : Tendsto upper atTop (nhds 0) := by
    have h :=
      hpoly.const_mul
        (C * (dilation : ℝ) ^ dimension * theta)
    simpa only [upper, mul_zero] using! h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ norm_nonneg _
  · filter_upwards [hscale, hcard, hbound] with N hscaleN hcardN hboundN
    have hpairReal :
        (nestedPairCount (prefixes N) (futures N) : ℝ) ≤
          (scale N : ℝ) ^ dimension := by
      exact_mod_cast hcardN
    have hscaleReal :
        (scale N : ℝ) ^ dimension ≤
          ((dilation * (gap N + 1) : ℕ) : ℝ) ^ dimension := by
      exact pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast hscaleN) dimension
    have hrateNonneg :
        0 ≤ C * (527 / 540 : ℝ) ^ gap N := by
      positivity
    have hfactor :
        (527 / 540 : ℝ) ^ gap N =
          theta * (theta ^ gapSucc N)⁻¹ := by
      dsimp only [theta, gapSucc]
      rw [show (527 / 540 : ℝ) = (540 / 527 : ℝ)⁻¹ by
        norm_num, inv_pow, pow_succ, mul_inv_rev]
      field_simp
    calc
      ‖∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u‖ ≤
          ∑ p ∈ prefixes N, ∑ u ∈ futures N p, ‖z N p u‖ := by
        calc
          ‖∑ p ∈ prefixes N, ∑ u ∈ futures N p, z N p u‖ ≤
              ∑ p ∈ prefixes N,
                ‖∑ u ∈ futures N p, z N p u‖ :=
            norm_sum_le _ _
          _ ≤
              ∑ p ∈ prefixes N, ∑ u ∈ futures N p, ‖z N p u‖ := by
            apply Finset.sum_le_sum
            intro p _hp
            exact norm_sum_le _ _
      _ ≤
          ∑ p ∈ prefixes N, ∑ _u ∈ futures N p,
            C * (527 / 540 : ℝ) ^ gap N := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro u hu
        exact hboundN p hp u hu
      _ =
          (nestedPairCount (prefixes N) (futures N) : ℝ) *
            (C * (527 / 540 : ℝ) ^ gap N) := by
        simp only [Finset.sum_const, nsmul_eq_mul, nestedPairCount,
          Nat.cast_sum]
        rw [Finset.sum_mul]
      _ ≤
          (scale N : ℝ) ^ dimension *
            (C * (527 / 540 : ℝ) ^ gap N) :=
        mul_le_mul_of_nonneg_right hpairReal hrateNonneg
      _ ≤
          ((dilation * (gap N + 1) : ℕ) : ℝ) ^ dimension *
            (C * (527 / 540 : ℝ) ^ gap N) :=
        mul_le_mul_of_nonneg_right hscaleReal hrateNonneg
      _ = upper N := by
        rw [hfactor]
        dsimp only [upper, gapSucc]
        push_cast
        rw [mul_pow]
        ring
  · exact hupper

/-- Converging aggregate freezing, mixing, and factorized-main bounds
imply convergence of the exact nested aggregate.  The three hypotheses
are precisely the separately auditable outputs of the late-case proof. -/
theorem tendsto_nested_exact_sum_zero_of_freezing_mixing_factorized
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (prefixes : ℕ → Finset α)
    (futures : ℕ → α → Finset β)
    (exactTerm frozenJoint : ℕ → α → β → ℂ)
    (prefixMean : ℕ → α → ℂ)
    (futureMean : ℕ → α → β → ℂ)
    (freezingError mixingError : ℕ → ℝ)
    (hfreezing : ∀ N,
      ∑ p ∈ prefixes N, ∑ u ∈ futures N p,
        ‖exactTerm N p u - frozenJoint N p u‖ ≤ freezingError N)
    (hmixing : ∀ N, ∀ p ∈ prefixes N, ∀ u ∈ futures N p,
      ‖frozenJoint N p u -
          prefixMean N p * futureMean N p u‖ ≤ mixingError N)
    (hfreezingZero : Tendsto freezingError atTop (nhds 0))
    (hmixingZero : Tendsto
      (fun N ↦
        (nestedPairCount (prefixes N) (futures N) : ℝ) *
          mixingError N)
      atTop (nhds 0))
    (hfactorizedZero : Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N,
          ‖prefixMean N p‖ *
            ∑ u ∈ futures N p, ‖futureMean N p u‖)
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦
        ∑ p ∈ prefixes N, ∑ u ∈ futures N p, exactTerm N p u)
      atTop (nhds 0) := by
  have hupper :=
    (hfreezingZero.add hmixingZero).add hfactorizedZero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦
      norm_nested_sum_le_freezing_add_mixing_add_factorized
        (prefixes N) (futures N)
        (exactTerm N) (frozenJoint N)
        (prefixMean N) (futureMean N)
        (hfreezing N) (hmixing N)
  · simpa only [zero_add] using! hupper

/-! ## Concrete Gauss frozen-prefix/future-indicator specialization -/

/-- Joint Gauss expectation of the literal density-weighted affine frozen
prefix factor and one finite future digit block. -/
def gaussLateLebesgueWeightedFrozenJoint
    {ι : Type*} [Fintype ι]
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (b gap : ℕ) (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) (events : Fin r → Set ℝ) : ℂ :=
  ∫ x,
    gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
        N lower upper k h F b goodWords x *
      gaussFutureDigitBlockIndicator (b + gap) times events x
    ∂gaussMeasure

/-- Mean of the literal density-weighted affine frozen prefix factor. -/
def gaussLateLebesgueWeightedFrozenPrefixMean
    {ι : Type*} [Fintype ι]
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (b : ℕ) (goodWords : Set (PositiveDigitWord b)) : ℂ :=
  ∫ x,
    gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
      N lower upper k h F b goodWords x
    ∂gaussMeasure

/-- Mean of one finite future digit block. -/
def gaussLateFutureDigitBlockMean
    {r : ℕ} (base : ℕ) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) : ℂ :=
  ∫ x, gaussFutureDigitBlockIndicator base times events x
    ∂gaussMeasure

/-- The pointwise functional mixing theorem, rewritten in the exact three
terms used by aggregate recombination and weakened to a common lower bound
on the mixing gap. -/
theorem
    gaussLateLebesgueWeightedFrozen_covariance_le_commonGap
    {ι : Type*} [Fintype ι]
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (b gap gapFloor : ℕ) (hgap : gapFloor ≤ gap)
    (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    ‖gaussLateLebesgueWeightedFrozenJoint
          N lower upper k h F b gap goodWords times events -
        gaussLateLebesgueWeightedFrozenPrefixMean
            N lower upper k h F b goodWords *
          gaussLateFutureDigitBlockMean
            (b + gap) times events‖ ≤
      (384 * Real.log 2) * (527 / 540 : ℝ) ^ gapFloor := by
  have hraw :=
    gaussPrefixLebesgueWeightedAffineFrozen_futureDigitBlock_covariance_le_rate
      N lower upper k h F b gap goodWords times hEvents
  have hpow :
      (527 / 540 : ℝ) ^ gap ≤
        (527 / 540 : ℝ) ^ gapFloor := by
    exact
      (pow_le_pow_iff_right_of_lt_one₀
        (by norm_num : (0 : ℝ) < 527 / 540)
        (by norm_num : (527 / 540 : ℝ) < 1)).2 hgap
  calc
    ‖gaussLateLebesgueWeightedFrozenJoint
          N lower upper k h F b gap goodWords times events -
        gaussLateLebesgueWeightedFrozenPrefixMean
            N lower upper k h F b goodWords *
          gaussLateFutureDigitBlockMean
            (b + gap) times events‖ ≤
        (384 * Real.log 2) * (527 / 540 : ℝ) ^ gap := by
      simpa only [gaussLateLebesgueWeightedFrozenJoint,
        gaussLateLebesgueWeightedFrozenPrefixMean,
        gaussLateFutureDigitBlockMean] using! hraw
    _ ≤ (384 * Real.log 2) * (527 / 540 : ℝ) ^ gapFloor := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Concrete aggregate late-case inequality for the actual frozen factors.

The caller supplies only the summed exact-to-frozen error.  Functional
Gauss prefix--future mixing supplies the entire middle term, uniformly at
the common gap floor.  The last term is left in its factorized form so
that the oscillatory prefix-cylinder estimate and the future digit-mass
bound can be audited independently. -/
theorem
    norm_nested_gaussLateLebesgueWeightedFrozen_sum_le
    {ι α β : Type*} [Fintype ι]
    [DecidableEq α] [DecidableEq β]
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (prefixes : Finset α) (futures : α → Finset β)
    (F : α → GaussPrefixMixedDepthTuple N k)
    (b gap : α → ℕ) (gapFloor : ℕ)
    (hgap : ∀ p ∈ prefixes, gapFloor ≤ gap p)
    (goodWords : ∀ p, Set (PositiveDigitWord (b p)))
    {r : ℕ} (times : α → β → Fin r → ℕ)
    (events : α → β → Fin r → Set ℝ)
    (hEvents : ∀ p ∈ prefixes, ∀ u ∈ futures p, ∀ i,
      MeasurableSet (events p u i))
    (exactTerm : α → β → ℂ) {freezingError : ℝ}
    (hfreezing :
      ∑ p ∈ prefixes, ∑ u ∈ futures p,
        ‖exactTerm p u -
          gaussLateLebesgueWeightedFrozenJoint
            N lower upper k h (F p) (b p) (gap p)
              (goodWords p) (times p u) (events p u)‖ ≤
        freezingError) :
    ‖∑ p ∈ prefixes, ∑ u ∈ futures p, exactTerm p u‖ ≤
      freezingError +
        (nestedPairCount prefixes futures : ℝ) *
          ((384 * Real.log 2) * (527 / 540 : ℝ) ^ gapFloor) +
        ∑ p ∈ prefixes,
          ‖gaussLateLebesgueWeightedFrozenPrefixMean
            N lower upper k h (F p) (b p) (goodWords p)‖ *
          ∑ u ∈ futures p,
            ‖gaussLateFutureDigitBlockMean
              (b p + gap p) (times p u) (events p u)‖ := by
  apply
    norm_nested_sum_le_freezing_add_mixing_add_factorized
      prefixes futures exactTerm
      (fun p u ↦
        gaussLateLebesgueWeightedFrozenJoint
          N lower upper k h (F p) (b p) (gap p)
            (goodWords p) (times p u) (events p u))
      (fun p ↦
        gaussLateLebesgueWeightedFrozenPrefixMean
          N lower upper k h (F p) (b p) (goodWords p))
      (fun p u ↦
        gaussLateFutureDigitBlockMean
          (b p + gap p) (times p u) (events p u))
      hfreezing
  intro p hp u hu
  exact
    gaussLateLebesgueWeightedFrozen_covariance_le_commonGap
      N lower upper k h (F p) (b p) (gap p) gapFloor
      (hgap p hp) (goodWords p) (times p u)
      (hEvents p hp u hu)

end

end Erdos1002

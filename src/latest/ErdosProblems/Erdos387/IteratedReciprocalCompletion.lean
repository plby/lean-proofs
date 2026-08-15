/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ReciprocalIntervalCompletion

/-!
# Completion after iterated reciprocal differencing

Fourier completion adds a linear term.  One cyclic difference removes that
term and adds one further translate pair to the rational phase.  The
unconditional simple-pole estimate therefore gives a uniform completed bound
at every fixed differencing depth, and the generic interval completion turns
it into a short-sum estimate.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace IteratedReciprocalCompletion

noncomputable def phase
    (p : ℕ) [NeZero p] (c a : ZMod p) (hs : List ℕ) :
    ZMod p → ZMod p :=
  InverseRational.zmodIteratedInversePhase p c a hs

noncomputable def twistedSequence
    (p : ℕ) [NeZero p] (c a : ZMod p) (hs : List ℕ)
    (b x : ZMod p) : ℂ :=
  ZMod.stdAddChar (b * x + phase p c a hs x)

/-- Coefficients of the phase after the original positive shifts and one
additional cyclic shift. -/
def cyclicDifferenceCoefficient
    (p : ℕ) [NeZero p] (c a : ZMod p) (hs : List ℕ)
    (h : ZMod p) : ZMod p → ZMod p :=
  InverseRational.iteratedDifferenceCoefficient
    (InverseRational.singlePoleCoefficient c (-a))
    ((h, 0) :: InverseRational.positiveShiftPairs p hs)

theorem simplePolePhase_cyclicDifferenceCoefficient
    {p : ℕ} [NeZero p] (c a : ZMod p) (hs : List ℕ)
    (h x : ZMod p) :
    InverseRational.simplePolePhase
        (cyclicDifferenceCoefficient p c a hs h) x =
      phase p c a hs (x + h) - phase p c a hs x := by
  rw [cyclicDifferenceCoefficient,
    InverseRational.simplePolePhase_iteratedDifferenceCoefficient]
  have hbase : InverseRational.simplePolePhase
      (InverseRational.singlePoleCoefficient c (-a)) =
      (fun y : ZMod p => c * (a + y)⁻¹) := by
    funext y
    exact InverseRational.simplePolePhase_singlePoleCoefficient_neg c a y
  rw [hbase]
  simp only [InverseRational.iteratedTranslateDifference, add_zero]
  rw [InverseRational.iteratedTranslateDifference_positiveShiftPairs,
    InverseRational.iteratedTranslateDifference_positiveShiftPairs]
  rfl

theorem twistedSequence_correlation
    {p : ℕ} [NeZero p] (c a : ZMod p) (hs : List ℕ)
    (b h x : ZMod p) :
    twistedSequence p c a hs b (h + x) *
        conj (twistedSequence p c a hs b x) =
      ZMod.stdAddChar (b * h) *
        ZMod.stdAddChar
          (InverseRational.simplePolePhase
            (cyclicDifferenceCoefficient p c a hs h) x) := by
  unfold twistedSequence
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 1
  rw [simplePolePhase_cyclicDifferenceCoefficient]
  rw [show phase p c a hs (h + x) = phase p c a hs (x + h) by
    congr 1
    ring]
  ring

/-- Pole envelope after the one extra cyclic difference. -/
def poleEnvelope (j : ℕ) : ℕ := 2 ^ (j + 1)

theorem cyclicDifference_poleSupport_nonempty
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ t ∈ hs, t + 1 < p)
    (hpow : poleEnvelope hs.length < p)
    {h : ZMod p} (hh : h ≠ 0) :
    (InverseRational.poleSupport
      (cyclicDifferenceCoefficient p c a hs h)).Nonempty := by
  apply InverseRational.singlePole_iteratedDifference_nonempty hc
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · simpa using hh
    · exact InverseRational.positiveShiftPairs_distinct hs hshift t ht
  · simpa [poleEnvelope] using hpow

theorem card_cyclicDifference_poleSupport_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ) (h : ZMod p) :
    (InverseRational.poleSupport
      (cyclicDifferenceCoefficient p c a hs h)).card ≤
        poleEnvelope hs.length := by
  calc
    (InverseRational.poleSupport
      (cyclicDifferenceCoefficient p c a hs h)).card ≤
        2 ^ ((h, 0) ::
          InverseRational.positiveShiftPairs p hs).length *
          (InverseRational.poleSupport
            (InverseRational.singlePoleCoefficient c (-a))).card :=
      InverseRational.card_poleSupport_iteratedDifferenceCoefficient_le _ _
    _ = poleEnvelope hs.length := by
      rw [InverseRational.poleSupport_singlePoleCoefficient
        (pole := -a) hc]
      simp [poleEnvelope]

/-- Every nonzero cyclic correlation is controlled by the conductor after
one additional difference. -/
theorem norm_correlation_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 1 < p) {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ t ∈ hs, t + 1 < p)
    (hpow : poleEnvelope hs.length < p)
    (b : ZMod p) {h : ZMod p} (hh : h ≠ 0) :
    ‖∑ x : ZMod p,
        twistedSequence p c a hs b (h + x) *
          conj (twistedSequence p c a hs b x)‖ ≤
      ((2 * poleEnvelope hs.length - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) + poleEnvelope hs.length := by
  let coeff := cyclicDifferenceCoefficient p c a hs h
  have hne : (InverseRational.poleSupport coeff).Nonempty :=
    cyclicDifference_poleSupport_nonempty hc hs hshift hpow hh
  have hcard : (InverseRational.poleSupport coeff).card ≤
      poleEnvelope hs.length :=
    card_cyclicDifference_poleSupport_le hc hs h
  have hcardp : (InverseRational.poleSupport coeff).card < p :=
    hcard.trans_lt hpow
  have hweil := RationalStepanov.norm_simplePolePhase_sum_le
    hp coeff hne hcardp
  rw [show (∑ x : ZMod p,
      twistedSequence p c a hs b (h + x) *
        conj (twistedSequence p c a hs b x)) =
      ZMod.stdAddChar (b * h) *
        ∑ x : ZMod p,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    exact twistedSequence_correlation c a hs b h x,
    norm_mul, AddChar.norm_apply, one_mul]
  have hcond :
      2 * (InverseRational.poleSupport coeff).card - 1 ≤
        2 * poleEnvelope hs.length - 1 := by omega
  exact hweil.trans (add_le_add
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcond)
      (Real.sqrt_nonneg _)) (by exact_mod_cast hcard))

/-- Squared uniform bound for every complete linear twist of the iterated
phase. -/
theorem norm_sum_twistedSequence_sq_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 1 < p) {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ t ∈ hs, t + 1 < p)
    (hpow : poleEnvelope hs.length < p) (b : ZMod p) :
    ‖∑ x : ZMod p, twistedSequence p c a hs b x‖ ^ 2 ≤
      (p : ℝ) + (p - 1 : ℕ) *
        (((2 * poleEnvelope hs.length - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) + poleEnvelope hs.length) := by
  let z : ZMod p → ℂ := twistedSequence p c a hs b
  have hcyclic := CyclicWeyl.norm_sum_sq_le_sum_norm_cyclicCorrelation z
  calc
    ‖∑ x : ZMod p, twistedSequence p c a hs b x‖ ^ 2 ≤
        ∑ h : ZMod p, ‖∑ x : ZMod p,
          z (h + x) * conj (z x)‖ := hcyclic
    _ = ‖∑ x : ZMod p, z (0 + x) * conj (z x)‖ +
        ∑ h ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          ‖∑ x : ZMod p, z (h + x) * conj (z x)‖ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    _ ≤ (p : ℝ) +
        ∑ _h ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          (((2 * poleEnvelope hs.length - 1 : ℕ) : ℝ) *
            Real.sqrt (p : ℝ) + poleEnvelope hs.length) := by
      apply add_le_add
      · have hzero : (∑ x : ZMod p,
            z (0 + x) * conj (z x)) = (p : ℂ) := by
          calc
            (∑ x : ZMod p, z (0 + x) * conj (z x)) =
                ∑ _x : ZMod p, (1 : ℂ) := by
              apply Finset.sum_congr rfl
              intro x _hx
              simp only [zero_add]
              rw [Complex.mul_conj', show ‖z x‖ = 1 by
                exact AddChar.norm_apply _ _]
              norm_num
            _ = (p : ℂ) := by simp
        rw [hzero, Complex.norm_natCast]
      · apply Finset.sum_le_sum
        intro h hh
        exact norm_correlation_le hp hc hs hshift hpow b
          (Finset.ne_of_mem_erase hh)
    _ = (p : ℝ) + (p - 1 : ℕ) *
        (((2 * poleEnvelope hs.length - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) + poleEnvelope hs.length) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 2
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
        Finset.card_univ, ZMod.card]

noncomputable def completeBound (p j : ℕ) : ℝ :=
  Real.sqrt ((p : ℝ) + (p - 1 : ℕ) *
    (((2 * poleEnvelope j - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) +
      poleEnvelope j))

theorem completeBound_nonneg (p j : ℕ) : 0 ≤ completeBound p j :=
  Real.sqrt_nonneg _

theorem norm_completeTwistedPhase_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 1 < p) {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ t ∈ hs, t + 1 < p)
    (hpow : poleEnvelope hs.length < p) (b : ZMod p) :
    ‖ReciprocalIntervalCompletion.completeTwistedPhase p
        (phase p c a hs) b‖ ≤ completeBound p hs.length := by
  have hsquare := norm_sum_twistedSequence_sq_le
    (a := a) hp hc hs hshift hpow b
  have hrad : 0 ≤ (p : ℝ) + (p - 1 : ℕ) *
      (((2 * poleEnvelope hs.length - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) + poleEnvelope hs.length) := by positivity
  have hsqrt : (completeBound p hs.length) ^ 2 =
      (p : ℝ) + (p - 1 : ℕ) *
        (((2 * poleEnvelope hs.length - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) + poleEnvelope hs.length) := by
    rw [completeBound, Real.sq_sqrt hrad]
  change ‖∑ x : ZMod p, twistedSequence p c a hs b x‖ ≤ _
  nlinarith [norm_nonneg (∑ x : ZMod p,
    twistedSequence p c a hs b x), completeBound_nonneg p hs.length]

/-- Completed short-sum estimate at arbitrary differencing depth. -/
theorem norm_shortPhase_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 1 < p) {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ t ∈ hs, t + 1 < p)
    (hpow : poleEnvelope hs.length < p)
    (M : ℤ) (m : ℕ) (hm : m ≤ p) :
    ‖ReciprocalIntervalCompletion.shortPhase p
        (phase p c a hs) M m‖ ≤
      (Real.log p + 1) * completeBound p hs.length := by
  apply ReciprocalIntervalCompletion.norm_shortPhase_le_log_of_complete_bound
    p (phase p c a hs) M m (completeBound p hs.length) hm
    (completeBound_nonneg p hs.length)
  intro b
  exact norm_completeTwistedPhase_le hp hc hs hshift hpow b

end IteratedReciprocalCompletion

end Erdos387

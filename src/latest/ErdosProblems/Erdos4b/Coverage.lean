import ErdosProblems.Erdos4b.VariableFiber

/-!
# Quantitative coverage from the degenerate companion weight

This file packages the exact finite inequality which turns the pinned
Maynard `S₂` sum into probability mass on the residue class hitting a
surviving prime.  The companion support has radius two, so the doubled
weight is the square of the ordinary first-family divisor sum.
-/

namespace Erdos4b

open Filter
open scoped BigOperators

noncomputable section

/-- Dividing a nonnegative raw residue weight by any upper bound for its
positive normalization gives a lower bound for the normalized mass. -/
theorem scaledTrivialResidueRawWeight_div_upper_le_mass
    {K m N q : ℕ} {A alpha Z : ℝ} (hq : 0 < q) (a : Fin q)
    (hmass : 0 < scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N)
    (hupper : scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N ≤ Z) :
    scaledTrivialResidueRawWeight K A alpha m N q a / Z ≤
      scaledTrivialResidueMass K A alpha m N q a := by
  unfold scaledTrivialResidueMass normalizeFiniteWeight
  rw [sum_scaledTrivialResidueRawWeight K A alpha m N q hq]
  exact div_le_div_of_nonneg_left
    (scaledTrivialResidueRawWeight_nonneg K A alpha m N q a)
    hmass hupper

/-- Probability mass assigned to the residue of the actual offset `m*p`
modulo `q`.  The zero-modulus branch makes the definition total. -/
noncomputable def scaledTrivialOffsetHitMass
    (K : ℕ) (A alpha : ℝ) (m N q p : ℕ) : ℝ :=
  if hq : 0 < q then
    scaledTrivialOffsetResidueMass K A alpha m N q
      ⟨(m * p) % q, Nat.mod_lt (m * p) hq⟩
  else 0

theorem scaledTrivialOffsetHitMass_nonneg
    (K : ℕ) (A alpha : ℝ) (m N q p : ℕ) :
    0 ≤ scaledTrivialOffsetHitMass K A alpha m N q p := by
  unfold scaledTrivialOffsetHitMass
  split_ifs with hq
  · exact scaledTrivialOffsetResidueMass_nonneg K A alpha m N q _
  · exact le_rfl

/-- Exact cancellation of the pre-sieve density in the ratio between the
pinned `S₂` scale and the normalization scale.  The only surviving loss is
the harmless natural/real cutoff logarithm ratio. -/
theorem variablePinnedKernelScale_div_normalizationScale
    {K N : ℕ} {alpha : ℝ} (hK : 0 < K) (hN : 2 < N)
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :
    variablePinnedKernelScale K alpha N /
        ((Nat.totient (BoundedGaps.Maynard.engelsmaMaynardModulus N) : ℝ) *
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N) =
      (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
          (N : ℝ)) *
        (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
          Real.log
            (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^ K := by
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let L := Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let Lr := Real.log
    (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
  have hW : (0 : ℝ) < W := by
    exact_mod_cast (show 0 < W by
      dsimp [W, BoundedGaps.Maynard.engelsmaMaynardModulus]
      exact primorial_pos _)
  have hphi : (0 : ℝ) < Nat.totient W := by
    exact_mod_cast Nat.totient_pos.mpr (by exact_mod_cast hW)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hR)
  have hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
    apply BoundedGaps.Maynard.maynardRealCutoff_gt_one
    · omega
    · have hfloor := Nat.floor_le
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ)) alpha)
      unfold BoundedGaps.Maynard.engelsmaMaynardRadius
        BoundedGaps.Maynard.maynardDivisorCutoff at hR
      have hpow : 1 < Real.rpow ((N - 1 : ℕ) : ℝ) alpha := by
        have hRcast : (1 : ℝ) <
            (⌊Real.rpow ((N - 1 : ℕ) : ℝ) alpha⌋₊ : ℕ) := by
          exact_mod_cast hR
        exact hRcast.trans_le hfloor
      have hbase : (1 : ℝ) < (N - 1 : ℕ) := by
        exact_mod_cast (by omega : 1 < N - 1)
      rcases (Real.one_lt_rpow_iff_of_pos (by positivity)).mp hpow with
        hgood | hbad
      · exact hgood.2
      · exact (not_lt_of_ge hbase.le hbad.1).elim
  have hLr : 0 < Lr := by
    dsimp [Lr]
    exact Real.log_pos hRreal
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  unfold variablePinnedKernelScale Erdos6.Maynard.tupleMaynardScale
  unfold BoundedGaps.Maynard.maynardSieveScale
  rw [Fintype.card_coe, card_primorialShifts]
  rw [BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div]
  change
    (((Nat.totient W : ℝ) / W) ^ 2 * L ^ 2 *
          (((Nat.totient W : ℝ) / W) * L) ^ (k + 1 - 1)) /
        ((Nat.totient W : ℝ) *
          (((Nat.totient W : ℝ) ^ (k + 1) * (N : ℝ) * Lr ^ (k + 1)) /
            (W : ℝ) ^ (k + 1 + 1))) =
      L / (N : ℝ) * (L / Lr) ^ (k + 1)
  simp only [Nat.add_one_sub_one, div_pow, pow_succ]
  field_simp [hW.ne', hphi.ne', hNR.ne', hLr.ne']
  rw [div_pow]
  field_simp [pow_ne_zero _ hW.ne']
  ring

/-- The exact finite coverage inequality.  Its numerator is the pinned
main term minus the two natural-endpoint progression-discrepancy sums; `Z`
is a common upper bound for the (possibly `q`-dependent) normalizations. -/
theorem auxiliaryPrimeInterval_scaledTrivialCoverage_lower
    {K m N p A₀ B : ℕ} {Ac alpha Z : ℝ}
    (hm : 0 < m) (hp : p.Prime) (hpN : p ≤ N)
    (hRp : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ p)
    (hpre : largeGapPreSieved
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) m p)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes
      (primorialShifts K)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N))
    (hA₀ : 0 < A₀) (hA₀B : A₀ ≤ B)
    (hRA₀ : BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ A₀)
    (hmargin : ∀ q ∈ Finset.Ico A₀ B,
      ∀ h : ↑(primorialShifts K),
        h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) < p)
    (hZpos : 0 < Z)
    (hmass : ∀ q ∈ auxiliaryPrimeInterval A₀ B,
      0 < scaledTrivialCompanionNormalizationMass K Ac alpha
        (fun _ => m) (fun _ => q) N)
    (hupper : ∀ q ∈ auxiliaryPrimeInterval A₀ B,
      scaledTrivialCompanionNormalizationMass K Ac alpha
        (fun _ => m) (fun _ => q) N ≤ Z) :
    (((auxiliaryPrimeInterval A₀ B).card : ℝ) *
          ∑ h : ↑(primorialShifts K),
            pinnedRestrictedArithmeticKernel K Ac alpha N h -
        (pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (B - 1) +
          pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (A₀ - 1))) / Z ≤
      ∑ q ∈ auxiliaryPrimeInterval A₀ B,
        scaledTrivialOffsetHitMass K Ac alpha m N q p := by
  classical
  let Q := auxiliaryPrimeInterval A₀ B
  have hqprime : ∀ q ∈ Q, q.Prime := by
    intro q hq
    exact (mem_auxiliaryPrimeInterval.mp hq).2.2
  have hqR : ∀ q ∈ Q,
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q := by
    intro q hq
    exact hRA₀.trans (mem_auxiliaryPrimeInterval.mp hq).1
  have hmarginQ : ∀ q ∈ Q, ∀ h : ↑(primorialShifts K),
      h.1 * (BoundedGaps.Maynard.engelsmaMaynardModulus N * q) < p := by
    intro q hq h
    exact hmargin q
      (Finset.mem_Ico.mpr ⟨(mem_auxiliaryPrimeInterval.mp hq).1,
        (mem_auxiliaryPrimeInterval.mp hq).2.1⟩) h
  have hpoint :
      (∑ q ∈ Q, ∑ h : ↑(primorialShifts K),
        scaledTrivialPointWeight K Ac alpha m N q
          (p - h.1 *
            (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))) =
        pinnedRestrictedPairSum K Ac alpha N p Q := by
    exact sum_pinned_pointWeights_eq_restrictedPairSum K Ac alpha m N p Q
      hp hRp hqprime hqR
      (fun q hq h => (hmarginQ q hq h).le) hcover
  have herr := abs_pinnedRestrictedPairErrorSum_le_weightedDiscrepancies
    (K := K) (N := N) (p := p) (A := A₀) (B := B)
    (Ac := Ac) (alpha := alpha) hp hRp hcover
    (fun q hq h => (hmargin q hq h).le) hA₀ hA₀B
  have hraw :
      (∑ q ∈ Q, ∑ h : ↑(primorialShifts K),
        scaledTrivialPointWeight K Ac alpha m N q
          (p - h.1 *
            (BoundedGaps.Maynard.engelsmaMaynardModulus N * q))) / Z ≤
        ∑ q ∈ Q,
          scaledTrivialOffsetHitMass K Ac alpha m N q p := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.sum_div]
    rw [← Finset.sum_div]
    have hqpos := (hqprime q hq).pos
    have hsum := sum_shift_pointWeights_le_residueRawWeight
      (K := K) (m := m) (N := N) (q := q) (p := p)
      (A := Ac) (alpha := alpha) hm hqpos hpN hpre
      (hmarginQ q hq)
    have hrawmass := scaledTrivialResidueRawWeight_div_upper_le_mass
      (K := K) (m := m) (N := N) (q := q) (A := Ac)
      (alpha := alpha) hqpos
      ⟨p % q, Nat.mod_lt p hqpos⟩ (hmass q hq) (hupper q hq)
    have hpush := scaledTrivialResidueMass_le_offset_hit
      K Ac alpha m N q p hqpos
    have hhit : scaledTrivialOffsetHitMass K Ac alpha m N q p =
        scaledTrivialOffsetResidueMass K Ac alpha m N q
          ⟨(m * p) % q, Nat.mod_lt (m * p) hqpos⟩ := by
      simp [scaledTrivialOffsetHitMass, hqpos]
    rw [hhit]
    exact (div_le_div_of_nonneg_right hsum hZpos.le).trans
      (hrawmass.trans hpush)
  apply le_trans ?_ hraw
  rw [hpoint, pinnedRestrictedPairSum_eq_main_add_error]
  have herrlower :
      -(pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (B - 1) +
          pinnedRestrictedWeightedDiscrepancySum K Ac alpha N (A₀ - 1)) ≤
        pinnedRestrictedPairErrorSum K Ac alpha N p Q := by
    exact (neg_le_of_abs_le herr)
  apply div_le_div_of_nonneg_right _ hZpos.le
  dsimp only [Q] at herrlower ⊢
  linarith

end

end Erdos4b

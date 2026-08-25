/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4.SingletonFiber
import ErdosProblems.Erdos4.SmoothParameters
import BoundedGaps.Maynard.ConcreteRoughModulusPrimeLogMass

/-!
# Uniform singleton asymptotics for the separated Erdős--Rankin weight

The decisive simplification in the final covering argument is to use the
one-shift tuple `{0}` in both divisor families.  There are then no
cross-coordinate collisions.  Both the unpinned quadratic and the pinned
quadratic are exact scalar squarefree reciprocal-totient means; their ratio
supplies the logarithmic concentration needed by the probabilistic cover.

The companion modulus contains a residual cofactor which need not be
squarefree.  The uniform Wirsing estimate in `BoundedGaps` is stated for a
squarefree augmented modulus.  The first section below transports it through
the natural-number radical, without changing either coprimality or the local
density.
-/

namespace Erdos4

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval
noncomputable section

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev natRadical (n : ℕ) : ℕ :=
  UniqueFactorizationMonoid.radical n

theorem prime_dvd_natRadical_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    p ∣ natRadical n ↔ p ∣ n := by
  exact UniqueFactorizationMonoid.dvd_radical_iff
    hp.squarefree.isRadical hn.ne'

theorem coprime_natRadical_right_iff (a : ℕ) {n : ℕ} (hn : 0 < n) :
    a.Coprime (natRadical n) ↔ a.Coprime n := by
  constructor
  · intro hrad
    by_contra hnot
    obtain ⟨p, hp, hpa, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, hpa, (prime_dvd_natRadical_iff hp hn).2 hpn⟩) hrad
  · intro hcop
    by_contra hrad
    obtain ⟨p, hp, hpa, hprad⟩ := Nat.Prime.not_coprime_iff_dvd.mp hrad
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, hpa, (prime_dvd_natRadical_iff hp hn).1 hprad⟩) hcop

theorem squarefreeCoprimeInvTotientMean_natRadical {W : ℕ} (hW : 0 < W)
    (Q : ℕ) :
    BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean (natRadical W) Q =
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W Q := by
  unfold BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
  apply Finset.sum_congr rfl
  intro n hn
  simp only [coprime_natRadical_right_iff n hW]

theorem coprimeHarmonicDensity_eq_primeFactorsProduct {W : ℕ}
    (hW : 0 < W) :
    BoundedGaps.Maynard.coprimeHarmonicDensity W =
      ∏ p ∈ W.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have htot : (W.totient : ℝ) =
      (W : ℝ) * ∏ p ∈ W.primeFactors, (1 - (p : ℝ)⁻¹) :=
    by
      have hq := Nat.totient_eq_mul_prod_factors W
      have hr := congrArg (fun z : ℚ => (z : ℝ)) hq
      push_cast at hr
      simpa using hr
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  unfold BoundedGaps.Maynard.coprimeHarmonicDensity
  apply (div_eq_iff hWR).2
  rw [htot]
  ring

theorem coprimeHarmonicDensity_natRadical {W : ℕ} (hW : 0 < W) :
    BoundedGaps.Maynard.coprimeHarmonicDensity (natRadical W) =
      BoundedGaps.Maynard.coprimeHarmonicDensity W := by
  rw [coprimeHarmonicDensity_eq_primeFactorsProduct (Nat.radical_pos W),
    coprimeHarmonicDensity_eq_primeFactorsProduct hW]
  rw [Nat.primeFactors_radical]

theorem primeLogDivisorMass_natRadical (W : ℕ) :
    BoundedGaps.Maynard.primeLogDivisorMass (natRadical W) =
      BoundedGaps.Maynard.primeLogDivisorMass W := by
  unfold BoundedGaps.Maynard.primeLogDivisorMass
  rw [Nat.primeFactors_radical]

/-- The all-endpoint Wirsing estimate, transported to an arbitrary positive
modulus by replacing it with its radical. -/
theorem exists_uniform_abs_singletonMean_sub_density_log_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ {W Q : ℕ}, 0 < W →
        |BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W Q -
            BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log Q| ≤
          10 * BoundedGaps.Maynard.coprimeHarmonicDensity W *
            (K + BoundedGaps.Maynard.primeLogDivisorMass W + Real.log 2) := by
  obtain ⟨K, hK, hbound⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le
  refine ⟨K, hK, ?_⟩
  intro W Q hW
  have hradPos : 0 < natRadical W := Nat.radical_pos W
  have hradSq : Squarefree (natRadical W) :=
    UniqueFactorizationMonoid.squarefree_radical
  have h := hbound (D := 0) (P := natRadical W) (Q := Q)
    hradPos (by simpa using hradSq)
  simpa [squarefreeCoprimeInvTotientMean_natRadical hW,
    coprimeHarmonicDensity_natRadical hW,
    primeLogDivisorMass_natRadical] using h

/-- A relative lower bound for the singleton mean at an arbitrary positive
modulus.  This is the form used for the first family. -/
theorem exists_uniform_singletonMean_lower_bound_general :
    ∃ K : ℝ, 0 < K ∧
      ∀ {W Q : ℕ}, 0 < W →
        20 * (K + BoundedGaps.Maynard.primeLogDivisorMass W + Real.log 2) ≤
            Real.log Q →
        BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log Q / 2 ≤
          BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W Q := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_abs_singletonMean_sub_density_log_le
  refine ⟨K, hK, ?_⟩
  intro W Q hW hlarge
  let δ := BoundedGaps.Maynard.coprimeHarmonicDensity W
  let E := K + BoundedGaps.Maynard.primeLogDivisorMass W + Real.log 2
  let M := BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W Q
  have hδ : 0 < δ := by
    dsimp [δ, BoundedGaps.Maynard.coprimeHarmonicDensity]
    exact div_pos
      (by exact_mod_cast Nat.totient_pos.mpr hW)
      (by exact_mod_cast hW)
  have habs : |M - δ * Real.log Q| ≤ 10 * δ * E := by
    simpa [M, δ, E] using hbound hW
  have hlower : -(10 * δ * E) ≤ M - δ * Real.log Q :=
    (abs_le.mp habs).1
  have hscaled : 20 * δ * E ≤ δ * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hlarge hδ.le
    dsimp [E] at this ⊢
    nlinarith
  nlinarith

/-! ### Exact separated singleton kernels -/

noncomputable def separatedSingletonFirstMean (RD Y : ℕ) : ℝ :=
  BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
    (primorial Y) (RD - 1)

noncomputable def separatedSingletonCompanionMean
    (RE w m : ℕ) : ℝ :=
  BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
    (primorial w * m) (RE - 1)

theorem separatedSingletonFirstQuadratic_eq (RD Y : ℕ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum singletonShift
        (separatedFirstSupport singletonShift RD Y)
        (separatedFirstCoefficient singletonShift RD Y (fun _ => 1)) =
      separatedSingletonFirstMean RD Y := by
  exact singleton_compatibleQuadratic_eq_mean RD (primorial Y)

theorem separatedSingletonCompanionQuadratic_eq (RE w m : ℕ) :
    BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum singletonShift
        (fullySeparatedCompanionSupport singletonShift RE (primorial w) m)
        (fullySeparatedCompanionCoefficient singletonShift RE
          (primorial w) m (fun _ => 1)) =
      separatedSingletonCompanionMean RE w m := by
  exact singleton_compatibleQuadratic_eq_mean RE (primorial w * m)

theorem separatedSingletonFirstPinnedKernel_eq_sq
    {RD Y : ℕ} (hRD : 2 ≤ RD) :
    rawPinnedPairTotientKernel
        (separatedFirstSupport singletonShift RD Y)
        (separatedFirstCoefficient singletonShift RD Y (fun _ => 1))
        singletonShiftOne =
      separatedSingletonFirstMean RD Y ^ 2 := by
  exact singleton_rawPinnedPairTotientKernel_eq_mean_sq hRD

theorem separatedSingletonCompanionPinnedKernel_eq_sq
    {RE w m : ℕ} (hRE : 2 ≤ RE) :
    rawPinnedPairTotientKernel
        (fullySeparatedCompanionSupport singletonShift RE (primorial w) m)
        (fullySeparatedCompanionCoefficient singletonShift RE
          (primorial w) m (fun _ => 1)) singletonShiftOne =
      separatedSingletonCompanionMean RE w m ^ 2 := by
  exact singleton_rawPinnedPairTotientKernel_eq_mean_sq hRE

theorem pinnedPairOffModulus_singleton
    (d e : ↑singletonShift → ℕ) :
    pinnedPairOffModulus singletonShift singletonShiftOne d e = 1 := by
  have herase : (Finset.univ : Finset ↑singletonShift).erase
      singletonShiftOne = ∅ := by
    ext h
    simp [singletonShift_subsingleton h singletonShiftOne]
  unfold pinnedPairOffModulus
  rw [herase]
  simp

theorem fullPinnedOffModulus_singleton
    (d e d' e' : ↑singletonShift → ℕ) :
    fullPinnedOffModulus singletonShift singletonShiftOne d e d' e' = 1 := by
  simp [fullPinnedOffModulus, pinnedPairOffModulus_singleton]

theorem primeVariableProgressionCount_mod_one
    (A B r : ℕ) :
    BoundedGaps.Maynard.primeVariableProgressionCount A B 1 r =
      (auxiliaryPrimeInterval A B).card := by
  unfold BoundedGaps.Maynard.primeVariableProgressionCount
    auxiliaryPrimeInterval
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ico, Nat.ModEq, Nat.mod_one]
  tauto

theorem fullPinnedCountError_singleton_eq_zero
    {RD RE w Y m p A B : ℕ}
    {d e d' e' : ↑singletonShift → ℕ}
    (hdmem : d ∈ separatedFirstSupport singletonShift RD Y)
    (hd'mem : d' ∈ separatedFirstSupport singletonShift RD Y)
    (hemem : e ∈ fullySeparatedCompanionSupport singletonShift RE
      (primorial w) m)
    (he'mem : e' ∈ fullySeparatedCompanionSupport singletonShift RE
      (primorial w) m)
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes singletonShift
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hrest : FullPinnedRestricted singletonShiftOne d e d' e')
    (hmargin : ∀ q ∈ Finset.Ico A B,
      (singletonShiftOne : ℕ) * (primorial w * q) < p) :
    fullPinnedCountError w m p (auxiliaryPrimeInterval A B)
        singletonShiftOne d e d' e' = 0 := by
  have hcount := pinnedQuadrupleQCount_primeInterval_eq_progressionCount
    singletonShiftOne hdmem hd'mem hemem he'mem hwY hcover hm hp
      hRDp hREp hREY hrest hmargin
  unfold fullPinnedCountError fullPinnedExpectedCount
  rw [hcount, fullPinnedOffModulus_singleton,
    primeVariableProgressionCount_mod_one]
  norm_num

theorem fullPinnedRestrictedErrorSum_singleton_eq_zero
    {RD RE w Y m p A B : ℕ}
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes singletonShift
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hmargin : ∀ q ∈ Finset.Ico A B,
      (singletonShiftOne : ℕ) * (primorial w * q) < p)
    (lambda : (↑singletonShift → ℕ) → (↑singletonShift → ℕ) → ℝ) :
    fullPinnedRestrictedErrorSum singletonShift
        (separatedFirstSupport singletonShift RD Y)
        (fullySeparatedCompanionSupport singletonShift RE (primorial w) m)
        lambda w m p (auxiliaryPrimeInterval A B) = 0 := by
  classical
  unfold fullPinnedRestrictedErrorSum
  apply Finset.sum_eq_zero
  intro h hh
  rw [singletonShift_subsingleton h singletonShiftOne]
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro d' hd'
  apply Finset.sum_eq_zero
  intro e' he'
  by_cases hrest : FullPinnedRestricted singletonShiftOne d e d' e'
  · rw [if_pos hrest,
      fullPinnedCountError_singleton_eq_zero hd hd' he he' hwY hcover hm
        hp hRDp hREp hREY hrest hmargin]
    ring
  · simp [hrest]

/-- For the one-shift separated tensor, every pinned prime count has modulus
one.  Hence the full pinned sum is exact, with no Bombieri--Vinogradov error. -/
theorem sum_pinned_scaledSingletonPointWeights_eq
    {RD RE w Y m p A B : ℕ}
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes singletonShift
      (primorial w))
    (hm : 0 < m) (hp : p.Prime)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hRDA : RD ≤ A) (hREA : RE ≤ A)
    (hmargin : ∀ q ∈ Finset.Ico A B,
      (singletonShiftOne : ℕ) * (primorial w * q) < p)
    (hpre : largeGapPreSieved Y m p)
    (hRDtwo : 2 ≤ RD) (hREtwo : 2 ≤ RE) :
    (∑ q ∈ auxiliaryPrimeInterval A B, ∑ h : ↑singletonShift,
      scaledDoubledPointWeight singletonShift
        (separatedFirstSupport singletonShift RD Y)
        (fullySeparatedCompanionSupport singletonShift RE (primorial w) m)
        (fullySeparatedDoubledCoefficient singletonShift RD RE Y
          (primorial w) m (fun _ => 1) (fun _ => 1))
        w m q (p - h.1 * (primorial w * q))) =
      ((auxiliaryPrimeInterval A B).card : ℝ) *
        (separatedSingletonFirstMean RD Y ^ 2 *
          separatedSingletonCompanionMean RE w m ^ 2) := by
  classical
  let D := separatedFirstSupport singletonShift RD Y
  let E := fullySeparatedCompanionSupport singletonShift RE (primorial w) m
  let a := separatedFirstCoefficient singletonShift RD Y (fun _ => 1)
  let b := fullySeparatedCompanionCoefficient singletonShift RE
    (primorial w) m (fun _ => 1)
  let lambda := fullySeparatedDoubledCoefficient singletonShift RD RE Y
    (primorial w) m (fun _ => 1) (fun _ => 1)
  have hQprime : ∀ q ∈ auxiliaryPrimeInterval A B, q.Prime := by
    intro q hq
    exact (mem_auxiliaryPrimeInterval.mp hq).2.2
  have hRDq : ∀ q ∈ auxiliaryPrimeInterval A B, RD ≤ q := by
    intro q hq
    exact hRDA.trans (mem_auxiliaryPrimeInterval.mp hq).1
  have hREq : ∀ q ∈ auxiliaryPrimeInterval A B, RE ≤ q := by
    intro q hq
    exact hREA.trans (mem_auxiliaryPrimeInterval.mp hq).1
  have hmarginQ : ∀ q ∈ auxiliaryPrimeInterval A B,
      ∀ h : ↑singletonShift, h.1 * (primorial w * q) < p := by
    intro q hq h
    rw [singletonShift_subsingleton h singletonShiftOne]
    exact hmargin q (Finset.mem_filter.mp hq).1
  rw [sum_pinned_scaledDoubledPointWeights_eq_restrictedSum
    (lambda := lambda) (Q := auxiliaryPrimeInterval A B) hwY hcover hm hp
      hRDp hREY hQprime hRDq hREq hmarginQ hpre]
  rw [fullPinnedRestrictedSum_eq_main_add_error]
  have herr : fullPinnedRestrictedErrorSum singletonShift D E lambda
      w m p (auxiliaryPrimeInterval A B) = 0 := by
    exact fullPinnedRestrictedErrorSum_singleton_eq_zero hwY hcover hm hp
      hRDp hREp hREY hmargin lambda
  rw [show fullPinnedRestrictedErrorSum singletonShift D E lambda
      w m p (auxiliaryPrimeInterval A B) = 0 by exact herr, add_zero]
  have hsupport := fullySeparatedSupportConditions hm hp
    (primorial_dvd_primorial hwY) hcover hRDp hREp hREY
  have hkernel := fullPinnedRestrictedArithmeticKernel_tensor hsupport a b
  rw [show lambda = fun d e => a d * b e by rfl, hkernel]
  have huniv : (Finset.univ : Finset ↑singletonShift) = {singletonShiftOne} := by
    ext h
    simp [singletonShift_subsingleton h singletonShiftOne]
  rw [show (∑ h : ↑singletonShift,
      rawPinnedPairTotientKernel D a h *
        rawPinnedPairTotientKernel E b h) =
      rawPinnedPairTotientKernel D a singletonShiftOne *
        rawPinnedPairTotientKernel E b singletonShiftOne by
      rw [show (∑ h : ↑singletonShift,
          rawPinnedPairTotientKernel D a h *
            rawPinnedPairTotientKernel E b h) =
          ∑ h ∈ (Finset.univ : Finset ↑singletonShift),
            rawPinnedPairTotientKernel D a h *
              rawPinnedPairTotientKernel E b h by simp]
      rw [huniv]
      simp]
  rw [show rawPinnedPairTotientKernel D a singletonShiftOne =
      separatedSingletonFirstMean RD Y ^ 2 by
      exact separatedSingletonFirstPinnedKernel_eq_sq hRDtwo]
  rw [show rawPinnedPairTotientKernel E b singletonShiftOne =
      separatedSingletonCompanionMean RE w m ^ 2 by
      exact separatedSingletonCompanionPinnedKernel_eq_sq hREtwo]

/-! ### Singleton residue masses -/

noncomputable def scaledSingletonPointWeight
    (RD RE w Y m q n : ℕ) : ℝ :=
  doubledSelbergWeight singletonShift
    (separatedFirstSupport singletonShift RD Y)
    (fullySeparatedCompanionSupport singletonShift RE (primorial w) m)
    (fullySeparatedDoubledCoefficient singletonShift RD RE Y
      (primorial w) m (fun _ => 1) (fun _ => 1))
    m (primorial w * q) n

theorem scaledSingletonPointWeight_nonneg
    (RD RE w Y m q n : ℕ) :
    0 ≤ scaledSingletonPointWeight RD RE w Y m q n :=
  doubledSelbergWeight_nonneg _ _ _ _ _ _ _

noncomputable def scaledSingletonNormalizationError
    (RD RE w Y m q T : ℕ) : ℝ :=
  doubledSelbergFilteredNormalizationError singletonShift
    (separatedFirstSupport singletonShift RD Y)
    (fullySeparatedCompanionSupport singletonShift RE (primorial w) m)
    (fullySeparatedDoubledCoefficient singletonShift RD RE Y
      (primorial w) m (fun _ => 1) (fun _ => 1))
    (primorial w) m (primorial w * q) T

noncomputable def scaledSingletonNormalizationMass
    (RD RE w Y m q T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 T,
    if largeGapPreSieved w m n then
      scaledSingletonPointWeight RD RE w Y m q n
    else 0

theorem scaledSingletonNormalizationMass_eq_main_add_error
    {RD RE w Y m q T : ℕ}
    (hw : 2 ≤ w) (hm : 0 < m) (hq : q.Prime) (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes singletonShift
      (primorial w))
    (hRDq : RD ≤ q) (hREq : RE ≤ q) (hREY : RE ≤ Y) :
    scaledSingletonNormalizationMass RD RE w Y m q T =
      (T : ℝ) * preSieveDensity w m *
          (separatedSingletonFirstMean RD Y *
            separatedSingletonCompanionMean RE w m) +
        scaledSingletonNormalizationError RD RE w Y m q T := by
  have h := preSievedScaledFullySeparatedDoubledWeightSum_eq_main_add_error
    (H := singletonShift) (RD := RD) (RE := RE) (w := w) (Y := Y)
      (m := m) (q := q) (T := T) hw hm hq hwY hcover hRDq hREq hREY
      (fun _ => 1) (fun _ => 1)
  simpa [scaledSingletonNormalizationMass, scaledSingletonPointWeight,
    scaledSingletonNormalizationError,
    separatedSingletonFirstQuadratic_eq,
    separatedSingletonCompanionQuadratic_eq] using h

noncomputable def scaledSingletonResidueRawWeight
    (RD RE w Y m T q : ℕ) (a : Fin q) : ℝ :=
  ∑ n ∈ Finset.Icc 0 T,
    if largeGapPreSieved w m n ∧ n % q = a.1 then
      scaledSingletonPointWeight RD RE w Y m q n
    else 0

theorem scaledSingletonResidueRawWeight_nonneg
    (RD RE w Y m T q : ℕ) (a : Fin q) :
    0 ≤ scaledSingletonResidueRawWeight RD RE w Y m T q a := by
  unfold scaledSingletonResidueRawWeight
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact scaledSingletonPointWeight_nonneg RD RE w Y m q n
  · exact le_rfl

theorem sum_scaledSingletonResidueRawWeight
    (RD RE w Y m T q : ℕ) (hq : 0 < q) :
    (∑ a : Fin q, scaledSingletonResidueRawWeight RD RE w Y m T q a) =
      scaledSingletonNormalizationMass RD RE w Y m q T := by
  classical
  unfold scaledSingletonResidueRawWeight scaledSingletonNormalizationMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpre : largeGapPreSieved w m n
  · simp only [hpre, true_and, if_true]
    let a : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
    rw [Finset.sum_eq_single a]
    · simp [a]
    · intro b hb hba
      have hne : n % q ≠ b.1 := by
        intro heq
        apply hba
        exact Fin.ext heq.symm
      simp [hne]
    · simp
  · simp [hpre]

noncomputable def scaledSingletonResidueMass
    (RD RE w Y m T q : ℕ) (a : Fin q) : ℝ :=
  normalizeFiniteWeight
    (scaledSingletonResidueRawWeight RD RE w Y m T q) a

theorem scaledSingletonResidueMass_nonneg
    (RD RE w Y m T q : ℕ) (a : Fin q) :
    0 ≤ scaledSingletonResidueMass RD RE w Y m T q a := by
  exact normalizeFiniteWeight_nonneg _
    (scaledSingletonResidueRawWeight_nonneg RD RE w Y m T q) a

theorem sum_scaledSingletonResidueMass_eq_one
    {RD RE w Y m T q : ℕ} (hq : 0 < q)
    (hmass : 0 < scaledSingletonNormalizationMass RD RE w Y m q T) :
    ∑ a : Fin q, scaledSingletonResidueMass RD RE w Y m T q a = 1 := by
  apply sum_normalizeFiniteWeight_eq_one
  rw [sum_scaledSingletonResidueRawWeight RD RE w Y m T q hq]
  exact hmass

theorem scaledSingletonPointWeight_le_residueRawWeight_hit
    {RD RE w Y m T q p : ℕ}
    (hm : 0 < m) (hq : 0 < q) (hpT : p ≤ T)
    (hpre : largeGapPreSieved w m p)
    (hmargin : primorial w * q < p) :
    scaledSingletonPointWeight RD RE w Y m q
        (p - primorial w * q) ≤
      scaledSingletonResidueRawWeight RD RE w Y m T q
        ⟨p % q, Nat.mod_lt p hq⟩ := by
  classical
  let n := p - primorial w * q
  have hnmem : n ∈ Finset.Icc 0 T := by
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.sub_le _ _).trans hpT⟩
  have hnpre : largeGapPreSieved w m n := by
    have := largeGapPreSieved_sub_scaledShift
      (w := w) (m := m) (q := q) (p := p) (h := 1)
      hm hq (by simpa [n] using hmargin) hpre
    simpa [n] using this
  have hnmod : n % q = p % q := by
    have := sub_scaledShift_mod (primorial_pos w) hq
      (show 1 * (primorial w * q) ≤ p by simpa using hmargin.le)
    simpa [n] using this
  unfold scaledSingletonResidueRawWeight
  let f : ℕ → ℝ := fun x =>
    if largeGapPreSieved w m x ∧ x % q = p % q then
      scaledSingletonPointWeight RD RE w Y m q x else 0
  change scaledSingletonPointWeight RD RE w Y m q n ≤
    ∑ x ∈ Finset.Icc 0 T, f x
  have hterm : f n = scaledSingletonPointWeight RD RE w Y m q n := by
    simp [f, hnpre, hnmod]
  rw [← hterm]
  apply Finset.single_le_sum (s := Finset.Icc 0 T)
  · intro x hx
    dsimp [f]
    split_ifs
    · exact scaledSingletonPointWeight_nonneg RD RE w Y m q x
    · exact le_rfl
  · exact hnmem

/-- With the zero singleton shift, the pinned point is the prime itself. -/
theorem scaledSingletonPointWeight_le_residueRawWeight_self
    {RD RE w Y m T q p : ℕ}
    (hq : 0 < q) (hpT : p ≤ T) (hpre : largeGapPreSieved w m p) :
    scaledSingletonPointWeight RD RE w Y m q p ≤
      scaledSingletonResidueRawWeight RD RE w Y m T q
        ⟨p % q, Nat.mod_lt p hq⟩ := by
  classical
  unfold scaledSingletonResidueRawWeight
  let f : ℕ → ℝ := fun n =>
    if largeGapPreSieved w m n ∧ n % q = p % q then
      scaledSingletonPointWeight RD RE w Y m q n else 0
  change scaledSingletonPointWeight RD RE w Y m q p ≤
    ∑ n ∈ Finset.Icc 0 T, f n
  have hpmem : p ∈ Finset.Icc 0 T :=
    Finset.mem_Icc.mpr ⟨Nat.zero_le _, hpT⟩
  have hterm : f p = scaledSingletonPointWeight RD RE w Y m q p := by
    simp [f, hpre]
  rw [← hterm]
  apply Finset.single_le_sum (s := Finset.Icc 0 T)
  · intro n hn
    dsimp [f]
    split_ifs
    · exact scaledSingletonPointWeight_nonneg RD RE w Y m q n
    · exact le_rfl
  · exact hpmem

theorem scaledSingletonResidueRawWeight_div_upper_le_mass
    {RD RE w Y m T q : ℕ} {Z : ℝ} (hq : 0 < q) (a : Fin q)
    (hmass : 0 < scaledSingletonNormalizationMass RD RE w Y m q T)
    (hupper : scaledSingletonNormalizationMass RD RE w Y m q T ≤ Z) :
    scaledSingletonResidueRawWeight RD RE w Y m T q a / Z ≤
      scaledSingletonResidueMass RD RE w Y m T q a := by
  unfold scaledSingletonResidueMass normalizeFiniteWeight
  rw [sum_scaledSingletonResidueRawWeight RD RE w Y m T q
    hq]
  exact div_le_div_of_nonneg_left
    (scaledSingletonResidueRawWeight_nonneg RD RE w Y m T q a)
    hmass hupper

theorem sum_singletonShift (f : ↑singletonShift → ℝ) :
    ∑ h : ↑singletonShift, f h = f singletonShiftOne := by
  classical
  have huniv : (Finset.univ : Finset ↑singletonShift) =
      {singletonShiftOne} := by
    ext h
    simp [singletonShift_subsingleton h singletonShiftOne]
  calc
    (∑ h : ↑singletonShift, f h) =
        ∑ h ∈ (Finset.univ : Finset ↑singletonShift), f h := by simp
    _ = ∑ h ∈ ({singletonShiftOne} : Finset ↑singletonShift), f h := by
      rw [huniv]
    _ = f singletonShiftOne := by simp

/-- The probability mass assigned by the singleton residue distribution to
the residue hit by `p`.  The zero-modulus branch makes this a total function
on natural moduli; it is never used for the prime moduli below. -/
noncomputable def scaledSingletonHitMass
    (RD RE w Y m T q p : ℕ) : ℝ :=
  if hq : 0 < q then
    scaledSingletonResidueMass RD RE w Y m T q
      ⟨p % q, Nat.mod_lt p hq⟩
  else 0

/-- Quantitative coverage supplied by all auxiliary primes in one interval.
The denominator may vary with `q`; a common upper bound `Z` is enough. -/
theorem auxiliaryPrimeInterval_singletonCoverage_lower
    {RD RE w Y m T p A B : ℕ} {Z : ℝ}
    (hwY : w ≤ Y)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes singletonShift
      (primorial w))
    (hm : 0 < m) (hp : p.Prime) (hpT : p ≤ T)
    (hRDp : RD ≤ p) (hREp : RE ≤ p) (hREY : RE ≤ Y)
    (hRDA : RD ≤ A) (hREA : RE ≤ A)
    (hpreY : largeGapPreSieved Y m p)
    (hprew : largeGapPreSieved w m p)
    (hRDtwo : 2 ≤ RD) (hREtwo : 2 ≤ RE)
    (hmass : ∀ q ∈ auxiliaryPrimeInterval A B,
      0 < scaledSingletonNormalizationMass RD RE w Y m q T)
    (hupper : ∀ q ∈ auxiliaryPrimeInterval A B,
      scaledSingletonNormalizationMass RD RE w Y m q T ≤ Z) :
    ((auxiliaryPrimeInterval A B).card : ℝ) *
          (separatedSingletonFirstMean RD Y ^ 2 *
            separatedSingletonCompanionMean RE w m ^ 2) / Z ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        scaledSingletonHitMass RD RE w Y m T q p := by
  classical
  have hpinned := sum_pinned_scaledSingletonPointWeights_eq
    (B := B) hwY hcover hm hp hRDp hREp hREY hRDA hREA
      (fun q hq => by simp [hp.pos]) hpreY hRDtwo hREtwo
  have hpoint :
      (∑ q ∈ auxiliaryPrimeInterval A B,
        scaledSingletonPointWeight RD RE w Y m q p) =
        ((auxiliaryPrimeInterval A B).card : ℝ) *
          (separatedSingletonFirstMean RD Y ^ 2 *
            separatedSingletonCompanionMean RE w m ^ 2) := by
    calc
      (∑ q ∈ auxiliaryPrimeInterval A B,
          scaledSingletonPointWeight RD RE w Y m q p) =
          ∑ q ∈ auxiliaryPrimeInterval A B, ∑ h : ↑singletonShift,
            scaledDoubledPointWeight singletonShift
              (separatedFirstSupport singletonShift RD Y)
              (fullySeparatedCompanionSupport singletonShift RE
                (primorial w) m)
              (fullySeparatedDoubledCoefficient singletonShift RD RE Y
                (primorial w) m (fun _ ↦ 1) (fun _ ↦ 1))
              w m q (p - h.1 * (primorial w * q)) := by
        apply Finset.sum_congr rfl
        intro q hq
        symm
        simpa [scaledSingletonPointWeight, scaledDoubledPointWeight] using
          (sum_singletonShift (fun h : ↑singletonShift ↦
            scaledDoubledPointWeight singletonShift
              (separatedFirstSupport singletonShift RD Y)
              (fullySeparatedCompanionSupport singletonShift RE
                (primorial w) m)
              (fullySeparatedDoubledCoefficient singletonShift RD RE Y
                (primorial w) m (fun _ ↦ 1) (fun _ ↦ 1))
              w m q (p - h.1 * (primorial w * q))))
      _ = _ := hpinned
  rw [← hpoint, Finset.sum_div]
  apply Finset.sum_le_sum
  intro q hq
  have hqprime := (mem_auxiliaryPrimeInterval.mp hq).2.2
  have hraw := scaledSingletonPointWeight_le_residueRawWeight_self
    (RD := RD) (RE := RE) (Y := Y) hqprime.pos hpT hprew
  calc
    scaledSingletonPointWeight RD RE w Y m q p / Z ≤
        scaledSingletonResidueRawWeight RD RE w Y m T q
          ⟨p % q, Nat.mod_lt p hqprime.pos⟩ / Z := by
      exact div_le_div_of_nonneg_right hraw (by
        have hZpos := (hmass q hq).trans_le (hupper q hq)
        exact hZpos.le)
    _ ≤ scaledSingletonHitMass RD RE w Y m T q p := by
      have hhit : scaledSingletonHitMass RD RE w Y m T q p =
          scaledSingletonResidueMass RD RE w Y m T q
            ⟨p % q, Nat.mod_lt p hqprime.pos⟩ := by
        simp [scaledSingletonHitMass, hqprime.pos]
      rw [hhit]
      exact scaledSingletonResidueRawWeight_div_upper_le_mass hqprime.pos _
        (hmass q hq) (hupper q hq)

end
end Erdos4

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement
import ErdosProblems.Erdos297.DeletedSetSums
import ErdosProblems.Erdos297.EntropyTypical
import ErdosProblems.Erdos297.GoodFactorization
import ErdosProblems.Erdos297.GoodSetDensity
import ErdosProblems.Erdos297.LcmTail
import ErdosProblems.Erdos297.LocalLimit
import ErdosProblems.Erdos297.LogisticNormalization
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos297.Riemann
import ErdosProblems.Erdos297.WeightedPowerset

/-!
# Erdős Problem 297: assembly of the lower bound

This file turns the two quantitative outputs of the Liu--Sawhney
construction into a lower bound for the original counting function.  The
outputs are:

* an exact reciprocal-sum event of mass at least `exp (-o(N))`; and
* a uniform upper bound `exp (-gamma * N + o(N))` for every atom in that
  event.

The first part of the file is deliberately independent of the arithmetic and
Fourier construction.  This makes explicit the finite mass-to-cardinality
argument and the passage from exponential cardinality estimates to the
normalized logarithm in `Statement.lean`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos297

noncomputable section

attribute [local instance] Classical.propDecidable

open GoodFactorization

/-! ## Exact events and their mass -/

/-- Subsets of `I` whose reciprocal sum is exactly one in `ℚ`. -/
def exactReciprocalEvent (I : Finset ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter fun A ↦ UnitFractions.rec_sum A = 1

/-- The mass of the exact reciprocal-sum event for the finite product law
used by the Fourier argument. -/
def exactReciprocalMass (I : Finset ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ A ∈ exactReciprocalEvent I, EntropyTypical.bernoulliWeight I p A

theorem exactReciprocalMass_eq_sum_ite (I : Finset ℕ) (p : ℕ → ℝ) :
    exactReciprocalMass I p =
      ∑ A ∈ I.powerset,
        if UnitFractions.rec_sum A = 1 then
          EntropyTypical.bernoulliWeight I p A else 0 := by
  rw [exactReciprocalMass, exactReciprocalEvent, Finset.sum_filter]

/-- The local-limit module and this counting assembly use the same exact
reciprocal event and product weight. -/
theorem exactReciprocalMass_eq_localLimit (I : Finset ℕ) (p : ℕ → ℝ) :
    exactReciprocalMass I p = LocalLimit.exactReciprocalMass I p 1 := by
  rw [exactReciprocalMass_eq_sum_ite]
  rfl

/-- The full arithmetic set to which the Liu--Sawhney local limit is applied
at the source scales. -/
def liuGoodSet (N : ℕ) : Finset ℕ :=
  goodDenominators N (M N) (S N)

theorem liuGoodSet_subset_denominators {N : ℕ} (hM : 1 ≤ M N) :
    liuGoodSet N ⊆ denominators N := by
  intro n hn
  rw [mem_denominators]
  have hgood : n ∈ goodDenominators N (M N) (S N) := hn
  have hIccMem : n ∈ Finset.Icc (M N) N :=
    goodDenominators_subset_Icc N (M N) (S N) hgood
  have hIcc := Finset.mem_Icc.mp hIccMem
  exact ⟨hM.trans hIcc.1, hIcc.2⟩

theorem liuGoodSet_pos {N n : ℕ} (hM : 1 ≤ M N)
    (hn : n ∈ liuGoodSet N) : 0 < n :=
  goodDenominator_pos hM hn

@[simp] theorem mem_exactReciprocalEvent {I A : Finset ℕ} :
    A ∈ exactReciprocalEvent I ↔
      A ⊆ I ∧ UnitFractions.rec_sum A = 1 := by
  simp [exactReciprocalEvent]

/-- Every exact event supported on available denominators is a family counted
by `count N`. -/
theorem exactReciprocalEvent_subset_representations {N : ℕ} {I : Finset ℕ}
    (hI : I ⊆ denominators N) :
    exactReciprocalEvent I ⊆ representations N := by
  intro A hA
  rw [mem_exactReciprocalEvent] at hA
  rw [mem_representations]
  exact ⟨hA.1.trans hI, hA.2⟩

theorem exactReciprocalEvent_card_le_count {N : ℕ} {I : Finset ℕ}
    (hI : I ⊆ denominators N) :
    (exactReciprocalEvent I).card ≤ count N := by
  rw [count]
  exact card_le_card (exactReciprocalEvent_subset_representations hI)

/-! ## Logistic weights at a finite scale -/

/-- The continuum logistic profile sampled at the denominator `n` on scale
`N`. -/
def scaledSelectionProbability (lam : ℝ) (N n : ℕ) : ℝ :=
  selectionProbability lam ((n : ℝ) / N)

/-- The finite log-partition summand in the lower-bound calculation. -/
def scaledLogPartition (lam : ℝ) (N n : ℕ) : ℝ :=
  Real.log (1 + Real.exp (-(lam * (N : ℝ) / n)))

lemma selectionProbability_eq_tiltedProbability {lam x : ℝ} (hx : x ≠ 0) :
    selectionProbability lam x = tiltedProbability (lam / x) := by
  rw [selectionProbability, if_neg hx, tiltedProbability, Real.exp_neg]
  have he : Real.exp (lam / x) ≠ 0 := Real.exp_ne_zero _
  field_simp [he]
  ring

lemma scaledSelectionProbability_eq_tiltedProbability
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    scaledSelectionProbability lam N n =
      tiltedProbability (lam * (N : ℝ) / n) := by
  rw [scaledSelectionProbability,
    selectionProbability_eq_tiltedProbability (by positivity)]
  congr 1
  field_simp

lemma scaledSelectionProbability_pos
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    0 < scaledSelectionProbability lam N n := by
  rw [scaledSelectionProbability_eq_tiltedProbability hN hn]
  exact tiltedProbability_pos _

lemma scaledSelectionProbability_lt_one
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    scaledSelectionProbability lam N n < 1 := by
  rw [scaledSelectionProbability_eq_tiltedProbability hN hn]
  exact tiltedProbability_lt_one _

lemma scaled_log_selectionProbability
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Real.log (scaledSelectionProbability lam N n) =
      -(lam * (N : ℝ) / n) - scaledLogPartition lam N n := by
  rw [scaledSelectionProbability_eq_tiltedProbability hN hn,
    log_tiltedProbability]
  rfl

lemma scaled_log_one_sub_selectionProbability
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Real.log (1 - scaledSelectionProbability lam N n) =
      -scaledLogPartition lam N n := by
  rw [scaledSelectionProbability_eq_tiltedProbability hN hn,
    log_one_sub_tiltedProbability]
  rfl

lemma scaled_logOdds
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Real.log (1 - scaledSelectionProbability lam N n) -
        Real.log (scaledSelectionProbability lam N n) =
      lam * (N : ℝ) / n := by
  rw [scaled_log_selectionProbability hN hn,
    scaled_log_one_sub_selectionProbability hN hn]
  ring

lemma subsetLinear_eq_sum_of_subset {I A : Finset ℕ} {f : ℕ → ℝ}
    (hA : A ⊆ I) :
    EntropyTypical.subsetLinear I f A = ∑ n ∈ A, f n := by
  rw [EntropyTypical.subsetLinear]
  have hfilter : I.filter (fun n ↦ n ∈ A) = A := by
    ext n
    simp only [Finset.mem_filter]
    tauto
  calc
    (∑ i ∈ I, if i ∈ A then f i else 0) =
        ∑ i ∈ I.filter (fun n ↦ n ∈ A), f i := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ A, f i := by rw [hfilter]

lemma cast_rec_sum (A : Finset ℕ) :
    (((UnitFractions.rec_sum A : ℚ) : ℝ)) =
      ∑ n ∈ A, (1 : ℝ) / n := by
  simp [UnitFractions.rec_sum]

/-- Exact information identity for the unperturbed logistic product law.
The selected-coordinate contribution collapses to `lam * N` on the exact
reciprocal-sum event. -/
theorem logisticInformation_eq
    {lam : ℝ} {N : ℕ} (hN : 0 < N) {I A : Finset ℕ}
    (hIpos : ∀ n ∈ I, 0 < n) (hA : A ⊆ I) :
    EntropyTypical.bernoulliInformation I
        (scaledSelectionProbability lam N) A =
      lam * (N : ℝ) * ((UnitFractions.rec_sum A : ℚ) : ℝ) +
        ∑ n ∈ I, scaledLogPartition lam N n := by
  rw [EntropyTypical.bernoulliInformation_eq]
  have hbase :
      (∑ n ∈ I, -Real.log (1 - scaledSelectionProbability lam N n)) =
        ∑ n ∈ I, scaledLogPartition lam N n := by
    apply Finset.sum_congr rfl
    intro n hnI
    rw [scaled_log_one_sub_selectionProbability hN (hIpos n hnI)]
    ring
  rw [hbase, subsetLinear_eq_sum_of_subset hA]
  have hodds :
      (∑ n ∈ A,
          (Real.log (1 - scaledSelectionProbability lam N n) -
            Real.log (scaledSelectionProbability lam N n))) =
        ∑ n ∈ A, lam * (N : ℝ) / n := by
    apply Finset.sum_congr rfl
    intro n hnA
    exact scaled_logOdds hN (hIpos n (hA hnA))
  rw [hodds, cast_rec_sum]
  rw [Finset.mul_sum]
  ring_nf

theorem logisticInformation_eq_on_exactEvent
    {lam : ℝ} {N : ℕ} (hN : 0 < N) {I A : Finset ℕ}
    (hIpos : ∀ n ∈ I, 0 < n) (hA : A ∈ exactReciprocalEvent I) :
    EntropyTypical.bernoulliInformation I
        (scaledSelectionProbability lam N) A =
      lam * (N : ℝ) + ∑ n ∈ I, scaledLogPartition lam N n := by
  rw [logisticInformation_eq hN hIpos (mem_exactReciprocalEvent.mp hA).1,
    (mem_exactReciprocalEvent.mp hA).2]
  norm_num

/-- Exact atom formula for the unperturbed logistic law on an exact
reciprocal-sum subset. -/
theorem logisticWeight_eq_on_exactEvent
    {lam : ℝ} {N : ℕ} (hN : 0 < N) {I A : Finset ℕ}
    (hIpos : ∀ n ∈ I, 0 < n) (hA : A ∈ exactReciprocalEvent I) :
    EntropyTypical.bernoulliWeight I
        (scaledSelectionProbability lam N) A =
      Real.exp (-(lam * (N : ℝ) +
        ∑ n ∈ I, scaledLogPartition lam N n)) := by
  rw [EntropyTypical.bernoulliWeight_eq_exp_neg_information]
  · rw [logisticInformation_eq_on_exactEvent hN hIpos hA]
  · intro n hnI
    exact scaledSelectionProbability_pos hN (hIpos n hnI)
  · intro n hnI
    exact scaledSelectionProbability_lt_one hN (hIpos n hnI)

/-! ## Exact common rescaling of a finite reciprocal expectation -/

/-- Expected reciprocal sum for independent coordinates with marginals `p`.
Only the finite first-moment expression is needed here. -/
def reciprocalExpectation (I : Finset ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ n ∈ I, p n / n

/-- The common multiplier which corrects a nonzero retained expectation to
one. -/
def reciprocalRescalingFactor (I : Finset ℕ) (p : ℕ → ℝ) : ℝ :=
  (reciprocalExpectation I p)⁻¹

/-- Probabilities after common rescaling. -/
def rescaledProbability (I : Finset ℕ) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  reciprocalRescalingFactor I p * p n

theorem reciprocalExpectation_rescaled {I : Finset ℕ} {p : ℕ → ℝ}
    (hne : reciprocalExpectation I p ≠ 0) :
    reciprocalExpectation I (rescaledProbability I p) = 1 := by
  simp only [reciprocalExpectation, rescaledProbability,
    reciprocalRescalingFactor, mul_div_assoc, ← Finset.mul_sum]
  exact inv_mul_cancel₀ hne

theorem reciprocalExpectation_scaledSelectionProbability
    (lam : ℝ) (N : ℕ) (I : Finset ℕ) :
    reciprocalExpectation I (scaledSelectionProbability lam N) =
      ∑ n ∈ I, selectionProbability lam ((n : ℝ) / N) / n := by
  rfl

theorem tendsto_full_reciprocalExpectation {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fun N : ℕ ↦ reciprocalExpectation (Icc 1 N)
        (scaledSelectionProbability lam N))
      atTop (nhds (moment lam)) := by
  simpa [reciprocalExpectation_scaledSelectionProbability] using
    tendsto_sum_Icc_selectionProbability_div hlam

lemma freeEnergyKernel_eq_scaledLogPartition
    {lam : ℝ} {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    freeEnergyKernel lam ((n : ℝ) / N) = scaledLogPartition lam N n := by
  rw [freeEnergyKernel, if_neg (by positivity)]
  unfold scaledLogPartition
  congr 2
  field_simp

/-- The finite log-partition sum has normalized limit `gamma lam - lam`. -/
theorem tendsto_scaledLogPartition_sum_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Icc 1 N, scaledLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)) := by
  have h := tendsto_rightRiemannSum_freeEnergyKernel hlam
  have heq :
      (fun N : ℕ ↦ (∑ n ∈ Icc 1 N, scaledLogPartition lam N n) / N)
        =ᶠ[atTop] rightRiemannSum (freeEnergyKernel lam) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    symm
    rw [← Finset.Ico_succ_right_eq_Icc 1 N]
    change rightRiemannSum (freeEnergyKernel lam) N =
      (∑ n ∈ Ico 1 (N + 1), scaledLogPartition lam N n) / N
    rw [← Finset.sum_Ico_add (fun n : ℕ ↦ scaledLogPartition lam N n) 0 N 1]
    simp only [Nat.Ico_zero_eq_range, rightRiemannSum, Finset.sum_div]
    congr 1
    funext k
    rw [freeEnergyKernel_eq_scaledLogPartition hN (by omega)]
    simp [Nat.add_comm]
  have hlim := h.congr' heq.symm
  convert hlim using 1
  congr 1
  simp only [gamma]
  ring

/-- Deleting `o(N)` sampled coordinates does not change the normalized
log-partition limit. -/
theorem tendsto_scaledLogPartition_sum_div_of_complement_card_isLittleO
    {I : ℕ → Finset ℕ}
    (hI : ∀ᶠ N : ℕ in atTop, I N ⊆ Finset.Icc 1 N)
    (hcompl :
      (fun N : ℕ ↦ (((Finset.Icc 1 N \ I N).card : ℕ) : ℝ))
        =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fun N : ℕ ↦ (∑ n ∈ I N, scaledLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)) := by
  let D : ℕ → Finset ℕ := fun N ↦ Finset.Icc 1 N \ I N
  have hdel : Tendsto
      (fun N : ℕ ↦ (∑ n ∈ D N, scaledLogPartition lam N n) / N)
      atTop (nhds 0) := by
    have hd := DeletedSetSums.tendsto_discreteLogPartition_sum_div D
      (by simpa only [D] using hcompl) hlam.le
    apply hd.congr'
    filter_upwards with N
    congr 2
    funext n
    unfold scaledLogPartition
    congr 3
    ring
  have hsub := (tendsto_scaledLogPartition_sum_div hlam).sub hdel
  have hsub' : Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.Icc 1 N, scaledLogPartition lam N n) / N -
          (∑ n ∈ D N, scaledLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)) := by
    simpa using hsub
  apply hsub'.congr'
  filter_upwards [hI] with N hIN
  have hsum := Finset.sum_sdiff (f := scaledLogPartition lam N) hIN
  dsimp [D]
  rw [← sub_div]
  congr 1
  symm
  exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsum)

/-- The concrete arithmetic good set retains the full critical
log-partition density. -/
theorem tendsto_liuGoodSet_scaledLogPartition_sum_div {lam : ℝ}
    (hlam : 0 < lam) :
    Tendsto
      (fun N : ℕ ↦ (∑ n ∈ liuGoodSet N,
        scaledLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)) := by
  apply tendsto_scaledLogPartition_sum_div_of_complement_card_isLittleO
  · simpa only [liuGoodSet, GoodSetDensity.sourceGoodDenominators] using
      GoodSetDensity.eventually_sourceGoodDenominators_subset_denominators
  · simpa only [liuGoodSet] using
      GoodSetDensity.goodDenominators_complement_card_isLittleO
  · exact hlam

/-- Epsilon form of a normalized log-partition limit. -/
theorem eventually_scaledLogPartition_lower_of_tendsto
    {I : ℕ → Finset ℕ} {lam gamma : ℝ}
    (hlim : Tendsto
      (fun N : ℕ ↦ (∑ n ∈ I N, scaledLogPartition lam N n) / N)
      atTop (nhds (gamma - lam)))
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      (gamma - lam - eta) * N ≤
        ∑ n ∈ I N, scaledLogPartition lam N n := by
  have hnear : ∀ᶠ N : ℕ in atTop,
      gamma - lam - eta <
        (∑ n ∈ I N, scaledLogPartition lam N n) / N :=
    hlim.eventually (Ioi_mem_nhds (sub_lt_self _ heta))
  filter_upwards [hnear, eventually_gt_atTop (0 : ℕ)] with N hNnear hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  exact ((lt_div_iff₀ hNR).mp hNnear).le

/-- A nonnegative error tending to zero is eventually smaller than any
prescribed positive constant. -/
theorem eventually_error_le_of_tendsto_zero {e : ℕ → ℝ}
    (he : Tendsto e atTop (nhds 0)) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, e N ≤ eta := by
  exact (he.eventually (Iio_mem_nhds heta)).mono fun _N h ↦ h.le

/-! ## Stability of information under a common perturbation -/

/-- If both coordinate log-likelihoods change by at most `delta`, the
information of every atom changes by at most `card I * delta`.  This is the
finite estimate used to absorb the common `1 + o(1)` rescaling. -/
theorem bernoulliInformation_lower_of_log_close
    {I : Finset ℕ} {p r : ℕ → ℝ} {delta : ℝ}
    (hselected : ∀ n ∈ I, |Real.log (r n) - Real.log (p n)| ≤ delta)
    (homitted : ∀ n ∈ I,
      |Real.log (1 - r n) - Real.log (1 - p n)| ≤ delta)
    (A : Finset ℕ) :
    EntropyTypical.bernoulliInformation I p A - (I.card : ℝ) * delta ≤
      EntropyTypical.bernoulliInformation I r A := by
  rw [EntropyTypical.bernoulliInformation,
    EntropyTypical.bernoulliInformation]
  have hpoint : ∀ n ∈ I,
      (if n ∈ A then -Real.log (p n) else -Real.log (1 - p n)) - delta ≤
        if n ∈ A then -Real.log (r n) else -Real.log (1 - r n) := by
    intro n hnI
    by_cases hnA : n ∈ A
    · simp only [if_pos hnA]
      have := (abs_le.mp (hselected n hnI)).2
      linarith
    · simp only [if_neg hnA]
      have := (abs_le.mp (homitted n hnI)).2
      linarith
  calc
    (∑ n ∈ I, if n ∈ A then -Real.log (p n) else -Real.log (1 - p n)) -
          (I.card : ℝ) * delta =
        ∑ n ∈ I,
          ((if n ∈ A then -Real.log (p n) else -Real.log (1 - p n)) -
            delta) := by simp [Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ I,
          if n ∈ A then -Real.log (r n) else -Real.log (1 - r n) :=
      Finset.sum_le_sum hpoint

/-- A ready-to-use information lower bound for probabilities which are
logarithmically close to the sampled logistic profile. -/
theorem perturbedLogistic_information_lower
    {lam gamma eta delta : ℝ} {N : ℕ} (hN : 0 < N)
    {I A : Finset ℕ} {r : ℕ → ℝ}
    (hIpos : ∀ n ∈ I, 0 < n) (hA : A ∈ exactReciprocalEvent I)
    (hpartition :
      (gamma - lam - eta / 2) * N ≤ ∑ n ∈ I, scaledLogPartition lam N n)
    (herror : (I.card : ℝ) * delta ≤ eta / 2 * N)
    (hselected : ∀ n ∈ I,
      |Real.log (r n) - Real.log (scaledSelectionProbability lam N n)| ≤ delta)
    (homitted : ∀ n ∈ I,
      |Real.log (1 - r n) -
        Real.log (1 - scaledSelectionProbability lam N n)| ≤ delta) :
    (gamma - eta) * N ≤ EntropyTypical.bernoulliInformation I r A := by
  have hstable := bernoulliInformation_lower_of_log_close
    hselected homitted A
  rw [logisticInformation_eq_on_exactEvent hN hIpos hA] at hstable
  calc
    (gamma - eta) * N ≤
        lam * N + ∑ n ∈ I, scaledLogPartition lam N n -
          (I.card : ℝ) * delta := by linarith
    _ ≤ EntropyTypical.bernoulliInformation I r A := hstable

/-! ## Mass-to-count conversion -/

/-- A mass lower bound and a uniform atom upper bound imply an exponential
lower bound for the original exact count. -/
theorem exp_lower_le_count_of_exact_mass
    {N : ℕ} {I : Finset ℕ} {p : ℕ → ℝ} {d L : ℝ}
    (hI : I ⊆ denominators N)
    (hmass : Real.exp (-d) ≤ exactReciprocalMass I p)
    (hatom : ∀ A ∈ exactReciprocalEvent I,
      EntropyTypical.bernoulliWeight I p A ≤ Real.exp (-L)) :
    Real.exp (L - d) ≤ (count N : ℝ) := by
  have hsum : exactReciprocalMass I p ≤
      ((exactReciprocalEvent I).card : ℝ) * Real.exp (-L) := by
    rw [exactReciprocalMass]
    calc
      (∑ A ∈ exactReciprocalEvent I, EntropyTypical.bernoulliWeight I p A)
          ≤ ∑ _A ∈ exactReciprocalEvent I, Real.exp (-L) :=
        Finset.sum_le_sum hatom
      _ = ((exactReciprocalEvent I).card : ℝ) * Real.exp (-L) := by simp
  have hcard : Real.exp (L - d) ≤
      ((exactReciprocalEvent I).card : ℝ) := by
    have h := hmass.trans hsum
    calc
      Real.exp (L - d) = Real.exp (-d) / Real.exp (-L) := by
        rw [Real.exp_sub, Real.exp_neg, Real.exp_neg]
        field_simp
      _ ≤ ((exactReciprocalEvent I).card : ℝ) := by
        rw [div_le_iff₀ (Real.exp_pos (-L))]
        simpa [mul_comm] using h
  exact hcard.trans (by exact_mod_cast exactReciprocalEvent_card_le_count hI)

/-- Logarithmic form of `exp_lower_le_count_of_exact_mass`. -/
theorem logGrowth_lower_of_exact_mass
    {N : ℕ} (hN : 0 < N) {I : Finset ℕ} {p : ℕ → ℝ} {d L : ℝ}
    (hI : I ⊆ denominators N)
    (hmass : Real.exp (-d) ≤ exactReciprocalMass I p)
    (hatom : ∀ A ∈ exactReciprocalEvent I,
      EntropyTypical.bernoulliWeight I p A ≤ Real.exp (-L)) :
    (L - d) / N ≤ logGrowth N := by
  have hcount : 0 < (count N : ℝ) := by
    exact_mod_cast count_pos hN
  have hlog : L - d ≤ Real.log (count N : ℝ) :=
    (Real.le_log_iff_exp_le hcount).2
      (exp_lower_le_count_of_exact_mass hI hmass hatom)
  rw [logGrowth]
  exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg N)

/-! ## An interface for the arithmetic/Fourier witness -/

/-- At scale `N`, a lower-bound witness consists of a finite set of available
denominators and product probabilities for which the exact event has
subexponential mass and every exact atom has the entropy-scale upper bound.

The same error parameter `eta` is used in both estimates.  This loses
`2 * eta` in the final exponent and makes the epsilon bookkeeping explicit.
-/
def LowerBoundWitness (gamma eta : ℝ) (N : ℕ) : Prop :=
  ∃ (I : Finset ℕ) (p : ℕ → ℝ),
    I ⊆ denominators N ∧
      Real.exp (-(eta * N)) ≤ exactReciprocalMass I p ∧
      ∀ A ∈ exactReciprocalEvent I,
        EntropyTypical.bernoulliWeight I p A ≤
          Real.exp (-((gamma - eta) * N))

/-- A convenient certificate format for the output of the analytic part of
the lower bound.  Instead of asking directly for an atom bound, it asks for
the corresponding lower bound on self-information. -/
def LowerInformationCertificate (gamma eta : ℝ) (N : ℕ) : Prop :=
  ∃ (I : Finset ℕ) (p : ℕ → ℝ),
    I ⊆ denominators N ∧
      (∀ n ∈ I, 0 < p n) ∧
      (∀ n ∈ I, p n < 1) ∧
      Real.exp (-(eta * N)) ≤ exactReciprocalMass I p ∧
      ∀ A ∈ exactReciprocalEvent I,
        (gamma - eta) * N ≤ EntropyTypical.bernoulliInformation I p A

theorem lowerBoundWitness_of_informationCertificate
    {gamma eta : ℝ} {N : ℕ}
    (hcert : LowerInformationCertificate gamma eta N) :
    LowerBoundWitness gamma eta N := by
  rcases hcert with ⟨I, p, hI, hp0, hp1, hmass, hinfo⟩
  refine ⟨I, p, hI, hmass, ?_⟩
  intro A hA
  simpa using
    (EntropyTypical.bernoulliWeight_le_exp_of_information_ge I p hp0 hp1
      (A := A) (H := (gamma - eta) * N) (d := 0)
      (by simpa using hinfo A hA))

/-- The abstract lower-bound assembly: witnesses with arbitrarily small
linear error imply the eventual lower half of convergence to `gamma`. -/
theorem eventually_gamma_sub_le_logGrowth_of_witnesses
    {gamma : ℝ}
    (hwitness : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ N : ℕ in atTop, LowerBoundWitness gamma eta N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, gamma - epsilon ≤ logGrowth N := by
  let eta := epsilon / 2
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  filter_upwards [hwitness eta heta, eventually_gt_atTop (0 : ℕ)] with N hW hN
  rcases hW with ⟨I, p, hI, hmass, hatom⟩
  have hlower := logGrowth_lower_of_exact_mass hN hI hmass hatom
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have heq :
      (((gamma - eta) * N - eta * N) / (N : ℝ)) = gamma - epsilon := by
    dsimp [eta]
    field_simp
    ring
  rw [heq] at hlower
  exact hlower

/-- It is enough for the arithmetic/Fourier construction to produce
information certificates with arbitrarily small linear error. -/
theorem eventually_gamma_sub_le_logGrowth_of_informationCertificates
    {gamma : ℝ}
    (hcert : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ N : ℕ in atTop, LowerInformationCertificate gamma eta N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, gamma - epsilon ≤ logGrowth N := by
  apply eventually_gamma_sub_le_logGrowth_of_witnesses
    (fun eta heta ↦ (hcert eta heta).mono fun _N hN ↦
      lowerBoundWitness_of_informationCertificate hN)
    hepsilon

/-! ## Concrete-profile certificate assembly -/

/-- This theorem packages all deterministic work needed after a normalized
profile and a local-limit mass estimate have been constructed. -/
theorem eventually_informationCertificates_of_normalizedProfile
    {lam : ℝ} (_hlam : IsUniqueCriticalParameter lam)
    (I : ℕ → Finset ℕ) (p : ℕ → ℕ → ℝ) (error : ℕ → ℝ)
    (hsubset : ∀ᶠ N : ℕ in atTop, I N ⊆ denominators N)
    (hpos : ∀ᶠ N : ℕ in atTop, ∀ n ∈ I N, 0 < p N n)
    (hlt : ∀ᶠ N : ℕ in atTop, ∀ n ∈ I N, p N n < 1)
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop,
      Real.exp (-(eta * N)) ≤ exactReciprocalMass (I N) (p N))
    (hpartition : Tendsto
      (fun N : ℕ ↦ (∑ n ∈ I N, scaledLogPartition lam N n) / N)
      atTop (nhds (gamma lam - lam)))
    (herror0 : Tendsto error atTop (nhds 0))
    (herrorNonneg : ∀ N, 0 ≤ error N)
    (hselected : ∀ᶠ N : ℕ in atTop, ∀ n ∈ I N,
      |Real.log (p N n) - Real.log (scaledSelectionProbability lam N n)| ≤
        error N)
    (homitted : ∀ᶠ N : ℕ in atTop, ∀ n ∈ I N,
      |Real.log (1 - p N n) -
        Real.log (1 - scaledSelectionProbability lam N n)| ≤ error N) :
    ∀ eta : ℝ, 0 < eta →
      ∀ᶠ N : ℕ in atTop,
        LowerInformationCertificate (gamma lam) eta N := by
  intro eta heta
  have heta2 : 0 < eta / 2 := div_pos heta (by norm_num)
  have hpart := eventually_scaledLogPartition_lower_of_tendsto
    hpartition heta2
  have herr := eventually_error_le_of_tendsto_zero herror0 heta2
  filter_upwards [hsubset, hpos, hlt, hmass eta heta, hpart, herr,
    hselected, homitted, eventually_gt_atTop (0 : ℕ)] with
      N hIN hpN hltN hmassN hpartN herrN hselectedN homittedN hN
  refine ⟨I N, p N, hIN, hpN, hltN, hmassN, ?_⟩
  intro A hA
  have hIpos : ∀ n ∈ I N, 0 < n := by
    intro n hnI
    exact (mem_denominators.mp (hIN hnI)).1
  have hcardNat : (I N).card ≤ N := by
    calc
      (I N).card ≤ (denominators N).card := Finset.card_le_card hIN
      _ = N := by simp [denominators]
  have hcard : ((I N).card : ℝ) ≤ N := by exact_mod_cast hcardNat
  have herror : ((I N).card : ℝ) * error N ≤ eta / 2 * N := by
    calc
      ((I N).card : ℝ) * error N ≤ (N : ℝ) * error N :=
        mul_le_mul_of_nonneg_right hcard (herrorNonneg N)
      _ ≤ (N : ℝ) * (eta / 2) :=
        mul_le_mul_of_nonneg_left herrN (Nat.cast_nonneg N)
      _ = eta / 2 * N := by ring
  apply perturbedLogistic_information_lower hN hIpos hA hpartN herror
    hselectedN homittedN

/-- The normalized critical logistic profile supplies all lower-bound
certificates once its exact reciprocal event has subexponential mass. -/
theorem eventually_informationCertificates_normalizedLogistic_of_mass
    {lam : ℝ} (hlam : IsUniqueCriticalParameter lam)
    (hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop,
      Real.exp (-(eta * N)) ≤
        exactReciprocalMass (LogisticNormalization.goodSet N)
          (LogisticNormalization.normalizedLogisticProbability lam N)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop,
      LowerInformationCertificate (gamma lam) eta N := by
  apply eventually_informationCertificates_of_normalizedProfile
    hlam LogisticNormalization.goodSet
      (LogisticNormalization.normalizedLogisticProbability lam)
      (LogisticNormalization.logPerturbationError lam)
  · simpa only [denominators] using
      LogisticNormalization.eventually_goodSet_subset_Icc
  · exact (LogisticNormalization.eventually_normalized_probability_mem_Ioo
      hlam).mono fun _N hN n hn ↦ (hN n hn).1
  · exact (LogisticNormalization.eventually_normalized_probability_mem_Ioo
      hlam).mono fun _N hN n hn ↦ (hN n hn).2
  · exact hmass
  · simpa only [LogisticNormalization.goodSet, liuGoodSet] using
      tendsto_liuGoodSet_scaledLogPartition_sum_div
        (LogisticNormalization.criticalParameter_pos hlam)
  · exact LogisticNormalization.tendsto_logPerturbationError hlam
  · exact LogisticNormalization.logPerturbationError_nonneg lam
  · exact (LogisticNormalization.eventually_uniform_log_close hlam).mono
      fun _N hN n hn ↦ by
        simpa only [LogisticNormalization.rawLogisticProbability,
          scaledSelectionProbability] using (hN n hn).1
  · exact (LogisticNormalization.eventually_uniform_log_close hlam).mono
      fun _N hN n hn ↦ by
        simpa only [LogisticNormalization.rawLogisticProbability,
          scaledSelectionProbability] using (hN n hn).2

/-- A reciprocal-event lower bound at the smooth-LCM scale is
subexponential on the original `N` scale. -/
theorem eventually_normalizedLogistic_subexponentialMass_of_smoothLcm
    {lam : ℝ}
    (hlocal : ∀ᶠ N : ℕ in atTop,
      1 / (4 * (smoothLcm (S N) : ℝ)) ≤
        exactReciprocalMass (LogisticNormalization.goodSet N)
          (LogisticNormalization.normalizedLogisticProbability lam N)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop,
      Real.exp (-(eta * N)) ≤
        exactReciprocalMass (LogisticNormalization.goodSet N)
          (LogisticNormalization.normalizedLogisticProbability lam N) := by
  intro eta heta
  filter_upwards [
    LcmTail.eventually_exp_neg_mul_le_inv_four_smoothLcm eta heta,
    hlocal] with N htail hmass
  exact htail.trans hmass

/-- The direct smooth-LCM local-limit conclusion implies all information
certificates for the normalized critical logistic law. -/
theorem eventually_informationCertificates_normalizedLogistic_of_smoothLcm
    {lam : ℝ} (hlam : IsUniqueCriticalParameter lam)
    (hlocal : ∀ᶠ N : ℕ in atTop,
      1 / (4 * (smoothLcm (S N) : ℝ)) ≤
        exactReciprocalMass (LogisticNormalization.goodSet N)
          (LogisticNormalization.normalizedLogisticProbability lam N)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop,
      LowerInformationCertificate (gamma lam) eta N :=
  eventually_informationCertificates_normalizedLogistic_of_mass hlam
    (eventually_normalizedLogistic_subexponentialMass_of_smoothLcm hlocal)

/-- The full lower-bound conclusion, conditional only on the concrete
smooth-LCM local-limit estimate. -/
theorem eventually_gamma_sub_le_logGrowth_of_smoothLcm
    {lam : ℝ} (hlam : IsUniqueCriticalParameter lam)
    (hlocal : ∀ᶠ N : ℕ in atTop,
      1 / (4 * (smoothLcm (S N) : ℝ)) ≤
        exactReciprocalMass (LogisticNormalization.goodSet N)
          (LogisticNormalization.normalizedLogisticProbability lam N))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, gamma lam - epsilon ≤ logGrowth N :=
  eventually_gamma_sub_le_logGrowth_of_informationCertificates
    (eventually_informationCertificates_normalizedLogistic_of_smoothLcm
      hlam hlocal) hepsilon

/-- The lower half of the Liu--Sawhney asymptotic for Erdős Problem 297. -/
theorem eventually_gamma_sub_le_logGrowth {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, gamma lam - ε ≤ logGrowth N := by
  apply eventually_gamma_sub_le_logGrowth_of_smoothLcm hlam _ hε
  filter_upwards [
    LocalLimit.eventually_local_limit_normalizedLogistic hlam] with N hN
  rw [exactReciprocalMass_eq_localLimit]
  exact hN

end

end Erdos297

#print axioms Erdos297.exp_lower_le_count_of_exact_mass
#print axioms Erdos297.eventually_gamma_sub_le_logGrowth_of_witnesses
#print axioms Erdos297.eventually_gamma_sub_le_logGrowth

import ErdosProblems.Erdos140.Unbalancing
import ErdosProblems.Erdos140.BohrStopping
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The balanced-restriction stopping bridge

The balanced Bohr restriction argument uses three controlled changes of exponent which
are easy to blur in an informal proof.  Starting from a positive natural
exponent `p`, we first pass to the even exponent `q = 2p`.  The checked
power-moment form of unbalancing takes an odd exponent at least five, so we
promote once more to `qOdd = 2q + 3`.  Localized unbalancing can then return an
arbitrary positive exponent `r`; the stopping theorem is run at the fixed even exponent

`Q = unbalancingExponent (ε / 2) qOdd`.

This file proves the probability-space `L^p` monotonicity needed for both
changes of exponent and packages the final contradiction.  Its constants
match the audited proof: comparison loses a factor two, localized
unbalancing gains `1 + ε / 8`, and the stopping estimate has the same strict
`1 + ε / 8` threshold.

The Bohr-set construction supplies the four analytic hypotheses of
`balanced_convolution_of_stopping`; the theorem below contains no hidden
choice principle or unproved declaration.
-/

open Finset
open scoped BigOperators

namespace Erdos140
namespace BalancedRestriction

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A nonnegative weight of total mass one on a finite type. -/
structure ProbabilityWeight (ν : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ν x
  sum_eq_one : ∑ x, ν x = 1

/-- The natural-exponent weighted `L^p` norm.  Exponent zero is assigned the
value zero; every theorem using this definition assumes a positive exponent. -/
noncomputable def weightedLpNorm (ν f : X → ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else
    (weightedAbsMoment ν f p) ^ (1 / (p : ℝ))

omit [DecidableEq X] in
lemma weightedLpNorm_of_pos (ν f : X → ℝ) {p : ℕ} (hp : 0 < p) :
    weightedLpNorm ν f p =
      (weightedAbsMoment ν f p) ^ (1 / (p : ℝ)) := by
  simp [weightedLpNorm, hp.ne']

lemma weightedLpNorm_nonneg {ν : X → ℝ} (hν : ProbabilityWeight ν)
    (f : X → ℝ) (p : ℕ) :
    0 ≤ weightedLpNorm ν f p := by
  unfold weightedLpNorm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (weightedAbsMoment_nonneg hν.nonneg p) _

lemma weightedLpNorm_pow {ν f : X → ℝ} (hν : ProbabilityWeight ν)
    {p : ℕ} (hp : 0 < p) :
    weightedLpNorm ν f p ^ p = weightedAbsMoment ν f p := by
  rw [weightedLpNorm_of_pos _ _ hp, ← Real.rpow_natCast,
    ← Real.rpow_mul (weightedAbsMoment_nonneg hν.nonneg p)]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  simp

private lemma abs_pow_rpow_div {x : ℝ} {p q : ℕ} (hp : 0 < p) :
    (|x| ^ p) ^ ((q : ℝ) / (p : ℝ)) = |x| ^ q := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg x)]
  rw [← Real.rpow_natCast]
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- Generalized-mean inequality for finite probability weights, in the exact
form used by the balanced-restriction proof. -/
theorem weightedLpNorm_mono_exponent
    {ν f : X → ℝ} (hν : ProbabilityWeight ν)
    {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    weightedLpNorm ν f p ≤ weightedLpNorm ν f q := by
  have hq : 0 < q := hp.trans_le hpq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hratio : (1 : ℝ) ≤ (q : ℝ) / (p : ℝ) := by
    exact (le_div_iff₀ hpR).2 (by simpa using hpqR)
  have hmomentP : 0 ≤ weightedAbsMoment ν f p :=
    weightedAbsMoment_nonneg hν.nonneg p
  have hmomentQ : 0 ≤ weightedAbsMoment ν f q :=
    weightedAbsMoment_nonneg hν.nonneg q
  have hjensen :
      (weightedAbsMoment ν f p) ^ ((q : ℝ) / (p : ℝ)) ≤
        weightedAbsMoment ν f q := by
    have h := Real.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset X) ν (fun x ↦ |f x| ^ p)
      (fun x _ ↦ hν.nonneg x) (by simpa using hν.sum_eq_one)
      (fun x _ ↦ pow_nonneg (abs_nonneg _) _) hratio
    simpa only [weightedAbsMoment, mem_univ, abs_pow_rpow_div hp] using h
  rw [weightedLpNorm_of_pos _ _ hp, weightedLpNorm_of_pos _ _ hq]
  have hleft :
      0 ≤ (weightedAbsMoment ν f p) ^ ((q : ℝ) / (p : ℝ)) :=
    Real.rpow_nonneg hmomentP _
  have hroot := Real.rpow_le_rpow hleft hjensen
    (div_nonneg zero_le_one hqR.le)
  calc
    (weightedAbsMoment ν f p) ^ (1 / (p : ℝ)) =
        ((weightedAbsMoment ν f p) ^ ((q : ℝ) / (p : ℝ))) ^
          (1 / (q : ℝ)) := by
      rw [← Real.rpow_mul hmomentP]
      congr 1
      field_simp
    _ ≤ (weightedAbsMoment ν f q) ^ (1 / (q : ℝ)) := hroot

/-- Taking a positive natural root weakens a factor two by at most a factor
two.  This is the root adapter used after the moment-form convolution
comparison theorem. -/
theorem weightedLpNorm_le_two_of_moment_le_two
    {μ ν f g : X → ℝ} (hμ : ProbabilityWeight μ) (hν : ProbabilityWeight ν)
    {p : ℕ} (hp : 0 < p)
    (hmoment : weightedAbsMoment μ f p ≤ 2 * weightedAbsMoment ν g p) :
    weightedLpNorm μ f p ≤ 2 * weightedLpNorm ν g p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have ha : 0 ≤ (1 / (p : ℝ)) := by positivity
  have haone : (1 / (p : ℝ)) ≤ 1 := by
    rw [div_le_one hpR]
    exact_mod_cast hp
  have hμmoment : 0 ≤ weightedAbsMoment μ f p :=
    weightedAbsMoment_nonneg hμ.nonneg p
  have hνmoment : 0 ≤ weightedAbsMoment ν g p :=
    weightedAbsMoment_nonneg hν.nonneg p
  rw [weightedLpNorm_of_pos _ _ hp, weightedLpNorm_of_pos _ _ hp]
  calc
    (weightedAbsMoment μ f p) ^ (1 / (p : ℝ)) ≤
        (2 * weightedAbsMoment ν g p) ^ (1 / (p : ℝ)) :=
      Real.rpow_le_rpow hμmoment hmoment ha
    _ = (2 : ℝ) ^ (1 / (p : ℝ)) *
        (weightedAbsMoment ν g p) ^ (1 / (p : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hνmoment]
    _ ≤ 2 * (weightedAbsMoment ν g p) ^ (1 / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hνmoment _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) haone

/-- The first, even exponent used in the proof. -/
def comparisonExponent (p : ℕ) : ℕ := 2 * p

theorem comparisonExponent_even (p : ℕ) : Even (comparisonExponent p) := by
  exact ⟨p, by simp [comparisonExponent, two_mul]⟩

theorem le_comparisonExponent {p : ℕ} (hp : 0 < p) :
    p ≤ comparisonExponent p := by
  simp only [comparisonExponent]
  omega

theorem comparisonExponent_le_two_mul (p : ℕ) :
    comparisonExponent p ≤ 2 * p := le_rfl

/-- The odd exponent at which the power-moment unbalancing lemma is applied. -/
def unbalancingInputExponent (p : ℕ) : ℕ :=
  2 * comparisonExponent p + 3

theorem unbalancingInputExponent_odd (p : ℕ) :
    Odd (unbalancingInputExponent p) := by
  simp [unbalancingInputExponent, comparisonExponent, Nat.odd_iff]

theorem five_le_unbalancingInputExponent {p : ℕ} (hp : 0 < p) :
    5 ≤ unbalancingInputExponent p := by
  simp only [unbalancingInputExponent, comparisonExponent]
  omega

theorem comparisonExponent_le_unbalancingInputExponent (p : ℕ) :
    comparisonExponent p ≤ unbalancingInputExponent p := by
  simp only [unbalancingInputExponent]
  omega

/-- The second exponent promotion in the corrected argument: the even
comparison exponent may be promoted to the odd unbalancing input on any
finite probability space. -/
theorem weightedLpNorm_comparison_le_unbalancingInput
    {ν f : X → ℝ} (hν : ProbabilityWeight ν) {p : ℕ} (hp : 0 < p) :
    weightedLpNorm ν f (comparisonExponent p) ≤
      weightedLpNorm ν f (unbalancingInputExponent p) := by
  apply weightedLpNorm_mono_exponent hν
  · exact Nat.mul_pos (by norm_num) hp
  · exact comparisonExponent_le_unbalancingInputExponent p

/-- The fixed even stopping exponent.  The argument applies unbalancing with
error `ε / 2`, so this definition records that choice literally. -/
noncomputable def stoppingExponent (ε : ℝ) (p : ℕ) : ℕ :=
  unbalancingExponent (ε / 2) (unbalancingInputExponent p)

theorem stoppingExponent_even (ε : ℝ) (p : ℕ) :
    Even (stoppingExponent ε p) := by
  exact unbalancingExponent_even _ _

theorem stoppingExponent_pos {ε : ℝ} {p : ℕ}
    (hε : 0 < ε) (hp : 0 < p) :
    0 < stoppingExponent ε p := by
  apply unbalancingExponent_pos (p := unbalancingInputExponent p)
  · positivity
  · have hfive := five_le_unbalancingInputExponent hp
    omega

/-- An explicit bound showing that the fixed stopping exponent is only a
constant (depending on `ε`) times the original exponent. -/
theorem stoppingExponent_eq (ε : ℝ) (p : ℕ) :
    stoppingExponent ε p =
      (8 * p + 6) * unbalancingMultiplier (ε / 2) := by
  unfold stoppingExponent unbalancingExponent unbalancingInputExponent
    comparisonExponent
  ring

theorem stoppingExponent_le_const_mul {ε : ℝ} {p : ℕ} (hp : 0 < p) :
    stoppingExponent ε p ≤
      14 * unbalancingMultiplier (ε / 2) * p := by
  rw [stoppingExponent_eq]
  have hlinear : 8 * p + 6 ≤ 14 * p := by omega
  have h := Nat.mul_le_mul_right (unbalancingMultiplier (ε / 2)) hlinear
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- The exact-scaling core of localized unbalancing.  In the Bohr argument
the identity `positiveCorr = mainTerm * (1 + f)` holds up to a small boundary
error; regularity absorbs that error before this lemma is invoked.  This
theorem records the error-free analytic step and, importantly, returns a
*positive even* exponent, so subsequent `L^p` promotion is legitimate. -/
theorem unbalancing_of_exact_scaling
    {ν : X → ℝ} (hν : ProbabilityWeight ν)
    {f positiveCorr : X → ℝ} {η mainTerm : ℝ}
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (hmain : 0 < mainTerm)
    {p : ℕ} (hp : 5 ≤ p) (hpodd : Odd p)
    (hmom : ∀ k : ℕ, 0 ≤ weightedMoment ν f k)
    (hlarge : η ^ p ≤ weightedAbsMoment ν f p)
    (hscale : ∀ x, positiveCorr x = mainTerm * (1 + f x)) :
    ∃ r : ℕ, 0 < r ∧ Even r ∧ r ≤ unbalancingExponent η p ∧
      (1 + η / 2) * mainTerm ≤ weightedLpNorm ν positiveCorr r := by
  obtain ⟨r, hr, hreven, hrBound, hunbalanced⟩ :=
    unbalancing_of_nonnegative_moments hν.nonneg hν.sum_eq_one hmom
      hη₀ hη₁ hp hpodd hlarge
  refine ⟨r, hr, hreven, hrBound, ?_⟩
  have hmomentScale :
      weightedAbsMoment ν positiveCorr r =
        mainTerm ^ r * weightedAbsMoment ν (f + 1) r := by
    unfold weightedAbsMoment
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro x _
    rw [hscale x, abs_mul, abs_of_pos hmain, mul_pow]
    simp only [Pi.add_apply, Pi.one_apply]
    ring_nf
  have hpower :
      ((1 + η / 2) * mainTerm) ^ r ≤
        weightedAbsMoment ν positiveCorr r := by
    rw [hmomentScale, mul_pow]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hunbalanced (pow_nonneg hmain.le r))
  rw [weightedLpNorm_of_pos _ _ hr]
  have hbase : 0 ≤ (1 + η / 2) * mainTerm := by positivity
  have hroot := Real.rpow_le_rpow (pow_nonneg hbase r) hpower
    (by positivity : 0 ≤ (r : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hbase hr.ne'] at hroot
  simpa [one_div] using hroot

/-- The corrected exponent chain specialized to exact scaling. -/
theorem unbalancing_at_stoppingExponent_of_exact_scaling
    {ν : X → ℝ} (hν : ProbabilityWeight ν)
    {f positiveCorr : X → ℝ} {ε mainTerm : ℝ}
    (hε₀ : 0 < ε) (hε₂ : ε ≤ 2) (hmain : 0 < mainTerm)
    {p : ℕ} (hp : 0 < p)
    (hmom : ∀ k : ℕ, 0 ≤ weightedMoment ν f k)
    (hlarge : ε / 2 < weightedLpNorm ν f (comparisonExponent p))
    (hscale : ∀ x, positiveCorr x = mainTerm * (1 + f x)) :
    ∃ r : ℕ, 0 < r ∧ Even r ∧ r ≤ stoppingExponent ε p ∧
      (1 + ε / 8) * mainTerm ≤ weightedLpNorm ν positiveCorr r := by
  let qOdd := unbalancingInputExponent p
  have hqOddPos : 0 < qOdd := by
    have := five_le_unbalancingInputExponent hp
    omega
  have hpromote :
      weightedLpNorm ν f (comparisonExponent p) ≤ weightedLpNorm ν f qOdd := by
    simpa [qOdd] using weightedLpNorm_comparison_le_unbalancingInput hν hp
  have hlargeOdd : ε / 2 < weightedLpNorm ν f qOdd := hlarge.trans_le hpromote
  have hmomentLarge : (ε / 2) ^ qOdd ≤ weightedAbsMoment ν f qOdd := by
    calc
      (ε / 2) ^ qOdd ≤ weightedLpNorm ν f qOdd ^ qOdd :=
        pow_le_pow_left₀ (by positivity) hlargeOdd.le qOdd
      _ = weightedAbsMoment ν f qOdd := weightedLpNorm_pow hν hqOddPos
  obtain ⟨r, hr, hreven, hrBound, hrLarge⟩ :=
    unbalancing_of_exact_scaling hν (η := ε / 2) (mainTerm := mainTerm)
      (by positivity) (by linarith) hmain
      (five_le_unbalancingInputExponent hp)
      (unbalancingInputExponent_odd p) hmom hmomentLarge hscale
  refine ⟨r, hr, hreven, ?_, ?_⟩
  · simpa [stoppingExponent, qOdd] using hrBound
  · calc
      (1 + ε / 8) * mainTerm ≤ (1 + (ε / 2) / 2) * mainTerm := by
        apply mul_le_mul_of_nonneg_right _ hmain.le
        linarith
      _ ≤ weightedLpNorm ν positiveCorr r := hrLarge

/-- **Even-exponent promotion and the `1/8` contradiction.**

`balanced` is the balanced convolution, `corr` its autocorrelation after the
comparison step, and `positiveCorr` the unbalanced positive correlation.  In
the Bohr application the weights `μ` and `ν` are the corresponding normalized
Bohr probability weights.

The four analytic inputs are stated separately so their roles are visible:

* `hcomparison` is the factor-two convolution comparison at the even exponent;
* `hunbalance` is localized unbalancing, returning some positive `r ≤ Q`;
* `hstopping` is the strict stopping estimate at `Q`.

The conclusion is the desired balanced bound at the original exponent. -/
theorem balanced_convolution_of_stopping
    {μ ν : X → ℝ} (hμ : ProbabilityWeight μ) (hν : ProbabilityWeight ν)
    {balanced corr positiveCorr : X → ℝ}
    {ε mainTerm : ℝ} (hε : 0 < ε) (hmain : 0 < mainTerm)
    {p : ℕ} (hp : 0 < p)
    (hcomparison :
      weightedLpNorm μ balanced (comparisonExponent p) ≤
        2 * weightedLpNorm ν corr (comparisonExponent p))
    (hunbalance :
      ε * mainTerm / 2 < weightedLpNorm ν corr (comparisonExponent p) →
        ∃ r : ℕ, 0 < r ∧ r ≤ stoppingExponent ε p ∧
          (1 + ε / 8) * mainTerm ≤ weightedLpNorm ν positiveCorr r)
    (hstopping :
      weightedLpNorm ν positiveCorr (stoppingExponent ε p) <
        (1 + ε / 8) * mainTerm) :
    weightedLpNorm μ balanced p ≤ ε * mainTerm := by
  have hεmain : 0 < ε * mainTerm := mul_pos hε hmain
  by_contra hbound
  have hfail : ε * mainTerm < weightedLpNorm μ balanced p := lt_of_not_ge hbound
  have hpromoteBalanced :
      weightedLpNorm μ balanced p ≤
        weightedLpNorm μ balanced (comparisonExponent p) :=
    weightedLpNorm_mono_exponent hμ hp (le_comparisonExponent hp)
  have hcorrLarge :
      ε * mainTerm / 2 < weightedLpNorm ν corr (comparisonExponent p) := by
    nlinarith [hεmain, hfail.trans_le hpromoteBalanced, hcomparison,
      weightedLpNorm_nonneg hν corr (comparisonExponent p)]
  obtain ⟨r, hr, hrQ, hunbalanced⟩ := hunbalance hcorrLarge
  have hpromotePositive :
      weightedLpNorm ν positiveCorr r ≤
        weightedLpNorm ν positiveCorr (stoppingExponent ε p) :=
    weightedLpNorm_mono_exponent hν hr hrQ
  exact (not_lt_of_ge (hunbalanced.trans hpromotePositive)) hstopping

/-- **Balanced restriction assembled with the actual regular-Bohr stopping
chain.**  The predicate stopped by `BohrStopping` is precisely the fixed-`Q`
high positive-correlation inequality.  Once that predicate fails, the
factor-two comparison and localized-unbalancing implications feed
`balanced_convolution_of_stopping` and give the balanced estimate at the
original exponent `p`.

The returned `t` is an actual `RegularRestriction`: it contains the final
Bohr datum, its regularity certificate, the restricted set, and containment
in the Bohr carrier.  Rank and cardinality bounds are those accumulated by
the twelfth-power stopping theorem. -/
theorem exists_balanced_stopping_restriction
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {q K : ℝ} {m L rankCost p : ℕ}
    (hq : 0 ≤ q) (hqm : (2 : ℝ) ≤ q ^ m)
    (hK : 0 ≤ K) (hp : 0 < p)
    {ε : ℝ} (hε : 0 < ε)
    (μ ν : BohrStopping.RegularRestriction G → G → ℝ)
    (balanced corr positiveCorr : BohrStopping.RegularRestriction G → G → ℝ)
    (mainTerm : BohrStopping.RegularRestriction G → ℝ)
    (hμ : ∀ s, ProbabilityWeight (μ s))
    (hν : ∀ s, ProbabilityWeight (ν s))
    (hmain : ∀ s, 0 < mainTerm s)
    (hcomparison : ∀ s,
      weightedLpNorm (μ s) (balanced s) (comparisonExponent p) ≤
        2 * weightedLpNorm (ν s) (corr s) (comparisonExponent p))
    (hunbalance : ∀ s,
      ε * mainTerm s / 2 <
          weightedLpNorm (ν s) (corr s) (comparisonExponent p) →
        ∃ r : ℕ, 0 < r ∧ r ≤ stoppingExponent ε p ∧
          (1 + ε / 8) * mainTerm s ≤
            weightedLpNorm (ν s) (positiveCorr s) r)
    (hincrement : BohrStopping.ProducesIncrement
      (fun s ↦ (1 + ε / 8) * mainTerm s ≤
        weightedLpNorm (ν s) (positiveCorr s) (stoppingExponent ε p))
      q rankCost (BohrStopping.eleventhPowerStepCost K L))
    (initial : BohrStopping.RegularRestriction G)
    (hscale : BohrStopping.OnDyadicScale L initial.density) :
    ∃ n ≤ m * (L + 1), ∃ t : BohrStopping.RegularRestriction G,
      BohrStopping.ControlledChain q rankCost
          (BohrStopping.eleventhPowerStepCost K L) n initial t ∧
      weightedLpNorm (μ t) (balanced t) p ≤ ε * mainTerm t ∧
      q ^ n * initial.density ≤ t.density ∧
      t.rank ≤ initial.rank + (m * (L + 1)) * rankCost ∧
      Real.exp (-(BohrStopping.twelfthPowerSizeCostWithMultiplier K m L)) *
          (initial.card : ℝ) ≤ (t.card : ℝ) := by
  obtain ⟨n, hn, t, hchain, hnotBad, hdensity, hrank, hcard⟩ :=
    BohrStopping.exists_stopping_restriction_fixedFactor
      hq hqm hK hincrement initial hscale
  have hstopping :
      weightedLpNorm (ν t) (positiveCorr t) (stoppingExponent ε p) <
        (1 + ε / 8) * mainTerm t := lt_of_not_ge hnotBad
  have hbalanced :
      weightedLpNorm (μ t) (balanced t) p ≤ ε * mainTerm t :=
    balanced_convolution_of_stopping (hμ t) (hν t) hε (hmain t) hp
      (hcomparison t) (hunbalance t) hstopping
  exact ⟨n, hn, t, hchain, hbalanced, hdensity, hrank, hcard⟩

#print axioms weightedLpNorm_mono_exponent
#print axioms unbalancing_of_exact_scaling
#print axioms unbalancing_at_stoppingExponent_of_exact_scaling
#print axioms balanced_convolution_of_stopping
#print axioms exists_balanced_stopping_restriction

end BalancedRestriction
end Erdos140

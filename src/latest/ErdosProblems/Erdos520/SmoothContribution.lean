import ErdosProblems.Erdos520.SmoothSecondMoment
import ErdosProblems.Erdos520.SmoothMartingale
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.EulerProduct.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# The `y₀`-smooth contribution

This file isolates the arithmetic input in the treatment of the contribution
whose prime factors are all at most `y₀`.  The random part is unconditional:
the second-moment estimate in `SmoothSecondMoment` gives a pointwise tail;
a finite union bound treats all test points at one scale; and the first
Borel--Cantelli lemma gives the eventual almost-sure estimate.

Thus the only input to the final theorem below is a deterministic bound for
`Nat.smoothNumbersUpTo` strong enough to make the displayed scalar budget
summable.  No probabilistic assertion is included in that input.
-/

/-- Failure of the desired smooth-sum estimate at one test point. -/
def smoothContributionBad (z y : ℕ) (threshold : ℝ) : Set Omega :=
  {omega | threshold < |Ψ omega z y|}

/-- The second-moment/Markov tail at one test point, in real-valued measure.

The right side contains precisely the deterministic smooth-number quantity
which remains to be estimated by analytic number theory.
-/
theorem measureReal_smoothContributionBad_le
    (z y : ℕ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    μ.real (smoothContributionBad z y threshold) ≤
      (Nat.smoothNumbersUpTo z (y + 1)).card / threshold ^ 2 := by
  let W : Omega → ℝ := fun omega => |Ψ omega z y| ^ 2
  have hWnonneg : 0 ≤ᵐ[μ] W := ae_of_all μ fun _ => sq_nonneg _
  have hWint : Integrable W μ := by
    simpa only [W, Real.norm_eq_abs] using!
      (memLp_two_Ψ z y).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := μ) hWnonneg hWint
      (threshold ^ 2)
  have hsubset :
      smoothContributionBad z y threshold ⊆
        {omega | threshold ^ 2 ≤ W omega} := by
    intro omega homega
    change threshold < |Ψ omega z y| at homega
    exact le_of_lt ((sq_lt_sq₀ hthreshold.le (abs_nonneg _)).mpr homega)
  have hmoment : (∫ omega, W omega ∂μ) ≤
      (Nat.smoothNumbersUpTo z (y + 1)).card := by
    simpa only [W] using! integral_sq_Ψ_le_smoothNumbersUpTo_card z y
  have hmul :
      threshold ^ 2 * μ.real (smoothContributionBad z y threshold) ≤
        (Nat.smoothNumbersUpTo z (y + 1)).card :=
    calc
      threshold ^ 2 * μ.real (smoothContributionBad z y threshold)
          ≤ threshold ^ 2 * μ.real {omega | threshold ^ 2 ≤ W omega} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (sq_nonneg _)
      _ ≤ ∫ omega, W omega ∂μ := hmarkov
      _ ≤ (Nat.smoothNumbersUpTo z (y + 1)).card := hmoment
  rw [div_eq_mul_inv]
  exact (le_div_iff₀ (sq_pos_of_pos hthreshold)).mpr (by
    simpa [mul_comm] using! hmul)

/-- At scale `ell`, failure at any one of a finite collection of test
indices.  The functions `z` and `cutoff` turn a test index into the actual
smooth-sum endpoint and smoothness cutoff.
-/
def smoothContributionFailure
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold : ℕ → ℝ) (ell : ℕ) : Set Omega :=
  {omega |
    ∃ r ∈ tests ell,
      threshold ell < |Ψ omega (z ell r) (cutoff ell)|}

/-- The exact second-moment budget obtained by summing the smooth-number
cardinality bound over the test points at one scale. -/
noncomputable def smoothContributionSecondMomentBudget
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold : ℕ → ℝ) (ell : ℕ) : ℝ :=
  ∑ r ∈ tests ell,
    (Nat.smoothNumbersUpTo (z ell r) (cutoff ell + 1)).card /
      threshold ell ^ 2

/-- Finite union bound for the smooth contribution at all test points of one
scale. -/
theorem measureReal_smoothContributionFailure_le
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold : ℕ → ℝ) (hthreshold : ∀ ell, 0 < threshold ell)
    (ell : ℕ) :
    μ.real (smoothContributionFailure tests z cutoff threshold ell) ≤
      smoothContributionSecondMomentBudget tests z cutoff threshold ell := by
  let point : ℕ → Set Omega := fun r =>
    smoothContributionBad (z ell r) (cutoff ell) (threshold ell)
  have hfailure :
      smoothContributionFailure tests z cutoff threshold ell =
        ⋃ r ∈ tests ell, point r := by
    ext omega
    simp only [smoothContributionFailure, point, smoothContributionBad,
      Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hfailure]
  calc
    μ.real (⋃ r ∈ tests ell, point r)
        ≤ ∑ r ∈ tests ell, μ.real (point r) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ tests ell,
        (Nat.smoothNumbersUpTo (z ell r) (cutoff ell + 1)).card /
          threshold ell ^ 2 := by
      gcongr with r hr
      exact measureReal_smoothContributionBad_le
        (z ell r) (cutoff ell) (hthreshold ell)
    _ = smoothContributionSecondMomentBudget tests z cutoff threshold ell := rfl

/-- Summability of the deterministic second-moment budgets implies
summability of the actual failure probabilities. -/
theorem summable_measureReal_smoothContributionFailure
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold : ℕ → ℝ) (hthreshold : ∀ ell, 0 < threshold ell)
    (hbudget : Summable fun ell =>
      smoothContributionSecondMomentBudget tests z cutoff threshold ell) :
    Summable fun ell =>
      μ.real (smoothContributionFailure tests z cutoff threshold ell) := by
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _ hbudget
  intro ell
  exact measureReal_smoothContributionFailure_le
    tests z cutoff threshold hthreshold ell

/-- Borel--Cantelli converts a summable smooth-contribution budget into the
desired almost-sure eventual bound, simultaneously at every test point of
each sufficiently large scale. -/
theorem ae_eventually_smoothContribution_le_of_summable_budget
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold : ℕ → ℝ) (hthreshold : ∀ ell, 0 < threshold ell)
    (hbudget : Summable fun ell =>
      smoothContributionSecondMomentBudget tests z cutoff threshold ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (z ell r) (cutoff ell)| ≤ threshold ell := by
  have hsummable := summable_measureReal_smoothContributionFailure
    tests z cutoff threshold hthreshold hbudget
  have hbc : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      omega ∉ smoothContributionFailure tests z cutoff threshold ell := by
    apply ae_eventually_notMem
    have heq :
        (fun ell => μ (smoothContributionFailure tests z cutoff threshold ell)) =
          (fun ell => ENNReal.ofReal
            (μ.real (smoothContributionFailure tests z cutoff threshold ell))) := by
      funext ell
      exact (ofReal_measureReal
        (μ := μ)
        (s := smoothContributionFailure tests z cutoff threshold ell)).symm
    rw [heq]
    exact hsummable.tsum_ofReal_ne_top
  filter_upwards [hbc] with omega homega
  filter_upwards [homega] with ell hell
  intro r hr
  by_contra hnot
  exact hell ⟨r, hr, lt_of_not_ge hnot⟩

/-!
## Rankin's bound

Mathlib's finite Euler-product identity is enough to prove the exact Rankin
bound unconditionally.  What is *not* supplied by Mathlib is the asymptotic
estimate for this prime product at Caich's moving choice of `sigma` and
`y₀`.  Consequently the last analytic input below is now a completely
explicit scalar finite-product summability statement, rather than an opaque
smooth-number counting hypothesis.
-/

private noncomputable def smoothRankinWeight (sigma : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-sigma)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

private def smoothUpToEmbedding (z y : ℕ) :
    {n // n ∈ Nat.smoothNumbersUpTo z y} ↪ y.smoothNumbers where
  toFun n := ⟨n.1, (Nat.mem_smoothNumbersUpTo.mp n.2).2⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : y.smoothNumbers => (x : ℕ)) h

private def smoothSubtypeFinset (z y : ℕ) : Finset y.smoothNumbers :=
  (Nat.smoothNumbersUpTo z y).attach.map (smoothUpToEmbedding z y)

@[simp] private theorem card_smoothSubtypeFinset (z y : ℕ) :
    (smoothSubtypeFinset z y).card =
      (Nat.smoothNumbersUpTo z y).card := by
  simp [smoothSubtypeFinset]

private theorem mem_smoothSubtypeFinset {z y : ℕ} {m : y.smoothNumbers} :
    m ∈ smoothSubtypeFinset z y ↔ m.1 ≤ z := by
  constructor
  · intro hm
    rw [smoothSubtypeFinset, Finset.mem_map] at hm
    rcases hm with ⟨a, _ha, hma⟩
    rw [← hma]
    exact (Nat.mem_smoothNumbersUpTo.mp a.2).1
  · intro hm
    rw [smoothSubtypeFinset, Finset.mem_map]
    let a : {n // n ∈ Nat.smoothNumbersUpTo z y} :=
      ⟨m.1, Nat.mem_smoothNumbersUpTo.mpr ⟨hm, m.2⟩⟩
    refine ⟨a, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- The usual Rankin bound for smooth numbers, with its Euler product written
out explicitly.  This is valid for every positive real Rankin parameter.
-/
theorem card_smoothNumbersUpTo_le_rankinProduct
    {sigma : ℝ} (hsigma : 0 < sigma) (z y : ℕ) :
    ((Nat.smoothNumbersUpTo z y).card : ℝ) ≤
      (z : ℝ) ^ sigma *
        ∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  by_cases hz : z = 0
  · subst z
    have hempty : Nat.smoothNumbersUpTo 0 y = ∅ := by
      ext n
      simp only [Nat.mem_smoothNumbersUpTo, Finset.notMem_empty, iff_false]
      rintro ⟨hn, hsmooth⟩
      exact hsmooth.1 (Nat.eq_zero_of_le_zero hn)
    rw [hempty]
    simp [Real.zero_rpow hsigma.ne']
  have hzpos : 0 < z := Nat.pos_of_ne_zero hz
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := smoothRankinWeight sigma)
      (fun {p} hp => by
        change |(p : ℝ) ^ (-sigma)| < 1
        have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
        rw [abs_of_pos (Real.rpow_pos_of_pos hp0 _)]
        rw [Real.rpow_neg hp0.le]
        exact inv_lt_one_of_one_lt₀
          (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hsigma)) y
  have hpoint (m : y.smoothNumbers) (hm : m ∈ smoothSubtypeFinset z y) :
      (1 : ℝ) ≤ (z : ℝ) ^ sigma * smoothRankinWeight sigma m := by
    have hmpos : 0 < (m : ℕ) := Nat.pos_of_ne_zero m.property.1
    have hmposR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hmz : (m : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (mem_smoothSubtypeFinset.mp hm)
    have hpowers : (m : ℝ) ^ sigma ≤ (z : ℝ) ^ sigma :=
      Real.rpow_le_rpow hmposR.le hmz hsigma.le
    change 1 ≤ (z : ℝ) ^ sigma * (m : ℝ) ^ (-sigma)
    rw [Real.rpow_neg hmposR.le]
    calc
      (1 : ℝ) = (m : ℝ) ^ sigma * ((m : ℝ) ^ sigma)⁻¹ := by
        exact (mul_inv_cancel₀ (Real.rpow_pos_of_pos hmposR sigma).ne').symm
      _ ≤ (z : ℝ) ^ sigma * ((m : ℝ) ^ sigma)⁻¹ :=
        mul_le_mul_of_nonneg_right hpowers
          (inv_nonneg.mpr (Real.rpow_nonneg hmposR.le _))
  calc
    ((Nat.smoothNumbersUpTo z y).card : ℝ)
        = ∑ _m ∈ smoothSubtypeFinset z y, (1 : ℝ) := by simp
    _ ≤ ∑ m ∈ smoothSubtypeFinset z y,
        (z : ℝ) ^ sigma * smoothRankinWeight sigma m := by
      gcongr with m hm
      exact hpoint m hm
    _ = (z : ℝ) ^ sigma *
        ∑ m ∈ smoothSubtypeFinset z y, smoothRankinWeight sigma m := by
      rw [Finset.mul_sum]
    _ ≤ (z : ℝ) ^ sigma *
        ∑' m : y.smoothNumbers, smoothRankinWeight sigma m := by
      gcongr
      exact heuler.2.summable.sum_le_tsum (smoothSubtypeFinset z y)
        (fun _m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (z : ℝ) ^ sigma *
        ∏ p ∈ y.primesBelow, (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
      rw [heuler.2.tsum_eq]
      simp [smoothRankinWeight]

/-- The explicit Rankin/Markov/union budget for the finite family of smooth
test points. -/
noncomputable def smoothContributionRankinBudget
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold sigma : ℕ → ℝ) (ell : ℕ) : ℝ :=
  ∑ r ∈ tests ell,
    ((z ell r : ℝ) ^ sigma ell *
      ∏ p ∈ (cutoff ell + 1).primesBelow,
        (1 - (p : ℝ) ^ (-sigma ell))⁻¹) /
      threshold ell ^ 2

theorem smoothContributionSecondMomentBudget_le_rankin
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold sigma : ℕ → ℝ) (hsigma : ∀ ell, 0 < sigma ell)
    (ell : ℕ) :
    smoothContributionSecondMomentBudget tests z cutoff threshold ell ≤
      smoothContributionRankinBudget tests z cutoff threshold sigma ell := by
  unfold smoothContributionSecondMomentBudget smoothContributionRankinBudget
  gcongr with r hr
  exact card_smoothNumbersUpTo_le_rankinProduct
    (hsigma ell) (z ell r) (cutoff ell + 1)

/-- Complete smooth-contribution conclusion from summability of the explicit
finite Rankin products.  Estimating these products for the chosen schedule is
the remaining analytic-number-theory task.
-/
theorem ae_eventually_smoothContribution_le_of_rankin
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold sigma : ℕ → ℝ)
    (hthreshold : ∀ ell, 0 < threshold ell)
    (hsigma : ∀ ell, 0 < sigma ell)
    (hsummable : Summable fun ell =>
      smoothContributionRankinBudget tests z cutoff threshold sigma ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (z ell r) (cutoff ell)| ≤ threshold ell := by
  apply ae_eventually_smoothContribution_le_of_summable_budget
    tests z cutoff threshold hthreshold
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold smoothContributionSecondMomentBudget
    positivity
  · intro ell
    exact smoothContributionSecondMomentBudget_le_rankin
      tests z cutoff threshold sigma hsigma ell
  · exact hsummable

/-!
## A uniform deterministic cardinality interface

Often the same smooth-number bound is used at every test point of one scale.
The following form identifies the exact remaining arithmetic obligation: a
uniform cardinality majorant whose elementary scalar Markov/union budget is
summable.
-/

/-- Scalar budget arising from a uniform smooth-number cardinality bound. -/
noncomputable def smoothContributionUniformBudget
    (tests : ℕ → Finset ℕ) (cardinalityBound threshold : ℕ → ℝ)
    (ell : ℕ) : ℝ :=
  (tests ell).card * cardinalityBound ell / threshold ell ^ 2

theorem smoothContributionSecondMomentBudget_le_uniform
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold cardinalityBound : ℕ → ℝ)
    (hcard : ∀ ell r, r ∈ tests ell →
      ((Nat.smoothNumbersUpTo (z ell r) (cutoff ell + 1)).card : ℝ) ≤
        cardinalityBound ell)
    (ell : ℕ) :
    smoothContributionSecondMomentBudget tests z cutoff threshold ell ≤
      smoothContributionUniformBudget tests cardinalityBound threshold ell := by
  unfold smoothContributionSecondMomentBudget smoothContributionUniformBudget
  calc
    (∑ r ∈ tests ell,
        (Nat.smoothNumbersUpTo (z ell r) (cutoff ell + 1)).card /
          threshold ell ^ 2)
        ≤ ∑ _r ∈ tests ell,
            cardinalityBound ell / threshold ell ^ 2 := by
      gcongr with r hr
      exact hcard ell r hr
    _ = (tests ell).card * cardinalityBound ell / threshold ell ^ 2 := by
      simp [mul_div_assoc]

/-- Fully probabilistic completion of the smooth-contribution step from a
deterministic uniform smooth-number estimate. -/
theorem ae_eventually_smoothContribution_le_of_uniform_cardinality
    (tests : ℕ → Finset ℕ) (z : ℕ → ℕ → ℕ) (cutoff : ℕ → ℕ)
    (threshold cardinalityBound : ℕ → ℝ)
    (hthreshold : ∀ ell, 0 < threshold ell)
    (hcard : ∀ ell r, r ∈ tests ell →
      ((Nat.smoothNumbersUpTo (z ell r) (cutoff ell + 1)).card : ℝ) ≤
        cardinalityBound ell)
    (hsummable : Summable fun ell =>
      smoothContributionUniformBudget tests cardinalityBound threshold ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (z ell r) (cutoff ell)| ≤ threshold ell := by
  apply ae_eventually_smoothContribution_le_of_summable_budget
    tests z cutoff threshold hthreshold
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold smoothContributionSecondMomentBudget
    positivity
  · intro ell
    exact smoothContributionSecondMomentBudget_le_uniform
      tests z cutoff threshold cardinalityBound hcard ell
  · exact hsummable

end Problem520
end Erdos

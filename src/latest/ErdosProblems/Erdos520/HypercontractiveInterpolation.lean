import ErdosProblems.Erdos520.CaichHypercontractive
import ErdosProblems.Erdos520.OrthogonalMaximal
import ErdosProblems.Erdos520.PublishedInterpolation
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# What hypercontractivity would have to prove for LTW interpolation

The finite Bonami/divisor-weight estimate does give a clean route to the
root-exponential interpolation statement.  The remaining input is an
explicit summability assertion for short-interval divisor energies.  The
coarse divisor estimate currently available in `CaichHypercontractive` does
not prove that assertion; it loses the interval length and is already too
large before taking a union over endpoints.
-/

/-- The integers `a+1,...,a+L`, encoded as an image of `range L`. -/
def caichIntervalSupport (a L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun k => a + k + 1

theorem sum_caichIntervalSupport_f (omega : Omega) (a L : ℕ) :
    ∑ n ∈ caichIntervalSupport a L, f omega n =
      fIntervalSum omega a L := by
  unfold caichIntervalSupport fIntervalSum
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact Nat.add_left_cancel (Nat.add_right_cancel hij)

theorem caichIntervalSupport_subset_Ioc {a L x : ℕ} (hax : a + L ≤ x) :
    caichIntervalSupport a L ⊆ Finset.Ioc 0 x := by
  intro n hn
  rw [caichIntervalSupport, Finset.mem_image] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  rw [Finset.mem_range] at hk
  rw [Finset.mem_Ioc]
  omega

/-- Exact Bonami coefficient energy for one multiplicative interval. -/
noncomputable def caichIntervalDivisorEnergy (r a L : ℕ) : ℝ :=
  ∑ n ∈ caichIntervalSupport a L,
    (orderedDivisorCount (2 * r - 1) n : ℝ)

theorem caichIntervalDivisorEnergy_nonneg (r a L : ℕ) :
    0 ≤ caichIntervalDivisorEnergy r a L := by
  unfold caichIntervalDivisorEnergy
  positivity

/-- The divisor estimate currently available in `CaichHypercontractive`
controls a short-interval energy only by the global upper endpoint.  In
particular, it retains no saving in the interval length `L`. -/
theorem caichIntervalDivisorEnergy_le_globalEndpoint
    (r : ℕ) (hr : 1 ≤ r) (a L x : ℕ) (hx : 3 ≤ x)
    (hax : a + L ≤ x) :
    caichIntervalDivisorEnergy r a L ≤
      (x : ℝ) * (2 * Real.log (x : ℝ)) ^ (2 * r - 2) := by
  have hm : 1 ≤ 2 * r - 1 := by omega
  have hcast : caichIntervalDivisorEnergy r a L =
      ((∑ n ∈ caichIntervalSupport a L,
        orderedDivisorCount (2 * r - 1) n : ℕ) : ℝ) := by
    unfold caichIntervalDivisorEnergy
    norm_cast
  rw [hcast]
  simpa only [show (2 * r - 1) - 1 = 2 * r - 2 by omega] using!
    sum_orderedDivisorCount_le_two_log (2 * r - 1) x
      (caichIntervalSupport a L) hm hx
        (caichIntervalSupport_subset_Ioc hax)

theorem integrable_abs_fIntervalSum_pow (r a L : ℕ) :
    Integrable (fun omega : Omega => |fIntervalSum omega a L| ^ (2 * r)) μ := by
  apply Integrable.of_bound
    (by
      simpa only [Real.norm_eq_abs] using!
        ((measurable_fIntervalSum a L).norm.pow_const (2 * r)).aestronglyMeasurable)
    ((L : ℝ) ^ (2 * r))
  filter_upwards [] with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_fIntervalSum_le omega a L) _

/-- The exact hypercontractive root-moment bound on a short interval. -/
theorem fIntervalSum_hypercontractive
    (r : ℕ) (hr : 1 ≤ r) (a L x : ℕ) (hax : a + L ≤ x) :
    (∫ omega, |fIntervalSum omega a L| ^ (2 * r) ∂μ) ^
        (1 / (r : ℝ)) ≤
      caichIntervalDivisorEnergy r a L := by
  have h := caichFiniteRMFSum_hypercontractive
    r hr x (caichIntervalSupport a L) (fun _ => 1)
      (caichIntervalSupport_subset_Ioc hax)
  simp only [caichFiniteRMFSum_one, one_pow, mul_one] at h
  simpa only [sum_caichIntervalSupport_f, caichIntervalDivisorEnergy] using! h

/-- Raw `2r`-moment form of the exact interval-energy estimate. -/
theorem integral_abs_fIntervalSum_pow_le_energy
    (r : ℕ) (hr : 1 ≤ r) (a L x : ℕ) (hax : a + L ≤ x) :
    (∫ omega, |fIntervalSum omega a L| ^ (2 * r) ∂μ) ≤
      caichIntervalDivisorEnergy r a L ^ r := by
  let I : ℝ := ∫ omega, |fIntervalSum omega a L| ^ (2 * r) ∂μ
  let E : ℝ := caichIntervalDivisorEnergy r a L
  have hI : 0 ≤ I := integral_nonneg fun omega => by positivity
  have hroot : I ^ (1 / (r : ℝ)) ≤ E := by
    simpa only [I, E] using! fIntervalSum_hypercontractive r hr a L x hax
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot r
  have hr0 : r ≠ 0 := by omega
  simpa only [I, E, one_div, Real.rpow_inv_natCast_pow hI hr0] using! hpow

/-- One-prefix Markov bound in the exact divisor-energy normalization. -/
theorem measureReal_abs_fIntervalSum_ge_le_energy
    (r : ℕ) (hr : 1 ≤ r) (a L x : ℕ) (hax : a + L ≤ x)
    {u : ℝ} (hu : 0 < u) :
    μ.real {omega | u ≤ |fIntervalSum omega a L|} ≤
      (caichIntervalDivisorEnergy r a L / u ^ 2) ^ r := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ)
    (ae_of_all μ fun omega => pow_nonneg (abs_nonneg _) (2 * r))
    (integrable_abs_fIntervalSum_pow r a L) (u ^ (2 * r))
  have hset : {omega | u ^ (2 * r) ≤
      |fIntervalSum omega a L| ^ (2 * r)} =
      {omega | u ≤ |fIntervalSum omega a L|} := by
    ext omega
    simpa only [Set.mem_setOf_eq] using!
      (pow_le_pow_iff_left₀ hu.le (abs_nonneg _)
        (by omega : 2 * r ≠ 0))
  rw [hset] at hmarkov
  have hmoment := integral_abs_fIntervalSum_pow_le_energy r hr a L x hax
  have hmul : u ^ (2 * r) *
      μ.real {omega | u ≤ |fIntervalSum omega a L|} ≤
        caichIntervalDivisorEnergy r a L ^ r := hmarkov.trans hmoment
  have hdiv :
      μ.real {omega | u ≤ |fIntervalSum omega a L|} ≤
        caichIntervalDivisorEnergy r a L ^ r / u ^ (2 * r) := by
    exact (le_div_iff₀ (pow_pos hu _)).2 (by simpa [mul_comm] using! hmul)
  calc
    μ.real {omega | u ≤ |fIntervalSum omega a L|} ≤
        caichIntervalDivisorEnergy r a L ^ r / u ^ (2 * r) := hdiv
    _ = (caichIntervalDivisorEnergy r a L / u ^ 2) ^ r := by
      rw [div_pow, pow_mul]

/-- The finite union cost for all prefixes of an interval of length `L`. -/
noncomputable def caichHypercontractiveIntervalCost
    (r a L : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (L + 1),
    (caichIntervalDivisorEnergy r a k / u ^ 2) ^ r

theorem caichHypercontractiveIntervalCost_nonneg
    (r a L : ℕ) (u : ℝ) :
    0 ≤ caichHypercontractiveIntervalCost r a L u := by
  unfold caichHypercontractiveIntervalCost
  apply Finset.sum_nonneg
  intro k hk
  exact pow_nonneg
    (div_nonneg (caichIntervalDivisorEnergy_nonneg r a k) (sq_nonneg u)) r

/-- Hypercontractivity plus a finite union controls the entire interval
maximum. -/
theorem measureReal_fIntervalPrefixMax_gt_le_hypercontractiveCost
    (r : ℕ) (hr : 1 ≤ r) (a L x : ℕ) (hax : a + L ≤ x)
    {u : ℝ} (hu : 0 < u) :
    μ.real {omega | u < fIntervalPrefixMax omega a L} ≤
      caichHypercontractiveIntervalCost r a L u := by
  have heq : {omega | u < fIntervalPrefixMax omega a L} =
      ⋃ k ∈ Finset.range (L + 1),
        {omega | u < |fIntervalSum omega a k|} := by
    ext omega
    simp [fIntervalPrefixMax, Finset.lt_sup'_iff]
  rw [heq]
  calc
    μ.real (⋃ k ∈ Finset.range (L + 1),
        {omega | u < |fIntervalSum omega a k|}) ≤
        ∑ k ∈ Finset.range (L + 1),
          μ.real {omega | u < |fIntervalSum omega a k|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (L + 1),
        (caichIntervalDivisorEnergy r a k / u ^ 2) ^ r := by
      gcongr with k hk
      have hkL : k ≤ L := Nat.le_of_lt_succ (by simpa using! hk)
      calc
        μ.real {omega | u < |fIntervalSum omega a k|} ≤
            μ.real {omega | u ≤ |fIntervalSum omega a k|} := by
          apply measureReal_mono
          · intro omega homega
            change u < |fIntervalSum omega a k| at homega
            change u ≤ |fIntervalSum omega a k|
            exact homega.le
          · finiteness
        _ ≤ (caichIntervalDivisorEnergy r a k / u ^ 2) ^ r :=
          measureReal_abs_fIntervalSum_ge_le_energy
            r hr a k x (by omega) hu
    _ = caichHypercontractiveIntervalCost r a L u := rfl

/-! ## Specialization to the exact LTW mesh -/

noncomputable def ltwHypercontractiveInterpolationCost
    (r i : ℕ) : ℝ :=
  caichHypercontractiveIntervalCost r (ltwRademacherTestPoint i)
    (ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i)
    (ltwInterpolationScale (ltwRademacherTestPoint (i + 1)))

def ltwHypercontractiveInterpolationFailure (i : ℕ) : Set Omega :=
  {omega | ltwInterpolationScale (ltwRademacherTestPoint (i + 1)) <
    fIntervalPrefixMax omega (ltwRademacherTestPoint i)
      (ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i)}

theorem eventually_ltwInterpolationScale_testPoint_pos :
    ∀ᶠ i : ℕ in atTop,
      0 < ltwInterpolationScale (ltwRademacherTestPoint (i + 1)) := by
  have htest : Tendsto (fun i => ltwRademacherTestPoint (i + 1)) atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [htest.eventually (eventually_ge_atTop 3)] with i hi
  unfold ltwInterpolationScale
  exact div_pos (Real.sqrt_pos.2 (by exact_mod_cast (show 0 <
    ltwRademacherTestPoint (i + 1) by omega)))
      (Real.log_pos (by exact_mod_cast (show 1 <
        ltwRademacherTestPoint (i + 1) by omega)))

theorem eventually_measureReal_ltwHypercontractiveInterpolationFailure_le
    (r : ℕ → ℕ) (hr : ∀ i, 1 ≤ r i) :
    ∀ᶠ i : ℕ in atTop,
      μ.real (ltwHypercontractiveInterpolationFailure i) ≤
        ltwHypercontractiveInterpolationCost (r i) i := by
  have htest : Tendsto (fun i => ltwRademacherTestPoint (i + 1)) atTop atTop :=
    tendsto_ltwRademacherTestPoint_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [htest.eventually (eventually_ge_atTop 3),
      eventually_ltwInterpolationScale_testPoint_pos] with i hi hscale
  have hmono := ltwRademacherTestPoint_mono (Nat.le_add_right i 1)
  have hadd : ltwRademacherTestPoint i +
      (ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i) =
        ltwRademacherTestPoint (i + 1) := Nat.add_sub_of_le hmono
  exact measureReal_fIntervalPrefixMax_gt_le_hypercontractiveCost
    (r i) (hr i) (ltwRademacherTestPoint i)
      (ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i)
      (ltwRademacherTestPoint (i + 1)) (by omega) hscale

/-- A summable exact divisor-energy cost would prove the precise LTW
Rademacher interpolation proposition. -/
theorem LauTenenbaumWuRademacherInterpolation_of_hypercontractiveCost
    (r : ℕ → ℕ) (hr : ∀ i, 1 ≤ r i)
    (hcost : Summable fun i =>
      ltwHypercontractiveInterpolationCost (r i) i) :
    LauTenenbaumWuRademacherInterpolation := by
  have hmeasure : Summable fun i =>
      μ.real (ltwHypercontractiveInterpolationFailure i) := by
    apply hcost.of_norm_bounded_eventually_nat
    filter_upwards [eventually_measureReal_ltwHypercontractiveInterpolationFailure_le
      r hr] with i hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using! hi
  have hbc : ∀ᵐ omega ∂μ, ∀ᶠ i : ℕ in atTop,
      omega ∉ ltwHypercontractiveInterpolationFailure i := by
    apply ae_eventually_notMem
    have heq : (fun i => μ (ltwHypercontractiveInterpolationFailure i)) =
        fun i => ENNReal.ofReal
          (μ.real (ltwHypercontractiveInterpolationFailure i)) := by
      funext i
      exact (ofReal_measureReal
        (μ := μ) (s := ltwHypercontractiveInterpolationFailure i)).symm
    rw [heq]
    exact hmeasure.tsum_ofReal_ne_top
  filter_upwards [hbc] with omega homega
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [homega] with i hi
  intro N hiN hNi
  have hdiff : N - ltwRademacherTestPoint i ≤
      ltwRademacherTestPoint (i + 1) - ltwRademacherTestPoint i :=
    Nat.sub_le_sub_right hNi _
  have hinc := abs_fIntervalSum_le_prefixMax omega
    (ltwRademacherTestPoint i) hdiff
  have hsum := partialSum_add_sub omega (ltwRademacherTestPoint i)
    (N - ltwRademacherTestPoint i)
  rw [Nat.add_sub_of_le hiN.le] at hsum
  rw [hsum]
  exact hinc.trans (by
    have hi' : ¬ltwInterpolationScale
        (ltwRademacherTestPoint (i + 1)) <
          fIntervalPrefixMax omega (ltwRademacherTestPoint i)
            (ltwRademacherTestPoint (i + 1) -
              ltwRademacherTestPoint i) := by
      simpa only [ltwHypercontractiveInterpolationFailure,
        Set.mem_setOf_eq] using! hi
    simpa using! not_lt.mp hi')

end Problem520
end Erdos

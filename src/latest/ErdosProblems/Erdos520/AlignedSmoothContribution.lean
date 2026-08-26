import ErdosProblems.Erdos520.AlignedGlobalTestAssembly
import ErdosProblems.Erdos520.AlignedClampedSchedule
import ErdosProblems.Erdos520.SmoothScheduleBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# The smooth contribution on the aligned root-exponential mesh

This file verifies the explicit Rankin geometry from `SmoothScheduleBudget`
for the aligned macro blocks.  The smooth cutoff is the initial aligned thin
endpoint `X_(ell-2)`, and the endpoint `z` ranges over the root-exponential
tests in `(X_(ell-1), X_ell]`.

All prime-reciprocal input is supplied by the unconditional Chebyshev bound
already proved in `ThinScheduleChebyshev`; no analytic hypothesis remains in
the final theorem.
-/

/-- Discard a finite initial segment of a scale-indexed test family. -/
def testsFrom (S : ℕ) (tests : ℕ → Finset ℕ) (ell : ℕ) : Finset ℕ :=
  if S ≤ ell then tests ell else ∅

theorem mem_testsFrom_iff {S ell r : ℕ} {tests : ℕ → Finset ℕ} :
    r ∈ testsFrom S tests ell ↔ S ≤ ell ∧ r ∈ tests ell := by
  by_cases h : S ≤ ell
  · simp [testsFrom, h]
  · simp [testsFrom, h]

theorem eventually_testsFrom_eq (S : ℕ) (tests : ℕ → Finset ℕ) :
    ∀ᶠ ell : ℕ in atTop, testsFrom S tests ell = tests ell := by
  filter_upwards [eventually_ge_atTop S] with ell hell
  simp [testsFrom, hell]

/-- Exact logarithm of an aligned outer endpoint. -/
theorem log_alignedOuterEndpoint (K ell : ℕ) :
    Real.log (alignedOuterEndpoint K ell : ℝ) =
      (alignedOuterExponent K ell : ℝ) * Real.log 2 := by
  unfold alignedOuterEndpoint
  rw [show (((2 ^ alignedOuterExponent K ell : ℕ) : ℝ)) =
      (2 : ℝ) ^ alignedOuterExponent K ell by norm_cast,
    Real.log_pow]

/-- Exact logarithm of the power-of-two exponent in an outer endpoint. -/
theorem log_alignedOuterExponent (K ell : ℕ) :
    Real.log (alignedOuterExponent K ell : ℝ) =
      (ell : ℝ) ^ K * Real.log 2 := by
  unfold alignedOuterExponent
  rw [show (((2 ^ ell ^ K : ℕ) : ℝ)) = (2 : ℝ) ^ (ell ^ K) by norm_cast,
    Real.log_pow]
  norm_cast

/-- A one-step macro exponent gap contains at least `ell-2` binary doublings. -/
theorem alignedOuterExponent_mul_two_pow_sub_two_le_previous
    {K ell : ℕ} (hK : 2 ≤ K) (hell : 3 ≤ ell) :
    alignedOuterExponent K (ell - 2) * 2 ^ (ell - 2) ≤
      alignedOuterExponent K (ell - 1) := by
  let a : ℕ := ell - 2
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hpow : a ≤ a ^ (K - 1) :=
    le_self_pow₀ ha (by omega : K - 1 ≠ 0)
  have hmul : a ≤ K * a ^ (K - 1) := by
    exact hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hbern : a ^ K + K * a ^ (K - 1) * 1 ≤ (a + 1) ^ K := by
    exact pow_add_mul_le_add_pow (R := ℕ) (by omega) (by omega) K
  have hexponents : a ^ K + a ≤ (a + 1) ^ K := by
    exact (Nat.add_le_add_left (by simpa using! hmul) _).trans (by simpa using! hbern)
  unfold alignedOuterExponent
  have hpowTwo : 2 ^ (a ^ K + a) ≤ 2 ^ ((a + 1) ^ K) :=
    Nat.pow_le_pow_right (by norm_num) hexponents
  rw [pow_add] at hpowTwo
  simpa only [a, show ell - 1 = (ell - 2) + 1 by omega] using! hpowTwo

/-- A fixed polynomial is eventually dominated by the binary factor present
in the gap between the initial smooth cutoff and the preceding macro scale. -/
theorem eventually_mul_pow_le_two_pow_sub_two_mul_log_two
    (A : ℝ) (K : ℕ) :
    ∀ᶠ ell : ℕ in atTop,
      A * (ell : ℝ) ^ K ≤ ((2 ^ (ell - 2) : ℕ) : ℝ) * Real.log 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : Tendsto
      (fun ell : ℕ =>
        Real.exp (Real.log 2 * (ell : ℝ)) /
          (ell : ℝ) ^ (K : ℝ)) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop (K : ℝ) (Real.log 2) hlog).comp
      tendsto_natCast_atTop_atTop
  have hratio : ∀ᶠ ell : ℕ in atTop,
      4 * A / Real.log 2 ≤
        Real.exp (Real.log 2 * (ell : ℝ)) /
          (ell : ℝ) ^ (K : ℝ) :=
    ht.eventually (eventually_ge_atTop (4 * A / Real.log 2))
  filter_upwards [hratio, eventually_ge_atTop (2 : ℕ)] with ell hellRatio hell
  have hellR : (0 : ℝ) < ell := by positivity
  have hdenom : 0 < (ell : ℝ) ^ (K : ℝ) :=
    Real.rpow_pos_of_pos hellR _
  have hcross :
      (4 * A / Real.log 2) * (ell : ℝ) ^ K ≤
        ((2 ^ ell : ℕ) : ℝ) := by
    have h := (le_div_iff₀ hdenom).mp hellRatio
    rw [Real.rpow_natCast] at h
    have hexp : Real.exp (Real.log 2 * (ell : ℝ)) =
        ((2 ^ ell : ℕ) : ℝ) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      norm_cast
    simpa only [hexp] using! h
  have htwo : ((2 ^ ell : ℕ) : ℝ) =
      4 * ((2 ^ (ell - 2) : ℕ) : ℝ) := by
    rw [show ell = (ell - 2) + 2 by omega, pow_add]
    norm_num
    ring
  rw [htwo] at hcross
  calc
    A * (ell : ℝ) ^ K =
        ((4 * A / Real.log 2) * (ell : ℝ) ^ K) *
          (Real.log 2 / 4) := by field_simp
    _ ≤ (4 * ((2 ^ (ell - 2) : ℕ) : ℝ)) *
          (Real.log 2 / 4) :=
      mul_le_mul_of_nonneg_right hcross (by positivity)
    _ = ((2 ^ (ell - 2) : ℕ) : ℝ) * Real.log 2 := by ring

/-- The Rankin saving available between `X_(ell-2)` and every selected test
point dominates any fixed polynomial multiple of `ell^K`, eventually. -/
theorem eventually_alignedSmoothRankinSaving
    {A : ℝ} {K m : ℕ} (hK : 2 ≤ K) :
    ∀ᶠ ell : ℕ in atTop, ∀ r ∈ alignedRootExpTests K m ell,
      (A * (ell : ℝ) ^ K) *
          (alignedThinExponent K ell 0 : ℝ) ≤
        Real.log (alignedRootExpTestPoint m r : ℝ) := by
  filter_upwards [eventually_mul_pow_le_two_pow_sub_two_mul_log_two A K,
      eventually_ge_atTop (5 : ℕ)] with ell hpoly hell
  intro r hr
  have hzLower : alignedOuterEndpoint K (ell - 1) <
      alignedRootExpTestPoint m r := by
    unfold alignedRootExpTests at hr
    rw [if_neg (by omega : ¬ell < 5)] at hr
    exact (Finset.mem_filter.mp hr).2.1
  have hgap := alignedOuterExponent_mul_two_pow_sub_two_le_previous hK
    (show 3 ≤ ell by omega)
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hlogLower :
      Real.log (alignedOuterEndpoint K (ell - 1) : ℝ) <
        Real.log (alignedRootExpTestPoint m r : ℝ) := by
    apply Real.strictMonoOn_log
    · change (0 : ℝ) < (alignedOuterEndpoint K (ell - 1) : ℝ)
      exact_mod_cast (show 0 < alignedOuterEndpoint K (ell - 1) by
        unfold alignedOuterEndpoint
        positivity)
    · change (0 : ℝ) < (alignedRootExpTestPoint m r : ℝ)
      exact_mod_cast (show 0 < alignedRootExpTestPoint m r by omega)
    · exact_mod_cast hzLower
  calc
    (A * (ell : ℝ) ^ K) * (alignedThinExponent K ell 0 : ℝ) ≤
        (((2 ^ (ell - 2) : ℕ) : ℝ) * Real.log 2) *
          (alignedThinExponent K ell 0 : ℝ) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = ((alignedOuterExponent K (ell - 2) * 2 ^ (ell - 2) : ℕ) : ℝ) *
          Real.log 2 := by
      rw [alignedThinExponent_zero, Nat.cast_mul]
      ring
    _ ≤ (alignedOuterExponent K (ell - 1) : ℝ) * Real.log 2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgap) hlog
    _ = Real.log (alignedOuterEndpoint K (ell - 1) : ℝ) :=
      (log_alignedOuterEndpoint K (ell - 1)).symm
    _ ≤ Real.log (alignedRootExpTestPoint m r : ℝ) := hlogLower.le

/-! ## Specializing the explicit Rankin geometry -/

/-- One fixed coefficient large enough for the Euler loss, test entropy, and
linear Borel--Cantelli saving. -/
noncomputable def alignedSmoothRankinCoefficient
    (C : ℝ) (N m : ℕ) : ℝ :=
  max 2 (max (8 * smoothRankinLogConstant C N) (4 * (2 * m + 2 : ℕ)))

theorem two_le_alignedSmoothRankinCoefficient (C : ℝ) (N m : ℕ) :
    2 ≤ alignedSmoothRankinCoefficient C N m :=
  le_max_left _ _

theorem eight_mul_smoothRankinLogConstant_le_coefficient
    (C : ℝ) (N m : ℕ) :
    8 * smoothRankinLogConstant C N ≤
      alignedSmoothRankinCoefficient C N m :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem four_mul_alignedRootExpEntropy_le_coefficient
    (C : ℝ) (N m : ℕ) :
    4 * (2 * m + 2 : ℕ) ≤ alignedSmoothRankinCoefficient C N m :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem alignedSmoothRankinCoefficient_nonneg (C : ℝ) (N m : ℕ) :
    0 ≤ alignedSmoothRankinCoefficient C N m := by
  exact (show (0 : ℝ) ≤ 2 by norm_num).trans
    (two_le_alignedSmoothRankinCoefficient C N m)

/-- The polynomial Rankin-saving budget used at outer scale `ell`. -/
noncomputable def alignedSmoothRankinU
    (C : ℝ) (N m K ell : ℕ) : ℝ :=
  alignedSmoothRankinCoefficient C N m * (ell : ℝ) ^ K

/-- The initial power-of-two exponent eventually exceeds the fixed Chebyshev
cutoff. -/
theorem eventually_le_alignedThinInitialExponent
    {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∀ᶠ ell : ℕ in atTop, N ≤ alignedThinExponent K ell 0 := by
  filter_upwards [eventually_ge_atTop (N + 3)] with ell hell
  let a : ℕ := ell - 2
  have hNa : N ≤ a := by dsimp [a]; omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hapow : a ≤ a ^ K :=
    le_self_pow₀ ha (by omega : K ≠ 0)
  rw [alignedThinExponent_zero]
  unfold alignedOuterExponent
  exact hNa.trans (hapow.trans (Nat.lt_two_pow_self (n := a ^ K)).le)

/-- Every selected test point eventually has iterated logarithm at least one. -/
theorem eventually_one_le_log₂_alignedRootExpTestPoint
    {K m : ℕ} (hK : 1 ≤ K) :
    ∀ᶠ ell : ℕ in atTop, ∀ r ∈ alignedRootExpTests K m ell,
      1 ≤ log₂ (alignedRootExpTestPoint m r) := by
  let c : ℝ := 1 / (3 * (2 : ℝ) ^ K)
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : Tendsto (fun ell : ℕ => c * (ell : ℝ) ^ K) atTop atTop :=
    (Filter.tendsto_const_mul_pow_atTop (α := ℝ)
      (by omega : K ≠ 0) hc).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))]
    with ell hell
  intro r hr
  exact hell.trans (by
    simpa only [c] using!
      (alignedRootExpTestPoint_log₂_scale_lower hK hr))

/-- The logarithmic Euler-product loss is absorbed by one half of the fixed
coefficient, uniformly beyond the first natural scale. -/
theorem alignedSmoothRankinEulerGeometry
    {C : ℝ} {N m K ell : ℕ} (hC : 0 ≤ C) (hN : 2 ≤ N)
    (hell : 1 ≤ ell) :
    4 * smoothRankinLogConstant C N *
        (1 + Real.log (alignedThinExponent K ell 0 : ℝ)) ≤
      alignedSmoothRankinU C N m K ell := by
  have hpowNat : (ell - 2) ^ K ≤ ell ^ K :=
    Nat.pow_le_pow_left (Nat.sub_le ell 2) K
  have hpow : ((ell - 2 : ℕ) : ℝ) ^ K ≤ (ell : ℝ) ^ K := by
    exact_mod_cast hpowNat
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hlogTwoNonneg : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hpowOne : (1 : ℝ) ≤ (ell : ℝ) ^ K := by
    exact one_le_pow₀ (by exact_mod_cast hell)
  have hlogBound :
      1 + Real.log (alignedThinExponent K ell 0 : ℝ) ≤
        2 * (ell : ℝ) ^ K := by
    rw [alignedThinExponent_zero, log_alignedOuterExponent]
    have hmul : ((ell - 2 : ℕ) : ℝ) ^ K * Real.log 2 ≤
        (ell : ℝ) ^ K := by
      calc
        ((ell - 2 : ℕ) : ℝ) ^ K * Real.log 2 ≤
            (ell : ℝ) ^ K * Real.log 2 :=
          mul_le_mul_of_nonneg_right hpow hlogTwoNonneg
        _ ≤ (ell : ℝ) ^ K * 1 :=
          mul_le_mul_of_nonneg_left hlogTwo (by positivity)
        _ = (ell : ℝ) ^ K := by ring
    linarith
  have hD : 0 ≤ smoothRankinLogConstant C N :=
    (smoothRankinLogConstant_pos hC hN).le
  calc
    4 * smoothRankinLogConstant C N *
          (1 + Real.log (alignedThinExponent K ell 0 : ℝ)) ≤
        4 * smoothRankinLogConstant C N * (2 * (ell : ℝ) ^ K) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = (8 * smoothRankinLogConstant C N) * (ell : ℝ) ^ K := by ring
    _ ≤ alignedSmoothRankinCoefficient C N m * (ell : ℝ) ^ K :=
      mul_le_mul_of_nonneg_right
        (eight_mul_smoothRankinLogConstant_le_coefficient C N m)
        (by positivity)
    _ = alignedSmoothRankinU C N m K ell := rfl

/-- The exact aligned test entropy consumes at most one quarter of `U`. -/
theorem card_alignedRootExpTests_le_exp_alignedSmoothRankinU
    (C : ℝ) (N K m ell : ℕ) :
    ((alignedRootExpTests K m ell).card : ℝ) ≤
      Real.exp (alignedSmoothRankinU C N m K ell / 4) := by
  have hcard := card_alignedRootExpTests_le_exp_entropy K m ell
  apply hcard.trans
  apply Real.exp_le_exp.mpr
  have hpow : 0 ≤ (ell : ℝ) ^ (K : ℝ) := Real.rpow_nonneg (by positivity) _
  have hcoef := four_mul_alignedRootExpEntropy_le_coefficient C N m
  rw [alignedSmoothRankinU, Real.rpow_natCast]
  calc
    ((2 * m + 2 : ℕ) : ℝ) * (ell : ℝ) ^ K =
        (4 * (2 * m + 2 : ℕ) : ℝ) * (ell : ℝ) ^ K / 4 := by
      norm_num
      ring
    _ ≤ alignedSmoothRankinCoefficient C N m * (ell : ℝ) ^ K / 4 := by
      gcongr

/-- The chosen `U` dominates the linear summability budget at every scale. -/
theorem two_mul_scale_le_alignedSmoothRankinU
    (C : ℝ) (N m : ℕ) {K ell : ℕ} (hK : 1 ≤ K) :
    2 * (ell : ℝ) ≤ alignedSmoothRankinU C N m K ell := by
  by_cases hell : ell = 0
  · subst ell
    simp [alignedSmoothRankinU, show K ≠ 0 by omega]
  have hellOne : 1 ≤ ell := Nat.one_le_iff_ne_zero.mpr hell
  have hpowNat : ell ≤ ell ^ K :=
    le_self_pow₀ hellOne (by omega : K ≠ 0)
  have hpow : (ell : ℝ) ≤ (ell : ℝ) ^ K := by exact_mod_cast hpowNat
  calc
    2 * (ell : ℝ) ≤ 2 * (ell : ℝ) ^ K :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ alignedSmoothRankinCoefficient C N m * (ell : ℝ) ^ K :=
      mul_le_mul_of_nonneg_right
        (two_le_alignedSmoothRankinCoefficient C N m) (by positivity)
    _ = alignedSmoothRankinU C N m K ell := rfl

/-! ## Unconditional almost-sure smooth bound -/

/-- On the exact aligned root-exponential test mesh, the contribution smooth
at the initial thin cutoff is almost surely eventually bounded by the full
critical test threshold.

This theorem has no prime-number or smooth-number hypothesis: Chebyshev's
unconditional prime-counting bound is chosen internally. -/
theorem ae_eventually_smoothContribution_alignedRootExpTests
    {K m : ℕ} (hK : 2 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m r)
            (alignedThinEndpoint K ell 0)| ≤
          criticalScale η (alignedRootExpTestPoint m r) := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  let A : ℝ := alignedSmoothRankinCoefficient C N m
  let U : ℕ → ℝ := fun ell => alignedSmoothRankinU C N m K ell
  have hsaving : ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ alignedRootExpTests K m ell,
        U ell * (alignedThinExponent K ell 0 : ℝ) ≤
          Real.log (alignedRootExpTestPoint m r : ℝ) := by
    simpa only [U, alignedSmoothRankinU, A] using!
      (eventually_alignedSmoothRankinSaving
        (A := alignedSmoothRankinCoefficient C N m) hK)
  have hE : ∀ᶠ ell : ℕ in atTop,
      N ≤ alignedThinExponent K ell 0 :=
    eventually_le_alignedThinInitialExponent (by omega) N
  have hlogOne : ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ alignedRootExpTests K m ell,
        1 ≤ log₂ (alignedRootExpTestPoint m r) :=
    eventually_one_le_log₂_alignedRootExpTestPoint (by omega)
  have hgeometry : ∀ᶠ ell : ℕ in atTop,
      (∀ r ∈ alignedRootExpTests K m ell,
        U ell * (alignedThinExponent K ell 0 : ℝ) ≤
          Real.log (alignedRootExpTestPoint m r : ℝ)) ∧
      N ≤ alignedThinExponent K ell 0 ∧
      (∀ r ∈ alignedRootExpTests K m ell,
        1 ≤ log₂ (alignedRootExpTestPoint m r)) ∧
      5 ≤ ell := by
    filter_upwards [hsaving, hE, hlogOne,
        eventually_ge_atTop (5 : ℕ)] with ell hs hEell hlog hell
    exact ⟨hs, hEell, hlog, hell⟩
  rw [eventually_atTop] at hgeometry
  obtain ⟨S, hS⟩ := hgeometry
  let tailTests : ℕ → Finset ℕ :=
    testsFrom S (alignedRootExpTests K m)
  have htail :=
    ae_eventually_smoothContributionPointwise_powerTwo_of_logGeometry
      hC.le hP hN tailTests
      (fun _ell r => alignedRootExpTestPoint m r)
      (fun ell _r => alignedThinExponent K ell 0)
      (fun _ell r => criticalScale η (alignedRootExpTestPoint m r))
      U
      (by
        intro ell r hr
        obtain ⟨hSell, _hr⟩ := (mem_testsFrom_iff.mp hr)
        exact (hS ell hSell).2.1)
      (by
        intro ell r hr
        obtain ⟨hSell, hrTests⟩ := (mem_testsFrom_iff.mp hr)
        have hlarge := (hS ell hSell).2.2.2
        have hcutoffLt := alignedThinInitial_lt_testPoint_of_mem hrTests
        exact (show 0 < alignedThinEndpoint K ell 0 by
          unfold alignedThinEndpoint
          positivity).trans hcutoffLt)
      (by
        intro ell r hr
        obtain ⟨hSell, hrTests⟩ := (mem_testsFrom_iff.mp hr)
        exact (hS ell hSell).1 r hrTests)
      (by
        intro ell r hr
        obtain ⟨hSell, _hrTests⟩ := (mem_testsFrom_iff.mp hr)
        exact alignedSmoothRankinEulerGeometry hC.le hN
          (show 1 ≤ ell by have := (hS ell hSell).2.2.2; omega))
      (by
        intro ell r hr
        obtain ⟨hSell, hrTests⟩ := (mem_testsFrom_iff.mp hr)
        have hgood := hS ell hSell
        have hz : 0 < alignedRootExpTestPoint m r := by
          have hcutoffLt := alignedThinInitial_lt_testPoint_of_mem hrTests
          exact (show 0 < alignedThinEndpoint K ell 0 by
            unfold alignedThinEndpoint
            positivity).trans hcutoffLt
        have hlogPos : 0 < log₂ (alignedRootExpTestPoint m r) :=
          zero_lt_one.trans_le (hgood.2.2.1 r hrTests)
        unfold criticalScale
        exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hz))
          (Real.rpow_pos_of_pos hlogPos _))
      (by
        intro ell r hr
        obtain ⟨hSell, hrTests⟩ := (mem_testsFrom_iff.mp hr)
        have hgood := hS ell hSell
        let z : ℕ := alignedRootExpTestPoint m r
        let q : ℝ := log₂ z ^ (1 / 4 + η)
        have hz : 0 < z := by
          have hcutoffLt := alignedThinInitial_lt_testPoint_of_mem hrTests
          exact (show 0 < alignedThinEndpoint K ell 0 by
            unfold alignedThinEndpoint
            positivity).trans hcutoffLt
        have hqOne : 1 ≤ q := by
          dsimp [q]
          exact Real.one_le_rpow (hgood.2.2.1 r hrTests) (by linarith)
        have hqSq : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
        calc
          (alignedRootExpTestPoint m r : ℝ) = (z : ℝ) * 1 := by
            simp [z]
          _ ≤ (z : ℝ) * q ^ 2 :=
            mul_le_mul_of_nonneg_left hqSq (by positivity)
          _ = criticalScale η (alignedRootExpTestPoint m r) ^ 2 := by
            unfold criticalScale
            dsimp [z, q]
            rw [mul_pow, Real.sq_sqrt (by positivity)] )
      (by
        intro ell
        by_cases hSell : S ≤ ell
        · simpa only [tailTests, testsFrom, if_pos hSell] using!
            card_alignedRootExpTests_le_exp_alignedSmoothRankinU
              C N K m ell
        · simpa only [tailTests, testsFrom, if_neg hSell, Finset.card_empty,
              Nat.cast_zero] using! (Real.exp_pos (U ell / 4)).le)
      (by
        intro ell
        exact two_mul_scale_le_alignedSmoothRankinU C N m
          (K := K) (ell := ell) (by omega))
  filter_upwards [htail] with omega homega
  filter_upwards [homega, eventually_ge_atTop S] with ell hell hSell
  intro r hr
  have hrTail : r ∈ tailTests ell := by
    simpa only [tailTests, testsFrom, if_pos hSell] using! hr
  simpa only [alignedThinEndpoint] using! hell r hrTail

/-- Equivalent form using the total clamped schedule.  Since the clamp is
eventually inactive, its initial cutoff is literally the aligned cutoff at
the outer test level. -/
theorem ae_eventually_smoothContribution_clampedAlignedRootExpTests
    (S : ℕ) {K m : ℕ} (hK : 2 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ alignedRootExpTests K m ell,
        |Ψ omega (alignedRootExpTestPoint m r)
            (alignedThinEndpoint K (clampedAlignedScale S ell) 0)| ≤
          criticalScale η (alignedRootExpTestPoint m r) := by
  have hbase :=
    ae_eventually_smoothContribution_alignedRootExpTests
      (K := K) (m := m) hK hη
  filter_upwards [hbase] with omega homega
  filter_upwards [homega, eventually_clampedAlignedScale_eq S]
    with ell hell hscale
  simpa only [hscale] using! hell

end Problem520
end Erdos

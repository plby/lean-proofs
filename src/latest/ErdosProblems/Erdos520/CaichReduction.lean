import ErdosProblems.Erdos520.Basic
import ErdosProblems.Erdos520.ThinBlock
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Asymptotics Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# The downstream Caich reduction

This file starts after the conditional thin-block moment estimate has been
converted into a `2⁻ell` tail for each prime block.  It formalizes the parts of
the argument which no longer use the arithmetic definition of the random
multiplicative function:

* the honest union bound over polynomially many prime blocks;
* summability and the first Borel--Cantelli lemma;
* the exponent gap in the stopped-concentration estimate;
* transfer from scale indices to all natural inputs; and
* conversion to `CriticalUpperBound`.

No declaration below is an axiom.  The structure at the end records, as named
fields, the paper-derived inputs which still have to be instantiated.
-/

/-- The failure at scale `ell`: either the Euler-product small-energy event
fails, or one of the `J` thin prime blocks has excessive maximal energy while
its past Euler-product energy is at most the small-energy threshold.

The `j`th member of `Finset.range J` represents paper index `j + 1`, so this is
the union over exactly `1 ≤ j ≤ J`.
-/
def thinBlockFailure {Ω : Type*}
    (smallEnergyBad : Set Ω) (thinBad : ℕ → Set Ω) (J : ℕ) : Set Ω :=
  smallEnergyBad ∪ ⋃ j ∈ Finset.range J, thinBad (j + 1)

/-- The finite union bound used in equation (27), stated for real-valued
measures so that it composes directly with ordinary real summability.
-/
theorem measureReal_thinBlockFailure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (smallEnergyBad : Set Ω) (thinBad : ℕ → Set Ω)
    (J : ℕ) (q : ℝ)
    (hthin : ∀ j, j ∈ Finset.range J → μ.real (thinBad (j + 1)) ≤ q) :
    μ.real (thinBlockFailure smallEnergyBad thinBad J)
      ≤ μ.real smallEnergyBad + (J : ℝ) * q := by
  rw [thinBlockFailure]
  calc
    μ.real (smallEnergyBad ∪ ⋃ j ∈ Finset.range J, thinBad (j + 1))
        ≤ μ.real smallEnergyBad +
            μ.real (⋃ j ∈ Finset.range J, thinBad (j + 1)) :=
      measureReal_union_le _ _
    _ ≤ μ.real smallEnergyBad +
          ∑ j ∈ Finset.range J, μ.real (thinBad (j + 1)) := by
      gcongr
      exact measureReal_biUnion_finset_le _ _
    _ ≤ μ.real smallEnergyBad + ∑ _j ∈ Finset.range J, q := by
      gcongr with j hj
      exact hthin j hj
    _ = μ.real smallEnergyBad + (J : ℝ) * q := by simp

/-- Polynomially many `2⁻ell` tails, together with any already summable
small-energy failure budget, remain summable.
-/
theorem summable_measureReal_thinBlockFailure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (smallEnergyBad : ℕ → Set Ω) (thinBad : ℕ → ℕ → Set Ω)
    (J : ℕ → ℕ) (D : ℝ) (K : ℕ)
    (hJ : ∀ ell, (J ell : ℝ) ≤ D * (ell : ℝ) ^ K)
    (hsmall : Summable fun ell => μ.real (smallEnergyBad ell))
    (hthin : ∀ ell j, j ∈ Finset.range (J ell) →
      μ.real (thinBad ell (j + 1)) ≤ (1 / 2 : ℝ) ^ ell) :
    Summable fun ell =>
      μ.real (thinBlockFailure (smallEnergyBad ell) (thinBad ell) (J ell)) := by
  apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _
    (hsmall.add (summable_const_mul_polynomial_mul_two_pow D K))
  intro ell
  refine (measureReal_thinBlockFailure_le μ _ _ _ _ (hthin ell)).trans ?_
  rw [add_le_add_iff_left]
  calc
    (J ell : ℝ) * (1 / 2 : ℝ) ^ ell
        ≤ (D * (ell : ℝ) ^ K) * (1 / 2 : ℝ) ^ ell :=
      mul_le_mul_of_nonneg_right (hJ ell) (pow_nonneg (by norm_num) ell)
    _ = D * ((ell : ℝ) ^ K * (1 / 2 : ℝ) ^ ell) := by ring

/-- A real-summable sequence of failure measures occurs only finitely often
almost surely.  This is the real-valued wrapper around Mathlib's first
Borel--Cantelli lemma.
-/
theorem ae_eventually_notMem_of_summable_measureReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {bad : ℕ → Set Ω} (hbad : Summable fun ell => μ.real (bad ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop, omega ∉ bad ell := by
  apply ae_eventually_notMem
  have heq : (fun ell => μ (bad ell)) =
      (fun ell => ENNReal.ofReal (μ.real (bad ell))) := by
    funext ell
    exact (ofReal_measureReal (μ := μ) (s := bad ell)).symm
  rw [heq]
  exact hbad.tsum_ofReal_ne_top

/-- Equation (27) followed by Borel--Cantelli: the maximum thin-block energy
is eventually controlled almost surely once the small-energy failures are
summable, the number of blocks is polynomial, and each block has `2⁻ell`
tail.
-/
theorem ae_eventually_thinBlockGood
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (smallEnergyBad : ℕ → Set Ω) (thinBad : ℕ → ℕ → Set Ω)
    (J : ℕ → ℕ) (D : ℝ) (K : ℕ)
    (hJ : ∀ ell, (J ell : ℝ) ≤ D * (ell : ℝ) ^ K)
    (hsmall : Summable fun ell => μ.real (smallEnergyBad ell))
    (hthin : ∀ ell j, j ∈ Finset.range (J ell) →
      μ.real (thinBad ell (j + 1)) ≤ (1 / 2 : ℝ) ^ ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      omega ∉ thinBlockFailure (smallEnergyBad ell) (thinBad ell) (J ell) :=
  ae_eventually_notMem_of_summable_measureReal
    (summable_measureReal_thinBlockFailure μ smallEnergyBad thinBad J D K
      hJ hsmall hthin)

/-- A convenient comparison-test wrapper for stopped-concentration errors.
Any nonnegative sequence eventually bounded by `exp (-ell)` is summable.
-/
theorem summable_of_eventually_le_exp_neg_nat {u : ℕ → ℝ}
    (hu : ∀ ell, 0 ≤ u ell)
    (hbound : ∀ᶠ ell : ℕ in atTop, u ell ≤ Real.exp (-(ell : ℝ))) :
    Summable u := by
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [hbound] with ell hell
  simpa [Real.norm_eq_abs, abs_of_nonneg (hu ell)] using! hell

/-- A logarithmic power cannot spoil a convergent power-law budget.  This is
the summability calculation behind Caich's
`T₁(ell)⁻¹/⁶ ≍ (log ell)¹/⁶ ell⁻³/²` small-energy failure probability.
-/
theorem summable_log_rpow_mul_nat_rpow_neg (a : ℝ) {b : ℝ} (hb : 1 < b) :
    Summable fun ell : ℕ =>
      Real.log (ell : ℝ) ^ a * (ell : ℝ) ^ (-b) := by
  let s : ℝ := (b - 1) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hpower : s - b < -1 := by dsimp [s]; linarith
  have hlog := isLittleO_log_rpow_rpow_atTop a hs
  have hboundReal :
      ∀ᶠ x : ℝ in atTop, Real.log x ^ a ≤ x ^ s := by
    filter_upwards [hlog.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hxone
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogNonneg _),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hxone) _)] using! hx
  have hboundNat :
      ∀ᶠ ell : ℕ in atTop,
        Real.log (ell : ℝ) ^ a ≤ (ell : ℝ) ^ s :=
    tendsto_natCast_atTop_atTop.eventually hboundReal
  apply (Real.summable_nat_rpow.mpr hpower).of_norm_bounded_eventually_nat
  filter_upwards [hboundNat, eventually_ge_atTop (1 : ℕ)] with ell hell hellOne
  have hxOne : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hellOne
  have hxPos : (0 : ℝ) < (ell : ℝ) := zero_lt_one.trans_le hxOne
  have hlogNonneg : 0 ≤ Real.log (ell : ℝ) := Real.log_nonneg hxOne
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hlogNonneg _) (Real.rpow_nonneg hxPos.le _))]
  calc
    Real.log (ell : ℝ) ^ a * (ell : ℝ) ^ (-b)
        ≤ (ell : ℝ) ^ s * (ell : ℝ) ^ (-b) :=
      mul_le_mul_of_nonneg_right hell (Real.rpow_nonneg hxPos.le _)
    _ = (ell : ℝ) ^ (s - b) := by
      rw [← Real.rpow_add hxPos]
      congr 1

/-- The concrete polynomial/logarithmic budget in equation (15) is
summable. -/
theorem summable_caich_smallEnergy_budget :
    Summable fun ell : ℕ =>
      Real.log (ell : ℝ) ^ (1 / 6 : ℝ) *
        (ell : ℝ) ^ (-3 / 2 : ℝ) := by
  simpa only [neg_div] using!
    (summable_log_rpow_mul_nat_rpow_neg (1 / 6 : ℝ)
      (b := (3 / 2 : ℝ)) (by norm_num))

/-- An exceptional event bounded by a constant multiple of Caich's
small-energy budget is summable. -/
theorem summable_measureReal_of_caich_smallEnergy_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {bad : ℕ → Set Ω} (C : ℝ)
    (hbound : ∀ᶠ ell : ℕ in atTop,
      μ.real (bad ell) ≤ C *
        (Real.log (ell : ℝ) ^ (1 / 6 : ℝ) *
          (ell : ℝ) ^ (-3 / 2 : ℝ))) :
    Summable fun ell => μ.real (bad ell) := by
  apply (summable_caich_smallEnergy_budget.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hbound] with ell hell
  simpa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using! hell

/-- The elementary `T(ell) = ell^10` bookkeeping in equation (29):
`sqrt(T(ell) * ell * log ell) ≤ T(ell)` for every positive natural scale.
-/
theorem caich_qv_prefactor_le {ell : ℕ} (hell : 1 ≤ ell) :
    Real.sqrt
        ((ell : ℝ) ^ 10 * (ell : ℝ) * Real.log (ell : ℝ))
      ≤ (ell : ℝ) ^ 10 := by
  have hxOne : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hxNonneg : (0 : ℝ) ≤ (ell : ℝ) := zero_le_one.trans hxOne
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hlog : Real.log (ell : ℝ) ≤ (ell : ℝ) :=
      Real.log_le_self hxNonneg
    have hxNine : (ell : ℝ) ≤ (ell : ℝ) ^ 9 :=
      le_self_pow₀ hxOne (by norm_num)
    calc
      (ell : ℝ) ^ 10 * (ell : ℝ) * Real.log (ell : ℝ)
          ≤ (ell : ℝ) ^ 10 * (ell : ℝ) * (ell : ℝ) ^ 9 :=
        mul_le_mul_of_nonneg_left (hlog.trans hxNine)
          (mul_nonneg (pow_nonneg hxNonneg _) hxNonneg)
      _ = ((ell : ℝ) ^ 10) ^ 2 := by ring

/-- Eventual-filter form of `caich_qv_prefactor_le`, matching its use after
Borel--Cantelli. -/
theorem eventually_caich_qv_prefactor_le :
    ∀ᶠ ell : ℕ in atTop,
      Real.sqrt
          ((ell : ℝ) ^ 10 * (ell : ℝ) * Real.log (ell : ℝ))
        ≤ (ell : ℝ) ^ 10 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with ell hell
  exact caich_qv_prefactor_le hell

/-- Rewriting the quadratic-variation scale from (29) as the power appearing
in (30). -/
theorem caich_qv_power_identity {ell : ℕ} (hell : 0 < ell) (K : ℝ) :
    (ell : ℝ) ^ 10 / (ell : ℝ) ^ (K / 2) =
      (ell : ℝ) ^ (10 - K / 2) := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_sub (by exact_mod_cast hell) (10 : ℝ) (K / 2)).symm

/-- Real powers of strictly smaller exponent are little-oh of larger real
powers at infinity.  This elementary asymptotic lemma is useful for making
the exponent bookkeeping in (33)--(34) explicit.
-/
theorem isLittleO_rpow_rpow_atTop_of_lt {p q : ℝ} (hpq : p < q) :
    (fun x : ℝ => x ^ p) =o[atTop] fun x : ℝ => x ^ q := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
    exact (Real.rpow_pos_of_pos hx q).ne' hzero |>.elim
  · have hlim := tendsto_rpow_neg_atTop (sub_pos.mpr hpq)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_sub hx]
    congr 1
    ring

/-- If the negative power in a stopped-Hoeffding exponent has strictly larger
degree than both the test-point entropy term and the linear function, then the
resulting error probabilities are summable.

This directly formalizes the comparison behind equation (34):
`exp (C ell^p - c ell^q)` is eventually at most `exp (-ell)` when
`q > max p 1` and `c > 0`.
-/
theorem summable_exp_rpow_sub_rpow
    {C c p q : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hpq : p < q) (hq : 1 < q) :
    Summable fun ell : ℕ =>
      Real.exp (C * (ell : ℝ) ^ p - c * (ell : ℝ) ^ q) := by
  have hCp : (fun x : ℝ => C * x ^ p) =o[atTop] fun x : ℝ => x ^ q :=
    (isLittleO_rpow_rpow_atTop_of_lt hpq).const_mul_left C
  have hOne : (fun x : ℝ => x) =o[atTop] fun x : ℝ => x ^ q := by
    simpa only [Real.rpow_one] using!
      (isLittleO_rpow_rpow_atTop_of_lt hq :
        (fun x : ℝ => x ^ (1 : ℝ)) =o[atTop] fun x : ℝ => x ^ q)
  have hdomReal :
      ∀ᶠ x : ℝ in atTop, C * x ^ p + x ≤ c * x ^ q := by
    have hbound := (hCp.add hOne).bound hc
    filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with x hx hnonneg
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (mul_nonneg hC (Real.rpow_nonneg hnonneg _)) hnonneg),
      abs_of_nonneg (Real.rpow_nonneg hnonneg _)] using! hx
  have hdomNat :
      ∀ᶠ ell : ℕ in atTop,
        C * (ell : ℝ) ^ p + ell ≤ c * (ell : ℝ) ^ q :=
    tendsto_natCast_atTop_atTop.eventually hdomReal
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [hdomNat] with ell hell
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_monotone
  linarith

/-- The numerical gap used in (33): `2 K eta > 10` makes the concentration
power `K + 2 K eta - 10` strictly larger than the test-point entropy power
`K`.
-/
theorem caich_concentration_exponent_gap {K : ℕ} {η : ℝ}
    (hgap : 10 < 2 * (K : ℝ) * η) :
    (K : ℝ) < (K : ℝ) + 2 * (K : ℝ) * η - 10 := by
  linarith

/-- The exact stopped-concentration budget from (34) is summable after Caich's
choice `2 K eta > 10`.  The extra hypothesis `1 ≤ K` is only used to compare
the final exponent with the linear function required by the geometric-series
majorant.
-/
theorem summable_caich_concentration_budget
    {C c η : ℝ} {K : ℕ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : 1 ≤ K) (hgap : 10 < 2 * (K : ℝ) * η) :
    Summable fun ell : ℕ =>
      Real.exp
        (C * (ell : ℝ) ^ (K : ℝ) -
          c * (ell : ℝ) ^ ((K : ℝ) + 2 * (K : ℝ) * η - 10)) := by
  apply summable_exp_rpow_sub_rpow hC hc
    (caich_concentration_exponent_gap hgap)
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  exact hKreal.trans_lt (caich_concentration_exponent_gap hgap)

/-- Named inputs remaining after a per-thin-block `2⁻ell` tail has been
proved.  This is deliberately more granular than the former single
`criticalUpperBound_of_thinBlock` boundary.

`paperBad` packages the already-published decomposition/smoothing,
quadratic-variation auxiliary errors, smooth-number contribution, and
interpolation failures.  `concentrationBad` is separated because its
summability at exponent `1/4 + eta` follows from the stopped-Hoeffding
calculation and the exponent lemma above.
-/
structure CaichPostTailInputs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) where
  /-- Number of thin prime blocks at scale `ell`, for the decomposition chosen
  at exponent `eta`. -/
  J : ℝ → ℕ → ℕ
  /-- The integer `K = K(eta)` in `J(ell) = O(ell^K)`.  Dependence on `eta` is
  essential: no single finite `K` works uniformly for every positive `eta`. -/
  blockDegree : ℝ → ℕ
  blockDegree_pos : ∀ η, 0 < η → 1 ≤ blockDegree η
  /-- Implied constant in the polynomial block count. -/
  blockConstant : ℝ → ℝ
  blockCount_le : ∀ η, 0 < η → ∀ ell,
    (J η ell : ℝ) ≤ blockConstant η * (ell : ℝ) ^ blockDegree η
  /-- Failure of Caich's small Euler-product-energy event. -/
  smallEnergyBad : ℝ → ℕ → Set Ω
  /-- The localized event
  `{U_j > B A_ell} ∩ {I_{j-1} ≤ A_ell}`.  Including the second condition is
  essential: conditional Markov gives a `2⁻ell` bound only on this event. -/
  thinBlockBad : ℝ → ℕ → ℕ → Set Ω
  /-- Implied constant in the published small-energy estimate (15). -/
  smallEnergyConstant : ℝ → ℝ
  /-- Equation (15), expressed with its elementary
  `(log ell)^(1/6) ell^(-3/2)` budget.  Its summability is proved above. -/
  smallEnergy_measure_le : ∀ η, 0 < η →
    ∀ᶠ ell : ℕ in atTop,
      μ.real (smallEnergyBad η ell) ≤ smallEnergyConstant η *
        (Real.log (ell : ℝ) ^ (1 / 6 : ℝ) *
          (ell : ℝ) ^ (-3 / 2 : ℝ))
  /-- The post-moment conditional-Markov tail, integrated over the past. -/
  thinBlock_tail : ∀ η, 0 < η → ∀ ell j, j ∈ Finset.range (J η ell) →
    μ.real (thinBlockBad η ell (j + 1)) ≤ (1 / 2 : ℝ) ^ ell
  /-- All remaining published exceptional events, apart from stopped
  concentration. -/
  paperBad : ℝ → ℕ → Set Ω
  paperBad_summable : ∀ η, 0 < η →
    Summable fun ell => μ.real (paperBad η ell)
  /-- Failure of the stopped-martingale bound at a test point in a scale. -/
  concentrationBad : ℝ → ℕ → Set Ω
  /-- Constant in the `exp(C ell^K)` test-point count. -/
  entropyConstant : ℝ → ℝ
  entropyConstant_nonneg : ∀ η, 0 < η → 0 ≤ entropyConstant η
  /-- Positive constant in the stopped-Hoeffding decay. -/
  decayConstant : ℝ → ℝ
  decayConstant_pos : ∀ η, 0 < η → 0 < decayConstant η
  /-- Caich's choice of `K`, written in the exact form needed in (33). -/
  concentration_gap : ∀ η, 0 < η →
    10 < 2 * (blockDegree η : ℝ) * η
  /-- The stopped-Hoeffding estimate after union over test points, but before
  the now-formal summability comparison. -/
  concentration_measure_le : ∀ η, 0 < η → ∀ ell,
    μ.real (concentrationBad η ell) ≤
      Real.exp
        (entropyConstant η * (ell : ℝ) ^ (blockDegree η : ℝ) -
          decayConstant η *
            (ell : ℝ) ^ ((blockDegree η : ℝ) +
              2 * (blockDegree η : ℝ) * η - 10))
  /-- Sends a natural input to its Caich scale block. -/
  level : ℝ → ℕ → ℕ
  level_tendsto : ∀ η, 0 < η → Tendsto (level η) atTop atTop
  /-- Uniform deterministic constant at a fixed exponent.  Allowing this to
  depend on the sample would only weaken the required paper input. -/
  boundConstant : ℝ → ℝ
  boundConstant_nonneg : ∀ η, 0 < η → 0 ≤ boundConstant η
  /-- Published deterministic implication on simultaneous good events,
  including decomposition and interpolation from test points to every `N`. -/
  bound_of_good : ∀ η, 0 < η → ∀ omega N,
    omega ∉ thinBlockFailure (smallEnergyBad η (level η N))
      (thinBlockBad η (level η N)) (J η (level η N)) →
    omega ∉ paperBad η (level η N) →
    omega ∉ concentrationBad η (level η N) →
    |M omega N| ≤ boundConstant η * criticalScale η N

/-- The complete paper-independent downstream reduction from the named
post-tail Caich inputs to the almost-sure `1/4 + eta` bound.
-/
theorem criticalUpperBound_of_caichPostTailInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {M : Ω → ℕ → ℝ} (h : CaichPostTailInputs μ M) :
    CriticalUpperBound μ M := by
  intro η hη
  have hsmallEnergySummable :
      Summable fun ell => μ.real (h.smallEnergyBad η ell) :=
    summable_measureReal_of_caich_smallEnergy_bound μ (h.smallEnergyConstant η)
      (h.smallEnergy_measure_le η hη)
  have hthin :
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        omega ∉ thinBlockFailure (h.smallEnergyBad η ell)
          (h.thinBlockBad η ell) (h.J η ell) :=
    ae_eventually_thinBlockGood (h.smallEnergyBad η) (h.thinBlockBad η) (h.J η)
      (h.blockConstant η) (h.blockDegree η) (h.blockCount_le η hη)
      hsmallEnergySummable (h.thinBlock_tail η hη)
  have hpaper :
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        omega ∉ h.paperBad η ell :=
    ae_eventually_notMem_of_summable_measureReal (h.paperBad_summable η hη)
  have hconcentrationSummable :
      Summable fun ell => μ.real (h.concentrationBad η ell) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg)
      (h.concentration_measure_le η hη)
      (summable_caich_concentration_budget
        (h.entropyConstant_nonneg η hη) (h.decayConstant_pos η hη)
        (h.blockDegree_pos η hη) (h.concentration_gap η hη))
  have hconcentration :
      ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
        omega ∉ h.concentrationBad η ell :=
    ae_eventually_notMem_of_summable_measureReal hconcentrationSummable
  filter_upwards [hthin, hpaper, hconcentration] with omega
      hthinOmega hpaperOmega hconcentrationOmega
  refine ⟨h.boundConstant η, h.boundConstant_nonneg η hη, ?_⟩
  filter_upwards [(h.level_tendsto η hη).eventually hthinOmega,
      (h.level_tendsto η hη).eventually hpaperOmega,
      (h.level_tendsto η hη).eventually hconcentrationOmega] with N hNthin hNpaper hNconc
  exact h.bound_of_good η hη omega N hNthin hNpaper hNconc

end Problem520
end Erdos

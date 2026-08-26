import ErdosProblems.Erdos520.CaichSmallEnergy
import ErdosProblems.Erdos520.IntegerThinSchedule
import ErdosProblems.Erdos520.SmoothRankinEstimate

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set

namespace Erdos
namespace Problem520

/-!
# The precise Harper input at Caich's initial cutoff

This file records, without adding an axiom, the exact scalar consequence of
Harper's Rademacher low-moment argument that Caich uses.  It also proves the
elementary conversion from that consequence to the `ell ^ (-K/3)` budget.

Harper's paper uses a real parameter `x`, puts

`F₀(s) = ∏_{p ≤ x^(1/e)} (1 + f(p) / p^s)`,

and proves, at `q = 2/3`, uniform moment bounds on every unit interval in the
vertical variable.  Splitting the full integral into those intervals and
using

`|1/2 + it|⁻² ≪ (|N| + 1)⁻²`

gives a convergent series: after Harper's Rademacher translation loss the
power is `(2 - 1/4) * (2/3) = 7/6 > 1`.  Taking `x = y ^ e` makes the prime
cutoff exactly `y`, `log x = e * log y`, and

`log log x = 1 + log log y`.

Thus the published result has precisely the form packaged below.  The
definition is an interface/statement, not a theorem asserted in Lean: a
kernel-level proof still requires formalizing Harper's deep low-moment
argument (including its unit-interval-to-weighted-integral assembly).
-/

/-- The initial energy, written independently of Caich's inert parameters
`ell` and `K`.  At the initial cutoff this is exactly
`caichNormalizedEnergy ell K y y`. -/
noncomputable def harperInitialNormalizedEnergy
    (y : ℕ) (omega : Omega) : ℝ :=
  (2 * Real.pi) * smoothEnergy omega y / Real.log (y : ℝ)

theorem caichNormalizedEnergy_initial_eq_harper
    (ell K y : ℕ) (hy : 1 < y) (omega : Omega) :
    caichNormalizedEnergy ell K y y omega =
      harperInitialNormalizedEnergy y omega := by
  exact caichNormalizedEnergy_initial_eq ell K y hy omega

/-- Exact eventual scalar form of Harper's published Rademacher input after
specializing `q = 2/3`, `k = 0`, setting `x = y ^ e`, and summing the unit
vertical intervals against `|1/2+it|⁻²`.

The constants `C` and `Y` are absolute.  The redundant-looking condition
`2 ≤ y` keeps every logarithm and real power on its intended positive branch.
-/
def HarperRademacherInitialMomentBound (C : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → 2 ≤ y →
    (∫ omega,
        harperInitialNormalizedEnergy y omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      C / (1 + logLogNat y) ^ ((1 : ℝ) / 3)

/-- A proposition spelling out the complete published input, including an
absolute positive constant and a sufficiently-large cutoff.  This is a
definition, not an axiom or an unproved Lean theorem. -/
def HarperRademacherInitialMomentStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Y : ℕ, 2 ≤ Y ∧
    HarperRademacherInitialMomentBound C Y

/-- Caich's initial energy inherits the exact Harper budget, with no
dependence on `ell` or `K` before schedule geometry is used. -/
theorem integral_caichInitialEnergy_twoThird_le_of_harperBound
    {C : ℝ} {Y ell K y : ℕ}
    (hHarper : HarperRademacherInitialMomentBound C Y)
    (hY : Y ≤ y) (hy : 2 ≤ y) :
    (∫ omega,
        caichNormalizedEnergy ell K y y omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      C / (1 + logLogNat y) ^ ((1 : ℝ) / 3) := by
  simpa only [caichNormalizedEnergy_initial_eq_harper ell K y
    (show 1 < y by omega)] using! hHarper y hY hy

/-- Taking a one-third power converts a lower bound for the `log log` scale
into the exact `ell^(K/3)` denominator used by Caich. -/
theorem scaleRpowThird_le_logLogRpowThird
    {ell K : ℕ} {L : ℝ} (hell : 1 ≤ ell)
    (hL : (ell : ℝ) ^ K ≤ L) :
    (ell : ℝ) ^ ((K : ℝ) / 3) ≤ L ^ ((1 : ℝ) / 3) := by
  have hell0 : 0 ≤ (ell : ℝ) := by positivity
  have hpow0 : 0 ≤ (ell : ℝ) ^ K := by positivity
  have hrpow := Real.rpow_le_rpow hpow0 hL (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc
    (ell : ℝ) ^ ((K : ℝ) / 3) =
        ((ell : ℝ) ^ K) ^ ((1 : ℝ) / 3) := by
      rw [show (K : ℝ) / 3 = (K : ℝ) * ((1 : ℝ) / 3) by ring,
        Real.rpow_mul hell0, Real.rpow_natCast]
    _ ≤ L ^ ((1 : ℝ) / 3) := hrpow

/-- The published Harper statement implies exactly the moment hypothesis
consumed by `CaichSmallEnergy` once the initial cutoff has the required
`log log` size. -/
theorem integral_caichInitialEnergy_twoThird_le_caichBudget_of_harperBound
    {C : ℝ} {Y ell K y : ℕ}
    (hC : 0 ≤ C) (hHarper : HarperRademacherInitialMomentBound C Y)
    (hY : Y ≤ y) (hy : 2 ≤ y) (hell : 1 ≤ ell)
    (hscale : (ell : ℝ) ^ K ≤ 1 + logLogNat y) :
    (∫ omega,
        caichNormalizedEnergy ell K y y omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      caichInitialEnergyMomentBudget ell K C := by
  have hscale0 : 0 < (ell : ℝ) ^ ((K : ℝ) / 3) := by positivity
  have hthird := scaleRpowThird_le_logLogRpowThird hell hscale
  have hlogThirdPos : 0 < (1 + logLogNat y) ^ ((1 : ℝ) / 3) := by
    have hbasePos : 0 < 1 + logLogNat y := by
      have hpowPos : 0 < (ell : ℝ) ^ K := by positivity
      exact hpowPos.trans_le hscale
    exact Real.rpow_pos_of_pos hbasePos _
  calc
    (∫ omega,
        caichNormalizedEnergy ell K y y omega ^ ((2 : ℝ) / 3) ∂μ) ≤
        C / (1 + logLogNat y) ^ ((1 : ℝ) / 3) :=
      integral_caichInitialEnergy_twoThird_le_of_harperBound
        hHarper hY hy
    _ ≤ C / (ell : ℝ) ^ ((K : ℝ) / 3) :=
      div_le_div_of_nonneg_left hC hscale0 hthird
    _ = caichInitialEnergyMomentBudget ell K C := by
      rfl

/-! ## The exact integer schedule has more than enough initial scale -/

private theorem one_add_log_log_two_pos :
    0 < 1 + Real.log (Real.log 2) := by
  have hexpLog : Real.exp (-1) < Real.log 2 :=
    Real.exp_neg_one_lt_half.trans
      ((by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
        Real.log_two_gt_d9)
  have hloglog : -1 < Real.log (Real.log 2) :=
    (Real.lt_log_iff_exp_lt (Real.log_pos (by norm_num))).mpr hexpLog
  linarith

/-- For `ell ≥ 2`, the initial endpoint of the exact integer thin schedule
already satisfies the scale inequality needed above.  In fact its `log log`
size is substantially larger than `(ell+1)^K`. -/
theorem integerThinInitial_scale_le_one_add_logLog
    {B K ell : ℕ} (hB : 1 ≤ B) (hell : 2 ≤ ell) :
    (((ell + 1 : ℕ) : ℝ) ^ K) ≤
      1 + logLogNat (integerThinEndpoint B K ell 0) := by
  let L : ℕ := ell + 1
  let J : ℕ := integerThinBlockCount K ell
  let m : ℕ := integerThinExponent B K ell 0
  have hL : 3 ≤ L := by dsimp [L]; omega
  have hJ : J = L ^ K := by rfl
  have hmpos : 0 < m := by
    exact integerThinExponent_pos (K := K) (ell := ell) (j := 0) hB
  have hmform : m = B * L ^ J := by
    dsimp [m, L, J]
    rw [integerThinExponent_eq_of_le (Nat.zero_le _)]
    simp
  have hLm : L ^ J ≤ m := by
    rw [hmform]
    exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt hB)
  have hlogL : (1 : ℝ) ≤ Real.log (L : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (L : ℝ))]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hL)
  have hlogPow : (J : ℝ) ≤ Real.log (L ^ J : ℕ) := by
    rw [show ((L ^ J : ℕ) : ℝ) = (L : ℝ) ^ J by norm_cast,
      Real.log_pow]
    calc
      (J : ℝ) = (J : ℝ) * 1 := by ring
      _ ≤ (J : ℝ) * Real.log (L : ℝ) :=
        mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg J)
  have hlogm : (J : ℝ) ≤ Real.log (m : ℝ) := by
    exact hlogPow.trans (Real.log_le_log (by positivity) (by exact_mod_cast hLm))
  have hloglog := logLogNat_two_pow_eq hmpos
  rw [show integerThinEndpoint B K ell 0 = 2 ^ m by rfl, hloglog]
  have hoffset := one_add_log_log_two_pos
  rw [hJ] at hlogm
  norm_cast at hlogm ⊢
  linarith

/-- Fully elementary schedule specialization: once the absolute Harper
cutoff `Y` is passed, its published moment bound supplies Caich's exact
`(ell+1)^(-K/3)` initial budget on the concrete integer schedule. -/
theorem integral_integerThinInitialEnergy_twoThird_le_of_harperBound
    {C : ℝ} {Y B K ell : ℕ}
    (hC : 0 ≤ C) (hHarper : HarperRademacherInitialMomentBound C Y)
    (hB : 1 ≤ B) (hell : 2 ≤ ell)
    (hY : Y ≤ integerThinEndpoint B K ell 0) :
    (∫ omega,
        caichNormalizedEnergy (ell + 1) K
          (integerThinEndpoint B K ell 0)
          (integerThinEndpoint B K ell 0) omega ^ ((2 : ℝ) / 3) ∂μ) ≤
      caichInitialEnergyMomentBudget (ell + 1) K C := by
  apply integral_caichInitialEnergy_twoThird_le_caichBudget_of_harperBound
    hC hHarper hY
  · exact two_le_integerThinEndpoint hB
  · omega
  · exact integerThinInitial_scale_le_one_add_logLog hB hell

end Problem520
end Erdos

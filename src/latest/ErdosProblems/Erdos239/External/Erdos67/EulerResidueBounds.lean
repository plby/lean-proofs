import ErdosProblems.Erdos239.External.Erdos67.EulerPrincipal
import ErdosProblems.Erdos239.External.Erdos67.EulerQuantitative
import ErdosProblems.Erdos239.External.Erdos67.EulerLower
import ErdosProblems.Erdos239.External.Erdos67.WeightedTransfer

/-!
# Unconditional Euler bounds at Tao's exponent

This module packages the principal and nonprincipal estimates in exactly the
uniform-over-divisors form used by `WeightedTransfer`.
-/

open Filter Asymptotics

namespace Erdos67.EulerResidueBounds

noncomputable section

open EulerResidue EulerQuantitative EulerLower

def principalErrorAt (h : ℕ →*₀ ℂ) (X t : ℕ) : ℝ :=
  principalEulerError (singularSeries h X) t X

def nonprincipalErrorAt (B D : ℝ) (X _t : ℕ) : ℝ :=
  nonprincipalEulerError B D X

def factorErrorAt (X d : ℕ) : ℝ :=
  ‖(d : ℂ) ^ (1 - (taoExponent X : ℂ)) - 1‖

def principalFactorErrorAt (X t : ℕ) : ℝ :=
  ‖(t.totient : ℂ)⁻¹ * principalEulerFactor t X - (t : ℂ)⁻¹‖

def divisorTransferBudget (h : ℕ →*₀ ℂ) (q k X : ℕ)
    (B D : ℝ) (d : ℕ) : ℝ :=
  ‖residueScale h d (taoExponent X)‖ *
      eulerResidueError (q ^ k / d)
        (principalErrorAt h X (q ^ k / d))
        (nonprincipalErrorAt B D X (q ^ k / d)) +
    ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ * factorErrorAt X d

def totalTransferBudget (h : ℕ →*₀ ℂ) (q k X : ℕ)
    (B D : ℝ) : ℝ :=
  ∑ d ∈ (q ^ k).divisors, divisorTransferBudget h q k X B D d

theorem totalTransferBudget_nonneg (h : ℕ →*₀ ℂ) (q k X : ℕ)
    {B D : ℝ} (hB : 0 ≤ B) :
    0 ≤ totalTransferBudget h q k X B D := by
  unfold totalTransferBudget divisorTransferBudget eulerResidueError
    principalErrorAt nonprincipalErrorAt principalEulerError
    nonprincipalEulerError factorErrorAt
  positivity

/-- Fully unconditional principal/nonprincipal package.  The distance bound
`D` is retained in the nonprincipal error rather than hidden in the
structure's type. -/
structure TaoCharacterBoundsWithDistance
    (h : ℕ →*₀ ℂ) (q k X : ℕ) (D : ℝ) where
  B : ℝ
  B_nonneg : 0 ≤ B
  principal : ∀ t, t ∣ q ^ k → t ≠ 0 →
    ‖(t.totient : ℂ)⁻¹ * principalTwistSeries h t (taoExponent X) -
        singularSeries h X / (t : ℂ)‖ ≤
      principalEulerError (singularSeries h X) t X
  nonprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
    NonprincipalTwistsBounded h t (taoExponent X)
      (nonprincipalEulerError B D X)
  factor : ∀ d, d ∣ q ^ k → d ≠ 0 →
    ‖(d : ℂ) ^ (1 - (taoExponent X : ℂ)) - 1‖ ≤ factorErrorAt X d
  budget : ∀ d, d ∣ q ^ k → d ≠ 0 →
    ‖residueScale h d (taoExponent X)‖ *
        eulerResidueError (q ^ k / d)
          (principalErrorAt h X (q ^ k / d))
          (nonprincipalErrorAt B D X (q ^ k / d)) +
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ * factorErrorAt X d ≤
        totalTransferBudget h q k X B D

/-- All Euler estimates, including the positive-main and half-error
conditions, in the exact shape consumed by the normalized weighted transfer
theorem. -/
structure TaoTransferReady
    (h : ℕ →*₀ ℂ) (q k X : ℕ) (D eta : ℝ)
    extends TaoCharacterBoundsWithDistance h q k X D where
  two_le : 2 ≤ X
  eta_nonneg : 0 ≤ eta
  main_pos : 0 <
    ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖
  relative_error :
    totalTransferBudget h q k X B D ≤
      eta * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖

/-- A transfer certificate which retains the quantitative same-scale lower
bound used in its construction.  The parameter `c` is deliberately an
explicit parameter of the structure: the uniform theorem below chooses it
before the scale `X` and before the completely multiplicative function `h`.
This makes the independence of `c` from `h` visible in the theorem type,
while leaving the existing `TaoTransferReady` API unchanged. -/
structure TaoTransferReadyWithLower
    (h : ℕ →*₀ ℂ) (q k X : ℕ) (D eta c : ℝ)
    extends TaoTransferReady h q k X D eta where
  lower_constant_pos : 0 < c
  singular_lower :
    c * Real.log (X : ℝ) ≤ ‖singularSeries h X‖

/-- The retained singular-series lower bound in the normalized form used by
the residue convolution. -/
theorem TaoTransferReadyWithLower.normalized_main_lower
    {q k X : ℕ} [NeZero q] {h : ℕ →*₀ ℂ} {D eta c : ℝ}
    (P : TaoTransferReadyWithLower h q k X D eta c) :
    c * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) ≤
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ := by
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right P.singular_lower (by positivity)

/-- Squared form of `normalized_main_lower`, convenient for the quadratic
energy budget in the final convolution estimate. -/
theorem TaoTransferReadyWithLower.normalized_main_lower_sq
    {q k X : ℕ} [NeZero q] {h : ℕ →*₀ ℂ} {D eta c : ℝ}
    (P : TaoTransferReadyWithLower h q k X D eta c) :
    (c * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) ^ 2 ≤
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ ^ 2 := by
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    (Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le one_lt_two P.two_le))).le
  have hlower0 : 0 ≤
      c * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by
    exact div_nonneg (mul_nonneg P.lower_constant_pos.le hlog) (by positivity)
  exact (sq_le_sq₀ hlower0 (norm_nonneg _)).2 P.normalized_main_lower

theorem TaoTransferReady.squared_error_le
    {q k X : ℕ} {h : ℕ →*₀ ℂ} {D eta : ℝ}
    (P : TaoTransferReady h q k X D eta)
    (H : ℕ) (J : ℝ)
    (hsmall : 4 * (H : ℝ) ^ 2 * eta ^ 2 ≤ J) :
    4 * (H : ℝ) ^ 2 *
        (totalTransferBudget h q k X P.B D) ^ 2 ≤
      J * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ ^ 2 := by
  have hbudget0 : 0 ≤ totalTransferBudget h q k X P.B D :=
    totalTransferBudget_nonneg h q k X P.B_nonneg
  have hmain0 : 0 ≤
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ := norm_nonneg _
  have hetaMain0 : 0 ≤
      eta * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ :=
    mul_nonneg P.eta_nonneg hmain0
  have hsq := (sq_le_sq₀ hbudget0 hetaMain0).2 P.relative_error
  calc
    4 * (H : ℝ) ^ 2 *
        (totalTransferBudget h q k X P.B D) ^ 2 ≤
      4 * (H : ℝ) ^ 2 *
        (eta * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (4 * (H : ℝ) ^ 2 * eta ^ 2) *
        ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ ^ 2 := by ring
    _ ≤ J * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

/-- One-call consumer for the corrected shifted-convolution transfer theorem.
The principal, nonprincipal, Euler-factor, residue-budget, and positive-main
hypotheses are all discharged by `P`; only the genuine aggregate shifted
convolution estimate and its elementary squared-error budget remain. -/
theorem TaoTransferReady.normalized_shiftedResiduePrefixEnergy_le
    {q k X : ℕ} [NeZero q] {h : ℕ →*₀ ℂ}
    {D eta : ℝ} (P : TaoTransferReady h q k X D eta)
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (u : ZMod (q ^ k) → ℂ) (hu : ∀ b, ‖u b‖ ≤ 1)
    (H : ℕ) (hH : 0 < H) (K J : ℝ)
    (hconv :
      ∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h (taoExponent X) u
            (cyclicGoodResidues q k H) L ≤
        K * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ ^ 2 *
          ((q ^ k : ℕ) : ℝ) * H)
    (hsmall : 4 * (H : ℝ) ^ 2 * eta ^ 2 ≤ J) :
    (1 / (((q ^ k : ℕ) : ℝ) * H)) *
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ cyclicGoodResidues q k H,
            Complex.normSq (shiftedResiduePrefix u L a) ≤ 2 * K + 2 * J := by
  apply normalized_medium_cyclicGood_shiftedResiduePrefixEnergy_le
    (sigma := (taoExponent X : ℂ))
    k hh (by
      simpa using one_lt_taoExponent (lt_of_lt_of_le one_lt_two P.two_le))
    (singularSeries h X) (principalErrorAt h X)
    (nonprincipalErrorAt P.B D X) (factorErrorAt X)
    (totalTransferBudget h q k X P.B D) K J hprime
  · exact P.principal
  · exact P.nonprincipal
  · exact P.factor
  · exact P.budget
  · exact hu
  · exact hH
  · exact P.main_pos
  · exact totalTransferBudget_nonneg h q k X P.B_nonneg
  · exact hconv
  · exact P.squared_error_le H J hsmall

theorem exists_taoCharacterBoundsWithDistance
    {q k X : ℕ} (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    {D : ℝ} (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D)
    (hX : 2 ≤ X) :
    Nonempty (TaoCharacterBoundsWithDistance h q k X D) := by
  obtain ⟨B, hB0, hnonprincipal⟩ :=
    exists_uniform_nonprincipalTwistsBounded_divisors q k hq0 hh hD
  refine ⟨⟨B, hB0, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht ht0
    exact norm_normalized_principalTwist_sub_div_le hq0 hh hprime ht ht0
      (lt_of_lt_of_le one_lt_two hX)
  · intro t ht ht0
    exact hnonprincipal t ht ht0 X hX
  · intro d hd hd0
    exact le_rfl
  · intro d hd hd0
    unfold totalTransferBudget
    change divisorTransferBudget h q k X B D d ≤
      ∑ t ∈ (q ^ k).divisors, divisorTransferBudget h q k X B D t
    apply Finset.single_le_sum
    · intro t ht
      unfold divisorTransferBudget eulerResidueError principalErrorAt
        nonprincipalErrorAt factorErrorAt principalEulerError
        nonprincipalEulerError
      positivity
    · exact Nat.mem_divisors.mpr ⟨hd, pow_ne_zero _ hq0⟩

/-- The common nonprincipal error in the package is little-oh of `log X`. -/
theorem uniform_nonprincipalError_isLittleO_log
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D B : ℝ}
    (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D) (hB : 0 ≤ B) :
    (nonprincipalEulerError B D) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) :=
  nonprincipalEulerError_isLittleO_log
    ((pretentiousMass_nonneg hh 0).trans (hD 0)) hB

theorem tendsto_factorErrorAt_zero {d : ℕ} (hd0 : d ≠ 0) :
    Tendsto (factorErrorAt · d) atTop (nhds 0) := by
  have hexponent : Tendsto
      (fun X : ℕ ↦ (1 : ℂ) - (taoExponent X : ℂ)) atTop (nhds 0) := by
    convert tendsto_const_nhds.sub EulerResidue.tendsto_taoExponent.ofReal using 1 <;>
      norm_num
  have hpow := (continuousAt_const_cpow
    (Nat.cast_ne_zero.mpr hd0 : (d : ℂ) ≠ 0)).tendsto.comp hexponent
  have hsub := hpow.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1))
  simpa only [factorErrorAt, Function.comp_apply, Complex.cpow_zero, sub_self,
    norm_zero] using hsub.norm

theorem factorErrorAt_isLittleO_one {d : ℕ} (hd0 : d ≠ 0) :
    (factorErrorAt · d) =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).mpr (tendsto_factorErrorAt_zero hd0)

theorem norm_residueScale_taoExponent_isBigO_one
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {d : ℕ} (hd0 : d ≠ 0) :
    (fun X : ℕ ↦ ‖residueScale h d (taoExponent X)‖) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd0)
  have hu : 0 ≤ taoExponent X :=
    (one_lt_taoExponent (by omega)).le.trans' (by norm_num)
  have hpow : (d : ℝ) ^ (-taoExponent X) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hdOne (neg_nonpos.mpr hu)
  unfold residueScale
  rw [norm_mul, hh hd0, one_mul]
  rw [show -(taoExponent X : ℂ) = ((-taoExponent X : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.norm_cpow_real, Complex.norm_natCast]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  simpa only [norm_one, mul_one] using hpow

theorem eulerResidueErrorAt_isLittleO_log
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {D B : ℝ}
    (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D) (hB : 0 ≤ B)
    {t : ℕ} (ht0 : t ≠ 0) :
    (fun X : ℕ ↦ eulerResidueError t (principalErrorAt h X t)
      (nonprincipalErrorAt B D X t)) =o[atTop]
        (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  have hp : (principalErrorAt h · t) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [principalErrorAt] using principalEulerError_isLittleO_log hh ht0
  have hn : (nonprincipalErrorAt B D · t) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [nonprincipalErrorAt] using
      nonprincipalEulerError_isLittleO_log
        ((pretentiousMass_nonneg hh 0).trans (hD 0)) hB
  have hc := hn.const_mul_left
    (‖((t.totient : ℂ)⁻¹)‖ *
      ((EulerResidue.nonprincipalCharacters t).card : ℝ))
  simpa only [eulerResidueError, principalErrorAt, nonprincipalErrorAt,
    mul_assoc] using hp.add hc

theorem divisorTransferBudget_isLittleO_log
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {q k d : ℕ} (hq0 : q ≠ 0) (hd : d ∣ q ^ k) (hd0 : d ≠ 0)
    {D B : ℝ} (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D)
    (hB : 0 ≤ B) :
    (divisorTransferBudget h q k · B D d) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  have hqk0 : q ^ k ≠ 0 := pow_ne_zero _ hq0
  have ht0 : q ^ k / d ≠ 0 := by
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hqk0) hd)
      (Nat.pos_of_ne_zero hd0)).ne'
  have hscale := norm_residueScale_taoExponent_isBigO_one hh hd0
  have herr := eulerResidueErrorAt_isLittleO_log hh hD hB ht0
  have hfirst := hscale.mul_isLittleO herr
  have hs : (fun X : ℕ ↦ ‖singularSeries h X‖) =O[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := norm_singularSeries_isBigO_log hh
  have hqnorm : (fun X : ℕ ↦
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖) =O[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [norm_div, div_eq_mul_inv, norm_mul, norm_inv, mul_comm] using
      hs.const_mul_left ‖((q ^ k : ℕ) : ℂ)‖⁻¹
  have hfactor := factorErrorAt_isLittleO_one hd0
  have hsecond := hqnorm.mul_isLittleO hfactor
  have hfirst' : (fun X : ℕ ↦
      ‖residueScale h d (taoExponent X)‖ *
        eulerResidueError (q ^ k / d)
          (principalErrorAt h X (q ^ k / d))
          (nonprincipalErrorAt B D X (q ^ k / d))) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [one_mul] using hfirst
  have hsecond' : (fun X : ℕ ↦
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ * factorErrorAt X d) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [mul_one] using hsecond
  simpa only [divisorTransferBudget] using hfirst'.add hsecond'

theorem totalTransferBudget_isLittleO_log
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {q k : ℕ} (hq0 : q ≠ 0)
    {D B : ℝ} (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D)
    (hB : 0 ≤ B) :
    (totalTransferBudget h q k · B D) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  have hsum : (∑ d ∈ (q ^ k).divisors,
      fun X : ℕ ↦ divisorTransferBudget h q k X B D d) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    apply Asymptotics.IsLittleO.sum
    intro d hdmem
    have hd := Nat.dvd_of_mem_divisors hdmem
    have hd0 : d ≠ 0 := by
      intro hdzero
      subst d
      exact (pow_ne_zero k hq0) (zero_dvd_iff.mp hd)
    exact divisorTransferBudget_isLittleO_log hh hq0 hd hd0 hD hB
  unfold totalTransferBudget
  convert hsum using 1
  ext X
  simp

/-- A positive constant lower bound for the singular series, together with
the unconditional Euler estimates above, gives the complete finite-divisor
package eventually.  The next theorem instantiates the lower bound
unconditionally. -/
theorem eventually_taoTransferReady_of_singular_lower_global
    {q k : ℕ} (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    {D c : ℝ} (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D)
    (hc : 0 < c)
    (hlower : ∀ᶠ X : ℕ in atTop,
      c * Real.log (X : ℝ) ≤ ‖singularSeries h X‖) :
    ∀ᶠ X : ℕ in atTop,
      Nonempty (TaoTransferReady h q k X D (1 / 2)) := by
  obtain ⟨B, hB, hnonprincipal⟩ :=
    exists_uniform_nonprincipalTwistsBounded_divisors q k hq0 hh hD
  have hqkposNat : 0 < q ^ k := pow_pos (Nat.pos_of_ne_zero hq0) _
  have hqkpos : 0 < (((q ^ k : ℕ) : ℝ)) := by exact_mod_cast hqkposNat
  let eps : ℝ := c / (2 * ((q ^ k : ℕ) : ℝ))
  have heps : 0 < eps := by
    dsimp only [eps]
    positivity
  have hsmall :=
    (totalTransferBudget_isLittleO_log (q := q) (k := k) hh hq0 hD hB).bound heps
  filter_upwards [hsmall, hlower, eventually_ge_atTop 2] with X hsmallX hlowerX hX
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hX))
  have hbudget0 : 0 ≤ totalTransferBudget h q k X B D :=
    totalTransferBudget_nonneg h q k X hB
  have hsmallX' : totalTransferBudget h q k X B D ≤
      eps * Real.log (X : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hbudget0,
      abs_of_nonneg hlog.le] using hsmallX
  have hsingularPos : 0 < ‖singularSeries h X‖ :=
    (mul_pos hc hlog).trans_le hlowerX
  have hmain : 0 <
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_natCast]
    exact div_pos hsingularPos hqkpos
  have hhalf : 2 * totalTransferBudget h q k X B D ≤
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_natCast]
    calc
      2 * totalTransferBudget h q k X B D ≤
          2 * (eps * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmallX' (by norm_num)
      _ = c * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by
        dsimp only [eps]
        field_simp
      _ ≤ ‖singularSeries h X‖ / ((q ^ k : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hlowerX hqkpos.le
  refine ⟨{
    B := B
    B_nonneg := hB
    principal := ?_
    nonprincipal := ?_
    factor := ?_
    budget := ?_
    two_le := hX
    eta_nonneg := by norm_num
    main_pos := hmain
    relative_error := by
      nlinarith [hhalf] }⟩
  · intro t ht ht0
    exact norm_normalized_principalTwist_sub_div_le hq0 hh hprime ht ht0
      (lt_of_lt_of_le one_lt_two hX)
  · intro t ht ht0
    exact hnonprincipal t ht ht0 X hX
  · intro d hd hd0
    exact le_rfl
  · intro d hd hd0
    unfold totalTransferBudget
    change divisorTransferBudget h q k X B D d ≤
      ∑ t ∈ (q ^ k).divisors, divisorTransferBudget h q k X B D t
    apply Finset.single_le_sum
    · intro t ht
      unfold divisorTransferBudget eulerResidueError principalErrorAt
        nonprincipalErrorAt factorErrorAt principalEulerError
        nonprincipalEulerError
      positivity
    · exact Nat.mem_divisors.mpr ⟨hd, pow_ne_zero _ hq0⟩

/-- Compatibility form under a global distance bound.  The Section 4
assembly uses the genuinely uniform same-scale theorem below instead. -/
theorem eventually_taoTransferReady_of_global
    {q k : ℕ} (hq0 : q ≠ 0) {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    {D : ℝ} (hD : ∀ Y : ℕ, pretentiousMass h Y ≤ D) :
    ∀ᶠ X : ℕ in atTop,
      Nonempty (TaoTransferReady h q k X D (1 / 2)) := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_pos_eventually_mul_log_le_norm_singularSeries_of_global hh hD
  exact eventually_taoTransferReady_of_singular_lower_global
    hq0 hh hprime hD hc hlower

/-! ## Uniform same-scale transfer package -/

/-- An `h`-independent upper envelope for one divisor contribution. -/
def uniformDivisorTransferBudget (q k X : ℕ)
    (B D : ℝ) (d : ℕ) : ℝ :=
  eulerResidueError (q ^ k / d)
      (2 * Real.log (X : ℝ) * principalFactorErrorAt X (q ^ k / d))
      (nonprincipalErrorAt B D X (q ^ k / d)) +
    2 * Real.log (X : ℝ) * factorErrorAt X d

def uniformTotalTransferBudget (q k X : ℕ) (B D : ℝ) : ℝ :=
  ∑ d ∈ (q ^ k).divisors, uniformDivisorTransferBudget q k X B D d

theorem norm_residueScale_taoExponent_le_one
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {d X : ℕ} (hd0 : d ≠ 0) (hX : 2 ≤ X) :
    ‖residueScale h d (taoExponent X)‖ ≤ 1 := by
  have hdOne : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd0)
  have hu : 0 ≤ taoExponent X :=
    (one_lt_taoExponent (by omega)).le.trans' (by norm_num)
  have hpow : (d : ℝ) ^ (-taoExponent X) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hdOne (neg_nonpos.mpr hu)
  unfold residueScale
  rw [norm_mul, hh hd0, one_mul]
  rw [show -(taoExponent X : ℂ) = ((-taoExponent X : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.norm_cpow_real, Complex.norm_natCast]
  exact hpow

/-- The zeta majorant gives a bound uniform in the later choice of `h`. -/
theorem eventually_norm_singularSeries_le_two_mul_log :
    ∀ᶠ X : ℕ in atTop, ∀ h : ℕ →*₀ ℂ, HasUnitNorm h →
      ‖singularSeries h X‖ ≤ 2 * Real.log (X : ℝ) := by
  have hzeta : ∀ᶠ X : ℕ in atTop,
      (taoExponent X - 1) *
          (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) < 2 :=
    tendsto_taoExponent_mul_realZetaSum.eventually
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hzeta, eventually_ge_atTop 2] with X hzetaX hX
  intro h hh
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hzetaX' :
      (Real.log (X : ℝ))⁻¹ *
          (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) ≤ 2 := by
    have htao : taoExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by
      unfold taoExponent
      ring
    rw [htao] at hzetaX
    exact hzetaX.le
  have hsum :
      (∑' n : ℕ, 1 / (n : ℝ) ^ taoExponent X) ≤
        2 * Real.log (X : ℝ) := by
    rw [inv_mul_eq_div] at hzetaX'
    exact (div_le_iff₀ hlog).mp hzetaX'
  exact (norm_singularSeries_le_realZetaSum hh (by omega)).trans hsum

theorem divisorTransferBudget_le_uniform
    {q k X d : ℕ} (hq0 : q ≠ 0)
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {B D : ℝ} (hB : 0 ≤ B) (hX : 2 ≤ X)
    (hd : d ∣ q ^ k) (hd0 : d ≠ 0)
    (hsingular : ‖singularSeries h X‖ ≤ 2 * Real.log (X : ℝ)) :
    divisorTransferBudget h q k X B D d ≤
      uniformDivisorTransferBudget q k X B D d := by
  have hqk0 : q ^ k ≠ 0 := pow_ne_zero _ hq0
  have ht0 : q ^ k / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hqk0) hd)
      (Nat.pos_of_ne_zero hd0)).ne'
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).le
  have hscale := norm_residueScale_taoExponent_le_one hh hd0 hX
  have hprincipal : principalErrorAt h X (q ^ k / d) ≤
      2 * Real.log (X : ℝ) *
        principalFactorErrorAt X (q ^ k / d) := by
    unfold principalErrorAt principalEulerError principalFactorErrorAt
    exact mul_le_mul_of_nonneg_right hsingular (norm_nonneg _)
  have herr : eulerResidueError (q ^ k / d)
        (principalErrorAt h X (q ^ k / d))
        (nonprincipalErrorAt B D X (q ^ k / d)) ≤
      eulerResidueError (q ^ k / d)
        (2 * Real.log (X : ℝ) *
          principalFactorErrorAt X (q ^ k / d))
        (nonprincipalErrorAt B D X (q ^ k / d)) := by
    unfold eulerResidueError
    exact add_le_add hprincipal le_rfl
  have herr0 : 0 ≤ eulerResidueError (q ^ k / d)
      (principalErrorAt h X (q ^ k / d))
      (nonprincipalErrorAt B D X (q ^ k / d)) := by
    unfold eulerResidueError principalErrorAt nonprincipalErrorAt
      principalEulerError nonprincipalEulerError
    positivity
  have hfirst :
      ‖residueScale h d (taoExponent X)‖ *
          eulerResidueError (q ^ k / d)
            (principalErrorAt h X (q ^ k / d))
            (nonprincipalErrorAt B D X (q ^ k / d)) ≤
        eulerResidueError (q ^ k / d)
          (2 * Real.log (X : ℝ) *
            principalFactorErrorAt X (q ^ k / d))
          (nonprincipalErrorAt B D X (q ^ k / d)) :=
    (mul_le_of_le_one_left herr0 hscale).trans herr
  have hdivNorm :
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ ≤
        2 * Real.log (X : ℝ) := by
    rw [norm_div]
    have hden : 1 ≤ ‖((q ^ k : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hqk0
    exact (div_le_self (norm_nonneg _) hden).trans hsingular
  unfold divisorTransferBudget uniformDivisorTransferBudget
  exact add_le_add hfirst
    (mul_le_mul_of_nonneg_right hdivNorm (norm_nonneg _))

theorem totalTransferBudget_le_uniform
    {q k X : ℕ} (hq0 : q ≠ 0)
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {B D : ℝ} (hB : 0 ≤ B) (hX : 2 ≤ X)
    (hsingular : ‖singularSeries h X‖ ≤ 2 * Real.log (X : ℝ)) :
    totalTransferBudget h q k X B D ≤
      uniformTotalTransferBudget q k X B D := by
  unfold totalTransferBudget uniformTotalTransferBudget
  apply Finset.sum_le_sum
  intro d hdmem
  have hd := Nat.dvd_of_mem_divisors hdmem
  have hd0 : d ≠ 0 := by
    intro hdzero
    subst d
    exact (pow_ne_zero k hq0) (zero_dvd_iff.mp hd)
  exact divisorTransferBudget_le_uniform hq0 hh hB hX hd hd0 hsingular

theorem uniformDivisorTransferBudget_isLittleO_log
    {q k d : ℕ} (hq0 : q ≠ 0) (hd : d ∣ q ^ k) (hd0 : d ≠ 0)
    {B D : ℝ} (hB : 0 ≤ B) (hD0 : 0 ≤ D) :
    (uniformDivisorTransferBudget q k · B D d) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  have hqk0 : q ^ k ≠ 0 := pow_ne_zero _ hq0
  have ht0 : q ^ k / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hqk0) hd)
      (Nat.pos_of_ne_zero hd0)).ne'
  have hlogO : (fun X : ℕ ↦ 2 * Real.log (X : ℝ)) =O[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    exact (Asymptotics.isBigO_refl (l := atTop) (fun X : ℕ ↦
      Real.log (X : ℝ))).const_mul_left 2
  have hcoeff : (fun X : ℕ ↦
      principalFactorErrorAt X (q ^ k / d)) =o[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (by
      simpa only [principalFactorErrorAt] using
        tendsto_norm_normalized_principalEulerFactor_sub_inv ht0)
  have hp := hlogO.mul_isLittleO hcoeff
  have hp' : (fun X : ℕ ↦
      2 * Real.log (X : ℝ) * principalFactorErrorAt X (q ^ k / d))
      =o[atTop] (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [mul_one] using hp
  have hn : (nonprincipalErrorAt B D · (q ^ k / d)) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [nonprincipalErrorAt] using
      nonprincipalEulerError_isLittleO_log hD0 hB
  have hc := hn.const_mul_left
    (‖((q ^ k / d).totient : ℂ)⁻¹‖ *
      ((EulerResidue.nonprincipalCharacters (q ^ k / d)).card : ℝ))
  have herr : (fun X : ℕ ↦
      eulerResidueError (q ^ k / d)
        (2 * Real.log (X : ℝ) *
          principalFactorErrorAt X (q ^ k / d))
        (nonprincipalErrorAt B D X (q ^ k / d))) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [eulerResidueError, mul_assoc] using hp'.add hc
  have hf := factorErrorAt_isLittleO_one hd0
  have hsecond := hlogO.mul_isLittleO hf
  have hsecond' : (fun X : ℕ ↦
      2 * Real.log (X : ℝ) * factorErrorAt X d) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    simpa only [mul_one] using hsecond
  simpa only [uniformDivisorTransferBudget] using herr.add hsecond'

theorem uniformTotalTransferBudget_isLittleO_log
    {q k : ℕ} (hq0 : q ≠ 0) {B D : ℝ}
    (hB : 0 ≤ B) (hD0 : 0 ≤ D) :
    (uniformTotalTransferBudget q k · B D) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  have hsum : (∑ d ∈ (q ^ k).divisors,
      fun X : ℕ ↦ uniformDivisorTransferBudget q k X B D d) =o[atTop]
      (fun X : ℕ ↦ Real.log (X : ℝ)) := by
    apply Asymptotics.IsLittleO.sum
    intro d hdmem
    have hd := Nat.dvd_of_mem_divisors hdmem
    have hd0 : d ≠ 0 := by
      intro hdzero
      subst d
      exact (pow_ne_zero k hq0) (zero_dvd_iff.mp hd)
    exact uniformDivisorTransferBudget_isLittleO_log
      hq0 hd hd0 hB hD0
  unfold uniformTotalTransferBudget
  convert hsum using 1
  ext X
  simp

/-- Uniform, same-scale, arbitrarily accurate transfer certificate, retaining
the lower constant which controls the singular-series main term.  Both `c`
and the eventual scale threshold are selected before `h`; the only distance
hypothesis is the mass bound at that same scale `X`. -/
theorem eventually_taoTransferReadyWithLower
    {q k : ℕ} (hq0 : q ≠ 0) (D eta : ℝ)
    (hD0 : 0 ≤ D) (heta : 0 < eta) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℕ in atTop, ∀ h : ℕ →*₀ ℂ, HasUnitNorm h →
        (∀ p : ℕ, p.Prime → p ∣ q → h p = 1) →
        pretentiousMass h X ≤ D →
          Nonempty (TaoTransferReadyWithLower h q k X D eta c) := by
  obtain ⟨B, hB, hnonprincipal⟩ :=
    exists_uniform_nonprincipalTwistsBounded_divisors_sameScale q k hq0 D
  obtain ⟨c, hc, hlower⟩ :=
    exists_pos_eventually_mul_log_le_norm_singularSeries D
  refine ⟨c, hc, ?_⟩
  have hqkposNat : 0 < q ^ k := pow_pos (Nat.pos_of_ne_zero hq0) _
  have hqkpos : 0 < (((q ^ k : ℕ) : ℝ)) := by exact_mod_cast hqkposNat
  let eps : ℝ := eta * c / ((q ^ k : ℕ) : ℝ)
  have heps : 0 < eps := by
    dsimp only [eps]
    positivity
  have hsmall :=
    (uniformTotalTransferBudget_isLittleO_log
      (q := q) (k := k) hq0 hB hD0).bound heps
  filter_upwards [hsmall, hlower, eventually_norm_singularSeries_le_two_mul_log,
      eventually_ge_atTop 4] with X hsmallX hlowerX hupperX hX
  intro h hh hprime hmass
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have huniform0 : 0 ≤ uniformTotalTransferBudget q k X B D := by
    unfold uniformTotalTransferBudget uniformDivisorTransferBudget
      eulerResidueError nonprincipalErrorAt nonprincipalEulerError
      principalFactorErrorAt factorErrorAt
    positivity
  have hsmallX' : uniformTotalTransferBudget q k X B D ≤
      eps * Real.log (X : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg huniform0,
      abs_of_nonneg hlog.le] using hsmallX
  have hlowerH := hlowerX h hh hmass
  have hsingularPos : 0 < ‖singularSeries h X‖ :=
    (mul_pos hc hlog).trans_le hlowerH
  have hmain : 0 <
      ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_natCast]
    exact div_pos hsingularPos hqkpos
  have hactualUniform := totalTransferBudget_le_uniform
    (q := q) (k := k) (X := X) (h := h) (B := B) (D := D)
    hq0 hh hB (by omega : 2 ≤ X) (hupperX h hh)
  have hrelative : totalTransferBudget h q k X B D ≤
      eta * ‖singularSeries h X / ((q ^ k : ℕ) : ℂ)‖ := by
    rw [norm_div, Complex.norm_natCast]
    calc
      totalTransferBudget h q k X B D ≤
          uniformTotalTransferBudget q k X B D := hactualUniform
      _ ≤ eps * Real.log (X : ℝ) := hsmallX'
      _ = eta * (c * Real.log (X : ℝ) /
          ((q ^ k : ℕ) : ℝ)) := by
        dsimp only [eps]
        field_simp
      _ ≤ eta * (‖singularSeries h X‖ /
          ((q ^ k : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hlowerH hqkpos.le) heta.le
  refine ⟨{
    B := B
    B_nonneg := hB
    principal := ?_
    nonprincipal := ?_
    factor := ?_
    budget := ?_
    two_le := by omega
    eta_nonneg := heta.le
    main_pos := hmain
    relative_error := hrelative
    lower_constant_pos := hc
    singular_lower := hlowerH }⟩
  · intro t ht ht0
    exact norm_normalized_principalTwist_sub_div_le hq0 hh hprime ht ht0
      (by omega)
  · intro t ht ht0
    exact hnonprincipal t ht ht0 X hX h hh hmass
  · intro d hd hd0
    exact le_rfl
  · intro d hd hd0
    unfold totalTransferBudget
    change divisorTransferBudget h q k X B D d ≤
      ∑ t ∈ (q ^ k).divisors, divisorTransferBudget h q k X B D t
    apply Finset.single_le_sum
    · intro t ht
      unfold divisorTransferBudget eulerResidueError principalErrorAt
        nonprincipalErrorAt factorErrorAt principalEulerError
        nonprincipalEulerError
      positivity
    · exact Nat.mem_divisors.mpr ⟨hd, pow_ne_zero _ hq0⟩

/-- Compatibility projection of the quantitative same-scale package. -/
theorem eventually_taoTransferReady
    {q k : ℕ} (hq0 : q ≠ 0) (D eta : ℝ)
    (hD0 : 0 ≤ D) (heta : 0 < eta) :
    ∀ᶠ X : ℕ in atTop, ∀ h : ℕ →*₀ ℂ, HasUnitNorm h →
      (∀ p : ℕ, p.Prime → p ∣ q → h p = 1) →
      pretentiousMass h X ≤ D →
        Nonempty (TaoTransferReady h q k X D eta) := by
  obtain ⟨c, _hc, hready⟩ :=
    eventually_taoTransferReadyWithLower hq0 D eta hD0 heta
  filter_upwards [hready] with X hX
  intro h hh hprime hmass
  obtain ⟨P⟩ := hX h hh hprime hmass
  exact ⟨P.toTaoTransferReady⟩

end

end Erdos67.EulerResidueBounds

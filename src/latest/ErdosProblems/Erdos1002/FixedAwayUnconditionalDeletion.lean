import ErdosProblems.Erdos1002.FixedAwayMinorDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional fixed-away deletion

The long-range Chan--Kumchev estimate used in the manuscript gives an
`O(log N)` bound for the zero Fourier carrier.  The final probability
deletion only needs the weaker statement that this energy is
`o((log N)^2)`.  This module records the corresponding hypothesis-free
assembly interface and then supplies it from the elementary denominator
shells.

All estimates in this file concern the literal finite Fourier
reconstruction used by `normalizedFixedAwayMinorRemainder`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

/-! ## A reconstruction estimate with an arbitrary zero-carrier bound -/

/-- Parseval assembly for the full fixed-away reconstruction when the
zero carrier is bounded by an arbitrary nonnegative quantity `Z`.

Unlike the earlier linear-energy theorem, this statement does not impose
any rate on `Z`; this is the form needed for a merely subquadratic
zero-carrier estimate. -/
theorem norm_sq_fixedAwaySmoothReconstructionL2_le_of_zeroRest
    {t δ T0 Z : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hT0half : T0 ≤ 1 / 2)
    (hN : 4 ≤ N) (hL : 1 ≤ Real.log (N : ℝ))
    (hzero :
      (∑' n : ℕ,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤ Z)
    (hnonzero : ∀ ell : NonzeroFourierIndex,
      (∑' n : ℤ,
        ‖fixedAwayNonzeroFullCarrierCoefficients
          t δ N ell n‖ ^ 2) ≤
        fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
          Real.log (N : ℝ)) :
    ‖fixedAwaySmoothReconstructionL2
        (⟨N, by omega⟩ : ℕ+) N t δ hδ hδt.le‖ ^ 2 ≤
      6 * (
        ‖bernoulliMarkFourierCoefficient 0‖ ^ 2 *
          (fixedAwayShiftedDiagonalUniformConstant T0 δ + Z) +
        windowCarrierMassConstant ^ 2 *
          fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
            Real.log (N : ℝ)) := by
  let Np : ℕ+ := ⟨N, by omega⟩
  let L : ℝ := Real.log (N : ℝ)
  let D : ℝ := fixedAwayNonzeroCarrierLinearEnergyBound T0 δ
  let b : ℂ := bernoulliMarkFourierCoefficient 0
  let Y : UnitCircleL2 :=
    fixedAwayInfiniteNonzeroFullCarrierL2 t δ N hδ hδt
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hδt.le |>.trans htT0
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hD : 0 ≤ D := by
    dsimp [D]
    exact fixedAwayNonzeroCarrierLinearEnergyBound_nonneg hT0nonneg
  have hbound : ∀ ell : NonzeroFourierIndex,
      (∑' n : ℤ,
        ‖fixedAwayNonzeroFullCarrierCoefficients
          t δ N ell n‖ ^ 2) ≤ D * L := by
    intro ell
    simpa only [D, L] using! hnonzero ell
  have hYnorm :=
    norm_fixedAwayInfiniteNonzeroFullCarrierL2_le
      (T0 := T0) N hδ hδt hbound hT0nonneg hLpos.le
  have hYsq :
      ‖Y‖ ^ 2 ≤ windowCarrierMassConstant ^ 2 * D * L := by
    have hsq := pow_le_pow_left₀ (norm_nonneg Y)
      (by simpa only [Y, D, L] using! hYnorm) 2
    calc
      ‖Y‖ ^ 2 ≤
          (windowCarrierMassConstant * Real.sqrt (D * L)) ^ 2 := hsq
      _ = windowCarrierMassConstant ^ 2 * D * L := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hD hLpos.le)]
        ring
  have hsingleInt :
      (∑' n : ℤ,
        ‖fixedAwayShiftedSingletonOne t δ N 0 n‖ ^ 2) ≤
        fixedAwayShiftedDiagonalUniformConstant T0 δ := by
    exact (tsum_fixedAwayShiftedSingletonOne_norm_sq_le
      (N := N) (ell := 0) hδ hδt).trans
        (fixedAwayShiftedDiagonalConstant_le_uniform
          hδ hδt.le htT0)
  have hsingleSummable :=
    summable_fixedAwayShiftedSingletonOne_norm_sq
      (N := N) (ell := 0) hδ hδt
  have hsingleP :
      (∑' n : ℕ+,
        ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2) ≤
        fixedAwayShiftedDiagonalUniformConstant T0 δ :=
    (tsum_pnat_intCast_le_tsum
      (fun n : ℤ ↦ ‖fixedAwayShiftedSingletonOne t δ N 0 n‖ ^ 2)
      hsingleSummable (fun _n ↦ sq_nonneg _)).trans hsingleInt
  have hrestNatSummable :
      Summable fun n : ℕ ↦
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2 :=
    (summable_fixedAwayZeroCarrierRestCoefficients_norm_sq
      N hδ hδt).comp_injective Int.ofNat_injective
  have hrestP :
      (∑' n : ℕ+,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤ Z :=
    (tsum_pnat_comp_le_tsum
      (fun n : ℕ ↦ ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2)
      hrestNatSummable (fun _n ↦ sq_nonneg _)).trans hzero
  have hYFourierSummable :
      Summable fun n : ℤ ↦
        ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 :=
    (hasSum_sq_fourierCoeff Y).summable
  have hYP :
      (∑' n : ℕ+,
        ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2) ≤
        windowCarrierMassConstant ^ 2 * D * L := by
    calc
      (∑' n : ℕ+,
          ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2) ≤
          ∑' n : ℤ,
            ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 :=
        tsum_pnat_intCast_le_tsum
          (fun n : ℤ ↦
            ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2)
          hYFourierSummable (fun _n ↦ sq_nonneg _)
      _ = ‖Y‖ ^ 2 := tsum_sq_fourierCoeff_eq_norm_sq Y
      _ ≤ windowCarrierMassConstant ^ 2 * D * L := hYsq
  have hCnonneg : 0 ≤ D * L := mul_nonneg hD hLpos.le
  have hfullPoint : ∀ n : ℕ+,
      ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2 ≤
        3 * (
          ‖b‖ ^ 2 *
              ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2 +
          ‖b‖ ^ 2 *
              ‖fixedAwayZeroCarrierRestCoefficients
                t δ N (n : ℤ)‖ ^ 2 +
          ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2) := by
    intro n
    rw [fixedAwayFullCarrierCoefficient_pos_eq_zero_add_nonzero
      N (n : ℕ) hδ hδt (htT0.trans hT0half)
      (by omega) n.pos]
    rw [← fourierCoeff_fixedAwayInfiniteNonzeroFullCarrierL2
      N hδ hδt hbound hCnonneg (n : ℤ)]
    rw [fixedAwayFullCarrierBlock_zero_eq_singleton_add_rest
      t δ N (n : ℤ) (by omega)]
    change ‖b * (_ + _) + _‖ ^ 2 ≤ _
    rw [mul_add]
    have hnorm :
        ‖b * fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ) +
          b * fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ) +
          fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ≤
        ‖b * fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ +
          ‖b * fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ)‖ +
          ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    have hthree := sq_add_three_le
      (‖b * fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖)
      (‖b * fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖)
      (‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖)
    simpa only [norm_mul, mul_pow] using! hthree
  have hpnatIntInj : Function.Injective (fun n : ℕ+ ↦ (n : ℤ)) := by
    intro a b hab
    exact Subtype.ext (Int.ofNat_inj.mp hab)
  have hsP :
      Summable fun n : ℕ+ ↦
        ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2 :=
    hsingleSummable.comp_injective hpnatIntInj
  have hrP :
      Summable fun n : ℕ+ ↦
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2 :=
    hrestNatSummable.comp_injective Subtype.val_injective
  have hyP :
      Summable fun n : ℕ+ ↦
        ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 :=
    hYFourierSummable.comp_injective hpnatIntInj
  let f₀ : ℕ+ → ℝ := fun n ↦
    ‖b‖ ^ 2 *
      ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2
  let f₁ : ℕ+ → ℝ := fun n ↦
    ‖b‖ ^ 2 *
      ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2
  let f₂ : ℕ+ → ℝ := fun n ↦
    ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2
  have hf₀ : Summable f₀ := by
    dsimp [f₀]
    exact hsP.mul_left (‖b‖ ^ 2)
  have hf₁ : Summable f₁ := by
    dsimp [f₁]
    exact hrP.mul_left (‖b‖ ^ 2)
  have hf₂ : Summable f₂ := by
    simpa only [f₂] using! hyP
  have hright :
      Summable fun n : ℕ+ ↦ 3 * (f₀ n + f₁ n + f₂ n) :=
    ((hf₀.add hf₁).add hf₂).mul_left 3
  have hfullSummable :
      Summable fun n : ℕ+ ↦
        ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2 := by
    apply hright.of_nonneg_of_le (fun _n ↦ sq_nonneg _)
    intro n
    simpa only [f₀, f₁, f₂] using! hfullPoint n
  have hsum :
      (∑' n : ℕ+,
        ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2) ≤
        3 * (
          ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ +
          ‖b‖ ^ 2 * Z +
          windowCarrierMassConstant ^ 2 * D * L) := by
    calc
      (∑' n : ℕ+,
          ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2) ≤
          ∑' n : ℕ+, 3 * (f₀ n + f₁ n + f₂ n) := by
        apply hfullSummable.tsum_le_tsum _ hright
        intro n
        simpa only [f₀, f₁, f₂] using! hfullPoint n
      _ = 3 * (
          ‖b‖ ^ 2 *
              (∑' n : ℕ+,
                ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2) +
          ‖b‖ ^ 2 *
              (∑' n : ℕ+,
                ‖fixedAwayZeroCarrierRestCoefficients
                  t δ N (n : ℤ)‖ ^ 2) +
          (∑' n : ℕ+,
            ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2)) := by
        rw [tsum_mul_left, (hf₀.add hf₁).tsum_add hf₂,
          hf₀.tsum_add hf₁]
        dsimp [f₀, f₁, f₂]
        rw [tsum_mul_left, tsum_mul_left]
      _ ≤ 3 * (
          ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ +
          ‖b‖ ^ 2 * Z +
          windowCarrierMassConstant ^ 2 * D * L) := by
        gcongr
  change
    ‖fixedAwaySmoothReconstructionL2
      Np (Np : ℕ) t δ hδ hδt.le‖ ^ 2 ≤ _
  rw [norm_fixedAwaySmoothReconstructionL2_sq_eq_positiveCarriers
    hδ hδt (htT0.trans hT0half) Np]
  calc
    2 * (∑' n : ℕ+,
        ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2) ≤
      2 * (3 * (
        ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ +
        ‖b‖ ^ 2 * Z +
        windowCarrierMassConstant ^ 2 * D * L)) := by gcongr
    _ = 6 * (
        ‖b‖ ^ 2 *
          (fixedAwayShiftedDiagonalUniformConstant T0 δ + Z) +
        windowCarrierMassConstant ^ 2 * D * L) := by ring
    _ = 6 * (
        ‖bernoulliMarkFourierCoefficient 0‖ ^ 2 *
          (fixedAwayShiftedDiagonalUniformConstant T0 δ + Z) +
        windowCarrierMassConstant ^ 2 *
          fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
            Real.log (N : ℝ)) := by
      rfl

/-! ## Subquadratic zero energy implies subquadratic reconstruction energy -/

/-- The exact rate needed from the zero carrier.  It is deliberately
quantified uniformly in the smoothing threshold `t` on a fixed compact
interval. -/
def FixedAwayZeroCarrierSubquadraticEnergy : Prop :=
  ∀ {δ T0 : ℝ}, 0 < δ → δ < T0 →
    ∀ eta > 0, ∀ᶠ N : ℕ in atTop, ∀ (t : ℝ),
      δ < t → t ≤ T0 →
        (∑' n : ℕ,
          ‖fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ)‖ ^ 2) ≤
          eta * Real.log (N : ℝ) ^ 2

/-- A subquadratic zero-carrier estimate, together with the already proved
linear estimate for all nonzero carriers, gives a uniform subquadratic
bound for the literal smooth reconstruction. -/
theorem uniform_norm_sq_fixedAwaySmoothReconstructionL2_small_of_zeroRest
    (hzeroSmall : FixedAwayZeroCarrierSubquadraticEnergy)
    {δ T0 : ℝ} (hδ : 0 < δ) (hδT0 : δ < T0)
    (hT0half : T0 ≤ 1 / 2)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (hNpos : 0 < N) (t : ℝ),
      ∀ (hδt : δ < t) (_htT0 : t ≤ T0),
      ‖fixedAwaySmoothReconstructionL2
          (⟨N, hNpos⟩ : ℕ+) N t δ hδ hδt.le‖ ^ 2 ≤
        eta * Real.log (N : ℝ) ^ 2 := by
  let E : ℝ := fixedAwayShiftedDiagonalUniformConstant T0 δ
  let D : ℝ := fixedAwayNonzeroCarrierLinearEnergyBound T0 δ
  let M : ℝ := windowCarrierMassConstant ^ 2
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hδT0.le
  have hE : 0 ≤ E := by
    dsimp [E]
    exact fixedAwayShiftedDiagonalUniformConstant_nonneg hT0nonneg
  have hD : 0 ≤ D := by
    dsimp [D]
    exact fixedAwayNonzeroCarrierLinearEnergyBound_nonneg hT0nonneg
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hb :
      ‖bernoulliMarkFourierCoefficient 0‖ ^ 2 ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg _)
      (norm_bernoulliMarkFourierCoefficient_le_one 0)
  have hzeroEvent :=
    hzeroSmall hδ hδT0 (eta / 18) (by positivity)
  have hnonzeroEvent :=
    eventually_tsum_fixedAwayFullCarrierBlock_nonzero_le_linear
      (T0 := T0) hδ
  have hlogTendsto :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ N : ℕ in atTop,
      max 1 (max (18 * E / eta) (18 * M * D / eta)) ≤
        Real.log (N : ℝ) :=
    hlogTendsto.eventually
      (eventually_ge_atTop
        (max 1 (max (18 * E / eta) (18 * M * D / eta))))
  filter_upwards [
      eventually_ge_atTop 4, hzeroEvent, hnonzeroEvent, hlogLarge] with
      N hN hzeroN hnonzeroN hlogLargeN
  intro hNpos t hδt htT0
  let L : ℝ := Real.log (N : ℝ)
  let Z : ℝ := (eta / 18) * L ^ 2
  have hL : 1 ≤ L := le_trans (le_max_left _ _) hlogLargeN
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hzero :
      (∑' n : ℕ,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤ Z := by
    simpa only [Z, L] using! hzeroN t hδt htT0
  have hnonzero : ∀ ell : NonzeroFourierIndex,
      (∑' n : ℤ,
        ‖fixedAwayNonzeroFullCarrierCoefficients
          t δ N ell n‖ ^ 2) ≤ D * L := by
    intro ell
    simpa only [D, L, fixedAwayNonzeroFullCarrierCoefficients] using!
      hnonzeroN t hδt htT0 (ell : ℤ) ell.property
  have hraw :=
    norm_sq_fixedAwaySmoothReconstructionL2_le_of_zeroRest
      N hδ hδt htT0 hT0half hN hL hzero
        (by simpa only [D, L] using! hnonzero)
  have hElarge : 18 * E / eta ≤ L :=
    (le_max_left _ _).trans (le_max_right _ _)
      |>.trans hlogLargeN
  have hMDlarge : 18 * M * D / eta ≤ L :=
    (le_max_right _ _).trans (le_max_right _ _)
      |>.trans hlogLargeN
  have hEbound : 6 * E ≤ (eta / 3) * L ^ 2 := by
    have hlinear : 6 * E ≤ (eta / 3) * L := by
      have hmul : 18 * E ≤ L * eta :=
        (div_le_iff₀ heta).mp hElarge
      nlinarith
    calc
      6 * E ≤ (eta / 3) * L := hlinear
      _ ≤ (eta / 3) * L ^ 2 := by
        have hcoeff : 0 ≤ eta / 3 := by positivity
        have hLL : L ≤ L ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hLL hcoeff
  have hMDbound : 6 * M * D * L ≤ (eta / 3) * L ^ 2 := by
    have hmul : 18 * M * D ≤ L * eta :=
      (div_le_iff₀ heta).mp hMDlarge
    nlinarith [hLpos.le]
  have hZbound : 6 * Z = (eta / 3) * L ^ 2 := by
    dsimp [Z]
    ring
  have hbE :
      6 * (‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * E) ≤
        (eta / 3) * L ^ 2 := by
    calc
      6 * (‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * E) ≤
          6 * (1 * E) := by gcongr
      _ = 6 * E := by ring
      _ ≤ (eta / 3) * L ^ 2 := hEbound
  have hbZ :
      6 * (‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * Z) ≤
        (eta / 3) * L ^ 2 := by
    have hZnonneg : 0 ≤ Z := by
      dsimp [Z]
      positivity
    calc
      6 * (‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * Z) ≤
          6 * (1 * Z) := by gcongr
      _ = 6 * Z := by ring
      _ = (eta / 3) * L ^ 2 := hZbound
  have hraw' :
      ‖fixedAwaySmoothReconstructionL2
          (⟨N, hNpos⟩ : ℕ+) N t δ hδ hδt.le‖ ^ 2 ≤
        6 * (
          ‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * (E + Z) +
          M * D * L) := by
    simpa only [E, D, M, L, Z] using! hraw
  calc
    ‖fixedAwaySmoothReconstructionL2
        (⟨N, hNpos⟩ : ℕ+) N t δ hδ hδt.le‖ ^ 2 ≤
        6 * (
          ‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * (E + Z) +
          M * D * L) := hraw'
    _ = 6 * (‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * E) +
        6 * (‖bernoulliMarkFourierCoefficient 0‖ ^ 2 * Z) +
        6 * M * D * L := by ring
    _ ≤ (eta / 3) * L ^ 2 +
        (eta / 3) * L ^ 2 +
        (eta / 3) * L ^ 2 := by
      exact add_le_add (add_le_add hbE hbZ) hMDbound
    _ = eta * Real.log (N : ℝ) ^ 2 := by
      dsimp [L]
      ring

/-- Passing from the Fourier reconstruction back to the literal smooth
shot sum preserves the subquadratic estimate. -/
theorem uniform_norm_sq_fixedAwaySmoothShotL2_small_of_zeroRest
    (hzeroSmall : FixedAwayZeroCarrierSubquadraticEnergy)
    {δ T0 : ℝ} (hδ : 0 < δ) (hδT0 : δ < T0)
    (hT0half : T0 ≤ 1 / 2)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (_hNpos : 0 < N) (t : ℝ),
      ∀ (hδt : δ < t) (_htT0 : t ≤ T0),
      ‖fixedAwaySmoothShotL2 t δ N N hδ hδt.le‖ ^ 2 ≤
        eta * Real.log (N : ℝ) ^ 2 := by
  have hrecon :=
    uniform_norm_sq_fixedAwaySmoothReconstructionL2_small_of_zeroRest
      hzeroSmall hδ hδT0 hT0half
        (eta := eta / 4) (by positivity)
  obtain ⟨N₀, herror⟩ :=
    uniform_norm_naturalCutoffShotErrorL2_sq_small
      (show 0 < eta / 4 by positivity)
  filter_upwards [hrecon, eventually_ge_atTop N₀] with
      N hreconN hN₀
  intro hNpos t hδt htT0
  let Np : ℕ+ := ⟨N, hNpos⟩
  let R : UnitCircleL2 :=
    fixedAwaySmoothReconstructionL2 Np N t δ hδ hδt.le
  let E : UnitCircleL2 := naturalCutoffShotErrorL2 Np
  have hreconSq :
      ‖R‖ ^ 2 ≤ (eta / 4) * Real.log (N : ℝ) ^ 2 := by
    simpa only [R, Np] using!
      hreconN hNpos t hδt htT0
  have herrorSq :
      ‖E‖ ^ 2 ≤ (eta / 4) * Real.log (N : ℝ) ^ 2 := by
    simpa only [E, Np] using! herror Np hN₀
  have hwindow := fixedAwaySmooth_windowError_identity
    Np N hδ hδt.le
  have herrId :
      primitiveShotSumL2 (Np : ℕ) N -
          naturalCutoffReconstructionL2 Np N = -E := by
    change primitiveShotSumL2 (Np : ℕ) (Np : ℕ) -
      naturalCutoffReconstructionL2 Np (Np : ℕ) = -E
    dsimp [E, naturalCutoffShotErrorL2, reconstructedShotL2]
    abel
  rw [herrId] at hwindow
  have hshot :
      fixedAwaySmoothShotL2 t δ N N hδ hδt.le = R - E := by
    change fixedAwaySmoothShotL2 t δ (Np : ℕ) N hδ hδt.le = R - E
    calc
      fixedAwaySmoothShotL2 t δ (Np : ℕ) N hδ hδt.le =
          (fixedAwaySmoothShotL2 t δ (Np : ℕ) N hδ hδt.le - R) + R := by
        abel
      _ = -E + R := by rw [hwindow]
      _ = R - E := by abel
  rw [hshot]
  have hnorm := norm_sub_le R E
  have hsq :
      ‖R - E‖ ^ 2 ≤ 2 * (‖R‖ ^ 2 + ‖E‖ ^ 2) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    nlinarith [sq_nonneg (‖R‖ - ‖E‖)]
  calc
    ‖R - E‖ ^ 2 ≤ 2 * (‖R‖ ^ 2 + ‖E‖ ^ 2) := hsq
    _ ≤ 2 * ((eta / 4) * Real.log (N : ℝ) ^ 2 +
        (eta / 4) * Real.log (N : ℝ) ^ 2) := by gcongr
    _ = eta * Real.log (N : ℝ) ^ 2 := by ring

/-- Uniform `L²` convergence of the normalized fixed-away smooth sum,
assuming only subquadratic zero-carrier energy. -/
theorem uniform_eLpNorm_fixedAwaySmoothShotSum_div_small_of_zeroRest
    (hzeroSmall : FixedAwayZeroCarrierSubquadraticEnergy)
    {δ T0 : ℝ} (hδ : 0 < δ) (hδT0 : δ < T0)
    (hT0half : T0 ≤ 1 / 2) :
    ∀ eta > 0, ∀ᶠ N : ℕ in atTop, ∀ (_hNpos : 0 < N) (t : ℝ),
      ∀ (_hδt : δ < t) (_htT0 : t ≤ T0),
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum t δ N N alpha /
              Real.log (N : ℝ))
          2 uniform01Measure ≤ ENNReal.ofReal eta := by
  intro eta heta
  have hsquare :=
    uniform_norm_sq_fixedAwaySmoothShotL2_small_of_zeroRest
      hzeroSmall hδ hδT0 hT0half (eta := eta ^ 2)
        (sq_pos_of_pos heta)
  have hlogTendsto :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogPos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) :=
    hlogTendsto.eventually (eventually_gt_atTop 0)
  filter_upwards [hsquare, hlogPos] with N hsquareN hlogN
  intro hNpos t hδt htT0
  rw [eLpNorm_fixedAwaySmoothShotSum_div_eq_ofReal
    N N (Real.log (N : ℝ)) hδ hδt.le hlogN]
  apply ENNReal.ofReal_le_ofReal
  have hsquare' :
      ‖fixedAwaySmoothShotL2 t δ N N hδ hδt.le‖ ^ 2 ≤
        (eta * Real.log (N : ℝ)) ^ 2 := by
    simpa only [mul_pow] using!
      hsquareN hNpos t hδt htT0
  have hnorm :
      ‖fixedAwaySmoothShotL2 t δ N N hδ hδt.le‖ ≤
        eta * Real.log (N : ℝ) := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg heta.le hlogN.le)).mp hsquare'
  exact (div_le_iff₀ hlogN).2 hnorm

/-- The endpoint discrepancy is already `o(1)` in normalized `L²`; hence
the smooth estimate above gives the complete fixed-away minor remainder. -/
theorem iterated_eLpNorm_normalizedFixedAwayMinorRemainder_small_of_zeroRest
    (hzeroSmall : FixedAwayZeroCarrierSubquadraticEnergy)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ eta > 0, ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      eLpNorm
          (normalizedFixedAwayMinorRemainder N (A : ℝ) ε)
          2 uniform01Measure ≤ ENNReal.ofReal eta := by
  intro eta heta
  have hsmooth :=
    uniform_eLpNorm_fixedAwaySmoothShotSum_div_small_of_zeroRest
      hzeroSmall (δ := ε / 2) (T0 := ε)
        (by positivity) (by linarith) hεhalf.le
        (eta / 2) (by positivity)
  have hendpoint :=
    eventually_eLpNorm_fixedAwayMinorEndpointDiscrepancy_div_log_small
      ε hε (eta / 2) (by positivity)
  filter_upwards [eventually_ge_atTop 1] with A hA
  have hadmissible :=
    eventually_minorComponentSplit_admissible (A : ℝ) ε hε
  filter_upwards [hsmooth, hendpoint, hadmissible] with
      N hsmoothN hendpointN hadmissibleN
  rcases hadmissibleN with ⟨hN, hL, hquarter⟩
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hroom : (A : ℝ) / Real.log (N : ℝ) ≤ ε / 4 :=
    (div_le_iff₀ hL).2 (by simpa only [mul_comm] using! hquarter.le)
  have hNpos : 0 < N := by omega
  have hhalf : ε / 2 < ε := by linarith
  have hsmoothN' :
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ))
          2 uniform01Measure ≤ ENNReal.ofReal (eta / 2) :=
    hsmoothN hNpos ε hhalf le_rfl
  have hfun :
      normalizedFixedAwayMinorRemainder N (A : ℝ) ε =
        (fun alpha ↦
          fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ) +
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ)) := by
    funext alpha
    exact
      normalizedFixedAwayMinorRemainder_eq_smooth_add_endpoints
        N (A : ℝ) ε alpha hN hApos hL hε hroom
  rw [hfun]
  have hf : AEStronglyMeasurable
      (fun alpha ↦
        fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
          Real.log (N : ℝ))
      uniform01Measure :=
    ((measurable_fixedAwaySmoothShotSum ε (ε / 2) N N).div_const
      (Real.log (N : ℝ) : ℂ)).aestronglyMeasurable
  have hg : AEStronglyMeasurable
      (fun alpha ↦
        fixedAwayMinorEndpointDiscrepancy N ε alpha /
          Real.log (N : ℝ))
      uniform01Measure :=
    ((measurable_fixedAwayMinorEndpointDiscrepancy N ε).div_const
      (Real.log (N : ℝ) : ℂ)).aestronglyMeasurable
  have hadd :
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
                Real.log (N : ℝ) +
              fixedAwayMinorEndpointDiscrepancy N ε alpha /
                Real.log (N : ℝ))
          2 uniform01Measure ≤
        eLpNorm
            (fun alpha ↦
              fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
                Real.log (N : ℝ))
            2 uniform01Measure +
          eLpNorm
            (fun alpha ↦
              fixedAwayMinorEndpointDiscrepancy N ε alpha /
                Real.log (N : ℝ))
            2 uniform01Measure := by
    simpa only [Pi.add_apply] using!
      eLpNorm_add_le hf hg (by norm_num : (1 : ENNReal) ≤ 2)
  calc
    eLpNorm
        (fun alpha ↦
          fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ) +
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ))
        2 uniform01Measure ≤
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ))
          2 uniform01Measure +
        eLpNorm
          (fun alpha ↦
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ))
          2 uniform01Measure := hadd
    _ ≤ ENNReal.ofReal (eta / 2) + ENNReal.ofReal (eta / 2) :=
      add_le_add hsmoothN' hendpointN
    _ = ENNReal.ofReal eta := by
      rw [← ENNReal.ofReal_add
        (by positivity : 0 ≤ eta / 2)
        (by positivity : 0 ≤ eta / 2)]
      congr 1
      ring

/-- Probability deletion of the literal fixed-away minor remainder from
subquadratic zero-carrier energy. -/
theorem iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder_of_zeroRest
    (hzeroSmall : FixedAwayZeroCarrierSubquadraticEnergy)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedFixedAwayMinorRemainder
              N (A : ℝ) ε alpha‖} < δ := by
  apply iterated_probabilityDeletion_of_iterated_eLpNorm_two
    (μ := uniform01Measure)
    (fun A N ↦ normalizedFixedAwayMinorRemainder N (A : ℝ) ε)
  · exact
      iterated_eventually_aestronglyMeasurable_fixedAwayMinorRemainder
        ε hε
  · exact
      iterated_eLpNorm_normalizedFixedAwayMinorRemainder_small_of_zeroRest
        hzeroSmall ε hε hεhalf

end

end Erdos1002

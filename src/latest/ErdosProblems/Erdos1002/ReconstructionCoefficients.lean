import ErdosProblems.Erdos1002.FourierSeries
import ErdosProblems.Erdos1002.MobiusCollapse
import Mathlib.Dynamics.Ergodic.AddCircle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fourier coefficients in the exact Fourier--Ramanujan reconstruction

This file connects the arithmetic Möbius collapse to the Fourier Hilbert
basis on the unit circle.  In particular, it records explicitly how a
positive integral dilation moves a Fourier mode and packages the coefficient
appearing in the full-denominator periodized kernel.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

/-- The ambient normalized Haar `L²` space on the unit circle. -/
abbrev UnitCircleL2 :=
  Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance)

/-- Multiplication by a positive integer on the unit additive circle. -/
def positiveCircleDilation (p : ℕ+) (x : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  (p : ℤ) • x

theorem positiveCircleDilation_measurePreserving (p : ℕ+) :
    MeasurePreserving (positiveCircleDilation p)
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance)
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast p.ne_zero
  simpa [positiveCircleDilation] using!
    (Measure.measurePreserving_zsmul
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) hp)

/-- Pullback of an `L²` function by positive integral dilation. -/
def positiveDilationL2 (p : ℕ+) : UnitCircleL2 →ₗᵢ[ℂ] UnitCircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (positiveCircleDilation p)
    (positiveCircleDilation_measurePreserving p)

theorem fourier_positiveCircleDilation (p : ℕ+) (m : ℤ)
    (x : AddCircle (1 : ℝ)) :
    fourier m (positiveCircleDilation p x) = fourier (m * (p : ℤ)) x := by
  simp only [fourier_apply, positiveCircleDilation, smul_smul]

/-- Dilation moves the `m`-th Fourier basis vector to the `(m*p)`-th one. -/
theorem positiveDilationL2_fourierLp (p : ℕ+) (m : ℤ) :
    positiveDilationL2 p (fourierLp 2 m) = fourierLp 2 (m * (p : ℤ)) := by
  change Lp.compMeasurePreserving (positiveCircleDilation p)
      (positiveCircleDilation_measurePreserving p) (fourierLp 2 m) = _
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_compMeasurePreserving (fourierLp 2 m)
      (positiveCircleDilation_measurePreserving p),
      (positiveCircleDilation_measurePreserving p).quasiMeasurePreserving.ae
        (coeFn_fourierLp 2 m),
      coeFn_fourierLp 2 (m * (p : ℤ))] with x hcomp hm hmp
  rw [hcomp, Function.comp_apply, hm, hmp, fourier_positiveCircleDilation]

/-- The continuous linear functional extracting the `n`-th Fourier
coefficient of an `L²` class. -/
def fourierCoefficientCLM (n : ℤ) : UnitCircleL2 →L[ℂ] ℂ :=
  innerSL ℂ (fourierLp 2 n)

@[simp]
theorem fourierCoefficientCLM_apply (f : UnitCircleL2) (n : ℤ) :
    fourierCoefficientCLM n f = fourierCoeff (f : AddCircle (1 : ℝ) → ℂ) n := by
  simpa [fourierCoefficientCLM, innerSL_apply_apply, ← coe_fourierBasis,
    HilbertBasis.repr_apply_apply] using! fourierBasis_repr f n

theorem fourierCoeff_fourierLp (m n : ℤ) :
    fourierCoeff (fourierLp 2 m : AddCircle (1 : ℝ) → ℂ) n =
      if n = m then 1 else 0 := by
  rw [← fourierCoefficientCLM_apply]
  by_cases hnm : n = m
  · subst n
    simp [fourierCoefficientCLM, innerSL_apply_apply,
      orthonormal_fourier.1]
  · simp only [fourierCoefficientCLM, innerSL_apply_apply, if_neg hnm]
    exact orthonormal_fourier.2 hnm

/-- The exact `L²` Fourier expansion of a positively dilated sawtooth. -/
theorem hasSum_positiveDilation_sawtooth (p : ℕ+) :
    HasSum
      (fun m : NonzeroFourierIndex ↦
        (1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) •
          fourierLp 2 ((m : ℤ) * (p : ℤ)))
      (positiveDilationL2 p sawtoothL2) := by
  have hmap := (positiveDilationL2 p).toContinuousLinearMap.hasSum
    hasSum_sawtoothNonzeroFourierSeries
  have hdilate (m : ℤ) :
      (positiveDilationL2 p).toContinuousLinearMap (fourierLp 2 m) =
        fourierLp 2 (m * (p : ℤ)) :=
    positiveDilationL2_fourierLp p m
  simpa only [map_smul, positiveDilationL2_fourierLp,
    sawtoothNonzeroFourierTerm, hdilate] using! hmap

/-- At a positive frequency divisible by `p`, dilation contributes the
expected rescaled sawtooth coefficient. -/
theorem fourierCoeff_positiveDilation_sawtooth_of_dvd
    (p : ℕ+) (n : ℕ) (hn : n ≠ 0) (hpn : (p : ℕ) ∣ n) :
    fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      (p : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  let q : ℕ := n / (p : ℕ)
  have hp_le_n : (p : ℕ) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn
  have hqpos : 0 < q := Nat.div_pos hp_le_n p.pos
  let m₀ : NonzeroFourierIndex :=
    ⟨(q : ℤ), by exact_mod_cast (Nat.ne_of_gt hqpos)⟩
  have hprodNat : q * (p : ℕ) = n := by
    simpa [q, mul_comm] using! Nat.mul_div_cancel' hpn
  have hmode : (n : ℤ) = (m₀ : ℤ) * (p : ℤ) := by
    change (n : ℤ) = (q : ℤ) * (p : ℤ)
    exact_mod_cast hprodNat.symm
  let g : NonzeroFourierIndex → ℂ := fun m ↦
    (1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) *
      if (n : ℤ) = (m : ℤ) * (p : ℤ) then 1 else 0
  have hmapped := (fourierCoefficientCLM (n : ℤ)).hasSum
    (hasSum_positiveDilation_sawtooth p)
  have hseries : HasSum g
      (fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) (n : ℤ)) := by
    simpa only [g, map_smul, smul_eq_mul, fourierCoefficientCLM_apply,
      fourierCoeff_fourierLp] using! hmapped
  have hzero : ∀ m : NonzeroFourierIndex, m ≠ m₀ → g m = 0 := by
    intro m hm
    have hne : (n : ℤ) ≠ (m : ℤ) * (p : ℤ) := by
      intro heq
      have heq' : (m : ℤ) * (p : ℤ) = (m₀ : ℤ) * (p : ℤ) :=
        heq.symm.trans hmode
      have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast p.ne_zero
      apply hm
      exact Subtype.ext (mul_right_cancel₀ hpZ heq')
    simp [g, hne]
  have hsingle : HasSum g (g m₀) := hasSum_single m₀ hzero
  have heq := hseries.unique hsingle
  rw [heq]
  simp only [g, hmode, if_pos, mul_one]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hnC : (n : ℂ) = (q : ℂ) * (p : ℂ) := by exact_mod_cast hprodNat.symm
  change 1 / (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ)) = _
  rw [hnC]
  field_simp [hpC, hqC, Real.pi_ne_zero, Complex.I_ne_zero]

/-- At a positive frequency not divisible by `p`, the dilated sawtooth has
zero Fourier coefficient. -/
theorem fourierCoeff_positiveDilation_sawtooth_of_not_dvd
    (p : ℕ+) (n : ℕ) (hpn : ¬(p : ℕ) ∣ n) :
    fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      0 := by
  let g : NonzeroFourierIndex → ℂ := fun m ↦
    (1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) *
      if (n : ℤ) = (m : ℤ) * (p : ℤ) then 1 else 0
  have hmapped := (fourierCoefficientCLM (n : ℤ)).hasSum
    (hasSum_positiveDilation_sawtooth p)
  have hseries : HasSum g
      (fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) (n : ℤ)) := by
    simpa only [g, map_smul, smul_eq_mul, fourierCoefficientCLM_apply,
      fourierCoeff_fourierLp] using! hmapped
  have hzero (m : NonzeroFourierIndex) : g m = 0 := by
    have hne : (n : ℤ) ≠ (m : ℤ) * (p : ℤ) := by
      intro heq
      have hdvdZ : (p : ℤ) ∣ (n : ℤ) := by
        refine ⟨(m : ℤ), ?_⟩
        simpa [mul_comm] using! heq
      exact hpn (Int.natCast_dvd_natCast.mp hdvdZ)
    simp [g, hne]
  have hsumzero : HasSum g 0 := by
    exact (hasSum_zero :
      HasSum (fun _ : NonzeroFourierIndex ↦ (0 : ℂ)) 0).congr_fun hzero
  exact hseries.unique hsumzero

/-- Complete positive-frequency coefficient formula for one dilated
sawtooth. -/
theorem fourierCoeff_positiveDilation_sawtooth
    (p : ℕ+) (n : ℕ) (hn : n ≠ 0) :
    fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      if (p : ℕ) ∣ n then
        (p : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
      else 0 := by
  by_cases hpn : (p : ℕ) ∣ n
  · rw [if_pos hpn]
    exact fourierCoeff_positiveDilation_sawtooth_of_dvd p n hn hpn
  · rw [if_neg hpn]
    exact fourierCoeff_positiveDilation_sawtooth_of_not_dvd p n hpn

/-- Integer-frequency version of the dilation formula.  This includes both
signs and will be used to verify all Fourier modes of the reconstructed
`L²` class. -/
theorem fourierCoeff_positiveDilation_sawtooth_int
    (p : ℕ+) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) n =
      if (p : ℤ) ∣ n then
        (p : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
      else 0 := by
  let g : NonzeroFourierIndex → ℂ := fun m ↦
    (1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) *
      if n = (m : ℤ) * (p : ℤ) then 1 else 0
  have hmapped := (fourierCoefficientCLM n).hasSum
    (hasSum_positiveDilation_sawtooth p)
  have hseries : HasSum g
      (fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) n) := by
    simpa only [g, map_smul, smul_eq_mul, fourierCoefficientCLM_apply,
      fourierCoeff_fourierLp] using! hmapped
  by_cases hpn : (p : ℤ) ∣ n
  · rw [if_pos hpn]
    let q : ℤ := n / (p : ℤ)
    have hprod : q * (p : ℤ) = n := by
      simpa [q] using! Int.ediv_mul_cancel hpn
    have hqne : q ≠ 0 := by
      intro hq
      apply hn
      rw [← hprod, hq, zero_mul]
    let m₀ : NonzeroFourierIndex := ⟨q, hqne⟩
    have hmode : n = (m₀ : ℤ) * (p : ℤ) := by
      change n = q * (p : ℤ)
      exact hprod.symm
    have hzero : ∀ m : NonzeroFourierIndex, m ≠ m₀ → g m = 0 := by
      intro m hm
      have hne : n ≠ (m : ℤ) * (p : ℤ) := by
        intro heq
        have heq' : (m : ℤ) * (p : ℤ) = (m₀ : ℤ) * (p : ℤ) :=
          heq.symm.trans hmode
        have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast p.ne_zero
        apply hm
        exact Subtype.ext (mul_right_cancel₀ hpZ heq')
      simp [g, hne]
    have hsingle : HasSum g (g m₀) := hasSum_single m₀ hzero
    have heq := hseries.unique hsingle
    rw [heq]
    simp only [g, if_pos hmode, mul_one]
    change 1 / (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ)) = _
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.ne_zero
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqne
    have hnC : (n : ℂ) = (q : ℂ) * (p : ℂ) := by exact_mod_cast hprod.symm
    rw [hnC]
    field_simp [hpC, hqC, Real.pi_ne_zero, Complex.I_ne_zero]
  · rw [if_neg hpn]
    have hzero (m : NonzeroFourierIndex) : g m = 0 := by
      have hne : n ≠ (m : ℤ) * (p : ℤ) := by
        intro heq
        apply hpn
        refine ⟨(m : ℤ), ?_⟩
        simpa [mul_comm] using! heq
      simp [g, hne]
    have hsumzero : HasSum g 0 := by
      exact (hasSum_zero :
        HasSum (fun _ : NonzeroFourierIndex ↦ (0 : ℂ)) 0).congr_fun hzero
    exact hseries.unique hsumzero

/-- Dilation preserves the zero mean of the sawtooth. -/
theorem fourierCoeff_positiveDilation_sawtooth_zero (p : ℕ+) :
    fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  let g : NonzeroFourierIndex → ℂ := fun m ↦
    (1 / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))) *
      if (0 : ℤ) = (m : ℤ) * (p : ℤ) then 1 else 0
  have hmapped := (fourierCoefficientCLM 0).hasSum
    (hasSum_positiveDilation_sawtooth p)
  have hseries : HasSum g
      (fourierCoeff
        (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) 0) := by
    simpa only [g, map_smul, smul_eq_mul, fourierCoefficientCLM_apply,
      fourierCoeff_fourierLp] using! hmapped
  have hzero (m : NonzeroFourierIndex) : g m = 0 := by
    simp [g, m.property]
  have hsumzero : HasSum g 0 := by
    exact (hasSum_zero :
      HasSum (fun _ : NonzeroFourierIndex ↦ (0 : ℂ)) 0).congr_fun hzero
  exact hseries.unique hsumzero

/-- The positive Fourier coefficient obtained by inserting all positive
Ramanujan moduli in the periodized kernel.  This is the right-hand side of
the manuscript's coefficient formula before Möbius collapse. -/
def allDenominatorPositiveCoefficient (N n : ℕ) : ℂ :=
  (-Complex.I / (2 * (Real.pi : ℂ))) *
    ((∑' p : ℕ+,
      ((ramanujanSum (p : ℕ) (n : ℤ)).re / (p : ℝ) ^ 2) *
        hStarRatio n ((p : ℕ) * N) : ℝ) : ℂ)

/-- The divisor mass that remains after the exact Möbius collapse.  The
endpoint `d = N` carries weight one half. -/
def midpointDivisorMass (N n : ℕ) : ℝ :=
  (∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
    if N ∣ n then (N : ℝ) / 2 else 0

/-- Exact collapsed form of the all-denominator positive coefficient. -/
theorem allDenominatorPositiveCoefficient_eq_collapsed
    (N n : ℕ) (hn : n ≠ 0) :
    allDenominatorPositiveCoefficient N n =
      (midpointDivisorMass N n : ℂ) /
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  rw [allDenominatorPositiveCoefficient,
    ramanujan_hStar_mobius_collapse n N hn]
  simp only [midpointDivisorMass]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hnR, hnC, hpiC, Complex.I_ne_zero]
  simp [Complex.I_sq]

/-! ## The finite rotation sum in `L²` -/

/-- The circle `L²` class of the sum of the first `N` positive dilates of
the sawtooth.  The index `k` in `range N` represents the manuscript's
integer `k + 1`. -/
def rotationSumCircleL2 (N : ℕ) : UnitCircleL2 :=
  ∑ k ∈ Finset.range N,
    positiveDilationL2 ⟨k + 1, Nat.succ_pos k⟩ sawtoothL2

private theorem sum_range_succ_indicator_dvd
    (N n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range N,
      if k + 1 ∣ n then ((k + 1 : ℕ) : ℂ) else 0) =
      ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ N), (d : ℂ) := by
  let s := (Finset.range N).filter (fun k ↦ k + 1 ∣ n)
  have hset : s.image (fun k ↦ k + 1) =
      n.divisors.filter (fun d ↦ d ≤ N) := by
    ext d
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      Nat.mem_divisors]
    constructor
    · rintro ⟨k, ⟨hkN, hkn⟩, rfl⟩
      exact ⟨⟨hkn, hn⟩, Nat.succ_le_iff.mpr hkN⟩
    · rintro ⟨⟨hdn, _hn⟩, hdN⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
      refine ⟨d - 1, ⟨?_, ?_⟩, ?_⟩
      · omega
      · simpa [show d - 1 + 1 = d by omega] using hdn
      · omega
  calc
    (∑ k ∈ Finset.range N,
        if k + 1 ∣ n then ((k + 1 : ℕ) : ℂ) else 0) =
        ∑ k ∈ s, ((k + 1 : ℕ) : ℂ) := by
      symm
      exact Finset.sum_filter (fun k ↦ k + 1 ∣ n)
        (fun k ↦ ((k + 1 : ℕ) : ℂ))
    _ = ∑ d ∈ s.image (fun k : ℕ ↦ k + 1), (d : ℂ) := by
      symm
      exact Finset.sum_image
        (f := fun d : ℕ ↦ (d : ℂ)) (g := fun k : ℕ ↦ k + 1)
        (by
          intro a ha b hb hab
          exact Nat.add_right_cancel hab)
    _ = ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ N), (d : ℂ) := by
      rw [hset]

/-- Exact positive-frequency coefficient of the finite rotation sum. -/
theorem fourierCoeff_rotationSumCircleL2
    (N n : ℕ) (hn : n ≠ 0) :
    fourierCoeff
        (rotationSumCircleL2 N : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      (∑ d ∈ n.divisors.filter (fun d ↦ d ≤ N), (d : ℂ)) /
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  rw [← fourierCoefficientCLM_apply]
  simp only [rotationSumCircleL2, map_sum]
  calc
    (∑ k ∈ Finset.range N,
        fourierCoefficientCLM (n : ℤ)
          (positiveDilationL2 ⟨k + 1, Nat.succ_pos k⟩ sawtoothL2)) =
        ∑ k ∈ Finset.range N,
          if k + 1 ∣ n then
            ((k + 1 : ℕ) : ℂ) /
              (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [fourierCoefficientCLM_apply]
      exact fourierCoeff_positiveDilation_sawtooth
        ⟨k + 1, Nat.succ_pos k⟩ n hn
    _ = (∑ k ∈ Finset.range N,
          if k + 1 ∣ n then ((k + 1 : ℕ) : ℂ) else 0) /
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      calc
        (∑ k ∈ Finset.range N,
            if k + 1 ∣ n then
              ((k + 1 : ℕ) : ℂ) /
                (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
            else 0) =
            ∑ k ∈ Finset.range N,
              (if k + 1 ∣ n then ((k + 1 : ℕ) : ℂ) else 0) /
                (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          split_ifs <;> simp
        _ = (∑ k ∈ Finset.range N,
              if k + 1 ∣ n then ((k + 1 : ℕ) : ℂ) else 0) /
                (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
          rw [Finset.sum_div]
    _ = (∑ d ∈ n.divisors.filter (fun d ↦ d ≤ N), (d : ℂ)) /
          (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      rw [sum_range_succ_indicator_dvd N n hn]

/-- Splitting the divisor prefix at its endpoint exposes exactly the
half-weighted mass used by the Möbius collapse. -/
theorem sum_divisors_filter_le_eq_lt_add_endpoint
    (N n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors.filter (fun d ↦ d ≤ N), (d : ℝ)) =
      (∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
        if N ∣ n then (N : ℝ) else 0 := by
  have hmem : N ∈ n.divisors ↔ N ∣ n := by
    simp [Nat.mem_divisors, hn]
  have hterm (d : ℕ) :
      (if d ≤ N then (d : ℝ) else 0) =
        (if d < N then (d : ℝ) else 0) +
          if d = N then (d : ℝ) else 0 := by
    by_cases hlt : d < N
    · simp [hlt, hlt.le, ne_of_lt hlt]
    · by_cases heq : d = N
      · simp [heq]
      · have hNlt : N < d := by omega
        have hdnot : ¬d ≤ N := Nat.not_le_of_lt hNlt
        simp [hlt, heq, hdnot]
  have hendpoint :
      (∑ d ∈ n.divisors, if d = N then (d : ℝ) else 0) =
        if N ∈ n.divisors then (N : ℝ) else 0 := by
    by_cases hN : N ∈ n.divisors <;> simp [hN]
  calc
    (∑ d ∈ n.divisors.filter (fun d ↦ d ≤ N), (d : ℝ)) =
        ∑ d ∈ n.divisors, if d ≤ N then (d : ℝ) else 0 :=
      Finset.sum_filter (fun d ↦ d ≤ N) (fun d ↦ (d : ℝ))
    _ = (∑ d ∈ n.divisors, if d < N then (d : ℝ) else 0) +
          ∑ d ∈ n.divisors, if d = N then (d : ℝ) else 0 := by
      simp_rw [hterm]
      exact Finset.sum_add_distrib
    _ = (∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∈ n.divisors then (N : ℝ) else 0 := by
      rw [Finset.sum_filter, hendpoint]
    _ = (∑ d ∈ n.divisors.filter (fun d ↦ d < N), (d : ℝ)) +
          if N ∣ n then (N : ℝ) else 0 := by
      by_cases hN : N ∣ n
      · simp [hN, hmem.mpr hN]
      · have hnotmem : N ∉ n.divisors := fun h ↦ hN (hmem.mp h)
        simp [hN, hnotmem]

/-! ## Exact all-denominator reconstruction in `L²` -/

/-- The `L²` realization of the full-denominator periodization.  The exact
coefficient calculation below proves the manuscript's identity
`Z_{N,∞} = S_N - (1/2) ψ(N·)` at every positive mode. -/
def allDenominatorReconstructionL2 (N : ℕ+) : UnitCircleL2 :=
  rotationSumCircleL2 (N : ℕ) -
    (1 / 2 : ℂ) • positiveDilationL2 N sawtoothL2

/-- Every positive Fourier coefficient of the `L²` reconstruction agrees
exactly with the all-modulus Fourier--Ramanujan coefficient. -/
theorem fourierCoeff_allDenominatorReconstructionL2
    (N : ℕ+) (n : ℕ) (hn : n ≠ 0) :
    fourierCoeff
        (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      allDenominatorPositiveCoefficient (N : ℕ) n := by
  rw [allDenominatorPositiveCoefficient_eq_collapsed (N : ℕ) n hn]
  rw [← fourierCoefficientCLM_apply]
  simp only [allDenominatorReconstructionL2, map_sub, map_smul,
    fourierCoefficientCLM_apply, smul_eq_mul]
  rw [fourierCoeff_rotationSumCircleL2 (N : ℕ) n hn,
    fourierCoeff_positiveDilation_sawtooth N n hn]
  have hprefixR :=
    sum_divisors_filter_le_eq_lt_add_endpoint (N : ℕ) n hn
  have hprefixC := congrArg (fun x : ℝ ↦ (x : ℂ)) hprefixR
  push_cast at hprefixC
  by_cases hN : (N : ℕ) ∣ n
  · simp [hN] at hprefixC
    rw [if_pos hN, hprefixC]
    simp only [midpointDivisorMass, if_pos hN]
    push_cast
    ring
  · simp [hN] at hprefixC
    rw [if_neg hN, hprefixC]
    simp only [midpointDivisorMass, if_neg hN]
    push_cast
    ring

private theorem sum_range_succ_indicator_dvd_int
    (N : ℕ) (n : ℤ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range N,
      if ((k + 1 : ℕ) : ℤ) ∣ n then ((k + 1 : ℕ) : ℂ) else 0) =
      ∑ d ∈ n.natAbs.divisors.filter (fun d ↦ d ≤ N), (d : ℂ) := by
  have hnabs : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  calc
    (∑ k ∈ Finset.range N,
        if ((k + 1 : ℕ) : ℤ) ∣ n then ((k + 1 : ℕ) : ℂ) else 0) =
        ∑ k ∈ Finset.range N,
          if k + 1 ∣ n.natAbs then ((k + 1 : ℕ) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [Int.natCast_dvd]
    _ = ∑ d ∈ n.natAbs.divisors.filter (fun d ↦ d ≤ N), (d : ℂ) :=
      sum_range_succ_indicator_dvd N n.natAbs hnabs

/-- Exact coefficient of the finite rotation sum at an arbitrary nonzero
integer frequency. -/
theorem fourierCoeff_rotationSumCircleL2_int
    (N : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (rotationSumCircleL2 N : AddCircle (1 : ℝ) → ℂ) n =
      (∑ d ∈ n.natAbs.divisors.filter (fun d ↦ d ≤ N), (d : ℂ)) /
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
  rw [← fourierCoefficientCLM_apply]
  simp only [rotationSumCircleL2, map_sum]
  calc
    (∑ k ∈ Finset.range N,
        fourierCoefficientCLM n
          (positiveDilationL2 ⟨k + 1, Nat.succ_pos k⟩ sawtoothL2)) =
        ∑ k ∈ Finset.range N,
          if ((k + 1 : ℕ) : ℤ) ∣ n then
            ((k + 1 : ℕ) : ℂ) /
              (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [fourierCoefficientCLM_apply]
      exact fourierCoeff_positiveDilation_sawtooth_int
        ⟨k + 1, Nat.succ_pos k⟩ n hn
    _ = (∑ k ∈ Finset.range N,
          if ((k + 1 : ℕ) : ℤ) ∣ n then ((k + 1 : ℕ) : ℂ) else 0) /
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      calc
        (∑ k ∈ Finset.range N,
            if ((k + 1 : ℕ) : ℤ) ∣ n then
              ((k + 1 : ℕ) : ℂ) /
                (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
            else 0) =
            ∑ k ∈ Finset.range N,
              (if ((k + 1 : ℕ) : ℤ) ∣ n then
                ((k + 1 : ℕ) : ℂ) else 0) /
                  (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          split_ifs <;> simp
        _ = (∑ k ∈ Finset.range N,
              if ((k + 1 : ℕ) : ℤ) ∣ n then
                ((k + 1 : ℕ) : ℂ) else 0) /
                  (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
          rw [Finset.sum_div]
    _ = (∑ d ∈ n.natAbs.divisors.filter (fun d ↦ d ≤ N), (d : ℂ)) /
          (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      rw [sum_range_succ_indicator_dvd_int N n hn]

theorem fourierCoeff_rotationSumCircleL2_zero (N : ℕ) :
    fourierCoeff (rotationSumCircleL2 N : AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  rw [← fourierCoefficientCLM_apply]
  simp only [rotationSumCircleL2, map_sum]
  apply Finset.sum_eq_zero
  intro k _hk
  rw [fourierCoefficientCLM_apply,
    fourierCoeff_positiveDilation_sawtooth_zero]

/-- The complete coefficient sequence of the all-denominator
reconstruction, including the zero and negative modes. -/
def exactAllDenominatorCoefficient (N : ℕ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else
    (midpointDivisorMass N n.natAbs : ℂ) /
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))

/-- The manuscript's exact all-denominator identity, expressed as equality
of every Fourier coefficient of an actual `L²` class.  In particular, this
also proves square summability of the displayed coefficient sequence. -/
theorem fourierCoeff_allDenominatorReconstructionL2_int
    (N : ℕ+) (n : ℤ) :
    fourierCoeff
        (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ) n =
      exactAllDenominatorCoefficient (N : ℕ) n := by
  by_cases hn : n = 0
  · subst n
    rw [exactAllDenominatorCoefficient, if_pos rfl]
    rw [← fourierCoefficientCLM_apply]
    simp only [allDenominatorReconstructionL2, map_sub, map_smul,
      fourierCoefficientCLM_apply, smul_eq_mul,
      fourierCoeff_rotationSumCircleL2_zero,
      fourierCoeff_positiveDilation_sawtooth_zero]
    ring
  · rw [exactAllDenominatorCoefficient, if_neg hn]
    rw [← fourierCoefficientCLM_apply]
    simp only [allDenominatorReconstructionL2, map_sub, map_smul,
      fourierCoefficientCLM_apply, smul_eq_mul]
    rw [fourierCoeff_rotationSumCircleL2_int (N : ℕ) n hn,
      fourierCoeff_positiveDilation_sawtooth_int N n hn]
    have hprefixR := sum_divisors_filter_le_eq_lt_add_endpoint
      (N : ℕ) n.natAbs (Int.natAbs_ne_zero.mpr hn)
    have hprefixC := congrArg (fun x : ℝ ↦ (x : ℂ)) hprefixR
    push_cast at hprefixC
    by_cases hN : (N : ℕ) ∣ n.natAbs
    · have hNZ : (N : ℤ) ∣ n := Int.natCast_dvd.mpr hN
      simp [hN] at hprefixC
      rw [if_pos hNZ, hprefixC]
      simp only [midpointDivisorMass, if_pos hN]
      push_cast
      ring
    · have hNZ : ¬(N : ℤ) ∣ n := fun h ↦ hN (Int.natCast_dvd.mp h)
      simp [hN] at hprefixC
      rw [if_neg hNZ, hprefixC]
      simp only [midpointDivisorMass, if_neg hN]
      push_cast
      ring

/-- At positive modes the complete coefficient sequence specializes to the
Ramanujan coefficient defined before collapse. -/
theorem exactAllDenominatorCoefficient_natCast
    (N : ℕ+) (n : ℕ) (hn : n ≠ 0) :
    exactAllDenominatorCoefficient (N : ℕ) (n : ℤ) =
      allDenominatorPositiveCoefficient (N : ℕ) n := by
  calc
    exactAllDenominatorCoefficient (N : ℕ) (n : ℤ) =
        fourierCoeff
          (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ)
            (n : ℤ) :=
      (fourierCoeff_allDenominatorReconstructionL2_int N (n : ℤ)).symm
    _ = allDenominatorPositiveCoefficient (N : ℕ) n :=
      fourierCoeff_allDenominatorReconstructionL2 N n hn

/-- The exact coefficient sequence is square summable because it is the
Fourier sequence of the reconstructed `L²` class. -/
theorem summable_sq_exactAllDenominatorCoefficient (N : ℕ+) :
    Summable fun n : ℤ ↦
      ‖exactAllDenominatorCoefficient (N : ℕ) n‖ ^ 2 := by
  have h := (hasSum_sq_fourierCoeff (allDenominatorReconstructionL2 N)).summable
  simpa only [fourierCoeff_allDenominatorReconstructionL2_int] using! h

/-- Full `L²` Fourier reconstruction from the exact all-denominator
coefficient sequence. -/
theorem hasSum_exactAllDenominatorFourierSeries (N : ℕ+) :
    HasSum
      (fun n : ℤ ↦
        exactAllDenominatorCoefficient (N : ℕ) n • fourierLp 2 n)
      (allDenominatorReconstructionL2 N) := by
  simpa only [fourierCoeff_allDenominatorReconstructionL2_int] using!
    hasSum_fourier_series_L2 (allDenominatorReconstructionL2 N)

/-- Fourier coefficients uniquely characterize the all-denominator
reconstruction in `L²`; there is no hidden choice of a representative. -/
theorem eq_allDenominatorReconstructionL2_of_fourierCoeff
    (N : ℕ+) (f : UnitCircleL2)
    (hf : ∀ n : ℤ,
      fourierCoeff (f : AddCircle (1 : ℝ) → ℂ) n =
        exactAllDenominatorCoefficient (N : ℕ) n) :
    f = allDenominatorReconstructionL2 N := by
  apply fourierBasis.repr.injective
  ext n
  rw [fourierBasis_repr, fourierBasis_repr, hf,
    fourierCoeff_allDenominatorReconstructionL2_int]

/-! ## Representatives and the literal finite sum -/

/-- The finite rotation sum as a concrete complex-valued function on the
unit circle. -/
def rotationSumCircleFunction (N : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ k ∈ Finset.range N,
    sawtoothCircle (positiveCircleDilation ⟨k + 1, Nat.succ_pos k⟩ x)

theorem positiveDilationL2_sawtooth_coe_ae (p : ℕ+) :
    (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle]
      fun x ↦ sawtoothCircle (positiveCircleDilation p x) := by
  have hcomp := Lp.coeFn_compMeasurePreserving sawtoothL2
    (positiveCircleDilation_measurePreserving p)
  have hsaw :=
    (positiveCircleDilation_measurePreserving p).quasiMeasurePreserving.ae
      sawtoothL2_coe_ae
  exact hcomp.trans hsaw

/-- The `L²` class `rotationSumCircleL2` is represented almost everywhere
by the literal finite circle sum. -/
theorem rotationSumCircleL2_coe_ae (N : ℕ) :
    (rotationSumCircleL2 N : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle]
      rotationSumCircleFunction N := by
  induction N with
  | zero =>
      simpa [rotationSumCircleL2, rotationSumCircleFunction] using!
        (Lp.coeFn_zero ℂ 2
          (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))
  | succ N ih =>
      let p : ℕ+ := ⟨N + 1, Nat.succ_pos N⟩
      have hdecomp : rotationSumCircleL2 (N + 1) =
          rotationSumCircleL2 N + positiveDilationL2 p sawtoothL2 := by
        simp [rotationSumCircleL2, Finset.sum_range_succ, p]
      rw [hdecomp]
      filter_upwards [Lp.coeFn_add (rotationSumCircleL2 N)
          (positiveDilationL2 p sawtoothL2), ih,
        positiveDilationL2_sawtooth_coe_ae p] with x hadd hprev hlast
      rw [hadd]
      change (rotationSumCircleL2 N : AddCircle (1 : ℝ) → ℂ) x +
          (positiveDilationL2 p sawtoothL2 : AddCircle (1 : ℝ) → ℂ) x = _
      rw [hprev, hlast]
      simp [rotationSumCircleFunction, Finset.sum_range_succ, p]

/-- Concrete representative of the exact all-denominator identity. -/
def allDenominatorReconstructionCircle
    (N : ℕ+) (x : AddCircle (1 : ℝ)) : ℂ :=
  rotationSumCircleFunction (N : ℕ) x -
    (1 / 2 : ℂ) * sawtoothCircle (positiveCircleDilation N x)

/-- The exact identity is an equality in `L²`, with the displayed literal
finite-sum representative holding almost everywhere. -/
theorem allDenominatorReconstructionL2_coe_ae (N : ℕ+) :
    (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle]
      allDenominatorReconstructionCircle N := by
  filter_upwards [Lp.coeFn_sub (rotationSumCircleL2 (N : ℕ))
      ((1 / 2 : ℂ) • positiveDilationL2 N sawtoothL2),
    Lp.coeFn_smul (1 / 2 : ℂ) (positiveDilationL2 N sawtoothL2),
    rotationSumCircleL2_coe_ae (N : ℕ),
    positiveDilationL2_sawtooth_coe_ae N] with x hsub hsmul hrot hdil
  rw [show allDenominatorReconstructionL2 N =
      rotationSumCircleL2 (N : ℕ) -
        (1 / 2 : ℂ) • positiveDilationL2 N sawtoothL2 by rfl]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  change (rotationSumCircleL2 (N : ℕ) : AddCircle (1 : ℝ) → ℂ) x -
      (1 / 2 : ℂ) *
        (positiveDilationL2 N sawtoothL2 : AddCircle (1 : ℝ) → ℂ) x = _
  rw [hrot, hdil]
  rfl
end

end Erdos1002

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeRanks
import ErdosProblems.Erdos186.PZ.Reduction.FailureEstimates

/-!
# Uniform one-step estimates on a bounded-rank trace

The exact integer estimates in `FailureEstimates` and
`NoDimensionIncrease` are converted here to the uniform real multiplier used
by the Lemma-10 bookkeeping.
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

/-- The fixed loss which dominates both the upward Lemma-6 coefficient and
the residue-fibre coefficient while selected ranks and scale denominators
are bounded by `R` and `D`. -/
def uniformStepCost (R D : ℕ) : ℝ :=
  (2 : ℝ) ^ R * (2 * D + 1 : ℕ) ^ R * (2 : ℝ) ^ R * (D : ℝ) ^ R

theorem one_le_uniformStepCost {R D : ℕ} (hD : 0 < D) :
    1 ≤ uniformStepCost R D := by
  have hDn : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h₁ : (1 : ℝ) ≤ 2 ^ R := one_le_pow₀ (by norm_num)
  have h₂ : (1 : ℝ) ≤ (2 * D + 1 : ℕ) ^ R := by
    exact_mod_cast (one_le_pow₀ (show 1 ≤ 2 * D + 1 by omega) :
      1 ≤ (2 * D + 1) ^ R)
  have h₃ : (1 : ℝ) ≤ (D : ℝ) ^ R := one_le_pow₀ hDn
  dsimp [uniformStepCost]
  calc
    (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
    _ ≤ (2 : ℝ) ^ R * (2 * D + 1 : ℕ) ^ R *
        (2 : ℝ) ^ R * (D : ℝ) ^ R := by gcongr

/-- If `m^a ≤ D k`, division by `k^q` gains `m^{-aq}`, up to the
fixed factor `D^R`. -/
theorem inv_pow_dilation_le
    {m : ℕ} {a : ℝ} {D k q R : ℕ}
    (hm : 0 < m) (hD : 0 < D) (hk : 0 < k) (hq : q ≤ R)
    (hscale : Real.rpow (m : ℝ) a ≤ (D : ℝ) * (k : ℝ)) :
    ((k : ℝ) ^ q)⁻¹ ≤
      (D : ℝ) ^ R * (Real.rpow (m : ℝ) (-a)) ^ q := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hpowpos : 0 < Real.rpow (m : ℝ) a :=
    Real.rpow_pos_of_pos hmreal _
  have hinv : (k : ℝ)⁻¹ ≤
      (D : ℝ) * Real.rpow (m : ℝ) (-a) := by
    rw [show Real.rpow (m : ℝ) (-a) =
      (Real.rpow (m : ℝ) a)⁻¹ from Real.rpow_neg hmreal.le a]
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_iff₀ hkreal).2
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpowpos).2 (by simpa [mul_comm] using hscale)
  calc
    ((k : ℝ) ^ q)⁻¹ = ((k : ℝ)⁻¹) ^ q := by rw [inv_pow]
    _ ≤ ((D : ℝ) * Real.rpow (m : ℝ) (-a)) ^ q :=
      pow_le_pow_left₀ (by positivity) hinv q
    _ = (D : ℝ) ^ q * (Real.rpow (m : ℝ) (-a)) ^ q :=
      mul_pow _ _ _
    _ ≤ (D : ℝ) ^ R * (Real.rpow (m : ℝ) (-a)) ^ q := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hDreal hq)
        (pow_nonneg (Real.rpow_nonneg hmreal.le _) _)

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma : ℝ}

/-- One upward coordinate replacement, on a bounded-rank portion of the
trace, has the uniform source saving. -/
theorem CoordinateReplacement.selectedVolume_dimensionIncrease_uniform
    {S T : CoordinateReplacementState selector}
    (hST : CoordinateReplacement selector delta gamma S T)
    {m : ℕ} {a : ℝ} {R Q : ℕ}
    (hm : 0 < m)
    (hSrank : S.selected.dimension ≤ R)
    (hTrank : T.selected.dimension ≤ R)
    (hTambient : T.ambientDimension ≤ Q)
    (hrank : S.selected.dimension < T.selected.dimension)
    (hscale : Real.rpow (m : ℝ) a ≤
      ((selector.input T.points T.eligible).scale : ℝ)) :
    (T.selected.progression.volume : ℝ) ≤
      uniformStepCost R (scaleDenSum C Q) *
        (Real.rpow (m : ℝ) (-a) ^
          (T.selected.dimension - S.selected.dimension)) *
            (S.selected.progression.volume : ℝ) := by
  let D := scaleDenSum C Q
  let q := T.selected.dimension - S.selected.dimension
  have hD : 0 < D := scaleDenSum_pos C Q
  have hden : T.selected.witness.scaleDen ≤ D := by
    rw [T.selected_scaleDen]
    exact scaleDen_le_scaleDenSum C hTambient
  have hqR : q ≤ R := by dsimp [q]; omega
  have hk : 0 < T.selected.dilation := T.selected.witness.k_pos
  have hscaleNat := T.selected.witness.scale_lower
  have hscaleNum : T.selected.witness.scaleNum =
      C.scaleNum T.ambientDimension :=
    (selector.input T.points T.eligible).selectedCFP_scaleNum
  rw [hscaleNum] at hscaleNat
  have hnum : 1 ≤ C.scaleNum T.ambientDimension := C.scaleNum_pos _
  have hscaleDilation : Real.rpow (m : ℝ) a ≤
      (D : ℝ) * (T.selected.dilation : ℝ) := by
    have hscale_le : (selector.input T.points T.eligible).scale ≤
        T.selected.witness.scaleDen * T.selected.dilation := by
      calc
        (selector.input T.points T.eligible).scale =
            1 * (selector.input T.points T.eligible).scale := by simp
        _ ≤ C.scaleNum T.ambientDimension *
              (selector.input T.points T.eligible).scale :=
          Nat.mul_le_mul_right _ hnum
        _ ≤ T.selected.witness.scaleDen * T.selected.dilation := by
          simpa [CoordinateReplacementState.selected,
            BoundedCFPSelector.chosen, EligibleInput.selectedCFP] using hscaleNat
    exact hscale.trans <| by
      exact_mod_cast hscale_le.trans
        (Nat.mul_le_mul_right _ hden)
  have hinv := inv_pow_dilation_le hm hD hk hqR hscaleDilation
  have hexact := hST.selectedVolume_dimensionIncrease hrank.le
  have hexactReal :
      (T.selected.dilation : ℝ) ^ q *
          (T.selected.progression.volume : ℝ) ≤
        (2 : ℝ) ^ T.selected.dimension *
          (2 * T.selected.witness.scaleDen : ℕ) ^ S.selected.dimension *
            ((2 : ℝ) ^ S.selected.dimension *
              (S.selected.progression.volume : ℝ)) := by
    exact_mod_cast hexact
  have hkpow : 0 < (T.selected.dilation : ℝ) ^ q := by positivity
  have hdivide : (T.selected.progression.volume : ℝ) ≤
      (((2 : ℝ) ^ T.selected.dimension *
          (2 * T.selected.witness.scaleDen : ℕ) ^ S.selected.dimension *
            ((2 : ℝ) ^ S.selected.dimension *
              (S.selected.progression.volume : ℝ))) /
        (T.selected.dilation : ℝ) ^ q) := by
    exact (le_div_iff₀ hkpow).2 (by simpa [mul_comm] using hexactReal)
  have hgeom :
      (2 : ℝ) ^ T.selected.dimension *
          (2 * T.selected.witness.scaleDen : ℕ) ^ S.selected.dimension *
            (2 : ℝ) ^ S.selected.dimension ≤
        (2 : ℝ) ^ R * (2 * D + 1 : ℕ) ^ R * (2 : ℝ) ^ R := by
    have htwoT : (2 : ℝ) ^ T.selected.dimension ≤ (2 : ℝ) ^ R :=
      pow_le_pow_right₀ (by norm_num) hTrank
    have hdenBase : (2 * T.selected.witness.scaleDen : ℕ) ≤ 2 * D + 1 :=
      (Nat.mul_le_mul_left 2 hden).trans (Nat.le_add_right _ 1)
    have hdenPow : ((2 * T.selected.witness.scaleDen : ℕ) : ℝ) ^
        S.selected.dimension ≤ ((2 * D + 1 : ℕ) : ℝ) ^ R := by
      exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdenBase) _).trans
        (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * D + 1 by omega))
          hSrank)
    have htwoS : (2 : ℝ) ^ S.selected.dimension ≤ (2 : ℝ) ^ R :=
      pow_le_pow_right₀ (by norm_num) hSrank
    exact mul_le_mul (mul_le_mul htwoT hdenPow (by positivity) (by positivity))
      htwoS (by positivity) (by positivity)
  calc
    (T.selected.progression.volume : ℝ) ≤
        (((2 : ℝ) ^ T.selected.dimension *
          (2 * T.selected.witness.scaleDen : ℕ) ^ S.selected.dimension *
            ((2 : ℝ) ^ S.selected.dimension *
              (S.selected.progression.volume : ℝ))) /
        (T.selected.dilation : ℝ) ^ q) := hdivide
    _ = ((2 : ℝ) ^ T.selected.dimension *
          (2 * T.selected.witness.scaleDen : ℕ) ^ S.selected.dimension *
            (2 : ℝ) ^ S.selected.dimension) *
          (S.selected.progression.volume : ℝ) *
            (((T.selected.dilation : ℝ) ^ q)⁻¹) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((2 : ℝ) ^ R * (2 * D + 1 : ℕ) ^ R * (2 : ℝ) ^ R) *
          (S.selected.progression.volume : ℝ) *
            (((T.selected.dilation : ℝ) ^ q)⁻¹) := by
      gcongr
    _ ≤ ((2 : ℝ) ^ R * (2 * D + 1 : ℕ) ^ R * (2 : ℝ) ^ R) *
          (S.selected.progression.volume : ℝ) *
            ((D : ℝ) ^ R * (Real.rpow (m : ℝ) (-a)) ^ q) := by
      gcongr
    _ = uniformStepCost R D *
        (Real.rpow (m : ℝ) (-a) ^ q) *
          (S.selected.progression.volume : ℝ) := by
      simp [uniformStepCost]
      ring

/-- One non-upward coordinate replacement has the uniform residue-fibre
cost; in the equal-rank case the sharper `gamma` factor is used instead. -/
theorem CoordinateReplacement.selectedVolume_nonup_uniform
    {S T : CoordinateReplacementState selector}
    (hST : CoordinateReplacement selector delta gamma S T)
    {R Q : ℕ}
    (hSrank : S.selected.dimension ≤ R)
    (hTrank : T.selected.dimension ≤ R)
    (hTambient : T.ambientDimension ≤ Q)
    (hrank : T.selected.dimension < S.selected.dimension) :
    (T.selected.progression.volume : ℝ) ≤
      uniformStepCost R (scaleDenSum C Q) *
        (S.selected.progression.volume : ℝ) := by
  let D := scaleDenSum C Q
  have hD : 0 < D := scaleDenSum_pos C Q
  have hden : T.selected.witness.scaleDen ≤ D := by
    rw [T.selected_scaleDen]
    exact scaleDen_le_scaleDenSum C hTambient
  have hraw := hST.selectedVolume_le
  have hrawReal :
      (T.selected.progression.volume : ℝ) ≤
        (2 : ℝ) ^ T.selected.dimension *
          ((2 * T.selected.witness.scaleDen + 1 : ℕ) ^
            S.selected.dimension *
              ((2 : ℝ) ^ S.selected.dimension *
                (S.selected.progression.volume : ℝ))) := by
    exact_mod_cast hraw
  calc
    (T.selected.progression.volume : ℝ) ≤ _ := hrawReal
    _ = ((2 : ℝ) ^ T.selected.dimension *
          (2 * T.selected.witness.scaleDen + 1 : ℕ) ^ S.selected.dimension *
            (2 : ℝ) ^ S.selected.dimension) *
          (S.selected.progression.volume : ℝ) := by ring
    _ ≤ ((2 : ℝ) ^ R * (2 * D + 1 : ℕ) ^ R *
          (2 : ℝ) ^ R) * (S.selected.progression.volume : ℝ) := by
      have htwoT : (2 : ℝ) ^ T.selected.dimension ≤ (2 : ℝ) ^ R :=
        pow_le_pow_right₀ (by norm_num) hTrank
      have hdenBase : 2 * T.selected.witness.scaleDen + 1 ≤ 2 * D + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hden) 1
      have hdenPow : (((2 * T.selected.witness.scaleDen + 1 : ℕ) : ℝ) ^
          S.selected.dimension) ≤ (((2 * D + 1 : ℕ) : ℝ) ^ R) := by
        exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdenBase) _).trans
          (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * D + 1 by omega))
            hSrank)
      have htwoS : (2 : ℝ) ^ S.selected.dimension ≤ (2 : ℝ) ^ R :=
        pow_le_pow_right₀ (by norm_num) hSrank
      gcongr
    _ ≤ uniformStepCost R D * (S.selected.progression.volume : ℝ) := by
      dsimp [uniformStepCost]
      have hDR : (1 : ℝ) ≤ (D : ℝ) ^ R :=
        one_le_pow₀ (by exact_mod_cast hD)
      have hbase0 : 0 ≤ (2 : ℝ) ^ R *
          (((2 * D + 1 : ℕ) : ℝ) ^ R) * (2 : ℝ) ^ R := by positivity
      have hvol0 : 0 ≤ (S.selected.progression.volume : ℝ) := by positivity
      calc
        (2 : ℝ) ^ R * (((2 * D + 1 : ℕ) : ℝ) ^ R) *
              (2 : ℝ) ^ R * (S.selected.progression.volume : ℝ) =
            ((2 : ℝ) ^ R * (((2 * D + 1 : ℕ) : ℝ) ^ R) *
              (2 : ℝ) ^ R) * 1 *
                (S.selected.progression.volume : ℝ) := by ring
        _ ≤ ((2 : ℝ) ^ R * (((2 * D + 1 : ℕ) : ℝ) ^ R) *
              (2 : ℝ) ^ R) * ((D : ℝ) ^ R) *
                (S.selected.progression.volume : ℝ) := by gcongr

/-- Numerical parameters for a bounded-rank portion of the guarded process. -/
def quantitativeMoveParameters (C : HigherDimensionalContext beta eta)
    (delta gamma : ℝ) (m : ℕ) (a : ℝ)
    (R Q : ℕ) (hdelta : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hm : 0 < m) (ha : 0 ≤ a) :
    MoveParameters where
  retention := delta
  cost := uniformStepCost R (scaleDenSum C Q)
  shrinkFactor := gamma
  upBase := Real.rpow (m : ℝ) (-a)
  retention_nonneg := hdelta
  one_le_cost := one_le_uniformStepCost (scaleDenSum_pos C Q)
  shrinkFactor_nonneg := hgamma0
  shrinkFactor_le_one := hgamma1
  upBase_nonneg := Real.rpow_nonneg (by positivity) _
  upBase_le_one := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast hm
    · linarith

/-- Uniformly bounded ranks, ambient dimensions, and next-state scales turn
an exact coordinate trace into the numerical trace used by Lemma 10. -/
def coordinateTraceControl_of_bounds
    {initial : CoordinateReplacementState selector} {length : ℕ}
    (T : RelationTrace (CoordinateReplacement selector delta gamma)
      initial length)
    {m : ℕ} {a : ℝ} {R Q : ℕ}
    (hdelta : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hm : 0 < m) (ha : 0 ≤ a)
    (hrank : ∀ i, i ≤ length → (T.state i).selected.dimension ≤ R)
    (hambient : ∀ i, i < length →
      (T.state (i + 1)).ambientDimension ≤ Q)
    (hscale : ∀ i, i < length →
      Real.rpow (m : ℝ) a ≤
        ((selector.input (T.state (i + 1)).points
          (T.state (i + 1)).eligible).scale : ℝ)) :
    CoordinateTraceControl
      (quantitativeMoveParameters C delta gamma m a R Q
        hdelta hgamma0 hgamma1 hm ha) T := by
  let p := quantitativeMoveParameters C delta gamma m a R Q
    hdelta hgamma0 hgamma1 hm ha
  refine {
    retention_eq := rfl
    upSaving := fun i ↦ p.upBase ^
      ((T.state (i + 1)).selected.dimension -
        (T.state i).selected.dimension)
    upSaving_nonneg := ?_
    gap_control := ?_
    upSaving_control := ?_ }
  · intro i hi
    exact pow_nonneg p.upBase_nonneg _
  · intro i hi
    let S := T.state i
    let U := T.state (i + 1)
    have hST := T.valid i hi
    have hSr := hrank i (by omega)
    have hUr := hrank (i + 1) (by omega)
    have hUa := hambient i hi
    have hUs := hscale i hi
    have hrule := coordinateMoveKind_dimension_rule S U
    cases hkind : coordinateMoveKind S U with
    | up =>
        have hlt : S.selected.dimension < U.selected.dimension := by
          simpa [hkind] using hrule
        have hbound := hST.selectedVolume_dimensionIncrease_uniform hm
          hSr hUr hUa hlt hUs
        simpa [p, quantitativeMoveParameters, stepMultiplier, hkind,
          S, U, mul_assoc] using hbound
    | down =>
        have hlt : U.selected.dimension < S.selected.dimension := by
          simpa [hkind] using hrule
        have hbound := hST.selectedVolume_nonup_uniform hSr hUr hUa hlt
        simpa [p, quantitativeMoveParameters, stepMultiplier, hkind, S, U]
          using hbound
    | shrink =>
        have heq : U.selected.dimension = S.selected.dimension := by
          simpa [hkind] using hrule
        have hbound := hST.selectedVolume_lt_of_dimension_eq heq
        simpa [p, quantitativeMoveParameters, stepMultiplier, hkind, S, U]
          using hbound.le
  · intro i hi hkind
    exact le_rfl

end

end Erdos186.PZ.Reduction

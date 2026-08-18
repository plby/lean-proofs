/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionBox
import ErdosProblems.Erdos186.PZ.Intersection.DilationVolume
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientPostCFPAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SourceReverseControl

/-!
# Uniform covolume bounds for the two source side progressions
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The determinant of a full-dimensional progression occupying a `gamma`
fraction of a source progression and lying in its fixed control box is at
most a dimension-dependent constant divided by `gamma`. -/
theorem gamma_mul_stepMatrix_det_natAbs_le_sourceControlConstant
    {ambient r : ℕ} (P : GAP r r) (S : GAP ambient r)
    (m : ℕ) (z : LatticePoint r)
    (gamma : ℝ)
    (hP : P.Nondegenerate)
    (hcontain : P.carrier ⊆ CFP.translate z (controlIntegerBox S m).carrier)
    (hvolume : gamma * (S.volume : ℝ) ≤ (P.volume : ℝ)) :
    gamma * ((stepMatrix P).det.natAbs : ℝ) ≤
      ((2 ^ r * r.factorial * (2 * m) ^ r : ℕ) : ℝ) := by
  let pActive : ℝ := ∏ i, ((P.widths i - 1 : ℕ) : ℝ)
  let sActive : ℝ := ∏ i, ((S.widths i - 1 : ℕ) : ℝ)
  let det : ℝ := ((stepMatrix P).det.natAbs : ℝ)
  have hpActive : 0 ≤ pActive := by
    dsimp only [pActive]
    positivity
  have hsActive : 0 ≤ sActive := by
    dsimp only [sActive]
    positivity
  have hdetNonneg : 0 ≤ det := by
    dsimp only [det]
    positivity
  have hSvolume : 0 < (S.volume : ℝ) := by
    dsimp only [GAP.volume]
    exact_mod_cast (Finset.prod_pos fun i _ ↦ S.width_pos i :
      0 < ∏ i, S.widths i)
  have hPvolumeActive : (P.volume : ℝ) ≤ (2 ^ r : ℕ) * pActive := by
    dsimp only [pActive]
    exact_mod_cast volume_le_two_pow_mul_prod_width_sub_one P hP
  have hSactiveVolume : sActive ≤ (S.volume : ℝ) := by
    dsimp only [sActive, GAP.volume]
    have hnat : (∏ i, (S.widths i - 1)) ≤ ∏ i, S.widths i := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦
        Nat.sub_le (S.widths i) 1
    exact_mod_cast hnat
  have hdet := stepMatrix_det_scaledVolume_le_boxVolume P
    (controlIntegerBox S m) z hcontain
  have hboxProduct :
      (∏ j, (((controlIntegerBox S m).upper j -
          (controlIntegerBox S m).lower j : ℤ) : ℝ)) =
        ((2 * m : ℕ) : ℝ) ^ r * sActive := by
    dsimp only [controlIntegerBox, sActive]
    push_cast
    calc
      (∏ i : Fin r, ((m : ℝ) * (S.widths i - 1 : ℕ) -
          -((m : ℝ) * (S.widths i - 1 : ℕ)))) =
          ∏ i : Fin r, (((2 * m : ℕ) : ℝ) *
            ((S.widths i - 1 : ℕ) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
      _ = (∏ _i : Fin r, ((2 * m : ℕ) : ℝ)) *
          ∏ i : Fin r, ((S.widths i - 1 : ℕ) : ℝ) := by
        rw [Finset.prod_mul_distrib]
      _ = ((2 * m : ℕ) : ℝ) ^ r *
          ∏ i : Fin r, ((S.widths i - 1 : ℕ) : ℝ) := by simp
      _ = (2 * (m : ℝ)) ^ r *
          ∏ i : Fin r, ((S.widths i - 1 : ℕ) : ℝ) := by norm_cast
  rw [hboxProduct] at hdet
  have hdet' : det * pActive ≤
      (r.factorial : ℝ) * ((2 * m : ℕ) : ℝ) ^ r * sActive := by
    simpa only [det, pActive, sActive, mul_assoc] using hdet
  have hscaledVolume : gamma * (S.volume : ℝ) ≤
      (2 ^ r : ℕ) * pActive := hvolume.trans hPvolumeActive
  have hmulDet : gamma * det * (S.volume : ℝ) ≤
      (2 ^ r : ℕ) * (r.factorial : ℝ) *
        ((2 * m : ℕ) : ℝ) ^ r * (S.volume : ℝ) := by
    calc
      gamma * det * (S.volume : ℝ) =
          det * (gamma * (S.volume : ℝ)) := by ring
      _ ≤ det * ((2 ^ r : ℕ) * pActive) := by gcongr
      _ = (2 ^ r : ℕ) * (det * pActive) := by ring
      _ ≤ (2 ^ r : ℕ) *
          ((r.factorial : ℝ) * ((2 * m : ℕ) : ℝ) ^ r * sActive) := by
        exact mul_le_mul_of_nonneg_left hdet' (by positivity)
      _ ≤ (2 ^ r : ℕ) * (r.factorial : ℝ) *
          ((2 * m : ℕ) : ℝ) ^ r * (S.volume : ℝ) := by
        have hfactor : 0 ≤ (2 ^ r : ℕ) * (r.factorial : ℝ) *
            ((2 * m : ℕ) : ℝ) ^ r := by positivity
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hSactiveVolume hfactor)
  push_cast
  change gamma * det ≤
    (2 : ℝ) ^ r * (r.factorial : ℝ) * (2 * (m : ℝ)) ^ r
  apply le_of_mul_le_mul_right ?_ hSvolume
  push_cast at hmulDet
  simpa only [mul_assoc] using hmulDet

/-- The fixed determinant constant at one source rank. -/
def sourceStepDeterminantConstant
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (r : ℕ) : ℕ :=
  2 ^ r * r.factorial * (2 * (2 * context.scaleDen r)) ^ r

/-- A finite bound for the determinant-power covering constants in every
rank up to `rankCeiling`. -/
def sourceCommonCoveringRadiusBound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (rankCeiling + 1),
    sourceStepDeterminantConstant context r ^ (2 * r)

theorem sourceStepDeterminantConstant_pow_le_commonBound
    {beta eta : ℝ} (context : Reduction.HigherDimensionalContext beta eta)
    {r rankCeiling : ℕ} (hr : r ≤ rankCeiling) :
    sourceStepDeterminantConstant context r ^ (2 * r) ≤
      sourceCommonCoveringRadiusBound context rankCeiling := by
  unfold sourceCommonCoveringRadiusBound
  refine Finset.single_le_sum
    (f := fun i : ℕ ↦ sourceStepDeterminantConstant context i ^ (2 * i))
    (s := Finset.range (rankCeiling + 1)) ?_ ?_
  · intro i _
    exact Nat.zero_le _
  · simp only [Finset.mem_range]
    omega

/-- Both determinants in the canonical high-coefficient side package obey
the same fixed source constant. -/
theorem HighCoefficientSideSelectionData.gamma_mul_stepDeterminants_le
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}
    (E : HighCoefficientSideSelectionData selector hA D theta gamma) :
    let r := (selector.chosen A hA).dimension
    gamma * ((stepMatrix (rankCastGAP E.forwardWitness.progression
      E.forwardWitness_rank)).det.natAbs : ℝ) ≤
        sourceStepDeterminantConstant context r ∧
    gamma * ((stepMatrix (rankCastGAP E.reverseWitness.progression
      E.reverseWitness_rank)).det.natAbs : ℝ) ≤
        sourceStepDeterminantConstant context r := by
  dsimp only
  let S := selector.chosen A hA
  let r := S.dimension
  let m := sourceControlScale selector hA
  let B := controlIntegerBox S.progression m
  let P₁ := rankCastGAP E.forwardWitness.progression E.forwardWitness_rank
  let P₂ := rankCastGAP E.reverseWitness.progression E.reverseWitness_rank
  have hcontain₁ : P₁.carrier ⊆ CFP.translate E.translate₁ B.carrier := by
    dsimp only [P₁]
    rw [rankCastGAP_carrier, E.forwardWitness_progression_carrier]
    simpa only [B, m] using E.contained₁
  have hcontain₂ : P₂.carrier ⊆ CFP.translate (-E.translate₂) B.carrier := by
    dsimp only [P₂]
    rw [rankCastGAP_carrier, E.reverseWitness_progression_carrier]
    simpa only [B, m, negatedGAP.carrier] using
      negatedGAP_carrier_subset_translate_controlIntegerBox
        S.progression m E.side₂.progression E.translate₂ E.contained₂
  have hvolume₁ : gamma * (S.progression.volume : ℝ) ≤
      (P₁.volume : ℝ) := by
    dsimp only [P₁]
    rw [rankCastGAP_volume, E.forwardWitness_progression_volume]
    exact E.volume₁
  have hvolume₂ : gamma * (S.progression.volume : ℝ) ≤
      (P₂.volume : ℝ) := by
    dsimp only [P₂]
    rw [rankCastGAP_volume, E.reverseWitness_progression_volume]
    exact E.volume₂
  have H₁ := gamma_mul_stepMatrix_det_natAbs_le_sourceControlConstant
    P₁ S.progression m E.translate₁ gamma
    (rankCastGAP_nondegenerate E.forwardWitness_rank
      E.forwardWitness.progression_nondegenerate)
    hcontain₁ hvolume₁
  have H₂ := gamma_mul_stepMatrix_det_natAbs_le_sourceControlConstant
    P₂ S.progression m (-E.translate₂) gamma
    (rankCastGAP_nondegenerate E.reverseWitness_rank
      E.reverseWitness.progression_nondegenerate)
    hcontain₂ hvolume₂
  constructor
  · change gamma * ((stepMatrix P₁).det.natAbs : ℝ) ≤
      (sourceStepDeterminantConstant context r : ℕ)
    dsimp only [sourceStepDeterminantConstant, m, sourceControlScale]
    push_cast
    push_cast at H₁
    change gamma * ((stepMatrix P₁).det.natAbs : ℝ) ≤
      (2 : ℝ) ^ r * (r.factorial : ℝ) *
        (2 * (2 * (context.scaleDen r : ℝ))) ^ r
    change gamma * ((stepMatrix P₁).det.natAbs : ℝ) ≤
      (2 : ℝ) ^ r * (r.factorial : ℝ) *
        (2 * ((2 * context.scaleDen r : ℕ) : ℝ)) ^ r at H₁
    norm_cast at H₁ ⊢
  · change gamma * ((stepMatrix P₂).det.natAbs : ℝ) ≤
      (sourceStepDeterminantConstant context r : ℕ)
    dsimp only [sourceStepDeterminantConstant, m, sourceControlScale]
    push_cast
    push_cast at H₂
    change gamma * ((stepMatrix P₂).det.natAbs : ℝ) ≤
      (2 : ℝ) ^ r * (r.factorial : ℝ) *
        (2 * (2 * (context.scaleDen r : ℝ))) ^ r
    change gamma * ((stepMatrix P₂).det.natAbs : ℝ) ≤
      (2 : ℝ) ^ r * (r.factorial : ℝ) *
        (2 * ((2 * context.scaleDen r : ℕ) : ℝ)) ^ r at H₂
    norm_cast at H₂ ⊢

/-- The determinant-power common covering radius is uniformly controlled by
`gamma ^ (-2 * rankCeiling)`.  This division-free form is the one used by
the frozen-source square-root-range asymptotics. -/
theorem HighCoefficientSideSelectionData.gamma_pow_mul_commonCoveringRadius_le
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu theta gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}
    (E : HighCoefficientSideSelectionData selector hA D theta gamma)
    {rankCeiling : ℕ}
    (hrank : (selector.chosen A hA).dimension ≤ rankCeiling)
    (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1) :
    gamma ^ (2 * rankCeiling) * (E.commonCoveringRadius : ℝ) ≤
      sourceCommonCoveringRadiusBound context rankCeiling := by
  let r := (selector.chosen A hA).dimension
  let d₁ : ℝ := ((stepMatrix (rankCastGAP E.forwardWitness.progression
    E.forwardWitness_rank)).det.natAbs : ℝ)
  let d₂ : ℝ := ((stepMatrix (rankCastGAP E.reverseWitness.progression
    E.reverseWitness_rank)).det.natAbs : ℝ)
  let K : ℝ := sourceStepDeterminantConstant context r
  obtain ⟨hdet₁, hdet₂⟩ := E.gamma_mul_stepDeterminants_le
  have hgammaNonneg : 0 ≤ gamma := hgamma.le
  have hd₁ : 0 ≤ d₁ := by dsimp only [d₁]; positivity
  have hd₂ : 0 ≤ d₂ := by dsimp only [d₂]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpow₁ : (gamma * d₁) ^ r ≤ K ^ r :=
    pow_le_pow_left₀ (mul_nonneg hgammaNonneg hd₁) hdet₁ r
  have hpow₂ : (gamma * d₂) ^ r ≤ K ^ r :=
    pow_le_pow_left₀ (mul_nonneg hgammaNonneg hd₂) hdet₂ r
  have hpair : gamma ^ (2 * r) * (E.commonCoveringRadius : ℝ) ≤
      K ^ (2 * r) := by
    have hmul := mul_le_mul hpow₁ hpow₂
      (pow_nonneg (mul_nonneg hgammaNonneg hd₂) r) (pow_nonneg hK r)
    dsimp only [HighCoefficientSideSelectionData.commonCoveringRadius]
    push_cast
    change gamma ^ (2 * r) * (d₁ ^ r * d₂ ^ r) ≤ K ^ (2 * r)
    calc
      gamma ^ (2 * r) * (d₁ ^ r * d₂ ^ r) =
          (gamma * d₁) ^ r * (gamma * d₂) ^ r := by
        rw [show 2 * r = r + r by omega, pow_add, mul_pow, mul_pow]
        ring
      _ ≤ K ^ r * K ^ r := hmul
      _ = K ^ (2 * r) := by
        rw [show 2 * r = r + r by omega, pow_add]
  have hgammaPow : gamma ^ (2 * rankCeiling) ≤ gamma ^ (2 * r) := by
    exact pow_le_pow_of_le_one hgammaNonneg hgammaOne (by omega)
  have hradiusNonneg : 0 ≤ (E.commonCoveringRadius : ℝ) := by positivity
  calc
    gamma ^ (2 * rankCeiling) * (E.commonCoveringRadius : ℝ) ≤
        gamma ^ (2 * r) * (E.commonCoveringRadius : ℝ) :=
      mul_le_mul_of_nonneg_right hgammaPow hradiusNonneg
    _ ≤ K ^ (2 * r) := hpair
    _ ≤ sourceCommonCoveringRadiusBound context rankCeiling := by
      dsimp only [K, r]
      exact_mod_cast
        sourceStepDeterminantConstant_pow_le_commonBound context hrank

end

end Erdos186.PZ.Intersection

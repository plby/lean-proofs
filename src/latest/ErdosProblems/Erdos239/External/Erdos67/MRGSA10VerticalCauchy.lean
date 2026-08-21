import ErdosProblems.Erdos239.External.Erdos67.MRHalaszBands

/-!
# A consumer form of vertical Cauchy--Schwarz for GS A.10

The GHS window estimate naturally exports two numerical second-moment
bounds.  This file turns those bounds directly into the corresponding
three-factor contour estimate.
-/

open MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- `L∞ × L² × L²` on a symmetric interval, with the two
second moments already replaced by numerical upper bounds. -/
theorem norm_intervalIntegral_triple_le_Linfty_mul_L2_bounds
    {f g k : ℝ → ℂ} {M E₁ E₂ T : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hg : Continuous g) (hk : Continuous k)
    (hf : ∀ t, |t| ≤ T → ‖f t‖ ≤ M)
    (hgEnergy : (∫ t in -T..T, ‖g t‖ ^ (2 : ℝ)) ≤ E₁)
    (hkEnergy : (∫ t in -T..T, ‖k t‖ ^ (2 : ℝ)) ≤ E₂) :
    ‖∫ t in -T..T, f t * g t * k t‖ ≤
      M * E₁ ^ ((1 : ℝ) / 2) * E₂ ^ ((1 : ℝ) / 2) := by
  let S : Set ℝ := Set.Ioc (-T) T
  have hgLp : MemLp g (2 : ENNReal) (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
    exact (hg.norm.pow 2).integrableOn_Ioc
  have hkLp : MemLp k (2 : ENNReal) (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).2
    exact (hk.norm.pow 2).integrableOn_Ioc
  have hbase := norm_intervalIntegral_triple_le_Linfty_mul_L2_mul_L2
    (f := f) (g := g) (k := k) hM hT hf hgLp hkLp
  have hg0 : 0 ≤ ∫ t in -T..T, ‖g t‖ ^ (2 : ℝ) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun t ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hk0 : 0 ≤ ∫ t in -T..T, ‖k t‖ ^ (2 : ℝ) :=
    intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun t ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hE₁ : 0 ≤ E₁ := hg0.trans hgEnergy
  have hE₂ : 0 ≤ E₂ := hk0.trans hkEnergy
  have hgPow :
      (∫ t in -T..T, ‖g t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤
        E₁ ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hg0 hgEnergy (by norm_num)
  have hkPow :
      (∫ t in -T..T, ‖k t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤
        E₂ ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hk0 hkEnergy (by norm_num)
  calc
    ‖∫ t in -T..T, f t * g t * k t‖ ≤
        M *
          ((∫ t in -T..T, ‖g t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
          ((∫ t in -T..T, ‖k t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := hbase
    _ ≤ M * E₁ ^ ((1 : ℝ) / 2) * E₂ ^ ((1 : ℝ) / 2) := by
      calc
        M *
            ((∫ t in -T..T, ‖g t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
            ((∫ t in -T..T, ‖k t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ≤
            M *
              ((∫ t in -T..T, ‖g t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
                E₂ ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hkPow
            (mul_nonneg hM (Real.rpow_nonneg hg0 _))
        _ ≤ M * E₁ ^ ((1 : ℝ) / 2) * E₂ ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgPow hM)
            (Real.rpow_nonneg hE₂ _)

end

end Erdos67.MRHalaszBands

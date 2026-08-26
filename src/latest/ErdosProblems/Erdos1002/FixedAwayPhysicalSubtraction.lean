import ErdosProblems.Erdos1002.FixedAwayInfiniteCarriers
import ErdosProblems.Erdos1002.NaturalCutoffShotFourierReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Physical subtraction model for the fixed-away cutoff

The conditionally convergent fixed-away periodization need not be built a
second time.  We subtract the compact nearest-cell correction from the
already constructed natural-cutoff reconstruction.  Since the correction
is supported in `|pδ_p| < t < 1/2`, it is a finite nearest-cell function,
and the window-error identity is then literal algebra in circle `L²`.
-/

open MeasureTheory Set AddCircle
open scoped BigOperators ENNReal Real

namespace Erdos1002

noncomputable section

/-- The compact correction `(1-χ)(pδ_p)` times one primitive shot. -/
def fixedAwayCorrectionShotTerm
    (t δ : ℝ) (N p : ℕ) (alpha : ℝ) : ℂ :=
  (fixedAwaySmoothCorrection t δ
      ((p : ℝ) * resonanceDelta p alpha) : ℂ) *
    (primitiveShot N p alpha : ℂ)

/-- The complementary smooth fixed-away shot `χ(pδ_p) Y_p`. -/
def fixedAwaySmoothShotTerm
    (t δ : ℝ) (N p : ℕ) (alpha : ℝ) : ℂ :=
  (fixedAwaySmoothCutoff t δ
      ((p : ℝ) * resonanceDelta p alpha) : ℂ) *
    (primitiveShot N p alpha : ℂ)

def fixedAwayCorrectionShotSum
    (t δ : ℝ) (N P : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 P, fixedAwayCorrectionShotTerm t δ N p alpha

def fixedAwaySmoothShotSum
    (t δ : ℝ) (N P : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 P, fixedAwaySmoothShotTerm t δ N p alpha

/-- The physical smooth and compact pieces add to the literal primitive
shot sum pointwise, including exact rational resonances. -/
theorem fixedAwaySmooth_add_correction_eq_primitive
    (t δ : ℝ) (N P : ℕ) (alpha : ℝ) :
    fixedAwaySmoothShotSum t δ N P alpha +
        fixedAwayCorrectionShotSum t δ N P alpha =
      (primitiveShotSum N P alpha : ℂ) := by
  unfold fixedAwaySmoothShotSum fixedAwayCorrectionShotSum primitiveShotSum
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  unfold fixedAwaySmoothShotTerm fixedAwayCorrectionShotTerm
    fixedAwaySmoothCorrection
  push_cast
  ring

theorem measurable_fixedAwayCorrectionShotTerm
    (t δ : ℝ) (N p : ℕ) :
    Measurable (fixedAwayCorrectionShotTerm t δ N p) := by
  unfold fixedAwayCorrectionShotTerm
  exact (((fixedAwaySmoothCorrection_contDiff (m := 1) t δ).continuous.measurable.comp
      (measurable_const.mul (measurable_resonanceDelta p))).complex_ofReal).mul
    (measurable_primitiveShot N p).complex_ofReal

theorem measurable_fixedAwaySmoothShotTerm
    (t δ : ℝ) (N p : ℕ) :
    Measurable (fixedAwaySmoothShotTerm t δ N p) := by
  unfold fixedAwaySmoothShotTerm
  exact (((fixedAwaySmoothCutoff_contDiff (m := 1) t δ).continuous.measurable.comp
      (measurable_const.mul (measurable_resonanceDelta p))).complex_ofReal).mul
    (measurable_primitiveShot N p).complex_ofReal

theorem measurable_fixedAwayCorrectionShotSum
    (t δ : ℝ) (N P : ℕ) :
    Measurable (fixedAwayCorrectionShotSum t δ N P) := by
  unfold fixedAwayCorrectionShotSum
  exact Finset.measurable_fun_sum (Finset.Icc 1 P) fun p _ ↦
    measurable_fixedAwayCorrectionShotTerm t δ N p

theorem measurable_fixedAwaySmoothShotSum
    (t δ : ℝ) (N P : ℕ) :
    Measurable (fixedAwaySmoothShotSum t δ N P) := by
  unfold fixedAwaySmoothShotSum
  exact Finset.measurable_fun_sum (Finset.Icc 1 P) fun p _ ↦
    measurable_fixedAwaySmoothShotTerm t δ N p

theorem norm_fixedAwayCorrectionShotTerm_le
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N p : ℕ) (alpha : ℝ) :
    ‖fixedAwayCorrectionShotTerm t δ N p alpha‖ ≤
      ‖(primitiveShot N p alpha : ℂ)‖ := by
  unfold fixedAwayCorrectionShotTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcut := fixedAwaySmoothCorrection_mem_Icc hδ hδt
    ((p : ℝ) * resonanceDelta p alpha)
  rw [abs_of_nonneg hcut.1]
  simpa only [one_mul] using!
    mul_le_mul_of_nonneg_right hcut.2 (norm_nonneg _)

theorem norm_fixedAwaySmoothShotTerm_le
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N p : ℕ) (alpha : ℝ) :
    ‖fixedAwaySmoothShotTerm t δ N p alpha‖ ≤
      ‖(primitiveShot N p alpha : ℂ)‖ := by
  unfold fixedAwaySmoothShotTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcut := fixedAwaySmoothCutoff_mem_Icc hδ hδt
    ((p : ℝ) * resonanceDelta p alpha)
  rw [abs_of_nonneg hcut.1]
  simpa only [one_mul] using!
    mul_le_mul_of_nonneg_right hcut.2 (norm_nonneg _)

theorem norm_fixedAwayCorrectionShotSum_le_bound
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) (alpha : ℝ) :
    ‖fixedAwayCorrectionShotSum t δ N P alpha‖ ≤
      primitiveShotSumBound N P := by
  unfold fixedAwayCorrectionShotSum primitiveShotSumBound
  calc
    ‖∑ p ∈ Finset.Icc 1 P,
        fixedAwayCorrectionShotTerm t δ N p alpha‖ ≤
      ∑ p ∈ Finset.Icc 1 P,
        ‖fixedAwayCorrectionShotTerm t δ N p alpha‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
        ‖(primitiveShot N p alpha : ℂ)‖ := by
      gcongr with p hp
      exact norm_fixedAwayCorrectionShotTerm_le hδ hδt N p alpha
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
        (N : ℝ) / (2 * (p : ℝ)) := by
      gcongr with p hp
      exact norm_primitiveShot_le N p alpha (Finset.mem_Icc.mp hp).1

theorem norm_fixedAwaySmoothShotSum_le_bound
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) (alpha : ℝ) :
    ‖fixedAwaySmoothShotSum t δ N P alpha‖ ≤
      primitiveShotSumBound N P := by
  unfold fixedAwaySmoothShotSum primitiveShotSumBound
  calc
    ‖∑ p ∈ Finset.Icc 1 P,
        fixedAwaySmoothShotTerm t δ N p alpha‖ ≤
      ∑ p ∈ Finset.Icc 1 P,
        ‖fixedAwaySmoothShotTerm t δ N p alpha‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
        ‖(primitiveShot N p alpha : ℂ)‖ := by
      gcongr with p hp
      exact norm_fixedAwaySmoothShotTerm_le hδ hδt N p alpha
    _ ≤ ∑ p ∈ Finset.Icc 1 P,
        (N : ℝ) / (2 * (p : ℝ)) := by
      gcongr with p hp
      exact norm_primitiveShot_le N p alpha (Finset.mem_Icc.mp hp).1

/-- Fundamental-domain representatives of the two physical pieces. -/
def fixedAwayCorrectionShotCircle
    (t δ : ℝ) (N P : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (fixedAwayCorrectionShotSum t δ N P)

def fixedAwaySmoothShotCircle
    (t δ : ℝ) (N P : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (fixedAwaySmoothShotSum t δ N P)

theorem fixedAwayCorrectionShotCircle_memLp
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) :
    MemLp (fixedAwayCorrectionShotCircle t δ N P) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (fixedAwayCorrectionShotSum t δ N P) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    apply MemLp.of_bound
      (measurable_fixedAwayCorrectionShotSum t δ N P).aestronglyMeasurable
      (primitiveShotSumBound N P)
    filter_upwards with alpha
    exact norm_fixedAwayCorrectionShotSum_le_bound hδ hδt N P alpha
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0
      (fixedAwayCorrectionShotSum t δ N P)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

theorem fixedAwaySmoothShotCircle_memLp
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) :
    MemLp (fixedAwaySmoothShotCircle t δ N P) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (fixedAwaySmoothShotSum t δ N P) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    apply MemLp.of_bound
      (measurable_fixedAwaySmoothShotSum t δ N P).aestronglyMeasurable
      (primitiveShotSumBound N P)
    filter_upwards with alpha
    exact norm_fixedAwaySmoothShotSum_le_bound hδ hδt N P alpha
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0
      (fixedAwaySmoothShotSum t δ N P)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

def fixedAwayCorrectionShotL2
    (t δ : ℝ) (N P : ℕ) (hδ : 0 < δ) (hδt : δ ≤ t) :
    UnitCircleL2 :=
  (fixedAwayCorrectionShotCircle_memLp hδ hδt N P).toLp
    (fixedAwayCorrectionShotCircle t δ N P)

def fixedAwaySmoothShotL2
    (t δ : ℝ) (N P : ℕ) (hδ : 0 < δ) (hδt : δ ≤ t) :
    UnitCircleL2 :=
  (fixedAwaySmoothShotCircle_memLp hδ hδt N P).toLp
    (fixedAwaySmoothShotCircle t δ N P)

theorem fixedAwayCorrectionShotL2_coe_ae
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) :
    (fixedAwayCorrectionShotL2 t δ N P hδ hδt :
        AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fixedAwayCorrectionShotCircle t δ N P :=
  (fixedAwayCorrectionShotCircle_memLp hδ hδt N P).coeFn_toLp

theorem fixedAwaySmoothShotL2_coe_ae
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) :
    (fixedAwaySmoothShotL2 t δ N P hδ hδt :
        AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fixedAwaySmoothShotCircle t δ N P :=
  (fixedAwaySmoothShotCircle_memLp hδ hδt N P).coeFn_toLp

/-- The physical `L²` decomposition, with no principal-value limit. -/
theorem fixedAwaySmoothShotL2_add_correction
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (N P : ℕ) :
    fixedAwaySmoothShotL2 t δ N P hδ hδt +
        fixedAwayCorrectionShotL2 t δ N P hδ hδt =
      primitiveShotSumL2 N P := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (fixedAwaySmoothShotL2 t δ N P hδ hδt)
      (fixedAwayCorrectionShotL2 t δ N P hδ hδt),
    fixedAwaySmoothShotL2_coe_ae hδ hδt N P,
    fixedAwayCorrectionShotL2_coe_ae hδ hδt N P,
    primitiveShotSumL2_coe_ae N P] with x hadd hs hc hp
  rw [hadd]
  change
    (fixedAwaySmoothShotL2 t δ N P hδ hδt :
        AddCircle (1 : ℝ) → ℂ) x +
      (fixedAwayCorrectionShotL2 t δ N P hδ hδt :
        AddCircle (1 : ℝ) → ℂ) x =
      (primitiveShotSumL2 N P : AddCircle (1 : ℝ) → ℂ) x
  rw [hs, hc, hp]
  unfold fixedAwaySmoothShotCircle fixedAwayCorrectionShotCircle
    primitiveShotSumCircle AddCircle.liftIoc
  change fixedAwaySmoothShotSum t δ N P
      ((AddCircle.equivIoc 1 0 x : Ioc (0 : ℝ) (0 + 1)) : ℝ) +
    fixedAwayCorrectionShotSum t δ N P
      ((AddCircle.equivIoc 1 0 x : Ioc (0 : ℝ) (0 + 1)) : ℝ) =
    (primitiveShotSum N P
      ((AddCircle.equivIoc 1 0 x : Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℂ)
  exact fixedAwaySmooth_add_correction_eq_primitive t δ N P
    ((AddCircle.equivIoc 1 0 x : Ioc (0 : ℝ) (0 + 1)) : ℝ)

/-- The smooth fixed-away reconstruction is the already rigorous full
natural reconstruction minus the compact cell correction. -/
def fixedAwaySmoothReconstructionL2
    (N : ℕ+) (P : ℕ) (t δ : ℝ)
    (hδ : 0 < δ) (hδt : δ ≤ t) : UnitCircleL2 :=
  naturalCutoffReconstructionL2 N P -
    fixedAwayCorrectionShotL2 t δ (N : ℕ) P hδ hδt

/-- Exact transfer of the previously proved nearest-cell/window error to
the smooth fixed-away cutoff. -/
theorem fixedAwaySmooth_windowError_identity
    (N : ℕ+) (P : ℕ) {t δ : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t) :
    fixedAwaySmoothShotL2 t δ (N : ℕ) P hδ hδt -
        fixedAwaySmoothReconstructionL2 N P t δ hδ hδt =
      primitiveShotSumL2 (N : ℕ) P - naturalCutoffReconstructionL2 N P := by
  unfold fixedAwaySmoothReconstructionL2
  calc
    fixedAwaySmoothShotL2 t δ (N : ℕ) P hδ hδt -
          (naturalCutoffReconstructionL2 N P -
            fixedAwayCorrectionShotL2 t δ (N : ℕ) P hδ hδt) =
        (fixedAwaySmoothShotL2 t δ (N : ℕ) P hδ hδt +
          fixedAwayCorrectionShotL2 t δ (N : ℕ) P hδ hδt) -
            naturalCutoffReconstructionL2 N P := by abel
    _ = primitiveShotSumL2 (N : ℕ) P -
        naturalCutoffReconstructionL2 N P := by
      rw [fixedAwaySmoothShotL2_add_correction hδ hδt]

end

end Erdos1002

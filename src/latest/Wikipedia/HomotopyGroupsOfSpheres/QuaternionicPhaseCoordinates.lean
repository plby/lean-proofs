import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicScalarPhaseFamily

/-!
# A smooth family in fixed source and target coordinates

The scalar phase is varied through the actual complex exponential. Source
coordinates stay centered at the original preimage; target coordinates stay
centered at its unchanged first column. This keeps both derivative spaces
fixed while the phase varies.
-/

noncomputable section

open scoped ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicSymmetricMatrices QuaternionicColumns QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ
local notation "QSphere" => SphereCenteredCoordinates.UnitSphere (QuaternionSpace 1)

def phaseProjection (z : UnitSphere) (a : ℝ) (p : ParameterSpace z) : Fin 2 → ℍ :=
  firstColumnFormula (Real.pi / 2 + p.1) (Real.pi / 2 + p.2.1)
    (scale (Circle.exp a) (symmetricMap (localSphere z p)))

theorem phaseProjection_at_zero_phase (z : UnitSphere) :
    phaseProjection z 0 = localProjection z := by
  funext p
  simp only [phaseProjection, Circle.exp_zero, scale_one, localProjection]

theorem phaseProjection_zero (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : phaseProjection z a 0 = targetColumn := by
  simpa only [phaseProjection, Prod.fst_zero, Prod.snd_zero, add_zero, localSphere_zero] using
    midpoint_scaled_target (Circle.exp a) z hz

theorem contDiff_uncurry_phaseProjection (z : UnitSphere) {n : ℕ∞ω} :
    ContDiff ℝ n (Function.uncurry (phaseProjection z)) := by
  have hq : ContDiff ℝ n (fun y : ℝ × ParameterSpace z ↦ (Circle.exp y.1 : ℂ)) :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const).cexp
  have hB (r k : Fin 3) : ContDiff ℝ n (fun y : ℝ × ParameterSpace z ↦
      (scale (Circle.exp y.1) (symmetricMap (localSphere z y.2))).val.val r k) :=
    hq.mul ((contDiff_symmetricMap_entry (localSphere z)
      (contDiff_localSphere_entry z) r k).comp contDiff_snd)
  apply contDiff_pi.mpr
  intro r
  exact contDiff_firstColumnFormula_entry _ _ _
    (contDiff_const.add contDiff_snd.fst) (contDiff_const.add contDiff_snd.snd.fst) hB r

theorem contDiff_phaseProjection (z : UnitSphere) (a : ℝ) {n : ℕ∞ω} :
    ContDiff ℝ n (phaseProjection z a) := by
  have hB (r k : Fin 3) : ContDiff ℝ n (fun p : ParameterSpace z ↦
      (scale (Circle.exp a) (symmetricMap (localSphere z p))).val.val r k) :=
    contDiff_const.mul (contDiff_symmetricMap_entry (localSphere z)
      (contDiff_localSphere_entry z) r k)
  apply contDiff_pi.mpr
  intro r
  exact contDiff_firstColumnFormula_entry _ _ _
    (contDiff_const.add contDiff_fst) (contDiff_const.add contDiff_snd.fst) hB r

theorem phaseProjection_pairing (z : UnitSphere) (a : ℝ) (p : ParameterSpace z) :
    pairing (phaseProjection z a p) (phaseProjection z a p) = 1 :=
  firstColumnFormula_pairing (Real.pi / 2 + p.1) (Real.pi / 2 + p.2.1)
    (scale (Circle.exp a) (symmetricMap (localSphere z p)))

theorem phaseProjection_norm (z : UnitSphere) (a : ℝ) (p : ParameterSpace z) :
    ‖(WithLp.toLp 2 (phaseProjection z a p) : QuaternionSpace 1)‖ = 1 :=
  (pairing_self_eq_one_iff_norm (phaseProjection z a p)).mp (phaseProjection_pairing z a p)

def phaseColumn (z : UnitSphere) (a : ℝ) (p : ParameterSpace z) : QSphere :=
  ⟨WithLp.toLp 2 (phaseProjection z a p), mem_sphere_zero_iff_norm.mpr
    (phaseProjection_norm z a p)⟩

theorem contDiff_uncurry_phaseColumn_val (z : UnitSphere) {n : ℕ∞ω} :
    ContDiff ℝ n (fun y : ℝ × ParameterSpace z ↦ (phaseColumn z y.1 y.2).val) :=
  PiLp.contDiff_toLp.comp (contDiff_uncurry_phaseProjection z)

theorem continuous_phaseColumn (z : UnitSphere) (a : ℝ) : Continuous (phaseColumn z a) :=
  ((contDiff_uncurry_phaseColumn_val z (n := 0)).continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

theorem phaseColumn_zero (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : phaseColumn z a 0 = localColumn z 0 := by
  apply Subtype.ext
  change WithLp.toLp 2 (phaseProjection z a 0) = WithLp.toLp 2 (localProjection z 0)
  rw [phaseProjection_zero z hz, localProjection_zero, hz]

def phaseCoordinates (z : UnitSphere) (a : ℝ) (p : ParameterSpace z) : TargetSpace z :=
  SphereCenteredCoordinates.chart (localColumn z 0) (phaseColumn z a p)

theorem phaseCoordinates_zero (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : phaseCoordinates z a 0 = 0 := by
  rw [phaseCoordinates, phaseColumn_zero z hz, SphereCenteredCoordinates.chart_self]

theorem phaseCoordinates_at_zero_phase (z : UnitSphere) :
    phaseCoordinates z 0 = localCoordinateMap z := by
  funext p
  apply congrArg (SphereCenteredCoordinates.chart (localColumn z 0))
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2) (congrFun (phaseProjection_at_zero_phase z) p)

theorem contDiffAt_uncurry_phaseCoordinates (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) {n : ℕ∞ω} :
    ContDiffAt ℝ n (Function.uncurry (phaseCoordinates z)) (a, 0) := by
  have hs : ContDiffAt ℝ n (stereoToFun (-(localColumn z 0).val)) (phaseColumn z a 0).val := by
    rw [phaseColumn_zero z hz]
    exact SphereCenteredCoordinates.contDiffAt_stereoToFun (localColumn z 0)
  change ContDiffAt ℝ n (fun y : ℝ × ParameterSpace z ↦
    stereoToFun (-(localColumn z 0).val) (phaseColumn z y.1 y.2).val) (a, 0)
  exact hs.comp (a, 0) (contDiff_uncurry_phaseColumn_val z).contDiffAt

theorem contDiffAt_phaseCoordinates (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) {n : ℕ∞ω} : ContDiffAt ℝ n (phaseCoordinates z a) 0 :=
  (contDiffAt_uncurry_phaseCoordinates z hz a).comp 0
    (contDiffAt_const.prodMk contDiffAt_id)

theorem continuous_phaseDerivative (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    Continuous (fun a : ℝ ↦ fderiv ℝ (phaseCoordinates z a) 0) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact ((contDiffAt_uncurry_phaseCoordinates z hz a (n := 1)).fderiv
    (show ContDiffAt ℝ 0 (fun _ : ℝ ↦ (0 : ParameterSpace z)) a from contDiffAt_const)
    (by norm_num)).continuousAt

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

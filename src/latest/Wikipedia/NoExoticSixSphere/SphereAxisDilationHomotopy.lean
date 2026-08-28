import Wikipedia.NoExoticSixSphere.SphereAxisDilation
import Mathlib.Topology.Homotopy.Basic

/-! # A whole-sphere positive-scale homotopy fixed at the collapsed pole -/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem axisDilation_base {c : ℝ} (hc : 0 < c) :
    axisDilation c (antipode pinchPole) = antipode pinchPole := by
  apply Subtype.ext
  rw [axisDilation_val hc]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hh : (antipode pinchPole).val 0 = -1 := by simp [antipode, pinchPole, spherePole]
    change (axisDenominator c ((antipode pinchPole).val 0))⁻¹ *
      axisNumerator c ((antipode pinchPole).val 0) = (antipode pinchPole).val 0
    rw [hh]
    norm_num [axisDenominator, axisNumerator]
    ring
  · have hz : (antipode pinchPole).val j.succ = 0 := by simp [antipode, pinchPole, spherePole]
    change (axisDenominator c ((antipode pinchPole).val 0))⁻¹ *
      ((2 * c) * (antipode pinchPole).val j.succ) = (antipode pinchPole).val j.succ
    rw [hz, mul_zero, mul_zero]

def scaleToOne (c : ℝ) (t : unitInterval) : ℝ := (1 - t.val) * c + t.val

theorem scaleToOne_pos {c : ℝ} (hc : 0 < c) (t : unitInterval) : 0 < scaleToOne c t := by
  by_cases ht : 0 < t.val
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.property.2) hc.le) ht
  · have hz : t.val = 0 := le_antisymm (le_of_not_gt ht) t.property.1
    simpa [scaleToOne, hz] using hc

theorem continuous_scaleToOne (c : ℝ) : Continuous (scaleToOne c) :=
  ((continuous_const.sub continuous_subtype_val).mul continuous_const).add continuous_subtype_val

theorem scaleToOne_zero (c : ℝ) : scaleToOne c 0 = c := by simp [scaleToOne]

theorem scaleToOne_one (c : ℝ) : scaleToOne c 1 = 1 := by simp [scaleToOne]

theorem contMDiff_axisDilation {c : ℝ} (hc : 0 < c) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (axisDilation c) := by
  intro x
  exact (contMDiffAt_axisDilation (c, x) hc).comp x (contMDiffAt_const.prodMk contMDiffAt_id)

def axisDilationMap (c : ℝ) (hc : 0 < c) : C(Sphere 3, Sphere 3) :=
  ⟨axisDilation c, (contMDiff_axisDilation hc).continuous⟩

theorem continuous_axisScaleHomotopy {c : ℝ} (hc : 0 < c) :
    Continuous (fun p : unitInterval × Sphere 3 ↦ axisDilation (scaleToOne c p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : ContinuousAt (fun q : unitInterval × Sphere 3 ↦ (scaleToOne c q.1, q.2)) p :=
    (((continuous_scaleToOne c).comp continuous_fst).prodMk continuous_snd).continuousAt
  exact (contMDiffAt_axisDilation (scaleToOne c p.1, p.2)
    (scaleToOne_pos hc p.1)).continuousAt.comp
      (f := fun q : unitInterval × Sphere 3 ↦ (scaleToOne c q.1, q.2)) hp

def axisScaleHomotopy (c : ℝ) (hc : 0 < c) :
    (axisDilationMap c hc).HomotopyRel (ContinuousMap.id (Sphere 3)) {antipode pinchPole} where
  toFun p := axisDilation (scaleToOne c p.1) p.2
  continuous_toFun := continuous_axisScaleHomotopy hc
  map_zero_left x := by rw [scaleToOne_zero]; rfl
  map_one_left x := by rw [scaleToOne_one, axisDilation_one]; rfl
  prop' t x hx := by
    rcases mem_singleton_iff.mp hx with rfl
    change axisDilation (scaleToOne c t) (antipode pinchPole) =
      axisDilation c (antipode pinchPole)
    rw [axisDilation_base (scaleToOne_pos hc t), axisDilation_base hc]

end NoExoticSixSphere.SphereSumNeck

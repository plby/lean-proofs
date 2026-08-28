import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Zero-avoiding linearization near an invertible derivative

An actual derivative estimate gives a small ball on which the nonlinear
remainder is at most half the linear image. Every straight interpolation
between the derivative and the original map therefore avoids zero away
from the center. No local degree formula is assumed.
-/

noncomputable section

open Set Metric Topology Filter Asymptotics ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_remainder_bound {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ball (0 : E) ε,
      ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
  have herr : (fun x : E => f x - L x) =o[𝓝 (0 : E)] (fun x : E => x) := by
    convert hf.isLittleO using 1
    · rfl
    · rfl
    · simp only [hzero, sub_zero]
      rfl
    · simp only [sub_zero]
  have hbig : (fun x : E => x) =O[𝓝 (0 : E)] (fun x : E => L x) := by
    apply isBigO_iff.mpr
    refine ⟨‖L.symm.toContinuousLinearMap‖, Eventually.of_forall ?_⟩
    intro x
    have h := L.symm.toContinuousLinearMap.le_opNorm (L x)
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using h
  exact eventually_nhds_iff_ball.mp
    ((herr.trans_isBigO hbig).bound (by norm_num : (0 : ℝ) < 1 / 2))

def blend (f : E → F) (L : E ≃L[ℝ] F) (t : I) (x : E) : F :=
  L x + (t : ℝ) • (f x - L x)

theorem blend_ne_zero {f : E → F} (L : E ≃L[ℝ] F) (t : I) {x : E}
    (hx : x ≠ 0) (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    blend f L t x ≠ 0 := by
  have hL : L x ≠ 0 := fun h => hx (L.injective (h.trans (map_zero L).symm))
  have hsmall : ‖(t : ℝ) • (f x - L x)‖ < ‖L x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    calc
      (t : ℝ) * ‖f x - L x‖ ≤ ‖f x - L x‖ :=
        mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖L x‖ := hbound
      _ < ‖L x‖ := by nlinarith [norm_pos_iff.mpr hL]
  intro h
  have heq : (t : ℝ) • (f x - L x) = -L x := by
    change L x + (t : ℝ) • (f x - L x) = 0 at h
    rw [add_comm] at h
    exact add_eq_zero_iff_eq_neg.mp h
  rw [heq, norm_neg] at hsmall
  exact (lt_irrefl _ hsmall)

theorem image_ne_zero {f : E → F} (L : E ≃L[ℝ] F) {x : E}
    (hx : x ≠ 0) (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) : f x ≠ 0 := by
  have h := blend_ne_zero L (1 : I) hx hbound
  change L x + (1 : ℝ) • (f x - L x) ≠ 0 at h
  simpa using h

def linearSphereMap (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    C(sphere (0 : E) 1, PuncturedRadial.Space F) :=
  ⟨fun u => ⟨L (r • (u : E)), fun h =>
      (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u))
        (L.injective (h.trans (map_zero L).symm))⟩,
    (L.continuous.comp (continuous_const.smul continuous_subtype_val)).subtype_mk _⟩

variable (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
  (hc : Continuous (fun u : sphere (0 : E) 1 => f (r • (u : E))))
  (hb : ∀ u : sphere (0 : E) 1,
    ‖f (r • (u : E)) - L (r • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (r • (u : E))‖)

def boundaryMap : C(sphere (0 : E) 1, PuncturedRadial.Space F) :=
  ⟨fun u => ⟨f (r • (u : E)), image_ne_zero L
      (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)) (hb u)⟩, hc.subtype_mk _⟩

/-- A genuine homotopy in the punctured target, with the original boundary values. -/
def boundaryHomotopy : (linearSphereMap L r hr).Homotopy (boundaryMap f L r hr hc hb) where
  toFun q := ⟨blend f L q.1 (r • (q.2 : E)), blend_ne_zero L q.1
    (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q.2)) (hb q.2)⟩
  continuous_toFun := by
    have ht : Continuous (fun q : I × sphere (0 : E) 1 => (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hL : Continuous (fun q : I × sphere (0 : E) 1 => L (r • (q.2 : E))) :=
      L.continuous.comp (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact (hL.add (ht.smul ((hc.comp continuous_snd).sub hL))).subtype_mk _
  map_zero_left u := by
    apply Subtype.ext
    simp [blend, linearSphereMap]
  map_one_left u := by
    apply Subtype.ext
    simp [blend, boundaryMap]

end Wikipedia.SmoothSixDPoincare.LocalDegree

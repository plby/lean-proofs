import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Tactic.Linarith

/-! A common angular coordinate on one closed half-plane. The endpoints at
angle 0 and pi are included, so the result applies at a straight boundary. -/

namespace Erdos633b

open InnerProductGeometry

theorem abs_principal_angle_of_abs_le {t : ℝ} (ht : |t| ≤ Real.pi) :
    |(t : Real.Angle).toReal| = |t| := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h] at ht ⊢
    exact Real.Angle.abs_toReal_coe_eq_self_iff.mpr ⟨h, ht⟩
  · have h' : t < 0 := lt_of_not_ge h
    have ht' : -t ≤ Real.pi := by simpa only [abs_of_neg h'] using ht
    have he := Real.Angle.abs_toReal_neg_coe_eq_self_iff.mpr
      (show 0 ≤ -t ∧ -t ≤ Real.pi from ⟨by linarith, ht'⟩)
    simpa only [Real.Angle.coe_neg, neg_neg, abs_of_neg h'] using he

namespace HalfPlaneAngles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

theorem coe_angle_eq_oangle (o : Orientation ℝ V (Fin 2))
    {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (hs : 0 ≤ (o.oangle u v).sign) :
    (angle u v : Real.Angle) = o.oangle u v := by
  rw [o.angle_eq_abs_oangle_toReal hu hv]
  exact Real.Angle.coe_abs_toReal_of_sign_nonneg hs

theorem angle_eq_abs_sub (o : Orientation ℝ V (Fin 2)) {u v w : V}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvsign : 0 ≤ (o.oangle u v).sign) (hwsign : 0 ≤ (o.oangle u w).sign) :
    angle v w = |angle u w - angle u v| := by
  have he : o.oangle v w = ((angle u w - angle u v : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, coe_angle_eq_oangle o hu hv hvsign,
      coe_angle_eq_oangle o hu hw hwsign]
    exact (o.oangle_sub_left hu hv hw).symm
  rw [o.angle_eq_abs_oangle_toReal hv hw, he]
  apply abs_principal_angle_of_abs_le
  apply abs_le.mpr
  constructor <;> linarith [angle_nonneg u v, angle_nonneg u w, angle_le_pi u v, angle_le_pi u w]

theorem sameRay_of_angle_eq (o : Orientation ℝ V (Fin 2)) {u v w : V}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvsign : 0 ≤ (o.oangle u v).sign) (hwsign : 0 ≤ (o.oangle u w).sign)
    (he : angle u v = angle u w) : SameRay ℝ v w := by
  have h := angle_eq_abs_sub o hu hv hw hvsign hwsign
  rw [he, sub_self, abs_zero] at h
  exact o.oangle_eq_zero_iff_sameRay.mp ((o.oangle_eq_zero_iff_angle_eq_zero hv hw).mpr h)

end HalfPlaneAngles

end Erdos633b

import Wikipedia.HopfProblem.QuaternionCoordinatePowerComposition
import Wikipedia.HopfProblem.QuaternionPowerNullhomotopy

/-!
# Radial retraction and power null-homotopies for nonzero quaternions

The radial homotopy is made in the unchanged punctured quaternion space.
It transports the accepted exponent result for the ordinary three-sphere
to actual powers of arbitrary nonzero-quaternion-valued maps.
-/

noncomputable section

open scoped Topology Quaternion unitInterval ContinuousMap

namespace Wikipedia.HopfProblem.QuaternionCoordinatePowers

open UnitQuaternionSphere QuaternionPowerNullhomotopy SixSphereCube

def normalize : C(Punctured, UnitQuaternions) where
  toFun q := ⟨‖q.val‖⁻¹ • q.val, (mem_unitary_iff_norm_eq_one _).mpr (by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr q.property))⟩
  continuous_toFun :=
    (((continuous_norm.comp continuous_subtype_val).inv₀
      (fun q => norm_ne_zero_iff.mpr q.property)).smul continuous_subtype_val).subtype_mk _

def includeUnit : C(UnitQuaternions, Punctured) where
  toFun q := ⟨q.val, unit_ne_zero q⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def radialScalar (t : unitInterval) (q : Punctured) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * ‖q.val‖⁻¹

theorem radialScalar_pos (t : unitInterval) (q : Punctured) : 0 < radialScalar t q := by
  have hn : 0 < ‖q.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr q.property)
  have h₀ := t.property.1
  have h₁ := t.property.2
  by_cases ht : (t : ℝ) = 0
  · simp [radialScalar, ht]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne h₀ (fun h => ht h.symm)
    have hp := mul_pos htpos hn
    dsimp only [radialScalar]
    linarith

def radialHomotopy : (ContinuousMap.id Punctured).Homotopy (includeUnit.comp normalize) where
  toFun tq := ⟨radialScalar tq.1 tq.2 • tq.2.val,
    smul_ne_zero (radialScalar_pos _ _).ne' tq.2.property⟩
  continuous_toFun := by
    have hs : Continuous (fun tq : unitInterval × Punctured => radialScalar tq.1 tq.2) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_fst).mul
          ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
            (fun tq => norm_ne_zero_iff.mpr tq.2.property)))
    exact (hs.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_zero_left q := Subtype.ext (by simp [radialScalar])
  map_one_left q := Subtype.ext (by simp [radialScalar, includeUnit, normalize])

theorem radial_homotopic :
    (ContinuousMap.id Punctured).Homotopic (includeUnit.comp normalize) := ⟨radialHomotopy⟩

theorem twelfthPower_nullhomotopic {X : Type*} [TopologicalSpace X]
    (e : StandardSphere ≃ₕ X) (hexp : SphereExponentTwelve) (g : C(X, Punctured)) :
    ((quaternionPower 12).comp g).Nullhomotopic := by
  have hr := (ContinuousMap.Homotopic.refl (quaternionPower 12)).comp
    (radial_homotopic.comp (ContinuousMap.Homotopic.refl g))
  have he : (quaternionPower 12).comp ((includeUnit.comp normalize).comp g) =
      includeUnit.comp ((normalize.comp g) ^ 12) := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [ContinuousMap.id_comp, he] at hr
  obtain ⟨u, hu⟩ :=
    (source_twelfth_power_nullhomotopic e hexp (normalize.comp g)).comp_right includeUnit
  exact ⟨u, hr.trans hu⟩

end Wikipedia.HopfProblem.QuaternionCoordinatePowers

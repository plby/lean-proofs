import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Algebra
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Homotopy
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleLift

/-!
# Displacement under a circle reparametrization

Straight interpolation between two real parameters with the same integral
endpoint increment gives a free homotopy of closed circle paths.  Hence a
global lift with period increment `1` preserves displacement, and one with
period increment `-1` reverses its sign.  The interpolation argument does not
need the lift to be monotone.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

open CircleDegree

/-- Traverse the domain circle once in the positive direction. -/
def circleTrace (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) :
    C(I, AddCircle (1 : ℝ)) := F.comp onceAround

@[simp] theorem circleTrace_apply
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) (t : I) :
    circleTrace F t = F ((t : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- Traverse a circle map using a continuous real parameter. -/
def parameterTrace (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)))
    (u : C(I, ℝ)) : C(I, AddCircle (1 : ℝ)) :=
  F.comp ⟨fun t => (u t : AddCircle (1 : ℝ)), cover.continuous.comp u.continuous⟩

@[simp] theorem parameterTrace_apply
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) (u : C(I, ℝ)) (t : I) :
    parameterTrace F u t = F (u t : AddCircle (1 : ℝ)) := rfl

/-- Linear interpolation between real parameters, projected to the circle. -/
def parameterHomotopy (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)))
    (u v : C(I, ℝ)) :
    ContinuousMap.Homotopy (parameterTrace F u) (parameterTrace F v) where
  toFun p := F (((1 - (p.1 : ℝ)) * u p.2 + (p.1 : ℝ) * v p.2 : ℝ) :
    AddCircle (1 : ℝ))
  continuous_toFun := F.continuous.comp (cover.continuous.comp
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (u.continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (v.continuous.comp continuous_snd))))
  map_zero_left t := by
    change F (((1 - (0 : ℝ)) * u t + 0 * v t : ℝ) : AddCircle (1 : ℝ)) = _
    simp only [sub_zero, one_mul, zero_mul, add_zero, parameterTrace_apply]
  map_one_left t := by
    change F (((1 - (1 : ℝ)) * u t + 1 * v t : ℝ) : AddCircle (1 : ℝ)) = _
    simp only [sub_self, zero_mul, one_mul, zero_add, parameterTrace_apply]

/-- Equal integral endpoint increments keep every interpolated path closed. -/
theorem parameterHomotopy_closed
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) (u v : C(I, ℝ))
    {d : ℝ} (hd : (d : AddCircle (1 : ℝ)) = 0)
    (hu : u 1 = u 0 + d) (hv : v 1 = v 0 + d) (s : I) :
    parameterHomotopy F u v (s, 1) = parameterHomotopy F u v (s, 0) := by
  apply congrArg F
  change (((1 - (s : ℝ)) * u 1 + (s : ℝ) * v 1 : ℝ) : AddCircle (1 : ℝ)) =
    (((1 - (s : ℝ)) * u 0 + (s : ℝ) * v 0 : ℝ) : AddCircle (1 : ℝ))
  have heq : (1 - (s : ℝ)) * u 1 + (s : ℝ) * v 1 =
      ((1 - (s : ℝ)) * u 0 + (s : ℝ) * v 0) + d := by
    rw [hu, hv]
    ring
  rw [heq, AddCircle.coe_add, hd, add_zero]

/-- Displacement depends only on the integral endpoint increment of the real
parameter, even when its starting point changes. -/
theorem displacement_parameterTrace_eq
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) (u v : C(I, ℝ))
    {d : ℝ} (hd : (d : AddCircle (1 : ℝ)) = 0)
    (hu : u 1 = u 0 + d) (hv : v 1 = v 0 + d) :
    displacement (parameterTrace F u) = displacement (parameterTrace F v) :=
  displacement_eq_of_homotopy (parameterHomotopy F u v)
    (parameterHomotopy_closed F u v hd hu hv)

/-- A real parameter advancing once gives the usual trace displacement. -/
theorem displacement_parameterTrace_of_positive_increment
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) (u : C(I, ℝ))
    (hu : u 1 = u 0 + 1) :
    displacement (parameterTrace F u) = displacement (circleTrace F) := by
  let v : C(I, ℝ) := ⟨fun t => (t : ℝ), continuous_subtype_val⟩
  have hv : v 1 = v 0 + 1 := by simp [v]
  exact displacement_parameterTrace_eq F u v (AddCircle.coe_period 1) hu hv

/-- A real parameter retreating once gives the negative trace displacement. -/
theorem displacement_parameterTrace_of_negative_increment
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ))) (u : C(I, ℝ))
    (hu : u 1 = u 0 - 1) :
    displacement (parameterTrace F u) = -displacement (circleTrace F) := by
  let v : C(I, ℝ) :=
    ⟨fun t => 1 - (t : ℝ), continuous_const.sub continuous_subtype_val⟩
  have hd : ((-1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_neg, AddCircle.coe_period, neg_zero]
  have hu' : u 1 = u 0 + (-1 : ℝ) := by simpa only [sub_eq_add_neg] using hu
  have hv : v 1 = v 0 + (-1 : ℝ) := by simp [v]
  have hrev : parameterTrace F v = reverse (circleTrace F) := by
    ext t
    simp only [parameterTrace_apply, reverse_apply, circleTrace_apply, coe_symm_eq]
    rfl
  rw [displacement_parameterTrace_eq F u v hd hu' hv, hrev, displacement_reverse]

/-- A positive unit-period real lift preserves the displacement of every
continuous circle-valued map.  No monotonicity hypothesis is used. -/
theorem displacement_trace_comp_of_positive_lift
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)))
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) {φ : ℝ → ℝ}
    (hφ : Continuous φ)
    (hlift : ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    (hperiod : ∀ t : ℝ, φ (t + 1) = φ t + 1) :
    displacement (circleTrace (F.comp (e : C(_, _)))) =
      displacement (circleTrace F) := by
  let u : C(I, ℝ) := ⟨fun t => φ t, hφ.comp continuous_subtype_val⟩
  have htrace : circleTrace (F.comp (e : C(_, _))) = parameterTrace F u := by
    ext t
    exact congrArg F (hlift t).symm
  rw [htrace]
  apply displacement_parameterTrace_of_positive_increment
  simpa [u] using hperiod 0

/-- A negative unit-period real lift reverses the displacement of every
continuous circle-valued map.  No monotonicity hypothesis is used. -/
theorem displacement_trace_comp_of_negative_lift
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)))
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) {φ : ℝ → ℝ}
    (hφ : Continuous φ)
    (hlift : ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    (hperiod : ∀ t : ℝ, φ (t + 1) = φ t - 1) :
    displacement (circleTrace (F.comp (e : C(_, _)))) =
      -displacement (circleTrace F) := by
  let u : C(I, ℝ) := ⟨fun t => φ t, hφ.comp continuous_subtype_val⟩
  have htrace : circleTrace (F.comp (e : C(_, _))) = parameterTrace F u := by
    ext t
    exact congrArg F (hlift t).symm
  rw [htrace]
  apply displacement_parameterTrace_of_negative_increment
  simpa [u] using hperiod 0

/-- Preserving a nonzero trace displacement forces an increasing real lift of
the circle homeomorphism. -/
theorem exists_increasing_lift_of_displacement_eq
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)))
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hne : displacement (circleTrace F) ≠ 0)
    (heq : displacement (circleTrace (F.comp (e : C(_, _)))) =
      displacement (circleTrace F)) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ))) ∧
      StrictMono φ ∧ ∀ t : ℝ, φ (t + 1) = φ t + 1 := by
  obtain ⟨φ, hφ, hlift, hpos | hneg⟩ := exists_monotone_lift e
  · exact ⟨φ, hφ, hlift, hpos⟩
  · have hrev := displacement_trace_comp_of_negative_lift F e hφ hlift hneg.2
    exact False.elim (hne (by linarith))

/-- The same nonzero-displacement criterion supplies a real homeomorphism
lift, with increasing orientation and its positive unit-period law. -/
theorem exists_increasing_homeomorph_lift_of_displacement_eq
    (F : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)))
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hne : displacement (circleTrace F) ≠ 0)
    (heq : displacement (circleTrace (F.comp (e : C(_, _)))) =
      displacement (circleTrace F)) :
    ∃ G : ℝ ≃ₜ ℝ,
      (∀ t : ℝ, (G t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ))) ∧
      StrictMono G ∧ ∀ t : ℝ, G (t + 1) = G t + 1 := by
  obtain ⟨G, hlift, hpos | hneg⟩ := exists_monotone_homeomorph_lift e
  · exact ⟨G, hlift, hpos⟩
  · have hrev := displacement_trace_comp_of_negative_lift F e G.continuous hlift hneg.2
    exact False.elim (hne (by linarith))

end

end Puzzling139335.CentralRotation.BoundaryOrientation

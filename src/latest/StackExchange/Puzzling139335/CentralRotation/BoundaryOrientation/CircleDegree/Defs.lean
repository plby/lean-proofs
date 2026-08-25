import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.Linarith

/-!
# Lift displacement of paths on the circle

The displacement of a path on `ℝ / ℤ` is the difference between the final and
initial values of any continuous real lift.  The choice in `pathLift` only
constructs a lift; `displacement_eq_sub_of_lift` removes that choice from every
subsequent calculation.
-/

noncomputable section

namespace Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

open Set unitInterval

abbrev Circle := AddCircle (1 : ℝ)

theorem cover : IsCoveringMap ((↑) : ℝ → Circle) := AddCircle.isCoveringMap_coe 1

/-- A representative of the starting point, used only to construct a path lift. -/
def baseLift (γ : C(I, Circle)) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (γ 0)).1

@[simp] theorem coe_baseLift (γ : C(I, Circle)) : (baseLift γ : Circle) = γ 0 :=
  AddCircle.coe_equivIco

/-- A continuous lift of a circle-valued path. -/
def pathLift (γ : C(I, Circle)) : C(I, ℝ) :=
  cover.liftPath γ (baseLift γ) (coe_baseLift γ).symm

@[simp] theorem coe_pathLift (γ : C(I, Circle)) (t : I) :
    (pathLift γ t : Circle) = γ t :=
  congr_fun (cover.liftPath_lifts γ (baseLift γ) (coe_baseLift γ).symm) t

@[simp] theorem pathLift_zero (γ : C(I, Circle)) : pathLift γ 0 = baseLift γ :=
  cover.liftPath_zero γ (baseLift γ) (coe_baseLift γ).symm

/-- Endpoint displacement in the universal covering of the circle. -/
def displacement (γ : C(I, Circle)) : ℝ := pathLift γ 1 - pathLift γ 0

/-- Two continuous lifts of the same path differ by a constant. -/
theorem lifts_sub_eq (γ : C(I, Circle)) (Γ Δ : C(I, ℝ))
    (hΓ : ∀ t, (Γ t : Circle) = γ t) (hΔ : ∀ t, (Δ t : Circle) = γ t)
    (s t : I) : Γ s - Δ s = Γ t - Δ t := by
  apply cover.const_of_comp (Γ.continuous.sub Δ.continuous) _ s t
  intro u v
  change ((Γ u - Δ u : ℝ) : Circle) = ((Γ v - Δ v : ℝ) : Circle)
  simp only [AddCircle.coe_sub, hΓ, hΔ, sub_self]

/-- Displacement is independent of the choice of the initial lift. -/
theorem displacement_eq_sub_of_lift (γ : C(I, Circle)) (Γ : C(I, ℝ))
    (hΓ : ∀ t, (Γ t : Circle) = γ t) :
    displacement γ = Γ 1 - Γ 0 := by
  have h := lifts_sub_eq γ Γ (pathLift γ) hΓ (coe_pathLift γ) 1 0
  dsimp only [displacement]
  linarith

/-- The same displacement formula for a lift with any prescribed starting point. -/
theorem displacement_eq_liftPath (γ : C(I, Circle)) (b : ℝ)
    (hb : γ 0 = (b : Circle)) :
    displacement γ = cover.liftPath γ b hb 1 - b := by
  rw [displacement_eq_sub_of_lift γ (cover.liftPath γ b hb)
    (fun t => congr_fun (cover.liftPath_lifts γ b hb) t)]
  rw [cover.liftPath_zero]

/-- A closed path has integral displacement. -/
theorem displacement_eq_int (γ : C(I, Circle)) (hclosed : γ 1 = γ 0) :
    ∃ n : ℤ, displacement γ = n := by
  have hz : (displacement γ : Circle) = 0 := by
    simp only [displacement, AddCircle.coe_sub, coe_pathLift, hclosed, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact ⟨n, by simpa using hn.symm⟩

@[simp] theorem displacement_const (x : Circle) :
    displacement (ContinuousMap.const I x) = 0 := by
  let Γ : C(I, ℝ) := ContinuousMap.const I (baseLift (ContinuousMap.const I x))
  rw [displacement_eq_sub_of_lift _ Γ (by intro t; exact coe_baseLift _)]
  exact sub_self _

/-- The positively oriented once-around path. -/
def onceAround : C(I, Circle) :=
  ⟨fun t => ((t : ℝ) : Circle), cover.continuous.comp continuous_subtype_val⟩

@[simp] theorem onceAround_apply (t : I) : onceAround t = ((t : ℝ) : Circle) := rfl

@[simp] theorem displacement_onceAround : displacement onceAround = 1 := by
  rw [displacement_eq_sub_of_lift onceAround
    ⟨fun t => (t : ℝ), continuous_subtype_val⟩ (by intro t; rfl)]
  norm_num

end Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

end

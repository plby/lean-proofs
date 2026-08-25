import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Maps
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleLift.Existence

/-!
# Multiplication of displacement under composition

A continuous real lift of a circle map has constant increment over each unit
interval.  That increment is its degree.  Integral increments then compute the
effect of the circle map on every closed path.
-/

noncomputable section

namespace Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

open unitInterval

/-- A unit increment law determines the increment over every integral shift. -/
theorem lift_add_int_of_period {φ : ℝ → ℝ} {k : ℝ}
    (hperiod : ∀ t, φ (t + 1) = φ t + k) (t : ℝ) (n : ℤ) :
    φ (t + n) = φ t + k * n := by
  have hp : Function.Periodic (fun s => φ s - k * s) 1 := by
    intro s
    change φ (s + 1) - k * (s + 1) = φ s - k * s
    rw [hperiod]
    ring
  have hi := hp.int_mul n t
  change φ (t + (n : ℝ) * 1) - k * (t + (n : ℝ) * 1) = φ t - k * t at hi
  simp only [mul_one, mul_add] at hi
  linarith

/-- The increment of a global lift is the degree of the circle map. -/
theorem lift_add_one_eq_degree (f : C(Circle, Circle)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = f (t : Circle))
    (t : ℝ) : φ (t + 1) = φ t + degree f := by
  have he (u v : ℝ) :
      ((φ (u + 1) - φ u : ℝ) : Circle) = ((φ (v + 1) - φ v : ℝ) : Circle) := by
    simp only [AddCircle.coe_sub, hlift, AddCircle.coe_add, AddCircle.coe_period,
      add_zero, sub_self]
  have hd := cover.const_of_comp
    ((hφ.comp (continuous_id.add continuous_const)).sub hφ) he t 0
  change φ (t + 1) - φ t = φ (0 + 1) - φ 0 at hd
  rw [zero_add] at hd
  rw [degree_eq_sub_of_lift f hφ hlift]
  linarith

/-- A circle map with lift increment `k` multiplies every closed path's
displacement by `k`. -/
theorem displacement_comp_of_lift_period (f : C(Circle, Circle)) {φ : ℝ → ℝ} {k : ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = f (t : Circle))
    (hperiod : ∀ t, φ (t + 1) = φ t + k) (γ : C(I, Circle))
    (hclosed : γ 1 = γ 0) : displacement (f.comp γ) = k * displacement γ := by
  let Γ : C(I, ℝ) := ⟨fun t => φ (pathLift γ t), hφ.comp (pathLift γ).continuous⟩
  have hΓ (t : I) : (Γ t : Circle) = (f.comp γ) t := by
    change (φ (pathLift γ t) : Circle) = f (γ t)
    rw [hlift, coe_pathLift]
  rw [displacement_eq_sub_of_lift (f.comp γ) Γ hΓ]
  obtain ⟨n, hn⟩ := displacement_eq_int γ hclosed
  have hend : pathLift γ 1 = pathLift γ 0 + n := by
    change pathLift γ 1 - pathLift γ 0 = (n : ℝ) at hn
    linarith
  change φ (pathLift γ 1) - φ (pathLift γ 0) = k * displacement γ
  rw [hend, lift_add_int_of_period hperiod, hn]
  ring

/-- Composition with a circle map multiplies the displacement of a closed
path by its degree, as computed from any global real lift. -/
theorem displacement_comp_of_lift (f : C(Circle, Circle)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = f (t : Circle))
    (γ : C(I, Circle)) (hclosed : γ 1 = γ 0) :
    displacement (f.comp γ) = degree f * displacement γ :=
  displacement_comp_of_lift_period f hφ hlift (lift_add_one_eq_degree f hφ hlift)
    γ hclosed

/-- Degrees multiply under composition when a global real lift of the outer
map is supplied. -/
theorem degree_comp_of_lift (f g : C(Circle, Circle)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = f (t : Circle)) :
    degree (f.comp g) = degree f * degree g := by
  change displacement (f.comp (g.comp onceAround)) = degree f * degree g
  apply displacement_comp_of_lift f hφ hlift
  change g ((1 : ℝ) : Circle) = g ((0 : ℝ) : Circle)
  rw [AddCircle.coe_period]
  rfl

/-- Every continuous circle map admits a global real lift after composing
with the quotient map from the real line. -/
theorem exists_global_lift (f : C(Circle, Circle)) :
    ∃ φ : C(ℝ, ℝ), ∀ t : ℝ, (φ t : Circle) = f (t : Circle) := by
  let F : C(ℝ, Circle) :=
    ⟨fun t => f (t : Circle), f.continuous.comp cover.continuous⟩
  obtain ⟨φ, _, hφ⟩ :=
    Puzzling139335.CentralRotation.BoundaryOrientation.exists_real_lift F 0
      (baseLift (f.comp onceAround)) (coe_baseLift (f.comp onceAround))
  exact ⟨φ, hφ⟩

/-- Composition by a continuous circle map multiplies a closed path's
displacement by the degree of that map. -/
theorem displacement_map (f : C(Circle, Circle)) (γ : C(I, Circle))
    (hclosed : γ 1 = γ 0) :
    displacement (f.comp γ) = degree f * displacement γ := by
  obtain ⟨φ, hφ⟩ := exists_global_lift f
  exact displacement_comp_of_lift f φ.continuous hφ γ hclosed

/-- Degrees of continuous circle maps multiply under composition. -/
theorem degree_comp (f g : C(Circle, Circle)) :
    degree (f.comp g) = degree f * degree g := by
  obtain ⟨φ, hφ⟩ := exists_global_lift f
  exact degree_comp_of_lift f g φ.continuous hφ

end Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

end

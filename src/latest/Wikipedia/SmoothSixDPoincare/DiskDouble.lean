import Wikipedia.SmoothSixDPoincare.RadialExtension
import Mathlib.Topology.Homeomorph.Quotient

/-!
# The quotient obtained by gluing two disks along their boundary

The relation below identifies the boundary point `z` in the left disk with
`e z` in the right disk. The radial extension untwists this quotient by an
actual homeomorphism. Neither a smooth extension nor a disk decomposition
of an arbitrary manifold is assumed to have been proved here.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.DiskDouble

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Disk := closedBall (0 : E) 1
abbrev Boundary := sphere (0 : E) 1

/-- The inclusion of the unit sphere into the closed unit disk. -/
def boundary (x : Boundary E) : Disk E := ⟨x, sphere_subset_closedBall x.property⟩

variable {E}

/-- Generating identifications for gluing the two closed disks by `e`. -/
def Rel (e : Boundary E ≃ₜ Boundary E) : Disk E ⊕ Disk E → Disk E ⊕ Disk E → Prop
  | .inl x, .inr y => ∃ z : Boundary E, x = boundary E z ∧ y = boundary E (e z)
  | _, _ => False

/-- The topological quotient of two genuine closed disks by the boundary identification. -/
abbrev Space (e : Boundary E ≃ₜ Boundary E) := Quot (Rel e)

/-- Change coordinates on the right disk using the inverse radial extension. -/
def untwist (e : Boundary E ≃ₜ Boundary E) : Disk E ⊕ Disk E ≃ₜ Disk E ⊕ Disk E :=
  (Homeomorph.refl (Disk E)).sumCongr (RadialExtension.closedBallHomeomorph e.symm)

theorem rel_untwist_iff (e : Boundary E ≃ₜ Boundary E) (x y : Disk E ⊕ Disk E) :
    Rel e x y ↔ Rel (Homeomorph.refl (Boundary E)) (untwist e x) (untwist e y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => rfl
    | inr y =>
      change (∃ z, x = boundary E z ∧ y = boundary E (e z)) ↔
        ∃ z, x = boundary E z ∧
          RadialExtension.closedBallHomeomorph e.symm y = boundary E z
      constructor
      · rintro ⟨z, rfl, rfl⟩
        refine ⟨z, rfl, ?_⟩
        simp [boundary]
      · rintro ⟨z, hx, hy⟩
        refine ⟨z, hx, ?_⟩
        apply (RadialExtension.closedBallHomeomorph e.symm).injective
        rw [hy]
        simp [boundary]
  | inr x =>
    cases y <;> rfl

/-- Any boundary twist gives the same topological double as identity gluing. -/
def homeomorphUntwisted (e : Boundary E ≃ₜ Boundary E) :
    Space e ≃ₜ Space (Homeomorph.refl (Boundary E)) :=
  Homeomorph.Quot.congr (untwist e) (rel_untwist_iff e)

end Wikipedia.SmoothSixDPoincare.DiskDouble

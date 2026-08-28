import Wikipedia.SmoothSixDPoincare.HemisphereSurjective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Two disks glued by any boundary homeomorphism give a topological sphere

This proves the complete terminal gluing step of the intended Smale argument.
It does not provide the geometric decomposition of an arbitrary smooth
homotopy six-sphere.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.DiskDouble

open Hemisphere

variable (n : ℕ)

def hemisphereMap : Ball n ⊕ Ball n → Sphere n :=
  Sum.elim (point false) (point true)

theorem continuous_hemisphereMap : Continuous (hemisphereMap n) :=
  continuous_sum_dom.mpr ⟨continuous_point false, continuous_point true⟩

theorem hemisphereMap_respects (x y : Ball n ⊕ Ball n)
    (h : Rel (Homeomorph.refl (Boundary (Ambient n))) x y) :
    hemisphereMap n x = hemisphereMap n y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y =>
      obtain ⟨z, rfl, rfl⟩ := h
      exact point_boundary z
  | inr x => cases y <;> exact h.elim

def sphereMap : Space (Homeomorph.refl (Boundary (Ambient n))) → Sphere n :=
  Quot.lift (hemisphereMap n) (hemisphereMap_respects n)

theorem continuous_sphereMap : Continuous (sphereMap n) :=
  continuous_quot_lift (hemisphereMap_respects n) (continuous_hemisphereMap n)

theorem sphereMap_injective : Function.Injective (sphereMap n) := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := point_injective false h
          subst y
          rfl
        | inr y =>
          exact Quot.sound ((point_false_eq_true_iff x y).mp h)
      | inr x =>
        cases y with
        | inl y =>
          exact (Quot.sound ((point_false_eq_true_iff y x).mp h.symm)).symm
        | inr y =>
          have hxy := point_injective true h
          subst y
          rfl

theorem sphereMap_surjective : Function.Surjective (sphereMap n) := by
  intro y
  obtain ⟨b, x, hx⟩ := point_jointly_surjective y
  cases b
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr x), hx⟩

/-- The identity double of the closed Euclidean `n`-disk is the standard `n`-sphere. -/
def homeomorphSphere : Space (Homeomorph.refl (Boundary (Ambient n))) ≃ₜ Sphere n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (sphereMap n) ⟨sphereMap_injective n, sphereMap_surjective n⟩)
    (continuous_sphereMap n)

/-- Arbitrary boundary gluing produces the standard sphere up to homeomorphism. -/
def twistedHomeomorphSphere (e : Boundary (Ambient n) ≃ₜ Boundary (Ambient n)) :
    Space e ≃ₜ Sphere n :=
  (homeomorphUntwisted e).trans (homeomorphSphere n)

end Wikipedia.SmoothSixDPoincare.DiskDouble

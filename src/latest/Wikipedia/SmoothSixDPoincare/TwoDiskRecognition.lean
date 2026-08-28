import Wikipedia.SmoothSixDPoincare.DoubleSphere

/-!
# Topological recognition from a genuine two-disk decomposition

The disks here are the actual Euclidean closed unit disks, with continuous
injective maps into the original manifold, exhaustive images, and exactly
the prescribed boundary overlap. The final geometric step of Smale's proof
must construct this data; no such construction is asserted in this file.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare

open DiskDouble Hemisphere

variable (n : ℕ) (M : Type*) [TopologicalSpace M]

/-- Concrete topological data for two closed disks covering a space. -/
structure TwoDiskDecomposition where
  boundaryEquiv : Boundary (Ambient n) ≃ₜ Boundary (Ambient n)
  left : C(Ball n, M)
  right : C(Ball n, M)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  covers : ∀ p : M, (∃ x, left x = p) ∨ ∃ y, right y = p
  overlap : ∀ x y, left x = right y ↔
    ∃ z : Boundary (Ambient n),
      x = boundary (Ambient n) z ∧ y = boundary (Ambient n) (boundaryEquiv z)

namespace TwoDiskDecomposition

variable {n M} (d : TwoDiskDecomposition n M)

def sumMap : Ball n ⊕ Ball n → M := Sum.elim d.left d.right

theorem continuous_sumMap : Continuous d.sumMap :=
  continuous_sum_dom.mpr ⟨d.left.continuous, d.right.continuous⟩

theorem sumMap_respects (x y : Ball n ⊕ Ball n) (h : DiskDouble.Rel d.boundaryEquiv x y) :
    d.sumMap x = d.sumMap y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y => exact (d.overlap x y).mpr h
  | inr x => cases y <;> exact h.elim

def quotientMap : DiskDouble.Space d.boundaryEquiv → M :=
  Quot.lift d.sumMap d.sumMap_respects

theorem continuous_quotientMap : Continuous d.quotientMap :=
  continuous_quot_lift d.sumMap_respects d.continuous_sumMap

theorem quotientMap_injective : Function.Injective d.quotientMap := by
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
          have hxy := d.left_injective h
          subst y
          rfl
        | inr y => exact Quot.sound ((d.overlap x y).mp h)
      | inr x =>
        cases y with
        | inl y => exact (Quot.sound ((d.overlap y x).mp h.symm)).symm
        | inr y =>
          have hxy := d.right_injective h
          subst y
          rfl

theorem quotientMap_surjective : Function.Surjective d.quotientMap := by
  intro p
  rcases d.covers p with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr y), hy⟩

/-- Identify the concrete covered space with its boundary-gluing quotient. -/
def quotientHomeomorph [T2Space M] : DiskDouble.Space d.boundaryEquiv ≃ₜ M :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective d.quotientMap ⟨d.quotientMap_injective, d.quotientMap_surjective⟩)
    d.continuous_quotientMap

/-- A genuine two-disk decomposition yields a homeomorphism to the standard sphere. -/
def homeomorphSphere [T2Space M] : M ≃ₜ Sphere n :=
  d.quotientHomeomorph.symm.trans (DiskDouble.twistedHomeomorphSphere n d.boundaryEquiv)

end TwoDiskDecomposition
end Wikipedia.SmoothSixDPoincare

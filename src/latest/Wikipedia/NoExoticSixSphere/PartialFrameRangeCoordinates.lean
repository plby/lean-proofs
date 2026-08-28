import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual partial-frame coordinates in an orthonormally trivialized subspace

If a partial frame lies in the range of an orthonormal frame, the adjoint of
that frame gives its unique isometric coordinates. Extraction and composition
are continuous in the original operator-norm topologies.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.RangeCoordinates

open GLOrthonormalization

variable {N n r : ℕ}

theorem adjoint_self (t : Space N n) (x : Vector n) : t.val.adjoint (t.val x) = x := by
  have h := (t.val.norm_map_iff_adjoint_comp_self).mp t.property
  exact congrArg (fun A : Vector n →L[ℝ] Vector n ↦ A x) h

theorem self_adjoint (t : Space N n) (x : Vector N) (hx : x ∈ t.val.range) :
    t.val (t.val.adjoint x) = x := by
  obtain ⟨y, rfl⟩ := hx
  change t.val (t.val.adjoint (t.val y)) = t.val y
  rw [adjoint_self]

theorem range_comp_le (t : Space N n) (q : Space n r) :
    (Stiefel.comp t q).val.range ≤ t.val.range := by
  rintro x ⟨y, rfl⟩
  exact ⟨q.val y, rfl⟩

def extract (t : Space N n) (a : Space N r) (ha : a.val.range ≤ t.val.range) : Space n r :=
  ⟨t.val.adjoint.comp a.val, fun x ↦ by
    change ‖t.val.adjoint (a.val x)‖ = ‖x‖
    rw [← t.property (t.val.adjoint (a.val x)), self_adjoint t (a.val x) (ha ⟨x, rfl⟩)]
    exact a.property x⟩

theorem extract_apply (t : Space N n) (a : Space N r) (ha : a.val.range ≤ t.val.range)
    (x : Vector r) : (extract t a ha).val x = t.val.adjoint (a.val x) := rfl

theorem comp_extract (t : Space N n) (a : Space N r) (ha : a.val.range ≤ t.val.range) :
    Stiefel.comp t (extract t a ha) = a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact self_adjoint t (a.val x) (ha ⟨x, rfl⟩)

theorem extract_comp (t : Space N n) (q : Space n r) :
    extract t (Stiefel.comp t q) (range_comp_le t q) = q := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact adjoint_self t (q.val x)

variable {X : Type*} [TopologicalSpace X]

theorem continuous_extract (t : X → Space N n) (a : X → Space N r)
    (ht : Continuous t) (ha : Continuous a) (hr : ∀ x, (a x).val.range ≤ (t x).val.range) :
    Continuous (fun x ↦ extract (t x) (a x) (hr x)) :=
  ((ContinuousLinearMap.adjoint.continuous.comp (continuous_subtype_val.comp ht)).clm_comp
    (continuous_subtype_val.comp ha)).subtype_mk _

def map (t : C(X, Space N n)) (a : C(X, Space N r))
    (hr : ∀ x, (a x).val.range ≤ (t x).val.range) : C(X, Space n r) :=
  ⟨fun x ↦ extract (t x) (a x) (hr x), continuous_extract t a t.continuous a.continuous hr⟩

end NoExoticSixSphere.Stiefel.RangeCoordinates

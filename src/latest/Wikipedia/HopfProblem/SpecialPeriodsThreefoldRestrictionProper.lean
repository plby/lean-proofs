import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRestrictionBasic
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Proper local projections on smaller base patches

Restricting a proper map into its original base patch to a smaller open
patch is actual base change.  The nested subtype of the original patch
is canonically homeomorphic to the smaller patch, while its inverse
image is definitionally the literal `restrictedPiece`.

Surjectivity and nonemptiness are likewise proved on the actual fibres.
Properness of the map into the entire ambient base is not assumed.
-/

noncomputable section

open Function Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Restriction

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]

/-- The smaller patch as a subset of the original patch is homeomorphic
to the same smaller patch with its native topology from the ambient base. -/
def smallerPatchHomeomorph (U V : Opens B) (hVU : V ≤ U) :
    (Subtype.val ⁻¹' (V : Set B) : Set U) ≃ₜ V where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hVU x.property⟩, x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := Subtype.ext rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The literal local projection is exactly the base-changed map,
followed by the canonical identification of its target with the smaller patch. -/
theorem localProjection_eq_basechange (p : C(X, B)) (U : Opens B)
    (hpU : ∀ x, p x ∈ U) (V : Opens B) (hVU : V ≤ U) :
    (localProjection p V : restrictedPiece p V → V) =
      smallerPatchHomeomorph U V hVU ∘
        (Subtype.val ⁻¹' (V : Set B) : Set U).restrictPreimage (patchProjection p U hpU) :=
  rfl

/-- Properness into the original patch is preserved when the domain and
base are restricted to any smaller open patch. -/
theorem localProjection_proper_of_le (p : C(X, B)) (U : Opens B)
    (hpU : ∀ x, p x ∈ U) (V : Opens B) (hVU : V ≤ U)
    (hproper : IsProperMap (patchProjection p U hpU)) :
    IsProperMap (localProjection p V) := by
  rw [localProjection_eq_basechange p U hpU V hVU]
  exact (smallerPatchHomeomorph U V hVU).isProperMap.comp
    (hproper.restrictPreimage (Subtype.val ⁻¹' (V : Set B) : Set U))

/-- Surjectivity onto the original patch restricts to surjectivity onto
the smaller patch, with the original point in each actual fibre. -/
theorem localProjection_surjective_of_le (p : C(X, B)) (U : Opens B)
    (hpU : ∀ x, p x ∈ U) (V : Opens B) (hVU : V ≤ U)
    (hsurj : Surjective (patchProjection p U hpU)) :
    Surjective (localProjection p V) := by
  intro y
  obtain ⟨x, hx⟩ := hsurj ⟨y.val, hVU y.property⟩
  have he : p x = y.val := congrArg (fun u : U => (u : B)) hx
  have hxV : x ∈ restrictedPiece p V := by
    change p x ∈ V
    rw [he]
    exact y.property
  exact ⟨⟨x, hxV⟩, Subtype.ext he⟩

/-- A nonempty smaller patch has a nonempty actual inverse image whenever
the original local projection is surjective. -/
theorem restrictedPiece_nonempty_of_surjective_of_le (p : C(X, B)) (U : Opens B)
    (hpU : ∀ x, p x ∈ U) (V : Opens B) (hVU : V ≤ U)
    (hsurj : Surjective (patchProjection p U hpU)) [Nonempty V] :
    Nonempty (restrictedPiece p V) := by
  obtain ⟨y⟩ := ‹Nonempty V›
  obtain ⟨x, _⟩ := localProjection_surjective_of_le p U hpU V hVU hsurj y
  exact ⟨x⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Restriction

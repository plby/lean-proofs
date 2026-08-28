import Wikipedia.NoExoticSixSphere.CompactClosedQuotient
import Mathlib.Topology.ContinuousMap.Basic

/-!
# An actual adjunction space with a surjective attaching map

The underlying set keeps the complement of the embedded attaching
domain and replaces that domain by the given target. Its topology is
the quotient topology of the original space. Exact fiber formulas are
proved before any separation or homotopy assertion.
-/

noncomputable section

universe u

open Set Topology

namespace NoExoticSixSphere.CompactAdjunction

variable (A X Y : Type u) [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

structure Data where
  embedding : C(A, X)
  closedEmbedding : IsClosedEmbedding embedding
  attaching : C(A, Y)
  attaching_surjective : Function.Surjective attaching

variable {A X Y}

def Space (D : Data A X Y) := {x : X // x ∉ Set.range D.embedding} ⊕ Y

variable (D : Data A X Y)

def projection (x : X) : Space D := by
  classical
  exact if hx : x ∈ Set.range D.embedding then
    Sum.inr (D.attaching (D.closedEmbedding.isEmbedding.toHomeomorph.symm ⟨x, hx⟩))
  else Sum.inl ⟨x, hx⟩

theorem projection_embedding (a : A) : projection D (D.embedding a) = Sum.inr (D.attaching a) := by
  classical
  have hx : D.embedding a ∈ Set.range D.embedding := ⟨a, rfl⟩
  dsimp only [projection, Space]
  rw [dif_pos hx]
  exact congrArg Sum.inr (congrArg D.attaching
    (D.closedEmbedding.isEmbedding.toHomeomorph.symm_apply_apply a))

theorem projection_of_notMem (x : X) (hx : x ∉ Set.range D.embedding) :
    projection D x = Sum.inl ⟨x, hx⟩ := by
  classical
  exact dif_neg hx

theorem projection_eq_inr_iff (x : X) (y : Y) :
    projection D x = Sum.inr y ↔ ∃ a, D.embedding a = x ∧ D.attaching a = y := by
  constructor
  · intro h
    by_cases hx : x ∈ Set.range D.embedding
    · obtain ⟨a, rfl⟩ := hx
      rw [projection_embedding] at h
      exact ⟨a, rfl, Sum.inr.inj h⟩
    · rw [projection_of_notMem D x hx] at h
      cases h
  · rintro ⟨a, rfl, rfl⟩
    exact projection_embedding D a

theorem projection_eq_inl_iff (x : X) (z : {x : X // x ∉ Set.range D.embedding}) :
    projection D x = Sum.inl z ↔ x = z.val := by
  constructor
  · intro h
    by_cases hx : x ∈ Set.range D.embedding
    · obtain ⟨a, rfl⟩ := hx
      rw [projection_embedding] at h
      cases h
    · rw [projection_of_notMem D x hx] at h
      exact congrArg Subtype.val (Sum.inl.inj h)
  · rintro rfl
    exact projection_of_notMem D z.val z.property

theorem projection_eq_iff (x y : X) : projection D x = projection D y ↔
    x = y ∨ ∃ a b, D.embedding a = x ∧ D.embedding b = y ∧ D.attaching a = D.attaching b := by
  constructor
  · intro h
    by_cases hx : x ∈ Set.range D.embedding
    · obtain ⟨a, rfl⟩ := hx
      rw [projection_embedding] at h
      obtain ⟨b, hb, hf⟩ := (projection_eq_inr_iff D y (D.attaching a)).mp h.symm
      exact Or.inr ⟨a, b, rfl, hb, hf.symm⟩
    · rw [projection_of_notMem D x hx] at h
      exact Or.inl ((projection_eq_inl_iff D y ⟨x, hx⟩).mp h.symm).symm
  · rintro (rfl | ⟨a, b, rfl, rfl, hab⟩)
    · rfl
    · rw [projection_embedding, projection_embedding, hab]

theorem projection_surjective : Function.Surjective (projection D) := by
  intro p
  cases p with
  | inl x => exact ⟨x.val, projection_of_notMem D x.val x.property⟩
  | inr y =>
      obtain ⟨a, rfl⟩ := D.attaching_surjective y
      exact ⟨D.embedding a, projection_embedding D a⟩

instance : TopologicalSpace (Space D) := TopologicalSpace.coinduced (projection D) inferInstance

theorem projection_isQuotientMap : IsQuotientMap (projection D) :=
  ⟨⟨rfl⟩, projection_surjective D⟩

def quotientMap : C(X, Space D) := ⟨projection D, (projection_isQuotientMap D).continuous⟩

end NoExoticSixSphere.CompactAdjunction

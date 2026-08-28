import Wikipedia.NoExoticSixSphere.CollapsedSubspace
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Collapsing a compact subset of a Hausdorff space

The literal quotient map is closed when the collapsed set is closed.
For a compact collapsed set its fibers are compact, so it is proper;
the product quotient then detects the closed diagonal. The whole source
space need not be compact.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.CollapsedSubspace

variable {X : Type*} [TopologicalSpace X] (A : Set X)

theorem isClosedMap (hA : IsClosed A) : IsClosedMap (quotientMap A) := by
  intro C hC
  apply (isQuotientMap A).isClosed_preimage.mp
  by_cases h : (C ∩ A).Nonempty
  · obtain ⟨a, haC, haA⟩ := h
    have he : quotientMap A ⁻¹' (quotientMap A '' C) = C ∪ A := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        rcases (quotientMap_eq_iff A y x).mp he with rfl | ⟨_, hx⟩
        · exact Or.inl hy
        · exact Or.inr hx
      · rintro (hx | hx)
        · exact ⟨x, hx, rfl⟩
        · exact ⟨a, haC, (quotientMap_eq_iff A a x).mpr (Or.inr ⟨haA, hx⟩)⟩
    rw [he]
    exact hC.union hA
  · have he : quotientMap A ⁻¹' (quotientMap A '' C) = C := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        rcases (quotientMap_eq_iff A y x).mp he with rfl | ⟨hyA, _⟩
        · exact hy
        · exact False.elim (h ⟨y, hy, hyA⟩)
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [he]
    exact hC

theorem fiber_eq (x : X) [Decidable (x ∈ A)] :
    quotientMap A ⁻¹' {quotientMap A x} = if x ∈ A then A else {x} := by
  classical
  by_cases hx : x ∈ A
  · rw [if_pos hx]
    ext y
    change quotientMap A y = quotientMap A x ↔ y ∈ A
    rw [quotientMap_eq_iff]
    exact ⟨fun h ↦ h.elim (fun he ↦ he ▸ hx) And.left, fun hy ↦ Or.inr ⟨hy, hx⟩⟩
  · rw [if_neg hx]
    ext y
    change quotientMap A y = quotientMap A x ↔ y = x
    rw [quotientMap_eq_iff]
    exact ⟨fun h ↦ h.elim id (fun h ↦ False.elim (hx h.2)), Or.inl⟩

variable [T2Space X]

theorem isProperMap (hA : IsCompact A) : IsProperMap (quotientMap A) := by
  classical
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨(quotientMap A).continuous, isClosedMap A hA.isClosed, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := (isQuotientMap A).surjective y
  rw [fiber_eq]
  split_ifs
  · exact hA
  · exact isCompact_singleton

theorem t2Space (hA : IsCompact A) : T2Space (Space A) := by
  have hr : IsClosed {p : X × X | quotientMap A p.1 = quotientMap A p.2} := by
    have he : {p : X × X | quotientMap A p.1 = quotientMap A p.2} =
        {p : X × X | p.1 = p.2} ∪ A ×ˢ A := by
      ext p
      exact quotientMap_eq_iff A p.1 p.2
    rw [he]
    exact (isClosed_eq continuous_fst continuous_snd).union (hA.isClosed.prod hA.isClosed)
  have hp := (isProperMap A hA).prodMap (isProperMap A hA)
  have hs : Function.Surjective (Prod.map (quotientMap A) (quotientMap A)) := by
    rintro ⟨y, z⟩
    obtain ⟨x, rfl⟩ := (isQuotientMap A).surjective y
    obtain ⟨w, rfl⟩ := (isQuotientMap A).surjective z
    exact ⟨(x, w), rfl⟩
  have hq : IsQuotientMap (Prod.map (quotientMap A) (quotientMap A)) :=
    hp.isClosedMap.isQuotientMap hp.continuous hs
  apply t2_iff_isClosed_diagonal.mpr
  exact hq.isClosed_preimage.mp hr

end NoExoticSixSphere.CollapsedSubspace

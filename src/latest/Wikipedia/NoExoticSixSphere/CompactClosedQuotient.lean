import Mathlib.Topology.Maps.Proper.Basic

/-!
# A compact Hausdorff quotient with a closed equality relation is Hausdorff

Closedness of the relation makes saturations of closed sets compact.
Consequently the quotient is closed and proper. Its square is then a
quotient map, which detects closedness of the diagonal in the target.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.CompactClosedQuotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] (f : X → Y) (hq : IsQuotientMap f)
    (hr : IsClosed {p : X × X | f p.1 = f p.2})

omit [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] in
theorem saturation_eq (C : Set X) :
    f ⁻¹' (f '' C) = Prod.fst '' ({p : X × X | f p.1 = f p.2} ∩ Prod.snd ⁻¹' C) := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨(x, y), ⟨he.symm, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨he, hy⟩, rfl⟩
    exact ⟨y, hy, he.symm⟩

include hr in
omit [TopologicalSpace Y] in
theorem saturation_isClosed (C : Set X) (hC : IsClosed C) : IsClosed (f ⁻¹' (f '' C)) := by
  rw [saturation_eq]
  exact ((hr.inter (hC.preimage continuous_snd)).isCompact.image continuous_fst).isClosed

include hq hr in
theorem isClosedMap : IsClosedMap f := by
  intro C hC
  exact hq.isClosed_preimage.mp (saturation_isClosed f hr C hC)

include hq hr in
theorem isProperMap : IsProperMap f := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hq.continuous, isClosedMap f hq hr, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hq.surjective y
  have he : f ⁻¹' {f x} = (fun z : X ↦ (z, x)) ⁻¹' {p : X × X | f p.1 = f p.2} := by
    ext z
    rfl
  rw [he]
  exact (hr.preimage (continuous_id.prodMk continuous_const)).isCompact

include hq hr in
theorem t2Space : T2Space Y := by
  have hp := (isProperMap f hq hr).prodMap (isProperMap f hq hr)
  have hs : Function.Surjective (Prod.map f f) := by
    rintro ⟨y, z⟩
    obtain ⟨x, rfl⟩ := hq.surjective y
    obtain ⟨w, rfl⟩ := hq.surjective z
    exact ⟨(x, w), rfl⟩
  have hqq : IsQuotientMap (Prod.map f f) :=
    hp.isClosedMap.isQuotientMap hp.continuous hs
  apply t2_iff_isClosed_diagonal.mpr
  apply hqq.isClosed_preimage.mp
  exact hr

end NoExoticSixSphere.CompactClosedQuotient

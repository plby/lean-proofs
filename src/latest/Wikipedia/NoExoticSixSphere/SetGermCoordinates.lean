import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local identity coordinates between subsets with the same germ

The original subtype topologies are retained. On an open set where two
subsets agree, the identity on the ambient space is a genuine open partial
homeomorphism between those subtypes.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.SetGerm

variable {X : Type*} [TopologicalSpace X] (S T N : Set X)
  (he : ∀ x ∈ N, x ∈ S ↔ x ∈ T)

def convert (t₀ : T) (s : S) : T := by
  classical
  exact if hs : s.val ∈ N then ⟨s.val, (he s.val hs).mp s.property⟩ else t₀

omit [TopologicalSpace X] in
theorem convert_val (t₀ : T) {s : S} (hs : s.val ∈ N) :
    (convert S T N he t₀ s).val = s.val := by
  simp only [convert, dif_pos hs]

theorem continuousOn_convert (t₀ : T) :
    ContinuousOn (convert S T N he t₀) (Subtype.val ⁻¹' N) := by
  apply IsInducing.subtypeVal.continuousOn_iff.mpr
  apply continuous_subtype_val.continuousOn.congr
  intro s hs
  exact convert_val S T N he t₀ hs

def coordinates (hN : IsOpen N) (s₀ : S) (t₀ : T) : OpenPartialHomeomorph S T where
  toFun := convert S T N he t₀
  invFun := convert T S N (fun x hx ↦ (he x hx).symm) s₀
  source := Subtype.val ⁻¹' N
  target := Subtype.val ⁻¹' N
  map_source' s hs := by
    change (convert S T N he t₀ s).val ∈ N
    rw [convert_val S T N he t₀ hs]
    exact hs
  map_target' t ht := by
    change (convert T S N (fun x hx ↦ (he x hx).symm) s₀ t).val ∈ N
    rw [convert_val T S N _ s₀ ht]
    exact ht
  left_inv' s hs := by
    apply Subtype.ext
    have hst : (convert S T N he t₀ s).val ∈ N := by
      rw [convert_val S T N he t₀ hs]
      exact hs
    rw [convert_val T S N _ s₀ hst, convert_val S T N he t₀ hs]
  right_inv' t ht := by
    apply Subtype.ext
    have hts : (convert T S N (fun x hx ↦ (he x hx).symm) s₀ t).val ∈ N := by
      rw [convert_val T S N _ s₀ ht]
      exact ht
    rw [convert_val S T N he t₀ hts, convert_val T S N _ s₀ ht]
  open_source := hN.preimage continuous_subtype_val
  open_target := hN.preimage continuous_subtype_val
  continuousOn_toFun := continuousOn_convert S T N he t₀
  continuousOn_invFun := continuousOn_convert T S N (fun x hx ↦ (he x hx).symm) s₀

theorem coordinates_val (hN : IsOpen N) (s₀ : S) (t₀ : T) {s : S}
    (hs : s ∈ (coordinates S T N he hN s₀ t₀).source) :
    (coordinates S T N he hN s₀ t₀ s).val = s.val :=
  convert_val S T N he t₀ hs

theorem coordinates_symm_val (hN : IsOpen N) (s₀ : S) (t₀ : T) {t : T}
    (ht : t ∈ (coordinates S T N he hN s₀ t₀).target) :
    ((coordinates S T N he hN s₀ t₀).symm t).val = t.val :=
  convert_val T S N (fun x hx ↦ (he x hx).symm) s₀ ht

end NoExoticSixSphere.SetGerm

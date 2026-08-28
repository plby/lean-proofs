import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Restricting a local coordinate change to corresponding subsets

An actual local image relation induces an open partial homeomorphism
between the two subsets with their original subtype topologies.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.SubsetCoordinates

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y) {S : Set X} {T : Set Y} (he : e.IsImage S T)

def map (t₀ : T) (s : S) : T := by
  classical
  exact if hs : s.val ∈ e.source then ⟨e s.val, (he hs).mpr s.property⟩ else t₀

theorem map_val (t₀ : T) {s : S} (hs : s.val ∈ e.source) :
    (map e he t₀ s).val = e s.val := by
  simp only [map, dif_pos hs]

theorem continuousOn_map (t₀ : T) :
    ContinuousOn (map e he t₀) (Subtype.val ⁻¹' e.source) := by
  apply IsInducing.subtypeVal.continuousOn_iff.mpr
  apply (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx ↦ hx)).congr
  intro s hs
  exact map_val e he t₀ hs

def coordinates (s₀ : S) (t₀ : T) : OpenPartialHomeomorph S T where
  toFun := map e he t₀
  invFun := map e.symm he.symm s₀
  source := Subtype.val ⁻¹' e.source
  target := Subtype.val ⁻¹' e.target
  map_source' s hs := by
    change (map e he t₀ s).val ∈ e.target
    rw [map_val e he t₀ hs]
    exact e.map_source hs
  map_target' t ht := by
    change (map e.symm he.symm s₀ t).val ∈ e.source
    rw [map_val e.symm he.symm s₀ ht]
    exact e.map_target ht
  left_inv' s hs := by
    apply Subtype.ext
    have hst : (map e he t₀ s).val ∈ e.target := by
      rw [map_val e he t₀ hs]
      exact e.map_source hs
    rw [map_val e.symm he.symm s₀ hst, map_val e he t₀ hs, e.left_inv hs]
  right_inv' t ht := by
    apply Subtype.ext
    have hts : (map e.symm he.symm s₀ t).val ∈ e.source := by
      rw [map_val e.symm he.symm s₀ ht]
      exact e.map_target ht
    rw [map_val e he t₀ hts, map_val e.symm he.symm s₀ ht, e.right_inv ht]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage continuous_subtype_val
  continuousOn_toFun := continuousOn_map e he t₀
  continuousOn_invFun := continuousOn_map e.symm he.symm s₀

theorem coordinates_val (s₀ : S) (t₀ : T) {s : S}
    (hs : s ∈ (coordinates e he s₀ t₀).source) :
    (coordinates e he s₀ t₀ s).val = e s.val :=
  map_val e he t₀ hs

theorem coordinates_symm_val (s₀ : S) (t₀ : T) {t : T}
    (ht : t ∈ (coordinates e he s₀ t₀).target) :
    ((coordinates e he s₀ t₀).symm t).val = e.symm t.val :=
  map_val e.symm he.symm s₀ ht

end NoExoticSixSphere.SubsetCoordinates

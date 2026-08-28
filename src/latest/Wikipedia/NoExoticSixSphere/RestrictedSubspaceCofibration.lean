import Wikipedia.NoExoticSixSphere.SubspaceCofibration

/-!
# Restricting a neighborhood deformation to a preserved subspace

If the actual deformation preserves a subspace, restricting its height
and motion gives neighborhood data for the intersection inside that
subspace. The zero set, stationarity, and terminal inclusion are retained.
-/

noncomputable section

open Set
open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.SubspaceCofibration

variable {X : Type*} [TopologicalSpace X] (A B : Set X)
  (D : NeighborhoodDeformation.Data (inclusion A))
  (hB : ∀ (t : I) (x : X), x ∈ B → D.deformation (t, x) ∈ B)

def restrictedData : NeighborhoodDeformation.Data (inclusion {x : B | x.val ∈ A}) where
  height := D.height.comp ⟨Subtype.val, continuous_subtype_val⟩
  deformation :=
    ⟨fun p ↦ ⟨D.deformation (p.1, p.2.val), hB p.1 p.2.val p.2.property⟩,
      (D.deformation.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩
  zero_iff x := by
    change D.height x.val = 0 ↔ _
    rw [D.zero_iff, mem_range, mem_range]
    rfl
  bottom x := Subtype.ext (D.bottom x.val)
  fixed t x := Subtype.ext (D.fixed t ⟨x.val.val, x.property⟩)
  terminal x hx := by
    rw [mem_range]
    exact (mem_range A _).mp (D.terminal x.val hx)

end NoExoticSixSphere.SubspaceCofibration

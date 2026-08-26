import ErdosProblems.Erdos73.OddTerminalPathsDefs
import ErdosProblems.Erdos73.PackingCopy

/-! Odd terminal paths in induced regions map to the original graph. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def regionTerminals (N R : Finset V) : Finset (R : Set V) :=
  Finset.univ.filter fun v => v.val ∈ N

@[simp] theorem mem_regionTerminals (N R : Finset V) (v : (R : Set V)) :
    v ∈ regionTerminals N R ↔ v.val ∈ N := by simp [regionTerminals]

theorem regionTerminals_card {N R : Finset V} (hNR : N ⊆ R) :
    (regionTerminals N R).card = N.card := by
  have he : (regionTerminals N R).image Subtype.val = N := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
      exact (mem_regionTerminals _ _ _).mp hw
    · intro hv
      exact mem_image.mpr ⟨⟨v, hNR hv⟩, (mem_regionTerminals _ _ _).mpr hv, rfl⟩
  exact (card_image_of_injective _ Subtype.val_injective).symm.trans (congrArg Finset.card he)

theorem IsOddTerminalPath.map_induced_region {N R : Finset V}
    {P : GraphPath (G.induce (R : Set V))} (hP : IsOddTerminalPath (regionTerminals N R) P) :
    IsOddTerminalPath N (P.mapCopy (Embedding.induce (R : Set V)).toCopy) := by
  refine ⟨(mem_regionTerminals _ _ _).mp hP.source_mem,
    (mem_regionTerminals _ _ _).mp hP.target_mem, ?_, ?_⟩
  · simpa only [GraphPath.mapCopy, Walk.length_map] using hP.odd_length
  · intro v hv hvN
    obtain ⟨w, hw, rfl⟩ := (P.mem_mapCopy_vertexSet _ v).mp hv
    rcases hP.internal_disjoint w hw ((mem_regionTerminals _ _ _).mpr hvN) with hw | hw
    · exact Or.inl (congrArg Subtype.val hw)
    · exact Or.inr (congrArg Subtype.val hw)

theorem no_oddTerminalPath_in_region_of_hitting {N X R : Finset V}
    (hX : HitsOddTerminalPaths G N X) (hRX : Disjoint R X) :
    ¬ ∃ P : GraphPath (G.induce (R : Set V)), IsOddTerminalPath (regionTerminals N R) P := by
  rintro ⟨P, hP⟩
  apply hX _ hP.map_induced_region
  apply Finset.disjoint_left.mpr
  intro v hv hvX
  obtain ⟨w, _, rfl⟩ := (P.mem_mapCopy_vertexSet _ v).mp hv
  exact Finset.disjoint_left.mp hRX w.property hvX

end
end Erdos73

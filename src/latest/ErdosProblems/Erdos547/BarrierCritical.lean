import ErdosProblems.Erdos547.ExtremalBarrier
import ErdosProblems.Erdos547.TutteTransport

/-!
# The blocks of an extremal barrier are factor-critical

Tutte's theorem is applied after one vertex of a block is removed. The local
deficiency inequality and the parity of the block give every required Tutte
inequality, including deletion of the empty set in that smaller graph.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem SeparatesOn.restore_deleted_vertex {C U : Finset V} {H : Finset (Finset V)}
    {v : V} (h : SeparatesOn G (C.erase v) U H) (hv : v ∈ C) :
    SeparatesOn G C (insert v U) H := by
  have hset : C.erase v \ U = C \ insert v U := by ext u; simp; tauto
  refine ⟨?_, h.nonempty, h.disjoint, h.cover.trans hset, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hv
    · exact Finset.mem_of_mem_erase (h.separator_subset hu)
  · intro D hD u hu z hz huz
    exact h.closed D hD u hu z (hset ▸ hz) huz

variable [Finite V]

namespace IsBarrier

variable {A S C : Finset V} {F : Finset (Finset V)}

theorem deleted_block_tutte_bound (h : IsBarrier G A S F) (hC : C ∈ F)
    {v : V} (hv : v ∈ C) (U : Finset V) (H : Finset (Finset V))
    (hH : SeparatesOn G (C.erase v) U H) : (oddParts H).card ≤ U.card := by
  have hvU : v ∉ U := fun hvU ↦ Finset.notMem_erase v C (hH.separator_subset hvU)
  have hlocal := h.local_odd_bound hC (hH.restore_deleted_vertex hv) (Finset.insert_nonempty _ _)
  rw [Finset.card_insert_of_notMem hvU] at hlocal
  have hcard := Finset.card_erase_add_one hv
  have hsub := Finset.card_le_card hH.separator_subset
  have hodd := h.odd_part hC
  have hpar := hH.odd_parts_iff
  rw [Nat.odd_iff] at hodd
  simp only [Nat.odd_iff] at hpar
  omega

theorem factorCritical_part (h : IsBarrier G A S F) (hC : C ∈ F) :
    IsFactorCritical (G.induce (C : Set V)) := by
  classical
  intro v
  obtain ⟨M, hM⟩ := perfect_matching_of_separation_bounds G (C.erase v.val)
    (h.deleted_block_tutte_bound hC v.property)
  let incl : (G.induce (↑(C.erase v.val) : Set V)) →g (G.induce (C : Set V)) := {
    toFun := fun x ↦ ⟨x.val, Finset.mem_of_mem_erase x.property⟩
    map_rel' := fun h ↦ h }
  have hi : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : (C : Set V) ↦ z.val) hxy)
  refine ⟨M.map incl, hM.1.map incl hi, ?_⟩
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    change incl y ≠ v
    intro heq
    have hval : y.val = v.val := congrArg Subtype.val heq
    exact (Finset.ne_of_mem_erase y.property) hval
  · intro hx
    have hxv : x.val ≠ v.val := fun hxv ↦ hx (Subtype.ext hxv)
    let y : (↑(C.erase v.val) : Set V) := ⟨x.val, Finset.mem_erase.mpr ⟨hxv, x.property⟩⟩
    exact ⟨y, hM.2 y, Subtype.ext rfl⟩

end IsBarrier

end Erdos547.DPRS

#print axioms Erdos547.DPRS.IsBarrier.factorCritical_part

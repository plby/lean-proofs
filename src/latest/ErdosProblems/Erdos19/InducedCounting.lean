import ErdosProblems.Erdos19.PeelableColoring
import ErdosProblems.Erdos19.Core

/-! # Counting neighbors in a finite induced core -/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

theorem subtype_preimage_ncard_le {V : Type*} [Fintype V] (S T : Set V) :
    (Subtype.val ⁻¹' T : Set S).ncard ≤ T.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  apply Set.ncard_le_ncard (t := T) ?_ (Set.toFinite T)
  rintro v ⟨w, hw, rfl⟩
  exact hw

theorem induced_neighbor_ncard_le {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (S : Set V) (v : S) :
    ((G.induce S).neighborSet v).ncard ≤ (G.neighborSet v.1).ncard :=
  subtype_preimage_ncard_le S (G.neighborSet v.1)

theorem induced_common_neighbor_ncard_le {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (S : Set V) (v w : S) :
    ((G.induce S).neighborSet v ∩ (G.induce S).neighborSet w).ncard ≤
      (G.neighborSet v.1 ∩ G.neighborSet w.1).ncard :=
  subtype_preimage_ncard_le S (G.neighborSet v.1 ∩ G.neighborSet w.1)

theorem induced_finset_neighbor_ncard {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (S : Finset V) (v : (S : Set V)) :
    ((G.induce (S : Set V)).neighborSet v).ncard = (S.filter (G.Adj v.1)).card := by
  classical
  let e : (G.induce (S : Set V)).neighborSet v ≃ ↥(S.filter (G.Adj v.1)) :=
    { toFun := fun w ↦ ⟨w.1.1, mem_filter.mpr ⟨w.1.2, w.2⟩⟩
      invFun := fun w ↦ ⟨⟨w.1, (mem_filter.mp w.2).1⟩, (mem_filter.mp w.2).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa only [Set.fintypeCard_eq_ncard, Fintype.card_coe] using Fintype.card_congr e

theorem colorable_of_colorable_peelable_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (S : Finset V) (k : ℕ) (hk : 0 < k)
    (hpeel : IsPeelableOutside G univ S k) (hcore : (G.induce (S : Set V)).Colorable k) :
    G.Colorable k := by
  classical
  obtain ⟨color⟩ := hcore
  let c₀ : V → Fin k := fun v ↦ if hv : v ∈ S then color ⟨v, hv⟩ else ⟨0, hk⟩
  have hc₀ : ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c₀ v ≠ c₀ w := by
    intro v hv w hw hadj
    simpa only [c₀, dif_pos hv, dif_pos hw] using
      color.valid (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) hadj
  obtain ⟨c, _, _, hc⟩ := hpeel.exists_list_coloring_extension (subset_univ S)
    (fun _ ↦ (univ : Finset (Fin k))) (fun _ _ ↦ by simp) c₀ hc₀
  exact ⟨{ toFun := c, map_rel' := fun hadj ↦ hc _ (mem_univ _) _ (mem_univ _) hadj }⟩

#print axioms colorable_of_colorable_peelable_core

end Erdos19

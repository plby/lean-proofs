import Arxiv.Arxiv2411_18291.IncidentRootEmbeddings

/-! # Edge degrees controlled by vertex fibres of prescribed embeddings -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem mapBlock_familyDegree_le_of_fibers {I U V : Type*} [Fintype I]
    [DecidableEq V] (Φ : I → U ↪ V) (e : Block U 2) (m : ℕ)
    (hf : ∀ x v, (univ.filter fun i => Φ i x = v).card ≤ m) (S : Block V 1) :
    familyDegree (fun i => mapBlock (Φ i) e) S.val ≤ 2 * m := by
  classical
  obtain ⟨v, hv⟩ := card_eq_one.mp S.property
  have hsub : (univ.filter fun i => S.val ⊆ (mapBlock (Φ i) e).val) ⊆
      e.val.biUnion (fun x => univ.filter fun i => Φ i x = v) := by
    intro i hi
    have hm : v ∈ e.val.map (Φ i) := by
      exact (mem_filter.mp hi).2 (by rw [hv]; exact mem_singleton_self _)
    obtain ⟨x, hx, hxi⟩ := mem_map.mp hm
    exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨mem_univ _, hxi⟩⟩
  calc
    _ ≤ (e.val.biUnion (fun x => univ.filter fun i => Φ i x = v)).card :=
      card_le_card hsub
    _ ≤ ∑ x ∈ e.val, (univ.filter fun i => Φ i x = v).card := card_biUnion_le
    _ ≤ ∑ _x ∈ e.val, m := sum_le_sum fun x _ => hf x v
    _ = 2 * m := by simp only [sum_const, nsmul_eq_mul, e.property, Nat.cast_id]

theorem embedding_fiber_card_le {I J U V V' : Type*} [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq V'] (e : I ≃ J) (g : V ↪ V') (Φ : J → U ↪ V)
    (m : ℕ) (hf : ∀ x v, (univ.filter fun j => Φ j x = v).card ≤ m) (x : U) (v : V') :
    (univ.filter fun i => (Φ (e i)).trans g x = v).card ≤ m := by
  classical
  by_cases hv : ∃ w, g w = v
  · obtain ⟨w, rfl⟩ := hv
    have hc : (univ.filter fun i => (Φ (e i)).trans g x = g w).card =
        (univ.filter fun j => Φ j x = w).card := by
      let e' : {i : I // g (Φ (e i) x) = g w} ≃ {j : J // Φ j x = w} :=
        Equiv.subtypeEquiv e (fun _ => g.injective.eq_iff)
      have heq := Fintype.card_congr e'
      simpa only [Fintype.card_subtype, Function.Embedding.trans_apply] using heq
    rw [hc]
    exact hf x w
  · have hempty : (univ.filter fun i => (Φ (e i)).trans g x = v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hv ⟨Φ (e i) x, (mem_filter.mp hi).2⟩
    rw [hempty, card_empty]
    exact Nat.zero_le _

theorem usedVertices_intersect_trans {W V V' : Type*} {F : Finset W}
    [DecidableEq V] [DecidableEq V'] (φ ψ : F ↪ V) (g : V ↪ V')
    (h : (usedVertices φ ∩ usedVertices ψ).Nonempty) :
    (usedVertices (φ.trans g) ∩ usedVertices (ψ.trans g)).Nonempty := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨x, hx⟩ := (mem_usedVertices φ v).mp (mem_inter.mp hv).1
  obtain ⟨y, hy⟩ := (mem_usedVertices ψ v).mp (mem_inter.mp hv).2
  refine ⟨g v, mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (mem_usedVertices _ _).mpr ⟨x, congrArg g hx⟩
  · exact (mem_usedVertices _ _).mpr ⟨y, congrArg g hy⟩

end Arxiv2411_18291

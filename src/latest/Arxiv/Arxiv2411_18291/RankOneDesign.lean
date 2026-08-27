import Arxiv.Arxiv2411_18291.CoefficientRelabeling

/-! # Rank-one designs are partitions into equal-sized blocks -/

open Finset

noncomputable section

namespace Arxiv2411_18291

def rankOneFamily (q m : ℕ) : Finset (Block (Fin q × Fin m) q) :=
  univ.image fun b : Fin m => graphClique (fun _ : Fin q => b)

theorem rankOneFamily_isDecomposition (q m : ℕ) :
    IsDecomposition (complete (Fin q × Fin m) 1) (rankOneFamily q m) := by
  apply isDecomposition_of_unique
  · intro Q _
    exact subset_univ _
  · intro e _
    obtain ⟨v, hv⟩ := card_eq_one.mp e.property
    refine ⟨graphClique (fun _ : Fin q => v.2), ⟨?_, ?_⟩, ?_⟩
    · exact mem_image.mpr ⟨v.2, mem_univ _, rfl⟩
    · simp only [hv, singleton_subset_iff]
      exact (mem_graphClique _ v.1 v.2).mpr rfl
    · intro Q hQ
      obtain ⟨b, _, rfl⟩ := mem_image.mp hQ.1
      have hmem := hQ.2 (show v ∈ e.val by rw [hv]; exact mem_singleton_self _)
      have hb : v.2 = b := (mem_graphClique _ v.1 v.2).mp hmem
      rw [hb]

theorem mapGraph_complete_equiv {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (f : V ≃ W) (r : ℕ) :
    mapGraph f.toEmbedding (complete V r) = complete W r := by
  apply eq_univ_of_forall
  intro e
  exact (mem_mapGraph _ _ _).mpr
    ⟨mapBlock f.symm.toEmbedding e, mem_univ _, (blockEquiv f).apply_symm_apply e⟩

theorem hasDecomposition_complete_one_of_dvd {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (h : q ∣ Fintype.card V) : HasDecomposition q (complete V 1) := by
  obtain ⟨m, hm⟩ := h
  let f : (Fin q × Fin m) ≃ V := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hm.symm)
  have hD := (rankOneFamily_isDecomposition q m).map f.toEmbedding
  rw [mapGraph_complete_equiv] at hD
  exact ⟨_, hD⟩

theorem hasDecomposition_complete_one_of_divisible {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (h : Divisible q (complete V 1)) : HasDecomposition q (complete V 1) := by
  apply hasDecomposition_complete_one_of_dvd
  simpa only [card_empty, Nat.sub_zero, Nat.choose_one_right] using
    h.complete_degree_dvd ∅ (by simp)

end Arxiv2411_18291

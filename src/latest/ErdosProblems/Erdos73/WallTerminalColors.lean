import ErdosProblems.Erdos73.ControlledWallRows

/-! Same-colour terminals on many distinct interior rows of a balanced wall. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure BipartiteColoringOn (G : SimpleGraph V) (T : Finset V) where
  color : V → Bool
  valid : ∀ x ∈ T, ∀ y ∈ T, G.Adj x y → color x ≠ color y

def bipartiteColoringOnOfBipartite {T : Finset V}
    (hT : (G.induce (T : Set V)).IsBipartite) : BipartiteColoringOn G T := by
  let c : (G.induce (T : Set V)).Coloring Bool := hT.toColoring (by decide)
  refine ⟨fun v => if hv : v ∈ T then c ⟨v, hv⟩ else false, ?_⟩
  intro x hx y hy hxy
  simp only [dif_pos hx, dif_pos hy]
  exact c.valid hxy

theorem exists_large_bool_fiber {I : Type*} [Fintype I] (f : I → Bool)
    (u : ℕ) (hsize : 2 * u ≤ Fintype.card I) :
    ∃ b : Bool, ∃ J : Finset I, u ≤ J.card ∧ ∀ i ∈ J, f i = b := by
  let J := Finset.univ.filter (fun i => f i = false)
  by_cases hJ : u ≤ J.card
  · exact ⟨false, J, hJ, fun _ hi => (Finset.mem_filter.mp hi).2⟩
  · have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
    rw [Finset.card_univ] at hcard
    refine ⟨true, Finset.univ \ J, by omega, ?_⟩
    intro i hi
    have hn : f i ≠ false := fun hh => (Finset.mem_sdiff.mp hi).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    cases he : f i
    · exact (hn he).elim
    · rfl

def innerRowEmbedding (g : ℕ) : Fin (g - 2) ↪ Fin g :=
  ⟨fun r => ⟨r.val + 1, by have hr := r.isLt; omega⟩, fun r s he => Fin.ext (by
    have hh := congrArg Fin.val he
    change r.val + 1 = s.val + 1 at hh
    omega)⟩

theorem exists_monochromatic_row_terminals {g : ℕ}
    (S : GraphSubdivisionModel (elementaryWall g g) G) (hg : 2 ≤ g)
    (c : BipartiteColoringOn G S.vertexSet) (u : ℕ) (hsize : 2 * u + 2 ≤ g) :
    ∃ N : Finset V, ∃ J : Finset (Fin g), ∃ b : Bool,
      N ⊆ S.vertexSet ∧ u ≤ J.card ∧
      (∀ r ∈ J, ∃ v ∈ N, v ∈ interiorWallRowSupport S hg r) ∧
      (∀ v ∈ N, c.color v = b) ∧
      (∀ v ∈ N, ∃ r : Fin (g - 2),
        v = S.branchVertex (elementaryWallInteriorNail hg (innerRowEmbedding g r) ⟨1, by omega⟩)) := by
  let sample (r : Fin (g - 2)) :=
    S.branchVertex (elementaryWallInteriorNail hg (innerRowEmbedding g r) ⟨1, by omega⟩)
  obtain ⟨b, I, hIcard, hIcolor⟩ := exists_large_bool_fiber (c.color ∘ sample) u
    (by simpa only [Fintype.card_fin] using (show 2 * u ≤ g - 2 by omega))
  refine ⟨I.image sample, I.map (innerRowEmbedding g), b, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
    exact (S.mem_vertexSet _).mpr (Or.inl ⟨_, rfl⟩)
  · simpa only [Finset.card_map] using hIcard
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hr
    exact ⟨sample j, Finset.mem_image.mpr ⟨j, hj, rfl⟩,
      interiorNail_mem_rowSupport S hg (innerRowEmbedding g j) ⟨1, by omega⟩⟩
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact hIcolor r hr
  · intro v hv
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r, rfl⟩

end
end Erdos73

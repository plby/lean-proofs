import ErdosProblems.Erdos1105.SharpBoundarySubset
import ErdosProblems.Erdos1105.ThreeCliqueRestriction
import ErdosProblems.Erdos1105.ColorPullback
import ErdosProblems.Erdos1105.EvenThreeClique

namespace Erdos1105

open SimpleGraph Finset

/-- Equality in the even clique-core bound is incompatible with a
rainbow representative avoiding the required path. -/
theorem rainbow_path_of_sharp_clique_core {V C : Type*} [Fintype V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hR : Set.InjOn (extendColor c) G.edgeSet) {d : ℕ} (hd : 2 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V)
    (hfree : ¬pathGraph (2 * d + 2) ⊑ G)
    (hclique : (graphCone G).IsClique (vertexCore (graphCone G) d : Set (Option V)))
    (hcard : (vertexCore (graphCone G) d).card = d + 3)
    (hsharp : G.edgeFinset.card = pathExtremalEdges (Fintype.card V) (2 * d + 1) (d - 1)) :
    ∃ f : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph V), IsRainbow f c := by
  classical
  have hconeSharp : (graphCone G).edgeFinset.card =
      (vertexCore (graphCone G) d).card.choose 2 +
        d * (Fintype.card (Option V) - (vertexCore (graphCone G) d).card) := by
    rw [graphCone_card_edges, Fintype.card_option, hcard, hsharp]
    have h := cone_nonempty_count (Fintype.card V) (2 * d + 2) (d + 3)
      (by omega) (by omega) hn
    rw [show 2 * d + 2 + 1 - (d + 3) = d by omega,
      show 2 * d + 2 - 1 = 2 * d + 1 by omega,
      show 2 * d + 2 - (d + 3) = d - 1 by omega] at h
    simpa only [Nat.add_comm] using h.symm
  obtain ⟨U, hUcard, hUcore, A, T, hA, hT, hAT, huni, hjoin⟩ :=
    exists_sharp_boundary_join (graphCone G) hd
      (by simpa only [Fintype.card_option] using Nat.add_le_add_right hn 1)
      hclique hcard (no_long_cycle_cone_of_path_free G (by omega) hfree) hconeSharp
  have hnoneCore := universal_mem_vertexCore (graphCone G) d
    (card_pos.mp (by omega)) (graphCone_universal G)
  have hnone : none ∈ U := hUcore hnoneCore
  let X : Finset V := univ.filter (fun v ↦ some v ∈ U)
  have hXim : X.image some = U.erase none := by
    ext w
    cases w with
    | none => simp
    | some v => simp [X]
  have hXcard : X.card = 2 * d + 2 := by
    have h := congrArg Finset.card hXim
    rw [card_image_of_injective _ (Option.some_injective V), card_erase_of_mem hnone, hUcard] at h
    omega
  let u : (U : Set (Option V)) := ⟨none, hnone⟩
  let f : (X : Set V) ↪ (U : Set (Option V)) :=
    ⟨fun v ↦ ⟨some v.val, (mem_filter.mp v.property).2⟩,
      fun _ _ h ↦ Subtype.ext (Option.some.inj (congrArg Subtype.val h))⟩
  have hfavoid (v : (X : Set V)) : f v ≠ u := by
    intro h
    exact Option.some_ne_none _ (congrArg Subtype.val h)
  have hfcover (w : (U : Set (Option V))) (hw : w ≠ u) : ∃ v, f v = w := by
    rcases w with ⟨w, hwU⟩
    cases w with
    | none => exact (hw (Subtype.ext rfl)).elim
    | some v => exact ⟨⟨v, mem_filter.mpr ⟨mem_univ _, hwU⟩⟩, rfl⟩
  have hu : ((graphCone G).induce (U : Set (Option V))).IsUniversal u := by
    intro w hne
    apply graphCone_universal G
    exact fun h ↦ hne (Subtype.ext h)
  obtain ⟨A', T', hA', hT', hAT', hjoin'⟩ :=
    threeCliqueJoin_remove_vertex f u hfavoid hfcover (huni u hu) hA hT hAT
  have hbaseJoin : threeCliqueJoin A' T' ≤ G.induce (X : Set V) := by
    intro v w hvw
    exact hjoin (hjoin' hvw)
  let φ := completeCopy (⊤ : SimpleGraph (X : Set V)) ⟨Subtype.val, Subtype.val_injective⟩
  let c' := c ∘ φ.mapEdgeSet
  have hcolors : Set.InjOn (extendColor c') (G.induce (X : Set V)).edgeSet :=
    rainbow_color_pullback c hR (Copy.induce G (X : Set V))
  obtain ⟨p, hp⟩ := rainbow_path_of_threeCliqueJoin c' hcolors hd
    (by simpa using hXcard.ge) hAT' hA' hT' hbaseJoin
  exact ⟨φ.comp p, (rainbow_comp_iff p φ c).mpr hp⟩

end Erdos1105

#print axioms Erdos1105.rainbow_path_of_sharp_clique_core

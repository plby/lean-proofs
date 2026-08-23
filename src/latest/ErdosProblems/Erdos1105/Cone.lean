import ErdosProblems.Erdos1105.CoreBound
import ErdosProblems.Erdos1105.PathFree

namespace Erdos1105

open SimpleGraph Finset

/-- Adjoin one new universal vertex. -/
def graphCone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | some v, some w => G.Adj v w
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by rintro (_ | v) (_ | w) h <;> first | exact h | exact h.symm⟩
  loopless := ⟨by rintro (_ | v) <;> first | exact not_false | exact G.loopless.irrefl v⟩

lemma graphCone_universal {V : Type*} (G : SimpleGraph V) :
    (graphCone G).IsUniversal none := by
  rintro (_ | v) h
  · exact (h rfl).elim
  · trivial

def coneSomeIso {V : Type*} (G : SimpleGraph V) :
    (graphCone G).induce {v | v ≠ none} ≃g G where
  toEquiv := (Equiv.setCongr (by ext v; exact Option.ne_none_iff_isSome)).trans
    (Equiv.optionIsSomeEquiv V)
  map_rel_iff' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    cases x with
    | none => exact (hx rfl).elim
    | some x =>
      cases y with
      | none => exact (hy rfl).elim
      | some y => rfl

lemma graphCone_delete_preconnected {V : Type*} (G : SimpleGraph V)
    (hconn : G.Preconnected) : ((graphCone G).induce {v | v ≠ none}).Preconnected :=
  hconn.map (coneSomeIso G).symm.toHom (coneSomeIso G).symm.surjective

lemma path_contained_of_cone_path_avoids_none {V : Type*} (G : SimpleGraph V)
    {x y : Option V} (p : (graphCone G).Walk x y) (hp : p.IsPath)
    (hnone : none ∉ p.support) {k : ℕ} (hlen : k ≤ p.length + 1) : pathGraph k ⊑ G := by
  classical
  have hs : ∀ v ∈ p.support, v ∈ ({v | v ≠ none} : Set (Option V)) := by
    intro v hv h
    exact hnone (h ▸ hv)
  let p' := p.induce {v | v ≠ none} hs
  have hp' : p'.IsPath := by
    apply (Walk.isPath_map_iff_of_injective
      (f := (Embedding.induce (G := graphCone G) {v | v ≠ none}).toHom)
      (p := p') (Embedding.induce (G := graphCone G) {v | v ≠ none}).injective).mp
    rw [Walk.map_induce]
    exact hp
  let r := p'.map (coneSomeIso G).toHom
  have hr : r.IsPath := hp'.map (coneSomeIso G).injective
  apply hr.isContained_pathGraph.trans'
  have hlenr : k ≤ r.length + 1 := by
    rw [Walk.length_map, induced_walk_length]
    exact hlen
  exact ⟨pathCopyOfLE hlenr⟩

lemma no_long_cycle_cone_of_path_free {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 3 ≤ k) (hfree : ¬pathGraph k ⊑ G) : NoLongCycle (graphCone G) (k + 1) := by
  classical
  intro v p hp
  by_contra! hlen
  apply hfree
  by_cases hnone : none ∈ p.support
  · let q := p.rotate none hnone
    have hq : q.IsCycle := hp.rotate hnone
    let r := q.tail.dropLast
    have hr : r.IsPath := hq.isPath_tail.dropLast
    have hrnone : none ∉ r.support := path_end_not_mem_dropLast q.tail hq.isPath_tail
      (by rw [Walk.length_tail, Walk.length_rotate]; omega)
    apply path_contained_of_cone_path_avoids_none G r hr hrnone
    simp only [r, q, Walk.length_dropLast, Walk.length_tail, Walk.length_rotate]
    omega
  · have htail : none ∉ p.tail.support := by
      intro h
      apply hnone
      rw [← Walk.cons_support_tail hp.not_nil]
      exact List.mem_cons_of_mem _ h
    apply path_contained_of_cone_path_avoids_none G p.tail hp.isPath_tail htail
    rw [Walk.length_tail]
    omega

lemma path_free_of_no_long_cycle_cone {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 2 ≤ k) (hcone : NoLongCycle (graphCone G) (k + 1)) :
    ¬pathGraph k ⊑ G := by
  classical
  intro hcopy
  obtain ⟨a, b, p, hp, hlen⟩ := exists_path_of_path_contained (by omega) hcopy
  let f : G →g graphCone G := { toFun := some, map_rel' := fun h ↦ h }
  let q := p.map f
  have hq : q.IsPath := hp.map (Option.some_injective V)
  have hnone : none ∉ q.support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨v, _, hv⟩
    exact Option.some_ne_none v hv
  let r := q.concat (show (graphCone G).Adj (some b) none from True.intro)
  have hr : r.IsPath := hq.concat hnone _
  have hclose : (graphCone G).Adj none (some a) := True.intro
  have hc : (Walk.cons hclose r).IsCycle := by
    apply (Walk.cons_isCycle_iff r hclose).mpr
    refine ⟨hr, ?_⟩
    intro he
    have h := hr.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    simp only [r, q, Walk.length_concat, Walk.length_map] at h
    omega
  have h := hcone none (Walk.cons hclose r) hc
  simp only [r, q, Walk.length_cons, Walk.length_concat, Walk.length_map] at h
  omega

lemma graphCone_comap_some {V : Type*} (H : SimpleGraph (Option V))
    (hu : H.IsUniversal none) : graphCone (H.comap some) = H := by
  ext x y
  cases x with
  | none =>
    cases y with
    | none => simp [graphCone]
    | some y => exact iff_of_true True.intro (hu (by simp))
  | some x =>
    cases y with
    | none => exact iff_of_true True.intro (hu (by simp)).symm
    | some y => rfl

lemma cone_clique_remove_none {V : Type*} [Fintype V] (H : SimpleGraph (Option V))
    {T : Finset (Option V)} (hT : H.IsClique (T : Set (Option V))) (hNone : none ∈ T) :
    ∃ S : Finset V, (H.comap some).IsClique (S : Set V) ∧ S.card + 1 = T.card := by
  classical
  let S := univ.filter fun v ↦ some v ∈ T
  have himage : S.image some = T.erase none := by
    ext v
    cases v <;> simp [S]
  have hcard : S.card + 1 = T.card := by
    have h := congrArg Finset.card himage
    rw [card_image_of_injective _ (Option.some_injective V), card_erase_of_mem hNone] at h
    have hpos := card_pos.mpr ⟨none, hNone⟩
    omega
  refine ⟨S, ?_, hcard⟩
  intro a ha b hb hab
  exact hT (mem_filter.mp ha).2 (mem_filter.mp hb).2 ((Option.some_injective V).ne hab)

lemma graphCone_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel (graphCone G).Adj] :
    (graphCone G).edgeFinset.card = G.edgeFinset.card + Fintype.card V := by
  classical
  have hdel := edgesInside_erase (graphCone G) (S := univ) (mem_univ (none : Option V))
  have hS : ((univ.erase (none : Option V) : Finset (Option V)) : Set (Option V)) =
      {v | v ≠ none} := by ext v; simp
  have hedges : (E767EGApi.edgesInside (graphCone G) (univ.erase none)).card =
      G.edgeFinset.card := by
    rw [E767EGApi.card_edgesInside]
    let e₀ : (↑(univ.erase (none : Option V)) : Set (Option V)) ≃ {v | v ≠ none} :=
      Equiv.setCongr hS
    let e : (graphCone G).induce (↑(univ.erase (none : Option V)) : Set (Option V)) ≃g
        (graphCone G).induce {v | v ≠ none} :=
      { toEquiv := e₀
        map_rel_iff' := by intros; rfl }
    exact SimpleGraph.Iso.card_edgeFinset_eq (e.trans (coneSomeIso G))
  have hdeg : degreeWithin (graphCone G) univ none = Fintype.card V := by
    calc
      _ = (univ.erase (none : Option V)).card := by
        unfold degreeWithin
        apply congrArg Finset.card
        ext v
        simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
        cases v <;> simp [graphCone]
      _ = _ := by simp
  rw [hedges, hdeg] at hdel
  simpa [E767EGApi.edgesInside] using hdel

end Erdos1105

#print axioms Erdos1105.no_long_cycle_cone_of_path_free
#print axioms Erdos1105.graphCone_card_edges

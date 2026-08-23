import ErdosProblems.Erdos1105.TwoAttachmentNeighbors
import ErdosProblems.Erdos1105.PendantBlock
import ErdosProblems.Erdos1105.Cone

namespace Erdos1105

open SimpleGraph Finset

/-- Removing the universal vertex from the two-attachment configuration
leaves a pendant clique of order `d+1`. -/
theorem low_core_two_attachment_pendant {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hd : 1 ≤ d) (hlen : 2 * d + 2 ≤ p.length)
    (hA : startNeighborIndices p = insert (p.length - d - 1) (range d))
    (hB : endNeighborIndices p = insert d (Ico (p.length - d) p.length)) :
    ∃ (S : Finset V) (v : V), S.card = d ∧ u ∉ S ∧ v ≠ u ∧ v ∉ S ∧
      G.IsClique (↑(insert v S) : Set V) ∧
      (∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S ∨ b = u ∨ b = v) := by
  classical
  let S := (range d).image p.getVert
  have hlong : 2 * d + 3 ≤ p.length + 1 := by omega
  have hbefore : ∀ j < d, ¬G.Adj y (p.getVert j) := by
    intro j hj hadj
    have hm : j ∈ endNeighborIndices p := mem_filter.mpr ⟨mem_range.mpr (by omega), hadj⟩
    rw [hB] at hm
    simp only [mem_insert, mem_Ico] at hm
    omega
  have hScard : S.card = d := by
    dsimp only [S]
    rw [card_image_of_injOn, card_range]
    intro i hi j hj heq
    exact hp.isPath.getVert_injOn (show i ≤ p.length by have := mem_range.mp hi; omega)
      (show j ≤ p.length by have := mem_range.mp hj; omega) heq
  have hnotS (j : ℕ) (hjd : d ≤ j) (hjL : j ≤ p.length) : p.getVert j ∉ S := by
    intro hj
    obtain ⟨r, hr, heq⟩ := mem_image.mp hj
    have hrd := mem_range.mp hr
    have := hp.isPath.getVert_injOn (show r ≤ p.length by omega) hjL heq
    omega
  have hatne : p.getVert d ≠ p.getVert (p.length - d) := by
    intro heq
    have := hp.isPath.getVert_injOn (show d ≤ p.length by omega)
      (Nat.sub_le _ _) heq
    omega
  have hclique (j : ℕ) (hj : j = d ∨ j = p.length - d) :
      G.IsClique (↑(insert (p.getVert j) S) : Set V) := by
    have hjd : d ≤ j := by rcases hj with rfl | rfl <;> omega
    have hjL : j ≤ p.length := by rcases hj with rfl | rfl <;> omega
    have hxj : G.Adj x (p.getVert j) := by
      have hm : j - 1 ∈ startNeighborIndices p := by
        rw [hA]
        rcases hj with rfl | rfl
        · exact mem_insert_of_mem (mem_range.mpr (by omega))
        · exact mem_insert_self _ _
      have h := (mem_filter.mp hm).2
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
    have hattach (a : V) (ha : a ∈ S) : G.Adj a (p.getVert j) := by
      obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
      exact (low_core_initial_segment_twins hG hu hconn p hp hlong
        (show d ≤ p.length by omega) hbefore r (mem_range.mp hr) j hjd hjL).mpr hxj
    intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | haS
    · rcases mem_insert.mp hb with rfl | hbS
      · exact (hab rfl).elim
      · exact (hattach b hbS).symm
    · rcases mem_insert.mp hb with rfl | hbS
      · exact hattach a haS
      · obtain ⟨r, hr, rfl⟩ := mem_image.mp haS
        obtain ⟨s, hs, rfl⟩ := mem_image.mp hbS
        exact low_core_initial_segment_clique hG hu hconn p hp hlong
          (show d ≤ p.length by omega) hbefore r (mem_range.mp hr) s
          (mem_range.mp hs).le (fun heq ↦ hab (congrArg p.getVert heq))
  have hclosed := low_core_two_attachment_initial_closed hG hu hconn p hp hd hlen hA hB
  rcases universal_at_two_attachments hG hu p hp.isPath hlen hA hB with hua | hub
  · refine ⟨S, p.getVert (p.length - d), hScard, hua ▸ hnotS d le_rfl (by omega),
      ?_, hnotS _ (by omega) (by omega), hclique _ (Or.inr rfl), ?_⟩
    · rw [hua]
      exact hatne.symm
    · intro a ha b hab
      obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
      simpa only [hua] using hclosed r (mem_range.mp hr) b hab
  · refine ⟨S, p.getVert d, hScard, hub ▸ hnotS _ (by omega) (by omega),
      ?_, hnotS d le_rfl (by omega), hclique _ (Or.inl rfl), ?_⟩
    · rw [hub]
      exact hatne
    · intro a ha b hab
      obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
      simpa only [hub, or_left_comm, or_comm, or_assoc] using hclosed r (mem_range.mp hr) b hab

/-- Transfer a clique attached through the cone vertex and one other
vertex to an ordinary pendant clique in the base graph. -/
theorem cone_pendant_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {S : Finset (Option V)} {v : Option V} {d : ℕ}
    (hS : S.card = d) (hu : none ∉ S) (hv : v ≠ none) (hvS : v ∉ S)
    (hclique : (graphCone G).IsClique (↑(insert v S) : Set (Option V)))
    (hclosed : ∀ a ∈ S, ∀ b, (graphCone G).Adj a b → b ∈ S ∨ b = none ∨ b = v) :
    ∃ (T : Finset V) (w : V), T.card = d ∧ w ∉ T ∧ G.IsClique (↑(insert w T) : Set V) ∧
      (∀ a ∈ T, ∀ b, G.Adj a b → b ∈ T ∨ b = w) := by
  classical
  obtain ⟨w, rfl⟩ := Option.ne_none_iff_exists'.mp hv
  let T := univ.filter fun a ↦ some a ∈ S
  have hmem (a : V) : a ∈ T ↔ some a ∈ S := by simp only [T, mem_filter, mem_univ, true_and]
  have himage : T.image some = S := by
    ext a
    cases a with
    | none => simp [hu]
    | some a => simp only [mem_image, Option.some.injEq]; exact exists_eq_right.trans (hmem a)
  have hTcard : T.card = d := by
    have hc := congrArg Finset.card himage
    rw [card_image_of_injective _ (Option.some_injective V), hS] at hc
    exact hc
  refine ⟨T, w, hTcard, fun hw ↦ hvS ((hmem w).mp hw), ?_, ?_⟩
  · intro a ha b hb hab
    change (graphCone G).Adj (some a) (some b)
    apply hclique
    · rcases mem_insert.mp ha with rfl | ha
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem ((hmem a).mp ha)
    · rcases mem_insert.mp hb with rfl | hb
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem ((hmem b).mp hb)
    · exact (Option.some_injective V).ne hab
  · intro a ha b hab
    rcases hclosed (some a) ((hmem a).mp ha) (some b) hab with hb | hb | hb
    · exact Or.inl ((hmem b).mpr hb)
    · exact (Option.some_ne_none b hb).elim
    · exact Or.inr (Option.some.inj hb)

theorem even_path_bound_of_two_attachment_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 3 ≤ d)
    (hn : 2 * d + 2 ≤ Fintype.card V) (hconn : G.Preconnected)
    (hfree : ¬pathGraph (2 * d + 2) ⊑ G) {x y : Option V}
    (p : (graphCone G).Walk x y)
    (hp : IsLongestSetPath (vertexCore (graphCone G) d : Set (Option V)) p)
    (hlen : 2 * d + 2 ≤ p.length)
    (hA : startNeighborIndices p = insert (p.length - d - 1) (range d))
    (hB : endNeighborIndices p = insert d (Ico (p.length - d) p.length)) :
    G.edgeFinset.card ≤ pathFormula (Fintype.card V) (2 * d + 2) := by
  have hG : NoLongCycle (graphCone G) (2 * d + 3) :=
    no_long_cycle_cone_of_path_free G (by omega) hfree
  obtain ⟨S, v, hS, hu, hv, hvS, hc, hclosed⟩ := low_core_two_attachment_pendant hG
    (graphCone_universal G) (graphCone_delete_preconnected G hconn) p hp (by omega) hlen hA hB
  obtain ⟨T, w, hT, hw, hclique, hclosed⟩ := cone_pendant_clique G hS hu hv hvS hc hclosed
  exact even_path_bound_of_pendant_clique G hconn hd hn hT hw hclique hclosed hfree

end Erdos1105

#print axioms Erdos1105.even_path_bound_of_two_attachment_core

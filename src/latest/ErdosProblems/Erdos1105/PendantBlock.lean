import ErdosProblems.Erdos1105.CliquePendant
import ErdosProblems.Erdos1105.EvenRootedCount

namespace Erdos1105

open SimpleGraph Finset

/-- A walk avoiding the sole boundary vertex cannot cross a closed set. -/
lemma walk_mem_iff_of_closed_except {V : Type*} {G : SimpleGraph V} {S : Finset V} {v : V}
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y = v)
    {a b : V} (p : G.Walk a b) (havoid : v ∉ p.support) :
    ∀ w ∈ p.support, w ∈ S ↔ a ∈ S := by
  induction p with
  | nil => simp
  | @cons a b z h q ih =>
    have ha : a ≠ v := by
      intro heq
      exact havoid (heq ▸ (Walk.cons h q).start_mem_support)
    have hqavoid : v ∉ q.support := fun hv ↦ havoid (List.mem_cons_of_mem a hv)
    have hb : b ≠ v := fun heq ↦ hqavoid (heq ▸ q.start_mem_support)
    have hba : b ∈ S ↔ a ∈ S :=
      ⟨fun hbS ↦ (hclosed b hbS a h.symm).resolve_right ha,
       fun haS ↦ (hclosed a haS b h).resolve_right hb⟩
    intro w hw
    rcases List.mem_cons.mp hw with heq | hwq
    · subst w
      rfl
    · exact (ih hqavoid w hwq).trans hba

/-- A pendant clique of order `d+1` forces all paths starting at its
attachment vertex to have length at most `d` in a `P_(2*d+2)`-free graph. -/
theorem rooted_path_bound_of_pendant_clique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {S : Finset V} {v : V} {d : ℕ}
    (hd : 2 ≤ d) (hS : S.card = d) (hv : v ∉ S)
    (hclique : G.IsClique (↑(insert v S) : Set V))
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y = v)
    (hfree : ¬pathGraph (2 * d + 2) ⊑ G) :
    ∀ w, ∀ p : G.Walk v w, p.IsPath → p.length ≤ d := by
  classical
  intro w p hp
  cases p with
  | nil => simp
  | @cons _ b z hvb q =>
    have hpath := (Walk.cons_isPath_iff _ _).mp hp
    have hconst := walk_mem_iff_of_closed_except hclosed q hpath.2
    by_cases hb : b ∈ S
    · have hsub : q.support.toFinset ⊆ S := by
        intro t ht
        exact (hconst t (List.mem_toFinset.mp ht)).mpr hb
      have hc := card_le_card hsub
      rw [List.toFinset_card_of_nodup hpath.1.support_nodup, Walk.length_support, hS] at hc
      simpa only [Walk.length_cons] using hc
    · have havoidS : ∀ t ∈ (Walk.cons hvb q).support, t ∉ S := by
        intro t ht
        rcases List.mem_cons.mp ht with heq | htq
        · exact heq ▸ hv
        · exact fun htS ↦ hb ((hconst t htq).mp htS)
      obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < S.card)
      have hcard : (insert v S).card = d + 1 := by rw [card_insert_of_notMem hv, hS]
      obtain ⟨r, hr, hrlen, hrsupp⟩ := clique_spanning_path G hclique
        (by omega) (mem_insert_self v S) (mem_insert_of_mem ha) (fun h ↦ hv (h ▸ ha))
      have hpr : ((Walk.cons hvb q).reverse.append r).IsPath := by
        apply isPath_append_of_inter_eq_end hp.reverse hr
        intro t htp htr
        have ht : t ∈ (Walk.cons hvb q).support := by
          simpa only [Walk.support_reverse, List.mem_reverse] using htp
        have htS := (hrsupp t).mp htr
        exact (mem_insert.mp htS).resolve_right (havoidS t ht)
      have hlen := path_length_lt_of_path_free hfree
        ((Walk.cons hvb q).reverse.append r) hpr
      simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons] at hlen ⊢
      omega

theorem even_path_bound_of_pendant_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected)
    {S : Finset V} {v : V} {l : ℕ} (hl : 3 ≤ l) (hn : 2 * l + 2 ≤ Fintype.card V)
    (hS : S.card = l) (hv : v ∉ S) (hclique : G.IsClique (↑(insert v S) : Set V))
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y = v)
    (hfree : ¬pathGraph (2 * l + 2) ⊑ G) :
    G.edgeFinset.card ≤ pathFormula (Fintype.card V) (2 * l + 2) :=
  even_path_bound_of_rooted_path_bound G hconn v hl hn
    (rooted_path_bound_of_pendant_clique G (by omega) hS hv hclique hclosed hfree)

end Erdos1105

#print axioms Erdos1105.even_path_bound_of_pendant_clique

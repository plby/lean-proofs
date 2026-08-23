import ErdosProblems.Erdos1105.BetweenCounting
import ErdosProblems.Erdos1105.DenseBipartiteSelection
import ErdosProblems.Erdos1105.DenseBipartiteCycle
import ErdosProblems.Erdos1105.RainbowCycleExtension
import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

open SimpleGraph Finset

/-- The even-path upper bound for a representative contained in
`H(n,2l+1,l)`: equivalently, it has a vertex cover of size `l`. -/
theorem even_path_vertex_cover_bound {V C : Type*} [Fintype V] [DecidableEq V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V) [DecidableRel R.Adj]
    (hrainbow : Set.InjOn (extendColor c) R.edgeSet) {l : ℕ} (hl : 2 ≤ l)
    (hn : 2 * l + 2 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph (2 * l + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (A : Finset V) (hA : A.card = l) (hcover : ∀ x y, R.Adj x y → x ∈ A ∨ y ∈ A) :
    R.edgeFinset.card ≤ pathFormula (Fintype.card V) (2 * l + 2) := by
  classical
  by_contra! hhigh
  have hedge := vertex_cover_edge_bound R A hcover
  have hlinear : (l - 1).choose 2 + (l - 1) * (Fintype.card V - l + 1) + 2 < R.edgeFinset.card :=
    (le_max_right _ _).trans_lt (by simpa only [pathFormula_even] using hhigh)
  have hchoose : l.choose 2 = (l - 1).choose 2 + (l - 1) := by
    have h := Nat.choose_succ_succ (l - 1) 1
    simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.choose_one_right,
      Nat.sub_add_cancel (by omega : 1 ≤ l), Nat.add_comm] using h
  have hY : Aᶜ.card = Fintype.card V - l := by rw [card_compl, hA]
  have hsum : (l - 1) * Aᶜ.card + 3 ≤ ∑ y ∈ Aᶜ, degreeWithin R A y := by
    rw [hA, hchoose] at hedge
    rw [hY]
    nlinarith
  obtain ⟨y, hy, hfy, B, hBY, hB, hsumB⟩ := exists_full_degree_and_dense_subset
    (degreeWithin R A) hl Aᶜ (by rw [hY]; omega)
    (fun v _ ↦ (degreeWithin_le_card R A v).trans_eq hA) hsum
  have hBAc : B ⊆ Aᶜ := hBY.trans (erase_subset _ _)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    exact fun x hx hxb ↦ mem_compl.mp (hBAc hxb) hx
  let G := R.between (A : Set V) (B : Set V)
  have hbip : G.IsBipartiteWith (A : Set V) (B : Set V) :=
    R.between_isBipartiteWith (Set.disjoint_left.mpr (fun x hx hxb ↦
      Finset.disjoint_left.mp hAB hx hxb))
  have hGcount : (A.card - 1) * A.card + 2 ≤ G.edgeFinset.card := by
    rw [between_edge_count R hAB, hA]
    exact hsumB
  obtain ⟨u, p, hp, hplen, hsupport⟩ := cycle_of_dense_bipartite_parts G hbip
    (by omega) (hA.trans hB.symm) hGcount
  have hsub : ∀ e ∈ p.edges, e ∈ R.edgeSet :=
    fun e he ↦ edgeSet_mono between_le (p.edges_subset_edgeSet he)
  let q := p.transfer R hsub
  have hq : q.IsCycle := hp.transfer hsub
  have hyout : y ∉ q.support := by
    intro h
    have hABmem := (hsupport y).mp (by simpa only [q, Walk.support_transfer] using h)
    rcases mem_union.mp hABmem with hya | hyB
    · exact mem_compl.mp hy hya
    · exact (mem_erase.mp (hBY hyB)).1 rfl
  have hzex : ∃ z ∈ Aᶜ, z ∉ insert y B := by
    by_contra h
    push Not at h
    have hc := (card_le_card (show Aᶜ ⊆ insert y B from h)).trans (card_insert_le _ _)
    rw [hY, hB] at hc
    omega
  obtain ⟨z, hz, hzout⟩ := hzex
  have hyz : y ≠ z := fun h ↦ hzout (h ▸ mem_insert_self y B)
  have hzcycle : z ∉ q.support := by
    intro h
    have hABmem := (hsupport z).mp (by simpa only [q, Walk.support_transfer] using h)
    rcases mem_union.mp hABmem with hza | hzB
    · exact mem_compl.mp hz hza
    · exact hzout (mem_insert_of_mem hzB)
  have hyA : ∀ x ∈ (A : Set V), R.Adj y x :=
    all_adj_of_degreeWithin_eq_card R A y (hfy.trans hA.symm)
  have hAsub : (A : Set V) ⊆ {x | x ∈ q.support} := by
    intro x hx
    exact (show x ∈ q.support ↔ x ∈ A ∪ B by
      simpa only [q, Walk.support_transfer] using hsupport x).mpr (mem_union_left _ hx)
  have htwo : ∃ a ∈ (A : Set V), ∃ b ∈ (A : Set V), a ≠ b :=
    Finset.one_lt_card.mp (by omega)
  have hqcover : ∀ d ∈ q.darts, d.fst ∈ (A : Set V) ∨ d.snd ∈ (A : Set V) := by
    intro d hd
    have he : d.edge ∈ q.edges := List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [show q.edges = p.edges from Walk.edges_transfer p hsub] at he
    have hadj : G.Adj d.fst d.snd := p.edges_subset_edgeSet he
    exact hadj.2.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.2)
  obtain ⟨f, hf⟩ := rainbow_path_of_cycle_two_external c hrainbow q hq (A : Set V)
    hAsub htwo hqcover hyout hzcycle hyz hyA
  have hqlen : q.length + 2 = 2 * l + 2 := by
    dsimp only [q]
    rw [Walk.length_transfer, hplen, hA]
  have hfree' : ∀ f : (pathGraph (q.length + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rwa [hqlen]
  exact hfree' f hf

end Erdos1105

#print axioms Erdos1105.even_path_vertex_cover_bound

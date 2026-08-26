import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Extra colouring lemmas used by Brooks

These lemmas are not yet in mathlib `master` (as of the pin used by this project). They support
Rabern's inductive proof: deleting a low-degree vertex, and the greedy `Δ+1` bound.
-/

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

/-- If deleting a vertex `v` leaves an `n`-colorable graph and `v` has fewer than `n` neighbors,
then `G` itself is `n`-colorable: color `G` with `v` removed, then give `v` one of the colors that
does not appear on any neighbor of `v`. -/
theorem Colorable.of_induce_compl_singleton {v : V} [Fintype (G.neighborSet v)]
    (h : (G.induce {v}ᶜ).Colorable n) (hv : G.degree v < n) : G.Colorable n := by
  classical
  obtain ⟨C⟩ := h
  have : NeZero n := ⟨by lia⟩
  -- Extend `C` to all of `V`; the color it assigns to `v` itself is irrelevant.
  obtain ⟨f, hf⟩ : ∃ f : V → Fin n, ∀ (u : V) (hu : u ≠ v),
      f u = C ⟨u, Set.mem_compl_singleton_iff.2 hu⟩ :=
    ⟨fun u => if hu : u = v then 0 else C ⟨u, Set.mem_compl_singleton_iff.2 hu⟩,
      fun _ hu => dif_neg hu⟩
  -- As `v` has fewer than `n` neighbors, some color `a` is unused on them.
  obtain ⟨a, ha⟩ : ∃ a, a ∉ (G.neighborFinset v).image f := by
    have hlt : ((G.neighborFinset v).image f).card < n := by
      refine lt_of_le_of_lt Finset.card_image_le ?_
      rwa [card_neighborFinset_eq_degree]
    obtain ⟨a, ha⟩ : (((G.neighborFinset v).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  have key : ∀ {q : V}, G.Adj v q → Function.update f v a v ≠ Function.update f v a q := by
    intro q hq
    rw [Function.update_self, Function.update_of_ne (G.ne_of_adj hq).symm]
    intro hc
    apply ha
    rw [hc]
    exact Finset.mem_image_of_mem f ((G.mem_neighborFinset v q).2 hq)
  have hvalid : ∀ {x y : V}, G.Adj x y →
      Function.update f v a x ≠ Function.update f v a y := by
    intro x y hxy
    rcases eq_or_ne x v with hx | hx
    · rw [hx] at hxy ⊢
      exact key hxy
    rcases eq_or_ne y v with hy | hy
    · rw [hy] at hxy ⊢
      exact (key hxy.symm).symm
    rw [Function.update_of_ne hx, Function.update_of_ne hy, hf x hx, hf y hy]
    exact C.valid hxy
  exact ⟨Coloring.mk (Function.update f v a) hvalid⟩

/-! ### Greedy coloring

A greedy coloring is built by coloring the vertices one at a time, giving each new vertex a color
that is missing from its already-colored neighbors. `Colorable.of_induce_insert` is the single
step of this process, and `colorable_maxDegree_succ` is the resulting bound.
-/

/-- The greedy step: if `G` restricted to `s` is `n`-colorable and `v` has fewer than `n` neighbors
*inside* `s`, then `G` restricted to `insert v s` is `n`-colorable. Note that only the neighbors of
`v` that are already colored are counted, so `v` may well have `n` or more neighbors in total. -/
theorem Colorable.of_induce_insert [DecidableEq V] {s : Finset V} {v : V}
    [Fintype (G.neighborSet v)] (h : (G.induce (↑s : Set V)).Colorable n)
    (hlt : (G.neighborFinset v ∩ s).card < n) :
    (G.induce (↑(insert v s) : Set V)).Colorable n := by
  classical
  obtain ⟨C⟩ := h
  have : NeZero n := ⟨by lia⟩
  -- Spread `C` out to a total function; its values outside `s` are irrelevant.
  obtain ⟨f, hf⟩ : ∃ f : V → Fin n, ∀ (u : V) (hu : u ∈ s), f u = C ⟨u, hu⟩ :=
    ⟨fun u => if hu : u ∈ s then C ⟨u, hu⟩ else 0, fun _ hu => dif_pos hu⟩
  -- As `v` has fewer than `n` neighbors in `s`, some color `a` is unused on them.
  obtain ⟨a, ha⟩ : ∃ a, a ∉ (G.neighborFinset v ∩ s).image f := by
    have hcard : ((G.neighborFinset v ∩ s).image f).card < n :=
      lt_of_le_of_lt Finset.card_image_le hlt
    obtain ⟨a, ha⟩ : (((G.neighborFinset v ∩ s).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  have hfree : ∀ w, G.Adj v w → w ∈ s → f w ≠ a := fun w hw hws hc =>
    ha (hc ▸ Finset.mem_image_of_mem f
      (Finset.mem_inter.2 ⟨(G.mem_neighborFinset v w).2 hw, hws⟩))
  refine ⟨Coloring.mk (fun u => if u.1 = v then a else f u.1) ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
  have hadj : G.Adj x y := hxy
  rcases eq_or_ne x v with hxv | hxv
  · rcases eq_or_ne y v with hyv | hyv
    · exact absurd (hxv.trans hyv.symm) hadj.ne
    · rw [if_pos hxv, if_neg hyv]
      exact (hfree y (hxv ▸ hadj) (hy.resolve_left hyv)).symm
  · rcases eq_or_ne y v with hyv | hyv
    · rw [if_neg hxv, if_pos hyv]
      exact hfree x (hyv ▸ hadj.symm) (hx.resolve_left hxv)
    · rw [if_neg hxv, if_neg hyv, hf x (hx.resolve_left hxv), hf y (hy.resolve_left hyv)]
      exact C.valid hadj

/-- Every finite induced subgraph of `G` is `(G.maxDegree + 1)`-colorable, by greedily adding one
vertex at a time. -/
theorem colorable_induce_maxDegree_succ [Fintype V] [DecidableRel G.Adj] (s : Finset V) :
    (G.induce (↑s : Set V)).Colorable (G.maxDegree + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty]
    exact .of_isEmpty _
  | insert a s _ ih =>
    refine ih.of_induce_insert ?_
    calc (G.neighborFinset a ∩ s).card
        ≤ (G.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
      _ = G.degree a := card_neighborFinset_eq_degree ..
      _ < G.maxDegree + 1 := Nat.lt_succ_of_le (G.degree_le_maxDegree a)

variable (G) in
/-- **Greedy coloring bound**: a finite graph is `(G.maxDegree + 1)`-colorable, since when a vertex
is colored it has at most `G.maxDegree` neighbors, so some color is still available for it. -/
theorem colorable_maxDegree_succ [Fintype V] [DecidableRel G.Adj] :
    G.Colorable (G.maxDegree + 1) := by
  have h := colorable_induce_maxDegree_succ (G := G) Finset.univ
  rw [Finset.coe_univ] at h
  exact (colorable_congr G.induceUnivIso).1 h

variable (G) in
/-- **Greedy coloring bound**, stated for the chromatic number. -/
theorem chromaticNumber_le_maxDegree_succ [Fintype V] [DecidableRel G.Adj] :
    G.chromaticNumber ≤ G.maxDegree + 1 := by
  simpa using G.colorable_maxDegree_succ.chromaticNumber_le


end SimpleGraph

import ErdosProblems.Erdos1105.PrivateNeighbors
import ErdosProblems.Erdos1105.PrivatePaths
import ErdosProblems.Erdos1105.OrePath

namespace Erdos1105

open SimpleGraph

/-- If the endpoint private-color counts exceed the degrees on a path,
one of its endpoints has a privately colored representative edge leaving it. -/
theorem private_extension_of_path_no_cycle {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (hfree : ¬cycleGraph (p.length + 1) ⊑ R.induce {v | v ∈ p.support})
    (hnew : p.length + 1 ≤ (privateColors c x).card + (privateColors c y).card) :
    (∃ w, ∃ hw : R.Adj x w, w ∉ p.support ∧ PrivateAt c x (c ⟨s(x, w), hw.ne⟩)) ∨
    (∃ w, ∃ hw : R.Adj y w, w ∉ p.support ∧ PrivateAt c y (c ⟨s(y, w), hw.ne⟩)) := by
  classical
  have hdeg :
      (R.induce {v | v ∈ p.support}).degree ⟨x, p.start_mem_support⟩ +
      (R.induce {v | v ∈ p.support}).degree ⟨y, p.end_mem_support⟩ < p.length + 1 := by
    by_contra! h
    exact hfree (cycle_contained_in_support_of_path_endpoint_degree_sum R p hp hlen h)
  by_cases hx : Nat.card ((R.induce {v | v ∈ p.support}).neighborSet
      ⟨x, p.start_mem_support⟩) < (privateColors c x).card
  · exact Or.inl (exists_private_neighbor_outside c R hpalette _ x p.start_mem_support hx)
  · have hy : Nat.card ((R.induce {v | v ∈ p.support}).neighborSet
        ⟨y, p.end_mem_support⟩) < (privateColors c y).card := by
      simp only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hx ⊢
      omega
    exact Or.inr (exists_private_neighbor_outside c R hpalette _ y p.end_mem_support hy)

/-- A path with a final inward-private edge traps every private neighbor
of its first vertex. Otherwise a second inward-private endpoint would
give a rainbow cycle. -/
theorem private_neighbors_trapped_by_inward_end {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : 1 ≤ p.length) (hnil : ¬p.Nil)
    (hlast : PrivateAt c p.penultimate
      (c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩))
    (hH : ∀ f : (cycleGraph (p.length + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (w : V) (hw : R.Adj x w) (hpriv : PrivateAt c x (c ⟨s(x, w), hw.ne⟩)) :
    w ∈ p.support := by
  by_contra hnot
  let q := Walk.cons hw.symm p
  have hq : q.IsPath := (Walk.cons_isPath_iff hw.symm p).mpr ⟨hp, hnot⟩
  have hqnil : ¬q.Nil := Walk.not_nil_cons
  have hqfirst : PrivateAt c q.snd (c ⟨s(w, q.snd), (q.adj_snd hqnil).ne⟩) := by
    simpa only [q, Walk.snd_cons, Sym2.eq_swap] using hpriv
  have hqlast : PrivateAt c q.penultimate
      (c ⟨s(q.penultimate, y), (q.adj_penultimate hqnil).ne⟩) := by
    simpa only [q, Walk.penultimate_cons_of_not_nil hw.symm p hnil] using hlast
  have hqH : ∀ f : (cycleGraph (q.length + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    simpa only [q, Walk.length_cons, Nat.add_assoc] using hH
  exact private_inward_path_impossible c R hR howned q hq
    (by simp only [q, Walk.length_cons]; omega) hqnil hqfirst hqlast hqH

/-- The preceding extension can always be oriented to put its new
privately colored edge at the end, private to the interior endpoint. -/
theorem exists_path_with_inward_end {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (hfree : ¬cycleGraph (p.length + 1) ⊑ R.induce {v | v ∈ p.support})
    (hnew : p.length + 1 ≤ (privateColors c x).card + (privateColors c y).card) :
    ∃ a b, ∃ q : R.Walk a b, q.IsPath ∧ q.length = p.length + 1 ∧
      ∃ hnil : ¬q.Nil, PrivateAt c q.penultimate
        (c ⟨s(q.penultimate, b), (q.adj_penultimate hnil).ne⟩) := by
  obtain h | h := private_extension_of_path_no_cycle c R hpalette p hp hlen hfree hnew
  · obtain ⟨w, hw, hnot, hpriv⟩ := h
    let q := p.reverse.concat hw
    have hqnil : ¬q.Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.length_concat]
      omega
    refine ⟨y, w, q, hp.reverse.concat (by simpa only [Walk.support_reverse, List.mem_reverse] using hnot) hw,
      ?_, hqnil, ?_⟩
    · simp only [q, Walk.length_concat, Walk.length_reverse]
    · simpa only [q, Walk.penultimate_concat] using hpriv
  · obtain ⟨w, hw, hnot, hpriv⟩ := h
    let q := p.concat hw
    have hqnil : ¬q.Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.length_concat]
      omega
    refine ⟨x, w, q, hp.concat hnot hw, Walk.length_concat p hw, hqnil, ?_⟩
    simpa only [q, Walk.penultimate_concat] using hpriv

end Erdos1105

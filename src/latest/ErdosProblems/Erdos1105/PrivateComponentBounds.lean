import ErdosProblems.Erdos1105.LongPrivatePaths
import ErdosProblems.Erdos1105.CanonicalPath

namespace Erdos1105

open SimpleGraph

/-- Private colors at a vertex are represented by distinct neighbors in
its own connected component. -/
theorem private_colors_le_component_degree {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    [DecidableRel R.Adj]
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (B : R.ConnectedComponent) [Fintype B] [DecidableRel B.toSimpleGraph.Adj] (v : B) :
    (privateColors c v.val).card ≤ B.toSimpleGraph.degree v := by
  have h := private_colors_le_induced_neighbors c R hpalette B.supp v.val v.property
    (fun w hw _ ↦ B.mem_supp_of_adj_mem_supp v.property hw)
  have heq : Nat.card ((R.induce B.supp).neighborSet ⟨v.val, v.property⟩) =
      B.toSimpleGraph.degree v := by
    change Nat.card (B.toSimpleGraph.neighborSet v) = _
    rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  exact h.trans_eq heq

/-- The private representative components have at most `k-1` vertices. -/
theorem private_component_card_le {V C : Type*} [Fintype V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B : R.ConnectedComponent) : Nat.card B ≤ n + 3 := by
  classical
  let := Fintype.ofFinite B
  by_contra! hlarge
  have hcount := private_colors_le_component_degree c R hpalette B
  have hmin (v : B) : 2 ≤ B.toSimpleGraph.degree v := (hnew v.val).trans (hcount v)
  have hdeg (u v : B) (hne : u ≠ v) :
      n + 3 ≤ B.toSimpleGraph.degree u + B.toSimpleGraph.degree v :=
    (hsum u.val v.val (fun h ↦ hne (Subtype.ext h))).trans (Nat.add_le_add (hcount u) (hcount v))
  have hcopy : pathGraph (n + 4) ⊑ B.toSimpleGraph :=
    path_contained_of_degree_sum B.toSimpleGraph B.connected_toSimpleGraph (n + 4)
      (by omega) (by simp only [Nat.card_eq_fintype_card] at hlarge; omega) hmin hdeg
  obtain ⟨f⟩ := hcopy
  let g := (Copy.induce R B.supp).comp f
  let p := (canonicalPath (n + 3)).map g.toHom
  have hp : p.IsPath := (canonicalPath_isPath _).map g.injective
  have hlt := private_path_length_lt c hc hH R hR howned hpalette hnew hsum p hp
  have hlen : p.length = n + 3 := by simp [p]
  omega

/-- Each component is Hamiltonian and its size is at least `(k+1)/2`.
This completes the component-size claim used by the cycle upper bound. -/
theorem private_component_hamiltonian_and_card {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) [DecidableRel R.Adj] (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B : R.ConnectedComponent) [Fintype B] :
    B.toSimpleGraph.IsHamiltonian ∧ n + 5 ≤ 2 * Nat.card B ∧ Nat.card B ≤ n + 3 := by
  classical
  have hcard := private_component_card_le c hc hH R hR howned hpalette hnew hsum B
  have hcount := private_colors_le_component_degree c R hpalette B
  obtain ⟨u⟩ := B.connected_toSimpleGraph.nonempty
  have hmin : 2 ≤ B.toSimpleGraph.degree u := (hnew u.val).trans (hcount u)
  have hcard₃ : 3 ≤ Fintype.card B := by
    have hlt := B.toSimpleGraph.degree_lt_card_verts u
    omega
  have hdeg (u v : B) (hne : u ≠ v) :
      n + 3 ≤ B.toSimpleGraph.degree u + B.toSimpleGraph.degree v :=
    (hsum u.val v.val (fun h ↦ hne (Subtype.ext h))).trans (Nat.add_le_add (hcount u) (hcount v))
  have hham : B.toSimpleGraph.IsHamiltonian :=
    hamiltonian_of_distinct_degree_sum B.toSimpleGraph hcard₃ (by
      intro a b hab
      simpa only [Nat.card_eq_fintype_card] using hcard.trans (hdeg a b hab))
  refine ⟨hham, ?_, hcard⟩
  have hex : ∃ v : B, v ≠ u := by
      have : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      exact exists_ne u
  obtain ⟨v, hv⟩ := hex
  have hsumuv := hdeg u v hv.symm
  have hu := B.toSimpleGraph.degree_lt_card_verts u
  have hv := B.toSimpleGraph.degree_lt_card_verts v
  rw [Nat.card_eq_fintype_card]
  omega

#print axioms private_component_card_le
#print axioms private_component_hamiltonian_and_card

end Erdos1105

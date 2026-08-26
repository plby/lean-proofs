import ErdosProblems.Erdos19.RoundRobin

/-! # Round-robin matchings inside a chosen auxiliary clique -/

namespace Erdos19

open _root_.SimpleGraph

theorem exists_roundRobin_family {V : Type*} (G : _root_.SimpleGraph V) (t : ℕ)
    (f : Fin (2 * t + 1) ↪ V)
    (hclique : ∀ x y, x ≠ y → G.Adj (f x) (f y)) :
    ∃ P : Fin (2 * t + 1) → G.Subgraph,
      (∀ i, (P i).IsMatching ∧ (P i).verts = Set.range f \ {f i}) ∧
      Pairwise (fun i j ↦ Disjoint (P i).spanningCoe (P j).spanningCoe) ∧
      (∀ x ∈ Set.range f, ∀ y ∈ Set.range f, x ≠ y → ∃ i, (P i).Adj x y) := by
  letI : NeZero (2 * t + 1) := ⟨by omega⟩
  let e := (ZMod.finEquiv (2 * t + 1)).toEquiv
  let hom : (⊤ : _root_.SimpleGraph (ZMod (2 * t + 1))) →g G :=
    { toFun := fun x ↦ f (e.symm x)
      map_rel' := fun h ↦ hclique _ _ (fun heq ↦ h (e.symm.injective heq)) }
  have hinj : Function.Injective hom := f.injective.comp e.symm.injective
  let P : Fin (2 * t + 1) → G.Subgraph := fun i ↦ (roundRobinMatching t (e i)).map hom
  have hverts : ∀ i, (P i).verts = Set.range f \ {f i} := by
    intro i
    rw [Subgraph.map_verts, roundRobinMatching_verts]
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨e.symm x, rfl⟩, ?_⟩
      intro heq
      have h : e.symm x = i := f.injective heq
      exact hx ((e.apply_symm_apply x).symm.trans (congrArg e h))
    · rintro ⟨⟨x, rfl⟩, hx⟩
      refine ⟨e x, ?_, ?_⟩
      · intro heq
        exact hx (congrArg f (e.injective heq))
      · exact congrArg f (e.symm_apply_apply x)
  have hmatching : ∀ i, (P i).IsMatching := fun i ↦
    (roundRobinMatching_isMatching t (e i)).map hom hinj
  refine ⟨P, fun i ↦ ⟨hmatching i, hverts i⟩, ?_, ?_⟩
  · intro i j hij
    apply _root_.SimpleGraph.disjoint_left.mpr
    intro x y hixy hjxy
    obtain ⟨a, b, hab, hax, hby⟩ := hixy
    obtain ⟨c, d, hcd, hcx, hdy⟩ := hjxy
    have hac := hinj (hax.trans hcx.symm)
    have hbd := hinj (hby.trans hdy.symm)
    subst c
    subst d
    exact _root_.SimpleGraph.disjoint_left.mp
      (roundRobinMatching_pairwise_disjoint t (fun h ↦ hij (e.injective h))) a b hab hcd
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ hab
    have heab : e a ≠ e b := fun h ↦ hab (congrArg f (e.injective h))
    obtain ⟨j, hj⟩ := roundRobinMatching_covers_edges t (e a) (e b) heab
    refine ⟨e.symm j, e a, e b, ?_, ?_, ?_⟩
    · simpa only [e.apply_symm_apply] using hj
    · exact congrArg f (e.symm_apply_apply a)
    · exact congrArg f (e.symm_apply_apply b)

#print axioms exists_roundRobin_family

end Erdos19

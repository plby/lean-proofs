import ErdosProblems.Erdos556.UniversalExtension

/-!
# Completing a matching with copies of its uncovered vertices
-/

namespace Erdos556

open SimpleGraph

def matchingCompletion {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) :
    (universalExtension (W := ↥(M.vertsᶜ)) G).Subgraph where
  verts := Set.univ
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => M.Adj u v
    | Sum.inl u, Sum.inr v => u = v.val
    | Sum.inr u, Sum.inl v => u.val = v
    | Sum.inr _, Sum.inr _ => False
  adj_sub := by
    intro x y h
    cases x <;> cases y
    · exact M.adj_sub h
    · exact Sum.inl_ne_inr
    · exact Sum.inr_ne_inl
    · exact h.elim
  edge_vert := fun _ => trivial
  symm := ⟨by intro x y h; cases x <;> cases y
              exacts [h.symm, h.symm, h.symm, h]⟩

theorem matchingCompletion_isPerfectMatching {V : Type*} {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) : (matchingCompletion M).IsPerfectMatching := by
  apply Subgraph.isPerfectMatching_iff.mpr
  intro x
  cases x with
  | inl u =>
    by_cases hu : u ∈ M.verts
    · obtain ⟨v, huv, hvuniq⟩ := hM hu
      refine ⟨Sum.inl v, huv, ?_⟩
      intro y hy
      cases y with
      | inl w => exact congrArg Sum.inl (hvuniq w hy)
      | inr w => exact (w.property (hy ▸ hu)).elim
    · refine ⟨Sum.inr ⟨u, hu⟩, rfl, ?_⟩
      intro y hy
      cases y with
      | inl v => exact (hu (M.edge_vert hy)).elim
      | inr v => exact congrArg Sum.inr (Subtype.ext hy.symm)
  | inr u =>
    refine ⟨Sum.inl u.val, rfl, ?_⟩
    intro y hy
    cases y with
    | inl v => exact congrArg Sum.inl hy.symm
    | inr v => exact hy.elim

theorem subgraphMatching_odd_components_bound {V : Type*} [Finite V]
    {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) (X : Set V) :
    ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard ≤ X.ncard + (M.vertsᶜ).ncard := by
  let Y : Set (V ⊕ ↥(M.vertsᶜ)) := Sum.inl '' X ∪ Set.range Sum.inr
  have hY : ∀ w : ↥(M.vertsᶜ), Sum.inr w ∈ Y := fun w => Or.inr ⟨w, rfl⟩
  have hpre : Sum.inl ⁻¹' Y = X := by ext u; simp [Y]
  have hcard := ncard_sum_set_of_all_inr Y hY
  have hodd := isomorphic_oddComponents_ncard (universalExtension_deleteIso G Y hY)
  rw [hpre] at hodd hcard
  rw [Nat.card_coe_set_eq] at hcard
  have hT := SimpleGraph.not_isTutteViolator_of_isPerfectMatching
    (matchingCompletion_isPerfectMatching M hM) Y
  unfold SimpleGraph.IsTutteViolator at hT
  omega

open scoped Classical in
theorem EdgeMatching.odd_components_bound {V : Type*} [Finite V]
    {G : SimpleGraph V} {F : Finset (Sym2 V)} (hF : EdgeMatching G F) (X : Set V) :
    ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard + 2 * F.card ≤
      X.ncard + Nat.card V := by
  have hh := subgraphMatching_odd_components_bound hF.toSubgraph hF.toSubgraph_isMatching X
  have hs : hF.toSubgraph.verts.ncard = 2 * F.card := by
    change (matchingSupport F : Set V).ncard = _
    rw [Set.ncard_coe_finset, hF.card_support]
  have hsum := Set.ncard_add_ncard_compl hF.toSubgraph.verts
  omega

end Erdos556

import ErdosProblems.Erdos547.ShrubState

/-!
# Inserting a shrub into a partial embedding
-/

namespace Erdos547.ShrubState

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} {C : I → Finset V} {head : ↥P.shrubs → I}
  {seed : (T.induce (P.seeds : Set U)).Copy G}

theorem exists_insert (E : ShrubState P G C head seed)
    (S : ↥P.shrubs) (hS : S ∉ E.placed) (j : I)
    (D : ShrubRootData T P.seeds S.val) (g : (T.induce (S.val : Set U)).Copy G)
    (hfresh : ∀ v, g v ∉ E.occupied)
    (hprimary : G.Adj (seed D.seed) (g D.root))
    (hsecondary : ∀ z, D.second = some z → G.Adj (seed z.1) (g z.2))
    (hnear : ∀ v : ↥S.val, col v.val ≠ P.shrubColour S → g v ∈ C (head S))
    (hfar : ∀ v : ↥S.val, col v.val = P.shrubColour S → g v ∈ C j) :
    ∃ E' : ShrubState P G C head seed,
      E'.placed = insert S E.placed ∧ E'.tail = Function.update E.tail S j ∧
      E.occupied ⊆ E'.occupied ∧
      E'.occupied = E.occupied ∪ Finset.univ.image g := by
  classical
  have himages : ∀ x : ↥(P.shrubDomain E.placed), ∀ y : ↥S.val, E.copy x ≠ g y := by
    intro x y he
    exact hfresh y (he ▸ E.image_mem_occupied x)
  have hp : G.Adj (E.copy (E.seedVertex D.seed)) (g D.root) := by
    rw [show E.copy (E.seedVertex D.seed) = seed D.seed from E.seed_eq _]
    exact hprimary
  have hs : ∀ z, D.second = some z →
      G.Adj (E.copy (E.seedVertex z.1)) (g z.2) := by
    intro z hz
    rw [show E.copy (E.seedVertex z.1) = seed z.1 from E.seed_eq _]
    exact hsecondary z hz
  obtain ⟨f, hold, hnew⟩ := P.extend_copy_by_shrub G (P.shrubDomain E.placed) S.val
    (P.seeds_subset_shrubDomain _) S.property (P.shrubDomain_disjoint hS)
    D E.copy g himages hp hs
  let f' : (T.induce ((P.shrubDomain (insert S E.placed) : Finset U) : Set U)).Copy G := {
    toHom := {
      toFun := fun v ↦ f ⟨v.val, by
        rw [← P.shrubDomain_insert S E.placed]
        exact v.property⟩
      map_rel' := fun hvw ↦ f.toHom.map_adj hvw
    }
    injective' := by
      intro v w hvw
      exact Subtype.ext (congrArg (fun z : ↥(P.shrubDomain E.placed ∪ S.val) ↦ z.val)
        (f.injective hvw))
  }
  have old_agree (v : ↥(P.shrubDomain E.placed))
      (hv : v.val ∈ P.shrubDomain (insert S E.placed)) : f' ⟨v.val, hv⟩ = E.copy v :=
    hold v
  have new_agree (v : ↥S.val)
      (hv : v.val ∈ P.shrubDomain (insert S E.placed)) : f' ⟨v.val, hv⟩ = g v :=
    hnew v
  let E' : ShrubState P G C head seed := {
    placed := insert S E.placed
    tail := Function.update E.tail S j
    copy := f'
    seed_eq := fun v ↦ (old_agree (E.seedVertex v) _).trans (E.seed_eq v)
    near_mem := by
      intro A hA v hv
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rw [new_agree v]
        exact hnear v hv
      · rw [old_agree ⟨v.val, P.shrub_subset_domain hA v.property⟩]
        exact E.near_mem A hA v hv
    far_mem := by
      intro A hA v hv
      by_cases he : A = S
      · subst A
        rw [new_agree v, Function.update_self]
        exact hfar v hv
      · have hA' : A ∈ E.placed := (Finset.mem_insert.mp hA).resolve_left he
        rw [old_agree ⟨v.val, P.shrub_subset_domain hA' v.property⟩, Function.update_of_ne he]
        exact E.far_mem A hA' v hv
  }
  have heq : E'.occupied = E.occupied ∪ Finset.univ.image g := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
      have hx : x.val ∈ P.shrubDomain E.placed ∪ S.val := by
        rw [← P.shrubDomain_insert]
        exact x.property
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨⟨x.val, hx⟩, Finset.mem_univ _, (old_agree ⟨x.val, hx⟩ x.property).symm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨x.val, hx⟩, Finset.mem_univ _, (new_agree ⟨x.val, hx⟩ x.property).symm⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨⟨x.val,
          P.shrubDomain_mono (Finset.subset_insert _ _) x.property⟩,
          Finset.mem_univ _, old_agree x _⟩
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_image.mpr ⟨⟨x.val,
          P.shrub_subset_domain (Finset.mem_insert_self S E.placed) x.property⟩,
          Finset.mem_univ _, new_agree x _⟩
  exact ⟨E', rfl, rfl, heq ▸ Finset.subset_union_left, heq⟩

end Erdos547.ShrubState

#print axioms Erdos547.ShrubState.exists_insert

import Mathlib
import ErdosProblems.Erdos550.RootedTreeAt
import ErdosProblems.Erdos550.TauFineBlockOrder
import ErdosProblems.Erdos550.TauFinePartition

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rooted component blocks for a prescribed seed

If a tree is rooted at a seed, every component left after deleting the seed
set has a unique top vertex: its parent is a seed, while every other parent
link stays inside the component.  This is the ordering fact needed to embed a
whole shrub immediately after its upper seed and to postpone its lower seeds.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The minimum-rank vertex of a nonseed component. -/
noncomputable def rootedComponentTop
    (T : SimpleGraph A) (S : Finset A) (rank : A → ℕ)
    (c : NonseedComponent T S) : A :=
  (componentNonseedVertices T S c.1).exists_min_image rank
    (componentNonseedVertices_nonempty T S c) |>.choose

lemma rootedComponentTop_mem
    (T : SimpleGraph A) (S : Finset A) (rank : A → ℕ)
    (c : NonseedComponent T S) :
    rootedComponentTop T S rank c ∈ componentNonseedVertices T S c.1 :=
  ((componentNonseedVertices T S c.1).exists_min_image rank
    (componentNonseedVertices_nonempty T S c)).choose_spec.1

lemma rootedComponentTop_min
    (T : SimpleGraph A) (S : Finset A) (rank : A → ℕ)
    (c : NonseedComponent T S) :
    ∀ x ∈ componentNonseedVertices T S c.1,
      rank (rootedComponentTop T S rank c) ≤ rank x :=
  ((componentNonseedVertices T S c.1).exists_min_image rank
    (componentNonseedVertices_nonempty T S c)).choose_spec.2

/-- A deleted component lies in the descendant shrub of its minimum-rank
vertex.  This is the convexity of components of a rooted tree. -/
lemma component_subset_shrubF_top
    (T : SimpleGraph A)
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (S : Finset A) (c : NonseedComponent T S) :
    componentNonseedVertices T S c.1 ⊆
      shrubF parent rank (Finset.univ.sup rank) S
        (rootedComponentTop T S rank c) := by
  let v := rootedComponentTop T S rank c
  let M := Finset.univ.sup rank
  have hM : ∀ x, rank x ≤ M :=
    fun x => Finset.le_sup (Finset.mem_univ x)
  have hv : v ∈ componentNonseedVertices T S c.1 := by
    exact rootedComponentTop_mem T S rank c
  have hmin : ∀ x ∈ componentNonseedVertices T S c.1,
      rank v ≤ rank x := by
    exact rootedComponentTop_min T S rank c
  have hclosure :
      ∀ x y, x ∈ shrubF parent rank M S v →
        (seedDeleted T S).Adj x y →
        y ∈ shrubF parent rank M S v := by
    intro x y hx hxy
    have hxy' : T.Adj x y ∧ x ∉ S ∧ y ∉ S :=
      (seedDeleted_adj_iff T S x y).mp hxy
    rcases hedge x y hxy'.1 with hpar | hpar
    · by_cases hxv : x = v
      · subst x
        have hyc : y ∈ componentNonseedVertices T S c.1 := by
          rw [mem_componentNonseedVertices_iff]
          refine ⟨hxy'.2.2, ?_⟩
          have hvc : v ∈ c.1.supp :=
            (mem_componentNonseedVertices_iff T S c.1 v).mp hv |>.2
          exact c.1.mem_supp_of_adj_mem_supp hvc hxy
        exact False.elim
          ((not_lt_of_ge (hmin y hyc)) (hrank v y hpar))
      · exact shrubF_parent_mem parent rank M S hrank hM
          v x y hx hxv hpar
    · apply shrubF_trans parent rank M S hrank hM v x hx
      rw [mem_shrubF]
      exact Or.inr ⟨y,
        ⟨hpar, hrank y x hpar, hM y, hxy'.2.2⟩,
        (mem_shrubF parent rank M S y y).2 (Or.inl rfl)⟩
  intro w hw
  have hvSupp : v ∈ c.1.supp :=
    (mem_componentNonseedVertices_iff T S c.1 v).mp hv |>.2
  have hwSupp : w ∈ c.1.supp :=
    (mem_componentNonseedVertices_iff T S c.1 w).mp hw |>.2
  have hvw : (seedDeleted T S).Reachable v w := by
    exact c.1.reachable_of_mem_supp hvSupp hwSupp
  have hvw' :
      Relation.ReflTransGen (seedDeleted T S).Adj v w :=
    ((seedDeleted T S).reachable_iff_reflTransGen v w).mp hvw
  have hwalk :
      ∀ {x y}, Relation.ReflTransGen (seedDeleted T S).Adj x y →
        x ∈ shrubF parent rank M S v →
        y ∈ shrubF parent rank M S v := by
    intro x y hreach hx
    induction hreach with
    | refl => exact hx
    | tail hreach hAdj ih =>
        exact hclosure _ _ ih hAdj
  exact hwalk hvw'
    ((mem_shrubF parent rank M S v v).2 (Or.inl rfl))

/-- Prescribed-root orientation, together with the induced rooted structure on
every deleted component. -/
theorem exists_rooted_component_block_data
    (T : SimpleGraph A) [DecidableRel T.Adj] (hT : T.IsTree)
    (r₀ : A) (S : Finset A) (hrootS : r₀ ∈ S) :
    ∃ (parent : A → Option A) (rank : A → ℕ),
      parent r₀ = none ∧
      (∀ a, parent a = none → a = r₀) ∧
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → T.Adj a b) ∧
      (∀ a b, T.Adj a b →
        parent a = some b ∨ parent b = some a) ∧
      Nonempty (RootedSeedComponentRankData T S parent rank) := by
  obtain ⟨parent, rank, hroot, hrootUnique, hrank, hparentAdj, hedge⟩ :=
    Erdos550.IsTree.exists_rooted_edge_structure_at T hT r₀
  let top : NonseedComponent T S → A :=
    rootedComponentTop T S rank
  have htopMem :
      ∀ c, top c ∈ componentNonseedVertices T S c.1 := by
    exact fun c => rootedComponentTop_mem T S rank c
  have htopParent :
      ∀ c, ∃ s ∈ S, parent (top c) = some s := by
    intro c
    have htopNotS : top c ∉ S :=
      (mem_componentNonseedVertices_iff T S c.1 (top c)).mp
        (htopMem c) |>.1
    cases hp : parent (top c) with
    | none =>
        have : top c = r₀ := hrootUnique _ hp
        exact False.elim (htopNotS (this ▸ hrootS))
    | some p =>
        have hpS : p ∈ S := by
          by_contra hpNotS
          have hpComp : p ∈ componentNonseedVertices T S c.1 := by
            have htopComp :
                nonseedComponentOf T S (top c) htopNotS = c :=
              (mem_indexed_component_iff T S c (top c)).mp
                (htopMem c) |>.choose_spec
            have heq :
                nonseedComponentOf T S p hpNotS =
                  nonseedComponentOf T S (top c) htopNotS :=
              nonseedComponentOf_eq_of_adj T S
                (hparentAdj _ _ hp).symm hpNotS htopNotS
            exact (mem_indexed_component_iff T S c p).2
              ⟨hpNotS, heq.trans htopComp⟩
          exact (not_lt_of_ge
            (rootedComponentTop_min T S rank c p hpComp))
            (hrank _ _ hp)
        exact ⟨p, hpS, rfl⟩
  have hparentInternal :
      ∀ c x, x ∈ componentNonseedVertices T S c.1 →
        x ≠ top c →
        ∃ y ∈ componentNonseedVertices T S c.1,
          parent x = some y := by
    intro c x hx hxtop
    have hxNotS :=
      (mem_componentNonseedVertices_iff T S c.1 x).mp hx |>.1
    cases hp : parent x with
    | none =>
        have : x = r₀ := hrootUnique x hp
        exact False.elim (hxNotS (this ▸ hrootS))
    | some p =>
        have hsub := component_subset_shrubF_top T parent rank
          hrank hparentAdj hedge S c hx
        have hpShrub :
            p ∈ shrubF parent rank (Finset.univ.sup rank) S (top c) :=
          shrubF_parent_mem parent rank (Finset.univ.sup rank) S hrank
            (fun z => Finset.le_sup (Finset.mem_univ z))
            (top c) x p hsub hxtop hp
        have htopNotS : top c ∉ S :=
          (mem_componentNonseedVertices_iff T S c.1 (top c)).mp
            (htopMem c) |>.1
        have hpNotS : p ∉ S :=
          shrubF_mem_notMem_S parent rank (Finset.univ.sup rank) S
            (top c) p htopNotS hpShrub
        have hpComp : p ∈ componentNonseedVertices T S c.1 := by
          have hxComp :
              nonseedComponentOf T S x hxNotS = c :=
            (mem_indexed_component_iff T S c x).mp hx |>.choose_spec
          have heq :
              nonseedComponentOf T S p hpNotS =
                nonseedComponentOf T S x hxNotS :=
            nonseedComponentOf_eq_of_adj T S
              (hparentAdj _ _ hp).symm hpNotS hxNotS
          exact (mem_indexed_component_iff T S c p).2
            ⟨hpNotS, heq.trans hxComp⟩
        exact ⟨p, hpComp, rfl⟩
  exact ⟨parent, rank, hroot, hrootUnique, hrank, hparentAdj, hedge,
    ⟨{
      root := top
      root_mem := htopMem
      root_parent_seed := htopParent
      parent_internal := hparentInternal
      root_rank_min := fun c x hx =>
        rootedComponentTop_min T S rank c x hx
    }⟩⟩

end Erdos550

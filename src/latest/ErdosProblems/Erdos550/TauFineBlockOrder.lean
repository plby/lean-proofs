import Mathlib
import ErdosProblems.Erdos550.SequentialBlockEmbedding
import ErdosProblems.Erdos550.TauFineIndexedData

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Head-singleton and shrub blocks

This is the source-side order used by the direct off--Turán embedding.  Seed
vertices are singleton blocks and every component of `T - S` is one shrub
block.  A rooted component has one upper boundary vertex; all other component
vertices have their parent inside the component.  Hence a ready source vertex
always exposes an entire block whose external predecessor is already embedded.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

/-- The block containing a tree vertex: a singleton for a seed and the whole
deleted component for a nonseed. -/
noncomputable def tauFineBlock
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S : Finset A) (a : A) : Finset A :=
  if ha : a ∈ S then {a}
  else componentNonseedVertices T S (nonseedComponentOf T S a ha).1

lemma mem_tauFineBlock_self
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S : Finset A) (a : A) :
    a ∈ tauFineBlock T S a := by
  by_cases ha : a ∈ S
  · simp [tauFineBlock, ha]
  · rw [tauFineBlock, dif_neg ha]
    exact mem_component_of_nonseed T S a ha

lemma tauFineBlock_eq_of_mem
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S : Finset A) {a b : A}
    (hb : b ∈ tauFineBlock T S a) :
    tauFineBlock T S b = tauFineBlock T S a := by
  by_cases ha : a ∈ S
  · have hba : b = a := by
      simpa [tauFineBlock, ha] using! hb
    subst b
    rfl
  · have hbmem :
        b ∈ componentNonseedVertices T S
          (nonseedComponentOf T S a ha).1 := by
      simpa [tauFineBlock, ha] using! hb
    have hbS : b ∉ S :=
      (mem_componentNonseedVertices_iff T S _ b).mp hbmem |>.1
    have hcomp :
        nonseedComponentOf T S b hbS =
          nonseedComponentOf T S a ha := by
      exact (mem_indexed_component_iff T S
        (nonseedComponentOf T S a ha) b).mp hbmem |>.choose_spec
    simp only [tauFineBlock, dif_neg ha, dif_neg hbS]
    rw [hcomp]

/-- Rooted orientation data for the deleted components.  The root of a shrub
is the unique component vertex whose parent lies outside the component. -/
structure RootedSeedComponentData
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S : Finset A)
    (parent : A → Option A) where
  root : NonseedComponent T S → A
  root_mem : ∀ c, root c ∈ componentNonseedVertices T S c.1
  root_parent_seed : ∀ c, ∃ s ∈ S, parent (root c) = some s
  parent_internal : ∀ c x,
    x ∈ componentNonseedVertices T S c.1 →
    x ≠ root c →
    ∃ y ∈ componentNonseedVertices T S c.1, parent x = some y

/-- The component roots are also minimum-rank vertices.  This stronger bundle
is returned by the prescribed-root construction and is used to orient the
contracted seed constraints. -/
structure RootedSeedComponentRankData
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S : Finset A)
    (parent : A → Option A) (rank : A → ℕ)
    extends RootedSeedComponentData T S parent where
  root_rank_min : ∀ c x,
    x ∈ componentNonseedVertices T S c.1 →
    rank (root c) ≤ rank x

/-- A block-closed processed set contains either every vertex or no vertex of
each τ-fine block. -/
lemma tauFineBlock_disjoint_of_not_mem
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S P : Finset A)
    (hP : IsBlockClosed (tauFineBlock T S) P)
    {a : A} (ha : a ∉ P) :
    Disjoint (tauFineBlock T S a) P := by
  rw [Finset.disjoint_left]
  intro x hxa hxP
  have hxsub := hP x hxP
  have hxeq := tauFineBlock_eq_of_mem T S hxa
  exact ha (hxsub (by simpa [hxeq] using! mem_tauFineBlock_self T S a))

/-- A ready nonseed vertex is necessarily the prescribed root of its whole
component block.  Otherwise its internal parent would already be processed,
contradicting block disjointness. -/
lemma ready_nonseed_eq_component_root
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S P : Finset A)
    (parent : A → Option A)
    (D : RootedSeedComponentData T S parent)
    (hPblock : IsBlockClosed (tauFineBlock T S) P)
    (a : A) (haS : a ∉ S) (haP : a ∉ P)
    (hready : ∀ y, parent a = some y → y ∈ P) :
    a = D.root (nonseedComponentOf T S a haS) := by
  let c := nonseedComponentOf T S a haS
  have hac :
      a ∈ componentNonseedVertices T S c.1 :=
    mem_component_of_nonseed T S a haS
  by_contra hne
  obtain ⟨p, hpc, hap⟩ :=
    D.parent_internal c a hac hne
  have hpblock : p ∈ tauFineBlock T S a := by
    simpa [tauFineBlock, haS, c] using! hpc
  have hpP : p ∈ P := hready p hap
  exact (Finset.disjoint_left.mp
    (tauFineBlock_disjoint_of_not_mem T S P hPblock haP))
    hpblock hpP

/-- The τ-fine blocks meet the predecessor condition of
`sequential_block_embedding`. -/
lemma tauFineBlock_predecessor
    {A : Type} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (S : Finset A)
    (parent : A → Option A)
    (D : RootedSeedComponentData T S parent)
    (P : Finset A)
    (hPblock : IsBlockClosed (tauFineBlock T S) P)
    (hPdown : ∀ x ∈ P, ∀ y, parent x = some y → y ∈ P)
    (a : A) (haP : a ∉ P)
    (hready : ∀ y, parent a = some y → y ∈ P)
    (x : A) (hx : x ∈ tauFineBlock T S a)
    (y : A) (hxy : parent x = some y) :
    y ∈ tauFineBlock T S a ∨ y ∈ P := by
  by_cases haS : a ∈ S
  · have hxa : x = a := by
      simpa [tauFineBlock, haS] using! hx
    subst x
    exact Or.inr (hready y hxy)
  · let c := nonseedComponentOf T S a haS
    have hxc :
        x ∈ componentNonseedVertices T S c.1 := by
      simpa [tauFineBlock, haS, c] using! hx
    have hroota : a = D.root c :=
      ready_nonseed_eq_component_root T S P parent D hPblock
        a haS haP hready
    by_cases hxr : x = D.root c
    · apply Or.inr
      apply hready y
      simpa [hxr, ← hroota] using! hxy
    · obtain ⟨p, hpc, hxp⟩ :=
        D.parent_internal c x hxc hxr
      have hyp : y = p := by
        rw [hxp] at hxy
        exact (Option.some.inj hxy).symm
      subst y
      exact Or.inl (by
        simpa [tauFineBlock, haS, c] using! hpc)

end Erdos550

import Mathlib
import ErdosProblems.Erdos550.RootedComponentBlocks

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A deleted component as a prescribed-root finite tree

This is the exact source object consumed by the sharp rooted regular-pair
lemma.  Its root is the top vertex adjacent to the already embedded upper
seed; the parent of that top vertex is suppressed locally, while every other
parent remains the global tree parent.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

abbrev RootedComponentVertex
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S) :=
  {x : A // x ∈ componentNonseedVertices T S c.1}

noncomputable def componentLocalRoot
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) :
    RootedComponentVertex T S c :=
  ⟨D.root c, D.root_mem c⟩

noncomputable def componentLocalParent
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) :
    RootedComponentVertex T S c →
      Option (RootedComponentVertex T S c) :=
  fun x =>
    if h : x.1 = D.root c then none
    else
      some ⟨(D.parent_internal c x.1 x.2 h).choose,
        (D.parent_internal c x.1 x.2 h).choose_spec.1⟩

@[simp] lemma componentLocalParent_root
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S) :
    componentLocalParent T S D c (componentLocalRoot T S D c) = none := by
  simp [componentLocalParent, componentLocalRoot]

lemma componentLocalParent_some_global
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S)
    {x y : RootedComponentVertex T S c}
    (hxy : componentLocalParent T S D c x = some y) :
    parent x.1 = some y.1 := by
  unfold componentLocalParent at hxy
  split at hxy
  · simp at hxy
  · have hy :
        y = ⟨(D.parent_internal c x.1 x.2 ‹x.1 ≠ D.root c›).choose,
          (D.parent_internal c x.1 x.2
            ‹x.1 ≠ D.root c›).choose_spec.1⟩ :=
      Option.some.inj hxy |>.symm
    subst y
    exact (D.parent_internal c x.1 x.2
      ‹x.1 ≠ D.root c›).choose_spec.2

lemma componentLocalParent_eq_some_of_global
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S)
    {x y : RootedComponentVertex T S c}
    (hxy : parent x.1 = some y.1) :
    componentLocalParent T S D c x = some y := by
  have hxne : x.1 ≠ D.root c := by
    intro hxroot
    obtain ⟨s, hsS, hrootParent⟩ := D.root_parent_seed c
    have hxyRoot : parent (D.root c) = some y.1 := by
      simpa [hxroot] using! hxy
    have hy : y.1 = s :=
      Option.some.inj (hxyRoot.symm.trans hrootParent)
    have hyNot :
        y.1 ∉ S :=
      (mem_componentNonseedVertices_iff T S c.1 y.1).mp y.2 |>.1
    exact hyNot (hy ▸ hsS)
  unfold componentLocalParent
  rw [dif_neg hxne]
  congr 1
  apply Subtype.ext
  have hchoice :=
    (D.parent_internal c x.1 x.2 hxne).choose_spec.2
  have hyChoice :
      y.1 =
        (D.parent_internal c x.1 x.2 hxne).choose :=
    Option.some.inj (hxy.symm.trans hchoice)
  exact hyChoice.symm

lemma componentLocalParent_none_unique
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (c : NonseedComponent T S)
    (x : RootedComponentVertex T S c)
    (hx : componentLocalParent T S D c x = none) :
    x = componentLocalRoot T S D c := by
  unfold componentLocalParent at hx
  split at hx
  · exact Subtype.ext ‹x.1 = D.root c›
  · simp at hx

lemma componentLocalParent_rank
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (c : NonseedComponent T S)
    {x y : RootedComponentVertex T S c}
    (hxy : componentLocalParent T S D c x = some y) :
    rank y.1 < rank x.1 :=
  hrank x.1 y.1 (componentLocalParent_some_global T S D c hxy)

lemma componentLocalParent_adj
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (c : NonseedComponent T S)
    {x y : RootedComponentVertex T S c}
    (hxy : componentLocalParent T S D c x = some y) :
    T.Adj x.1 y.1 :=
  hparentAdj x.1 y.1
    (componentLocalParent_some_global T S D c hxy)

lemma componentLocalParent_col
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (c : NonseedComponent T S)
    {x y : RootedComponentVertex T S c}
    (hxy : componentLocalParent T S D c x = some y) :
    col x.1 ≠ col y.1 :=
  hcol x.1 y.1
    (componentLocalParent_some_global T S D c hxy)

@[simp] lemma card_rootedComponentVertex
    (T : SimpleGraph A) (S : Finset A)
    (c : NonseedComponent T S) :
    Fintype.card (RootedComponentVertex T S c) =
      (componentNonseedVertices T S c.1).card := by
  simp [RootedComponentVertex]

end Erdos550

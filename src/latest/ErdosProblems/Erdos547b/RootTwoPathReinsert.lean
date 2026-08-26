/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68
import ErdosProblems.Erdos547b.Lemma710Full

/-!
# Reinserting pendant root--middle--leaf paths

The residual source in Claim 6.17 is obtained by deleting the middle and
leaf of several disjoint pendant two-paths.  This module records the literal
source system, proves that an outward-oriented deletion leaves a tree, and
provides the checked Hall/gluing endpoint used after embedding the core.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617RootPaths

open Finset Fintype SimpleGraph

universe u v w

structure RootTwoPathSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (I : Type v) [Fintype I] where
  parent : I → V
  middle : I → V
  leaf : I → V
  middle_injective : Function.Injective middle
  leaf_injective : Function.Injective leaf
  middle_ne_leaf : ∀ i j, middle i ≠ leaf j
  parent_ne_middle : ∀ i j, parent i ≠ middle j
  parent_ne_leaf : ∀ i j, parent i ≠ leaf j
  parent_middle_adj : ∀ i, T.Adj (parent i) (middle i)
  middle_leaf_adj : ∀ i, T.Adj (middle i) (leaf i)
  middle_neighbors : ∀ i x, T.Adj (middle i) x →
    x = parent i ∨ x = leaf i
  leaf_neighbors : ∀ i x, T.Adj (leaf i) x → x = middle i

structure PendantRootTwoPathFamily
    {V : Type u} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) where
  middles : Finset V
  parent : middles → V
  leaf : middles → V
  leaf_injective : Function.Injective leaf
  middle_ne_leaf : ∀ (i j : middles), i.1 ≠ leaf j
  parent_ne_middle : ∀ (i j : middles), parent i ≠ j.1
  parent_ne_leaf : ∀ (i j : middles), parent i ≠ leaf j
  parent_middle_adj : ∀ i : middles, T.Adj (parent i) i.1
  middle_leaf_adj : ∀ i : middles, T.Adj i.1 (leaf i)
  middle_neighbors : ∀ (i : middles) x, T.Adj i.1 x →
    x = parent i ∨ x = leaf i
  leaf_neighbors : ∀ (i : middles) x, T.Adj (leaf i) x → x = i.1

namespace PendantRootTwoPathFamily

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V}

noncomputable def selectedIndex (P : PendantRootTwoPathFamily T)
    {q : ℕ} (hq : q ≤ P.middles.card) (i : Fin q) : P.middles :=
  P.middles.equivFin.symm
    ⟨i.val, lt_of_lt_of_le i.isLt (by simpa using hq)⟩

theorem selectedIndex_injective (P : PendantRootTwoPathFamily T)
    {q : ℕ} (hq : q ≤ P.middles.card) :
    Function.Injective (P.selectedIndex hq) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg P.middles.equivFin hij
  simpa [selectedIndex] using congrArg Fin.val h

noncomputable def select (P : PendantRootTwoPathFamily T)
    {q : ℕ} (hq : q ≤ P.middles.card) :
    RootTwoPathSystem T (Fin q) where
  parent i := P.parent (P.selectedIndex hq i)
  middle i := (P.selectedIndex hq i).1
  leaf i := P.leaf (P.selectedIndex hq i)
  middle_injective := Subtype.val_injective.comp (P.selectedIndex_injective hq)
  leaf_injective := P.leaf_injective.comp (P.selectedIndex_injective hq)
  middle_ne_leaf i j := P.middle_ne_leaf _ _
  parent_ne_middle i j := P.parent_ne_middle _ _
  parent_ne_leaf i j := P.parent_ne_leaf _ _
  parent_middle_adj i := P.parent_middle_adj _
  middle_leaf_adj i := P.middle_leaf_adj _
  middle_neighbors i x h := P.middle_neighbors _ x h
  leaf_neighbors i x h := P.leaf_neighbors _ x h

end PendantRootTwoPathFamily

namespace RootTwoPathSystem

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} {I : Type v} [Fintype I] [DecidableEq I]

def leafSet (D : RootTwoPathSystem T I) : Finset V :=
  Finset.univ.image D.leaf

def pruned (D : RootTwoPathSystem T I) : SimpleGraph {x // x ∉ D.leafSet} :=
  T.induce ((D.leafSet : Set V)ᶜ)

theorem middle_not_mem_leafSet (D : RootTwoPathSystem T I) (i : I) :
    D.middle i ∉ D.leafSet := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
  exact D.middle_ne_leaf i j hj.symm

theorem parent_not_mem_leafSet (D : RootTwoPathSystem T I) (i : I) :
    D.parent i ∉ D.leafSet := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
  exact D.parent_ne_leaf i j hj.symm

def middleVertex (D : RootTwoPathSystem T I) (i : I) :
    {x // x ∉ D.leafSet} :=
  ⟨D.middle i, D.middle_not_mem_leafSet i⟩

def middleSet (D : RootTwoPathSystem T I) :
    Finset {x // x ∉ D.leafSet} :=
  Finset.univ.image D.middleVertex

def parentVertex (D : RootTwoPathSystem T I) (i : I) :
    {x // x ∉ D.leafSet} :=
  ⟨D.parent i, D.parent_not_mem_leafSet i⟩

theorem parentVertex_not_mem_middleSet
    (D : RootTwoPathSystem T I) (i : I) :
    D.parentVertex i ∉ D.middleSet := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
  exact D.parent_ne_middle i j (congrArg Subtype.val hj).symm

def core (D : RootTwoPathSystem T I) :
    SimpleGraph {x // x ∉ D.middleSet} :=
  D.pruned.induce ((D.middleSet : Set {x // x ∉ D.leafSet})ᶜ)

def parentCoreVertex (D : RootTwoPathSystem T I) (i : I) :
    {x // x ∉ D.middleSet} :=
  ⟨D.parentVertex i, D.parentVertex_not_mem_middleSet i⟩

theorem root_not_mem_leafSet_of_oriented
    (D : RootTwoPathSystem T I) (hT : T.IsTree) (root : V)
    (hparentDist : ∀ i, T.dist root (D.parent i) + 1 =
      T.dist root (D.middle i))
    (hleafDist : ∀ i, T.dist root (D.middle i) + 1 =
      T.dist root (D.leaf i)) :
    root ∉ D.leafSet := by
  intro hroot
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hroot
  have hl := hleafDist i
  rw [hi] at hl
  simp at hl

theorem root_not_mem_middleSet_of_oriented
    (D : RootTwoPathSystem T I) (hT : T.IsTree) (root : V)
    (hparentDist : ∀ i, T.dist root (D.parent i) + 1 =
      T.dist root (D.middle i))
    (hleafDist : ∀ i, T.dist root (D.middle i) + 1 =
      T.dist root (D.leaf i)) :
    (⟨root, D.root_not_mem_leafSet_of_oriented hT root hparentDist hleafDist⟩ :
      {x // x ∉ D.leafSet}) ∉ D.middleSet := by
  intro hroot
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hroot
  have hp := hparentDist i
  have hi' : D.middle i = root := congrArg Subtype.val hi
  rw [hi'] at hp
  simp at hp

def coreRootOfOriented
    (D : RootTwoPathSystem T I) (hT : T.IsTree) (root : V)
    (hparentDist : ∀ i, T.dist root (D.parent i) + 1 =
      T.dist root (D.middle i))
    (hleafDist : ∀ i, T.dist root (D.middle i) + 1 =
      T.dist root (D.leaf i)) : {x // x ∉ D.middleSet} :=
  ⟨⟨root, D.root_not_mem_leafSet_of_oriented hT root hparentDist hleafDist⟩,
    D.root_not_mem_middleSet_of_oriented hT root hparentDist hleafDist⟩

private theorem parent_survives_oriented_core
    (D : RootTwoPathSystem T I) (hT : T.IsTree) (root : V)
    (hparentDist : ∀ i, T.dist root (D.parent i) + 1 =
      T.dist root (D.middle i))
    (hleafDist : ∀ i, T.dist root (D.middle i) + 1 =
      T.dist root (D.leaf i))
    (x : {x // x ∉ D.middleSet}) (hx : x.1.1 ≠ root) :
    ∃ p : {x // x ∉ D.middleSet},
      D.core.Adj p x ∧ T.dist root p.1.1 + 1 = T.dist root x.1.1 := by
  classical
  let p₀ := Erdos547b.TreePartition.parent hT root hx
  have hp₀adj : T.Adj p₀ x.1.1 :=
    Erdos547b.TreePartition.parent_adj hT root hx
  have hp₀dist : T.dist root p₀ + 1 = T.dist root x.1.1 :=
    Erdos547b.TreePartition.parent_dist_add_one hT root hx
  have hp₀leaf : p₀ ∉ D.leafSet := by
    intro hp
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
    have hxi : x.1.1 = D.middle i := by
      apply D.leaf_neighbors i x.1.1
      simpa [hi] using hp₀adj
    apply x.2
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, Subtype.ext ?_⟩
    exact hxi.symm
  let p₁ : {z // z ∉ D.leafSet} := ⟨p₀, hp₀leaf⟩
  have hp₁middle : p₁ ∉ D.middleSet := by
    intro hp
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
    have hpEq : p₀ = D.middle i := congrArg Subtype.val hi.symm
    have hcases : x.1.1 = D.parent i ∨ x.1.1 = D.leaf i := by
      apply D.middle_neighbors i x.1.1
      simpa [hpEq] using hp₀adj
    rcases hcases with hparent | hleaf
    · have hpi := hparentDist i
      rw [← hpEq, ← hparent] at hpi
      omega
    · exact x.1.2 (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, hleaf.symm⟩)
  let p : {z // z ∉ D.middleSet} := ⟨p₁, hp₁middle⟩
  refine ⟨p, ?_, hp₀dist⟩
  simpa [core, pruned, p, p₁] using hp₀adj

theorem core_isTree_of_oriented
    (D : RootTwoPathSystem T I) (hT : T.IsTree) (root : V)
    (hparentDist : ∀ i, T.dist root (D.parent i) + 1 =
      T.dist root (D.middle i))
    (hleafDist : ∀ i, T.dist root (D.middle i) + 1 =
      T.dist root (D.leaf i)) :
    D.core.IsTree := by
  let r := D.coreRootOfOriented hT root hparentDist hleafDist
  have hconn : D.core.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨r, ?_⟩
    intro x
    generalize hn : T.dist root x.1.1 = n
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
        by_cases hx : x.1.1 = root
        · have hxroot : x = r := by
            apply Subtype.ext
            apply Subtype.ext
            exact hx
          subst x
          exact SimpleGraph.Reachable.refl r
        · obtain ⟨p, hpx, hpdist⟩ :=
            D.parent_survives_oriented_core hT root hparentDist hleafDist x hx
          have hpn : T.dist root p.1.1 < n := by omega
          exact (ih _ hpn p rfl).trans hpx.reachable
  refine ⟨hconn, ?_⟩
  let e₁ : SimpleGraph.Embedding D.pruned T := SimpleGraph.Embedding.induce _
  let e₂ : SimpleGraph.Embedding D.core D.pruned := SimpleGraph.Embedding.induce _
  exact SimpleGraph.IsAcyclic.comap (e₁.comp e₂) (e₁.comp e₂).injective
    hT.isAcyclic

variable {B : Type w} [Fintype B] [DecidableEq B]

def coreImages {G : SimpleGraph B} (D : RootTwoPathSystem T I)
    (f : D.core.Copy G) : Finset B :=
  Finset.univ.image f

def middleChoices (D : RootTwoPathSystem T I) (G : SimpleGraph B)
    [DecidableRel G.Adj] (f : D.core.Copy G) (pool : Finset B) (i : I) :
    Finset B :=
  (G.neighborFinset (f (D.parentCoreVertex i)) ∩ pool) \ D.coreImages f

theorem exists_middleAssignment
    (D : RootTwoPathSystem T I) (G : SimpleGraph B) [DecidableRel G.Adj]
    (f : D.core.Copy G) (pool : Finset B)
    (hlive : ∀ i, Fintype.card I ≤ #(D.middleChoices G f pool i)) :
    ∃ g : I → B, Function.Injective g ∧
      ∀ i, g i ∈ D.middleChoices G f pool i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    (D.middleChoices G f pool)).mp
  intro s
  by_cases hs : s = ∅
  · simp [hs]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    calc
      #s ≤ Fintype.card I := Finset.card_le_univ s
      _ ≤ #(D.middleChoices G f pool i) := hlive i
      _ ≤ #(s.biUnion (D.middleChoices G f pool)) :=
        Finset.card_le_card
          (Finset.subset_biUnion_of_mem (D.middleChoices G f pool) hi)

private theorem middleSet_nonempty_index
    (D : RootTwoPathSystem T I) (x : D.middleSet) :
    ∃ i : I, D.middleVertex i = x := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
  exact ⟨i, hi⟩

private noncomputable def middleIndex
    (D : RootTwoPathSystem T I) (x : D.middleSet) : I :=
  Classical.choose (D.middleSet_nonempty_index x)

private theorem middleIndex_spec
    (D : RootTwoPathSystem T I) (x : D.middleSet) :
    D.middleVertex (D.middleIndex x) = x :=
  Classical.choose_spec (D.middleSet_nonempty_index x)

private theorem leafSet_nonempty_index
    (D : RootTwoPathSystem T I) (x : D.leafSet) :
    ∃ i : I, D.leaf i = x.1 := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
  exact ⟨i, hi⟩

private noncomputable def leafIndex
    (D : RootTwoPathSystem T I) (x : D.leafSet) : I :=
  Classical.choose (D.leafSet_nonempty_index x)

private theorem leafIndex_spec
    (D : RootTwoPathSystem T I) (x : D.leafSet) :
    D.leaf (D.leafIndex x) = x.1 :=
  Classical.choose_spec (D.leafSet_nonempty_index x)

/-- Hall restores the middles beside their embedded parents, then the usual
large-degree leaf completion restores the terminal leaves. -/
theorem exists_copy_of_core_of_rootTwoPaths
    (D : RootTwoPathSystem T I) (G : SimpleGraph B) [DecidableRel G.Adj]
    (f : D.core.Copy G) (pool : Finset B)
    (hlive : ∀ i, Fintype.card I ≤ #(D.middleChoices G f pool i))
    (hdegree : ∀ z ∈ pool, Fintype.card V - 1 ≤ G.degree z) :
    Nonempty (T.Copy G) := by
  classical
  obtain ⟨mid, hmidInj, hmidChoice⟩ :=
    D.exists_middleAssignment G f pool hlive
  let gMiddle : D.middleSet → B := fun x ↦ mid (D.middleIndex x)
  have hgMiddleInj : Function.Injective gMiddle := by
    intro x y hxy
    have hidx : D.middleIndex x = D.middleIndex y := hmidInj hxy
    apply Subtype.ext
    calc
      x.1 = D.middleVertex (D.middleIndex x) :=
        (D.middleIndex_spec x).symm
      _ = D.middleVertex (D.middleIndex y) := by rw [hidx]
      _ = y.1 := D.middleIndex_spec y
  have hfg : ∀ x y, f x ≠ gMiddle y := by
    intro x y hxy
    have hnot := Finset.mem_sdiff.mp (hmidChoice (D.middleIndex y)) |>.2
    apply hnot
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    simpa [gMiddle] using hxy
  have hMM : ∀ x y : D.middleSet, D.pruned.Adj x y →
      G.Adj (gMiddle x) (gMiddle y) := by
    intro x y hxy
    exfalso
    have hTxy : T.Adj x.1.1 y.1.1 := hxy
    have hxMiddle : D.middle (D.middleIndex x) = x.1.1 :=
      congrArg Subtype.val (D.middleIndex_spec x)
    have hyMiddle : D.middle (D.middleIndex y) = y.1.1 :=
      congrArg Subtype.val (D.middleIndex_spec y)
    have hfromMiddle : T.Adj (D.middle (D.middleIndex x)) y.1.1 := by
      rw [hxMiddle]
      exact hTxy
    have hcases :=
      D.middle_neighbors (D.middleIndex x) y.1.1 hfromMiddle
    rcases hcases with hp | hl
    · exact D.parent_ne_middle (D.middleIndex x) (D.middleIndex y)
        (hp.symm.trans hyMiddle.symm)
    · exact D.middle_ne_leaf (D.middleIndex y) (D.middleIndex x)
        (hyMiddle.trans hl)
  have hMC : ∀ x : D.middleSet, ∀ y : ↥((D.middleSet :
      Set {x // x ∉ D.leafSet})ᶜ), D.pruned.Adj x y →
      G.Adj (gMiddle x) (f y) := by
    intro x y hxy
    let i := D.middleIndex x
    have hxMiddle : D.middle i = x.1.1 := by
      exact congrArg Subtype.val (D.middleIndex_spec x)
    have hTxy' : T.Adj x.1.1 y.1.1 := hxy
    have hTxy : T.Adj (D.middle i) y.1.1 := by
      rw [hxMiddle]
      exact hTxy'
    have hcases := D.middle_neighbors i y.1.1 hTxy
    rcases hcases with hp | hl
    · have hyParent : y = D.parentCoreVertex i := by
        apply Subtype.ext
        apply Subtype.ext
        exact hp
      have hchoice := Finset.mem_sdiff.mp (hmidChoice i) |>.1
      have hadj : G.Adj (f (D.parentCoreVertex i)) (mid i) :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hchoice).1
      simpa [gMiddle, i, hyParent] using hadj.symm
    · exact False.elim (y.1.2 (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, hl.symm⟩))
  obtain ⟨prunedCopy, hmidMap, hcoreMap⟩ :=
    Erdos547b.ZhaoLemma710Alt.copy_of_induce_compl_and_extension
      D.pruned G D.middleSet f gMiddle hgMiddleInj hfg hMM hMC
  let leafParent : D.leafSet → V := fun x ↦ D.middle (D.leafIndex x)
  have hleafParentNot (x : D.leafSet) : leafParent x ∉ D.leafSet :=
    D.middle_not_mem_leafSet (D.leafIndex x)
  have hleafParentAdj (x : D.leafSet) : T.Adj (leafParent x) x.1 := by
    simpa [leafParent, D.leafIndex_spec x] using
      D.middle_leaf_adj (D.leafIndex x)
  have hleafUnique (x : D.leafSet) (y : V) (hxy : T.Adj x.1 y) :
      y = leafParent x := by
    simpa [leafParent, D.leafIndex_spec x] using
      D.leaf_neighbors (D.leafIndex x) y (by simpa [D.leafIndex_spec x] using hxy)
  have hleafDegree (x : D.leafSet) :
      Fintype.card V - 1 ≤
        G.degree (prunedCopy ⟨leafParent x, hleafParentNot x⟩) := by
    let i := D.leafIndex x
    have hmemMiddle : D.middleVertex i ∈ D.middleSet :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    let xm : D.middleSet := ⟨D.middleVertex i, hmemMiddle⟩
    have hmap : prunedCopy ⟨leafParent x, hleafParentNot x⟩ = mid i := by
      calc
        prunedCopy ⟨leafParent x, hleafParentNot x⟩ = gMiddle xm := by
          have harg :
              (⟨leafParent x, hleafParentNot x⟩ :
                {z // z ∉ D.leafSet}) = xm.1 := by
            apply Subtype.ext
            rfl
          rw [harg]
          exact hmidMap xm
        _ = mid i := by
          simp only [gMiddle]
          have hs := D.middleIndex_spec xm
          have : D.middleIndex xm = i := D.middle_injective (by
            exact congrArg Subtype.val hs)
          rw [this]
    rw [hmap]
    exact hdegree (mid i)
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp (hmidChoice i) |>.1)).2
  obtain ⟨full, -, -⟩ :=
    Erdos547b.ZhaoClaim68.exists_copy_of_induce_compl_of_leaves
      T G D.leafSet leafParent hleafParentNot hleafParentAdj
      hleafUnique prunedCopy hleafDegree
  exact ⟨full⟩

end RootTwoPathSystem

end Erdos547b.ZhaoClaim617RootPaths

#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.core_isTree_of_oriented
#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.exists_copy_of_core_of_rootTwoPaths

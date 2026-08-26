/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616ResidualAllocation
import ErdosProblems.Erdos547b.Proposition57

/-!
# Canonical root supports and partitions for Zhao Claim 6.16

The three source pieces in Claim 6.16 are unions of whole root-deleted
branches.  The important point is that an embedding support does **not**
contain every isolated ordered-forest root.  It contains the owners of its
branches, together with an explicit allocation of genuinely isolated roots.
This prevents the major and minor parity certificates from simultaneously
forcing the same irrelevant root into two different host reservoirs.

`SupportPartition` is the relative form of Proposition 5.7's incidence
partition.  It is used for `F₀/F₁` inside the major support; the outer
major/`F_b` split is an ordinary `ZhaoProp57.RootPartition`.  The final
section glues already-realized supported embeddings over one chosen root map,
with a reservoir allowed to depend on the root.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim616RootPartitions

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoProp57
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoLemma59Part2Full

universe u v

/-- A root partition relative to `parent`.  This is the correct intermediate
object for `F₀/F₁`: their union is the major support, not the full forest. -/
structure SupportPartition {A : Type u} [Fintype A] [DecidableEq A]
    (F : SimpleGraph A) (roots parent left right : Finset A) : Prop where
  cover : left ∪ right = parent
  overlap_roots : left ∩ right ⊆ roots
  edge_cover : ∀ ⦃x y : A⦄, F.Adj x y → x ∈ parent → y ∈ parent →
    (x ∈ left ∧ y ∈ left) ∨ (x ∈ right ∧ y ∈ right)

namespace OrderedBranchForest

variable {r b : ℕ}

/-- Root coordinates selected for an embedding support. -/
def rootSupport (F : OrderedBranchForest r b) (q : Finset (Fin r)) :
    Finset F.Vertex :=
  q.image Sum.inl

/-- All vertices in the selected root-deleted branches, excluding the
original roots. -/
def branchVertexSupport (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) : Finset F.Vertex := by
  classical
  exact Finset.univ.filter fun x =>
      match x with
      | Sum.inl _ => False
      | Sum.inr z => z.1 ∈ s

/-- Embedding support with an explicit root-coordinate set. -/
def rootedBranchSupport (F : OrderedBranchForest r b)
    (q : Finset (Fin r)) (s : Finset (Fin b)) : Finset F.Vertex :=
  rootSupport F q ∪ branchVertexSupport F s

/-- Broad structural support used to identify `restrict F s` with its image.
Actual partial embeddings use `rootedBranchSupport`, not this all-root set. -/
def branchSupport (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    Finset F.Vertex :=
  rootedBranchSupport F Finset.univ s

@[simp] theorem root_mem_rootSupport_iff (F : OrderedBranchForest r b)
    (q : Finset (Fin r)) (i : Fin r) :
    (Sum.inl i : F.Vertex) ∈ rootSupport F q ↔ i ∈ q := by
  simp [rootSupport]

@[simp] theorem root_not_mem_branchVertexSupport
    (F : OrderedBranchForest r b) (s : Finset (Fin b)) (i : Fin r) :
    (Sum.inl i : F.Vertex) ∉ branchVertexSupport F s := by
  simp [branchVertexSupport]

@[simp] theorem branch_mem_branchVertexSupport_iff
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (z : Σ j, Fin (F.branches.size j)) :
    (Sum.inr z : F.Vertex) ∈ branchVertexSupport F s ↔ z.1 ∈ s := by
  simp [branchVertexSupport]

@[simp] theorem root_mem_rootedBranchSupport_iff
    (F : OrderedBranchForest r b) (q : Finset (Fin r))
    (s : Finset (Fin b)) (i : Fin r) :
    (Sum.inl i : F.Vertex) ∈ rootedBranchSupport F q s ↔ i ∈ q := by
  simp [rootedBranchSupport]

@[simp] theorem branch_mem_rootedBranchSupport_iff
    (F : OrderedBranchForest r b) (q : Finset (Fin r))
    (s : Finset (Fin b)) (z : Σ j, Fin (F.branches.size j)) :
    (Sum.inr z : F.Vertex) ∈ rootedBranchSupport F q s ↔ z.1 ∈ s := by
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hzRoot | hzBranch
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzRoot
      cases hi
    · exact (branch_mem_branchVertexSupport_iff F s z).mp hzBranch
  · intro hz
    exact Finset.mem_union_right _
      ((branch_mem_branchVertexSupport_iff F s z).mpr hz)

@[simp] theorem root_mem_branchSupport
    (F : OrderedBranchForest r b) (s : Finset (Fin b)) (i : Fin r) :
    (Sum.inl i : F.Vertex) ∈ branchSupport F s := by
  simp [branchSupport]

@[simp] theorem branch_mem_branchSupport_iff
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (z : Σ j, Fin (F.branches.size j)) :
    (Sum.inr z : F.Vertex) ∈ branchSupport F s ↔ z.1 ∈ s := by
  simp [branchSupport]

theorem rootedBranchSupport_union (F : OrderedBranchForest r b)
    (q q' : Finset (Fin r)) (s s' : Finset (Fin b)) :
    rootedBranchSupport F q s ∪ rootedBranchSupport F q' s' =
      rootedBranchSupport F (q ∪ q') (s ∪ s') := by
  ext x
  rcases x with i | z <;> simp

@[simp] theorem rootedBranchSupport_univ (F : OrderedBranchForest r b) :
    rootedBranchSupport F Finset.univ Finset.univ = Finset.univ := by
  ext x
  rcases x with i | z <;> simp

theorem rootedBranchSupport_subset_roots_of_branch_disjoint
    (F : OrderedBranchForest r b)
    (q q' : Finset (Fin r)) {s s' : Finset (Fin b)}
    (hss' : Disjoint s s') :
    rootedBranchSupport F q s ∩ rootedBranchSupport F q' s' ⊆ F.roots := by
  intro x hx
  rcases x with i | z
  · exact (F.mem_roots_iff (Sum.inl i)).mpr ⟨i, rfl⟩
  · have hzs : z.1 ∈ s :=
      (branch_mem_rootedBranchSupport_iff F q s z).mp
        (Finset.mem_inter.mp hx).1
    have hzs' : z.1 ∈ s' :=
      (branch_mem_rootedBranchSupport_iff F q' s' z).mp
        (Finset.mem_inter.mp hx).2
    exact False.elim (Finset.disjoint_left.mp hss' hzs hzs')

/-- Whole-branch covers give relative support partitions.  The owner
hypotheses say that every attachment edge is retained in the same piece as
its branch. -/
theorem rootedBranchSupportPartition
    (F : OrderedBranchForest r b)
    (parentRoots leftRoots rightRoots : Finset (Fin r))
    (parentBranches leftBranches rightBranches : Finset (Fin b))
    (hrootCover : leftRoots ∪ rightRoots = parentRoots)
    (hbranchCover : leftBranches ∪ rightBranches = parentBranches)
    (hbranchDisjoint : Disjoint leftBranches rightBranches)
    (hownerLeft : ∀ j ∈ leftBranches, F.owner j ∈ leftRoots)
    (hownerRight : ∀ j ∈ rightBranches, F.owner j ∈ rightRoots) :
    SupportPartition F.graph F.roots
      (rootedBranchSupport F parentRoots parentBranches)
      (rootedBranchSupport F leftRoots leftBranches)
      (rootedBranchSupport F rightRoots rightBranches) := by
  refine
    { cover := ?_
      overlap_roots :=
        rootedBranchSupport_subset_roots_of_branch_disjoint F
          leftRoots rightRoots hbranchDisjoint
      edge_cover := ?_ }
  · rw [rootedBranchSupport_union, hrootCover, hbranchCover]
  · intro x y hxy hxParent hyParent
    rcases x with i | z <;> rcases y with k | w
    · exact False.elim (F.graph_adj_root_root i k hxy)
    · have hwParent : w.1 ∈ parentBranches :=
        (branch_mem_rootedBranchSupport_iff F parentRoots parentBranches w).mp
          hyParent
      have hw : w.1 ∈ leftBranches ∨ w.1 ∈ rightBranches := by
        rw [← hbranchCover] at hwParent
        exact Finset.mem_union.mp hwParent
      rcases hw with hwLeft | hwRight
      · have howner := hownerLeft w.1 hwLeft
        have hi : i = F.owner w.1 :=
          (F.graph_adj_root_branch i w).mp hxy |>.1.symm
        subst i
        exact Or.inl ⟨by simp [howner], by simp [hwLeft]⟩
      · have howner := hownerRight w.1 hwRight
        have hi : i = F.owner w.1 :=
          (F.graph_adj_root_branch i w).mp hxy |>.1.symm
        subst i
        exact Or.inr ⟨by simp [howner], by simp [hwRight]⟩
    · have hzParent : z.1 ∈ parentBranches :=
        (branch_mem_rootedBranchSupport_iff F parentRoots parentBranches z).mp
          hxParent
      have hz : z.1 ∈ leftBranches ∨ z.1 ∈ rightBranches := by
        rw [← hbranchCover] at hzParent
        exact Finset.mem_union.mp hzParent
      rcases hz with hzLeft | hzRight
      · have howner := hownerLeft z.1 hzLeft
        have hk : k = F.owner z.1 :=
          (F.graph_adj_branch_root z k).mp hxy |>.1.symm
        subst k
        exact Or.inl ⟨by simp [hzLeft], by simp [howner]⟩
      · have howner := hownerRight z.1 hzRight
        have hk : k = F.owner z.1 :=
          (F.graph_adj_branch_root z k).mp hxy |>.1.symm
        subst k
        exact Or.inr ⟨by simp [hzRight], by simp [howner]⟩
    · obtain ⟨hzw, -⟩ := (F.graph_adj_branch_branch z w).mp hxy
      have hzParent : z.1 ∈ parentBranches :=
        (branch_mem_rootedBranchSupport_iff F parentRoots parentBranches z).mp
          hxParent
      have hz : z.1 ∈ leftBranches ∨ z.1 ∈ rightBranches := by
        rw [← hbranchCover] at hzParent
        exact Finset.mem_union.mp hzParent
      rcases hz with hzLeft | hzRight
      · have hwLeft : w.1 ∈ leftBranches := hzw ▸ hzLeft
        exact Or.inl ⟨by simp [hzLeft], by simp [hwLeft]⟩
      · have hwRight : w.1 ∈ rightBranches := hzw ▸ hzRight
        exact Or.inr ⟨by simp [hzRight], by simp [hwRight]⟩

theorem SupportPartition.toRootPartition
    (F : OrderedBranchForest r b)
    {roots parent left right : Finset F.Vertex}
    (part : SupportPartition F.graph roots parent left right)
    (hparent : parent = Finset.univ) :
    RootPartition F.graph roots left right where
  cover := part.cover.trans hparent
  overlap_roots := part.overlap_roots
  edge_cover := by
    intro x y hxy
    exact part.edge_cover hxy (hparent ▸ Finset.mem_univ x)
      (hparent ▸ Finset.mem_univ y)

end OrderedBranchForest

/-! ## Concrete merging over one parity-aware root map -/

/-- Merge two already-realized embeddings on a relative support partition.
The reservoir depends on the root, so the chosen root map may alternate
between the genuine `A₀` and `B₀` reservoirs. -/
theorem merge_supportedRootEmbeddings_relative_of_rootReservoir
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots parent left right : Finset A)
    (targetLeft targetRight : Finset B)
    (rootImage : A → B) (rootReservoir : A → Finset B)
    (part : SupportPartition F roots parent left right)
    (hrootInj : ∀ ⦃r q : A⦄, r ∈ roots → q ∈ roots →
      rootImage r = rootImage q → r = q)
    (hrootMem : ∀ ⦃r : A⦄, r ∈ roots → rootImage r ∈ rootReservoir r)
    (hrootLeft : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetLeft)
    (hrootRight : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetRight)
    (htarget : Disjoint targetLeft targetRight)
    (eLeft : SupportedRootEmbedding F G roots left targetLeft rootImage)
    (eRight : SupportedRootEmbedding F G roots right targetRight rootImage) :
    Nonempty (SupportedRootEmbedding F G roots parent
      (targetLeft ∪ targetRight) rootImage) := by
  classical
  let glued : A → B := fun x => if x ∈ left then eLeft.toFun x else eRight.toFun x
  have hright (x : A) (hx : x ∈ right) : glued x = eRight.toFun x := by
    by_cases hxl : x ∈ left
    · have hxr : x ∈ roots := part.overlap_roots
        (Finset.mem_inter.mpr ⟨hxl, hx⟩)
      have hle : eLeft.toFun x = rootImage x := eLeft.map_root hxr hxl
      have hre : eRight.toFun x = rootImage x := eRight.map_root hxr hx
      simp only [glued, hxl, if_pos, hle, hre]
    · simp only [glued, if_neg hxl]
  have hleft (x : A) (hx : x ∈ left) : glued x = eLeft.toFun x := by
    simp only [glued, hx, if_pos]
  have hgluedRoot {x : A} (hxRoot : x ∈ roots) (hx : x ∈ parent) :
      glued x = rootImage x := by
    have hxCover : x ∈ left ∨ x ∈ right := by
      rw [← part.cover] at hx
      exact Finset.mem_union.mp hx
    rcases hxCover with hxl | hxr
    · rw [hleft x hxl]
      exact eLeft.map_root hxRoot hxl
    · rw [hright x hxr]
      exact eRight.map_root hxRoot hxr
  have hgluedNonroot {x : A} (hx : x ∈ parent) (hxRoot : x ∉ roots) :
      glued x ∈ targetLeft ∪ targetRight := by
    have hxCover : x ∈ left ∨ x ∈ right := by
      rw [← part.cover] at hx
      exact Finset.mem_union.mp hx
    rcases hxCover with hxl | hxr
    · exact Finset.mem_union_left _ (by
        rw [hleft x hxl]
        exact eLeft.map_nonroot hxl hxRoot)
    · exact Finset.mem_union_right _ (by
        rw [hright x hxr]
        exact eRight.map_nonroot hxr hxRoot)
  have hgluedAdj : ∀ ⦃x y : A⦄, F.Adj x y → x ∈ parent → y ∈ parent →
      G.Adj (glued x) (glued y) := by
    intro x y hxy hx hy
    rcases part.edge_cover hxy hx hy with hL | hR
    · rw [hleft x hL.1, hleft y hL.2]
      exact eLeft.map_adj hxy hL.1 hL.2
    · rw [hright x hR.1, hright y hR.2]
      exact eRight.map_adj hxy hR.1 hR.2
  have hgluedInj : ∀ ⦃x y : A⦄, x ∈ parent → y ∈ parent →
      glued x = glued y → x = y := by
    intro x y hxParent hyParent hxy
    have hxCover : x ∈ left ∨ x ∈ right := by
      rw [← part.cover] at hxParent
      exact Finset.mem_union.mp hxParent
    have hyCover : y ∈ left ∨ y ∈ right := by
      rw [← part.cover] at hyParent
      exact Finset.mem_union.mp hyParent
    rcases hxCover with hxl | hxr <;> rcases hyCover with hyl | hyr
    · exact eLeft.injOn hxl hyl (by
        simpa only [hleft x hxl, hleft y hyl] using hxy)
    · by_cases hxRoot : x ∈ roots
      · by_cases hyRoot : y ∈ roots
        · exact hrootInj hxRoot hyRoot (by
            rw [← hgluedRoot hxRoot hxParent,
              ← hgluedRoot hyRoot hyParent]
            exact hxy)
        · have hxRes : glued x ∈ rootReservoir x := by
            rw [hgluedRoot hxRoot hxParent]
            exact hrootMem hxRoot
          have hyTarget : glued y ∈ targetRight := by
            rw [hright y hyr]
            exact eRight.map_nonroot hyr hyRoot
          exact False.elim (Finset.disjoint_left.mp (hrootRight hxRoot)
            hxRes (hxy ▸ hyTarget))
      · have hxTarget : glued x ∈ targetLeft := by
          rw [hleft x hxl]
          exact eLeft.map_nonroot hxl hxRoot
        by_cases hyRoot : y ∈ roots
        · have hyRes : glued y ∈ rootReservoir y := by
            rw [hgluedRoot hyRoot hyParent]
            exact hrootMem hyRoot
          exact False.elim (Finset.disjoint_left.mp (hrootLeft hyRoot)
            hyRes (hxy.symm ▸ hxTarget))
        · have hyTarget : glued y ∈ targetRight := by
            rw [hright y hyr]
            exact eRight.map_nonroot hyr hyRoot
          exact False.elim
            (Finset.disjoint_left.mp htarget hxTarget (hxy ▸ hyTarget))
    · by_cases hxRoot : x ∈ roots
      · by_cases hyRoot : y ∈ roots
        · exact hrootInj hxRoot hyRoot (by
            rw [← hgluedRoot hxRoot hxParent,
              ← hgluedRoot hyRoot hyParent]
            exact hxy)
        · have hxRes : glued x ∈ rootReservoir x := by
            rw [hgluedRoot hxRoot hxParent]
            exact hrootMem hxRoot
          have hyTarget : glued y ∈ targetLeft := by
            rw [hleft y hyl]
            exact eLeft.map_nonroot hyl hyRoot
          exact False.elim (Finset.disjoint_left.mp (hrootLeft hxRoot)
            hxRes (hxy ▸ hyTarget))
      · have hxTarget : glued x ∈ targetRight := by
          rw [hright x hxr]
          exact eRight.map_nonroot hxr hxRoot
        by_cases hyRoot : y ∈ roots
        · have hyRes : glued y ∈ rootReservoir y := by
            rw [hgluedRoot hyRoot hyParent]
            exact hrootMem hyRoot
          exact False.elim (Finset.disjoint_left.mp (hrootRight hyRoot)
            hyRes (hxy.symm ▸ hxTarget))
        · have hyTarget : glued y ∈ targetLeft := by
            rw [hleft y hyl]
            exact eLeft.map_nonroot hyl hyRoot
          exact False.elim
            (Finset.disjoint_left.mp htarget hyTarget (hxy ▸ hxTarget))
    · exact eRight.injOn hxr hyr (by
        simpa only [hright x hxr, hright y hyr] using hxy)
  exact ⟨
    { toFun := glued
      map_adj := by
        intro x y hxy hx hy
        exact hgluedAdj hxy hx hy
      injOn := by
        intro x y hx hy hxy
        exact hgluedInj hx hy hxy
      map_root := by
        intro x hxRoot hx
        exact hgluedRoot hxRoot hx
      map_nonroot := by
        intro x hx hxRoot
        exact hgluedNonroot hx hxRoot }
  ⟩

/-- Full-support specialization of the preceding relative merge. -/
theorem merge_supportedRootEmbeddings_of_rootReservoir
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots left right : Finset A)
    (targetLeft targetRight : Finset B)
    (rootImage : A → B) (rootReservoir : A → Finset B)
    (part : RootPartition F roots left right)
    (hrootInj : ∀ ⦃r q : A⦄, r ∈ roots → q ∈ roots →
      rootImage r = rootImage q → r = q)
    (hrootMem : ∀ ⦃r : A⦄, r ∈ roots → rootImage r ∈ rootReservoir r)
    (hrootLeft : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetLeft)
    (hrootRight : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetRight)
    (htarget : Disjoint targetLeft targetRight)
    (eLeft : SupportedRootEmbedding F G roots left targetLeft rootImage)
    (eRight : SupportedRootEmbedding F G roots right targetRight rootImage) :
    Nonempty (RootedTargetEmbedding F G roots
      (targetLeft ∪ targetRight) rootImage) := by
  let relative : SupportPartition F roots Finset.univ left right :=
    { cover := part.cover
      overlap_roots := part.overlap_roots
      edge_cover := by
        intro x y hxy _ _
        exact part.edge_cover hxy }
  obtain ⟨E⟩ := merge_supportedRootEmbeddings_relative_of_rootReservoir
    F G roots Finset.univ left right targetLeft targetRight
    rootImage rootReservoir relative hrootInj hrootMem hrootLeft hrootRight
    htarget eLeft eRight
  let copy : F.Copy G :=
    ⟨⟨E.toFun, fun {_ _} hxy => E.map_adj hxy (Finset.mem_univ _) (Finset.mem_univ _)⟩,
      fun {_ _} hxy => E.injOn (Finset.mem_univ _) (Finset.mem_univ _) hxy⟩
  exact ⟨
    { copy := copy
      map_root := by
        intro x hx
        change E.toFun x = rootImage x
        exact E.map_root hx (Finset.mem_univ x)
      map_nonroot := by
        intro x hx
        rw [Finset.mem_union]
        change E.toFun x ∈ targetLeft ∨ E.toFun x ∈ targetRight
        exact Finset.mem_union.mp (E.map_nonroot (Finset.mem_univ x) hx) }
  ⟩

/-- Direct composable merge of selected `F₀`, residual `F₁`, and minor
`F_b`.  The two source partitions are concrete incidence data; the only
embedding inputs are the three already-realized supported embeddings over
the same chosen root map. -/
theorem merge_three_supportedRootEmbeddings_of_rootReservoir
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots major first second third : Finset A)
    (targetFirst targetSecond targetThird : Finset B)
    (rootImage : A → B) (rootReservoir : A → Finset B)
    (inner : SupportPartition F roots major first second)
    (outer : RootPartition F roots major third)
    (hrootInj : ∀ ⦃r q : A⦄, r ∈ roots → q ∈ roots →
      rootImage r = rootImage q → r = q)
    (hrootMem : ∀ ⦃r : A⦄, r ∈ roots → rootImage r ∈ rootReservoir r)
    (hrootFirst : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetFirst)
    (hrootSecond : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetSecond)
    (hrootThird : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) targetThird)
    (hfirstSecond : Disjoint targetFirst targetSecond)
    (hmajorThird : Disjoint (targetFirst ∪ targetSecond) targetThird)
    (eFirst : SupportedRootEmbedding F G roots first targetFirst rootImage)
    (eSecond : SupportedRootEmbedding F G roots second targetSecond rootImage)
    (eThird : SupportedRootEmbedding F G roots third targetThird rootImage) :
    Nonempty (RootedTargetEmbedding F G roots
      ((targetFirst ∪ targetSecond) ∪ targetThird) rootImage) := by
  obtain ⟨eMajor⟩ := merge_supportedRootEmbeddings_relative_of_rootReservoir
    F G roots major first second targetFirst targetSecond rootImage rootReservoir
    inner hrootInj hrootMem hrootFirst hrootSecond hfirstSecond eFirst eSecond
  have hrootMajor : ∀ ⦃r : A⦄, r ∈ roots →
      Disjoint (rootReservoir r) (targetFirst ∪ targetSecond) := by
    intro r hr
    rw [Finset.disjoint_left]
    intro x hx hxtarget
    rcases Finset.mem_union.mp hxtarget with hxFirst | hxSecond
    · exact Finset.disjoint_left.mp (hrootFirst hr) hx hxFirst
    · exact Finset.disjoint_left.mp (hrootSecond hr) hx hxSecond
  exact merge_supportedRootEmbeddings_of_rootReservoir
    F G roots major third (targetFirst ∪ targetSecond) targetThird
    rootImage rootReservoir outer hrootInj hrootMem hrootMajor hrootThird
    hmajorThird eMajor eThird

/-! ## Active owners and the composable Claim-6.16 split -/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- Original-root coordinates which own at least one branch in `s`. -/
def ownersOf {r b : ℕ} (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) : Finset (Fin r) :=
  s.image F.owner

@[simp] theorem mem_ownersOf {r b : ℕ} (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) (i : Fin r) :
    i ∈ ownersOf F s ↔ ∃ j ∈ s, F.owner j = i := by
  simp [ownersOf]

theorem ownersOf_mono {r b : ℕ} (F : OrderedBranchForest r b)
    {s t : Finset (Fin b)} (hst : s ⊆ t) :
    ownersOf F s ⊆ ownersOf F t := by
  intro i hi
  obtain ⟨j, hjs, hji⟩ := (mem_ownersOf F s i).mp hi
  exact (mem_ownersOf F t i).mpr ⟨j, hst hjs, hji⟩

theorem ownersOf_union {r b : ℕ} (F : OrderedBranchForest r b)
    (s t : Finset (Fin b)) :
    ownersOf F (s ∪ t) = ownersOf F s ∪ ownersOf F t := by
  ext i
  simp only [mem_ownersOf, Finset.mem_union]
  constructor
  · rintro ⟨j, hj, hji⟩
    rcases hj with hjs | hjt
    · exact Or.inl ⟨j, hjs, hji⟩
    · exact Or.inr ⟨j, hjt, hji⟩
  · rintro (⟨j, hjs, hji⟩ | ⟨j, hjt, hji⟩)
    · exact ⟨j, Or.inl hjs, hji⟩
    · exact ⟨j, Or.inr hjt, hji⟩

/-- Component-root coordinates of the canonical major parity. -/
def majorRootIndices (P : ZhaoForestPartition T globalRoot small) :
    Finset (Fin P.numParts) :=
  Finset.univ.filter fun i =>
    T.dist globalRoot (P.roots i) % 2 = (majorParity P).val

/-- Component-root coordinates of the complementary parity. -/
def minorRootIndices (P : ZhaoForestPartition T globalRoot small) :
    Finset (Fin P.numParts) :=
  Finset.univ.filter fun i =>
    T.dist globalRoot (P.roots i) % 2 = (minorParity P).val

theorem majorRootIndices_disjoint_minorRootIndices
    (P : ZhaoForestPartition T globalRoot small) :
    Disjoint (majorRootIndices P) (minorRootIndices P) := by
  rw [Finset.disjoint_left]
  intro i hiMajor hiMinor
  have hmajor := (Finset.mem_filter.mp hiMajor).2
  have hminor := (Finset.mem_filter.mp hiMinor).2
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simp [majorParity, minorParity, h] at hmajor hminor
    omega
  · simp [majorParity, minorParity, h] at hmajor hminor
    omega

theorem majorRootIndices_union_minorRootIndices
    (P : ZhaoForestPartition T globalRoot small) :
    majorRootIndices P ∪ minorRootIndices P = Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_univ, iff_true,
    majorRootIndices, minorRootIndices, Finset.mem_filter, true_and]
  have hmod : T.dist globalRoot (P.roots i) % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simp [majorParity, minorParity, h]
    omega
  · simp [majorParity, minorParity, h]
    omega

theorem ownersOf_halfBranches_subset_majorRootIndices
    (P : ZhaoForestPartition T globalRoot small) :
    ownersOf (branchForest P) (halfBranches P) ⊆ majorRootIndices P := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := (mem_ownersOf (branchForest P) (halfBranches P) i).mp hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩

theorem ownersOf_minorBranches_subset_minorRootIndices
    (P : ZhaoForestPartition T globalRoot small) :
    ownersOf (branchForest P) (minorBranches P) ⊆ minorRootIndices P := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ :=
    (mem_ownersOf (branchForest P) (minorBranches P) i).mp hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (mem_minorBranches P j).mp hj⟩

/-- Major-parity roots which own no major branch.  They are explicitly
assigned to the selected piece; they are the only isolated roots added to a
local support. -/
def isolatedMajorRootIndices
    (P : ZhaoForestPartition T globalRoot small) : Finset (Fin P.numParts) :=
  majorRootIndices P \ ownersOf (branchForest P) (halfBranches P)

def selectedRootIndices
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (Fin P.numParts) :=
  ownersOf (branchForest P) S.selected ∪ isolatedMajorRootIndices P

def F1RootIndices
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (Fin P.numParts) :=
  ownersOf (branchForest P) (majorResidualBranches P S)

def FbRootIndices (P : ZhaoForestPartition T globalRoot small) :
    Finset (Fin P.numParts) :=
  minorRootIndices P

theorem selectedRootIndices_union_F1RootIndices
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    selectedRootIndices P S ∪ F1RootIndices P S = majorRootIndices P := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hiSelected | hiF1
    · rcases Finset.mem_union.mp hiSelected with hiOwner | hiIsolated
      · exact ownersOf_halfBranches_subset_majorRootIndices P
          (ownersOf_mono (branchForest P) S.selected_available hiOwner)
      · exact (Finset.mem_sdiff.mp hiIsolated).1
    · exact ownersOf_halfBranches_subset_majorRootIndices P
        (ownersOf_mono (branchForest P)
          (fun j hj => (mem_majorResidualBranches P S j).mp hj |>.1) hiF1)
  · intro hiMajor
    by_cases hiOwner : i ∈ ownersOf (branchForest P) (halfBranches P)
    · obtain ⟨j, hjHalf, hji⟩ :=
        (mem_ownersOf (branchForest P) (halfBranches P) i).mp hiOwner
      by_cases hjSelected : j ∈ S.selected
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact (mem_ownersOf (branchForest P) S.selected i).mpr
          ⟨j, hjSelected, hji⟩
      · apply Finset.mem_union_right
        exact (mem_ownersOf (branchForest P) (majorResidualBranches P S) i).mpr
          ⟨j, (mem_majorResidualBranches P S j).mpr
            ⟨hjHalf, hjSelected⟩, hji⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨hiMajor, hiOwner⟩

def selectedSupport
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (branchForest P).Vertex :=
  OrderedBranchForest.rootedBranchSupport (branchForest P)
    (selectedRootIndices P S) S.selected

def F1Support
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (branchForest P).Vertex :=
  OrderedBranchForest.rootedBranchSupport (branchForest P)
    (F1RootIndices P S) (majorResidualBranches P S)

def majorSupport (P : ZhaoForestPartition T globalRoot small) :
    Finset (branchForest P).Vertex :=
  OrderedBranchForest.rootedBranchSupport (branchForest P)
    (majorRootIndices P) (halfBranches P)

def FbSupport (P : ZhaoForestPartition T globalRoot small) :
    Finset (branchForest P).Vertex :=
  OrderedBranchForest.rootedBranchSupport (branchForest P)
    (FbRootIndices P) (minorBranches P)

/-- The genuine intermediate split: selected `F₀` and residual `F₁` cover
the major support, not the full forest. -/
theorem selected_F1_supportPartition
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    SupportPartition (branchForest P).graph (branchForest P).roots
      (majorSupport P) (selectedSupport P S) (F1Support P S) := by
  apply OrderedBranchForest.rootedBranchSupportPartition
  · exact selectedRootIndices_union_F1RootIndices P S
  · exact selected_union_majorResidual P S
  · exact selected_disjoint_majorResidual P S
  · intro j hj
    apply Finset.mem_union_left
    exact (mem_ownersOf (branchForest P) S.selected _).mpr ⟨j, hj, rfl⟩
  · intro j hj
    exact (mem_ownersOf (branchForest P) (majorResidualBranches P S) _).mpr
      ⟨j, hj, rfl⟩

/-- The composable outer stage: the completed major certificate is merged
with the minor `F_b` certificate in the full branch forest. -/
theorem major_Fb_rootPartition
    (P : ZhaoForestPartition T globalRoot small) :
    RootPartition (branchForest P).graph (branchForest P).roots
      (majorSupport P) (FbSupport P) := by
  apply OrderedBranchForest.SupportPartition.toRootPartition (branchForest P)
  · apply OrderedBranchForest.rootedBranchSupportPartition
    · exact majorRootIndices_union_minorRootIndices P
    · exact halfBranches_union_minorBranches P
    · exact halfBranches_disjoint_minorBranches P
    · intro j hj
      exact ownersOf_halfBranches_subset_majorRootIndices P
        ((mem_ownersOf (branchForest P) (halfBranches P) _).mpr ⟨j, hj, rfl⟩)
    · intro j hj
      exact ownersOf_minorBranches_subset_minorRootIndices P
        ((mem_ownersOf (branchForest P) (minorBranches P) _).mpr ⟨j, hj, rfl⟩)
  · exact OrderedBranchForest.rootedBranchSupport_univ (branchForest P)

theorem selected_F1_Fb_support_cover
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (selectedSupport P S ∪ F1Support P S) ∪ FbSupport P = Finset.univ := by
  rw [(selected_F1_supportPartition P S).cover,
    (major_Fb_rootPartition P).cover]

theorem selected_F1_Fb_edge_cover
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    {x y : (branchForest P).Vertex} (hxy : (branchForest P).graph.Adj x y) :
    (x ∈ selectedSupport P S ∧ y ∈ selectedSupport P S) ∨
      (x ∈ F1Support P S ∧ y ∈ F1Support P S) ∨
      (x ∈ FbSupport P ∧ y ∈ FbSupport P) := by
  rcases (major_Fb_rootPartition P).edge_cover hxy with hMajor | hFb
  · rcases (selected_F1_supportPartition P S).edge_cover hxy
      hMajor.1 hMajor.2 with hSelected | hF1
    · exact Or.inl hSelected
    · exact Or.inr (Or.inl hF1)
  · exact Or.inr (Or.inr hFb)

namespace OrderedBranchForest

variable {r b : ℕ}

/-! ## Transport from a reindexed restriction to its literal support -/

/-- Canonical map from a restricted forest back to the original branch
coordinates. -/
def restrictVertexMap (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    (OrderedBranchForest.restrict F s).Vertex → F.Vertex
  | Sum.inl i => Sum.inl i
  | Sum.inr z => Sum.inr ⟨OrderedBranchForest.selectedEquiv s z.1, z.2⟩

theorem restrictVertexMap_mem_branchSupport
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (x : (OrderedBranchForest.restrict F s).Vertex) :
    restrictVertexMap F s x ∈ branchSupport F s := by
  rcases x with i | z
  · simp [restrictVertexMap]
  · apply (branch_mem_branchSupport_iff F s _).mpr
    exact (OrderedBranchForest.selectedEquiv s z.1).2

theorem restrictVertexMap_injective
    (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    Function.Injective (restrictVertexMap F s) := by
  rintro (i | ⟨j, a⟩) (k | ⟨l, c⟩) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · cases h
  · cases h
  · have hsigma := Sum.inr.inj h
    have hjlValue :
        (OrderedBranchForest.selectedEquiv s j).1 =
          (OrderedBranchForest.selectedEquiv s l).1 :=
      congrArg Sigma.fst hsigma
    have hjlSubtype : OrderedBranchForest.selectedEquiv s j =
        OrderedBranchForest.selectedEquiv s l := Subtype.ext hjlValue
    have hjl : j = l :=
      (OrderedBranchForest.selectedEquiv s).injective hjlSubtype
    subst l
    have hac : a = c := eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
    subst c
    rfl

theorem restrictVertexMap_adj_iff
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (x y : (OrderedBranchForest.restrict F s).Vertex) :
    (OrderedBranchForest.restrict F s).graph.Adj x y ↔
      F.graph.Adj (restrictVertexMap F s x) (restrictVertexMap F s y) := by
  rcases x with i | ⟨j, a⟩ <;> rcases y with k | ⟨l, c⟩
  · change False ↔ False
    rfl
  · rfl
  · rfl
  · constructor
    · rintro ⟨hjl, hadj⟩
      change j = l at hjl
      cases hjl
      refine ⟨rfl, ?_⟩
      change (F.branches.tree (OrderedBranchForest.selectedEquiv s j)).Adj a c at hadj
      exact hadj
    · rintro ⟨hjl, hadj⟩
      have hjlSubtype : OrderedBranchForest.selectedEquiv s j =
          OrderedBranchForest.selectedEquiv s l := Subtype.ext hjl
      have hindex : j = l :=
        (OrderedBranchForest.selectedEquiv s).injective hjlSubtype
      cases hindex
      refine ⟨rfl, ?_⟩
      change (F.branches.tree (OrderedBranchForest.selectedEquiv s j)).Adj a c
      exact hadj

theorem exists_restrictVertexMap_eq_of_mem_branchSupport
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    {x : F.Vertex} (hx : x ∈ branchSupport F s) :
    ∃ y, restrictVertexMap F s y = x := by
  rcases x with i | ⟨j, a⟩
  · exact ⟨Sum.inl i, rfl⟩
  · have hj : j ∈ s := (branch_mem_branchSupport_iff F s ⟨j, a⟩).mp hx
    let q : {j // j ∈ s} := ⟨j, hj⟩
    let k : Fin s.card := (OrderedBranchForest.selectedEquiv s).symm q
    have hk : OrderedBranchForest.selectedEquiv s k = q :=
      (OrderedBranchForest.selectedEquiv s).apply_symm_apply q
    have hex : ∃ a' : Fin ((OrderedBranchForest.restrict F s).branches.size k),
        (⟨(OrderedBranchForest.selectedEquiv s k).1, a'⟩ :
          Σ l, Fin (F.branches.size l)) = ⟨j, a⟩ := by
      change ∃ a' : Fin (F.branches.size (OrderedBranchForest.selectedEquiv s k)),
        (⟨(OrderedBranchForest.selectedEquiv s k).1, a'⟩ :
          Σ l, Fin (F.branches.size l)) = ⟨j, a⟩
      rw [hk]
      exact ⟨a, rfl⟩
    obtain ⟨a', ha'⟩ := hex
    exact ⟨Sum.inr ⟨k, a'⟩, congrArg Sum.inr ha'⟩

/-- The restriction vertex type is exactly the broad structural support. -/
noncomputable def restrictVertexEquiv
    (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    (OrderedBranchForest.restrict F s).Vertex ≃ {x // x ∈ branchSupport F s} :=
  Equiv.ofBijective
    (fun x => ⟨restrictVertexMap F s x,
      restrictVertexMap_mem_branchSupport F s x⟩)
    ⟨by
      intro x y hxy
      apply restrictVertexMap_injective F s
      exact congrArg Subtype.val hxy,
     by
      intro x
      obtain ⟨y, hy⟩ :=
        exists_restrictVertexMap_eq_of_mem_branchSupport F s x.2
      exact ⟨y, Subtype.ext hy⟩⟩

@[simp] theorem restrictVertexMap_mem_roots_iff
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (x : (OrderedBranchForest.restrict F s).Vertex) :
    restrictVertexMap F s x ∈ F.roots ↔
      x ∈ (OrderedBranchForest.restrict F s).roots := by
  rcases x with i | z
  · constructor <;> intro _
    · exact ((OrderedBranchForest.restrict F s).mem_roots_iff _).mpr ⟨i, rfl⟩
    · exact (F.mem_roots_iff _).mpr ⟨i, rfl⟩
  · constructor
    · intro h
      obtain ⟨i, hi⟩ := (F.mem_roots_iff _).mp h
      cases hi
    · intro h
      obtain ⟨i, hi⟩ := ((OrderedBranchForest.restrict F s).mem_roots_iff _).mp h
      cases hi

@[simp] theorem restrictVertexMap_mem_rootedBranchSupport_iff
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (q : Finset (Fin r))
    (x : (OrderedBranchForest.restrict F s).Vertex) :
    restrictVertexMap F s x ∈ rootedBranchSupport F q s ↔
      x ∈ rootedBranchSupport (OrderedBranchForest.restrict F s) q Finset.univ := by
  rcases x with i | z
  · exact (root_mem_rootedBranchSupport_iff F q s i).trans
      (root_mem_rootedBranchSupport_iff (OrderedBranchForest.restrict F s)
        q Finset.univ i).symm
  · constructor
    · intro _
      exact (branch_mem_rootedBranchSupport_iff
        (OrderedBranchForest.restrict F s) q Finset.univ z).mpr
          (Finset.mem_univ z.1)
    · intro _
      exact (branch_mem_rootedBranchSupport_iff F q s _).mpr
        (OrderedBranchForest.selectedEquiv s z.1).2

/-- Transport a realized supported embedding of `restrict F s` to the
literal support in `F`.  This is the concrete adapter needed after the lower
Lemma-5.8/Lemma-5.9 branch realizers; it does not add a copy premise. -/
noncomputable def supportedRootEmbeddingOfRestrict
    {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (q : Finset (Fin r)) (G : SimpleGraph B)
    (rootImage : F.Vertex → B)
    (target : Finset B)
    (E : SupportedRootEmbedding
      (OrderedBranchForest.restrict F s).graph G
      (OrderedBranchForest.restrict F s).roots
      (rootedBranchSupport (OrderedBranchForest.restrict F s) q Finset.univ)
      target (fun x => rootImage (restrictVertexMap F s x))) :
    SupportedRootEmbedding F.graph G F.roots
      (rootedBranchSupport F q s) target rootImage := by
  let phi := restrictVertexMap F s
  let equiv := restrictVertexEquiv F s
  have hsuppBroad : rootedBranchSupport F q s ⊆ branchSupport F s := by
    intro x hx
    rcases x with i | z
    · simp
    · simpa using
        (branch_mem_rootedBranchSupport_iff F q s z).mp hx
  let pre : ∀ x : F.Vertex, x ∈ rootedBranchSupport F q s →
      (OrderedBranchForest.restrict F s).Vertex :=
    fun x hx => equiv.symm ⟨x, hsuppBroad hx⟩
  have hpre_eq (x : F.Vertex) (hx : x ∈ rootedBranchSupport F q s) :
      phi (pre x hx) = x := by
    have h := equiv.apply_symm_apply ⟨x, hsuppBroad hx⟩
    exact congrArg Subtype.val h
  have hpre_mem (x : F.Vertex) (hx : x ∈ rootedBranchSupport F q s) :
      pre x hx ∈
        rootedBranchSupport (OrderedBranchForest.restrict F s) q Finset.univ := by
    rw [← restrictVertexMap_mem_rootedBranchSupport_iff F s q]
    change phi (pre x hx) ∈ rootedBranchSupport F q s
    simpa only [hpre_eq x hx] using hx
  let pushed : F.Vertex → B := fun x =>
    if hx : x ∈ rootedBranchSupport F q s then E.toFun (pre x hx)
    else rootImage x
  have hpushed (x : F.Vertex) (hx : x ∈ rootedBranchSupport F q s) :
      pushed x = E.toFun (pre x hx) := by
    simp only [pushed, hx, dite_true]
  refine
    { toFun := pushed
      map_adj := ?_
      injOn := ?_
      map_root := ?_
      map_nonroot := ?_ }
  · intro x y hxy hx hy
    rw [hpushed x hx, hpushed y hy]
    apply E.map_adj
    · apply (restrictVertexMap_adj_iff F s _ _).mpr
      simpa only [phi, hpre_eq x hx, hpre_eq y hy] using hxy
    · exact hpre_mem x hx
    · exact hpre_mem y hy
  · intro x y hx hy hxy
    have hpre : pre x hx = pre y hy :=
      E.injOn (hpre_mem x hx) (hpre_mem y hy) (by
        simpa only [hpushed x hx, hpushed y hy] using hxy)
    calc
      x = phi (pre x hx) := (hpre_eq x hx).symm
      _ = phi (pre y hy) := congrArg phi hpre
      _ = y := hpre_eq y hy
  · intro x hxRoot hx
    rw [hpushed x hx]
    have hpreRoot : pre x hx ∈ (OrderedBranchForest.restrict F s).roots := by
      rw [← restrictVertexMap_mem_roots_iff F s]
      change phi (pre x hx) ∈ F.roots
      simpa only [hpre_eq x hx] using hxRoot
    rw [E.map_root hpreRoot (hpre_mem x hx)]
    exact congrArg rootImage (hpre_eq x hx)
  · intro x hx hxRoot
    rw [hpushed x hx]
    apply E.map_nonroot (hpre_mem x hx)
    intro hpreRoot
    apply hxRoot
    rw [← hpre_eq x hx, restrictVertexMap_mem_roots_iff F s]
    exact hpreRoot

end OrderedBranchForest

end Erdos547b.ZhaoClaim616RootPartitions

#print axioms Erdos547b.ZhaoClaim616RootPartitions.selected_F1_supportPartition
#print axioms Erdos547b.ZhaoClaim616RootPartitions.major_Fb_rootPartition
#print axioms Erdos547b.ZhaoClaim616RootPartitions.OrderedBranchForest.supportedRootEmbeddingOfRestrict
#print axioms Erdos547b.ZhaoClaim616RootPartitions.merge_three_supportedRootEmbeddings_of_rootReservoir

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.OverlappingCycleCover

/-!
# The full KSSS bounded cycle-cover bank

Unlike the vertex-disjoint test bank, this bank includes every edge-faithful
quotient of the `C4 ∪ C5` and `3C4` templates.  Thus the constituent cycles
may share vertices, exactly as in KSSS Definition 4.4.
-/

namespace Erdos207

open Finset

noncomputable section

universe u

inductive FullCycleCoverCopy (Y : Type*) where
  | triangle (f : Fin 3 ↪ Y)
  | c4c5 (f : C4C5QuotientMap Y)
  | threeC4 (f : ThreeC4QuotientMap Y)
  deriving DecidableEq

def fullCycleCoverCopyEquiv (Y : Type*) :
    (Fin 3 ↪ Y) ⊕ C4C5QuotientMap Y ⊕ ThreeC4QuotientMap Y ≃
      FullCycleCoverCopy Y where
  toFun
    | Sum.inl f => .triangle f
    | Sum.inr (Sum.inl f) => .c4c5 f
    | Sum.inr (Sum.inr f) => .threeC4 f
  invFun
    | .triangle f => Sum.inl f
    | .c4c5 f => Sum.inr (Sum.inl f)
    | .threeC4 f => Sum.inr (Sum.inr f)
  left_inv x := by
    rcases x with (f | f)
    · rfl
    · rcases f with (f | f) <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance fullCycleCoverCopyFintype
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    Fintype (FullCycleCoverCopy Y) :=
  Fintype.ofEquiv
    ((Fin 3 ↪ Y) ⊕ C4C5QuotientMap Y ⊕ ThreeC4QuotientMap Y)
    (fullCycleCoverCopyEquiv Y)

/-- The private vertices needed by one copy.  The subtype records precisely
that a local vertex is not one of the shared target vertices. -/
def FullCycleCoverPrivate {Y : Type u} : FullCycleCoverCopy Y → Type u
  | .triangle _ => PEmpty
  | .c4c5 _ => {v : C4C5LocalVertex Y // IsC4C5LocalPrivate v}
  | .threeC4 _ => {v : ThreeC4LocalVertex Y // IsThreeC4LocalPrivate v}

noncomputable instance fullCycleCoverPrivateFintype
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) : Fintype (FullCycleCoverPrivate i) := by
  cases i <;> simp only [FullCycleCoverPrivate] <;> exact Fintype.ofFinite _

abbrev FullCycleCoverVertex (Y : Type*) :=
  Y ⊕ Sigma (FullCycleCoverPrivate (Y := Y))

noncomputable instance fullCycleCoverVertexFintype
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    Fintype (FullCycleCoverVertex Y) :=
  Fintype.ofFinite _

noncomputable instance fullCycleCoverVertexDecidableEq
    {Y : Type*} [DecidableEq Y] :
    DecidableEq (FullCycleCoverVertex Y) :=
  Classical.decEq _

def fullCycleCoverBaseEmbedding (Y : Type*) :
    Y ↪ FullCycleCoverVertex Y :=
  Function.Embedding.inl

def fullCycleCoverSigmaEmbedding {Y : Type u}
    (i : FullCycleCoverCopy Y) :
    FullCycleCoverPrivate i ↪
      Sigma (fun j : FullCycleCoverCopy Y => FullCycleCoverPrivate j) where
  toFun x := ⟨i, x⟩
  inj' := by
    intro x y h
    cases h
    rfl

def c4c5LocalSplitEquiv (Y : Type*) :
    C4C5LocalVertex Y ≃
      Y ⊕ {v : C4C5LocalVertex Y // IsC4C5LocalPrivate v} where
  toFun
    | Sum.inl (.target y) => Sum.inl y
    | Sum.inl (.source x) => Sum.inr ⟨Sum.inl (.source x), trivial⟩
    | Sum.inl (.edge e) => Sum.inr ⟨Sum.inl (.edge e), trivial⟩
    | Sum.inr k => Sum.inr ⟨Sum.inr k, trivial⟩
  invFun
    | Sum.inl y => Sum.inl (.target y)
    | Sum.inr v => v.1
  left_inv x := by
    rcases x with (x | k)
    · cases x <;> rfl
    · rfl
  right_inv x := by
    rcases x with (y | v)
    · rfl
    · rcases v with ⟨v, hv⟩
      rcases v with (v | k)
      · cases v with
        | source x => rfl
        | target y => exact hv.elim
        | edge e => rfl
      · rfl

def threeC4LocalSplitEquiv (Y : Type*) :
    ThreeC4LocalVertex Y ≃
      Y ⊕ {v : ThreeC4LocalVertex Y // IsThreeC4LocalPrivate v} where
  toFun
    | Sum.inl (.target y) => Sum.inl y
    | Sum.inl (.source x) => Sum.inr ⟨Sum.inl (.source x), trivial⟩
    | Sum.inl (.edge e) => Sum.inr ⟨Sum.inl (.edge e), trivial⟩
    | Sum.inr k => Sum.inr ⟨Sum.inr k, trivial⟩
  invFun
    | Sum.inl y => Sum.inl (.target y)
    | Sum.inr v => v.1
  left_inv x := by
    rcases x with (x | k)
    · cases x <;> rfl
    · rfl
  right_inv x := by
    rcases x with (y | v)
    · rfl
    · rcases v with ⟨v, hv⟩
      rcases v with (v | k)
      · cases v with
        | source x => rfl
        | target y => exact hv.elim
        | edge e => rfl
      · rfl

def c4c5FullAttachmentEmbedding {Y : Type*}
    (f : C4C5QuotientMap Y) :
    C4C5LocalVertex Y ↪ FullCycleCoverVertex Y :=
  (c4c5LocalSplitEquiv Y).toEmbedding.trans <|
    Function.Embedding.sumMap (Function.Embedding.refl Y)
      (fullCycleCoverSigmaEmbedding (FullCycleCoverCopy.c4c5 f))

def threeC4FullAttachmentEmbedding {Y : Type*}
    (f : ThreeC4QuotientMap Y) :
    ThreeC4LocalVertex Y ↪ FullCycleCoverVertex Y :=
  (threeC4LocalSplitEquiv Y).toEmbedding.trans <|
    Function.Embedding.sumMap (Function.Embedding.refl Y)
      (fullCycleCoverSigmaEmbedding (FullCycleCoverCopy.threeC4 f))

def fullCycleCoverTriangleTriple {Y : Type*} [DecidableEq Y]
    (f : Fin 3 ↪ Y) : TripleOn (FullCycleCoverVertex Y) :=
  mapTriple (f.trans (fullCycleCoverBaseEmbedding Y)) finThreeTriple

def fullCycleCoverRoot {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) : SimpleGraph (FullCycleCoverVertex Y) :=
  match i with
  | .triangle f => coveredGraph {fullCycleCoverTriangleTriple f}
  | .c4c5 f =>
      (c4c5LocalTargetRoot f).map (c4c5FullAttachmentEmbedding f)
  | .threeC4 f =>
      (threeC4LocalTargetRoot f).map (threeC4FullAttachmentEmbedding f)

def fullCycleCoverOut {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) : TripleSystemOn (FullCycleCoverVertex Y) :=
  match i with
  | .triangle _ => ∅
  | .c4c5 f => mapTripleSystem (c4c5FullAttachmentEmbedding f)
      (c4c5LocalOut f)
  | .threeC4 f => mapTripleSystem (threeC4FullAttachmentEmbedding f)
      (threeC4LocalOut f)

def fullCycleCoverIn {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) : TripleSystemOn (FullCycleCoverVertex Y) :=
  match i with
  | .triangle f => {fullCycleCoverTriangleTriple f}
  | .c4c5 f => mapTripleSystem (c4c5FullAttachmentEmbedding f)
      (c4c5LocalIn f)
  | .threeC4 f => mapTripleSystem (threeC4FullAttachmentEmbedding f)
      (threeC4LocalIn f)

theorem fullCycleCoverCopy_isExclusiveGraphAbsorber
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) :
    IsExclusiveGraphAbsorberOn (fullCycleCoverRoot i)
      (fullCycleCoverOut i) (fullCycleCoverIn i) := by
  cases i with
  | triangle f =>
      exact singleton_exclusiveGraphAbsorberOn
        (fullCycleCoverTriangleTriple f)
  | c4c5 f =>
      exact (c4c5Local_isExclusiveGraphAbsorber f).map
        (c4c5FullAttachmentEmbedding f)
  | threeC4 f =>
      exact (threeC4Local_isExclusiveGraphAbsorber f).map
        (threeC4FullAttachmentEmbedding f)

def BelongsToFullCycleCoverCopy {Y : Type*} (i : FullCycleCoverCopy Y) :
    FullCycleCoverVertex Y → Prop
  | Sum.inl _ => True
  | Sum.inr p => p.1 = i

def IsPrivateForFullCycleCoverCopy {Y : Type*} (i : FullCycleCoverCopy Y) :
    FullCycleCoverVertex Y → Prop
  | Sum.inl _ => False
  | Sum.inr p => p.1 = i

lemma privateForFull_implies_belongs {Y : Type*}
    {i : FullCycleCoverCopy Y} {v : FullCycleCoverVertex Y}
    (h : IsPrivateForFullCycleCoverCopy i v) :
    BelongsToFullCycleCoverCopy i v := by
  cases v with
  | inl y => exact h.elim
  | inr p => exact h

lemma privateForFull_and_belongs_iff_eq {Y : Type*}
    {i j : FullCycleCoverCopy Y} {v : FullCycleCoverVertex Y}
    (hi : IsPrivateForFullCycleCoverCopy i v)
    (hj : BelongsToFullCycleCoverCopy j v) : i = j := by
  cases v with
  | inl y => exact hi.elim
  | inr p => exact hi.symm.trans hj

@[simp]
lemma c4c5FullAttachmentEmbedding_target {Y : Type*}
    (f : C4C5QuotientMap Y) (y : Y) :
    c4c5FullAttachmentEmbedding f (Sum.inl (.target y)) = Sum.inl y :=
  rfl

@[simp]
lemma threeC4FullAttachmentEmbedding_target {Y : Type*}
    (f : ThreeC4QuotientMap Y) (y : Y) :
    threeC4FullAttachmentEmbedding f (Sum.inl (.target y)) = Sum.inl y :=
  rfl

lemma c4c5FullAttachmentEmbedding_belongs {Y : Type*}
    (f : C4C5QuotientMap Y) (x : C4C5LocalVertex Y) :
    BelongsToFullCycleCoverCopy (.c4c5 f)
      (c4c5FullAttachmentEmbedding f x) := by
  rcases x with (x | k)
  · cases x with
    | source x => change FullCycleCoverCopy.c4c5 f = _; rfl
    | target y => trivial
    | edge e => change FullCycleCoverCopy.c4c5 f = _; rfl
  · change FullCycleCoverCopy.c4c5 f = _
    rfl

lemma threeC4FullAttachmentEmbedding_belongs {Y : Type*}
    (f : ThreeC4QuotientMap Y) (x : ThreeC4LocalVertex Y) :
    BelongsToFullCycleCoverCopy (.threeC4 f)
      (threeC4FullAttachmentEmbedding f x) := by
  rcases x with (x | k)
  · cases x with
    | source x => change FullCycleCoverCopy.threeC4 f = _; rfl
    | target y => trivial
    | edge e => change FullCycleCoverCopy.threeC4 f = _; rfl
  · change FullCycleCoverCopy.threeC4 f = _
    rfl

lemma c4c5FullAttachmentEmbedding_private {Y : Type*}
    (f : C4C5QuotientMap Y) {x : C4C5LocalVertex Y}
    (hx : IsC4C5LocalPrivate x) :
    IsPrivateForFullCycleCoverCopy (.c4c5 f)
      (c4c5FullAttachmentEmbedding f x) := by
  rcases x with (x | k)
  · cases x with
    | source x => rfl
    | target y => exact hx.elim
    | edge e => rfl
  · rfl

lemma threeC4FullAttachmentEmbedding_private {Y : Type*}
    (f : ThreeC4QuotientMap Y) {x : ThreeC4LocalVertex Y}
    (hx : IsThreeC4LocalPrivate x) :
    IsPrivateForFullCycleCoverCopy (.threeC4 f)
      (threeC4FullAttachmentEmbedding f x) := by
  rcases x with (x | k)
  · cases x with
    | source x => rfl
    | target y => exact hx.elim
    | edge e => rfl
  · rfl

lemma fullCycleCoverOut_edge_structure
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) {u v : FullCycleCoverVertex Y}
    (huv : (coveredGraph (fullCycleCoverOut i)).Adj u v) :
    BelongsToFullCycleCoverCopy i u ∧ BelongsToFullCycleCoverCopy i v ∧
      (IsPrivateForFullCycleCoverCopy i u ∨
        IsPrivateForFullCycleCoverCopy i v) := by
  cases i with
  | triangle f => simp [fullCycleCoverOut, coveredGraph] at huv
  | c4c5 f =>
      simp only [fullCycleCoverOut, coveredGraph_mapTripleSystem,
        SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      refine ⟨c4c5FullAttachmentEmbedding_belongs f a,
        c4c5FullAttachmentEmbedding_belongs f b, ?_⟩
      rcases c4c5LocalOut_edge_has_private f hab with ha | hb
      · exact Or.inl (c4c5FullAttachmentEmbedding_private f ha)
      · exact Or.inr (c4c5FullAttachmentEmbedding_private f hb)
  | threeC4 f =>
      simp only [fullCycleCoverOut, coveredGraph_mapTripleSystem,
        SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      refine ⟨threeC4FullAttachmentEmbedding_belongs f a,
        threeC4FullAttachmentEmbedding_belongs f b, ?_⟩
      rcases threeC4LocalOut_edge_has_private f hab with ha | hb
      · exact Or.inl (threeC4FullAttachmentEmbedding_private f ha)
      · exact Or.inr (threeC4FullAttachmentEmbedding_private f hb)

lemma fullCycleCoverRoot_edge_base
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) {u v : FullCycleCoverVertex Y}
    (huv : (fullCycleCoverRoot i).Adj u v) :
    (∃ y : Y, u = Sum.inl y) ∧ ∃ z : Y, v = Sum.inl z := by
  cases i with
  | triangle f =>
      obtain ⟨T, hT, huT, hvT, huvne⟩ := huv
      simp only [fullCycleCoverRoot, mem_singleton] at hT
      subst T
      obtain ⟨a, ha, hau⟩ := Finset.mem_map.mp huT
      obtain ⟨b, hb, hbv⟩ := Finset.mem_map.mp hvT
      exact ⟨⟨f a, hau.symm⟩, ⟨f b, hbv.symm⟩⟩
  | c4c5 f =>
      simp only [fullCycleCoverRoot, SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      unfold c4c5LocalTargetRoot at hab
      rw [SimpleGraph.map_adj] at hab
      obtain ⟨a, b, hab, rfl, rfl⟩ := hab
      rw [transformerTargetRoot, SimpleGraph.map_adj] at hab
      obtain ⟨y, z, hyz, rfl, rfl⟩ := hab
      exact ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩
  | threeC4 f =>
      simp only [fullCycleCoverRoot, SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      unfold threeC4LocalTargetRoot at hab
      rw [SimpleGraph.map_adj] at hab
      obtain ⟨a, b, hab, rfl, rfl⟩ := hab
      rw [transformerTargetRoot, SimpleGraph.map_adj] at hab
      obtain ⟨y, z, hyz, rfl, rfl⟩ := hab
      exact ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩

lemma fullCycleCoverOut_pairwise_disjoint
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {i j : FullCycleCoverCopy Y} (hij : i ≠ j) :
    Disjoint (coveredGraph (fullCycleCoverOut i))
      (coveredGraph (fullCycleCoverOut j)) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e hei hej
  induction e using Sym2.ind with
  | h u v =>
      have hi := fullCycleCoverOut_edge_structure i hei
      have hj := fullCycleCoverOut_edge_structure j hej
      rcases hi.2.2 with hpriv | hpriv
      · exact hij (privateForFull_and_belongs_iff_eq hpriv hj.1)
      · exact hij (privateForFull_and_belongs_iff_eq hpriv hj.2.1)

lemma fullCycleCoverOut_root_disjoint
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i j : FullCycleCoverCopy Y) :
    Disjoint (coveredGraph (fullCycleCoverOut i))
      (fullCycleCoverRoot j) := by
  rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
  intro e hei hej
  induction e using Sym2.ind with
  | h u v =>
      have hi := fullCycleCoverOut_edge_structure i hei
      obtain ⟨⟨y, huy⟩, ⟨z, hvz⟩⟩ :=
        fullCycleCoverRoot_edge_base j hej
      change u = Sum.inl y at huy
      change v = Sum.inl z at hvz
      rcases hi.2.2 with hpriv | hpriv
      · simpa [huy, IsPrivateForFullCycleCoverCopy] using hpriv
      · simpa [hvz, IsPrivateForFullCycleCoverCopy] using hpriv

/-- The full bounded cycle-cover bank absorbs every selected edge-disjoint
family of triangles and edge-faithful grouped cycle quotients. -/
theorem universalFullCycleCoverBank_switch
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (selected : Finset (FullCycleCoverCopy Y))
    (hroots : ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
      Disjoint (fullCycleCoverRoot i) (fullCycleCoverRoot j)) :
    IsTriangleDecomposition
      (graphSup univ
        (switchedAbsorberGraph selected fullCycleCoverRoot fullCycleCoverOut))
      (tripleUnion univ
        (switchedAbsorberTriples selected fullCycleCoverOut
          fullCycleCoverIn)) := by
  apply exclusiveAbsorberBank_switch_of_switched_disjoint
  · intro i hi
    exact fullCycleCoverCopy_isExclusiveGraphAbsorber i
  · intro i hi j hj hij
    by_cases hisel : i ∈ selected <;> by_cases hjsel : j ∈ selected
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_true]
      rw [disjoint_sup_left, disjoint_sup_right, disjoint_sup_right]
      exact ⟨⟨fullCycleCoverOut_pairwise_disjoint hij,
        fullCycleCoverOut_root_disjoint i j⟩,
        ⟨(fullCycleCoverOut_root_disjoint j i).symm,
          hroots i hisel j hjsel hij⟩⟩
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_true, if_false,
        sup_bot_eq]
      rw [disjoint_sup_left]
      exact ⟨fullCycleCoverOut_pairwise_disjoint hij,
        (fullCycleCoverOut_root_disjoint j i).symm⟩
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_true, if_false,
        sup_bot_eq]
      rw [disjoint_sup_right]
      exact ⟨fullCycleCoverOut_pairwise_disjoint hij,
        fullCycleCoverOut_root_disjoint i j⟩
    · simp only [switchedAbsorberGraph, hisel, hjsel, if_false, sup_bot_eq]
      exact fullCycleCoverOut_pairwise_disjoint hij

/-- A graph is grouped in the sense of KSSS Definition 4.4 when it is the
edge-disjoint supremum of a selected family of allowed bounded roots. -/
def HasFullCycleCoverGrouping
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (G : SimpleGraph (FullCycleCoverVertex Y)) : Prop :=
  ∃ selected : Finset (FullCycleCoverCopy Y),
    graphSup selected fullCycleCoverRoot = G ∧
      ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
        Disjoint (fullCycleCoverRoot i) (fullCycleCoverRoot j)

/-- Exact absorption interface for a grouped leftover: the fixed union of
all out-gadgets together with the leftover has a triangle decomposition. -/
theorem fullCycleCover_absorbs_grouped
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {G : SimpleGraph (FullCycleCoverVertex Y)}
    (hG : HasFullCycleCoverGrouping G) :
    ∃ C : TripleSystemOn (FullCycleCoverVertex Y),
      IsTriangleDecomposition
        (graphSup univ (fun i => coveredGraph (fullCycleCoverOut i)) ⊔ G) C := by
  obtain ⟨selected, hselected, hdisjoint⟩ := hG
  let C := tripleUnion univ
    (switchedAbsorberTriples selected fullCycleCoverOut fullCycleCoverIn)
  refine ⟨C, ?_⟩
  rw [← hselected, ← graphSup_univ_switchedAbsorberGraph]
  exact universalFullCycleCoverBank_switch selected hdisjoint

/-- Arithmetic behind the grouping step: after pairing each five-cycle with
a four-cycle, divisibility of the total edge count leaves a multiple of three
four-cycles. -/
lemma shortCycle_counts_groupable (triangles fourCycles fiveCycles : ℕ)
    (hmore : fiveCycles ≤ fourCycles)
    (hdiv : 3 ∣ 3 * triangles + 4 * fourCycles + 5 * fiveCycles) :
    ∃ threeFourGroups : ℕ,
      fourCycles = fiveCycles + 3 * threeFourGroups := by
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨(fourCycles - fiveCycles) / 3, ?_⟩
  omega

end

end Erdos207

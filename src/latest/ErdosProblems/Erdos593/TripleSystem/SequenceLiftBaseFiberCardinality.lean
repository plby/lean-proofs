import Mathlib.Data.Set.Card.Arithmetic
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIndex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite cardinality decomposition of sequence-lift base fibres

For a finite selected family of sequence-lift edges, the canonical base fibres
give an exact finite partition indexed by its active base nodes.  For an
embedded finite source, that partition can equivalently be expressed by the
subtypes of source-edge indices at each active base node.

These are finite selected-edge identities only.  In particular, this module
does not assert a global decomposition of base-letter images or of a trace.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite selected family has cardinality equal to the sum of the
cardinalities of its nonempty canonical base fibres. -/
theorem ncard_eq_sum_baseFiber_activeBaseNodeIndex
    {S : Set (Edge G)} (hS : S.Finite) :
    S.ncard =
      (@Finset.univ (activeBaseNodeIndex S) (activeBaseNodeIndexFintype hS)).sum
        (fun q => (baseFiber S q.1).ncard) := by
  classical
  letI : Fintype (activeBaseNodeIndex S) := activeBaseNodeIndexFintype hS
  have hsum := Set.ncard_iUnion_of_finite
    (s := fun q : activeBaseNodeIndex S => baseFiber S q.1)
    (fun q => hS.subset (baseFiber_subset S q.1))
    (fun q r hqr =>
      (pairwiseDisjoint_baseFiber_activeBaseNodeIndex S) (by simp) (by simp) hqr)
  simpa only [iUnion_baseFiber_activeBaseNodeIndex, finsum_eq_sum_of_fintype] using! hsum

/-- An embedded source-edge index is exactly a pair of an active base-node
index and a source-edge index in its corresponding canonical base fibre. -/
noncomputable def edgeIndexEquiv_sigmaBaseFiberIndex
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    (f : F.Embedding (system G)) :
    Equiv (Sigma (fun q : activeBaseNodeIndex f.edgeImage => baseFiberIndex f q.1)) E where
  toFun := fun x => x.2.1
  invFun := fun i => Sigma.mk (baseNodeIndexMap f i) (Subtype.mk i rfl)
  left_inv := by
    intro x
    cases x with
    | mk q i =>
      cases i with
      | mk i hi =>
        have hq : baseNodeIndexMap f i = q := Subtype.ext hi
        subst q
        rfl
  right_inv := by
    intro i
    rfl

/-- The finite edge image of an embedded source has cardinality equal to the
sum of the exact source-edge index subtypes in its active canonical base
fibres. -/
theorem edgeImage_ncard_eq_sum_baseFiberIndex
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E] (f : F.Embedding (system G)) :
    f.edgeImage.ncard =
      (@Finset.univ (activeBaseNodeIndex f.edgeImage)
        (activeBaseNodeIndexFintype (Set.finite_range f.edge))).sum
        (fun q =>
          @Fintype.card (baseFiberIndex f q.1) (baseFiberIndexFintype f q.1)) := by
  calc
    f.edgeImage.ncard =
        (@Finset.univ (activeBaseNodeIndex f.edgeImage)
          (activeBaseNodeIndexFintype (Set.finite_range f.edge))).sum
          (fun q => (baseFiber f.edgeImage q.1).ncard) :=
      ncard_eq_sum_baseFiber_activeBaseNodeIndex (Set.finite_range f.edge)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact baseFiber_edgeImage_ncard_eq_baseFiberIndex_card f q.1

/-- The number of source edges equals the sum of the exact source-edge index
subtypes in its active canonical base fibres. -/
theorem edge_card_eq_sum_baseFiberIndex_card
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E] (f : F.Embedding (system G)) :
    Fintype.card E =
      Finset.sum
        (@Finset.univ (activeBaseNodeIndex f.edgeImage)
          (activeBaseNodeIndexFintype (Set.finite_range f.edge)))
        (fun q => @Fintype.card (baseFiberIndex f q.1) (baseFiberIndexFintype f q.1)) := by
  letI : Fintype (activeBaseNodeIndex f.edgeImage) :=
    activeBaseNodeIndexFintype (Set.finite_range f.edge)
  letI : (q : activeBaseNodeIndex f.edgeImage) -> Fintype (baseFiberIndex f q.1) :=
    fun q => baseFiberIndexFintype f q.1
  calc
    Fintype.card E = Fintype.card
        (Sigma (fun q : activeBaseNodeIndex f.edgeImage => baseFiberIndex f q.1)) :=
      (Fintype.card_congr (edgeIndexEquiv_sigmaBaseFiberIndex f)).symm
    _ = Finset.sum Finset.univ (fun q : activeBaseNodeIndex f.edgeImage =>
        Fintype.card (baseFiberIndex f q.1)) := Fintype.card_sigma
    _ = Finset.sum
        (@Finset.univ (activeBaseNodeIndex f.edgeImage)
          (activeBaseNodeIndexFintype (Set.finite_range f.edge)))
        (fun q => @Fintype.card (baseFiberIndex f q.1) (baseFiberIndexFintype f q.1)) := rfl

end SequenceLift

end Erdos593

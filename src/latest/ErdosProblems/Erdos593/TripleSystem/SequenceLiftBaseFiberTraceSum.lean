import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberCardinality

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite local-letter sums of sequence-lift base fibres

For a finite linear selected family of sequence-lift edges, the exact
cardinality sum over canonical base fibres can be written using the distinct
base letters inside each fibre.  The embedded-source specializations and the
trace-key cardinality identity then follow from this local sum.

These statements sum separate fibres.  They neither identify base letters
across different base nodes nor assert a global base-letter union or a full
trace decomposition.
-/

namespace Erdos593

universe u v w

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A finite linear selected family has cardinality equal to the sum of the
distinct base-letter images inside its separate active canonical base fibres.
Multiplicity across different base nodes is deliberately retained. -/
theorem ncard_eq_sum_baseLetter_image_activeBaseNodeIndex_of_linear
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    S.ncard =
      (@Finset.univ (activeBaseNodeIndex S) (activeBaseNodeIndexFintype hS)).sum
        (fun q => (baseLetter '' baseFiber S q.1).ncard) := by
  calc
    S.ncard =
        (@Finset.univ (activeBaseNodeIndex S)
          (activeBaseNodeIndexFintype hS)).sum
          (fun q => (baseFiber S q.1).ncard) :=
      ncard_eq_sum_baseFiber_activeBaseNodeIndex hS
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact (ncard_baseLetter_image_eq_on_baseFiber_of_linear q.1 hlinear).symm

/-- For a finite linear source with no isolated points, the embedded edge image
has cardinality equal to the sum of its distinct local base-letter images over
the active canonical base nodes. -/
theorem edgeImage_ncard_eq_sum_baseLetter_image_ncard
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E] (f : F.Embedding (system G)) (hF : F.HasNoIsolatedPoints)
    (hlinear : F.Linear) :
    f.edgeImage.ncard =
      (@Finset.univ (activeBaseNodeIndex f.edgeImage)
        (activeBaseNodeIndexFintype (Set.finite_range f.edge))).sum
        (fun q => (baseLetter '' baseFiber f.edgeImage q.1).ncard) := by
  exact ncard_eq_sum_baseLetter_image_activeBaseNodeIndex_of_linear
    (Set.finite_range f.edge) (f.imageEdgeRestriction_linear hF hlinear)

/-- The number of source edges equals the sum of distinct local base-letter
images in the active canonical base fibres of its sequence-lift embedding. -/
theorem edge_card_eq_sum_baseLetter_image_ncard
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E] (f : F.Embedding (system G)) (hF : F.HasNoIsolatedPoints)
    (hlinear : F.Linear) :
    Fintype.card E =
      (@Finset.univ (activeBaseNodeIndex f.edgeImage)
        (activeBaseNodeIndexFintype (Set.finite_range f.edge))).sum
        (fun q => (baseLetter '' baseFiber f.edgeImage q.1).ncard) := by
  calc
    Fintype.card E =
        (@Finset.univ (activeBaseNodeIndex f.edgeImage)
          (activeBaseNodeIndexFintype (Set.finite_range f.edge))).sum
          (fun q => @Fintype.card (baseFiberIndex f q.1)
            (baseFiberIndexFintype f q.1)) :=
      edge_card_eq_sum_baseFiberIndex_card f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact (finiteLinear_baseLetter_image_ncard_eq_baseFiberIndex_card
        f hF hlinear q.1).symm

/-- The finite canonical trace-key image has cardinality equal to the sum of
distinct base-letter images inside its separate active canonical base fibres. -/
theorem traceKey_image_ncard_eq_sum_baseLetter_image_ncard
    {W : Type v} {E : Type w} {F : TripleSystem W E}
    [Fintype E] (f : F.Embedding (system G)) (hF : F.HasNoIsolatedPoints)
    (hlinear : F.Linear) :
    (traceKey '' f.edgeImage).ncard =
      (@Finset.univ (activeBaseNodeIndex f.edgeImage)
        (activeBaseNodeIndexFintype (Set.finite_range f.edge))).sum
        (fun q => (baseLetter '' baseFiber f.edgeImage q.1).ncard) := by
  calc
    (traceKey '' f.edgeImage).ncard = Fintype.card E :=
      (finiteLinear_traceKey_image f hF hlinear).2
    _ = _ := edge_card_eq_sum_baseLetter_image_ncard f hF hlinear

end SequenceLift

end Erdos593

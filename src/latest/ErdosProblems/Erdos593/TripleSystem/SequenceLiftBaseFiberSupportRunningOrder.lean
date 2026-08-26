import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberAssembly
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupport

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Running support orders for sequence-lift base fibres

Pairwise linearity makes the support intersection of any two distinct base
fibres empty or a singleton.  To turn that pairwise fact into a running
assembly, the nonempty overlaps of a newly attached fibre with the already
assembled tail must all be the same intersection.  The recursive predicate
below records exactly that local coherence condition.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A list of base nodes is a coherent support running order when, at every
head `q`, all nonempty pairwise support intersections of `baseFiber S q` with
fibres in the already assembled tail are equal.  The list is newest first.

Together with the pairwise singleton-or-empty consequence of linearity, this
is the exact non-tautological condition ensuring that the head meets the
support of the whole tail in at most one point. -/
def baseFiberSupportTailOverlapCoherent
    (S : Set (Edge G)) : List (Node G) → Prop
  | [] => True
  | q :: nodes =>
      baseFiberSupportTailOverlapCoherent S nodes ∧
      ∀ u ∈ nodes, ∀ v ∈ nodes,
        (((system G).edgeSupportSet (baseFiber S q) ∩
          (system G).edgeSupportSet (baseFiber S u)).Nonempty) →
        (((system G).edgeSupportSet (baseFiber S q) ∩
          (system G).edgeSupportSet (baseFiber S v)).Nonempty) →
        ((system G).edgeSupportSet (baseFiber S q) ∩
          (system G).edgeSupportSet (baseFiber S u)) =
          ((system G).edgeSupportSet (baseFiber S q) ∩
            (system G).edgeSupportSet (baseFiber S v))

/-- Pairwise support linearity plus a noduplicated coherent support order
gives the exact recursive geometry required by `baseFiberAssemblyCompatible`.

No finiteness assumption on `S` is needed: the finite object is the supplied
list of base nodes. -/
theorem baseFiberAssemblyCompatible_of_linear_of_nodup_of_supportTailOverlapCoherent
    {S : Set (Edge G)} {nodes : List (Node G)}
    (hlinear : ((system G).edgeRestriction S).Linear)
    (hnodup : nodes.Nodup)
    (hcoherent : baseFiberSupportTailOverlapCoherent S nodes) :
    baseFiberAssemblyCompatible S nodes := by
  induction nodes with
  | nil =>
      trivial
  | cons q nodes ih =>
      rw [List.nodup_cons] at hnodup
      change baseFiberSupportTailOverlapCoherent S nodes ∧ _ at hcoherent
      rcases hcoherent with ⟨hcoherentTail, hcoherentHead⟩
      refine ⟨ih hnodup.2 hcoherentTail, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro e hePrevious heQ
        rcases (mem_edgePieceUnion_baseFiberList S nodes).mp hePrevious with
          ⟨u, hu, heU⟩
        have hqu : q ≠ u := by
          intro hq
          exact hnodup.1 (hq.symm ▸ hu)
        exact (Set.disjoint_left.mp (baseFiber_disjoint hqu)) heQ heU
      · by_cases hdisjoint : Disjoint
            ((system G).edgeSupportSet
              (TripleSystem.edgePieceUnion (nodes.map (baseFiber S))))
            ((system G).edgeSupportSet (baseFiber S q))
        · exact Or.inl hdisjoint
        · right
          rcases Set.not_disjoint_iff.mp hdisjoint with
            ⟨r, hrPrevious, hrQ⟩
          refine ⟨r, Set.Subset.antisymm ?_ ?_⟩
          · intro x hx
            rcases hx.1 with ⟨e, hePrevious, hxe⟩
            rcases (mem_edgePieceUnion_baseFiberList S nodes).mp hePrevious with
              ⟨u, hu, heU⟩
            have hxU :
                x ∈ (system G).edgeSupportSet (baseFiber S u) :=
              ⟨e, heU, hxe⟩
            rcases hrPrevious with ⟨f, hfPrevious, hrf⟩
            rcases (mem_edgePieceUnion_baseFiberList S nodes).mp hfPrevious with
              ⟨v, hv, hfV⟩
            have hrV :
                r ∈ (system G).edgeSupportSet (baseFiber S v) :=
              ⟨f, hfV, hrf⟩
            have hintersections :=
              hcoherentHead u hu v hv
                ⟨x, hx.2, hxU⟩ ⟨r, hrQ, hrV⟩
            have hqv : q ≠ v := by
              intro hqv
              exact hnodup.1 (hqv.symm ▸ hv)
            have hsubsingleton :=
              baseFiber_support_inter_subsingleton_of_linear hlinear hqv
            have hxV :
                x ∈ (system G).edgeSupportSet (baseFiber S q) ∩
                  (system G).edgeSupportSet (baseFiber S v) := by
              rw [← hintersections]
              exact ⟨hx.2, hxU⟩
            have hrV' :
                r ∈ (system G).edgeSupportSet (baseFiber S q) ∩
                  (system G).edgeSupportSet (baseFiber S v) :=
              ⟨hrQ, hrV⟩
            exact Set.mem_singleton_iff.mpr (hsubsingleton hxV hrV')
          · intro x hx
            have hxr : x = r := Set.mem_singleton_iff.mp hx
            simpa [hxr] using! And.intro hrPrevious hrQ

end SequenceLift

end Erdos593

/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClosedClassifiedContactSegmentation

/-!
# The zero-edge branch of mixed contact segmentation

The fractured assignment compiler can retain an uncovered singleton as the
trivial alternating path.  This is the missing zero-edge case beside the
positive finite-input and infinite-input contact splitters.  Its unique
vertex is already in the closing set, so the exact mixed segmentation has
no pieces and contributes no relation edge.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X persistent : Set V} {kappa : Cardinal.{u}}

/-- The trivial alternating path has the exact zero-piece mixed contact
segmentation.  The closing-set membership is recorded because its sole
contact is the path's exposed source. -/
def trivialClosedClassifiedContactSegmentation
    (x : V) (_hx : x ∈ X) :
    FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) (AltPath.trivial x) X where
  count := 0
  point := fun _ => x
  point_injective := by
    intro i j _
    apply Fin.ext
    omega
  piece := fun i => Fin.elim0 i
  initial_eq := rfl
  terminal_eq := rfl
  vertexSet_exact := by
    ext y
    simp [AltPath.vertexSet]
  edgeSet_exact := by
    ext e
    simp [AltPath.edgeSet]

/-- Sum-typed form used by the total compressor-realization splitter. -/
def trivialClosedClassifiedContactSegmentationSum
    (x : V) (hx : x ∈ X) :
    ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) (AltPath.trivial x) X persistent :=
  .finite (trivialClosedClassifiedContactSegmentation
    (Y := Y) (kappa := kappa) x hx)

@[simp] theorem trivialClosedClassifiedContactSegmentationSum_shortcutEdges
    (x : V) (hx : x ∈ X) :
    (trivialClosedClassifiedContactSegmentationSum
      (Y := Y) (persistent := persistent) (kappa := kappa) x hx).shortcutEdges =
      ∅ := by
  ext e
  simp [trivialClosedClassifiedContactSegmentationSum,
    trivialClosedClassifiedContactSegmentation,
    ClosedClassifiedContactSegmentation.shortcutEdges,
    FiniteClosedClassifiedContactSegmentation.toChain,
    ClosedClassifiedContactChain.shortcutEdges]

@[simp] theorem trivialClosedClassifiedContactSegmentationSum_retainedEdges
    (x : V) (hx : x ∈ X) :
    (trivialClosedClassifiedContactSegmentationSum
      (Y := Y) (persistent := persistent) (kappa := kappa) x hx).retainedEdges =
      ∅ := by
  ext e
  simp [trivialClosedClassifiedContactSegmentationSum,
    trivialClosedClassifiedContactSegmentation,
    ClosedClassifiedContactSegmentation.retainedEdges,
    FiniteClosedClassifiedContactSegmentation.toChain,
    ClosedClassifiedContactChain.retainedEdges]

end Erdos599.Blueprint.LinkageBlueprint

#print axioms Erdos599.Blueprint.LinkageBlueprint.trivialClosedClassifiedContactSegmentation
#print axioms Erdos599.Blueprint.LinkageBlueprint.trivialClosedClassifiedContactSegmentationSum_shortcutEdges

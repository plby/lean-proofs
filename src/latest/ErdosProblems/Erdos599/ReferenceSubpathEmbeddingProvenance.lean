/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ReferenceSubpathEmbedding
import ErdosProblems.Erdos599.FracturedAssignmentProducedBackwardProvenance

/-! # Retaining indexed backward owners under reference embeddings -/

noncomputable section

namespace Erdos599.Blueprint

open _root_.Erdos599.Alternating

universe u v

variable {V : Type u} {Gamma : DWeb V}
variable {Local Global : Set Gamma.DPath}

namespace ReferenceSubpathEmbedding

/-- Transport the actual indexed owner certificate without changing its
links or their indexing.  Owner uniqueness follows from injectivity of the
reference embedding. -/
def indexedBackwardProvenance
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph} {I : Type v}
    (P : Q.IndexedBackwardProvenance Local I) :
    Q.IndexedBackwardProvenance Global I where
  link := P.link
  links_eq_range := P.links_eq_range
  owner i hi := (E.owner ⟨P.owner i hi, P.owner_mem i hi⟩).1
  owner_mem i hi := (E.owner ⟨P.owner i hi, P.owner_mem i hi⟩).2
  isSubpath i hi :=
    ⟨(P.isSubpath i hi).1.trans
        (E.support_subset ⟨P.owner i hi, P.owner_mem i hi⟩),
      (P.isSubpath i hi).2.trans
        (E.edgeSet_subset ⟨P.owner i hi, P.owner_mem i hi⟩)⟩
  owner_unique := by
    intro i j hi hj howner
    apply P.owner_unique i j hi hj
    exact congrArg Subtype.val (E.owner_injective (Subtype.ext howner))

/-- The existentially indexed certificate used by the actual fractured
compiler promotes by the same injective owner map. -/
def hasIndexedBackwardProvenance
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {Q : AltPath Gamma.graph}
    (P : LinkageBlueprint.FracturedAssignmentPeel.HasIndexedBackwardProvenance Q Local) :
    LinkageBlueprint.FracturedAssignmentPeel.HasIndexedBackwardProvenance Q Global :=
  ⟨P.Index, E.indexedBackwardProvenance P.certificate⟩

end ReferenceSubpathEmbedding

#print axioms ReferenceSubpathEmbedding.indexedBackwardProvenance
#print axioms ReferenceSubpathEmbedding.hasIndexedBackwardProvenance

end Erdos599.Blueprint

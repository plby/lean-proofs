/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceCrossSplice

/-!
# Inserting a closed coloured occurrence word

An owner-gap repair can discover a closed coloured component based at an
occurrence of an open route.  This file inserts that component at the chosen
occurrence.  The construction is purely literal: same-colour freshness is
proved for both append operations, and the resulting word has the old outer
endpoints and exactly the union of the two edge relations.

No interval-safeness conclusion is asserted here.  Establishing that the
inserted component fills (rather than creates) owner gaps is the separate
decreasing-gap argument.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FiniteColouredOccurrenceWord

variable {W Y : Set Gamma.DPath}

private theorem appendPrefixClosed_forward_fresh
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hforward : Disjoint Q.forwardEdges C.forwardEdges) :
    Disjoint ((Q.prefixAt k).forwardEdges ∪ C.forwardEdges)
      (Q.suffixFrom k).forwardEdges := by
  rw [Set.disjoint_union_left]
  exact ⟨Q.prefixAt_forwardEdges_disjoint_suffixFrom k,
    (hforward.mono (Q.suffixFrom_forwardEdges_subset k) Set.Subset.rfl).symm⟩

private theorem appendPrefixClosed_backward_fresh
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbackward : Disjoint Q.backwardEdges C.backwardEdges) :
    Disjoint ((Q.prefixAt k).backwardEdges ∪ C.backwardEdges)
      (Q.suffixFrom k).backwardEdges := by
  rw [Set.disjoint_union_left]
  exact ⟨Q.prefixAt_backwardEdges_disjoint_suffixFrom k,
    (hbackward.mono (Q.suffixFrom_backwardEdges_subset k) Set.Subset.rfl).symm⟩

/-- Insert a closed occurrence word `C` at occurrence `k` of `Q`.

The hypotheses say that `C` is based at the selected occurrence and uses no
same-colour edge already used by `Q`.  Ambient vertices may repeat freely. -/
def insertClosed (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbase : C.vertex 0 = Q.vertex k)
    (hclosed : C.vertex (Fin.last C.length) = C.vertex 0)
    (hforward : Disjoint Q.forwardEdges C.forwardEdges)
    (hbackward : Disjoint Q.backwardEdges C.backwardEdges) :
    FiniteColouredOccurrenceWord W Y :=
  let A := (Q.prefixAt k).append C
    (by simpa only [prefixAt_last] using hbase.symm)
    (hforward.mono (Q.prefixAt_forwardEdges_subset k) Set.Subset.rfl)
    (hbackward.mono (Q.prefixAt_backwardEdges_subset k) Set.Subset.rfl)
  A.append (Q.suffixFrom k)
    (by
      change ((Q.prefixAt k).append C _ _ _).vertex
          (Fin.last ((Q.prefixAt k).length + C.length)) =
        (Q.suffixFrom k).vertex 0
      rw [append_last, suffixFrom_first, hclosed, hbase])
    (by
      rw [append_forwardEdges]
      exact appendPrefixClosed_forward_fresh Q C k hforward)
    (by
      rw [append_backwardEdges]
      exact appendPrefixClosed_backward_fresh Q C k hbackward)

@[simp] theorem insertClosed_first
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbase hclosed hforward hbackward) :
    (Q.insertClosed C k hbase hclosed hforward hbackward).vertex 0 =
      Q.vertex 0 := by
  unfold insertClosed
  rw [append_first, append_first, prefixAt_first]

@[simp] theorem insertClosed_last
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbase hclosed hforward hbackward) :
    (Q.insertClosed C k hbase hclosed hforward hbackward).vertex
        (Fin.last (Q.insertClosed C k hbase hclosed hforward hbackward).length) =
      Q.vertex (Fin.last Q.length) := by
  unfold insertClosed
  change (((Q.prefixAt k).append C _ _ _).append (Q.suffixFrom k) _ _ _).vertex
      (Fin.last ((((Q.prefixAt k).append C _ _ _).length) +
        (Q.suffixFrom k).length)) = _
  rw [append_last, suffixFrom_last]

theorem insertClosed_forwardEdges
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbase hclosed hforward hbackward) :
    (Q.insertClosed C k hbase hclosed hforward hbackward).forwardEdges =
      Q.forwardEdges ∪ C.forwardEdges := by
  unfold insertClosed
  rw [append_forwardEdges, append_forwardEdges,
    Q.forwardEdges_eq_prefixAt_union_suffixFrom k]
  ext e
  simp only [Set.mem_union]
  tauto

theorem insertClosed_backwardEdges
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbase hclosed hforward hbackward) :
    (Q.insertClosed C k hbase hclosed hforward hbackward).backwardEdges =
      Q.backwardEdges ∪ C.backwardEdges := by
  unfold insertClosed
  rw [append_backwardEdges, append_backwardEdges,
    Q.backwardEdges_eq_prefixAt_union_suffixFrom k]
  ext e
  simp only [Set.mem_union]
  tauto

theorem insertClosed_vertexSet
    (Q C : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (hbase hclosed hforward hbackward) :
    (Q.insertClosed C k hbase hclosed hforward hbackward).vertexSet =
      Q.vertexSet ∪ C.vertexSet := by
  unfold insertClosed
  rw [append_vertexSet, append_vertexSet,
    Q.vertexSet_eq_prefixAt_union_suffixFrom k]
  ext x
  simp only [Set.mem_union]
  tauto

#print axioms vertexSet_eq_prefixAt_union_suffixFrom
#print axioms insertClosed_first
#print axioms insertClosed_last
#print axioms insertClosed_forwardEdges
#print axioms insertClosed_backwardEdges
#print axioms insertClosed_vertexSet

end FiniteColouredOccurrenceWord
end Alternating
end Erdos599

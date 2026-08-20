/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.Transversal
import ErdosProblems.Erdos722.Typicality
import ErdosProblems.Erdos722.Reserve
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Deterministic endpoint of the clique-removal nibble

The probabilistic nibble produces a matching in the auxiliary hypergraph
whose vertices are host `r`-edges and whose hyperedges are `q`-cliques.
This file records, without probability or asymptotics, that such a matching
is exactly a clique decomposition of the union of its covered edges.
-/

namespace Erdos722.NibbleBasics

open Finset
open Erdos722.Transversal

noncomputable section

variable {n q r : ℕ}

/-- The `r`-edges contained in a block. -/
def blockEdges (r : ℕ) (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  B.powersetCard r

/-- The union of the `r`-edges covered by a block family. -/
def coveredEdges (r : ℕ) (blocks : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  blocks.biUnion (blockEdges r)

/-- A family of available `q`-cliques whose `r`-edge sets are pairwise
disjoint.  This is the concrete matching predicate used by the nibble. -/
def IsCliquePacking (host blocks : Finset (Finset (Fin n)))
    (q r : ℕ) : Prop :=
  (∀ B ∈ blocks, B.card = q) ∧
    (∀ B ∈ blocks, blockEdges r B ⊆ host) ∧
    ∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C →
      Disjoint (blockEdges r B) (blockEdges r C)

@[simp] theorem mem_coveredEdges {e : Finset (Fin n)} :
    e ∈ coveredEdges r blocks ↔ ∃ B ∈ blocks, e ⊆ B ∧ e.card = r := by
  simp [coveredEdges, blockEdges, Finset.mem_powersetCard]

theorem IsCliquePacking.covered_subset
    (h : IsCliquePacking host blocks q r) :
    coveredEdges r blocks ⊆ host := by
  intro e he
  obtain ⟨B, hB, heB, her⟩ := mem_coveredEdges.mp he
  exact h.2.1 B hB (Finset.mem_powersetCard.mpr ⟨heB, her⟩)

private theorem filter_containing_eq_single
    (h : IsCliquePacking host blocks q r)
    {e : Finset (Fin n)} (he : e ∈ coveredEdges r blocks) :
    (blocks.filter fun B ↦ e ⊆ B) =
      {Classical.choose (mem_coveredEdges.mp he)} := by
  classical
  let witness := Classical.choose (mem_coveredEdges.mp he)
  have hwitness := Classical.choose_spec (mem_coveredEdges.mp he)
  ext B
  constructor
  · intro hB
    have hm := Finset.mem_filter.mp hB
    have hecard : e.card = r := hwitness.2.2
    have heInB : e ∈ blockEdges r B :=
      Finset.mem_powersetCard.mpr ⟨hm.2, hecard⟩
    have heInWitness : e ∈ blockEdges r witness :=
      Finset.mem_powersetCard.mpr ⟨hwitness.2.1, hecard⟩
    have hEq : B = witness := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (h.2.2 B hm.1 witness hwitness.1 hne) heInB heInWitness
    exact Finset.mem_singleton.mpr (hEq.trans (by rfl))
  · intro hB
    have hEq : B = witness := Finset.mem_singleton.mp hB
    subst B
    exact Finset.mem_filter.mpr ⟨hwitness.1, hwitness.2.1⟩

/-- A clique packing is an exact uniform decomposition of its covered
edge union. -/
theorem IsCliquePacking.isUniformDecomposition
    (h : IsCliquePacking host blocks q r) :
    IsUniformDecomposition (coveredEdges r blocks) blocks q r := by
  classical
  refine ⟨h.1, ?_, ?_⟩
  · intro B hB e he
    exact mem_coveredEdges.mpr ⟨B, hB,
      (Finset.mem_powersetCard.mp he).1,
      (Finset.mem_powersetCard.mp he).2⟩
  · intro e he
    rw [filter_containing_eq_single h he]
    simp

/-- The residual host left by a clique packing. -/
def leave (host blocks : Finset (Finset (Fin n))) (r : ℕ) :
    Finset (Finset (Fin n)) :=
  host \ coveredEdges r blocks

theorem covered_union_leave
    (h : IsCliquePacking host blocks q r) :
    coveredEdges r blocks ∪ leave host blocks r = host := by
  exact Finset.union_sdiff_of_subset (h.covered_subset)

theorem disjoint_covered_leave :
    Disjoint (coveredEdges r blocks) (leave host blocks r) := by
  exact Finset.disjoint_sdiff

theorem leave_subset (host blocks : Finset (Finset (Fin n))) (r : ℕ) :
    leave host blocks r ⊆ host :=
  Finset.sdiff_subset

/-- The exact bounded-leave endpoint required from the probabilistic
nibble.  Its first field is the matching/decomposition conclusion and its
second field is the power-cleared maximum lower-face degree estimate used
by the sparse reserve cover. -/
def HasBoundedNibble (host : Finset (Finset (Fin n)))
    (q r d exponent : ℕ) : Prop :=
  ∃ blocks : Finset (Finset (Fin n)),
    IsCliquePacking host blocks q r ∧
      ∀ J : Finset (Fin n), J.card = r - 1 →
        (Erdos722.Reserve.localDegree (leave host blocks r) J) ^ d ≤
          n ^ exponent

end

end Erdos722.NibbleBasics

import ErdosProblems.Erdos73.OddPathMatchingBarrier
import ErdosProblems.Erdos73.ComponentRepresentatives
import ErdosProblems.Erdos73.OddPathPairCounts

/-! The actual finite deletion set supplied by an odd-path matching barrier. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
structure OddPathBarrierWitness (G : SimpleGraph V) (A : Finset V) (k : ℕ) where
  removed : Finset (OddPathVertex A)
  representatives : Finset (OddPathVertex A)
  subset : representatives ⊆ (oddPathTerminals A ∪ oddPathExposedMates A removed) \ removed
  size : removed.card + A.card + 2 ≤ representatives.card + 2 * k
  covering : ∀ C : (vertexDeletedGraph (oddPathAuxiliary G A) removed).ConnectedComponent,
    ((oddPathTerminals A ∪ oddPathExposedMates A removed) ∩ deletedComponentVertices C).Nonempty →
      (representatives ∩ deletedComponentVertices C).Nonempty
  unique : ∀ C : (vertexDeletedGraph (oddPathAuxiliary G A) removed).ConnectedComponent,
    ∀ x ∈ representatives, ∀ y ∈ representatives,
      x ∈ deletedComponentVertices C → y ∈ deletedComponentVertices C → x = y

open scoped Classical in
theorem exists_oddPathBarrierWitness {G : SimpleGraph V} {A : Finset V} {k : ℕ}
    (hno : ¬ HasOddTerminalPathPacking G A k) : Nonempty (OddPathBarrierWitness G A k) := by
  obtain ⟨W, hW⟩ := exists_oddPathMatchingBarrier hno
  rw [topDeleteVerts_oddComponents_card] at hW
  obtain ⟨Z, hZ, hZcard, hcover, huniq⟩ := exists_deletedComponent_representatives
    (G := oddPathAuxiliary G A) W (oddPathTerminals A ∪ oddPathExposedMates A W)
    (odd_deletedComponent_meets_terminals_or_exposed W)
  exact ⟨⟨W, Z, hZ, by omega, hcover, huniq⟩⟩

namespace OddPathBarrierWitness

variable {G : SimpleGraph V} {A : Finset V} {k : ℕ}

def discarded (B : OddPathBarrierWitness G A k) : Finset (OddPathVertex A) :=
  (oddPathTerminals A ∪ oddPathExposedMates A B.removed) \ B.representatives

def deletedPairs (B : OddPathBarrierWitness G A k) : Finset (OddPathVertex A) :=
  matchingSupport (matchingOn (oddPathBaseMatching A) B.removed)

def deletion (B : OddPathBarrierWitness G A k) : Finset V :=
  B.discarded.image projection ∪ B.deletedPairs.image projection

theorem deletion_card (B : OddPathBarrierWitness G A k) : B.deletion.card + 2 ≤ 2 * k := by
  have hsub : B.representatives ⊆ oddPathTerminals A ∪ oddPathExposedMates A B.removed :=
    B.subset.trans Finset.sdiff_subset
  have hdis := oddPathTerminals_disjoint_exposed (A := A) B.removed
  have hdiscard := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint hdis, oddPathTerminals_card] at hdiscard
  change B.discarded.card + B.representatives.card =
    A.card + (oddPathExposedMates A B.removed).card at hdiscard
  have hpair := (matchingOn_isMatching
    (oddPathBaseMatching_isMatching G A) B.removed).card_support
  change B.deletedPairs.card = 2 * (matchingOn (oddPathBaseMatching A) B.removed).card at hpair
  have hcounts := oddPath_deleted_pair_count B.removed
  have hsize := B.size
  have hbound : B.deletion.card ≤ B.discarded.card + B.deletedPairs.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))
  omega

theorem representative_not_removed (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : x ∈ B.representatives) : x ∉ B.removed :=
  (Finset.mem_sdiff.mp (B.subset hx)).2

theorem survives_not_discarded (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion) : x ∉ B.discarded := by
  intro hh
  exact hx (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hh, rfl⟩))

theorem survives_not_deletedPairs (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion) : x ∉ B.deletedPairs := by
  intro hh
  exact hx (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hh, rfl⟩))

theorem survives_eligible_mem_representatives (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion)
    (helig : x ∈ oddPathTerminals A ∪ oddPathExposedMates A B.removed) :
    x ∈ B.representatives := by
  by_contra hn
  exact B.survives_not_discarded hx (Finset.mem_sdiff.mpr ⟨helig, hn⟩)

theorem survives_terminal_mem_representatives (B : OddPathBarrierWitness G A k)
    {x : OddPathVertex A} (hx : projection x ∉ B.deletion) (ht : projection x ∈ A) :
    x ∈ B.representatives :=
  B.survives_eligible_mem_representatives hx
    (Finset.mem_union_left _ ((mem_oddPathTerminals A x).mpr ht))

end OddPathBarrierWitness
end Erdos73

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceCoveringWitness
import ErdosProblems.Erdos4b.FGKMTBatchExtension
import ErdosProblems.Erdos4b.FGKMTPrimeEdgeResidue

/-! # One genuine residue per original prime covers the supported selected edges -/

namespace Erdos4b.FGKMT.SourceGeometricPartition.CoveringWitness

noncomputable section

variable {a c e : ℝ} {x : ℕ} {D : SourceProbabilityData c e x}
  {b : ResidueAssignment (sourceSmallPrimes a x)} {H : RegularSourceConditions D a b}
  (B : SourceGeometricPartition H) (W : B.CoveringWitness)

theorem exists_selectedEdge_residue {j : ℕ} (hj : j < sourceBatchCount x) (p : B.labels j) :
    ∃ r : Fin p.val.val, ∀ q ∈ coveringSelectedEdge B.family hj W.history p,
      integerResidueIndex p.val.val (q : ℤ) = r.val := by
  have hp : 0 < p.val.val := (mem_commonPinnedPrimeSet.mp p.val.property).2.2.pos
  rcases W.selectedEdge_support B hj p with hempty | ⟨n, _hn, heq⟩
  · refine ⟨⟨0, hp⟩, ?_⟩
    intro q hq
    rw [hempty] at hq
    exact False.elim (Finset.notMem_empty q hq)
  · refine ⟨⟨integerResidueIndex p.val.val n.val, integerResidueIndex_lt hp n.val⟩, ?_⟩
    intro q hq
    rw [heq] at hq
    exact D.primeTupleEdge_residue hq

theorem exists_prime_residues :
    ∃ r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x),
      ∀ (j : ℕ) (hj : j < sourceBatchCount x) (p : B.labels j),
        ∀ q ∈ coveringSelectedEdge B.family hj W.history p,
          integerResidueIndex p.val.val (q : ℤ) = (r p.val).val := by
  classical
  choose f hf using fun j : Fin (sourceBatchCount x) =>
    fun p : B.labels j => W.exists_selectedEdge_residue B j.isLt p
  obtain ⟨r, hr⟩ := exists_dependent_batch_extension
    (T := fun p : commonPinnedPrimeSet (x / 2) x => Fin p.val)
    (fun j : Fin (sourceBatchCount x) => B.labels j)
    (fun j k hne => B.labels_disjoint (fun h => hne (Fin.ext h))) f
    (fun p => ⟨0, (mem_commonPinnedPrimeSet.mp p.property).2.2.pos⟩)
  refine ⟨r, ?_⟩
  intro j hj p q hq
  rw [hr ⟨j, hj⟩ p]
  exact hf ⟨j, hj⟩ p q hq

theorem residueSurvivors_subset_remaining
    (r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x))
    (hr : ∀ (j : ℕ) (hj : j < sourceBatchCount x) (p : B.labels j),
      ∀ q ∈ coveringSelectedEdge B.family hj W.history p,
        integerResidueIndex p.val.val (q : ℤ) = (r p.val).val) :
    naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x) H.edgeFamily.vertices r ⊆
      coveringRemaining B.family H.edgeFamily.vertices (sourceBatchCount x) W.history := by
  intro q hq
  obtain ⟨hqV, havoid⟩ := (mem_naturalResidueSurvivors _ _ r q).mp hq
  rw [coveringRemaining_mem_iff]
  refine ⟨hqV, ?_⟩
  intro j hj p hqp
  have hnot := (residueAssignmentAvoids_singleton_iff _ r (q : ℤ)).mp havoid p.val
  exact hnot (hr j hj p q hqp).symm

theorem exists_prime_residue_sieve :
    ∃ r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x),
      (naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x) H.edgeFamily.vertices r).card ≤
        (coveringRemaining B.family H.edgeFamily.vertices (sourceBatchCount x) W.history).card := by
  obtain ⟨r, hr⟩ := W.exists_prime_residues B
  exact ⟨r, Finset.card_le_card (W.residueSurvivors_subset_remaining B r hr)⟩

end

end Erdos4b.FGKMT.SourceGeometricPartition.CoveringWitness

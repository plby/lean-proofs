/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualLocalDegreeTail
import ErdosProblems.Erdos207.SourceLocalDegreeCutoff

/-! # Eventual regularization cutoffs under the compatible residual law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_sourceResidualGraph_local_degree_control
    (ell j q R D s : ℕ) (k : Fin (ell + 1)) (C B epsilon : ℝ≥0)
    (hj : 4 ≤ j) (hC : 1 ≤ C) (hs : 3 * R + 1 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V],
      ∀ (L : FiniteLaw Ω) (W : Vortex V ell) (G : SimpleGraph V),
      ∀ (initial later available : Ω → TripleSystemOn V) (F : ℕ → ForbiddenFamilyOn V),
      ∀ (p b : ℝ≥0) (y z : ℕ → ℝ≥0),
      p ≤ 1 → Fintype.card V ≤ t ^ R → 1 ≤ p ^ 3 * (W.prefix k).terminalSize →
      (∀ j' ∈ Icc j q, 1 ≤ y j') →
      b ≤ B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t →
      (∀ i, (W.U i).Nonempty) →
      IsResidualGraphStronglyWellDistributed L W k G initial later p C b →
      (∀ j' ∈ Icc 4 q, SourceVortexWellSpread (W.prefix k) j' (F j') (y j') (z j')) →
      (∀ j' ∈ Icc j q, z j' ≤ y j' * p ^ (3 * (j - 3)) * (W.prefix k).terminalSize) →
      L.SupportedOn (fun ω ↦
        (∀ U ∈ available ω, (W.prefix k).level U = Fin.last k.val) ∧
        (∀ U ∈ available ω, ∀ e ∈ tripleEdgeFinset U,
          e ∈ graphEdges G ∧ e ∉ (coveredGraph (initial ω ∪ later ω)).edgeSet)) →
      L.probability (fun ω ↦
        ((t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient k.val j' 2 * y j') *
          (p ^ 3) ^ (j - 3) * ((W.prefix k).terminalSize : ℝ≥0) ^ (j - 3) <
        (finiteHypergraphMaxDegree (localForbiddenConfigurations ((Icc 4 q).biUnion F)
          (available ω) (initial ω ∪ later ω) j) : ℝ≥0)) ≤ epsilon := by
  obtain ⟨T, hT1, hT⟩ := eventually_sourceAllLocalCanonicalTail_le k.val j q R D s C B epsilon
    hs hepsilon
  refine ⟨T, hT1, fun t ht Ω V _ _ _ L W G initial later available F p b y z
    hp hN hdensity hy hb hnonempty hstrong hF hz hgeometry ↦ ?_⟩
  let K := fun j' ↦ sourceLocalDegreeCutoff k.val j j' t (W.prefix k).terminalSize p (y j')
  have hK : ∀ j' ∈ Icc j q, 0 < K j' := fun j' hj' ↦
    zero_lt_one.trans_le (sourceLocalDegreeCutoff_one_le k.val j j' t
      (W.prefix k).terminalSize p (y j') (hT1.trans ht) (hy j' hj') hdensity)
  have hprob := sourceResidualGraph_all_local_forbidden_maximum_tail (s := s) L W k G initial later
    available F p C b y z K hp hC hK hnonempty hj hstrong hF hz hgeometry
  have hbudget := hT t ht (Fintype.card V) (W.prefix k).terminalSize p b y hN hdensity hy hb
  have hsum := sourceLocalDegreeCutoff_sum k.val j q t (W.prefix k).terminalSize p y
  change (∑ j' ∈ Icc j q, K j') = _ at hsum
  rw [hsum] at hprob
  exact hprob.trans hbudget


end

end Erdos207

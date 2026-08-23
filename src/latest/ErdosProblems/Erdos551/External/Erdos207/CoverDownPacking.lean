/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.AbsorberCompletionCount

/-!
# From a cover-down packing to a KSSS certificate

The probabilistic construction only has to leave uncovered the absorber
graph and edges supported on the flexible set.  Divisibility of the flexible
remainder follows from admissibility: both the whole leave and the absorber
graph are triangle-divisible.
-/

namespace Erdos207

open Finset

/-- Graph edges belonging to `G` but not to `H`. -/
def graphDifference {V : Type*} (G H : SimpleGraph V) : SimpleGraph V :=
  G ⊓ Hᶜ

instance graphDifference.instDecidableRel
    {V : Type*} [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (graphDifference G H).Adj := by
  intro u v
  change Decidable (G.Adj u v ∧ (u ≠ v ∧ ¬ H.Adj u v))
  infer_instance

lemma sup_graphDifference_eq
    {V : Type*} {G H : SimpleGraph V} (hHG : H ≤ G) :
    H ⊔ graphDifference G H = G := by
  apply le_antisymm
  · intro u v huv
    rw [SimpleGraph.sup_adj] at huv
    rcases huv with huv | huv
    · exact hHG huv
    · exact huv.1
  · intro u v huv
    rw [SimpleGraph.sup_adj]
    by_cases hH : H.Adj u v
    · exact Or.inl hH
    · exact Or.inr ⟨huv, huv.ne, hH⟩

lemma disjoint_graphDifference
    {V : Type*} (G H : SimpleGraph V) :
    Disjoint H (graphDifference G H) := by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hH hdiff
  exact hdiff.2.2 hH

lemma graphDifference_le_left
    {V : Type*} (G H : SimpleGraph V) : graphDifference G H ≤ G := by
  intro u v huv
  exact huv.1

lemma emptyGraph_triangleDivisible
    {V : Type*} [Fintype V] [DecidableEq V] :
    TriangleDivisible (SimpleGraph.emptyGraph V) := by
  apply IsTriangleDecomposition.triangleDivisible (C := ∅)
  constructor
  · intro T hT
    simp at hT
  · intro u v huv
    exact huv.elim

/-- A1 itself implies that the fixed absorber graph is triangle-divisible,
by switching against the empty flexible remainder. -/
theorem HasHighGirthAbsorptionBank.graph_triangleDivisible
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hA : HasHighGirthAbsorptionBank q H X B) [DecidableRel H.Adj] :
    TriangleDivisible H := by
  let L := SimpleGraph.emptyGraph V
  have hsupport : GraphSupportedOn L (X : Set V) := by
    intro u v huv
    exact huv.elim
  have hdiv : TriangleDivisible L := emptyGraph_triangleDivisible
  obtain ⟨C, _hCB, hC⟩ := hA.2 L hsupport hdiv
  have htri := hC.1.triangleDivisible
  simpa only [L, sup_bot_eq] using htri

/-- Exact conditions the random cover-down must achieve. -/
def HasKSSSOutsidePacking {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B P : TripleSystemOn V) : Prop :=
  IsPackingOn P ∧ Disjoint P B ∧
    AvoidsForbidden P (absorberErdosForbiddenConfigurationsOn q B) ∧
    H ≤ leaveGraph P ∧
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V)

/-- Every outside packing at an admissible order gives the full deterministic
cover-down certificate.  The flexible leave's divisibility is derived rather
than assumed. -/
theorem ksssCoverDownCertificate_of_outsidePacking
    {n q : ℕ} {H : SimpleGraph (Fin n)} {X : Finset (Fin n)}
    {B P : TripleSystem n}
    (hadmissible : Admissible n)
    (hA : HasHighGirthAbsorptionBank q H X B)
    (hP : HasKSSSOutsidePacking q H X B P) :
    HasKSSSCoverDownCertificate q n := by
  let L := graphDifference (leaveGraph P) H
  have hleave : H ⊔ L = leaveGraph P := sup_graphDifference_eq hP.2.2.2.1
  have hHL : Disjoint H L := disjoint_graphDifference _ _
  have hcoveredLeave : Disjoint (coveredGraph P) (H ⊔ L) := by
    rw [hleave]
    exact coveredGraph_disjoint_leaveGraph P
  have hcomplete : coveredGraph P ⊔ (H ⊔ L) =
      SimpleGraph.completeGraph (Fin n) := by
    rw [hleave]
    exact coveredGraph_sup_leaveGraph P
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hleaveDiv : TriangleDivisible (leaveGraph P) :=
    IsPacking.leave_triangleDivisible hP.1 hadmissible
  have hHdiv : TriangleDivisible H := hA.graph_triangleDivisible
  have hLdiv : TriangleDivisible L := by
    apply TriangleDivisible.right_of_sup
      (G := H) (K := L) (by simpa only [hleave] using hleaveDiv) hHdiv hHL
  refine ⟨H, X, B, P, L, hA, ?_⟩
  apply hasAbsorberCompatibleCoverDown_of_avoids_erdos
  · exact hP.1
  · exact hcoveredLeave
  · exact hcomplete
  · exact hP.2.2.2.2
  · exact hLdiv
  · exact hP.2.1
  · exact hP.2.2.1

/-- Exact remaining output of the KSSS probabilistic construction after all
deterministic reductions in this development. -/
def KSSSOutsidePackingTheorem : Prop :=
  ∀ q : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B P : TripleSystem n,
        HasHighGirthAbsorptionBank q H X B ∧
        HasKSSSOutsidePacking q H X B P

theorem ksssCoverDownTheorem_of_outsidePacking
    (h : KSSSOutsidePackingTheorem) : KSSSCoverDownTheorem := by
  intro q
  obtain ⟨N₀, hN₀⟩ := h q
  refine ⟨N₀, ?_⟩
  intro n hn hadmissible
  obtain ⟨H, X, B, P, hA, hP⟩ := hN₀ n hn hadmissible
  exact ksssCoverDownCertificate_of_outsidePacking hadmissible hA hP

end Erdos207

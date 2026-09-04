/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Assembly
import ErdosProblems.Erdos207.HighGirthAbsorber

/-!
# Deterministic reduction of the KSSS cover-down output

The probabilistic part of KSSS constructs an outside packing whose uncovered
edges consist of the fixed absorber graph together with a triangle-divisible
graph on the flexible set.  It also rules out every short configuration that
could be created when the absorber bank is switched.  This file records that
output exactly and proves the final deterministic implication.
-/

namespace Erdos207

open Finset

/-- Exact deterministic output required from the KSSS nibble and cover-down
iteration relative to a fixed absorber. -/
noncomputable def HasAbsorberCompatibleCoverDown
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (P : TripleSystemOn V) (L : SimpleGraph V) : Prop :=
  IsPackingOn P ∧
    Disjoint (coveredGraph P) (H ⊔ L) ∧
    coveredGraph P ⊔ (H ⊔ L) = SimpleGraph.completeGraph V ∧
    GraphSupportedOn L (X : Set V) ∧
    @TriangleDivisible V _ _ L (Classical.decRel L.Adj) ∧
    ∀ C : TripleSystemOn V, C ⊆ B →
      IsHighGirthTriangleDecomposition q (H ⊔ L) C →
      GirthGreaterOn q (P ∪ C)

/-- A complete finite KSSS certificate at order `n`. -/
def HasKSSSCoverDownCertificate (q n : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
    ∃ B P : TripleSystem n, ∃ L : SimpleGraph (Fin n),
      HasHighGirthAbsorptionBank q H X B ∧
      HasAbsorberCompatibleCoverDown q H X B P L

/-- Switching the absorber in an absorber-compatible cover-down certificate
produces an exact high-girth Steiner triple system. -/
theorem highGirthSteiner_of_absorberCompatibleCoverDown
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P : TripleSystemOn V} {L : SimpleGraph V}
    (hA : HasHighGirthAbsorptionBank q H X B)
    (hP : HasAbsorberCompatibleCoverDown q H X B P L) :
    ∃ S : TripleSystemOn V,
      IsTriangleDecomposition (SimpleGraph.completeGraph V) S ∧
      GirthGreaterOn q S := by
  obtain ⟨hpacking, hdisjoint, hcomplete, hsupport, hdiv, hcompatible⟩ := hP
  let : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨C, hCB, hC⟩ := hA.2 L hsupport hdiv
  refine ⟨P ∪ C, ?_, hcompatible C hCB hC⟩
  rw [← hcomplete]
  exact hpacking.isTriangleDecomposition.union hC.1 hdisjoint

theorem highGirthSteiner_of_ksssCoverDownCertificate
    {q n : ℕ} (h : HasKSSSCoverDownCertificate q n) :
    ∃ S : TripleSystem n, IsSteiner S ∧ GirthGreater q S := by
  obtain ⟨H, X, B, P, L, hA, hP⟩ := h
  obtain ⟨S, hS, hgirth⟩ :=
    highGirthSteiner_of_absorberCompatibleCoverDown hA hP
  exact ⟨S, isSteiner_iff_triangleDecomposition.mpr hS, hgirth⟩

/-- The remaining probabilistic theorem can be stated entirely as eventual
existence of finite cover-down certificates. -/
def KSSSCoverDownTheorem : Prop :=
  ∀ q : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
    HasKSSSCoverDownCertificate q n

theorem highGirthSteinerSystems_of_ksssCoverDown
    (h : KSSSCoverDownTheorem) : HighGirthSteinerSystems := by
  intro q
  obtain ⟨N₀, hN₀⟩ := h q
  refine ⟨N₀, ?_⟩
  intro n hn hadmissible
  exact highGirthSteiner_of_ksssCoverDownCertificate (hN₀ n hn hadmissible)

end Erdos207

/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterCenters
import ErdosProblems.Erdos721.HunterPhaseNet

/-!
# Simultaneously phase-distributed center families

Bounded integral frequencies are encoded by a finite alphabet.  We enumerate
all rational spaces spanned by `R` such codes and all points in their finite
phase nets.  The product-Haar union bound then gives one block family which
works for every encoded space and every target point.
-/

namespace Erdos721.HunterDistributedCenters

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

open HunterTorus HunterLattice HunterPhaseNet HunterCenters

/-- A finite code for an integral vector with coordinates in `[-H,H]`. -/
abbrev FrequencyCode (D H : ℕ) := Fin D → Fin (2 * H + 1)

/-- Decode the centered finite alphabet to an integral frequency. -/
def decodeFrequency {D H : ℕ} (a : FrequencyCode D H) : Fin D → ℤ :=
  fun i ↦ (a i : ℤ) - H

/-- The rational space spanned by an `R`-tuple of bounded frequency codes. -/
def codedSubspace {D H R : ℕ} (ξ : Fin R → FrequencyCode D H) :
    Submodule ℚ (Fin D → ℚ) :=
  Submodule.span ℚ (Set.range fun i ↦ castIntVector (decodeFrequency (ξ i)))

lemma finrank_codedSubspace_le {D H R : ℕ}
    (ξ : Fin R → FrequencyCode D H) :
    Module.finrank ℚ (codedSubspace ξ) ≤ R := by
  classical
  unfold codedSubspace
  let f : Fin R → Fin D → ℚ :=
    fun i ↦ castIntVector (decodeFrequency (ξ i))
  have hrange : (Set.range f).toFinset.card ≤ R := by
    rw [Set.toFinset_card]
    exact (Fintype.card_range_le f).trans_eq (Fintype.card_fin R)
  exact (finrank_span_le_card (Set.range f)).trans hrange

lemma latticeRank_codedSubspace_le {D H R : ℕ}
    (ξ : Fin R → FrequencyCode D H) :
    latticeRank (codedSubspace ξ) ≤ R :=
  (latticeRank_le_finrank _).trans (finrank_codedSubspace_le ξ)

/-- A request consists of a coded rational subspace and one point in its
finite phase grid. -/
noncomputable def PhaseRequest (D H R Q : ℕ) : Type :=
  Σ ξ : Fin R → FrequencyCode D H,
    Fin (latticeRank (codedSubspace ξ)) → Fin Q

noncomputable instance phaseRequestFintype (D H R Q : ℕ) :
    Fintype (PhaseRequest D H R Q) := by
  classical
  unfold PhaseRequest
  infer_instance

/-- Target set attached to a finite phase request. -/
noncomputable def requestTarget {D H R Q : ℕ} (r : ℝ)
    (q : PhaseRequest D H R Q) : Set (Torus D) :=
  phaseNetTarget (codedSubspace q.1) r q.2

lemma measurableSet_requestTarget {D H R Q : ℕ} (r : ℝ)
    (q : PhaseRequest D H R Q) :
    MeasurableSet (requestTarget r q) :=
  measurableSet_phaseNetTarget _ _ _

lemma volume_requestTarget {D H R Q : ℕ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1)
    (q : PhaseRequest D H R Q) :
    ENNReal.ofReal (2 * r) ^ R ≤ volume (requestTarget r q) := by
  refine (pow_le_pow_of_le_one (by positivity) ?_ ?_).trans
    (volume_phaseNetTarget (codedSubspace q.1) hr0 hr q.2)
  · exact ENNReal.ofReal_le_one.mpr hr
  · exact latticeRank_codedSubspace_le q.1

/-- Explicit cardinal bound for all subspace-and-grid requests. -/
lemma card_phaseRequest_le (D H R Q : ℕ) (hQ : 1 ≤ Q) :
    Fintype.card (PhaseRequest D H R Q) ≤
      ((2 * H + 1) ^ D) ^ R * Q ^ R := by
  classical
  change Fintype.card
      (Σ ξ : Fin R → FrequencyCode D H,
        Fin (latticeRank (codedSubspace ξ)) → Fin Q) ≤ _
  rw [Fintype.card_sigma]
  calc
    (∑ ξ : Fin R → FrequencyCode D H,
        Fintype.card (Fin (latticeRank (codedSubspace ξ)) → Fin Q)) =
        ∑ ξ : Fin R → FrequencyCode D H,
          Q ^ latticeRank (codedSubspace ξ) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      simp only [Fintype.card_fun, Fintype.card_fin]
    _ ≤ ∑ _ξ : Fin R → FrequencyCode D H, Q ^ R := by
      apply Finset.sum_le_sum
      intro ξ hξ
      exact Nat.pow_le_pow_right hQ (latticeRank_codedSubspace_le ξ)
    _ = ((2 * H + 1) ^ D) ^ R * Q ^ R := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin]
      norm_num

/-- A family is phase-distributed if every block supplies a center and a
small correction annihilating all integral characters of every coded
subspace at every target point. -/
def PhaseDistributed {D H R Y S : ℕ} (r : ℝ)
    (x : CenterFamily Y S D) : Prop :=
  ∀ ξ : Fin R → FrequencyCode D H, ∀ b : Fin Y, ∀ xStar : Torus D,
    ∃ s : Fin S, ∃ u : EuclideanSpace ℝ (Fin D),
      ‖u‖ ≤ 2 * Real.sqrt R * r ∧
        ∀ η : Fin D → ℤ, castIntVector η ∈ codedSubspace ξ →
          integerDot η (x b s + project u - xStar) = 0

/-- Product-Haar selection of a simultaneously phase-distributed family. -/
theorem exists_phaseDistributed
    {D H R Y S Q : ℕ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1)
    (hQ : 2 ≤ Q) (hmesh : (Q : ℝ)⁻¹ ≤ r)
    (hsmall :
      (Fintype.card (PhaseRequest D H R Q) * Y : ℕ) *
          (1 - ENNReal.ofReal (2 * r) ^ R) ^ S < 1) :
    ∃ x : CenterFamily Y S D,
      PhaseDistributed (H := H) (R := R) r x := by
  obtain ⟨x, hx⟩ := exists_centerFamily_hits
    (requestTarget (D := D) (H := H) (R := R) (Q := Q) r)
    (fun q ↦ measurableSet_requestTarget r q)
    (fun q ↦ volume_requestTarget hr0 hr q) hsmall
  refine ⟨x, fun ξ b xStar ↦ ?_⟩
  let centers : Set (Torus D) := Set.range (x b)
  have hhit : ∀ a : Fin (latticeRank (codedSubspace ξ)) → Fin Q,
      ∃ z ∈ centers, z ∈ phaseNetTarget (codedSubspace ξ) r a := by
    intro a
    obtain ⟨s, hs⟩ := hx (⟨ξ, a⟩ : PhaseRequest D H R Q) b
    exact ⟨x b s, ⟨s, rfl⟩, hs⟩
  obtain ⟨z, ⟨s, rfl⟩, u, hu, hphase⟩ :=
    exists_small_correction_of_hits_phaseNet
      (codedSubspace ξ) hr0 hQ hmesh centers hhit xStar
  refine ⟨s, u, ?_, hphase⟩
  have hsqrt : Real.sqrt (latticeRank (codedSubspace ξ)) ≤ Real.sqrt R :=
    Real.sqrt_le_sqrt (by exact_mod_cast latticeRank_codedSubspace_le ξ)
  have hmul :
      2 * Real.sqrt (latticeRank (codedSubspace ξ)) * r ≤
        2 * Real.sqrt R * r := by
    gcongr
  exact hu.trans hmul

end Erdos721.HunterDistributedCenters

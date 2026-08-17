/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.RemainderBounds

/-!
# Structural properties of the temporary surface collection
-/

namespace Erdos95.TemporarySurfaces

open Erdos95.ES Erdos95.LineFamilies Erdos95.Partitioning
open Erdos95.PartitionRemainders Erdos95.GuthStructure
open Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Space := ES.Space3

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem base_subset_temporary
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    F₀ ⊆ temporarySurfaces F₀ L S p c r cellF := by
  intro Q hQ
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ)

theorem cell_subset_temporary
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    {sign : Fin J → Bool} (hsign : sign ∈ lowSigns L S p c r) :
    cellF sign ⊆ temporarySurfaces F₀ L S p c r cellF := by
  intro Q hQ
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨sign, hsign, hQ⟩))

theorem factors_subset_temporary
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    irreducibleFactors (partitionPolynomial p) ⊆
      temporarySurfaces F₀ L S p c r cellF := by
  intro Q hQ
  exact Finset.mem_union_right _ hQ

theorem temporary_irreducible
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hF₀ : ∀ Q ∈ F₀, Irreducible Q)
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ∀ Q ∈ cellF sign, Irreducible Q) :
    ∀ Q ∈ temporarySurfaces F₀ L S p c r cellF, Irreducible Q := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQleft | hQfac
  · rcases Finset.mem_union.mp hQleft with hQ₀ | hQcell
    · exact hF₀ Q hQ₀
    · obtain ⟨sign, hsign, hQsign⟩ := Finset.mem_biUnion.mp hQcell
      exact hcell sign hsign Q hQsign
  · exact irreducible_of_mem_irreducibleFactors hQfac

theorem temporary_normalized
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hF₀ : ∀ Q ∈ F₀, normalize Q = Q)
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ∀ Q ∈ cellF sign, normalize Q = Q) :
    ∀ Q ∈ temporarySurfaces F₀ L S p c r cellF,
      normalize Q = Q := by
  intro Q hQ
  rcases Finset.mem_union.mp hQ with hQleft | hQfac
  · rcases Finset.mem_union.mp hQleft with hQ₀ | hQcell
    · exact hF₀ Q hQ₀
    · obtain ⟨sign, hsign, hQsign⟩ := Finset.mem_biUnion.mp hQcell
      exact hcell sign hsign Q hQsign
  · exact normalize_eq_of_mem_irreducibleFactors hQfac

theorem temporary_degree_le
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r D : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3)
    (hQ : partitionPolynomial p ≠ 0)
    (hQdeg : (partitionPolynomial p).totalDegree ≤ D)
    (hF₀ : ∀ Q ∈ F₀, Q.totalDegree ≤ D)
    (hcell : ∀ sign ∈ lowSigns L S p c r,
      ∀ Q ∈ cellF sign, Q.totalDegree ≤ D) :
    ∀ Q ∈ temporarySurfaces F₀ L S p c r cellF,
      Q.totalDegree ≤ D := by
  intro Q hQmem
  rcases Finset.mem_union.mp hQmem with hQleft | hQfac
  · rcases Finset.mem_union.mp hQleft with hQ₀ | hQcell
    · exact hF₀ Q hQ₀
    · obtain ⟨sign, hsign, hQsign⟩ := Finset.mem_biUnion.mp hQcell
      exact hcell sign hsign Q hQsign
  · exact (totalDegree_le_of_mem_irreducibleFactors hQ hQfac).trans hQdeg

theorem card_temporary_le
    (F₀ : Finset Poly3) (L : Finset LineIndex) (S : Finset Space)
    {J : ℕ} (p : Fin J → Poly3) (c r : ℕ)
    (cellF : (Fin J → Bool) → Finset Poly3) :
    (temporarySurfaces F₀ L S p c r cellF).card ≤
      F₀.card + ∑ sign ∈ lowSigns L S p c r, (cellF sign).card +
        (irreducibleFactors (partitionPolynomial p)).card := by
  classical
  unfold temporarySurfaces
  calc
    (F₀ ∪ (lowSigns L S p c r).biUnion cellF ∪
        irreducibleFactors (partitionPolynomial p)).card ≤
        (F₀ ∪ (lowSigns L S p c r).biUnion cellF).card +
          (irreducibleFactors (partitionPolynomial p)).card :=
      Finset.card_union_le _ _
    _ ≤ F₀.card + ((lowSigns L S p c r).biUnion cellF).card +
          (irreducibleFactors (partitionPolynomial p)).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ F₀.card +
          ∑ sign ∈ lowSigns L S p c r, (cellF sign).card +
          (irreducibleFactors (partitionPolynomial p)).card := by
      gcongr
      exact Finset.card_biUnion_le

end Erdos95.TemporarySurfaces

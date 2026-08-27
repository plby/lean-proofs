/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCoreRootCandidates
import ErdosProblems.Erdos207.PaddedAbsorberRootLocalization

/-!
# Uniform root bounds for the padded absorber

The small vortex is the distinguished root set of the padded absorber.  This
file records the two uniform facts used by initial typicality: at most
fourteen roots meet one absorber vertex, and at most six roots are charged to
the bank or to a singleton forbidden completion over one fixed pair.
-/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

noncomputable def absorberRootNeighborSet
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) (v : W) : Finset W := by
  classical
  exact X.filter fun x ↦ H.Adj x v

@[simp]
lemma mem_absorberRootNeighborSet_iff
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {X : Finset W} {v x : W} :
    x ∈ absorberRootNeighborSet H X v ↔ x ∈ X ∧ H.Adj x v := by
  classical
  simp [absorberRootNeighborSet]

noncomputable def absorberRootPairObstructionSet
    {W : Type*} [Fintype W] [DecidableEq W]
    (q : ℕ) (B : TripleSystemOn W) (X : Finset W)
    {u v : W} (huv : u ≠ v) : Finset W := by
  classical
  exact X.filter fun x ↦ ∃ w : ThirdVertex u v, w.1 = x ∧
    (thirdVertexTriple huv w ∈ B ∨
      CompletesForbidden
        (absorberErdosForbiddenConfigurationsOn q B) ∅
        (thirdVertexTriple huv w))

@[simp]
lemma mem_absorberRootPairObstructionSet_iff
    {W : Type*} [Fintype W] [DecidableEq W]
    {q : ℕ} {B : TripleSystemOn W} {X : Finset W}
    {u v x : W} {huv : u ≠ v} :
    x ∈ absorberRootPairObstructionSet q B X huv ↔
      x ∈ X ∧ ∃ w : ThirdVertex u v, w.1 = x ∧
        (thirdVertexTriple huv w ∈ B ∨
          CompletesForbidden
            (absorberErdosForbiddenConfigurationsOn q B) ∅
            (thirdVertexTriple huv w)) := by
  classical
  simp [absorberRootPairObstructionSet]

def HasPaddedAbsorberRootBounds
    {W : Type*} [Fintype W] [DecidableEq W]
    (q : ℕ) (H : SimpleGraph W) (X : Finset W)
    (B : TripleSystemOn W) : Prop :=
  (∀ v, (absorberRootNeighborSet H X v).card ≤ 14) ∧
  ∀ u v (huv : u ≠ v),
    (absorberRootPairObstructionSet q B X huv).card ≤ 6

theorem paddedConstruction_hasRootBounds
    {q m n : ℕ}
    {H : SimpleGraph (Fin n)} {X : Finset (Fin n)}
    {B : TripleSystemOn (Fin n)}
    (f : HighGirthCycleCoverVertex (Fin (2 * m)) (q + 2) ↪ Fin n)
    (i : Fin m ↪ Fin (2 * m))
    (hH : H = (highGirthCycleCoverGraph (Fin (2 * m))
      (show 2 ≤ q + 2 by omega)).map f)
    (hX : X = ((univ : Finset (Fin m)).map
      (i.trans (highGirthCycleCoverRootEmbedding
        (Fin (2 * m)) (q + 2)))).map f)
    (hB : B = mapTripleSystem f
      (highGirthCycleCoverBank (Fin (2 * m))
        (show 2 ≤ q + 2 by omega))) :
    HasPaddedAbsorberRootBounds q H X B := by
  let V := Fin (2 * m)
  let q' := q + 2
  let root : V ↪ HighGirthCycleCoverVertex V q' :=
    highGirthCycleCoverRootEmbedding V q'
  have hq' : 2 ≤ q' := by omega
  subst H
  subst X
  subst B
  constructor
  · intro y
    let C : Finset (Fin n) :=
      (mappedHighGirthOriginalRootCandidates f y).map (root.trans f)
    have hsub : absorberRootNeighborSet
        ((highGirthCycleCoverGraph V hq').map f)
        (((univ : Finset (Fin m)).map (i.trans root)).map f) y ⊆ C := by
      intro x hx
      have hxdata := mem_absorberRootNeighborSet_iff.mp hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hxdata.1
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
      apply Finset.mem_map.mpr
      refine ⟨i a, ?_, rfl⟩
      exact root_mem_mappedHighGirthCandidates_of_map_adj
        hq' f hxdata.2
    calc
      (absorberRootNeighborSet
        ((highGirthCycleCoverGraph V hq').map f)
        (((univ : Finset (Fin m)).map (i.trans root)).map f) y).card
          ≤ C.card := card_le_card hsub
      _ = (mappedHighGirthOriginalRootCandidates f y).card := card_map _
      _ ≤ 14 := card_mappedHighGirthOriginalRootCandidates_le_fourteen f y
  · intro u v huv
    let C : Finset (Fin n) :=
      (mappedHighGirthPairOriginalRootCandidates f u v).map (root.trans f)
    have hsub : absorberRootPairObstructionSet q
        (mapTripleSystem f (highGirthCycleCoverBank V hq'))
        (((univ : Finset (Fin m)).map (i.trans root)).map f) huv ⊆ C := by
      intro x hx
      have hxdata := mem_absorberRootPairObstructionSet_iff.mp hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hxdata.1
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨w, hw, hobs⟩ := hxdata.2
      have haCandidate : i a ∈
          mappedHighGirthPairOriginalRootCandidates f u v := by
        rcases hobs with hbank | hforbidden
        · exact root_mem_mappedHighGirthPairCandidates_of_bank
            hq' f huv w (i a) hw hbank
        · exact root_mem_mappedHighGirthPairCandidates_of_forbidden
            hq' (by omega) f Subset.rfl huv w (i a) hw hforbidden
      exact Finset.mem_map.mpr ⟨i a, haCandidate, rfl⟩
    calc
      (absorberRootPairObstructionSet q
        (mapTripleSystem f (highGirthCycleCoverBank V hq'))
        (((univ : Finset (Fin m)).map (i.trans root)).map f) huv).card
          ≤ C.card := card_le_card hsub
      _ = (mappedHighGirthPairOriginalRootCandidates f u v).card :=
        card_map _
      _ ≤ 6 := card_mappedHighGirthPairOriginalRootCandidates_le_six f u v

/-- The efficient padded absorber can be chosen together with its two
constant root-incidence bounds. -/
theorem exists_paddedEfficientAbsorber_with_rootBounds_and_rootLocalization
    {q m n : ℕ} (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * m) ^ 156 ≤ n) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n),
        X.card = m ∧ HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
          (verticesOn B).card ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
          (∀ v, H.degree v ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156) ∧
          B.card ≤
            (highGirthAbsorberCardCoefficient (q + 2) *
              (2 * m) ^ 156) ^ 3 ∧
          HasPaddedAbsorberRootBounds q H X B ∧
          HasPaddedAbsorberRootLocalization q X B := by
  obtain ⟨H, X, B, hXcard, hA, hlocal, hdegree, hBcard,
      f, i, hH, hX, hB⟩ := exists_paddedEfficientAbsorber hm hfit
  have hWbound : Fintype.card
      (HighGirthCycleCoverVertex (Fin (2 * m)) (q + 2)) ≤
        highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 :=
    highGirthCycleCoverVertex_card_le (q + 2) (2 * m) (by omega)
  have hBsupport : (verticesOn B).card ≤
      highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 := by
    rw [hB, verticesOn_mapTripleSystem, card_map]
    exact (card_le_card (subset_univ _)).trans (by
      simpa only [card_univ] using hWbound)
  refine ⟨H, X, B, hXcard, hA, hlocal, hBsupport,
    hdegree, hBcard, ?_, ?_⟩
  · exact paddedConstruction_hasRootBounds f i hH hX hB
  · exact paddedConstruction_hasRootLocalization f i hX hB

/-- Backwards-compatible projection retaining the original root-bounds
interface. -/
theorem exists_paddedEfficientAbsorber_with_rootBounds
    {q m n : ℕ} (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * m) ^ 156 ≤ n) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n),
        X.card = m ∧ HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
          (verticesOn B).card ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
          (∀ v, H.degree v ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156) ∧
          B.card ≤
            (highGirthAbsorberCardCoefficient (q + 2) *
              (2 * m) ^ 156) ^ 3 ∧
          HasPaddedAbsorberRootBounds q H X B := by
  obtain ⟨H, X, B, hX, hA, hlocal, hsupport, hdegree, hB, hroot, _⟩ :=
    exists_paddedEfficientAbsorber_with_rootBounds_and_rootLocalization
      hm hfit
  exact ⟨H, X, B, hX, hA, hlocal, hsupport, hdegree, hB, hroot⟩

end

end Erdos207

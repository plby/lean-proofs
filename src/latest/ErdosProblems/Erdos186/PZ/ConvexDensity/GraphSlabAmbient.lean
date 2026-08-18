/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AffineSlab
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryGraph
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphDensityND

/-!
# Transporting graph slabs back to ambient Euclidean space

`GraphDensityND` naturally works in the product model
`EuclideanPoint n × ℝ`, whereas the convex-density output lives in
`EuclideanPoint (n+1)`.  The last-coordinate split is volume preserving.
This file proves that fact and gives a direct ambient version of the
higher-dimensional occupied-graph slab theorem.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

open Subgradient

theorem affineSlab_splitCoordinate_last_eq_lastCoordinateCLE {n : ℕ}
    (z : EuclideanPoint (n + 1)) :
    AffineSlab.splitCoordinate (Fin.last n) z =
      lastCoordinateCLE n z := by
  rw [lastCoordinateCLE_apply]
  apply Prod.ext
  · change AffineSlab.eraseCoordinate (Fin.last n) z = baseCoordinates z
    ext j
    rw [AffineSlab.eraseCoordinate_apply, Fin.succAbove_last_apply]
    rfl
  · rfl

@[simp]
theorem baseCoordinates_lastCoordinateCLE_symm {n : ℕ}
    (z : EuclideanPoint n × ℝ) :
    baseCoordinates ((lastCoordinateCLE n).symm z) = z.1 := by
  have h := (lastCoordinateCLE n).apply_symm_apply z
  change (baseCoordinates ((lastCoordinateCLE n).symm z),
    lastCoordinate ((lastCoordinateCLE n).symm z)) = z at h
  exact congrArg Prod.fst h

@[simp]
theorem lastCoordinate_lastCoordinateCLE_symm {n : ℕ}
    (z : EuclideanPoint n × ℝ) :
    lastCoordinate ((lastCoordinateCLE n).symm z) = z.2 := by
  have h := (lastCoordinateCLE n).apply_symm_apply z
  change (baseCoordinates ((lastCoordinateCLE n).symm z),
    lastCoordinate ((lastCoordinateCLE n).symm z)) = z at h
  exact congrArg Prod.snd h

/-- Splitting off the last Euclidean coordinate preserves Lebesgue volume. -/
theorem measurePreserving_lastCoordinateCLE (n : ℕ) :
    MeasurePreserving (lastCoordinateCLE n) := by
  have hfun :
      (lastCoordinateCLE n : EuclideanPoint (n + 1) →
        EuclideanPoint n × ℝ) =
      AffineSlab.splitCoordinate (Fin.last n) := by
    funext z
    exact (affineSlab_splitCoordinate_last_eq_lastCoordinateCLE z).symm
  rw [hfun]
  exact AffineSlab.measurePreserving_splitCoordinate (Fin.last n)

/-- Every set has the same outer Lebesgue volume as its inverse image under
the last-coordinate continuous linear equivalence. -/
theorem volume_lastCoordinateCLE_symm_image (n : ℕ)
    (S : Set (EuclideanPoint n × ℝ)) :
    (volume : Measure (EuclideanPoint (n + 1)))
        ((lastCoordinateCLE n).symm '' S) =
      (volume : Measure (EuclideanPoint n × ℝ)) S := by
  have himage : (lastCoordinateCLE n).symm '' S =
      lastCoordinateCLE n ⁻¹' S :=
    (lastCoordinateCLE n).toEquiv.symm.image_eq_preimage_symm S
  rw [himage]
  exact (measurePreserving_lastCoordinateCLE n).measure_preimage_emb
    (lastCoordinateCLE n).toHomeomorph.measurableEmbedding S

/-- Image of an ambient finite set under the last-coordinate split. -/
def lastCoordinateImageFinset {n : ℕ}
    (X : Finset (EuclideanPoint (n + 1))) :
    Finset (EuclideanPoint n × ℝ) :=
  X.map (lastCoordinateCLE n).toEquiv.toEmbedding

@[simp]
theorem mem_lastCoordinateImageFinset {n : ℕ}
    (X : Finset (EuclideanPoint (n + 1))) (z : EuclideanPoint n × ℝ) :
    z ∈ lastCoordinateImageFinset X ↔
      (lastCoordinateCLE n).symm z ∈ X := by
  exact Finset.mem_map_equiv

@[simp]
theorem card_lastCoordinateImageFinset {n : ℕ}
    (X : Finset (EuclideanPoint (n + 1))) :
    (lastCoordinateImageFinset X).card = X.card := by
  exact Finset.card_map _

/-- Ambient points whose first `n` coordinates belong to a prescribed cell. -/
def ambientGraphPointsOverCell {n m : ℕ}
    (X : Finset (EuclideanPoint (n + 1))) (v : Fin n → Fin m) :
    Finset (EuclideanPoint (n + 1)) := by
  classical
  exact X.filter fun z ↦ baseCoordinates z ∈ graphBaseCellND v

@[simp]
theorem mem_ambientGraphPointsOverCell_iff {n m : ℕ}
    {X : Finset (EuclideanPoint (n + 1))} {v : Fin n → Fin m}
    {z : EuclideanPoint (n + 1)} :
    z ∈ ambientGraphPointsOverCell X v ↔
      z ∈ X ∧ baseCoordinates z ∈ graphBaseCellND v := by
  simp [ambientGraphPointsOverCell]

theorem graphPointsOverCellND_lastCoordinateImageFinset {n m : ℕ}
    (X : Finset (EuclideanPoint (n + 1))) (v : Fin n → Fin m) :
    graphPointsOverCellND (lastCoordinateImageFinset X) v =
      (ambientGraphPointsOverCell X v).map
        (lastCoordinateCLE n).toEquiv.toEmbedding := by
  ext z
  simp only [mem_graphPointsOverCellND_iff, mem_lastCoordinateImageFinset,
    Finset.mem_map, mem_ambientGraphPointsOverCell_iff]
  constructor
  · rintro ⟨hzX, hzbase⟩
    refine ⟨(lastCoordinateCLE n).symm z, ⟨hzX, ?_⟩, ?_⟩
    · simpa using hzbase
    · simp
  · rintro ⟨y, ⟨hyX, hybase⟩, rfl⟩
    constructor
    · change (lastCoordinateCLE n).symm (lastCoordinateCLE n y) ∈ X
      rw [(lastCoordinateCLE n).symm_apply_apply]
      exact hyX
    · simpa using hybase

@[simp]
theorem card_graphPointsOverCellND_lastCoordinateImageFinset {n m : ℕ}
    (X : Finset (EuclideanPoint (n + 1))) (v : Fin n → Fin m) :
    (graphPointsOverCellND (lastCoordinateImageFinset X) v).card =
      (ambientGraphPointsOverCell X v).card := by
  rw [graphPointsOverCellND_lastCoordinateImageFinset]
  exact Finset.card_map _

/-- Ambient form of the higher-dimensional occupied-graph slab theorem. -/
theorem exists_occupied_upperBoundary_affine_slab_nd
    {n m K : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {c : ℝ}
    (hc : 2 * ((n : ℝ) + 1) / (m : ℝ) < c)
    {h : (Fin n → ℝ) → ℝ}
    (hconcave : ConcaveOn ℝ (Subgradient.pzExpandedBox n c) h)
    (hrange : ∀ x ∈ Subgradient.pzExpandedBox n c,
      h x ∈ Set.Icc (0 : ℝ) 1)
    (X : Finset (EuclideanPoint (n + 1)))
    (hgraph : ∀ z ∈ X, lastCoordinate z = h (WithLp.ofLp (baseCoordinates z)))
    (I : Finset (Fin n → Fin m)) (hI : I.Nonempty)
    (hoccupied : ∀ v ∈ I, K ≤ (ambientGraphPointsOverCell X v).card) :
    ∃ v ∈ I, ∃ p : Fin n → ℝ,
      let epsilon :=
        4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
          (c * (I.card : ℝ))
      let L := reflectedTangentAffine (fun x ↦ 1 - h x)
        (pzFinGridPoint v) p
      let productSlab := affineGraphSlab (graphBaseCellND v) L epsilon
      let ambientSlab := (lastCoordinateCLE n).symm '' productSlab
      (∀ i, |p i| ≤ 2 / c) ∧
        (ambientGraphPointsOverCell X v : Set (EuclideanPoint (n + 1))) ⊆
          ambientSlab ∧
        Convex ℝ ambientSlab ∧
        K ≤ (pointsIn X ambientSlab).card ∧
        volume ambientSlab =
          (∏ i : Fin n, ENNReal.ofReal ((m : ℝ)⁻¹)) *
            ENNReal.ofReal (2 * epsilon) := by
  let X' := lastCoordinateImageFinset X
  have hgraph' : ∀ z ∈ X', z.2 = h (WithLp.ofLp z.1) := by
    intro z hz
    have hzX : (lastCoordinateCLE n).symm z ∈ X := by
      simpa [X'] using hz
    have hzEq := hgraph ((lastCoordinateCLE n).symm z) hzX
    simpa using hzEq
  have hoccupied' : ∀ v ∈ I, K ≤ (graphPointsOverCellND X' v).card := by
    intro v hv
    rw [show X' = lastCoordinateImageFinset X by rfl,
      card_graphPointsOverCellND_lastCoordinateImageFinset]
    exact hoccupied v hv
  obtain ⟨v, hvI, p, hp, hsubset, hconvex, hcard, hvolume⟩ :=
    exists_occupied_graph_cell_affine_slab_nd hn hm hc hconcave hrange
      X' hgraph' I hI hoccupied'
  refine ⟨v, hvI, p, hp, ?_, ?_, ?_, ?_⟩
  · intro z hz
    let z' : EuclideanPoint n × ℝ := lastCoordinateCLE n z
    have hzX' : z' ∈ graphPointsOverCellND X' v := by
      rw [show graphPointsOverCellND X' v =
        (ambientGraphPointsOverCell X v).map
          (lastCoordinateCLE n).toEquiv.toEmbedding by
        simpa [X'] using graphPointsOverCellND_lastCoordinateImageFinset X v]
      exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
    exact ⟨z', hsubset hzX', by
      exact (lastCoordinateCLE n).symm_apply_apply z⟩
  · exact hconvex.linear_image
      (lastCoordinateCLE n).symm.toContinuousLinearEquiv.toLinearMap
  · apply hcard.trans
    let T := graphPointsInND X'
      (affineGraphSlab (graphBaseCellND v)
        (reflectedTangentAffine (fun x ↦ 1 - h x) (pzFinGridPoint v) p)
        (4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
          (c * (I.card : ℝ))))
    let T' := T.map (lastCoordinateCLE n).symm.toEquiv.toEmbedding
    have hT' : T' ⊆ pointsIn X
        ((lastCoordinateCLE n).symm ''
          affineGraphSlab (graphBaseCellND v)
            (reflectedTangentAffine (fun x ↦ 1 - h x) (pzFinGridPoint v) p)
            (4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
              (c * (I.card : ℝ)))) := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨z', hz'T, rfl⟩ := hz
      rw [mem_pointsIn]
      have hz' := mem_graphPointsInND_iff.mp hz'T
      exact ⟨by simpa [X'] using hz'.1,
        ⟨z', hz'.2, rfl⟩⟩
    have hcardT : T.card = T'.card := by
      exact (Finset.card_map _).symm
    rw [show graphPointsInND X'
        (affineGraphSlab (graphBaseCellND v)
          (reflectedTangentAffine (fun x ↦ 1 - h x) (pzFinGridPoint v) p)
          (4 * ((n : ℝ) + 1) ^ 4 * (m : ℝ) ^ (n - 2) /
            (c * (I.card : ℝ)))) = T by rfl,
      hcardT]
    exact Finset.card_le_card hT'
  · rw [volume_lastCoordinateCLE_symm_image]
    exact hvolume

end

end Erdos186.PZ.ConvexDensity

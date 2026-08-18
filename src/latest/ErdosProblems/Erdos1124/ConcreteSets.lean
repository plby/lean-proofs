/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.Geometry

/-!
# The concrete disk and square inside the unit torus

This file names the two affine images used in the discrepancy argument and
their images under the coordinatewise quotient map.  Because both affine
images lie in the half-open fundamental square, membership in either torus
set can be tested on the canonical representative without losing boundary
points.
-/

open Set MeasureTheory

namespace Erdos1124.ConcreteSets

noncomputable section

abbrev Plane := Geometry.Plane
abbrev Torus := TorusTransfer.Torus (Fin 2)

/-- The disk after the common affine placement in the fundamental square. -/
def embeddedDisk : Set Plane := Geometry.torusEmbed '' Geometry.unitDisk

/-- The equal-area square after the same affine placement. -/
def embeddedSquare : Set Plane := Geometry.torusEmbed '' Geometry.equalAreaSquare

/-- The corresponding subset of the two-dimensional unit torus. -/
def torusDisk : Set Torus := TorusTransfer.quotientMap '' embeddedDisk

/-- The corresponding square subset of the two-dimensional unit torus. -/
def torusSquare : Set Torus := TorusTransfer.quotientMap '' embeddedSquare

/-- Their common Euclidean area after scaling by `1/4`. -/
def embeddedMass : ℝ := Real.pi / 16

lemma embeddedMass_pos : 0 < embeddedMass := by
  unfold embeddedMass
  positivity

lemma embeddedDisk_subset_fundamentalCube :
    embeddedDisk ⊆ TorusTransfer.fundamentalCube :=
  Geometry.torusEmbed_unitDisk_subset_fundamentalCube

lemma embeddedSquare_subset_fundamentalCube :
    embeddedSquare ⊆ TorusTransfer.fundamentalCube :=
  Geometry.torusEmbed_equalAreaSquare_subset_fundamentalCube

lemma measurableSet_embeddedDisk : MeasurableSet embeddedDisk :=
  Geometry.measurableSet_torusEmbed_unitDisk

lemma measurableSet_embeddedSquare : MeasurableSet embeddedSquare :=
  Geometry.measurableSet_torusEmbed_equalAreaSquare

lemma volume_embeddedDisk :
    volume embeddedDisk = ENNReal.ofReal embeddedMass := by
  unfold embeddedDisk
  rw [Geometry.volume_torusEmbed_unitDisk]
  congr 1
  norm_num [embeddedMass]
  ring

lemma volume_embeddedSquare :
    volume embeddedSquare = ENNReal.ofReal embeddedMass := by
  unfold embeddedSquare
  rw [Geometry.volume_torusEmbed_equalAreaSquare]
  congr 1
  norm_num [embeddedMass]
  ring

/-- Quotient-image membership is exactly membership of the canonical
representative, for a set contained in the fundamental cube. -/
lemma mem_quotient_image_iff_representative_mem
    {E : Set Plane} (hE : E ⊆ TorusTransfer.fundamentalCube) (z : Torus) :
    z ∈ TorusTransfer.quotientMap '' E ↔ TorusTransfer.representative z ∈ E := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [TorusTransfer.representative_quotientMap_of_mem (hE hx)] using hx
  · intro hz
    refine ⟨TorusTransfer.representative z, hz, ?_⟩
    exact TorusTransfer.quotientMap_representative z

lemma mem_torusDisk_iff_representative_mem (z : Torus) :
    z ∈ torusDisk ↔ TorusTransfer.representative z ∈ embeddedDisk := by
  exact mem_quotient_image_iff_representative_mem
    embeddedDisk_subset_fundamentalCube z

lemma mem_torusSquare_iff_representative_mem (z : Torus) :
    z ∈ torusSquare ↔ TorusTransfer.representative z ∈ embeddedSquare := by
  exact mem_quotient_image_iff_representative_mem
    embeddedSquare_subset_fundamentalCube z

end

end Erdos1124.ConcreteSets

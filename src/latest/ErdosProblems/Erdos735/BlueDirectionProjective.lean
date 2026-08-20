/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.RedBlueDualIncidence

/-!
# Blue directions as projective arrangement vertices

This file identifies the primal finset `blueDirectionsThrough P s` with the
projective vertices of the blue dual-line arrangement incident with the line
indexed by `s`.  The quotient by repeated collinear directions is handled by
an explicit finite equivalence.
-/

open Classical
noncomputable section

namespace Erdos735.BlueDirectionProjective

open ProjectiveArrangement ProjectiveBoundaryExtraction
open RedBlueDualIncidence ChartOrder

abbrev Blue (P : Finset Point) := nonordinaryPoints P
abbrev OtherBlue (P : Finset Point) (s : Point) := {b // b ∈ (Blue P).erase s}

/-- The projective crossing represented by the direction from `s` to another
blue point. -/
noncomputable def directionVertex (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) (b : OtherBlue P s) : Vertex (Blue P) := by
  let p : Line (Blue P) := ⟨s, hs⟩
  let q : Line (Blue P) := ⟨b.1, (Finset.mem_erase.mp b.2).2⟩
  have hpq : p ≠ q := by
    intro h
    exact (Finset.mem_erase.mp b.2).1 (congrArg Subtype.val h).symm
  let pq : DistinctPointPair (Blue P) := ⟨(p, q), hpq⟩
  exact ⟨indexedIntersection (Blue P) pq,
    indexedIntersection_mem_projectiveVertices (Blue P) pq⟩

theorem directionVertex_on_fixed (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) (b : OtherBlue P s) :
    OnLine (Blue P) (directionVertex P s hs b) ⟨s, hs⟩ := by
  exact indexedIntersection_incident_left _ _

theorem directionVertex_on_other (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) (b : OtherBlue P s) :
    OnLine (Blue P) (directionVertex P s hs b)
      ⟨b.1, (Finset.mem_erase.mp b.2).2⟩ := by
  exact indexedIntersection_incident_right _ _

/-- The projective vertex map and the primal line-fiber map have exactly the
same equality relation. -/
theorem directionVertex_eq_iff_lineFiber_eq (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) (b d : OtherBlue P s) :
    directionVertex P s hs b = directionVertex P s hs d ↔
      lineFiber P s b.1 = lineFiber P s d.1 := by
  let ps : Line (Blue P) := ⟨s, hs⟩
  let pb : Line (Blue P) := ⟨b.1, (Finset.mem_erase.mp b.2).2⟩
  let pd : Line (Blue P) := ⟨d.1, (Finset.mem_erase.mp d.2).2⟩
  have hsb : ps ≠ pb := by
    intro h
    exact (Finset.mem_erase.mp b.2).1 (congrArg Subtype.val h).symm
  have hsd : ps ≠ pd := by
    intro h
    exact (Finset.mem_erase.mp d.2).1 (congrArg Subtype.val h).symm
  constructor
  · intro hv
    have hsDual : vertexHomogeneous (directionVertex P s hs b) ∈
        ProjectiveDuality.dualLine s :=
      (onLine_iff_mem_dualLine _ ps).mp
        (directionVertex_on_fixed P s hs b)
    have hbDual : vertexHomogeneous (directionVertex P s hs b) ∈
        ProjectiveDuality.dualLine b.1 :=
      (onLine_iff_mem_dualLine _ pb).mp
        (directionVertex_on_other P s hs b)
    have hdDual : vertexHomogeneous (directionVertex P s hs b) ∈
        ProjectiveDuality.dualLine d.1 := by
      rw [hv]
      exact (onLine_iff_mem_dualLine _ pd).mp
        (directionVertex_on_other P s hs d)
    have hcol : Collinear3 s b.1 d.1 :=
      collinear3_of_mem_three_dualLines
        (fun h ↦ hsb (Subtype.ext h))
        (vertexHomogeneous_ne_zero (directionVertex P s hs b))
        hsDual hbDual hdDual
    have hcol' : Collinear3 s d.1 b.1 := by
      exact (collinear3_swap_left s d.1 b.1).mp
        (collinear3_cycle.mp (collinear3_cycle.mp hcol))
    have hbmem : b.1 ∈ lineFiber P s d.1 := by
      exact Finset.mem_filter.mpr
        ⟨nonordinaryPoints_subset P (Finset.mem_erase.mp b.2).2, hcol'⟩
    exact lineFiber_eq_of_mem_lineFiber
      (fun h ↦ hsb (Subtype.ext h))
      (fun h ↦ hsd (Subtype.ext h))
      (left_mem_lineFiber (nonordinaryPoints_subset P hs)) hbmem
  · intro hfiber
    by_contra hv
    exact (lineFiber_ne_of_distinct_vertices_on_common_line hv hsb hsd
      (directionVertex_on_fixed P s hs b)
      (directionVertex_on_other P s hs b)
      (directionVertex_on_fixed P s hs d)
      (directionVertex_on_other P s hs d)) hfiber

/-- The finite projective vertices produced by all blue directions through
`s`. -/
noncomputable def directionVerticesThrough (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) : Finset (Vertex (Blue P)) :=
  Finset.univ.image (directionVertex P s hs)

theorem directionVerticesThrough_eq_verticesOn (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) :
    directionVerticesThrough P s hs =
      verticesOn (Finset.univ : Finset (Vertex (Blue P))) (OnLine (Blue P))
        (⟨s, hs⟩ : Line (Blue P)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_verticesOn _ _).mpr
      ⟨Finset.mem_univ _, directionVertex_on_fixed P s hs b⟩
  · intro hv
    have hvs := (mem_verticesOn _ _).mp hv |>.2
    obtain ⟨q, hqp, hvq⟩ :=
      exists_other_incident_line (Blue P) v (⟨s, hs⟩ : Line (Blue P))
    have hqs : q.1 ≠ s := by
      intro h
      exact hqp (Subtype.ext h)
    let b : OtherBlue P s := ⟨q.1, Finset.mem_erase.mpr ⟨hqs, q.2⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact ProjectiveArrangement.eq_of_two_common_lines
      (fun h ↦ hqp (Subtype.ext h.symm))
      (directionVertex_on_fixed P s hs b)
      (directionVertex_on_other P s hs b) hvs hvq

private theorem fiberWitness_exists (P : Finset Point) (s : Point)
    (L : {L // L ∈ blueDirectionsThrough P s}) :
    ∃ b ∈ (Blue P).erase s, lineFiber P s b = L.1 :=
  Finset.mem_image.mp L.2

private noncomputable def fiberWitness (P : Finset Point) (s : Point)
    (L : {L // L ∈ blueDirectionsThrough P s}) : OtherBlue P s :=
  ⟨Classical.choose (fiberWitness_exists P s L),
    (Classical.choose_spec (fiberWitness_exists P s L)).1⟩

private theorem fiberWitness_spec (P : Finset Point) (s : Point)
    (L : {L // L ∈ blueDirectionsThrough P s}) :
    lineFiber P s (fiberWitness P s L).1 = L.1 := by
  exact (Classical.choose_spec (fiberWitness_exists P s L)).2

private noncomputable def fiberToVertex (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) (L : {L // L ∈ blueDirectionsThrough P s}) :
    {v // v ∈ directionVerticesThrough P s hs} :=
  ⟨directionVertex P s hs (fiberWitness P s L),
    Finset.mem_image.mpr ⟨fiberWitness P s L, Finset.mem_univ _, rfl⟩⟩

private theorem fiberToVertex_bijective (P : Finset Point) (s : Point)
    (hs : s ∈ Blue P) : Function.Bijective (fiberToVertex P s hs) := by
  constructor
  · intro L M hLM
    apply Subtype.ext
    have hv := congrArg Subtype.val hLM
    have hf := (directionVertex_eq_iff_lineFiber_eq P s hs
      (fiberWitness P s L) (fiberWitness P s M)).mp hv
    rw [fiberWitness_spec P s L, fiberWitness_spec P s M] at hf
    exact hf
  · intro v
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp v.2
    let L : {L // L ∈ blueDirectionsThrough P s} :=
      ⟨lineFiber P s b.1, Finset.mem_image.mpr ⟨b.1, b.2, rfl⟩⟩
    refine ⟨L, ?_⟩
    apply Subtype.ext
    rw [show (fiberToVertex P s hs L).1 =
        directionVertex P s hs (fiberWitness P s L) by rfl, ← hb]
    exact (directionVertex_eq_iff_lineFiber_eq P s hs
      (fiberWitness P s L) b).mpr (fiberWitness_spec P s L)

/-- Exact cardinal bridge from primal blue directions to vertices of the
projective blue arrangement on the corresponding line. -/
theorem card_blueDirectionsThrough_eq_verticesOn (P : Finset Point)
    (s : Point) (hs : s ∈ Blue P) :
    (blueDirectionsThrough P s).card =
      (verticesOn (Finset.univ : Finset (Vertex (Blue P))) (OnLine (Blue P))
        (⟨s, hs⟩ : Line (Blue P))).card := by
  rw [← directionVerticesThrough_eq_verticesOn P s hs]
  simpa using Fintype.card_congr (Equiv.ofBijective (fiberToVertex P s hs)
    (fiberToVertex_bijective P s hs))

/-- Projective form of ABKPR's recognition trigger.  A blue dual line with
exactly three arrangement vertices, two of which have blue multiplicity two,
already forces the failed-Fano configuration. -/
theorem isFailedFano_of_three_projective_vertices_two_double
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (s : Line (Blue P))
    (v₂ v₃ : Vertex (Blue P)) (hvne : v₂ ≠ v₃)
    (hv₂s : OnLine (Blue P) v₂ s) (hv₃s : OnLine (Blue P) v₃ s)
    (hv₂double : lineMultiplicity (OnLine (Blue P)) v₂ = 2)
    (hv₃double : lineMultiplicity (OnLine (Blue P)) v₃ = 2)
    (hthree :
      (verticesOn (Finset.univ : Finset (Vertex (Blue P))) (OnLine (Blue P)) s).card = 3) :
    IsFailedFano P := by
  obtain ⟨b₂, hb₂s, hv₂b⟩ := exists_other_incident_line (Blue P) v₂ s
  obtain ⟨b₃, hb₃s, hv₃b⟩ := exists_other_incident_line (Blue P) v₃ s
  have hbad₂ : IsDoubleBlueDirection P s.1 b₂.1 :=
    isDoubleBlueDirection_of_incident_of_lineMultiplicity_eq_two
      v₂ s b₂ hb₂s.symm hv₂s hv₂b hv₂double
  have hbad₃ : IsDoubleBlueDirection P s.1 b₃.1 :=
    isDoubleBlueDirection_of_incident_of_lineMultiplicity_eq_two
      v₃ s b₃ hb₃s.symm hv₃s hv₃b hv₃double
  have hdirne : lineFiber P s.1 b₂.1 ≠ lineFiber P s.1 b₃.1 :=
    lineFiber_ne_of_distinct_vertices_on_common_line hvne
      hb₂s.symm hb₃s.symm hv₂s hv₂b hv₃s hv₃b
  apply isFailedFano_of_threeDirections_two_double hred hAcard
    hbad₂ hbad₃ hdirne
  rw [card_blueDirectionsThrough_eq_verticesOn P s.1 s.2]
  exact hthree

end Erdos735.BlueDirectionProjective

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

import ErdosProblems.Erdos735.Primal
import ErdosProblems.Erdos735.ProjectiveBoundaryExtraction

/-!
# Concrete red--blue incidence at projective arrangement vertices

This file identifies the projective incidence used by the concrete blue
cellulation with the homogeneous dual-line incidence in the reduced magic
configuration.  It proves the local ABKPR fact that a blue vertex of
multiplicity two lies on exactly one red line.
-/

namespace Erdos735

open Classical
open scoped LinearAlgebra.Projectivization

namespace RedBlueDualIncidence

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction

/-- The homogeneous representative of a concrete projective arrangement vertex. -/
noncomputable def vertexHomogeneous {B : Finset Point} (v : Vertex B) : DualPoint :=
  ProjectiveDuality.fromCoordinates v.1.rep

lemma vertexHomogeneous_ne_zero {B : Finset Point} (v : Vertex B) :
    vertexHomogeneous v ≠ ProjectiveDuality.homZero := by
  rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
  simpa [vertexHomogeneous] using v.1.rep_nonzero

/-- The projective incidence used to build the blue skeleton is the concrete
dual-line incidence used by the reduced magic configuration. -/
lemma onLine_iff_mem_dualLine {B : Finset Point} (v : Vertex B) (p : Line B) :
    OnLine B v p ↔ vertexHomogeneous v ∈ ProjectiveDuality.dualLine p.1 := by
  change normalVec p.1 ⬝ᵥ v.1.rep = 0 ↔ _
  simpa [vertexHomogeneous] using
    (dotProduct_normalVec_toCoordinates_iff p.1 (vertexHomogeneous v))

/-- Every vertex of the blue projective arrangement is a crossing of the
full dual arrangement. -/
theorem isDualCrossing_vertex_nonordinary (P : Finset Point)
    (v : Vertex (nonordinaryPoints P)) :
    IsDualCrossing P (vertexHomogeneous v) := by
  have hv := v.property
  unfold projectiveVertices at hv
  obtain ⟨pq, -, hpqv⟩ := Finset.mem_image.mp hv
  let p : Line (nonordinaryPoints P) := pq.1.1
  let q : Line (nonordinaryPoints P) := pq.1.2
  have hpq : p.1 ≠ q.1 := by
    intro h
    apply pq.2
    exact Subtype.ext h
  have hpinc : OnLine (nonordinaryPoints P) v p := by
    change Incident v.1 p.1
    rw [← hpqv]
    exact indexedIntersection_incident_left _ pq
  have hqinc : OnLine (nonordinaryPoints P) v q := by
    change Incident v.1 q.1
    rw [← hpqv]
    exact indexedIntersection_incident_right _ pq
  exact ⟨vertexHomogeneous_ne_zero v,
    p.1, nonordinaryPoints_subset P p.2,
    q.1, nonordinaryPoints_subset P q.2, hpq,
    (onLine_iff_mem_dualLine v p).mp hpinc,
    (onLine_iff_mem_dualLine v q).mp hqinc⟩

/-- At a crossing containing a blue line, at most one red line can occur.
Two distinct red lines already make their crossing ordinary, excluding the
blue line. -/
theorem ordinary_incident_unique_at_blue_crossing
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {h : DualPoint}
    (hcross : IsDualCrossing P h) {b : Point}
    (hbB : b ∈ nonordinaryPoints P)
    (hbh : h ∈ ProjectiveDuality.dualLine b)
    {a a' : Point} (haA : a ∈ ordinaryPoints P)
    (ha'A : a' ∈ ordinaryPoints P)
    (hah : h ∈ ProjectiveDuality.dualLine a)
    (ha'h : h ∈ ProjectiveDuality.dualLine a') : a = a' := by
  by_contra haa'
  have haP : a ∈ P := ordinaryPoints_subset P haA
  have ha'P : a' ∈ P := ordinaryPoints_subset P ha'A
  have hbP : b ∈ P := nonordinaryPoints_subset P hbB
  have hfiber := dualIncidentFiber_eq_lineFiber hcross.1 haP ha'P haa' hah ha'h
  have hAA := hred.2.2.2.2.1 a haA a' ha'A haa'
  rw [hAA] at hfiber
  have hbmem : b ∈ dualIncidentFiber P h := by
    simp [dualIncidentFiber, hbP, hbh]
  rw [hfiber] at hbmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
  rcases hbmem with hba | hba'
  · exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) haA (hba ▸ hbB)
  · exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha'A (hba' ▸ hbB)

/-- Blue members incident with a homogeneous point. -/
noncomputable def blueIncidentPoints (P : Finset Point) (h : DualPoint) : Finset Point :=
  (nonordinaryPoints P).filter fun b ↦ h ∈ ProjectiveDuality.dualLine b

/-- Red members incident with a homogeneous point. -/
noncomputable def redIncidentPoints (P : Finset Point) (h : DualPoint) : Finset Point :=
  (ordinaryPoints P).filter fun a ↦ h ∈ ProjectiveDuality.dualLine a

/-- Projective blue incidence and homogeneous blue incidence have the same
finite cardinality. -/
lemma card_blueIncidentPoints_eq_lineMultiplicity (P : Finset Point)
    (v : Vertex (nonordinaryPoints P)) :
    (blueIncidentPoints P (vertexHomogeneous v)).card =
      lineMultiplicity (OnLine (nonordinaryPoints P)) v := by
  classical
  apply Finset.card_bij (fun b _ ↦ (⟨b, (Finset.mem_filter.mp ‹_›).1⟩ :
    Line (nonordinaryPoints P)))
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (onLine_iff_mem_dualLine v _).mpr (Finset.mem_filter.mp hb).2
  · intro b hb b' hb' heq
    exact congrArg Subtype.val heq
  · intro b hb
    have hbinc : OnLine (nonordinaryPoints P) v b := by
      simpa using hb
    refine ⟨b.1, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨b.2, (onLine_iff_mem_dualLine v b).mp hbinc⟩

lemma dualIncidentFiber_eq_blueIncidentPoints_of_no_red
    {P : Finset Point} {h : DualPoint}
    (hno : ∀ a ∈ ordinaryPoints P, h ∉ ProjectiveDuality.dualLine a) :
    dualIncidentFiber P h = blueIncidentPoints P h := by
  classical
  ext p
  simp only [dualIncidentFiber, blueIncidentPoints, Finset.mem_filter]
  constructor
  · rintro ⟨hpP, hph⟩
    have hpA : p ∉ ordinaryPoints P := fun hpA ↦ hno p hpA hph
    exact ⟨Finset.mem_sdiff.mpr ⟨hpP, hpA⟩, hph⟩
  · rintro ⟨hpB, hph⟩
    exact ⟨nonordinaryPoints_subset P hpB, hph⟩

/-- A blue projective vertex of multiplicity two is incident with a red
line.  Otherwise the full crossing would have exactly two lines and hence be
an ordinary crossing, which the reduced red/blue characterization says is
formed by two red lines. -/
theorem exists_ordinary_incident_of_lineMultiplicity_eq_two
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v = 2) :
    ∃ a ∈ ordinaryPoints P,
      vertexHomogeneous v ∈ ProjectiveDuality.dualLine a := by
  by_contra hex
  push Not at hex
  have hfiber := dualIncidentFiber_eq_blueIncidentPoints_of_no_red hex
  have hcard : (dualIncidentFiber P (vertexHomogeneous v)).card = 2 := by
    rw [hfiber, card_blueIncidentPoints_eq_lineMultiplicity P v, hmult]
  have hord : IsOrdinaryDualCrossing P (vertexHomogeneous v) :=
    ⟨isDualCrossing_vertex_nonordinary P v, hcard⟩
  obtain ⟨a, haA, a', ha'A, haa', hne, haInc, ha'Inc⟩ :=
    (ordinaryDualCrossing_iff_red hred).mp hord
  exact hex a haA haInc

/-- Exact local reduced-magic fact at a bad blue vertex: there is precisely
one incident red line. -/
theorem redIncidentPoints_card_eq_one_of_lineMultiplicity_eq_two
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v = 2) :
    (redIncidentPoints P (vertexHomogeneous v)).card = 1 := by
  obtain ⟨a, haA, haInc⟩ :=
    exists_ordinary_incident_of_lineMultiplicity_eq_two hred v hmult
  have hblueCard : (blueIncidentPoints P (vertexHomogeneous v)).card = 2 := by
    rw [card_blueIncidentPoints_eq_lineMultiplicity P v, hmult]
  obtain ⟨b, hb⟩ : (blueIncidentPoints P (vertexHomogeneous v)).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hbB : b ∈ nonordinaryPoints P := (Finset.mem_filter.mp hb).1
  have hbInc : vertexHomogeneous v ∈ ProjectiveDuality.dualLine b :=
    (Finset.mem_filter.mp hb).2
  apply Finset.card_eq_one.mpr
  refine ⟨a, ?_⟩
  ext a'
  simp only [redIncidentPoints, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨ha'A, ha'Inc⟩
    exact ordinary_incident_unique_at_blue_crossing hred
      (isDualCrossing_vertex_nonordinary P v) hbB hbInc ha'A haA ha'Inc haInc
  · rintro rfl
    exact ⟨haA, haInc⟩

/-- Two distinct blue lines through a multiplicity-two projective vertex
form a double-blue direction in the primal incidence language. -/
theorem isDoubleBlueDirection_of_incident_of_lineMultiplicity_eq_two
    {P : Finset Point}
    (v : Vertex (nonordinaryPoints P))
    (s b : Line (nonordinaryPoints P)) (hsb : s ≠ b)
    (hsInc : OnLine (nonordinaryPoints P) v s)
    (hbInc : OnLine (nonordinaryPoints P) v b)
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v = 2) :
    IsDoubleBlueDirection P s.1 b.1 := by
  classical
  have hsb' : s.1 ≠ b.1 := fun h ↦ hsb (Subtype.ext h)
  have hsDual : vertexHomogeneous v ∈ ProjectiveDuality.dualLine s.1 :=
    (onLine_iff_mem_dualLine v s).mp hsInc
  have hbDual : vertexHomogeneous v ∈ ProjectiveDuality.dualLine b.1 :=
    (onLine_iff_mem_dualLine v b).mp hbInc
  have hfiber : dualIncidentFiber P (vertexHomogeneous v) =
      lineFiber P s.1 b.1 :=
    dualIncidentFiber_eq_lineFiber (vertexHomogeneous_ne_zero v)
      (nonordinaryPoints_subset P s.2) (nonordinaryPoints_subset P b.2)
      hsb' hsDual hbDual
  have hblue : dualIncidentFiber P (vertexHomogeneous v) ∩ nonordinaryPoints P =
      blueIncidentPoints P (vertexHomogeneous v) := by
    ext x
    simp only [Finset.mem_inter, dualIncidentFiber, blueIncidentPoints,
      Finset.mem_filter]
    constructor
    · rintro hx
      exact ⟨hx.2, hx.1.2⟩
    · rintro hx
      exact ⟨⟨nonordinaryPoints_subset P hx.1, hx.2⟩, hx.1⟩
  have hcard : (lineFiber P s.1 b.1 ∩ nonordinaryPoints P).card = 2 := by
    rw [← hfiber, hblue, card_blueIncidentPoints_eq_lineMultiplicity P v, hmult]
  exact ⟨s.2, b.2, hsb', hcard⟩

/-- Every multiplicity-two blue projective vertex supplies a concrete
double-blue pair.  The incident-line witnesses are retained for later
exception-recognition arguments. -/
theorem exists_isDoubleBlueDirection_of_lineMultiplicity_eq_two
    {P : Finset Point}
    (v : Vertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v = 2) :
    ∃ s b : Line (nonordinaryPoints P),
      IsDoubleBlueDirection P s.1 b.1 ∧
        OnLine (nonordinaryPoints P) v s ∧
        OnLine (nonordinaryPoints P) v b := by
  classical
  have hv := v.property
  unfold projectiveVertices at hv
  obtain ⟨pq, -, hpqv⟩ := Finset.mem_image.mp hv
  let s : Line (nonordinaryPoints P) := pq.1.1
  let b : Line (nonordinaryPoints P) := pq.1.2
  have hsb : s ≠ b := pq.2
  have hsInc : OnLine (nonordinaryPoints P) v s := by
    change Incident v.1 s.1
    rw [← hpqv]
    exact indexedIntersection_incident_left _ pq
  have hbInc : OnLine (nonordinaryPoints P) v b := by
    change Incident v.1 b.1
    rw [← hpqv]
    exact indexedIntersection_incident_right _ pq
  exact ⟨s, b,
    isDoubleBlueDirection_of_incident_of_lineMultiplicity_eq_two
      v s b hsb hsInc hbInc hmult,
    hsInc, hbInc⟩

/-- Distinct projective vertices on one common blue line determine distinct
primal line fibers.  Thus two bad vertices selected on the same blue dual
line satisfy the distinct-direction premise of the failed-Fano recognition
theorem. -/
theorem lineFiber_ne_of_distinct_vertices_on_common_line
    {P : Finset Point}
    {v u : Vertex (nonordinaryPoints P)} (hvu : v ≠ u)
    {s b d : Line (nonordinaryPoints P)} (hsb : s ≠ b) (hsd : s ≠ d)
    (hvs : OnLine (nonordinaryPoints P) v s)
    (hvb : OnLine (nonordinaryPoints P) v b)
    (hus : OnLine (nonordinaryPoints P) u s)
    (hud : OnLine (nonordinaryPoints P) u d) :
    lineFiber P s.1 b.1 ≠ lineFiber P s.1 d.1 := by
  intro hfiber
  have hbmem : b.1 ∈ lineFiber P s.1 d.1 := by
    rw [← hfiber]
    exact right_mem_lineFiber (nonordinaryPoints_subset P b.2)
  have hcol : Collinear3 s.1 d.1 b.1 :=
    (Finset.mem_filter.mp hbmem).2
  have husDual : vertexHomogeneous u ∈ ProjectiveDuality.dualLine s.1 :=
    (onLine_iff_mem_dualLine u s).mp hus
  have hudDual : vertexHomogeneous u ∈ ProjectiveDuality.dualLine d.1 :=
    (onLine_iff_mem_dualLine u d).mp hud
  have hubDual : vertexHomogeneous u ∈ ProjectiveDuality.dualLine b.1 :=
    mem_dualLine_of_collinear3 (fun h ↦ hsd (Subtype.ext h))
      husDual hudDual hcol
  have hub : OnLine (nonordinaryPoints P) u b :=
    (onLine_iff_mem_dualLine u b).mpr hubDual
  apply hvu
  apply Subtype.ext
  exact ProjectiveArrangement.eq_of_two_common_lines
    (fun h ↦ hsb (Subtype.ext h)) hvs hvb hus hub

open SignVector

/-- The multiplicity-two theorem in the exact lifted vertex type used by
the concrete projective `BoundaryExtraction`. -/
theorem redIncidentPoints_card_eq_one_of_lifted_blueMultiplicity_eq_two
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (X : LiftedCyclicEdgeRealization.LiftedBoundaryCardRealization
      (normals (nonordinaryPoints P)) (OnLine (nonordinaryPoints P)))
    (v : Vertex (nonordinaryPoints P) × Bool)
    (hmult : (X.toBoundaryExtraction
      (hn := normals_ne_zero (nonordinaryPoints P))).blueMultiplicity v = 2) :
    (redIncidentPoints P (vertexHomogeneous v.1)).card = 1 := by
  apply redIncidentPoints_card_eq_one_of_lineMultiplicity_eq_two hred v.1
  exact hmult

end RedBlueDualIncidence
end Erdos735

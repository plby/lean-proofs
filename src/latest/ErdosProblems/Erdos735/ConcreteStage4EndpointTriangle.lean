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

import ErdosProblems.Erdos735.ConcreteStage4FlankComplete
import ErdosProblems.Erdos735.ConcreteOppositeLineCoherence

/-!
# The missing flank at a deficient-component endpoint

An evil endpoint of the canonical Hall-deficient component has helping
degree one.  Its selected helping neighbor occupies one of the two cyclic
flanks of the adjacent bad quadrangle.  Outside failed Fano, every
zero-diagonal flank is a helping neighbor.  Hence the other cyclic flank
must be triangular.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4EndpointTriangle

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

/-- A degree-one endpoint has a cyclically adjacent, triangular flank which
is different from the face of every one of its helping neighbors. -/
theorem exists_missing_triangle_flank
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ ((ConcreteStage4FlankComplete.flankSystem
      hred ha hb hd hncol hAcard hnotFF).toHelpingGraph).NoEvilEvilPath)
    (endpoint : Fin 2) :
    let L := ConcreteStage4FlankComplete.flankSystem
      hred ha hb hd hncol hAcard hnotFF
    let G := L.toHelpingGraph
    let e := (G.deficientPathComponent hHall).endpoint endpoint
    let bad := (D hred ha hb hd hncol).across
      ((D hred ha hb hd hncol).evilDart e)
    ∃ j : Fin ((C ha hb hd hncol).faceDegree bad.1),
      ABKPR.Data.CyclicAdjacentIndex bad.2 j ∧
      (C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 = 3 ∧
      ∀ h : (D hred ha hb hd hncol).HelpingPair,
        G.Adj e h →
          ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 ≠ h.face := by
  let K := ConcreteStage4FlankComplete.geometricFlankBounds
    hred ha hb hd hncol hAcard hnotFF
  let L := ConcreteStage4FlankComplete.flankSystem
    hred ha hb hd hncol hAcard hnotFF
  let G := L.toHelpingGraph
  let component := G.deficientPathComponent hHall
  let e := component.endpoint endpoint
  let bad := (D hred ha hb hd hncol).across
    ((D hred ha hb hd hncol).evilDart e)
  let jNext := ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2
  let jPrev := ABKPR.faceSucc (C ha hb hd hncol) bad.1
    (ABKPR.faceSucc (C ha hb hd hncol) bad.1
      (ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2))
  have hdegree : (G.evilNeighbors e).card = 1 :=
    component.endpoint_degree_one endpoint
  have hnonempty : (G.evilNeighbors e).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨selected, hselectedMem⟩ := hnonempty
  have hselectedAdj : L.Adj e selected :=
    (Finset.mem_filter.mp hselectedMem).2
  obtain ⟨selectedSide, hselectedSide⟩ := hselectedAdj
  have hselectedGeom : (D hred ha hb hd hncol).IsGeometricFlank
      ConcretePolarFlankBounds.edgeLine e selected := by
    exact L.evilFlank_geometric e selectedSide selected hselectedSide
  obtain ⟨⟨jSelected, hjSelectedAdj, hjSelectedFace⟩, _howner⟩ :=
    hselectedGeom
  have hbadfour : (C ha hb hd hncol).faceDegree bad.1 = 4 :=
    ((D hred ha hb hd hncol).evilDart_across_bad e).1.1
  have hjSelected : jSelected = jNext ∨ jSelected = jPrev := by
    rcases hjSelectedAdj with h | h
    · exact Or.inl h.symm
    · right
      apply ABKPR.faceSucc_injective (C ha hb hd hncol) bad.1
      calc
        ABKPR.faceSucc (C ha hb hd hncol) bad.1 jSelected = bad.2 := h
        _ = ABKPR.faceSucc (C ha hb hd hncol) bad.1 jPrev :=
          (ABKPR.faceSucc_four_of_faceDegree_eq_four
            (C ha hb hd hncol) hbadfour bad.2).symm
  have hadjNext : ABKPR.Data.CyclicAdjacentIndex bad.2 jNext := Or.inl rfl
  have hadjPrev : ABKPR.Data.CyclicAdjacentIndex bad.2 jPrev := by
    right
    exact ABKPR.faceSucc_four_of_faceDegree_eq_four
      (C ha hb hd hncol) hbadfour bad.2
  have hnextPrev : jNext ≠ jPrev := by
    intro h
    have hsquare : ABKPR.faceSucc (C ha hb hd hncol) bad.1
        (ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2) = bad.2 := by
      calc
        ABKPR.faceSucc (C ha hb hd hncol) bad.1 jNext =
            ABKPR.faceSucc (C ha hb hd hncol) bad.1 jPrev :=
          congrArg (ABKPR.faceSucc (C ha hb hd hncol) bad.1) h
        _ = bad.2 := ABKPR.faceSucc_four_of_faceDegree_eq_four
          (C ha hb hd hncol) hbadfour bad.2
    exact ABKPR.secondSucc_ne_of_faceDegree_eq_four
      (C ha hb hd hncol) hbadfour bad.2 hsquare
  have uniqueNeighbor {h : (D hred ha hb hd hncol).HelpingPair}
      (hh : G.Adj e h) : h = selected := by
    have hhmem : h ∈ G.evilNeighbors e := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ h, hh⟩
    by_contra hne
    have hpair : ({selected, h} : Finset
        ((D hred ha hb hd hncol).HelpingPair)) ⊆ G.evilNeighbors e := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hselectedMem
      · exact hhmem
    have htwo : 2 ≤ (G.evilNeighbors e).card := by
      have hc := Finset.card_le_card hpair
      rw [Finset.card_pair (Ne.symm hne)] at hc
      exact hc
    omega
  have missing_is_triangle
      (j : Fin ((C ha hb hd hncol).faceDegree bad.1))
      (hadj : ABKPR.Data.CyclicAdjacentIndex bad.2 j)
      (hjne : j ≠ jSelected) :
      (C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 = 3 := by
    rcases (D hred ha hb hd hncol).flank_triangle_or_zeroDiagonal
        (ConcretePolarEndpointRestriction.concreteData_endpointRestriction
          hred ha hb hd hncol) e j hadj with htri | hzero
    · exact htri
    · obtain ⟨h, hhface, hhgeom⟩ :=
        ConcreteStage4FlankExistence.exists_geometricFlank_of_zeroDiagonal
          hred ha hb hd hncol hAcard hnotFF e j hadj hzero
      have hhAdj : L.Adj e h := by
        change ∃ side, K.evilFlank e side = some h
        exact (K.exists_evilFlank_iff e h).2 hhgeom
      have heq : h = selected := uniqueNeighbor hhAdj
      exfalso
      apply ConcretePolarABKPRData.concreteData_across_faces_ne
        hred ha hb hd hncol bad.1 j jSelected hjne
      calc
        ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 = h.face := hhface.symm
        _ = selected.face := congrArg ABKPR.Data.HelpingPair.face heq
        _ = ((D hred ha hb hd hncol).across ⟨bad.1, jSelected⟩).1 :=
          hjSelectedFace.symm
  rcases hjSelected with hselNext | hselPrev
  · refine ⟨jPrev, hadjPrev,
      missing_is_triangle jPrev hadjPrev ?_, ?_⟩
    · simpa [hselNext] using hnextPrev.symm
    · intro h hhAdj hfaceEq
      have heq := uniqueNeighbor hhAdj
      apply ConcretePolarABKPRData.concreteData_across_faces_ne
        hred ha hb hd hncol bad.1 jPrev jSelected (by
          simpa [hselNext] using hnextPrev.symm)
      calc
        ((D hred ha hb hd hncol).across ⟨bad.1, jPrev⟩).1 = h.face := hfaceEq
        _ = selected.face := congrArg ABKPR.Data.HelpingPair.face heq
        _ = ((D hred ha hb hd hncol).across ⟨bad.1, jSelected⟩).1 :=
          hjSelectedFace.symm
  · refine ⟨jNext, hadjNext,
      missing_is_triangle jNext hadjNext ?_, ?_⟩
    · simpa [hselPrev] using hnextPrev
    · intro h hhAdj hfaceEq
      have heq := uniqueNeighbor hhAdj
      apply ConcretePolarABKPRData.concreteData_across_faces_ne
        hred ha hb hd hncol bad.1 jNext jSelected (by
          simpa [hselPrev] using hnextPrev)
      calc
        ((D hred ha hb hd hncol).across ⟨bad.1, jNext⟩).1 = h.face := hfaceEq
        _ = selected.face := congrArg ABKPR.Data.HelpingPair.face heq
        _ = ((D hred ha hb hd hncol).across ⟨bad.1, jSelected⟩).1 :=
          hjSelectedFace.symm

/-- The missing triangular flank at either endpoint lies on that evil
endpoint's opposite line.  Thus it is exactly the local continuation
triangle required by the corrected Stage-4 path extraction. -/
theorem exists_missing_triangle_flank_incident
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ ((ConcreteStage4FlankComplete.flankSystem
      hred ha hb hd hncol hAcard hnotFF).toHelpingGraph).NoEvilEvilPath)
    (endpoint : Fin 2) :
    let L := ConcreteStage4FlankComplete.flankSystem
      hred ha hb hd hncol hAcard hnotFF
    let G := L.toHelpingGraph
    let e := (G.deficientPathComponent hHall).endpoint endpoint
    let bad := (D hred ha hb hd hncol).across
      ((D hred ha hb hd hncol).evilDart e)
    ∃ j : Fin ((C ha hb hd hncol).faceDegree bad.1),
      ABKPR.Data.CyclicAdjacentIndex bad.2 j ∧
      (C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 = 3 ∧
      SignVectorArrangement.LineFaceIncident (normals (B (P := P)))
        (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e)
        ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 ∧
      ∀ h : (D hred ha hb hd hncol).HelpingPair,
        G.Adj e h →
          ((D hred ha hb hd hncol).across ⟨bad.1, j⟩).1 ≠ h.face := by
  let L := ConcreteStage4FlankComplete.flankSystem
    hred ha hb hd hncol hAcard hnotFF
  let G := L.toHelpingGraph
  let e := (G.deficientPathComponent hHall).endpoint endpoint
  let bad := (D hred ha hb hd hncol).across
    ((D hred ha hb hd hncol).evilDart e)
  obtain ⟨j, hadj, htri, hmissing⟩ :=
    exists_missing_triangle_flank
      hred ha hb hd hncol hAcard hnotFF hHall endpoint
  refine ⟨j, hadj, htri, ?_, hmissing⟩
  exact ConcreteOppositeLineCoherence.triangleFlank_incident_evilOppositeLine
    hred ha hb hd hncol L
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
    e j hadj htri

end Erdos735.ConcreteStage4EndpointTriangle

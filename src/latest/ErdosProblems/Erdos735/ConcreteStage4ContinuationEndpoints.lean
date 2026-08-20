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

import ErdosProblems.Erdos735.ConcreteStage4EndpointTriangle

/-!
# Canonical endpoint continuations of the Stage-4 deficient component

Outside the failed-Fano exception, each degree-one endpoint of the canonical
Hall-deficient component has a unique missing flank among the two cyclic
flanks of its adjacent bad quadrangle.  We choose that flank and record the
properties already established by the local literal-polar argument: it is a
triangle, it lies on the endpoint's opposite line, and it is not the face of
any helping neighbor of that endpoint.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4ContinuationEndpoints

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector
open SignVectorArrangement

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

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- The canonical deficient component used throughout Stage 4. -/
private abbrev component
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  (G hred ha hb hd hncol hAcard hnotFF).deficientPathComponent hHall

/-- The bad quadrangle adjacent to endpoint `k`. -/
private abbrev endpointBad
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :=
  (D hred ha hb hd hncol).across
    ((D hred ha hb hd hncol).evilDart
      ((component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k))

/-- Choose the missing cyclic flank at endpoint `k`. -/
noncomputable def endpointIndex
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    Fin ((C ha hb hd hncol).faceDegree
      (endpointBad hred ha hb hd hncol hAcard hnotFF hHall k).1) :=
  Classical.choose
    (ConcreteStage4EndpointTriangle.exists_missing_triangle_flank_incident
      hred ha hb hd hncol hAcard hnotFF hHall k)

/-- The continuation face at endpoint `k`. -/
noncomputable def endpointTriangle
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) : StrictFace (normals (B (P := P))) :=
  ((D hred ha hb hd hncol).across
    ⟨(endpointBad hred ha hb hd hncol hAcard hnotFF hHall k).1,
      endpointIndex hred ha hb hd hncol hAcard hnotFF hHall k⟩).1

private theorem endpointIndex_spec
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
    let bad := endpointBad hred ha hb hd hncol hAcard hnotFF hHall k
    ABKPR.Data.CyclicAdjacentIndex bad.2
        (endpointIndex hred ha hb hd hncol hAcard hnotFF hHall k) ∧
      (C ha hb hd hncol).faceDegree
          (endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k) = 3 ∧
      LineFaceIncident (normals (B (P := P)))
          (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol)
            (L hred ha hb hd hncol hAcard hnotFF) e)
          (endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k) ∧
      ∀ h : (D hred ha hb hd hncol).HelpingPair,
        (G hred ha hb hd hncol hAcard hnotFF).Adj e h →
          endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k ≠ h.face := by
  exact Classical.choose_spec
    (ConcreteStage4EndpointTriangle.exists_missing_triangle_flank_incident
      hred ha hb hd hncol hAcard hnotFF hHall k)

theorem endpointIndex_adjacent
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    ABKPR.Data.CyclicAdjacentIndex
      (endpointBad hred ha hb hd hncol hAcard hnotFF hHall k).2
      (endpointIndex hred ha hb hd hncol hAcard hnotFF hHall k) :=
  (endpointIndex_spec hred ha hb hd hncol hAcard hnotFF hHall k).1

/-- Cellulation-degree form used by the boundary-dart continuation API. -/
theorem endpointTriangle_faceDegree_three
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    (C ha hb hd hncol).faceDegree
      (endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k) = 3 :=
  (endpointIndex_spec hred ha hb hd hncol hAcard hnotFF hHall k).2.1

theorem endpointTriangle_degree_three
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    strictFaceDegree (normals (B (P := P)))
      (endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k) = 3 := by
  rw [← ABKPR.Data.boundaryExtraction_faceDegree_eq_strictFaceDegree
    (B := ConcretePolarCellulation.boundaryExtraction
      (B (P := P)) ha hb hd hncol)]
  exact endpointTriangle_faceDegree_three
    hred ha hb hd hncol hAcard hnotFF hHall k

theorem endpointTriangle_incident_own
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    LineFaceIncident (normals (B (P := P)))
      (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol)
        (L hred ha hb hd hncol hAcard hnotFF)
        ((component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k))
      (endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k) :=
  (endpointIndex_spec
    hred ha hb hd hncol hAcard hnotFF hHall k).2.2.1

theorem endpointTriangle_ne_helpingNeighbor
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) (h : (D hred ha hb hd hncol).HelpingPair)
    (hh : (G hred ha hb hd hncol hAcard hnotFF).Adj
      ((component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k) h) :
    endpointTriangle hred ha hb hd hncol hAcard hnotFF hHall k ≠ h.face :=
  (endpointIndex_spec
    hred ha hb hd hncol hAcard hnotFF hHall k).2.2.2 h hh

end Erdos735.ConcreteStage4ContinuationEndpoints

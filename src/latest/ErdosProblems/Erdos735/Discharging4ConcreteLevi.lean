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

import ErdosProblems.Erdos735.Discharging4Concrete
import ErdosProblems.Erdos735.LeviStage4
import ErdosProblems.Erdos735.Stage3Packing

/-!
# The concrete Stage-4 graph and the sign-vector Levi theorem

This file states the last geometric extraction in an explicit form.  A
failure of the Hall/no-evil--evil-path property produces an alternating
path on a common arrangement line `pathLine`.  The ABKPR argument does
*not* apply Levi's theorem to that line: it applies Levi to the second line
supporting the edges opposite the path edges.  The two triangles in the
Levi certificate are consequently the continuation faces at the two ends
of the path, not the evil triangles themselves.  Keeping these two lines
and these two pairs of faces separate is essential for the statement to be
mathematically correct.
-/

namespace Erdos735

open scoped BigOperators
noncomputable section

namespace ABKPR.Data

open SignVector
open SignVectorArrangement

universe uI

variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {n : I → Vec3} {hn : ∀ i, n i ≠ 0}
variable {B : BoundaryExtraction n hn}
variable {A : ABKPR.Data (B.toBlueCellulation n hn)}

/-- The face degree in the cellulation extracted from sign vectors is the
cardinality definition used by the Levi interface. -/
lemma boundaryExtraction_faceDegree_eq_strictFaceDegree (f : StrictFace n) :
    (B.toBlueCellulation n hn).faceDegree f = strictFaceDegree n f := by
  unfold BlueCellulation.faceDegree strictFaceDegree
  change (B.faceBoundary f).length = (faceEdges n f).card
  rw [← B.faceBoundary_toFinset f]
  exact (List.toFinset_card_of_nodup (B.faceBoundary_nodup f)).symm

section PathGeometry

variable (L : A.FlankSystem I)

/-- The geometric object extracted from an alleged evil--evil component.

`pathLine` is the common owner of the bad-neighbor edges along the
alternating path.  `selectedOppositeLine` is the owner of the edges opposite
those path edges.  The two `endpointTriangle`s are the continuation faces at
the ends of the path.  The last field is the ABKPR continuation conclusion
on the *opposite* line: no third triangular face occurs there. -/
structure EvilPathGeometry where
  edgeLine_eq_strictEdgeOwner : L.edgeLine = strictEdgeOwner
  pathLine : I
  endpointEvil : Fin 2 → A.EvilFace
  endpointEvil_injective : Function.Injective endpointEvil
  endpoint_badEdge_owner : ∀ k,
    L.edgeLine
        (A.boundaryEdge (endpointEvil k).1 (A.evilIndex (endpointEvil k))) =
      pathLine
  selectedOppositeLine : I
  endpointTriangle : Fin 2 → StrictFace n
  endpointTriangle_injective : Function.Injective endpointTriangle
  endpointTriangle_incident : ∀ k,
    LineFaceIncident n selectedOppositeLine (endpointTriangle k)
  endpointTriangle_degree_three : ∀ k,
    strictFaceDegree n (endpointTriangle k) = 3
  allIncidentTrianglesAreEndpoints :
    ∀ f : StrictFace n,
      LineFaceIncident n selectedOppositeLine f →
        strictFaceDegree n f = 3 → ∃ k, endpointTriangle k = f

namespace EvilPathGeometry

variable {L : A.FlankSystem I} (P : EvilPathGeometry L)

/-- The evil endpoint faces remain incident with the common path line.  This
is useful provenance, but these are deliberately not the two faces used in
the Levi certificate. -/
lemma endpointEvil_incident_pathLine (k : Fin 2) :
    LineFaceIncident n P.pathLine (P.endpointEvil k).1 := by
  let e := A.boundaryEdge (P.endpointEvil k).1
    (A.evilIndex (P.endpointEvil k))
  refine ⟨e, ?_, ?_⟩
  · rw [← B.faceBoundary_toFinset]
    exact List.mem_toFinset.mpr (A.boundaryEdge_mem _ _)
  · rw [← P.edgeLine_eq_strictEdgeOwner]
    exact P.endpoint_badEdge_owner k

/-- Evil path endpoints are triangular in the sign-vector degree
convention.  Again, these path-line triangles are distinct from the
continuation triangles on the opposite line. -/
lemma endpointEvil_degree_three (k : Fin 2) :
    strictFaceDegree n (P.endpointEvil k).1 = 3 := by
  rw [← boundaryExtraction_faceDegree_eq_strictFaceDegree (B := B)]
  exact (P.endpointEvil k).2.1.1

/-- Forget the evil-face witnesses while retaining the exact finite
certificate consumed by the sign-vector Levi theorem. -/
def toLineCertificate : EvilPathLineCertificate n where
  selectedLine := P.selectedOppositeLine
  endpointTriangle := P.endpointTriangle
  endpoint_injective := P.endpointTriangle_injective
  allIncidentTrianglesAreEndpoints := P.allIncidentTrianglesAreEndpoints

end EvilPathGeometry

/-- Antipodally correct geometric output of the continuation argument.

The arrangement lives on the two-sphere, whereas the ABKPR continuation
argument is projective.  Thus its two endpoint triangles account for four
strict spherical faces: each endpoint face and its antipode. -/
structure ProjectiveEvilPathGeometry where
  edgeLine_eq_strictEdgeOwner : L.edgeLine = strictEdgeOwner
  pathLine : I
  endpointEvil : Fin 2 → A.EvilFace
  endpointEvil_injective : Function.Injective endpointEvil
  endpoint_badEdge_owner : ∀ k,
    L.edgeLine
        (A.boundaryEdge (endpointEvil k).1 (A.evilIndex (endpointEvil k))) =
      pathLine
  selectedOppositeLine : I
  endpointTriangle : Fin 2 → StrictFace n
  endpointTriangle_incident : ∀ k,
    LineFaceIncident n selectedOppositeLine (endpointTriangle k)
  endpointTriangle_degree_three : ∀ k,
    strictFaceDegree n (endpointTriangle k) = 3
  allIncidentTrianglesAreEndpointOrAntipode :
    ∀ f : StrictFace n,
      LineFaceIncident n selectedOppositeLine f →
        strictFaceDegree n f = 3 →
          ∃ k, endpointTriangle k = f ∨
            antipodalStrictFace (endpointTriangle k) = f

namespace ProjectiveEvilPathGeometry

variable {L : A.FlankSystem I} (P : ProjectiveEvilPathGeometry L)

/-- Forget path provenance and retain the projectively correct finite
certificate consumed by the strengthened Levi theorem. -/
def toProjectiveLineCertificate : ProjectiveEvilPathLineCertificate n where
  selectedLine := P.selectedOppositeLine
  endpointTriangle := P.endpointTriangle
  allIncidentTrianglesAreEndpointOrAntipode :=
    P.allIncidentTrianglesAreEndpointOrAntipode

end ProjectiveEvilPathGeometry

/-- The sole global path-extraction input left after constructing the
concrete helping graph.  It includes the opposite-edge continuation lemma,
which is precisely the genuinely geometric part of the ABKPR path
argument. -/
structure LeviPathExtraction where
  extract : ¬ (L.toHelpingGraph).NoEvilEvilPath → EvilPathGeometry L

namespace LeviPathExtraction

variable {L : A.FlankSystem I}

/-- The explicit geometric extraction instantiates the generic Stage-4
Levi bridge. -/
def toLeviPathBridge (X : LeviPathExtraction L) :
    ABKPR.HelpingGraph.LeviPathBridge (L.toHelpingGraph) n where
  certificate hpath := (X.extract hpath).toLineCertificate

/-- Levi excludes an evil--evil path in the concrete helper graph. -/
theorem noEvilEvilPath (X : LeviPathExtraction L)
    (Hlevi : HasSignVectorLeviProperty n) :
    (L.toHelpingGraph).NoEvilEvilPath :=
  ABKPR.HelpingGraph.noEvilEvilPath_of_signVectorLevi Hlevi
    (toLeviPathBridge X)

/-- The final charge contradiction for a sign-vector realization, with all
bookkeeping and graph degree bounds already discharged. -/
theorem contradiction
    (X : LeviPathExtraction L) (G : A.ReducedStage3Geometry)
    (hrest : A.EndpointRestriction)
    (Hlevi : HasSignVectorLeviProperty n) : False :=
  FlankSystem.contradiction L
    (ReducedStage3Geometry.toStage3Hypotheses A G hrest) hrest
    (A.neighborPacking_of_endpointRestriction hrest)
    (noEvilEvilPath X Hlevi)

end LeviPathExtraction

/-- Antipodally correct concrete extraction from every Hall failure. -/
structure ProjectiveLeviPathExtraction where
  extract : ¬ (L.toHelpingGraph).NoEvilEvilPath →
    ProjectiveEvilPathGeometry L

namespace ProjectiveLeviPathExtraction

variable {L : A.FlankSystem I}

def toProjectiveLeviPathBridge (X : ProjectiveLeviPathExtraction L) :
    ABKPR.HelpingGraph.ProjectiveLeviPathBridge (L.toHelpingGraph) n where
  certificate hpath := (X.extract hpath).toProjectiveLineCertificate

theorem noEvilEvilPath (X : ProjectiveLeviPathExtraction L)
    (Hlevi : HasProjectiveSignVectorLeviProperty n) :
    (L.toHelpingGraph).NoEvilEvilPath :=
  ABKPR.HelpingGraph.noEvilEvilPath_of_projective_signVectorLevi Hlevi
    (toProjectiveLeviPathBridge X)

theorem contradiction
    (X : ProjectiveLeviPathExtraction L) (G : A.ReducedStage3Geometry)
    (hrest : A.EndpointRestriction)
    (Hlevi : HasProjectiveSignVectorLeviProperty n) : False :=
  FlankSystem.contradiction L
    (ReducedStage3Geometry.toStage3Hypotheses A G hrest) hrest
    (A.neighborPacking_of_endpointRestriction hrest)
    (noEvilEvilPath X Hlevi)

end ProjectiveLeviPathExtraction

end PathGeometry

end ABKPR.Data

end

end Erdos735

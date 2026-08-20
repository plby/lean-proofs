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

import ErdosProblems.Erdos735.Stage4OppositeLine

/-!
# From a deficient path component to the corrected Levi certificate

The finite Hall argument supplies the two degree-one evil endpoints.  The
opposite-line coherence lemma supplies their common second line.  What
remains of the local ABKPR geometry is exactly:

* the continuation face at each degree-one endpoint is triangular and is
  incident with that endpoint's opposite line;
* the two continuation triangles are different;
* every triangular face incident with the selected opposite line is one of
  these two.

This file packages precisely those conclusions and constructs the corrected
`LeviPathExtraction`.  It also gives a dichotomy theorem suited to the
concrete proof: a local failure may produce the failed-Fano exception;
otherwise it supplies the continuation package.
-/

namespace Erdos735

noncomputable section

namespace ABKPR.Data

open SignVector SignVectorArrangement

universe uI

variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {n : I → Vec3} {hn : ∀ i, n i ≠ 0}
variable {B : BoundaryExtraction n hn}
variable {A : ABKPR.Data (B.toBlueCellulation n hn)}
variable (L : A.FlankSystem I)
variable (K : OppositeLineCoherence A L)

/-- The two continuation triangles and the exact exhaustion statement on
the common opposite line of a fixed deficient path component. -/
structure DeficientPathContinuation
    (hHall : ¬ L.toHelpingGraph.NoEvilEvilPath) where
  endpointTriangle : Fin 2 → StrictFace n
  endpointTriangle_injective : Function.Injective endpointTriangle
  endpointTriangle_incident_own : ∀ k,
    LineFaceIncident n
      (evilOppositeLine A L
        ((L.toHelpingGraph.deficientPathComponent hHall).endpoint k))
      (endpointTriangle k)
  endpointTriangle_degree_three : ∀ k,
    strictFaceDegree n (endpointTriangle k) = 3
  allIncidentTrianglesAreEndpoints : ∀ f : StrictFace n,
    LineFaceIncident n
        (evilOppositeLine A L
          ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0)) f →
      strictFaceDegree n f = 3 → ∃ k, endpointTriangle k = f

namespace DeficientPathContinuation

variable {L : A.FlankSystem I} {K : OppositeLineCoherence A L}
variable {hHall : ¬ L.toHelpingGraph.NoEvilEvilPath}

/-- Assemble the corrected geometric path certificate.  The path line and
the opposite line are kept separate, and the finite component's evil
endpoints are kept separate from its continuation triangles. -/
def toEvilPathGeometry
    (T : DeficientPathContinuation L hHall)
    (hedge : L.edgeLine = strictEdgeOwner) : EvilPathGeometry L where
  edgeLine_eq_strictEdgeOwner := hedge
  pathLine :=
    L.edgeLine
      (A.boundaryEdge
        ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0).1
        (A.evilIndex
          ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0)))
  endpointEvil := (L.toHelpingGraph.deficientPathComponent hHall).endpoint
  endpointEvil_injective :=
    (L.toHelpingGraph.deficientPathComponent hHall).endpoint_injective
  endpoint_badEdge_owner := by
    intro k
    exact (deficientPath_endpoints_badEdgeLine_eq A L hHall k).symm
  selectedOppositeLine :=
    evilOppositeLine A L
      ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0)
  endpointTriangle := T.endpointTriangle
  endpointTriangle_injective := T.endpointTriangle_injective
  endpointTriangle_incident := by
    intro k
    rw [OppositeLineCoherence.deficientPath_endpoints_oppositeLine_eq
      A L K hHall k]
    exact T.endpointTriangle_incident_own k
  endpointTriangle_degree_three := T.endpointTriangle_degree_three
  allIncidentTrianglesAreEndpoints := T.allIncidentTrianglesAreEndpoints

/-- One continuation package at one Hall-failure proof is enough: proofs of
the same proposition are subsingletons, so it handles every invocation of
`LeviPathExtraction.extract`. -/
def toLeviPathExtraction
    (T : DeficientPathContinuation L hHall)
    (hedge : L.edgeLine = strictEdgeOwner) : LeviPathExtraction L where
  extract h := by
    have hh : h = hHall := Subsingleton.elim _ _
    subst h
    exact toEvilPathGeometry (K := K) T hedge

end DeficientPathContinuation

/-- Projectively correct continuation package.  The two endpoint
continuations cover their two antipodal orbits, rather than only two chosen
spherical representatives. -/
structure ProjectiveDeficientPathContinuation
    (hHall : ¬ L.toHelpingGraph.NoEvilEvilPath) where
  endpointTriangle : Fin 2 → StrictFace n
  endpointTriangle_incident_own : ∀ k,
    LineFaceIncident n
      (evilOppositeLine A L
        ((L.toHelpingGraph.deficientPathComponent hHall).endpoint k))
      (endpointTriangle k)
  endpointTriangle_degree_three : ∀ k,
    strictFaceDegree n (endpointTriangle k) = 3
  allIncidentTrianglesAreEndpointOrAntipode : ∀ f : StrictFace n,
    LineFaceIncident n
        (evilOppositeLine A L
          ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0)) f →
      strictFaceDegree n f = 3 →
        ∃ k, endpointTriangle k = f ∨
          antipodalStrictFace (endpointTriangle k) = f

namespace ProjectiveDeficientPathContinuation

variable {L : A.FlankSystem I} {K : OppositeLineCoherence A L}
variable {hHall : ¬ L.toHelpingGraph.NoEvilEvilPath}

def toProjectiveEvilPathGeometry
    (T : ProjectiveDeficientPathContinuation L hHall)
    (hedge : L.edgeLine = strictEdgeOwner) :
    ProjectiveEvilPathGeometry L where
  edgeLine_eq_strictEdgeOwner := hedge
  pathLine :=
    L.edgeLine
      (A.boundaryEdge
        ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0).1
        (A.evilIndex
          ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0)))
  endpointEvil := (L.toHelpingGraph.deficientPathComponent hHall).endpoint
  endpointEvil_injective :=
    (L.toHelpingGraph.deficientPathComponent hHall).endpoint_injective
  endpoint_badEdge_owner := by
    intro k
    exact (deficientPath_endpoints_badEdgeLine_eq A L hHall k).symm
  selectedOppositeLine :=
    evilOppositeLine A L
      ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0)
  endpointTriangle := T.endpointTriangle
  endpointTriangle_incident := by
    intro k
    rw [OppositeLineCoherence.deficientPath_endpoints_oppositeLine_eq
      A L K hHall k]
    exact T.endpointTriangle_incident_own k
  endpointTriangle_degree_three := T.endpointTriangle_degree_three
  allIncidentTrianglesAreEndpointOrAntipode :=
    T.allIncidentTrianglesAreEndpointOrAntipode

def toProjectiveLeviPathExtraction
    (T : ProjectiveDeficientPathContinuation L hHall)
    (hedge : L.edgeLine = strictEdgeOwner) :
    ProjectiveLeviPathExtraction L where
  extract h := by
    have hh : h = hHall := Subsingleton.elim _ _
    subst h
    exact toProjectiveEvilPathGeometry (K := K) T hedge

end ProjectiveDeficientPathContinuation

/-- Projectively correct assembly dichotomy. -/
theorem exceptional_or_projectiveLeviPathExtraction
    {Exceptional : Prop}
    (K : OppositeLineCoherence A L)
    (hedge : L.edgeLine = strictEdgeOwner)
    (resolve : ∀ hHall : ¬ L.toHelpingGraph.NoEvilEvilPath,
      Exceptional ∨
        Nonempty (ProjectiveDeficientPathContinuation L hHall)) :
    Exceptional ∨ Nonempty (ProjectiveLeviPathExtraction L) := by
  by_cases hpath : L.toHelpingGraph.NoEvilEvilPath
  · right
    exact ⟨{
      extract := fun hHall ↦ (hHall hpath).elim
    }⟩
  · cases hresolve : resolve hpath with
    | inl hexceptional => exact Or.inl hexceptional
    | inr hcontinuation =>
        obtain ⟨T⟩ := hcontinuation
        exact Or.inr
          ⟨ProjectiveDeficientPathContinuation.toProjectiveLeviPathExtraction
            (K := K) T hedge⟩

theorem projectiveLeviPathExtraction_of_not_exceptional
    {Exceptional : Prop}
    (K : OppositeLineCoherence A L)
    (hedge : L.edgeLine = strictEdgeOwner)
    (resolve : ∀ hHall : ¬ L.toHelpingGraph.NoEvilEvilPath,
      Exceptional ∨
        Nonempty (ProjectiveDeficientPathContinuation L hHall))
    (hnot : ¬ Exceptional) :
    Nonempty (ProjectiveLeviPathExtraction L) := by
  rcases exceptional_or_projectiveLeviPathExtraction L K hedge resolve with h | h
  · exact (hnot h).elim
  · exact h

/-- Assembly-facing dichotomy.  If the Hall property already holds, the
extraction function has an empty domain.  Otherwise the concrete local
analysis of its canonical deficient component either recognizes the
exception or produces exactly the two continuation triangles required by
Levi. -/
theorem exceptional_or_leviPathExtraction
    {Exceptional : Prop}
    (K : OppositeLineCoherence A L)
    (hedge : L.edgeLine = strictEdgeOwner)
    (resolve : ∀ hHall : ¬ L.toHelpingGraph.NoEvilEvilPath,
      Exceptional ∨ Nonempty (DeficientPathContinuation L hHall)) :
    Exceptional ∨ Nonempty (LeviPathExtraction L) := by
  by_cases hpath : L.toHelpingGraph.NoEvilEvilPath
  · right
    exact ⟨{
      extract := fun hHall ↦ (hHall hpath).elim
    }⟩
  · cases hresolve : resolve hpath with
    | inl hexceptional => exact Or.inl hexceptional
    | inr hcontinuation =>
        obtain ⟨T⟩ := hcontinuation
        exact Or.inr ⟨DeficientPathContinuation.toLeviPathExtraction
          (K := K) T hedge⟩

/-- Nonexceptional form used by the reduced-core assembly. -/
theorem leviPathExtraction_of_not_exceptional
    {Exceptional : Prop}
    (K : OppositeLineCoherence A L)
    (hedge : L.edgeLine = strictEdgeOwner)
    (resolve : ∀ hHall : ¬ L.toHelpingGraph.NoEvilEvilPath,
      Exceptional ∨ Nonempty (DeficientPathContinuation L hHall))
    (hnot : ¬ Exceptional) : Nonempty (LeviPathExtraction L) := by
  rcases exceptional_or_leviPathExtraction L K hedge resolve with h | h
  · exact (hnot h).elim
  · exact h

end ABKPR.Data

end
end Erdos735

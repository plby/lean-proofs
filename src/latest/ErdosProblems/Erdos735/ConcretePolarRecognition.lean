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

import ErdosProblems.Erdos735.BlueDirectionProjective
import ErdosProblems.Erdos735.ConcreteStrictEdgeCyclic

/-!
# Concrete three-edge failed-Fano recognition

Three literal strict edges on one blue projective line whose endpoint pairs
form a triangle exhaust the cyclic order on that line.  If two of the three
vertices have blue multiplicity two, the projective failed-Fano recognition
theorem applies.  This theorem is the common final step for the local
triangle and opposite-triangle exclusions in the ABKPR discharging proof.
-/

open Classical
noncomputable section

namespace Erdos735.ConcretePolarRecognition

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices
open ConcreteStrictEdgeCyclic

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B
abbrev Vertex (B : Finset Point) := ProjectiveBoundaryExtraction.Vertex B

/-- A literal three-edge cycle on one blue owner, with two double vertices,
forces the failed-Fano configuration. -/
theorem isFailedFano_of_three_literal_edges_two_double
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    {a b d : Point}
    (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
    (hd : d ∈ nonordinaryPoints P)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
    [Nonempty (Line (nonordinaryPoints P))]
    (pick : OtherLineChoice (Line (nonordinaryPoints P)))
    (s : Line (nonordinaryPoints P))
    (v₂ v₃ x : Vertex (nonordinaryPoints P))
    (hv₂v₃ : v₂ ≠ v₃) (hv₂x : v₂ ≠ x) (hv₃x : v₃ ≠ x)
    (e₂₃ e₃x ex₂ : StrictEdge (normals (nonordinaryPoints P)))
    (he₂₃ : e₂₃.1.1 = s) (he₃x : e₃x.1.1 = s) (hex₂ : ex₂.1.1 = s)
    (hpair₂₃ :
      (concreteEdgeVertices
        (span_normalVec_range_eq_top_of_noncollinear_triple
          (nonordinaryPoints P) ha hb hd hncol) e₂₃).image Prod.fst =
          {v₂, v₃})
    (hpair₃x :
      (concreteEdgeVertices
        (span_normalVec_range_eq_top_of_noncollinear_triple
          (nonordinaryPoints P) ha hb hd hncol) e₃x).image Prod.fst =
          {v₃, x})
    (hpairx₂ :
      (concreteEdgeVertices
        (span_normalVec_range_eq_top_of_noncollinear_triple
          (nonordinaryPoints P) ha hb hd hncol) ex₂).image Prod.fst =
          {x, v₂})
    (hv₂double : lineMultiplicity (OnLine (nonordinaryPoints P)) v₂ = 2)
    (hv₃double : lineMultiplicity (OnLine (nonordinaryPoints P)) v₃ = 2) :
    IsFailedFano P := by
  let B := nonordinaryPoints P
  let hs := span_normalVec_range_eq_top_of_noncollinear_triple
    (nonordinaryPoints P) ha hb hd hncol
  let c₂₃ := (strictEdgeLiftedCyclicEquiv B ha hb hd hncol pick e₂₃).1
  let c₃x := (strictEdgeLiftedCyclicEquiv B ha hb hd hncol pick e₃x).1
  let cx₂ := (strictEdgeLiftedCyclicEquiv B ha hb hd hncol pick ex₂).1
  have hc₂₃line : cyclicEdgeLine c₂₃ = s := by
    simpa [c₂₃, B] using
      (strictEdgeLiftedCyclicEquiv_line B ha hb hd hncol pick e₂₃).trans he₂₃
  have hc₃xline : cyclicEdgeLine c₃x = s := by
    simpa [c₃x, B] using
      (strictEdgeLiftedCyclicEquiv_line B ha hb hd hncol pick e₃x).trans he₃x
  have hcx₂line : cyclicEdgeLine cx₂ = s := by
    simpa [cx₂, B] using
      (strictEdgeLiftedCyclicEquiv_line B ha hb hd hncol pick ex₂).trans hex₂
  have hc₂₃pair : cyclicEdgeVertices
      (Finset.univ : Finset (Vertex B)) (OnLine B) (vertexCoord B) c₂₃ =
        {v₂, v₃} := by
    rw [show c₂₃ = (strictEdgeLiftedCyclicEquiv
      B ha hb hd hncol pick e₂₃).1 by rfl,
      strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
        B ha hb hd hncol pick hs e₂₃]
    exact hpair₂₃
  have hc₃xpair : cyclicEdgeVertices
      (Finset.univ : Finset (Vertex B)) (OnLine B) (vertexCoord B) c₃x =
        {v₃, x} := by
    rw [show c₃x = (strictEdgeLiftedCyclicEquiv
      B ha hb hd hncol pick e₃x).1 by rfl,
      strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
        B ha hb hd hncol pick hs e₃x]
    exact hpair₃x
  have hcx₂pair : cyclicEdgeVertices
      (Finset.univ : Finset (Vertex B)) (OnLine B) (vertexCoord B) cx₂ =
        {x, v₂} := by
    rw [show cx₂ = (strictEdgeLiftedCyclicEquiv
      B ha hb hd hncol pick ex₂).1 by rfl,
      strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
        B ha hb hd hncol pick hs ex₂]
    exact hpairx₂
  have hvertices :
      verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) s =
        {v₂, v₃, x} := by
    exact verticesOn_eq_triple_of_three_edges
      (Finset.univ : Finset (Vertex B)) (OnLine B) (vertexCoord B)
      (vertexCoord_injective B) hv₂v₃ hv₂x hv₃x
      c₂₃ c₃x cx₂ hc₂₃line hc₃xline hcx₂line
      hc₂₃pair hc₃xpair hcx₂pair
  have hv₂s : OnLine B v₂ s := by
    have hm : v₂ ∈ verticesOn (Finset.univ : Finset (Vertex B))
        (OnLine B) s := by
      rw [hvertices]
      simp
    exact ((mem_verticesOn _ _).mp hm).2
  have hv₃s : OnLine B v₃ s := by
    have hm : v₃ ∈ verticesOn (Finset.univ : Finset (Vertex B))
        (OnLine B) s := by
      rw [hvertices]
      simp
    exact ((mem_verticesOn _ _).mp hm).2
  have hthree :
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) s).card = 3 := by
    rw [hvertices]
    simp [hv₂v₃, hv₂x, hv₃x]
  exact BlueDirectionProjective.isFailedFano_of_three_projective_vertices_two_double
    hred hAcard s v₂ v₃ hv₂v₃ hv₂s hv₃s
      hv₂double hv₃double hthree

end Erdos735.ConcretePolarRecognition

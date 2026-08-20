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

import ErdosProblems.Erdos735.Discharging4ConcreteLevi

/-!
# What a failure of the Stage-4 Hall inequality already gives

This file separates the finite graph part of the evil--evil path argument
from its projective-geometric continuation part.  A Hall failure gives a
finite set of evil vertices with too few helping neighbors.  Choosing one
neighbor of each evil vertex and applying the pigeonhole principle produces
two distinct evils adjacent to a common helper.  In a concrete flank system
the geometric-flank equation then proves that their bad edges have the same
line owner.

The opposite-edge continuation used by Levi's theorem is intentionally not
claimed here: it is the additional geometric conclusion recorded by
`EvilPathGeometry` in `Discharging4ConcreteLevi`.
-/

namespace Erdos735

open scoped BigOperators
noncomputable section

namespace ABKPR.HelpingGraph

universe uH uE

variable {Help : Type uH} {Evil : Type uE}
variable [Fintype Help] [Fintype Evil]
variable [DecidableEq Help] [DecidableEq Evil]
variable (G : HelpingGraph Help Evil)

local instance : DecidableRel G.Adj := G.adjDecidable

/-- A fixed neighboring helper for every evil vertex. -/
noncomputable def chosenHelper (e : Evil) : Help :=
  Classical.choose (Finset.card_pos.mp (by
    have h := G.evil_degree_one_le e
    omega : 0 < (G.evilNeighbors e).card))

lemma chosenHelper_mem_evilNeighbors (e : Evil) :
    G.chosenHelper e ∈ G.evilNeighbors e :=
  Classical.choose_spec (Finset.card_pos.mp (by
    have h := G.evil_degree_one_le e
    omega : 0 < (G.evilNeighbors e).card))

lemma chosenHelper_adj (e : Evil) : G.Adj e (G.chosenHelper e) := by
  exact (Finset.mem_filter.mp (G.chosenHelper_mem_evilNeighbors e)).2

/-- A failed Hall inequality forces two distinct evil vertices to choose
the same helping neighbor.  This is the first segment of the alternating
evil--helping path. -/
theorem exists_distinct_with_common_chosenHelper
    (hHall : ¬ G.NoEvilEvilPath) :
    ∃ e₀ e₁ : Evil, e₀ ≠ e₁ ∧
      G.chosenHelper e₀ = G.chosenHelper e₁ := by
  classical
  simp only [NoEvilEvilPath, not_forall] at hHall
  obtain ⟨S, hS⟩ := hHall
  let N : Finset Help :=
    Finset.univ.filter fun h ↦ ∃ e ∈ S, G.Adj e h
  have hlt : N.card < S.card := by
    exact Nat.lt_of_not_ge hS
  let chooseOnS : S → Help := fun e ↦ G.chosenHelper e.1
  have hnotinj : ¬ Function.Injective chooseOnS := by
    intro hinj
    have hcardImage : (Finset.univ.image chooseOnS).card = Fintype.card S := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hsubset : Finset.univ.image chooseOnS ⊆ N := by
      intro h hh
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hh
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, e.1, e.2, G.chosenHelper_adj e.1⟩
    have hle := Finset.card_le_card hsubset
    have hScard : Fintype.card S = S.card := Fintype.card_coe S
    rw [hcardImage, hScard] at hle
    omega
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨e₀, e₁, heq, hne⟩ := hnotinj
  exact ⟨e₀.1, e₁.1, fun h ↦ hne (Subtype.ext h), heq⟩

/-- A convenient witness retaining the common helper and both adjacency
proofs. -/
structure HallFailureCollision where
  first : Evil
  second : Evil
  first_ne_second : first ≠ second
  commonHelper : Help
  first_adj : G.Adj first commonHelper
  second_adj : G.Adj second commonHelper

/-- The pigeonhole collision produced by a Hall failure is nonempty.  The
`Nonempty` wrapper keeps the proof in `Prop`; the following definition makes
the harmless finite choice. -/
theorem hallFailureCollision_nonempty (hHall : ¬ G.NoEvilEvilPath) :
    Nonempty (HallFailureCollision G) := by
  obtain ⟨e₀, e₁, hne, heq⟩ :=
    G.exists_distinct_with_common_chosenHelper hHall
  exact ⟨
    { first := e₀
      second := e₁
      first_ne_second := hne
      commonHelper := G.chosenHelper e₀
      first_adj := G.chosenHelper_adj e₀
      second_adj := heq ▸ G.chosenHelper_adj e₁ }⟩

/-- Package the pigeonhole collision produced by a Hall failure. -/
noncomputable def hallFailureCollision (hHall : ¬ G.NoEvilEvilPath) :
    HallFailureCollision G :=
  Classical.choice (G.hallFailureCollision_nonempty hHall)

end ABKPR.HelpingGraph

namespace ABKPR.Data

universe uV uEd uF uL

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C}
variable {Line : Type uL} [Fintype Line] [DecidableEq Line]
variable (L : A.FlankSystem Line)

/-- One alternating evil--helper--evil step. -/
def EvilLinked (e₀ e₁ : A.EvilFace) : Prop :=
  ∃ h : A.HelpingPair, L.Adj e₀ h ∧ L.Adj e₁ h

/-- An adjacency in the concrete helping graph identifies the helper's
designated edge line with the evil's bad-edge line. -/
theorem helperLine_eq_badEdgeLine_of_adj
    {e : A.EvilFace} {h : A.HelpingPair} (hadj : L.Adj e h) :
    L.edgeLine (A.boundaryEdge h.face h.index) =
      L.edgeLine (A.boundaryEdge e.1 (A.evilIndex e)) := by
  obtain ⟨side, hside⟩ := hadj
  exact (L.evilFlank_geometric e side h hside).2

/-- The bad-edge owner is constant across one alternating step. -/
theorem badEdgeLine_eq_of_evilLinked
    {e₀ e₁ : A.EvilFace} (hlink : EvilLinked L e₀ e₁) :
    L.edgeLine (A.boundaryEdge e₀.1 (A.evilIndex e₀)) =
      L.edgeLine (A.boundaryEdge e₁.1 (A.evilIndex e₁)) := by
  obtain ⟨h, h₀, h₁⟩ := hlink
  exact (helperLine_eq_badEdgeLine_of_adj L h₀).symm.trans
    (helperLine_eq_badEdgeLine_of_adj L h₁)

/-- The common path-line owner propagates along an arbitrary finite
alternating chain. -/
theorem badEdgeLine_eq_of_reflTransGen_evilLinked
    {e₀ e₁ : A.EvilFace}
    (hpath : Relation.ReflTransGen (EvilLinked L) e₀ e₁) :
    L.edgeLine (A.boundaryEdge e₀.1 (A.evilIndex e₀)) =
      L.edgeLine (A.boundaryEdge e₁.1 (A.evilIndex e₁)) := by
  induction hpath with
  | refl => rfl
  | tail hpath hstep ih =>
      exact ih.trans (badEdgeLine_eq_of_evilLinked L hstep)

/-- The two evils in the Hall collision have the same bad-edge line owner.
The equality follows solely from the two geometric-flank equations through
their common helper. -/
theorem hallFailureCollision_badEdgeLine_eq
    (W : ABKPR.HelpingGraph.HallFailureCollision L.toHelpingGraph) :
    L.edgeLine (A.boundaryEdge W.first.1 (A.evilIndex W.first)) =
      L.edgeLine (A.boundaryEdge W.second.1 (A.evilIndex W.second)) := by
  exact badEdgeLine_eq_of_evilLinked L
    ⟨W.commonHelper, W.first_adj, W.second_adj⟩

/-- Concrete line-owner form of the first segment forced by a Hall
failure. -/
theorem exists_distinct_evil_common_helper_same_badEdgeLine
    (hHall : ¬ L.toHelpingGraph.NoEvilEvilPath) :
    ∃ e₀ e₁ : A.EvilFace, ∃ h : A.HelpingPair,
      e₀ ≠ e₁ ∧ L.Adj e₀ h ∧ L.Adj e₁ h ∧
        L.edgeLine (A.boundaryEdge e₀.1 (A.evilIndex e₀)) =
          L.edgeLine (A.boundaryEdge e₁.1 (A.evilIndex e₁)) := by
  let W := L.toHelpingGraph.hallFailureCollision hHall
  exact ⟨W.first, W.second, W.commonHelper, W.first_ne_second,
    W.first_adj, W.second_adj, hallFailureCollision_badEdgeLine_eq L W⟩

end ABKPR.Data

end
end Erdos735

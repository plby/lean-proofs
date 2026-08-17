/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos58.Basic
import ErdosProblems.Erdos58.Bipartite
import ErdosProblems.Erdos58.Critical
import ErdosProblems.Erdos58.DFSUpper

/-!
# Reduction of Erdős Problem 58 to the structural theorem

This file contains the vertex-critical endgame of the proof.  Its only
graph-theoretic input is the structural theorem of Gyárfás: a finite
vertex-two-connected graph of minimum degree at least `2 * j + 1`, having
exactly `j > 0` odd cycle lengths, is isomorphic to `K_(2*j+2)`.

The structural theorem is an explicit higher-order hypothesis here.  This
makes the reduction independently checkable while the geometric proof of the
structural theorem is developed in a separate module.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

noncomputable section

universe u

/-- The precise interface supplied by the Gyárfás structural theorem. -/
abbrev StructuralTheorem :=
  ∀ {X : Type u} [Fintype X] [DecidableEq X]
      (H : SimpleGraph X) [DecidableRel H.Adj] (j : ℕ),
    0 < j →
    Critical.VertexTwoConnected H →
    (∀ v : X, 2 * j + 1 ≤ H.degree v) →
    (oddCycleLengths H).ncard = j →
    Nonempty (H ≃g SimpleGraph.completeGraph (Fin (2 * j + 2)))

/-- On a finite graph, the extended-cardinality hypothesis is exactly the
ordinary natural-number bound needed by the structural theorem. -/
lemma ncard_oddCycleLengths_le_of_encard_le {V : Type u} [Finite V]
    (G : SimpleGraph V) {k : ℕ}
    (hk : (oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    (oddCycleLengths G).ncard ≤ k := by
  have hfinite := oddCycleLengths_finite G
  rw [← hfinite.cast_ncard_eq] at hk
  exact_mod_cast hk

/-- A copy of `K_n` gives the corresponding lower bound on chromatic
number. -/
lemma completeGraph_card_le_chromaticNumber_of_isContained
    {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (hcopy : SimpleGraph.completeGraph (Fin n) ⊑ G) :
    (n : ℕ∞) ≤ G.chromaticNumber := by
  obtain ⟨f⟩ := hcopy
  have hmono := SimpleGraph.chromaticNumber_mono_of_hom f.toHom
  simpa [SimpleGraph.chromaticNumber_top] using hmono

/-- The DFS module's finite-set representation is extensionally the same as
the public set-valued representation of odd cycle lengths. -/
lemma dfsUpper_oddCycleLengths_card_eq_ncard {V : Type u} [Finite V]
    (G : SimpleGraph V) :
    (DFSUpper.oddCycleLengths G).card = (oddCycleLengths G).ncard := by
  classical
  have hfinite := oddCycleLengths_finite G
  have heq : DFSUpper.oddCycleLengths G = hfinite.toFinset := by
    ext n
    simp only [DFSUpper.mem_oddCycleLengths_iff, Set.Finite.mem_toFinset,
      mem_oddCycleLengths]
  rw [heq]
  exact (Set.ncard_eq_toFinset_card (oddCycleLengths G) hfinite).symm

/-- The elementary DFS upper bound, stated using the public odd-cycle-length
set. -/
lemma colorable_two_mul_add_two_of_ncard_le {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ)
    (hcount : (oddCycleLengths G).ncard ≤ k) :
    G.Colorable (2 * k + 2) := by
  apply DFSUpper.colorable_of_oddCycleLengths_card_le G k
  rwa [dfsUpper_oddCycleLengths_card_eq_ncard]

/-- The sharp critical reduction: if `2*k+1` colors do not suffice, the
ambient graph contains `K_(2*k+2)`. -/
lemma completeGraph_isContained_of_not_colorable_of_structural
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hkpos : 0 < k)
    (hcount : (oddCycleLengths G).ncard ≤ k)
    (hstruct : StructuralTheorem.{u})
    (hnot : ¬G.Colorable (2 * k + 1)) :
    SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G := by
  obtain ⟨W, hdegree, htwo⟩ :=
    Critical.exists_vertexTwoConnected_witness (G := G) (n := 2 * k + 1)
      (by omega) hnot
  let _ : Fintype (Critical.Carrier G W) := Critical.instSub W.S
  let J : SimpleGraph (Critical.Carrier G W) := Critical.H G W
  let j : ℕ := (oddCycleLengths J).ncard
  have hjk : j ≤ k := by
    have hmono := ncard_oddCycleLengths_induce_le G (fun v : V ↦ v ∈ W.S)
    have hmono' : (oddCycleLengths J).ncard ≤
        (oddCycleLengths G).ncard := by
      simpa [J, Critical.H] using hmono
    exact hmono'.trans hcount
  have hnotlt : ¬j < k := by
    intro hjlt
    have hJcolor : J.Colorable (2 * j + 2) :=
      colorable_two_mul_add_two_of_ncard_le J j (by simp [j])
    have hcriticalColor : J.Colorable (2 * k + 1) :=
      SimpleGraph.Colorable.mono (by omega) hJcolor
    exact W.not_colorable (by simpa [J] using hcriticalColor)
  have hjeq : j = k := Nat.le_antisymm hjk (Nat.le_of_not_gt hnotlt)
  change (oddCycleLengths J).ncard = k at hjeq
  obtain ⟨e⟩ := hstruct J k hkpos (by simpa [J] using htwo)
    (by simpa [J] using hdegree) hjeq
  exact e.isContained'.trans
    (SimpleGraph.Embedding.induce (G := G) (fun v : V ↦ v ∈ W.S)).toCopy.isContained

/-- Erdős Problem 58, reduced to the Gyárfás structural theorem.

The public formulation uses extended cardinality and only a `Finite` instance
on the vertex type.  The conclusion states both the sharp chromatic bound and
the exact equality characterization by containment of a complete graph.
-/
theorem erdos_58_from_structural {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ)
    (hstruct : StructuralTheorem.{u})
    (hk : (oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (G.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let hcount : (oddCycleLengths G).ncard ≤ k :=
    ncard_oddCycleLengths_le_of_encard_le G hk
  by_cases hkzero : k = 0
  · subst k
    have hempty : oddCycleLengths G = ∅ := by
      apply (Set.ncard_eq_zero (oddCycleLengths_finite G)).mp
      omega
    have hcolor : G.Colorable 2 :=
      colorable_two_of_oddCycleLengths_eq_empty hempty
    refine ⟨?_, ?_⟩
    · simpa using hcolor.chromaticNumber_le
    · simpa using
        (chromaticNumber_eq_two_iff_completeGraph_two_isContained
          (G := G) hempty)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    have hcolor : G.Colorable (2 * k + 2) :=
      colorable_two_mul_add_two_of_ncard_le G k hcount
    have hupper : G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) :=
      hcolor.chromaticNumber_le
    refine ⟨hupper, ?_⟩
    constructor
    · intro hchi
      have hnot : ¬G.Colorable (2 * k + 1) := by
        intro hsmall
        have hle := hsmall.chromaticNumber_le
        rw [hchi] at hle
        have hfalse : 2 * k + 2 ≤ 2 * k + 1 := by
          exact_mod_cast hle
        omega
      exact completeGraph_isContained_of_not_colorable_of_structural
        G k hkpos hcount hstruct hnot
    · intro hcopy
      exact le_antisymm hupper
        (completeGraph_card_le_chromaticNumber_of_isContained hcopy)

end

end Erdos58

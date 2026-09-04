/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos58.Basic
import ErdosProblems.Erdos58.Critical
import ErdosProblems.Erdos58.Structural.ConnectivityBridge
import ErdosProblems.Erdos58.Structural.CaseConclusion
import ErdosProblems.Erdos58.Structural.IndependentGap
import ErdosProblems.Erdos58.Structural.K1Boundary
import ErdosProblems.Erdos58.Structural.LongestCycle
import ErdosProblems.Erdos58.Structural.SingletonFan
import ErdosProblems.Erdos58.Structural.SpliceConstruction
import ErdosProblems.Erdos58.Structural.Setup
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# The structural core of Erdős Problem 58

This file supplies cardinality endpoints used by the geometric proof of
Gyárfás's structural theorem.
-/

namespace Erdos58.Structural

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A positive lower bound of the form occurring in the structural theorem
forces a vertex-two-connected graph to have at least three vertices. -/
theorem card_three_le_of_minDegree {j : ℕ} (hj : 0 < j)
    [Nonempty V]
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v) :
    3 ≤ Fintype.card V := by
  classical
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have hle := hdegree v
  omega

/-- Once completeness is known, the minimum-degree hypothesis and the exact
odd-cycle count force the sharp number of vertices.  This arithmetic endpoint
is useful independently of the geometric part of Gyárfás's theorem. -/
theorem card_eq_two_mul_add_two_of_complete {j : ℕ} (hj : 0 < j)
    (hcomplete : G = SimpleGraph.completeGraph V)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    Fintype.card V = 2 * j + 2 := by
  classical
  have hV : Nonempty V := by
    by_contra hV
    have : IsEmpty V := not_nonempty_iff.mp hV
    have hempty : oddCycleLengths G = ∅ := by
      ext n
      simp [oddCycleLengths]
    rw [hempty] at hodd
    simp at hodd
    omega
  let : Nonempty V := hV
  have hcardLower : 2 * j + 2 ≤ Fintype.card V := by
    let v : V := Classical.choice inferInstance
    have hlt := G.degree_lt_card_verts v
    have hle := hdegree v
    omega
  subst G
  -- Transport the complete graph to its cardinality-sized standard model,
  -- then use the exact computation in `Basic`.
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let ge : SimpleGraph.completeGraph V ≃g
      SimpleGraph.completeGraph (Fin (Fintype.card V)) :=
    SimpleGraph.Iso.completeGraph e
  have hsets :
      oddCycleLengths (SimpleGraph.completeGraph V) =
        oddCycleLengths (SimpleGraph.completeGraph (Fin (Fintype.card V))) := by
    apply Set.Subset.antisymm
    · exact oddCycleLengths_mono_hom ge.toHom ge.injective
    · exact oddCycleLengths_mono_hom ge.symm.toHom ge.symm.injective
  rw [hsets] at hodd
  apply Nat.le_antisymm
  · by_contra hnot
    have hcardBig : 2 * j + 3 ≤ Fintype.card V := by omega
    let base : Set ℕ :=
      oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * j + 2)))
    let extra : ℕ := 2 * j + 3
    have hbaseFinite : base.Finite := oddCycleLengths_finite _
    have hbaseCard : base.ncard = j := by
      exact ncard_oddCycleLengths_completeGraph_two_mul_add_two j
    have hextraNot : extra ∉ base := by
      change extra ∉
        oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * j + 2)))
      rw [oddCycleLengths_completeGraph]
      simp [extra]
    have hsub : insert extra base ⊆
        oddCycleLengths
          (SimpleGraph.completeGraph (Fin (Fintype.card V))) := by
      rw [oddCycleLengths_completeGraph]
      intro n hn
      rcases hn with (rfl | hn)
      · refine ⟨?_, ?_⟩
        · exact ⟨j + 1, by omega⟩
        · exact ⟨by omega, hcardBig⟩
      · change n ∈
          oddCycleLengths (SimpleGraph.completeGraph (Fin (2 * j + 2))) at hn
        rw [oddCycleLengths_completeGraph] at hn
        exact ⟨hn.1, hn.2.1, hn.2.2.trans hcardLower⟩
    have hcount : j + 1 ≤
        (oddCycleLengths
          (SimpleGraph.completeGraph (Fin (Fintype.card V)))).ncard := by
      have := Set.ncard_le_ncard hsub (oddCycleLengths_finite _)
      rw [Set.ncard_insert_of_notMem hextraNot hbaseFinite, hbaseCard] at this
      exact this
    omega
  · exact hcardLower

/-- The independent-exterior branch of Gyárfás's structural theorem,
including both the complete-graph and sharp-cardinality conclusions. -/
theorem complete_and_card_of_independentExterior {j : ℕ} (hj : 0 < j)
    (hG : TwoConnected G) (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    G = SimpleGraph.completeGraph V ∧ Fintype.card V = 2 * j + 2 := by
  have hcomplete : G = SimpleGraph.completeGraph V :=
    IndependentGap.independentExteriorForcesComplete
      hj hG C hind hdegree hodd
  exact ⟨hcomplete,
    card_eq_two_mul_add_two_of_complete G hj hcomplete hdegree hodd⟩

/-- The independent-exterior branch in the exact isomorphism form required
by `MainReduction.StructuralTheorem`. -/
theorem iso_completeGraph_of_independentExterior {j : ℕ} (hj : 0 < j)
    (hG : TwoConnected G) (C : LongestOddCycle G)
    (hind : HasIndependentExterior C)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
  obtain ⟨hcomplete, hcard⟩ :=
    complete_and_card_of_independentExterior G hj hG C hind hdegree hodd
  let e : V ≃ Fin (2 * j + 2) := Fintype.equivFinOfCardEq hcard
  subst G
  exact ⟨SimpleGraph.Iso.completeGraph e⟩

/-- Gyárfás's structural theorem in the connectivity interface used by the
longest-cycle proof. -/
theorem gyarfas_structural_twoConnected {j : ℕ} (hj : 0 < j)
    (hG : TwoConnected G)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard = j) :
    Nonempty (G ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
  obtain ⟨C⟩ := exists_longestOddCycle hj hodd
  rcases independentExterior_or_exists_positive_longestExteriorPath
      hj C hdegree hodd.le with hind | ⟨P, hpos⟩
  · exact iso_completeGraph_of_independentExterior G hj hG C hind hdegree hodd
  · exact (CaseConclusion.nonIndependent_impossible
      hG hj P hpos hdegree hodd).elim

/-- **Gyárfás's structural theorem**, in the exact interface consumed by
`MainReduction.StructuralTheorem`: a finite vertex-two-connected graph with
minimum degree at least `2*j+1` and exactly `j>0` odd cycle lengths is the
complete graph on `2*j+2` vertices. -/
theorem gyarfas_structural {X : Type u} [Fintype X] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (j : ℕ) (hj : 0 < j)
    (hconn : Critical.VertexTwoConnected H)
    (hdegree : ∀ v : X, 2 * j + 1 ≤ H.degree v)
    (hodd : (oddCycleLengths H).ncard = j) :
    Nonempty (H ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
  have hH : TwoConnected H :=
    twoConnected_of_vertexTwoConnected_minDegree H hj hconn hdegree
  exact gyarfas_structural_twoConnected H hj hH hdegree hodd

end Erdos58.Structural

#print axioms Erdos58.Structural.gyarfas_structural

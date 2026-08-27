/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationReserveCandidates

/-!
# Simultaneous reserve-wedge candidate supply

The fixed-edge Chernoff estimate can be union-bounded over every internal
leftover edge.  No independence between different edges is needed.  This file
performs that finite extraction and then specializes it to the extension sets
provided by iteration typicality.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- If the sum of the fixed-edge exponential errors is below one, one reserve
realization leaves more than the prescribed cutoff of wedge candidates for
every indexed edge. -/
theorem exists_reserve_realization_with_all_wedge_supplies
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) (U : Finset V)
    (E : Finset J) (u v : J → V) (S : J → Finset V)
    (a : J → ℕ) (r : ℝ≥0) (hr : r ≤ 1)
    (huv : ∀ j ∈ E, u j ≠ v j)
    (hu : ∀ j ∈ E, u j ∉ U) (hv : ∀ j ∈ E, v j ∉ U)
    (hSU : ∀ j ∈ E, S j ⊆ U)
    (hadj : ∀ j ∈ E, ∀ w ∈ S j,
      G.Adj (u j) w ∧ G.Adj (v j) w)
    (ha : ∀ j ∈ E,
      (a j : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * (S j).card / 4)
    (hsmall :
      ∑ j ∈ E, Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) < 1) :
    ∃ ω : Sym2 V → Bool, ∀ j ∈ E,
      a j <
        (activeReserveWedgeVertices G U (S j) (u j) (v j) ω).card := by
  let L := reserveEdgeLaw G U r hr
  let Bad : J → (Sym2 V → Bool) → Prop := fun j ω ↦
    (activeReserveWedgeVertices G U (S j) (u j) (v j) ω).card ≤ a j
  have htail : ∀ j ∈ E,
      (L.probability (Bad j) : ℝ) ≤
        Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) := by
    intro j hj
    exact reserveEdgeLaw_probability_activeReserveWedgeVertices_card_le_le_exp
      G U (S j) (u j) (v j) r hr (huv j hj) (hu j hj) (hv j hj)
      (hSU j hj) (hadj j hj) (a j) (ha j hj)
  have hsumReal :
      ∑ j ∈ E, (L.probability (Bad j) : ℝ) < 1 := by
    refine lt_of_le_of_lt (Finset.sum_le_sum ?_) hsmall
    intro j hj
    exact htail j hj
  have hsum : ∑ j ∈ E, L.probability (Bad j) < 1 := by
    exact_mod_cast hsumReal
  obtain ⟨ω, hω⟩ := L.exists_avoiding_of_sum_probability_lt_one E Bad hsum
  refine ⟨ω, ?_⟩
  intro j hj
  have := hω j hj
  simp only [Bad] at this
  omega

/-- Specialization to the one-edge extension sets used by the master
iteration. -/
theorem exists_reserve_realization_with_extension_supplies
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    {ell : ℕ} {W : Vortex V ell}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell)
    (E : Finset J) (u v : J → V)
    (huv : ∀ j ∈ E, u j ≠ v j)
    (huInner : ∀ j ∈ E, u j ∉ W.U i.succ)
    (hvInner : ∀ j ∈ E, v j ∉ W.U i.succ)
    (r : ℝ≥0) (hr : r ≤ 1) (a : J → ℕ)
    (ha : ∀ j ∈ E,
      let S := iterationExtensionVertices A
        (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
      (a j : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * S.card / 4)
    (hsmall :
      ∑ j ∈ E,
        (let S := iterationExtensionVertices A
            (SimpleGraph.edge (u j) (v j)) (W.U i.succ);
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * S.card) / 4)) < 1) :
    ∃ ω : Sym2 V → Bool, ∀ j ∈ E,
      let S := iterationExtensionVertices A
        (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
      a j <
        (activeReserveWedgeVertices G (W.U i.succ) S
          (u j) (v j) ω).card := by
  let S : J → Finset V := fun j ↦
    iterationExtensionVertices A
      (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
  have hSU : ∀ j ∈ E, S j ⊆ W.U i.succ := by
    intro j _hj
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
  have hadj : ∀ j ∈ E, ∀ w ∈ S j,
      G.Adj (u j) w ∧ G.Adj (v j) w := by
    intro j hj w hw
    have hwInner := hSU j hj hw
    apply iterationExtensionVertices_edge_adjacencies (huv j hj)
    · intro huw
      subst w
      exact huInner j hj hwInner
    · intro hvw
      subst w
      exact hvInner j hj hwInner
    · exact htri
    · exact hw
  simpa only [S] using
    (exists_reserve_realization_with_all_wedge_supplies
      G (W.U i.succ) E u v S a r hr huv huInner hvInner hSU hadj ha hsmall)

/-- A common deterministic lower bound on all one-edge extension counts
turns iteration typicality into a uniform all-edge reserve realization. -/
theorem IsIterationTypical.exists_reserve_realization_with_internal_supplies
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (E : Finset J) (u v : J → V)
    (huv : ∀ j ∈ E, u j ≠ v j)
    (huOuter : ∀ j ∈ E, u j ∈ W.U i.castSucc)
    (hvOuter : ∀ j ∈ E, v j ∈ W.U i.castSucc)
    (huInner : ∀ j ∈ E, u j ∉ W.U i.succ)
    (hvInner : ∀ j ∈ E, v j ∉ W.U i.succ)
    (huvG : ∀ j ∈ E, G.Adj (u j) (v j))
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (a : J → ℕ)
    (ha : ∀ j ∈ E,
      (a j : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : (E.card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1) :
    ∃ ω : Sym2 V → Bool, ∀ j ∈ E,
      let S := iterationExtensionVertices A
        (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
      a j <
        (activeReserveWedgeVertices G (W.U i.succ) S
          (u j) (v j) ω).card := by
  let S : J → Finset V := fun j ↦
    iterationExtensionVertices A
      (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
  have hwindow : ∀ j ∈ E,
      WithinMultiplicativeError ξ ((S j).card : ℝ≥0)
        (p ^ 2 * eta * (W.U i.succ).card) := by
    intro j hj
    exact htyp.edge_extension_window i hstage (huv j hj)
      (huOuter j hj) (hvOuter j hj) (huvG j hj) hh
  have hmS : ∀ j ∈ E, m ≤ (S j).card := by
    intro j hj
    exact_mod_cast hm.trans (hwindow j hj).1
  have haS : ∀ j ∈ E,
      (a j : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * (S j).card / 4 := by
    intro j hj
    have hmSR : (m : ℝ) ≤ ((S j).card : ℝ) := by exact_mod_cast hmS j hj
    calc
      (a j : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4 := ha j hj
      _ ≤ ((r ^ 2 : ℝ≥0) : ℝ) * (S j).card / 4 := by
        gcongr
  have hsmallS :
      ∑ j ∈ E,
        Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) < 1 := by
    calc
      ∑ j ∈ E,
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) ≤
          ∑ _j ∈ E,
            Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by
        apply sum_le_sum
        intro j hj
        rw [Real.exp_le_exp]
        have hmSR : (m : ℝ) ≤ ((S j).card : ℝ) := by
          exact_mod_cast hmS j hj
        have hr2 : 0 ≤ ((r ^ 2 : ℝ≥0) : ℝ) := by positivity
        nlinarith
      _ = (E.card : ℝ) *
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by simp
      _ < 1 := hsmall
  simpa only [S] using
    (exists_reserve_realization_with_extension_supplies
      htri i E u v huv huInner hvInner r hr a haS hsmallS)

end

end Erdos207

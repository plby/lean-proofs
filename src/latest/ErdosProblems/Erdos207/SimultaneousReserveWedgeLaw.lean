/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousReserveWedgeCandidates
import ErdosProblems.Erdos207.FiniteConditioning

/-!
# Conditioning the reserve law on simultaneous wedge supply

The deterministic reserve extraction used by the internal-edge cover is not
enough for the master probability law: the selected reserve must remain a
random object, since later link triangles obtain two independent reserve-edge
factors from it.  Here the same Chernoff union bound is retained as a strict
probability estimate.  It shows that the event on which every internal edge
has its required wedge supply has positive probability, so the reserve law
can be conditioned on that event without losing its support information.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Every indexed edge has strictly more than its prescribed number of
active reserve wedges. -/
def AllReserveWedgeSupplies
    {V J : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V)
    (E : Finset J) (u v : J → V) (S : J → Finset V)
    (a : J → ℕ) (ω : Sym2 V → Bool) : Prop :=
  ∀ j ∈ E, a j <
    (activeReserveWedgeVertices G U (S j) (u j) (v j) ω).card

/-- The Chernoff estimates for individual wedge supplies union-bound to an
upper bound on the probability that at least one supply fails. -/
theorem reserveEdgeLaw_probability_not_allReserveWedgeSupplies_le
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
      (a j : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * (S j).card / 4) :
    (((reserveEdgeLaw G U r hr).probability
        (fun ω ↦ ¬ AllReserveWedgeSupplies G U E u v S a ω) : ℝ)) ≤
      ∑ j ∈ E,
        Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) := by
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
  have hnot : (fun ω ↦ ¬ AllReserveWedgeSupplies G U E u v S a ω) =
      (fun ω ↦ ∃ j ∈ E, Bad j ω) := by
    funext ω
    apply propext
    simp only [AllReserveWedgeSupplies, Bad, not_forall, not_lt]
    constructor
    · rintro ⟨j, hj, hbad⟩
      exact ⟨j, hj, hbad⟩
    · rintro ⟨j, hj, hbad⟩
      exact ⟨j, hj, hbad⟩
  rw [hnot]
  calc
    (L.probability (fun ω ↦ ∃ j ∈ E, Bad j ω) : ℝ) ≤
        (∑ j ∈ E, L.probability (Bad j) : ℝ) := by
      exact_mod_cast L.probability_exists_le E Bad
    _ ≤ ∑ j ∈ E,
        Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) := by
      apply sum_le_sum
      intro j hj
      exact htail j hj

/-- A strict union bound makes the simultaneous good-supply event have
positive probability under the unconditioned reserve-edge law. -/
theorem reserveEdgeLaw_probability_allReserveWedgeSupplies_pos
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
      ∑ j ∈ E, Real.exp
        (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) < 1) :
    0 < (reserveEdgeLaw G U r hr).probability
      (AllReserveWedgeSupplies G U E u v S a) := by
  let L := reserveEdgeLaw G U r hr
  have hbadReal :
      ((L.probability
        (fun ω ↦ ¬ AllReserveWedgeSupplies G U E u v S a ω) : ℝ)) < 1 :=
    (reserveEdgeLaw_probability_not_allReserveWedgeSupplies_le
      G U E u v S a r hr huv hu hv hSU hadj ha).trans_lt hsmall
  have hbad : L.probability
      (fun ω ↦ ¬ AllReserveWedgeSupplies G U E u v S a ω) < 1 := by
    exact_mod_cast hbadReal
  rw [L.probability_not] at hbad
  by_contra hzero
  have heq : L.probability (AllReserveWedgeSupplies G U E u v S a) = 0 :=
    le_antisymm (not_lt.mp hzero) zero_le
  simp only [heq, tsub_zero] at hbad
  exact (lt_irrefl 1 hbad)

/-- The reserve law conditioned on simultaneous wedge supply is supported
entirely on good reserve outcomes. -/
theorem conditionedReserveEdgeLaw_supported_allReserveWedgeSupplies
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (G : SimpleGraph V) (U : Finset V)
    (E : Finset J) (u v : J → V) (S : J → Finset V)
    (a : J → ℕ) (r : ℝ≥0) (hr : r ≤ 1)
    (hpos : 0 < (reserveEdgeLaw G U r hr).probability
      (AllReserveWedgeSupplies G U E u v S a)) :
    ((reserveEdgeLaw G U r hr).conditionOn
      (AllReserveWedgeSupplies G U E u v S a) hpos).SupportedOn
        (AllReserveWedgeSupplies G U E u v S a) :=
  FiniteLaw.conditionOn_supported _ _ hpos

/-- Iteration typicality and a common deterministic extension-count floor
give a positive-probability simultaneous reserve-supply event for an indexed
family of internal edges. -/
theorem IsIterationTypical.reserveEdgeLaw_probability_internalSupplies_pos
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
    let S : J → Finset V := fun j ↦
      iterationExtensionVertices A
        (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
    0 < (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (AllReserveWedgeSupplies G (W.U i.succ) E u v S a) := by
  dsimp only
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
    have hmSR : (m : ℝ) ≤ ((S j).card : ℝ) := by
      exact_mod_cast hmS j hj
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
  exact reserveEdgeLaw_probability_allReserveWedgeSupplies_pos
    G (W.U i.succ) E u v S a r hr huv huInner hvInner hSU hadj haS hsmallS

end

end Erdos207

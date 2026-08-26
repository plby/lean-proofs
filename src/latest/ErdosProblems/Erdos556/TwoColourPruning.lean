import ErdosProblems.Erdos556.TwoColourCoreOrder
import ErdosProblems.Erdos556.StoppedPruning
import ErdosProblems.Erdos556.NoLongCycles

/-!
# Controlled core extraction in two-colour long-cycle counterexamples
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_uniform_two_colour_pruned_core (D B : ℕ) (hD : 0 < D) (hB : 0 < B) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L b : ℕ),
      N₀ ≤ L → 2 ≤ L → L + b + 1 ≤ Fintype.card V →
      Fintype.card V ≤ D * L → Fintype.card V ≤ B * b →
      NoLongCycles G (2 * L) → NoLongCycles Gᶜ (2 * L) →
      ∃ S : Finset V, L + b + 1 ≤ S.card ∧ S.card ≤ 2 * L + b ∧
        (G.edgeFinset.card : ℝ) - (L + b : ℕ) * Fintype.card V ≤
          ((G.induce (S : Set V)).edgeFinset.card : ℝ) - (L + b : ℕ) * S.card := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_two_colour_core_order_bound D B hD hB
  refine ⟨N₀, ?_⟩
  intro V _ _ G _ L b hLlarge hL hfloor hscale hbudget hG hGc
  classical
  obtain ⟨S, hSfloor, hSenergy, hSstop⟩ := exists_induced_core_of_card_floor G
    ((L + b : ℕ) : ℝ) (L + b + 1) hfloor
  refine ⟨S, hSfloor, ?_, hSenergy⟩
  rcases hSstop with hstop | hmin
  · omega
  · have hSc : Fintype.card (S : Set V) = S.card := by
      calc
        Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
        _ = S.card := Set.ncard_coe_finset S
    have hScN := card_le_univ S
    have hdegree (v : (S : Set V)) : L + b ≤ (G.induce (S : Set V)).degree v := by
      have h : L + b < (G.induce (S : Set V)).degree v := by exact_mod_cast hmin v
      exact h.le
    have hshort := hG.induce (S : Set V)
    have hcomp := (hGc.complement_induce (S : Set V)).not_cycle (2 * L) (by omega) le_rfl
    have hbound := hN₀ (G.induce (S : Set V)) L b (by omega) hL (by omega) (by omega)
      hdegree hcomp hshort
    omega

#print axioms exists_uniform_two_colour_pruned_core

end Erdos556

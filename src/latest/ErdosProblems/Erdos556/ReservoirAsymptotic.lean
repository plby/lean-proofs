import ErdosProblems.Erdos556.Reservoir
import ErdosProblems.Erdos556.SamplingAsymptotic

/-!
# Uniform reservoirs for sufficiently large graphs

Fixed reciprocal degree and deletion bounds give a fixed path-length bound.
The threshold is uniform over all graphs and all choices of the integer
degree and deletion parameters satisfying those bounds.
-/

namespace Erdos556

open SimpleGraph Filter

theorem exists_uniform_connecting_reservoir (D B a : ℕ) (hD : 0 < D) (hB : 0 < B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (b d : ℕ),
      N₀ ≤ Fintype.card V → ConnectedAfterDeleting G b →
      (∀ w, d + b ≤ G.degree w) → Fintype.card V ≤ D * d →
      Fintype.card V ≤ B * b →
      ∃ R : Finset V, (R.card : ℝ) ≤ 2 * q * Fintype.card V ∧
        ∀ u v S, S.card ≤ a → ShortConnection G (3 * D) u v (R \ S) := by
  let L := 3 * D
  let K := B * ((a + 1) * L)
  have hL : 0 < L := by dsimp [L]; omega
  have hK : 0 < K := Nat.mul_pos hB (Nat.mul_pos (by omega) hL)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_reservoir_failure q hq0 hq1 L K a hK)
  refine ⟨max N₁ 1, ?_⟩
  intro V _ _ G _ b d hN hc hg hd hb
  have hV : 0 < Fintype.card V := by omega
  have hdpos : 0 < d := by nlinarith
  let m := Fintype.card V / K
  have hbudget : ((a + 1) * m) * L ≤ b := by
    have hmul : B * (((a + 1) * m) * L) ≤ B * b := by
      calc
        B * (((a + 1) * m) * L) = m * K := by dsimp [K]; ring
        _ ≤ Fintype.card V := Nat.div_mul_le_self _ _
        _ ≤ B * b := hb
    nlinarith
  have hdiam : 3 * Fintype.card V ≤ d * L := by dsimp [L]; nlinarith
  exact exists_connecting_reservoir G b d L m a hc hdpos hg hdiam hbudget q hq0 hq1
    (hN₁ _ (by omega)) hV

#print axioms exists_uniform_connecting_reservoir

end Erdos556

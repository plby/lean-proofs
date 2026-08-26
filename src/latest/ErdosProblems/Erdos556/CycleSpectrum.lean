import ErdosProblems.Erdos556.CycleReservoirSelection
import ErdosProblems.Erdos556.ReservoirCycleSpectrum

/-!
# The dense-graph cycle-spectrum theorem

For each fixed inverse minimum-degree scale, there are uniform constants
such that every sufficiently long cycle supplies every shorter cycle of
the same parity, apart from a bounded interval at either end. Reservoir
selection, bounded shortening, and exact closing are all proved in the
supporting files.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_dense_cycle_spectrum (D : ℕ) (hD : 0 < D) :
    ∃ N₀ K : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ D * d → (∀ v, d ≤ G.degree v) →
      ∀ (z : V) (c : G.Walk z z), c.IsCycle →
      ∀ n : ℕ, K ≤ n → n + K ≤ c.length → n % 2 = c.length % 2 →
      ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧ q.length = n := by
  let Q := 16 * D + 8 * (4 * D) ^ 2
  let M := cycleReservoirPrefix D Q
  let H := cycleReservoirInterval D Q
  let L := cycleReservoirDenominator D Q
  let C := 2 * (2 * Q + 16 * D + 3)
  let K := M + H + (32 * D + 8 * (4 * D) ^ 2 + 4) + 1
  let N₀ := D * C + 8 * (4 * D) ^ 2 + 2 * L * (Q + M + 1) + H
  have hQ : 0 < Q := by dsimp [Q]; omega
  refine ⟨N₀, K, ?_⟩
  intro V _ _ G _ d hN hscale hdegree z c hc n hn hnc hpar
  have hNshort : 8 * (4 * D) ^ 2 ≤ Fintype.card V := by dsimp [N₀] at hN; omega
  have hNloss : 2 * L * (Q + M + 1) ≤ Fintype.card V := by dsimp [N₀] at hN; omega
  have hNblock : H ≤ Fintype.card V := by dsimp [N₀] at hN; omega
  have hDC : D * C ≤ D * d := by
    have h : D * C ≤ Fintype.card V := by dsimp [N₀] at hN; omega
    exact h.trans hscale
  have hC : C ≤ d := (mul_le_mul_iff_right₀ hD).mp hDC
  have hlen : M < c.length := by dsimp [K] at hn hnc; omega
  obtain ⟨X, Y, hX, hY, hXY, hcomplete, u, hu, v, hv, huv, p, hp, hpL, hpPar, hpOff⟩ :=
    exists_cycle_reservoir G c hc D d Q hD hQ hscale hdegree hlen hNloss hNblock
  have hR : 2 * ((X ∪ Y).card + 16 * D + 1) ≤ d := by
    rw [card_union_of_disjoint hXY, hX, hY]
    dsimp [C] at hC
    omega
  have htarget : 32 * D + 8 * (4 * D) ^ 2 + 4 ≤ n := by dsimp [K] at hn; omega
  have hpath : n ≤ p.length + 2 := by
    change c.length ≤ p.length + M + H at hpL
    dsimp [K] at hnc
    omega
  have hX' : 16 * D + 8 * (4 * D) ^ 2 + 1 ≤ X.card := by
    change X.card = 16 * D + 8 * (4 * D) ^ 2 + 2 at hX
    omega
  have hY' : 16 * D + 8 * (4 * D) ^ 2 ≤ Y.card := hY.ge
  obtain ⟨q, hq, hqlen⟩ := exists_cycle_of_length_of_bipartite_reservoir G D d hD
    hscale hdegree hNshort X Y hXY hcomplete hX' hY' hR u v hu hv huv p hp hpOff
    n htarget hpath (hpar.trans hpPar.symm)
  exact ⟨u, q, hq, hqlen⟩

#print axioms exists_dense_cycle_spectrum

theorem exists_odd_cycle_cutoff_of_forbidden_cycle (D : ℕ) (hD : 0 < D) :
    ∃ N₀ K : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (d n : ℕ),
      N₀ ≤ Fintype.card V → Fintype.card V ≤ D * d → (∀ v, d ≤ G.degree v) →
      3 ≤ n → Odd n → K ≤ n → ¬ cycleGraph n ⊑ G →
      ∀ (z : V) (c : G.Walk z z), c.IsCycle → Odd c.length → c.length < n + K := by
  obtain ⟨N₀, K, hspec⟩ := exists_dense_cycle_spectrum D hD
  refine ⟨N₀, K, ?_⟩
  intro V _ _ G _ d n hN hscale hdegree hn hodd hnK hno z c hc hcodd
  by_contra hlong
  have hpar : n % 2 = c.length % 2 := (Nat.odd_iff.mp hodd).trans (Nat.odd_iff.mp hcodd).symm
  obtain ⟨w, q, hq, hqlen⟩ := hspec G d hN hscale hdegree z c hc n hnK (by omega) hpar
  apply hno
  exact (cycleGraph_isContained_iff (by omega)).mpr ⟨w, q, hq, hqlen⟩

#print axioms exists_odd_cycle_cutoff_of_forbidden_cycle

end Erdos556

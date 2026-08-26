import ErdosProblems.Erdos556.AvailableCycleVertices
import ErdosProblems.Erdos556.CycleParityBlock
import ErdosProblems.Erdos556.ExternalCycleReservoir
import ErdosProblems.Erdos556.InternalReservoirFromIntervals

/-!
# Finding a reservoir beside a long cycle path

Both possible locations of a large common-neighbor class are handled:
outside the cycle, or in one bounded interval on the cycle.
-/

namespace Erdos556

open SimpleGraph Finset

def cycleReservoirPrefix (D Q : ℕ) := 4 * D * (Q + 2)
def cycleReservoirDenominator (D Q : ℕ) := 2 * D * 2 ^ (2 * D * (Q + 2))
def cycleReservoirInterval (D Q : ℕ) := 8 * cycleReservoirDenominator D Q * (Q + 3)

theorem exists_cycle_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (D d Q : ℕ) (hD : 0 < D) (hQ : 0 < Q)
    (hscale : Fintype.card V ≤ D * d) (hdegree : ∀ v, d ≤ G.degree v)
    (hlen : cycleReservoirPrefix D Q < c.length)
    (hNloss : 2 * cycleReservoirDenominator D Q * (Q + cycleReservoirPrefix D Q + 1) ≤
      Fintype.card V)
    (hNblock : cycleReservoirInterval D Q ≤ Fintype.card V) :
    ∃ X Y : Finset V, X.card = Q + 2 ∧ Y.card = Q ∧ Disjoint X Y ∧
      (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) ∧
      ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ ∃ p : G.Walk u v, p.IsPath ∧
        c.length ≤ p.length + cycleReservoirPrefix D Q + cycleReservoirInterval D Q ∧
        p.length % 2 = c.length % 2 ∧
        ∀ w ∈ p.support, w ∈ X ∪ Y → w = u ∨ w = v := by
  classical
  let M := cycleReservoirPrefix D Q
  let K := cycleReservoirDenominator D Q
  let H := cycleReservoirInterval D Q
  obtain ⟨A, W, hA, hAP, hAX, hWsize, hcomplete⟩ := exists_cycle_interval_common_neighbors
    G c hc D (Q + 2) d (by omega) hscale hdegree hlen.le
  have hAM (i : ℕ) (hi : i ∈ A) : i ≤ M := (hAP i hi).1.le
  have hparA (i : ℕ) (hi : i ∈ A) (j : ℕ) (hj : j ∈ A) : i % 2 = j % 2 := by
    have hiE := Nat.even_iff.mp (hAP i hi).2
    have hjE := Nat.even_iff.mp (hAP j hj).2
    omega
  let E := W \ c.support.toFinset
  by_cases hext : Q ≤ E.card
  · obtain ⟨Y, hYE, hY⟩ := exists_subset_card_eq hext
    have hYW : Y ⊆ W := hYE.trans sdiff_subset
    have hYoff (y : V) (hy : y ∈ Y) : y ∉ c.support := by
      intro hyc
      exact (mem_sdiff.mp (hYE hy)).2 (List.mem_toFinset.mpr hyc)
    let X := A.image c.getVert
    have hcomp (x : V) (hx : x ∈ X) (y : V) (hy : y ∈ Y) : G.Adj x y := by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact hcomplete i hi y (hYW hy)
    have hXY : Disjoint X Y := by
      rw [Finset.disjoint_left]
      intro x hx hy
      exact (hcomp x hx x hy).ne rfl
    obtain ⟨u, hu, v, hv, huv, p, hp, hpL, hpPar, hpOff⟩ :=
      exists_long_path_outside_cycle_interval c hc A (by omega) M hlen hAM hparA Y hYoff
    exact ⟨X, Y, hAX, hY, hXY, hcomp, u, hu, v, hv, huv, p, hp,
      by omega, hpPar, hpOff⟩
  · have hK : 0 < K := by dsimp [K, cycleReservoirDenominator]; positivity
    obtain ⟨U, hUW, hUC, hUoff, hUsize⟩ := exists_available_cycle_vertices c W
      (Fintype.card V) K Q M hlen.le hWsize hNloss (Nat.lt_of_not_ge hext)
    have hcN : c.length ≤ Fintype.card V := by
      have h := hc.isPath_tail.length_lt
      rw [Walk.length_tail] at h
      have hlen3 := hc.three_le_length
      omega
    obtain ⟨B, hB, hBM, hblock⟩ := exists_cycle_parity_block c hc U hUC M
      (Fintype.card V) K (Q + 3) hK (by omega) hNblock hcN hUsize hUoff
    have hcomp (i : ℕ) (hi : i ∈ A) (j : ℕ) (hj : j ∈ B) :
        G.Adj (c.getVert i) (c.getVert j) := hcomplete i hi _ (hUW (hBM j hj).2.2)
    exact exists_internal_reservoir_from_intervals c hc A B Q M H hQ hA hB hlen hAM
      (fun j hj => ⟨(hBM j hj).1, (hBM j hj).2.1⟩) hparA
      (fun i hi j hj => (hblock i hi j hj).1) (fun i hi j hj => (hblock i hi j hj).2) hcomp

#print axioms exists_cycle_reservoir

end Erdos556

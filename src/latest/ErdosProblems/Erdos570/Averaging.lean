/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Support

/-!
# Fixed-cardinality edge averaging

This is the finite double-counting form of the random-subset step: among all
`r`-vertex subsets, one spans no more than the average number of edges.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos570

open Erdos79

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of graph edges whose two endpoints lie in `S`. -/
def internalEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card

/-- `internalEdgeCount` is the edge count of the induced graph. -/
theorem inducedCode_edgeCount_eq_internalEdgeCount
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (S : Finset (Fin H.vertexCount)) :
    (inducedCode H S).edgeCount = internalEdgeCount H.graph S := by
  classical
  let : Fintype (S : Set (Fin H.vertexCount)) :=
    Subtype.fintype (Membership.mem (S : Set (Fin H.vertexCount)))
  let : DecidableRel (inducedCode H S).graph.Adj :=
    Classical.decRel (inducedCode H S).graph.Adj
  rw [GraphCode.edgeCount_eq_card_edgeFinset]
  calc
    (inducedCode H S).graph.edgeFinset.card =
        (H.graph.induce (S : Set (Fin H.vertexCount))).edgeFinset.card := by
      exact (inducedCodeIso H S).card_edgeFinset_eq.symm
    _ = ((H.graph.induce (S : Set (Fin H.vertexCount))).edgeFinset.map
        (Function.Embedding.subtype (· ∈ (S : Set (Fin H.vertexCount)))).sym2Map).card := by
      rw [Finset.card_map]
    _ = (H.graph.edgeFinset ∩ S.sym2).card := by
      simpa using congrArg Finset.card
        (H.graph.map_edgeFinset_induce
          (s := (S : Set (Fin H.vertexCount))))
    _ = (H.graph.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card := by
      congr 1
      ext e
      simp only [Finset.mem_inter, Finset.mem_filter, and_congr_right_iff]
      intro he
      rw [Finset.mem_sym2_iff]
      simp only [Finset.subset_iff, Sym2.mem_toFinset]
    _ = internalEdgeCount H.graph S := rfl

/-- The total number of incidences `(edge, r-set containing that edge)` can
be counted edge-first or subset-first. -/
theorem sum_internalEdgeCount_powersetCard (G : SimpleGraph V)
    [DecidableRel G.Adj] {r : ℕ} (hr : 2 ≤ r) :
    ∑ S ∈ (Finset.univ : Finset V).powersetCard r,
        internalEdgeCount G S =
      G.edgeFinset.card * Nat.choose (Fintype.card V - 2) (r - 2) := by
  classical
  let P := (Finset.univ : Finset V).powersetCard r
  have hedge (e : Sym2 V) (he : e ∈ G.edgeFinset) : e.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeFinset he)
  have hcount (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      ((P.filter fun S ↦ e.toFinset ⊆ S).card) =
        Nat.choose (Fintype.card V - 2) (r - 2) := by
    rw [Finset.card_filter_powersetCard_subset e.toFinset Finset.univ r
      (Finset.subset_univ _) (by rw [hedge e he]; exact hr)]
    simp only [Finset.card_univ, hedge e he]
  calc
    ∑ S ∈ P, internalEdgeCount G S =
        ∑ S ∈ P, ∑ e ∈ G.edgeFinset,
          if e.toFinset ⊆ S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [internalEdgeCount, Finset.card_eq_sum_ones]
      simp only [Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset, ∑ S ∈ P,
          if e.toFinset ⊆ S then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, (P.filter fun S ↦ e.toFinset ⊆ S).card := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.card_eq_sum_ones]
      simp only [Finset.sum_filter]
    _ = ∑ _e ∈ G.edgeFinset,
          Nat.choose (Fintype.card V - 2) (r - 2) := by
      apply Finset.sum_congr rfl
      intro e he
      exact hcount e he
    _ = G.edgeFinset.card * Nat.choose (Fintype.card V - 2) (r - 2) := by
      simp

/-- Some `r`-vertex subset spans at most the exact average number of edges,
with division cleared. -/
theorem exists_subset_internalEdgeCount_mul_choose_le
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hr2 : 2 ≤ r) (hrV : r ≤ Fintype.card V) :
    ∃ S : Finset V, S.card = r ∧
      internalEdgeCount G S * Nat.choose (Fintype.card V) r ≤
        G.edgeFinset.card * Nat.choose (Fintype.card V - 2) (r - 2) := by
  classical
  let P := (Finset.univ : Finset V).powersetCard r
  have hP : P.Nonempty := Finset.powersetCard_nonempty.mpr (by simpa [P] using hrV)
  let total := ∑ S ∈ P, internalEdgeCount G S
  have hsum : total =
      G.edgeFinset.card * Nat.choose (Fintype.card V - 2) (r - 2) := by
    exact sum_internalEdgeCount_powersetCard G hr2
  have haverage : ∃ S ∈ P, internalEdgeCount G S * P.card ≤ total := by
    apply Finset.exists_le_of_sum_le hP
    rw [← Finset.sum_mul]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact Nat.le_of_eq (mul_comm total P.card)
  obtain ⟨S, hSP, hSavg⟩ := haverage
  refine ⟨S, (Finset.mem_powersetCard.mp hSP).2, ?_⟩
  rw [Finset.card_powersetCard, Finset.card_univ] at hSavg
  rw [hsum] at hSavg
  exact hSavg

/-- Coded-graph version of the fixed-cardinality averaging lemma. -/
theorem exists_inducedCode_edgeCount_mul_choose_le
    (H : GraphCode) {r : ℕ} (hr2 : 2 ≤ r) (hrH : r ≤ H.vertexCount) :
    ∃ S : Finset (Fin H.vertexCount), S.card = r ∧
      (inducedCode H S).edgeCount * Nat.choose H.vertexCount r ≤
        H.edgeCount * Nat.choose (H.vertexCount - 2) (r - 2) := by
  classical
  let : DecidableRel H.graph.Adj := Classical.decRel H.graph.Adj
  obtain ⟨S, hScard, hS⟩ :=
    exists_subset_internalEdgeCount_mul_choose_le H.graph hr2 (by simpa using hrH)
  refine ⟨S, hScard, ?_⟩
  rw [inducedCode_edgeCount_eq_internalEdgeCount]
  rw [GraphCode.edgeCount_eq_card_edgeFinset]
  simpa using hS

/-- The fixed-cardinality averaging bound with the binomial denominator
cancelled.  This is the exact integer form of
`e(H[S]) ≤ e(H) * r(r-1)/(n(n-1))`. -/
theorem exists_inducedCode_edgeCount_mul_order_le
    (H : GraphCode) {r : ℕ} (hr2 : 2 ≤ r) (hrH : r ≤ H.vertexCount) :
    ∃ S : Finset (Fin H.vertexCount), S.card = r ∧
      (inducedCode H S).edgeCount *
          (H.vertexCount * (H.vertexCount - 1)) ≤
        H.edgeCount * (r * (r - 1)) := by
  obtain ⟨S, hScard, hS⟩ :=
    exists_inducedCode_edgeCount_mul_choose_le H hr2 hrH
  let n := H.vertexCount
  have hn2 : 2 ≤ n := hr2.trans hrH
  have hnPred : n - 2 + 1 = n - 1 := by omega
  have hrPred : r - 2 + 1 = r - 1 := by omega
  have hnSelf : n - 1 + 1 = n := by omega
  have hrSelf : r - 1 + 1 = r := by omega
  have hstep1 : (n - 1) * Nat.choose (n - 2) (r - 2) =
      Nat.choose (n - 1) (r - 1) * (r - 1) := by
    simpa only [hnPred, hrPred] using
      Nat.add_one_mul_choose_eq (n - 2) (r - 2)
  have hstep2 : n * Nat.choose (n - 1) (r - 1) =
      Nat.choose n r * r := by
    simpa only [hnSelf, hrSelf] using
      Nat.add_one_mul_choose_eq (n - 1) (r - 1)
  have hchoose :
      n * (n - 1) * Nat.choose (n - 2) (r - 2) =
        Nat.choose n r * (r * (r - 1)) := by
    calc
      n * (n - 1) * Nat.choose (n - 2) (r - 2) =
          n * ((n - 1) * Nat.choose (n - 2) (r - 2)) := by ring
      _ = n * (Nat.choose (n - 1) (r - 1) * (r - 1)) := by
        rw [hstep1]
      _ = (n * Nat.choose (n - 1) (r - 1)) * (r - 1) := by ring
      _ = (Nat.choose n r * r) * (r - 1) := by
        rw [hstep2]
      _ = Nat.choose n r * (r * (r - 1)) := by ring
  have hmul := Nat.mul_le_mul_right (n * (n - 1)) hS
  have hfactored :
      Nat.choose n r *
          ((inducedCode H S).edgeCount * (n * (n - 1))) ≤
        Nat.choose n r * (H.edgeCount * (r * (r - 1))) := by
    dsimp only [n] at hchoose ⊢
    calc
      Nat.choose H.vertexCount r *
          ((inducedCode H S).edgeCount *
            (H.vertexCount * (H.vertexCount - 1))) =
          ((inducedCode H S).edgeCount * Nat.choose H.vertexCount r) *
            (H.vertexCount * (H.vertexCount - 1)) := by ring
      _ ≤ (H.edgeCount * Nat.choose (H.vertexCount - 2) (r - 2)) *
            (H.vertexCount * (H.vertexCount - 1)) := hmul
      _ = Nat.choose H.vertexCount r *
          (H.edgeCount * (r * (r - 1))) := by
        calc
          H.edgeCount * Nat.choose (H.vertexCount - 2) (r - 2) *
              (H.vertexCount * (H.vertexCount - 1)) =
              H.edgeCount * (H.vertexCount * (H.vertexCount - 1) *
                Nat.choose (H.vertexCount - 2) (r - 2)) := by ring
          _ = H.edgeCount * (Nat.choose H.vertexCount r *
                (r * (r - 1))) := by rw [hchoose]
          _ = Nat.choose H.vertexCount r *
              (H.edgeCount * (r * (r - 1))) := by ring
  have hchoosePos : 0 < Nat.choose n r := Nat.choose_pos hrH
  refine ⟨S, hScard, ?_⟩
  exact Nat.le_of_mul_le_mul_left hfactored hchoosePos

end Erdos570

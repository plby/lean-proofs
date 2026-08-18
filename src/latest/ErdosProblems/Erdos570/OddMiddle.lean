/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.Averaging
import ErdosProblems.Erdos570.Coloring
import ErdosProblems.Erdos570.Join
import ErdosProblems.Erdos570.OddArithmetic
import ErdosProblems.Erdos570.RamseyRegion

/-!
# The random-partition completion in the odd-cycle induction

This file formalizes Step 4 of the CFMPP proof.  The preceding neighborhood
argument only has to provide two disjoint host regions and the numerical
bounds in the theorem below.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- A proper smaller sampling ratio makes the averaged induced edge count
strictly smaller than the original positive edge count. -/
theorem edgeCount_lt_of_sampling_product
    {e m r n : ℕ} (hm : 0 < m) (hr2 : 2 ≤ r) (hrn : r < n)
    (hem : e ≤ m)
    (havg : e * (n * (n - 1)) ≤ m * (r * (r - 1))) :
    e < m := by
  have hnpos : 0 < n - 1 := by omega
  have hrle : r - 1 ≤ n - 1 := by omega
  have hprod : r * (r - 1) < n * (n - 1) := by
    calc
      r * (r - 1) ≤ r * (n - 1) := Nat.mul_le_mul_left r hrle
      _ < n * (n - 1) := Nat.mul_lt_mul_of_pos_right hrn hnpos
  by_contra hem'
  have heq : e = m := Nat.le_antisymm hem (Nat.le_of_not_gt hem')
  rw [heq] at havg
  have hstrict := Nat.mul_lt_mul_of_pos_left hprod hm
  exact (Nat.not_lt_of_ge (by simpa [mul_assoc, mul_left_comm, mul_comm] using havg)
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hstrict)).elim

/-- Completion of the middle-density case from the two host regions produced
by the first- and second-neighborhood estimates.

`U₁` contains no red path on `k-1` vertices, all cross edges between `U₁`
and `U₂` are blue, and the two displayed product inequalities are the
integer versions of the room estimates in the paper. -/
theorem odd_middle_partition_forces_target
    {F H : GraphCode} {B s k q : ℕ}
    (C : SimpleGraph (Fin (oddBudget B s H.edgeCount)))
    [DecidableRel C.Adj] [DecidableRel H.graph.Adj]
    (hk : 3 ≤ k) (hsB : s ≤ B)
    (hm : 0 < H.edgeCount)
    (hq : q = Nat.sqrt (2 * H.edgeCount))
    (hnoF : ¬ F.graph ⊑ C) (hnoH : ¬ H.graph ⊑ Cᶜ)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber F Q ≤ oddBudget B s Q.edgeCount)
    (U₁ U₂ : Finset (Fin (oddBudget B s H.edgeCount)))
    (hdisj : Disjoint U₁ U₂)
    (hcross : ∀ x ∈ U₁, ∀ y ∈ U₂, Cᶜ.Adj x y)
    (hpath : ¬ SimpleGraph.pathGraph (k - 1) ⊑
      C.induce (U₁ : Set (Fin (oddBudget B s H.edgeCount))))
    (r : ℕ) (hr2 : 2 ≤ r) (hrn : r < H.vertexCount)
    (hU₁room : H.vertexCount - r + (k - 1) * q ≤ U₁.card)
    (hU₂vertices : r ≤ U₂.card)
    (hU₂edges :
      2 * H.edgeCount * (r * (r - 1)) +
          B * (H.vertexCount * (H.vertexCount - 1)) ≤
        U₂.card * (H.vertexCount * (H.vertexCount - 1))) : False := by
  classical
  obtain ⟨S, hScard, haverage⟩ :=
    exists_inducedCode_edgeCount_mul_order_le H hr2 hrn.le
  let H₂raw := inducedCode H S
  let H₁ := inducedCode H Sᶜ
  let H₂ := supportCode H₂raw
  have hH₁vertices : H₁.vertexCount = H.vertexCount - r := by
    dsimp only [H₁]
    rw [inducedCode_vertexCount, Finset.card_compl, Fintype.card_fin, hScard]
  have hH₁edges : H₁.edgeCount ≤ H.edgeCount :=
    inducedCode_edgeCount_le H Sᶜ
  have hsqrt : Nat.sqrt (2 * H₁.edgeCount) ≤ q := by
    rw [hq]
    exact Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 2 hH₁edges)
  have hpathRoom : H₁.vertexCount + (k - 1) *
      Nat.sqrt (2 * H₁.edgeCount) ≤ U₁.card := by
    rw [hH₁vertices]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left (k - 1) hsqrt)
      (H.vertexCount - r)).trans hU₁room
  have hblue₁ : H₁.graph ⊑ Cᶜ.induce
      (U₁ : Set (Fin (oddBudget B s H.edgeCount))) := by
    rcases Erdos570.RamseyAt.on_finset
        (ramseyAt_path_sqrt_edges (H := H₁) (by omega)) C U₁ hpathRoom with
      hredPath | hblue
    · exact (hpath (by simpa [pathCode] using hredPath)).elim
    · exact hblue
  have hH₂edge : H₂.edgeCount = H₂raw.edgeCount := by
    simp [H₂]
  have hH₂le : H₂.edgeCount ≤ H.edgeCount := by
    rw [hH₂edge]
    exact inducedCode_edgeCount_le H S
  have haverage' : H₂.edgeCount *
        (H.vertexCount * (H.vertexCount - 1)) ≤
      H.edgeCount * (r * (r - 1)) := by
    rw [hH₂edge]
    simpa [H₂raw] using haverage
  have hH₂lt : H₂.edgeCount < H.edgeCount :=
    edgeCount_lt_of_sampling_product hm hr2 hrn hH₂le haverage'
  have hH₂no : NoIsolated H₂ := by
    exact supportCode_noIsolated H₂raw
  have hdenom : 0 < H.vertexCount * (H.vertexCount - 1) := by
    have : 2 ≤ H.vertexCount := hr2.trans hrn.le
    exact Nat.mul_pos (by omega) (by omega)
  have hscaled : (2 * H₂.edgeCount + B) *
        (H.vertexCount * (H.vertexCount - 1)) ≤
      U₂.card * (H.vertexCount * (H.vertexCount - 1)) := by
    nlinarith [haverage', hU₂edges]
  have hcoarse : 2 * H₂.edgeCount + B ≤ U₂.card :=
    Nat.le_of_mul_le_mul_right hscaled hdenom
  have hbudgetCoarse : oddBudget B s H₂.edgeCount ≤
      2 * H₂.edgeCount + B := by
    unfold oddBudget
    have hsub : B - Nat.sqrt H₂.edgeCount ≤ B := Nat.sub_le _ _
    omega
  have hH₂Ramsey : graphRamseyNumber F H₂ ≤ U₂.card :=
    (hIH H₂ hH₂no hH₂lt).trans (hbudgetCoarse.trans hcoarse)
  have hcore₂ : H₂.graph ⊑ Cᶜ.induce
      (U₂ : Set (Fin (oddBudget B s H.edgeCount))) := by
    rcases graphRamseyNumber_on_finset F H₂ C U₂ hH₂Ramsey with
      hredF | hblue
    · exact (hnoF (hredF.trans
        (SimpleGraph.Embedding.induce
          (U₂ : Set (Fin (oddBudget B s H.edgeCount)))).isContained)).elim
    · exact hblue
  have hblue₂ : H₂raw.graph ⊑ Cᶜ.induce
      (U₂ : Set (Fin (oddBudget B s H.edgeCount))) := by
    apply isContained_induce_of_supportCode_isContained Cᶜ U₂ hcore₂
    simpa [H₂raw, hScard] using hU₂vertices
  have hjoin : (joinCode H₂raw H₁).graph ⊑ Cᶜ := by
    apply joinCode_isContained_of_induced_copies
    · rw [Set.disjoint_left]
      intro x hx₂ hx₁
      exact Finset.disjoint_left.mp hdisj hx₁ hx₂
    · exact hblue₂
    · exact hblue₁
    · intro x y
      exact (hcross y.1 y.2 x.1 x.2).symm
  have hpart : IsContained H (joinCode H₂raw H₁) := by
    simpa [H₂raw, H₁] using isContained_joinCode_induced_partition H S
  have htarget : H.graph ⊑ Cᶜ :=
    SimpleGraph.IsContained.trans hpart hjoin
  exact hnoH htarget

end Erdos570

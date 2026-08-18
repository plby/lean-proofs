/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.OddMiddle
import ErdosProblems.Erdos570.OddNeighborhoodInduction
import ErdosProblems.Erdos570.OddScale
import ErdosProblems.Erdos570.CycleCode

/-!
# The middle-density triangle branch

For a triangle-free red graph, every red neighborhood is a blue clique.
This removes the first path-Ramsey loss from the general odd-cycle argument.
The remaining second-neighborhood deletion and random target partition are
the same as in the CFMPP middle-density proof.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Numerical room for the triangle-specific middle-density argument. -/
def TriangleMiddleRoom (B m n q : ℕ) : Prop :=
  ∀ a p : ℕ,
    n / 2 ≤ a →
    a < n →
    p < n + 6 * q →
    let r := max 2 (n - a)
    2 ≤ r ∧ r < n ∧ n - r ≤ a ∧
      r ≤ oddBudget B 1 m - (1 + a + p) ∧
      2 * m * (r * (r - 1)) + B * (n * (n - 1)) ≤
        (oddBudget B 1 m - (1 + a + p)) * (n * (n - 1))

/-- A fixed square-root error gap supplies all room needed by the
triangle-specific partition. -/
theorem triangleMiddleRoom_of_gap {B m n q : ℕ}
    (hq : q = Nat.sqrt (2 * m)) (hqpos : 0 < q) (hn4 : 4 ≤ n)
    (hgap : 6 * q + Nat.sqrt m + 2 ≤ m - n) :
    TriangleMiddleRoom B m n q := by
  intro a p haLower haUpper hpUpper
  let r := max 2 (n - a)
  let d := m - n
  have hdiff : 0 < n - a := Nat.sub_pos_iff_lt.mpr haUpper
  have hr2 : 2 ≤ r := by simp [r]
  have hrle : r ≤ n - a + 1 := by
    dsimp only [r]
    rw [max_le_iff]
    constructor <;> omega
  have hrn : r < n := by
    have hhalf : 2 * (n - a) ≤ n + 1 := by omega
    dsimp only [r]
    rw [max_lt_iff]
    constructor
    · omega
    · omega
  have hnr : n - r ≤ a := by omega
  have hdiffMN : 0 < m - n := by
    exact lt_of_lt_of_le (by omega : 0 < 6 * q + Nat.sqrt m + 2) hgap
  have hnle : n ≤ m := (Nat.sub_pos_iff_lt.mp hdiffMN).le
  have hmdecomp : n + d = m := by
    dsimp only [d]
    exact Nat.add_sub_of_le hnle
  have hrpred : 2 * (r - 1) ≤ n - 1 := by
    have hhalf : 2 * (n - a) ≤ n + 1 := by omega
    dsimp only [r]
    rw [max_def]
    split <;> omega
  have hvertexAdd : r + (1 + a + p) ≤ oddBudget B 1 m := by
    have hbase : 2 * m + 1 ≤ oddBudget B 1 m := by
      unfold oddBudget
      omega
    have hsum : r + (1 + a + p) ≤ 2 * m + 1 := by
      omega
    exact hsum.trans hbase
  have hrRoom : r ≤ oddBudget B 1 m - (1 + a + p) :=
    Nat.le_sub_of_add_le (by
      simpa [add_assoc, add_left_comm, add_comm] using hvertexAdd)
  have hratio : 2 * m * (r * (r - 1)) ≤
      (r + d) * (n * (n - 1)) := by
    have hrleN : r ≤ n := hrn.le
    have hfirst : 2 * n * (r * (r - 1)) ≤
        r * (n * (n - 1)) := by
      calc
        2 * n * (r * (r - 1)) = n * r * (2 * (r - 1)) := by ring
        _ ≤ n * r * (n - 1) := Nat.mul_le_mul_left (n * r) hrpred
        _ = r * (n * (n - 1)) := by ring
    have hrprod : 2 * (r * (r - 1)) ≤ n * (n - 1) := by
      calc
        2 * (r * (r - 1)) = r * (2 * (r - 1)) := by ring
        _ ≤ r * (n - 1) := Nat.mul_le_mul_left r hrpred
        _ ≤ n * (n - 1) := Nat.mul_le_mul_right (n - 1) hrleN
    have hsecond : 2 * d * (r * (r - 1)) ≤
        d * (n * (n - 1)) := by
      calc
        2 * d * (r * (r - 1)) = d * (2 * (r * (r - 1))) := by ring
        _ ≤ d * (n * (n - 1)) := Nat.mul_le_mul_left d hrprod
    calc
      2 * m * (r * (r - 1)) =
          2 * n * (r * (r - 1)) + 2 * d * (r * (r - 1)) := by
            rw [← hmdecomp]
            ring
      _ ≤ r * (n * (n - 1)) + d * (n * (n - 1)) :=
        Nat.add_le_add hfirst hsecond
      _ = (r + d) * (n * (n - 1)) := by ring
  have hcorr : B ≤ Nat.sqrt m + max (B - Nat.sqrt m) 1 := by omega
  have hedgeAdd : B + (r + d) + (1 + a + p) ≤
      oddBudget B 1 m := by
    unfold oddBudget
    omega
  have hedgeRoom : B + (r + d) ≤
      oddBudget B 1 m - (1 + a + p) :=
    Nat.le_sub_of_add_le (by
      simpa [add_assoc, add_left_comm, add_comm] using hedgeAdd)
  have hedgeProduct :
      2 * m * (r * (r - 1)) + B * (n * (n - 1)) ≤
        (oddBudget B 1 m - (1 + a + p)) * (n * (n - 1)) := by
    calc
      2 * m * (r * (r - 1)) + B * (n * (n - 1)) ≤
          (r + d) * (n * (n - 1)) + B * (n * (n - 1)) :=
        Nat.add_le_add_right hratio _
      _ = (B + (r + d)) * (n * (n - 1)) := by ring
      _ ≤ (oddBudget B 1 m - (1 + a + p)) *
          (n * (n - 1)) := Nat.mul_le_mul_right _ hedgeRoom
  exact ⟨hr2, hrn, hnr, hrRoom, hedgeProduct⟩

/-- The random-partition completion when the first host region is already a
blue clique, as happens for a red neighborhood in a triangle-free graph. -/
theorem triangle_middle_partition_forces_target
    {F H : GraphCode} {B : ℕ}
    (C : SimpleGraph (Fin (oddBudget B 1 H.edgeCount)))
    [DecidableRel C.Adj] [DecidableRel H.graph.Adj]
    (hB : 1 ≤ B) (hm : 0 < H.edgeCount)
    (hnoF : ¬ F.graph ⊑ C) (hnoH : ¬ H.graph ⊑ Cᶜ)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber F Q ≤ oddBudget B 1 Q.edgeCount)
    (U₁ U₂ : Finset (Fin (oddBudget B 1 H.edgeCount)))
    (hdisj : Disjoint U₁ U₂)
    (hcross : ∀ x ∈ U₁, ∀ y ∈ U₂, Cᶜ.Adj x y)
    (hclique : Cᶜ.IsClique (U₁ : Set (Fin (oddBudget B 1 H.edgeCount))))
    (r : ℕ) (hr2 : 2 ≤ r) (hrn : r < H.vertexCount)
    (hU₁room : H.vertexCount - r ≤ U₁.card)
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
  have hH₁room : H₁.vertexCount ≤ U₁.card := by
    rw [hH₁vertices]
    exact hU₁room
  let f : Fin H₁.vertexCount ↪ U₁ :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, Fintype.card_coe] using hH₁room))
  let hom₁ : H₁.graph →g Cᶜ.induce (U₁ : Set _) :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        exact hclique (f x).2 (f y).2 (by
          intro heq
          exact hxy.ne (f.injective (Subtype.ext heq))) }
  have hblue₁ : H₁.graph ⊑ Cᶜ.induce (U₁ : Set _) :=
    ⟨hom₁.toCopy f.injective⟩
  have hH₂edge : H₂.edgeCount = H₂raw.edgeCount := by simp [H₂]
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
  have hH₂no : NoIsolated H₂ := supportCode_noIsolated H₂raw
  have hdenom : 0 < H.vertexCount * (H.vertexCount - 1) := by
    have : 2 ≤ H.vertexCount := hr2.trans hrn.le
    exact Nat.mul_pos (by omega) (by omega)
  have hscaled : (2 * H₂.edgeCount + B) *
        (H.vertexCount * (H.vertexCount - 1)) ≤
      U₂.card * (H.vertexCount * (H.vertexCount - 1)) := by
    calc
      (2 * H₂.edgeCount + B) *
          (H.vertexCount * (H.vertexCount - 1)) =
          2 * (H₂.edgeCount *
            (H.vertexCount * (H.vertexCount - 1))) +
            B * (H.vertexCount * (H.vertexCount - 1)) := by ring
      _ ≤ 2 * (H.edgeCount * (r * (r - 1))) +
            B * (H.vertexCount * (H.vertexCount - 1)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 haverage') _
      _ = 2 * H.edgeCount * (r * (r - 1)) +
            B * (H.vertexCount * (H.vertexCount - 1)) := by ring
      _ ≤ U₂.card * (H.vertexCount * (H.vertexCount - 1)) := hU₂edges
  have hcoarse : 2 * H₂.edgeCount + B ≤ U₂.card :=
    Nat.le_of_mul_le_mul_right hscaled hdenom
  have hbudgetCoarse : oddBudget B 1 H₂.edgeCount ≤
      2 * H₂.edgeCount + B := by
    unfold oddBudget
    omega
  have hH₂Ramsey : graphRamseyNumber F H₂ ≤ U₂.card :=
    (hIH H₂ hH₂no hH₂lt).trans (hbudgetCoarse.trans hcoarse)
  have hcore₂ : H₂.graph ⊑ Cᶜ.induce (U₂ : Set _) := by
    rcases graphRamseyNumber_on_finset F H₂ C U₂ hH₂Ramsey with
      hredF | hblue
    · exact (hnoF (hredF.trans
        (SimpleGraph.Embedding.induce
          (U₂ : Set (Fin (oddBudget B 1 H.edgeCount)))).isContained)).elim
    · exact hblue
  have hblue₂ : H₂raw.graph ⊑ Cᶜ.induce (U₂ : Set _) := by
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

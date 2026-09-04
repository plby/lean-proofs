/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.EmbeddingNeighborhood
import ErdosProblems.Erdos570.CycleCode
import ErdosProblems.Erdos570.Neighborhood
import ErdosProblems.Erdos570.OddMiddle

/-!
# Neighborhood stage of the strengthened odd-cycle induction

This module assembles the minimum-degree deletion, the two red-neighborhood
closures, the path Ramsey estimates, and the random-partition completion.
The remaining assumptions are purely numerical and are discharged separately
from the explicit CFMPP constants.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Purely numerical room needed after the first- and second-neighborhood
estimates.  Here `a=|U₁|`, `p=|Π|`, and
`r=n-a+k*sqrt(2m)`. -/
def OddMiddleRoom (B s k m n q : ℕ) : Prop :=
  ∀ a p : ℕ,
    n / 2 + k * q ≤ a →
    a < n + (k - 1) * q →
    p < n + 2 * k * q →
    let r := n - a + k * q
    2 ≤ r ∧ r < n ∧
      r ≤ oddBudget B s m - (1 + a + p) ∧
      2 * m * (r * (r - 1)) + B * (n * (n - 1)) ≤
        (oddBudget B s m - (1 + a + p)) * (n * (n - 1))

/-- Two coarse scale separations imply all of `OddMiddleRoom`.  The proof
keeps the sampled-edge estimate division-free. -/
theorem oddMiddleRoom_of_gap {B s k m n q : ℕ}
    (hk : 5 ≤ k) (hq : q = Nat.sqrt (2 * m))
    (hqpos : 0 < q) (hn2 : 2 ≤ n)
    (hhalf : 2 * (k * q) ≤ n)
    (hgap : 4 * (k * q) + Nat.sqrt m ≤ m - n) :
    OddMiddleRoom B s k m n q := by
  intro a p haLower haUpper hpUpper
  let h := k * q
  let r := n - a + h
  have hhpos : 0 < h := Nat.mul_pos (by omega) hqpos
  have hk_le_h : k ≤ h := by
    dsimp only [h]
    simpa using Nat.mul_le_mul_left k (show 1 ≤ q by omega)
  have hh2 : 2 ≤ h := le_trans (by omega) hk_le_h
  have hdiffpos : 0 < m - n :=
    lt_of_lt_of_le (Nat.add_pos_left (Nat.mul_pos (by omega) hhpos) _) hgap
  have hnle : n ≤ m := (Nat.sub_pos_iff_lt.mp hdiffpos).le
  have hmdecomp : n + (m - n) = m := Nat.add_sub_of_le hnle
  have hpredq : (k - 1) * q + q = h := by
    dsimp only [h]
    calc
      (k - 1) * q + q = (k - 1) * q + 1 * q := by simp
      _ = (k - 1 + 1) * q := by rw [Nat.add_mul]
      _ = k * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have haUpper' : a < n + h := by omega
  have hpUpper' : p < n + 2 * h := by simpa [h, mul_assoc] using hpUpper
  have hr2 : 2 ≤ r := by
    dsimp only [r]
    omega
  have hrpred : 2 * (r - 1) ≤ n - 1 := by
    dsimp only [r]
    change n / 2 + h ≤ a at haLower
    by_cases han : a ≤ n
    · have hsub : n - a + a = n := Nat.sub_add_cancel han
      clear hq hk hqpos hhpos hk_le_h hh2 hnle hmdecomp hpredq haUpper
        haUpper' hpUpper hpUpper' hhalf hgap hdiffpos
      omega
    · have hsub : n - a = 0 := Nat.sub_eq_zero_of_le (by omega)
      omega
  have hrn : r < n := by omega
  have hcorr : B ≤ Nat.sqrt m + max (B - Nat.sqrt m) (k / 2) := by
    omega
  have hvertexAdd : r + (1 + a + p) ≤ oddBudget B s m := by
    unfold oddBudget
    by_cases han : a ≤ n
    · have hsub : n - a + a = n := Nat.sub_add_cancel han
      omega
    · have hsub : n - a = 0 := Nat.sub_eq_zero_of_le (by omega)
      omega
  have hrRoom : r ≤ oddBudget B s m - (1 + a + p) :=
    Nat.le_sub_of_add_le (by simpa [add_assoc, add_left_comm, add_comm] using hvertexAdd)
  let d := m - n
  have hratio : 2 * m * (r * (r - 1)) ≤
      (r + d) * (n * (n - 1)) := by
    have hrle : r ≤ n := hrn.le
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
        _ ≤ n * (n - 1) := Nat.mul_le_mul_right (n - 1) hrle
    have hsecond : 2 * d * (r * (r - 1)) ≤
        d * (n * (n - 1)) := by
      calc
        2 * d * (r * (r - 1)) = d * (2 * (r * (r - 1))) := by ring
        _ ≤ d * (n * (n - 1)) := Nat.mul_le_mul_left d hrprod
    have hmdecomp' : n + d = m := by simpa [d] using hmdecomp
    calc
      2 * m * (r * (r - 1)) =
          2 * n * (r * (r - 1)) + 2 * d * (r * (r - 1)) := by
            rw [← hmdecomp']
            ring
      _ ≤ r * (n * (n - 1)) + d * (n * (n - 1)) :=
        Nat.add_le_add hfirst hsecond
      _ = (r + d) * (n * (n - 1)) := by ring
  have hedgeAdd : B + (r + d) + (1 + a + p) ≤
      oddBudget B s m := by
    unfold oddBudget
    dsimp only [d, r]
    by_cases han : a ≤ n
    · have hsub : n - a + a = n := Nat.sub_add_cancel han
      omega
    · have hsub : n - a = 0 := Nat.sub_eq_zero_of_le (by omega)
      omega
  have hedgeRoom : B + (r + d) ≤
      oddBudget B s m - (1 + a + p) :=
    Nat.le_sub_of_add_le (by
      simpa [add_assoc, add_left_comm, add_comm] using hedgeAdd)
  have hedgeProduct :
      2 * m * (r * (r - 1)) + B * (n * (n - 1)) ≤
        (oddBudget B s m - (1 + a + p)) * (n * (n - 1)) := by
    calc
      2 * m * (r * (r - 1)) + B * (n * (n - 1)) ≤
          (r + d) * (n * (n - 1)) + B * (n * (n - 1)) :=
        Nat.add_le_add_right hratio _
      _ = (B + (r + d)) * (n * (n - 1)) := by ring
      _ ≤ (oddBudget B s m - (1 + a + p)) *
          (n * (n - 1)) := Nat.mul_le_mul_right _ hedgeRoom
  exact ⟨hr2, hrn, hrRoom, hedgeProduct⟩

/-- The connected middle-density case of the strengthened odd-cycle
induction, conditional only on explicit integer inequalities. -/
theorem odd_connected_middle_contradiction
    {H : GraphCode} {B s k D q : ℕ}
    (hk : 5 ≤ k) (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hq : q = Nat.sqrt (2 * H.edgeCount))
    (hB : s ≤ B)
    (hD : 2 ≤ D) (hnm : H.vertexCount ≤ H.edgeCount)
    (hlarge : 2 * D * (k * q) ≤ H.vertexCount)
    (hdensity : D * H.vertexCount ≤ (D - 1) * H.edgeCount)
    (hroom : OddMiddleRoom B s k H.edgeCount H.vertexCount q)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber (cycleCode k) Q ≤
        oddBudget B s Q.edgeCount)
    (C : SimpleGraph (Fin (oddBudget B s H.edgeCount)))
    [DecidableRel C.Adj]
    (hnoCycle : ¬ (cycleCode k).graph ⊑ C)
    (hnoH : ¬ H.graph ⊑ Cᶜ) : False := by
  classical
  let : DecidableRel H.graph.Adj := Classical.decRel _
  let : Nonempty (Fin H.vertexCount) := hconn.nonempty
  obtain ⟨v, hvmin⟩ := H.graph.exists_minimal_degree_vertex
  let δ := H.graph.degree v
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact (H.graph.degree_pos v).mpr (hH v)
  have hδle : δ ≤ H.edgeCount := by
    dsimp only [δ]
    calc
      H.graph.degree v ≤ H.graph.edgeFinset.card :=
        H.graph.degree_le_card_edgeFinset (v := v)
      _ = H.edgeCount := by rw [GraphCode.edgeCount_eq_card_edgeFinset]
  let Q := supportCode (deleteVertexCode H v)
  have hQedge : Q.edgeCount = H.edgeCount - δ := by
    dsimp only [Q]
    rw [supportCode_edgeCount, deleteVertexCode_edgeCount]
  have hQlt : Q.edgeCount < H.edgeCount := by
    rw [hQedge]
    omega
  have hQno : NoIsolated Q := supportCode_noIsolated _
  have hQram : graphRamseyNumber (cycleCode k) Q ≤
      oddBudget B s H.edgeCount := by
    exact (hIH Q hQno hQlt).trans (oddBudget_mono (by
      rw [hQedge]
      omega))
  have hQat : RamseyAt (cycleCode k) Q
      (oddBudget B s H.edgeCount) :=
    ramseyAt_of_graphRamseyNumber_le hQram
  have hvertexRoom : H.vertexCount - 1 ≤
      oddBudget B s H.edgeCount := by
    have hn := NoIsolated.vertexCount_le_twice_edgeCount hH
    unfold oddBudget
    omega
  obtain ⟨u, hpigeon⟩ :=
    exists_large_degree_of_ramseyAt_supported_delete
      (F := cycleCode k) C v hδpos hvertexRoom hQat hnoCycle hnoH
  have hdegreeSum : H.vertexCount * δ ≤ 2 * H.edgeCount := by
    have hmin : ∀ x : Fin H.vertexCount, δ ≤ H.graph.degree x := by
      intro x
      dsimp only [δ]
      rw [← hvmin]
      exact H.graph.minDegree_le_degree x
    calc
      H.vertexCount * δ = ∑ _x : Fin H.vertexCount, δ := by simp
      _ ≤ ∑ x : Fin H.vertexCount, H.graph.degree x := by
        exact Finset.sum_le_sum fun x _ ↦ hmin x
      _ = 2 * H.edgeCount := by
        rw [H.graph.sum_degrees_eq_twice_card_edges,
          ← GraphCode.edgeCount_eq_card_edgeFinset]
  have hhost : 2 * H.edgeCount ≤
      oddBudget B s H.edgeCount := by
    unfold oddBudget
    omega
  have huLarge : H.vertexCount / 2 + k * q ≤ C.degree u :=
    large_degree_of_pigeonhole hD hδpos hnm hlarge hdensity
      hdegreeSum hhost hpigeon
  let U₁ := C.neighborFinset u
  have hU₁lower : H.vertexCount / 2 + k * q ≤ U₁.card := by
    simpa [U₁] using huLarge
  have hcycleRaw : ¬ SimpleGraph.cycleGraph k ⊑ C := by
    simpa [cycleCode] using hnoCycle
  have hpath₁ : ¬ SimpleGraph.pathGraph (k - 1) ⊑
      C.induce (U₁ : Set (Fin (oddBudget B s H.edgeCount))) := by
    have hkpred : 2 ≤ k - 1 := by omega
    have hcycle' : ¬ SimpleGraph.cycleGraph ((k - 1) + 1) ⊑ C := by
      rw [show (k - 1) + 1 = k by omega]
      exact hcycleRaw
    have hset : (U₁ : Set (Fin (oddBudget B s H.edgeCount))) =
        C.neighborSet u := by
      ext x
      simp [U₁]
    rw [hset]
    exact
      pathGraph_not_isContained_neighbor_of_cycleGraph_not_isContained
        hkpred u hcycle'
  have hU₁upper : U₁.card < H.vertexCount + (k - 1) * q := by
    by_contra hnot
    have hsize : H.vertexCount + (k - 1) *
        Nat.sqrt (2 * H.edgeCount) ≤ U₁.card := by
      rw [← hq]
      exact Nat.le_of_not_gt hnot
    rcases Erdos570.RamseyAt.on_finset
        (ramseyAt_path_sqrt_edges (H := H) (by omega : 2 ≤ k - 1))
        C U₁ hsize with hred | hblue
    · exact hpath₁ (by simpa [pathCode] using hred)
    · exact hnoH (hblue.trans
        (SimpleGraph.Embedding.induce
          (U₁ : Set (Fin (oddBudget B s H.edgeCount)))).isContained)
  let P := secondNeighborFinset C u
  have hpathP : ¬ SimpleGraph.pathGraph (2 * k) ⊑
      C.induce (P : Set (Fin (oddBudget B s H.edgeCount))) := by
    have hset : (P : Set (Fin (oddBudget B s H.edgeCount))) =
        secondNeighborSet C u := by
      exact coe_secondNeighborFinset C u
    rw [hset]
    exact
      pathGraph_not_isContained_secondNeighbor_of_cycleGraph_not_isContained
        hk u hcycleRaw
  have hPupper : P.card < H.vertexCount + 2 * k * q := by
    by_contra hnot
    have hsize : H.vertexCount + (2 * k) *
        Nat.sqrt (2 * H.edgeCount) ≤ P.card := by
      rw [← hq]
      exact Nat.le_of_not_gt hnot
    rcases Erdos570.RamseyAt.on_finset
        (ramseyAt_path_sqrt_edges (H := H) (by omega : 2 ≤ 2 * k))
        C P hsize with hred | hblue
    · exact hpathP (by simpa [pathCode] using hred)
    · exact hnoH (hblue.trans
        (SimpleGraph.Embedding.induce
          (P : Set (Fin (oddBudget B s H.edgeCount)))).isContained)
  let removed := insert u (U₁ ∪ P)
  let U₂ := Finset.univ \ removed
  have huU₁ : u ∉ U₁ := by
    simp [U₁]
  have huP : u ∉ P := by
    simp [P, secondNeighborSet]
  have hU₁P : Disjoint U₁ P := by
    rw [Finset.disjoint_left]
    intro x hx₁ hxP
    have hxadj : C.Adj u x := by simpa [U₁] using hx₁
    have hxnot : ¬ C.Adj u x :=
      (mem_secondNeighborSet_iff.mp (by simpa [P] using hxP)).2.1
    exact hxnot hxadj
  have hremovedCard : removed.card = 1 + U₁.card + P.card := by
    dsimp only [removed]
    rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint hU₁P]
    · omega
    · simp [huU₁, huP]
  have hU₂card : U₂.card = oddBudget B s H.edgeCount -
      (1 + U₁.card + P.card) := by
    dsimp only [U₂]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ removed),
      Finset.card_univ, Fintype.card_fin, hremovedCard]
  have hU₁U₂ : Disjoint U₁ U₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hxnot := (Finset.mem_sdiff.mp hx₂).2
    exact hxnot (by simp [removed, hx₁])
  have hcross : ∀ x ∈ U₁, ∀ y ∈ U₂, Cᶜ.Adj x y := by
    intro x hx₁ y hy₂
    have hynot := (Finset.mem_sdiff.mp hy₂).2
    have hyu : y ≠ u := by
      intro hyu
      exact hynot (by simp [removed, hyu])
    have hynbr : ¬ C.Adj u y := by
      intro huy
      have hyU₁ : y ∈ U₁ := by simpa [U₁] using huy
      exact hynot (by simp [removed, hyU₁])
    have hxyne : x ≠ y := by
      intro hxy
      have hyU₁ : y ∈ U₁ := hxy ▸ hx₁
      exact hynot (by simp [removed, hyU₁])
    rw [SimpleGraph.compl_adj]
    refine ⟨hxyne, ?_⟩
    intro hxy
    have hyPset : y ∈ secondNeighborSet C u :=
      ⟨hyu, hynbr, ⟨x, by simpa [U₁] using hx₁, hxy⟩⟩
    have hyP : y ∈ P := by simpa [P] using hyPset
    exact hynot (by simp [removed, hyP])
  let r := H.vertexCount - U₁.card + k * q
  obtain ⟨hr2, hrn, hrU₂, hrEdges⟩ :=
    hroom U₁.card P.card hU₁lower hU₁upper hPupper
  have hU₁room : H.vertexCount - r + (k - 1) * q ≤ U₁.card := by
    dsimp only [r]
    have hkq : (k - 1) * q + q = k * q := by
      calc
        (k - 1) * q + q = (k - 1) * q + 1 * q := by simp
        _ = (k - 1 + 1) * q := by rw [Nat.add_mul]
        _ = k * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    omega
  have hm : 0 < H.edgeCount := hδpos.trans_le hδle
  apply odd_middle_partition_forces_target C (by omega) hB hm hq hnoCycle hnoH hIH
    U₁ U₂ hU₁U₂ hcross hpath₁ r hr2 hrn hU₁room
  · rw [hU₂card]
    exact hrU₂
  · rw [hU₂card]
    exact hrEdges

end Erdos570

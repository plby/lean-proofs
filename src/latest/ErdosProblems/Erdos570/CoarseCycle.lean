/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.EmbeddingNeighborhood
import ErdosProblems.Erdos570.CycleCode
import ErdosProblems.Erdos570.Neighborhood
import ErdosProblems.Erdos570.PathRamsey
import ErdosProblems.Erdos570.RamseyRegion

/-!
# A coarse cycle-versus-graph bound

The sparse-target argument only needs a deliberately rough bound for the
small core left after deleting leaves and suppressing long degree-two paths.
The proof here packages the minimum-degree deletion argument of Burr--Erdos--
Faudree--Rousseau--Schelp.  Our path bound makes the resulting estimate

`R(C_k,H) <= |H| + 2*k*e(H)`.

This is weaker than the displayed estimate in the paper, but is simpler and
has exactly the linear dependence needed by the reduction.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Giving every vertex a private color yields the crude path bound used in
the minimum-degree argument. -/
theorem ramseyAt_path_private_colors (H : GraphCode) {p : ℕ} (hp : 2 ≤ p) :
    RamseyAt (pathCode p) H
      (H.vertexCount + p * (H.vertexCount - 1)) := by
  classical
  intro C
  let color : H.graph.Coloring (Fin H.vertexCount) :=
    SimpleGraph.Coloring.mk id (by
      intro u v huv huvEq
      exact huv.ne huvEq)
  apply pathGraph_isContained_or_compl_of_coloring hp H.graph color C
  simp

/-- Convenient numerical consequence of the private-color path bound. -/
theorem graphRamseyNumber_path_le_mul_vertexCount
    (H : GraphCode) {p : ℕ} (hp : 2 ≤ p) :
    graphRamseyNumber (pathCode p) H ≤ (p + 1) * H.vertexCount := by
  apply graphRamseyNumber_le_of_ramseyAt
  exact (ramseyAt_path_private_colors H hp).mono_vertices (by
    have hsub : p * (H.vertexCount - 1) ≤ p * H.vertexCount :=
      Nat.mul_le_mul_left p (Nat.sub_le _ _)
    nlinarith)

/-- In a `C_k`-free host, the red neighborhood of any vertex is
`P_(k-1)`-free. -/
theorem path_pred_not_isContained_neighbor_of_cycle_not_isContained
    {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 3 ≤ k) (u : V)
    (hcycle : ¬ SimpleGraph.cycleGraph k ⊑ G) :
    ¬ SimpleGraph.pathGraph (k - 1) ⊑ G.induce (G.neighborSet u) := by
  have hkpred : 2 ≤ k - 1 := by omega
  have hkeq : k - 1 + 1 = k := by omega
  rw [← hkeq] at hcycle
  exact pathGraph_not_isContained_neighbor_of_cycleGraph_not_isContained
    hkpred u hcycle

/-- Coarse cycle-versus-target Ramsey bound.  The no-isolate hypothesis is
used only to make minimum-degree deletion strictly decrease the edge count;
isolates can always be discarded before applying the theorem. -/
theorem ramseyAt_cycle_coarse {k : ℕ} (hk : 3 ≤ k) :
    ∀ H : GraphCode, NoIsolated H →
      RamseyAt (cycleCode k) H
        (H.vertexCount + 2 * k * H.edgeCount) := by
  intro H hH
  suffices hmain : ∀ m : ℕ, ∀ Q : GraphCode, Q.edgeCount = m →
      NoIsolated Q → RamseyAt (cycleCode k) Q
        (Q.vertexCount + 2 * k * m) by
    simpa using hmain H.edgeCount H rfl hH
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro Q hQedge hQ
      subst m
      classical
      let N := Q.vertexCount + 2 * k * Q.edgeCount
      intro C
      letI : DecidableRel Q.graph.Adj := Classical.decRel _
      letI : DecidableRel C.Adj := Classical.decRel _
      by_cases hm : Q.edgeCount = 0
      · right
        have hzero : Q.vertexCount = 0 := by
          have hn := NoIsolated.vertexCount_le_twice_edgeCount hQ
          omega
        haveI : IsEmpty (Fin Q.vertexCount) := by
          rw [hzero]
          infer_instance
        exact SimpleGraph.IsContained.of_isEmpty
      have hmpos : 0 < Q.edgeCount := Nat.pos_of_ne_zero hm
      have hnpos : 0 < Q.vertexCount := by
        by_contra hn
        have : Q.vertexCount = 0 := Nat.eq_zero_of_not_pos hn
        have hedgeZero : Q.edgeCount = 0 := by
          haveI : IsEmpty (Fin Q.vertexCount) := by
            rw [this]
            infer_instance
          unfold GraphCode.edgeCount
          exact Nat.card_eq_zero.mpr (.inl inferInstance)
        exact hm hedgeZero
      letI : Nonempty (Fin Q.vertexCount) := Fin.pos_iff_nonempty.mp hnpos
      obtain ⟨v, hvmin⟩ := Q.graph.exists_minimal_degree_vertex
      let d := Q.graph.degree v
      have hdpos : 0 < d := by
        dsimp only [d]
        exact (Q.graph.degree_pos v).mpr (hQ v)
      let Q' := supportCode (deleteVertexCode Q v)
      have hQ'edge : Q'.edgeCount = Q.edgeCount - d := by
        dsimp only [Q']
        rw [supportCode_edgeCount, deleteVertexCode_edgeCount]
      have hQ'lt : Q'.edgeCount < Q.edgeCount := by
        rw [hQ'edge]
        omega
      have hQ'no : NoIsolated Q' := supportCode_noIsolated _
      have hQ'at0 : RamseyAt (cycleCode k) Q'
          (Q'.vertexCount + 2 * k * Q'.edgeCount) :=
        ih Q'.edgeCount hQ'lt Q' rfl hQ'no
      have hQ'v : Q'.vertexCount ≤ Q.vertexCount - 1 := by
        calc
          Q'.vertexCount ≤ (deleteVertexCode Q v).vertexCount :=
            (supportCode_isContained (deleteVertexCode Q v)).vertexCount_le
          _ = Q.vertexCount - 1 := deleteVertexCode_vertexCount Q v
      have hQ'room : Q'.vertexCount + 2 * k * Q'.edgeCount ≤ N := by
        dsimp only [N]
        rw [hQ'edge]
        exact Nat.add_le_add
          (hQ'v.trans (Nat.sub_le _ _))
          (Nat.mul_le_mul_left (2 * k) (Nat.sub_le _ _))
      have hQ'at : RamseyAt (cycleCode k) Q' N :=
        hQ'at0.mono_vertices hQ'room
      have hnroom : Q.vertexCount - 1 ≤ N := by
        dsimp only [N]
        omega
      by_cases hred : (cycleCode k).graph ⊑ C
      · exact Or.inl hred
      by_cases hblue : Q.graph ⊑ Cᶜ
      · exact Or.inr hblue
      obtain ⟨u, hu⟩ :=
        exists_large_degree_of_ramseyAt_supported_delete
          C v hdpos hnroom hQ'at hred hblue
      have hdegreeSum : Q.vertexCount * d ≤ 2 * Q.edgeCount := by
        have hmin : ∀ x : Fin Q.vertexCount, d ≤ Q.graph.degree x := by
          intro x
          dsimp only [d]
          rw [← hvmin]
          exact Q.graph.minDegree_le_degree x
        calc
          Q.vertexCount * d = ∑ _x : Fin Q.vertexCount, d := by simp
          _ ≤ ∑ x : Fin Q.vertexCount, Q.graph.degree x :=
            Finset.sum_le_sum fun x _ ↦ hmin x
          _ = 2 * Q.edgeCount := by
            rw [Q.graph.sum_degrees_eq_twice_card_edges,
              ← GraphCode.edgeCount_eq_card_edgeFinset]
      let R := Q.vertexCount + (k - 1) * (Q.vertexCount - 1)
      have hspare : d * (R - 1) + 1 ≤ N - (Q.vertexCount - 1) := by
        have hReq : R - 1 = k * (Q.vertexCount - 1) := by
          dsimp only [R]
          rw [Nat.add_comm Q.vertexCount,
            Nat.add_sub_assoc (by omega : 1 ≤ Q.vertexCount)]
          calc
            (k - 1) * (Q.vertexCount - 1) + (Q.vertexCount - 1) =
                (k - 1 + 1) * (Q.vertexCount - 1) := by ring
            _ = k * (Q.vertexCount - 1) := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
        have hmul := Nat.mul_le_mul_left k hdegreeSum
        have hleft : d * (R - 1) ≤ 2 * k * Q.edgeCount := by
          rw [hReq]
          calc
            d * (k * (Q.vertexCount - 1)) ≤ d * (k * Q.vertexCount) :=
              Nat.mul_le_mul_left d
                (Nat.mul_le_mul_left k (Nat.sub_le _ _))
            _ = k * (Q.vertexCount * d) := by ring
            _ ≤ k * (2 * Q.edgeCount) := hmul
            _ = 2 * k * Q.edgeCount := by ring
        have hNsub : N - (Q.vertexCount - 1) =
            2 * k * Q.edgeCount + 1 := by
          dsimp only [N]
          omega
        rw [hNsub]
        exact Nat.add_le_add_right hleft 1
      have hRdegree : R ≤ C.degree u := by
        by_contra hnot
        have hdeglt : C.degree u ≤ R - 1 := by omega
        have hmul : d * C.degree u ≤ d * (R - 1) :=
          Nat.mul_le_mul_left d hdeglt
        change N - (Q.vertexCount - 1) ≤ d * C.degree u at hu
        omega
      have hpathRamsey : RamseyAt (pathCode (k - 1)) Q R := by
        simpa [R] using ramseyAt_path_private_colors Q (by omega)
      let U := C.neighborFinset u
      rcases Erdos570.RamseyAt.on_finset hpathRamsey C U (by
          simpa [U] using hRdegree) with hpath | htarget
      · exfalso
        apply path_pred_not_isContained_neighbor_of_cycle_not_isContained
          hk u (by simpa [cycleCode] using hred)
        have hset : (U : Set (Fin N)) = C.neighborSet u := by
          ext x
          simp [U]
        rwa [← hset]
      · exfalso
        apply hblue
        exact htarget.trans
          (SimpleGraph.Embedding.induce
            (U : Set (Fin N))).isContained

/-- Numeric form of the coarse cycle bound. -/
theorem graphRamseyNumber_cycle_le_coarse
    {k : ℕ} (hk : 3 ≤ k) (H : GraphCode) (hH : NoIsolated H) :
    graphRamseyNumber (cycleCode k) H ≤
      H.vertexCount + 2 * k * H.edgeCount :=
  graphRamseyNumber_le_of_ramseyAt (ramseyAt_cycle_coarse hk H hH)

end Erdos570

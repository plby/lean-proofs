import ErdosProblems.Erdos88.BooleanSlices
import ErdosProblems.Erdos88.RobustRank

open scoped BigOperators

namespace Erdos88
namespace GraphQuadratic

open Classical

noncomputable def sym2Weight {V : Type*} (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) : Sym2 V → ℝ :=
  Sym2.lift ⟨w, hw⟩

@[simp] lemma sym2Weight_mk {V : Type*} (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (i j : V) :
    sym2Weight w hw s(i, j) = w i j := by
  rfl

lemma sum_adj_eq_sum_dart {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then w i j else 0) =
      ∑ d : G.Dart, w d.fst d.snd := by
  let e : (Σ i, G.neighborSet i) ≃ G.Dart :=
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩
      left_inv := by intro s; cases s; rfl
      right_inv := by intro d; cases d; rfl }
  calc
    (∑ i, ∑ j, if G.Adj i j then w i j else 0) =
        ∑ i, ∑ j : G.neighborSet i, w i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (G.Adj i))
        (by intro j; simp) (w i)
    _ = ∑ s : Σ i, G.neighborSet i, w s.1 s.2 := by
      rw [Fintype.sum_sigma]
    _ = ∑ d : G.Dart, w d.fst d.snd := by
      convert e.sum_comp (fun d : G.Dart => w d.fst d.snd) using 1 <;> rfl

lemma sum_dart_eq_two_mul_sum_edge {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → V → ℝ) (hw : ∀ i j, w i j = w j i) :
    (∑ d : G.Dart, w d.fst d.snd) =
      2 * ∑ e ∈ G.edgeFinset, sym2Weight w hw e := by
  let edgeOf : G.Dart → {e // e ∈ G.edgeFinset} :=
    fun d => ⟨d.edge, by simpa only [SimpleGraph.mem_edgeFinset] using d.edge_mem⟩
  rw [← Finset.sum_fiberwise Finset.univ edgeOf
    (fun d : G.Dart => w d.fst d.snd)]
  rw [Finset.mul_sum]
  rw [Finset.sum_subtype G.edgeFinset (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  rintro ⟨e, he⟩ _
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        exact G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
      let d : G.Dart := ⟨(u, v), huv⟩
      have hfiber :
          (Finset.univ.filter fun d' : G.Dart => edgeOf d' = edgeOf d) =
            {d, d.symm} := by
        ext d'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        simp only [edgeOf, Subtype.ext_iff]
        exact SimpleGraph.dart_edge_eq_iff d' d
      have hedge : edgeOf d = ⟨s(u, v), he⟩ := by
        apply Subtype.ext
        rfl
      rw [show (Finset.univ.filter fun d' : G.Dart =>
        edgeOf d' = ⟨s(u, v), he⟩) = {d, d.symm} by
          rw [← hedge]; exact hfiber]
      rw [Finset.sum_insert (by simpa using d.symm_ne.symm),
        Finset.sum_singleton]
      change w u v + w v u = 2 * sym2Weight w hw s(u, v)
      rw [sym2Weight_mk, ← hw u v]
      ring

noncomputable def graphSliceConstant {n : ℕ} (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) : ℝ :=
  e₀ + (G.edgeFinset.card : ℝ) / 4 + (∑ i, c i) / 2

noncomputable def graphSliceLinear {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) (i : Fin n) : ℝ :=
  c i / 2 + (G.degree i : ℝ) / 4

noncomputable def graphSliceMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fin n → Fin n → ℝ :=
  fun i j => (1 / 8 : ℝ) * RobustRank.graphAdjacencyMatrix G i j

lemma graphSliceMatrix_apply {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) :
    graphSliceMatrix G i j = if G.Adj i j then (1 / 8 : ℝ) else 0 := by
  by_cases hij : G.Adj i j <;>
    simp [graphSliceMatrix, RobustRank.graphAdjacencyMatrix, hij]

lemma graphSliceMatrix_symmetric {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : graphSliceMatrix G i j = graphSliceMatrix G j i := by
  rw [graphSliceMatrix_apply, graphSliceMatrix_apply]
  rw [G.adj_comm]

lemma sym2_signWeight_eq_walsh {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) :
    sym2Weight (fun i j => BooleanSlices.signOfSet W i *
        BooleanSlices.signOfSet W j) (fun i j => mul_comm _ _) e =
      Probability.walsh e.toFinset W := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      have hij : i ≠ j := by
        intro h
        subst j
        exact G.not_isDiag_of_mem_edgeFinset he rfl
      simp [Probability.walsh, Sym2.toFinset_mk_eq, hij,
        BooleanSlices.signOfSet, Probability.sign]

lemma quadraticPart_graphSliceMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) :
    BooleanSlices.quadraticPart (graphSliceMatrix G)
        (BooleanSlices.signOfSet W) = Probability.quadraticWalsh G W := by
  let w : Fin n → Fin n → ℝ := fun i j =>
    BooleanSlices.signOfSet W i * BooleanSlices.signOfSet W j
  have hw : ∀ i j, w i j = w j i := fun i j => mul_comm _ _
  rw [BooleanSlices.quadraticPart, Probability.quadraticWalsh]
  simp_rw [graphSliceMatrix_apply]
  have hadj := sum_adj_eq_sum_dart G w
  have hedge := sum_dart_eq_two_mul_sum_edge G w hw
  calc
    (∑ i, ∑ j, (BooleanSlices.signOfSet W i *
        (if G.Adj i j then (1 / 8 : ℝ) else 0)) *
          BooleanSlices.signOfSet W j) =
        (1 / 8 : ℝ) *
          (∑ i, ∑ j, if G.Adj i j then w i j else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            dsimp only [w]
            by_cases hij : G.Adj i j <;> simp [hij] <;> ring
    _ = (1 / 8 : ℝ) * ∑ d : G.Dart, w d.fst d.snd := by rw [hadj]
    _ = (1 / 8 : ℝ) *
        (2 * ∑ e ∈ G.edgeFinset, sym2Weight w hw e) := by rw [hedge]
    _ = (1 / 4 : ℝ) * ∑ e ∈ G.edgeFinset,
        Probability.walsh e.toFinset W := by
      have hsum : (∑ e ∈ G.edgeFinset, sym2Weight w hw e) =
          ∑ e ∈ G.edgeFinset, Probability.walsh e.toFinset W := by
        apply Finset.sum_congr rfl
        intro e he
        exact sym2_signWeight_eq_walsh G W e he
      rw [hsum]
      ring
    _ = (1 / 4 : ℝ) * ∑ e ∈ G.edgeFinset,
        Probability.walsh e.toFinset W := rfl

lemma sliceQuadratic_graph_coefficients {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (W : Finset (Fin n)) :
    BooleanSlices.sliceQuadratic (graphSliceConstant G e₀ c)
        (graphSliceLinear G c) (graphSliceMatrix G) W =
      Probability.perturbedEdgePolynomial G e₀ c W := by
  rw [Probability.perturbedEdgePolynomial_walsh]
  rw [BooleanSlices.sliceQuadratic, BooleanSlices.quadraticPolynomial,
    graphSliceConstant]
  have hlin : BooleanSlices.linearPart (graphSliceLinear G c)
      (BooleanSlices.signOfSet W) = Probability.linearWalsh G c W := by
    simp only [BooleanSlices.linearPart, graphSliceLinear,
      Probability.linearWalsh, BooleanSlices.signOfSet, Probability.sign]
  rw [hlin, quadraticPart_graphSliceMatrix]

lemma graphSliceMatrix_abs_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : |graphSliceMatrix G i j| ≤ 1 := by
  rw [graphSliceMatrix_apply]
  split <;> norm_num

lemma graphSliceLinear_nonneg {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (i : Fin n) :
    0 ≤ graphSliceLinear G c i := by
  dsimp only [graphSliceLinear]
  exact add_nonneg (div_nonneg (hc i) (by norm_num))
    (div_nonneg (by positivity) (by norm_num))

end GraphQuadratic
end Erdos88

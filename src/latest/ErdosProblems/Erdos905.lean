/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 905.
https://www.erdosproblems.com/forum/thread/905

Informal authors:
- N. G. Khadzhiivanov
- S. V. Nikiforov

Formal authors:
- Aristotle
- GPT 5.4
- Andres Gutierrez

URLs:
- https://www.erdosproblems.com/forum/thread/905#post-5276
-/
import Mathlib

namespace Erdos905


set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.maxHeartbeats false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Erdős Problem 905

*Reference:* [erdosproblems.com/905](https://www.erdosproblems.com/905)

Conjecture of Bollobás and Erdős, proved independently by Edwards (unpublished)
and Khadžiivanov-Nikiforov [KhNi79], with a cleaner proof by Bollobás-Nikiforov [BoNi04].

[KhNi79] N. Khadžiivanov and V. Nikiforov, *Solution of a problem of P. Erdős about the maximum
number of triangles with a common edge in a graph*, C. R. Acad. Bulgare Sci. **32** (1979),
1315-1318.

[BoNi04] B. Bollobás and V. Nikiforov, *Books in graphs*, arXiv:math/0405080, Eur. J. Combin.

## Proof roadmap

For a graph `G` on `n` vertices, write `t(e)` for the number of triangles through
an edge `e`, and `β` for the maximum of `t(e)` over all edges.

The formalization follows the Bollobás-Nikiforov route:

1. Prove a soft degree inequality for each edge, giving the easy case
   `n ≤ 3β`.
2. In the hard case, count "concordant" pairs `(T, y)` of a triangle `T` and a
   vertex `y`, obtaining the Khadžiivanov-Nikiforov inequality.
3. Combine that inequality with Cauchy-Schwarz, the handshaking lemma, and the
   Turán bound `m > n^2 / 4` to deduce `n < 6β`.
4. Choose an edge attaining `β`.
-/

open SimpleGraph

namespace ErdosProblems.P905

variable {V : Type*} [Fintype V]

/--
For an edge `e = s(u, v)` in a simple graph `G`, the
**triangle-degree** of `e` is the number of vertices `w` adjacent to
both `u` and `v`, i.e., the number of triangles containing `e`. -/
noncomputable def triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  Sym2.lift
    ⟨fun u v => Fintype.card (G.commonNeighbors u v),
     fun u v => by simp [G.commonNeighbors_symm]⟩ e

/-- Evaluates `triangleDegree` at a concrete pair. -/
theorem triangleDegree_mk
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    triangleDegree G s(u, v) =
      Fintype.card (G.commonNeighbors u v) := by
  simp [triangleDegree, Sym2.lift_mk]

/-- Triangle-degree is symmetric. -/
theorem triangleDegree_symm
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    triangleDegree G s(u, v) = triangleDegree G s(v, u) := by
  simp [triangleDegree_mk, G.commonNeighbors_symm]

/-- The maximum triangle-degree of an edge of `G`. -/
noncomputable def maxTriangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.sup (triangleDegree G)

/-- An edge attains `maxTriangleDegree`. -/
theorem exists_mem_edgeFinset_triangleDegree_eq_maxTriangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) :
    ∃ e ∈ G.edgeFinset,
      triangleDegree G e = maxTriangleDegree G := by
  obtain ⟨e, he⟩ :
      ∃ e ∈ G.edgeFinset,
        ∀ e' ∈ G.edgeFinset,
          triangleDegree G e' ≤ triangleDegree G e :=
    Finset.exists_max_image _ _ hne
  exact ⟨e, he.1, le_antisymm
    (Finset.le_sup (f := triangleDegree G) he.1)
    (Finset.sup_le fun e' he' => he.2 e' he')⟩

/-! ### Helper lemmas for the Bollobás-Nikiforov inequality -/

/-
Per-edge bound: `d(u) + d(v) ≤ n + t(e)`.
This is inclusion-exclusion on the union of the two neighborhoods.
-/
lemma degree_add_degree_le_card_add_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    G.degree u + G.degree v ≤
      Fintype.card V + Fintype.card (G.commonNeighbors u v) := by
  classical
  calc
    G.degree u + G.degree v
        = (G.neighborFinset u ∪ G.neighborFinset v).card +
            (G.neighborFinset u ∩ G.neighborFinset v).card := by
          change (G.neighborFinset u).card + (G.neighborFinset v).card =
            (G.neighborFinset u ∪ G.neighborFinset v).card +
              (G.neighborFinset u ∩ G.neighborFinset v).card
          exact (Finset.card_union_add_card_inter
            (G.neighborFinset u) (G.neighborFinset v)).symm
    _ ≤ Fintype.card V + (G.neighborFinset u ∩ G.neighborFinset v).card := by
          exact Nat.add_le_add_right (Finset.card_le_univ _) _
    _ = Fintype.card V + Fintype.card (G.commonNeighbors u v) := by
          congr 1
          rw [← Set.toFinset_card]
          congr
          ext x
          simp [SimpleGraph.commonNeighbors]

/-
Easy case of the Bollobás-Nikiforov inequality: when `n ≤ 3 * f₃`,
the per-edge bound `d(u) + d(v) ≤ n + f₃` is enough by summing over edges.
-/
lemma bollobas_nikiforov_of_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_case : Fintype.card V ≤ 3 * maxTriangleDegree G) :
    3 * ∑ v : V, G.degree v ^ 2 ≤
      6 * G.edgeFinset.card * maxTriangleDegree G +
        2 * Fintype.card V * G.edgeFinset.card := by
  have h_edges := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h_per_edge :
      ∀ u v, G.Adj u v →
        G.degree u + G.degree v ≤ Fintype.card V + maxTriangleDegree G := by
    intro u v huv
    have h_common :
        G.degree u + G.degree v ≤
          Fintype.card V + Fintype.card (G.commonNeighbors u v) := by
      exact degree_add_degree_le_card_add_commonNeighbors G u v
    have h_card_le_max : Fintype.card (G.commonNeighbors u v) ≤ maxTriangleDegree G := by
      convert Finset.le_sup (f := triangleDegree G)
        (show s(u, v) ∈ G.edgeFinset from by aesop) using 1
    grind +revert
  have h_sum_per_edge :
      ∑ u ∈ Finset.univ, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) ≤
        G.edgeFinset.card * (Fintype.card V + maxTriangleDegree G) * 2 := by
    have h_sum_per_edge :
        ∑ u ∈ Finset.univ, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) ≤
          ∑ u ∈ Finset.univ, ∑ v ∈ G.neighborFinset u,
            (Fintype.card V + maxTriangleDegree G) := by
      exact Finset.sum_le_sum fun u _ =>
        Finset.sum_le_sum fun v hv => h_per_edge u v <| by aesop
    have h_const_sum :
        ∑ u ∈ Finset.univ, ∑ v ∈ G.neighborFinset u,
          (Fintype.card V + maxTriangleDegree G) =
          G.edgeFinset.card * (Fintype.card V + maxTriangleDegree G) * 2 := by
      calc
        ∑ u ∈ Finset.univ, ∑ v ∈ G.neighborFinset u,
            (Fintype.card V + maxTriangleDegree G)
            = (Fintype.card V + maxTriangleDegree G) * ∑ u : V, G.degree u := by
              calc
                ∑ u ∈ Finset.univ, ∑ v ∈ G.neighborFinset u,
                    (Fintype.card V + maxTriangleDegree G)
                    = ∑ u : V, G.degree u * (Fintype.card V + maxTriangleDegree G) := by
                      simp
                _ = (Fintype.card V + maxTriangleDegree G) * ∑ u : V, G.degree u := by
                      rw [Finset.mul_sum]
                      simp [mul_comm]
        _ = (Fintype.card V + maxTriangleDegree G) * (2 * G.edgeFinset.card) := by
              rw [h_edges]
        _ = G.edgeFinset.card * (Fintype.card V + maxTriangleDegree G) * 2 := by
              ring
    exact h_sum_per_edge.trans_eq h_const_sum
  have h_handshake :
      ∑ x, ∑ y ∈ G.neighborFinset x, G.degree y = ∑ x, G.degree x * G.degree x := by
    simp_rw [SimpleGraph.neighborFinset_eq_filter]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [SimpleGraph.adj_comm]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [← Finset.sum_filter]
    rw [← SimpleGraph.neighborFinset_eq_filter (G := G) (v := x)]
    rw [Finset.sum_const_nat (m := G.degree x) (f := fun _ => G.degree x)]
    · rfl
    · intro y hy
      rfl
  simp_all +decide [Finset.sum_add_distrib, pow_two]
  nlinarith

/-! ### Infrastructure for the hard case (Bollobás-Nikiforov Section 2) -/

/-
Summing triangle-degrees over all edges gives at most `β * m`.
-/
lemma sum_triangleDegree_le_maxTriangleDegree_mul_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, triangleDegree G e ≤
      maxTriangleDegree G * G.edgeFinset.card := by
  -- Since `triangleDegree G e ≤ maxTriangleDegree G` for all
  -- `e ∈ G.edgeFinset`, we can apply the sum inequality.
  have h_le_sup : ∀ e ∈ G.edgeFinset, triangleDegree G e ≤ maxTriangleDegree G := by
    exact fun e he => Finset.le_sup (f := triangleDegree G) he
  simpa [mul_comm] using Finset.sum_le_sum h_le_sup

/-
If `m > n²/4` then `G` has a triangle, hence `maxTriangleDegree G > 0`.
-/
lemma maxTriangleDegree_pos_of_quarter_sq_lt_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    0 < maxTriangleDegree G := by
  contrapose! h
  have h_triangle_free : G.CliqueFree 3 := by
    intro T hT
    have h_adj : ∀ u v : V, u ∈ T → v ∈ T → u ≠ v → G.Adj u v := by
      exact fun u v hu hv huv => hT.1 hu hv huv
    have h_triangle_degree_pos : ∀ u v : V, u ∈ T → v ∈ T → u ≠ v → 1 ≤ triangleDegree G s(u, v) := by
      intro u v hu hv huv
      have h_common_neighbor : ∃ w : V, w ∈ T ∧ w ≠ u ∧ w ≠ v := by
        have := Finset.two_lt_card.1 (by linarith [hT.2])
        grind
      obtain ⟨w, hwT, hwu, hwv⟩ := h_common_neighbor
      refine Fintype.card_pos_iff.mpr ?_
      exact ⟨w, h_adj _ _ hu hwT (by tauto), h_adj _ _ hv hwT (by tauto)⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by linarith [hT.card_eq])
    exact not_lt_of_ge h
      (lt_of_lt_of_le (h_triangle_degree_pos u v hu hv huv)
        (Finset.le_sup (f := triangleDegree G) (by aesop)))
  convert SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) h_triangle_free using 1
  cases Nat.mod_two_eq_zero_or_one (Fintype.card V) <;> simp +decide [*]
  rw [← Nat.mod_add_div (Fintype.card V) 2, ‹Fintype.card V % 2 = _›]
  ring_nf
  grind +splitImp

/-
The sum of triangle-degrees is `3` times the number of triangles.
-/
lemma sum_triangleDegree_eq_three_mul_cliqueFinset [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, triangleDegree G e = 3 * (G.cliqueFinset 3).card := by
  -- Count incidences `(edge of a triangle)` in two ways:
  -- once by summing the number of common neighbors of each edge,
  -- and once by observing that every triangle contributes exactly three edges.
  unfold triangleDegree
  simp +decide [SimpleGraph.cliqueFinset]
  convert Finset.sum_congr rfl fun e he => ?_
  rotate_left
  use fun e =>
    ∑ T ∈ Finset.filter (fun T => G.IsNClique 3 T) Finset.univ,
      if e ∈ Finset.image (fun p : V × V => s(p.1, p.2)) (Finset.offDiag T) then 1 else 0
  · rcases e with ⟨u, v⟩
    simp +decide [SimpleGraph.commonNeighbors]
    refine Finset.card_bij (fun w _hw => {u, v, (w : V)}) ?_ ?_ ?_ <;>
      simp_all +decide [SimpleGraph.isNClique_iff]
    · intro w hu hv
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] <;> aesop
    · simp +contextual [Finset.Subset.antisymm_iff, Finset.subset_iff]
      aesop
    · intro b hb hb' x y hx hy hxy h
      obtain ⟨a, ha⟩ := Finset.card_eq_three.mp hb'
      simp_all +decide [SimpleGraph.IsClique]
      rcases ha with ⟨y, hy, z, hz, hyz, rfl⟩
      simp_all +decide
      grind +suggestions
  · rw [Finset.sum_comm, Finset.sum_congr rfl]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
    simp +decide [SimpleGraph.isNClique_iff]
    intro x hx hx'
    rw [Finset.card_eq_three] at hx'
    obtain ⟨a, b, c, hab, hbc, hac⟩ := hx'
    simp_all +decide [SimpleGraph.isClique_iff]
    rw [Finset.card_eq_three]
    use s(a, b), s(a, c), s(b, c)
    simp +decide [*, Finset.ext_iff]
    intro e
    constructor <;> intro he <;> rcases e with ⟨u, v⟩ <;> simp_all +decide
    · grind
    · rcases he with
      ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp_all +decide [SimpleGraph.adj_comm]
      exacts [⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩,
        ⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩, ⟨u, v, by aesop⟩]

/-- For each edge `e`, the concordant count `a(e) = n + 2t(e) - d(u) - d(v)`
satisfies `d(u) + d(v) ≤ n + 2 * t(e)` (i.e., `a(e) ≥ 0`).
This strengthens `degree_add_degree_le_card_add_commonNeighbors` by a factor of 2. -/
lemma degree_add_degree_le_card_add_two_mul_triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    G.degree u + G.degree v ≤
      Fintype.card V + 2 * Fintype.card (G.commonNeighbors u v) := by
  have := degree_add_degree_le_card_add_commonNeighbors G u v
  omega

lemma commonNeighbors_card_eq_triangleDegree_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] (e : Sym2 V) :
    (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
      (Finset.univ : Finset V)).card = triangleDegree G e := by
  convert triangleDegree_mk G (Quot.out e).1 (Quot.out e).2 using 1
  · convert rfl
    convert triangleDegree_mk G (Quot.out e).1 (Quot.out e).2 using 1
    rw [Fintype.card_of_subtype]
    aesop
  · exact congr_arg _ (by exact Eq.symm (Quot.out_eq e))

lemma edge_degree_add_degree_le_card_add_two_mul_triangleDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] (e : Sym2 V) :
    G.degree e.out.1 + G.degree e.out.2 ≤
      Fintype.card V + 2 * triangleDegree G e := by
  have h_deg := degree_add_degree_le_card_add_two_mul_triangleDegree G e.out.1 e.out.2
  have h_card :
      Fintype.card (G.commonNeighbors e.out.1 e.out.2) = triangleDegree G e := by
    rw [← commonNeighbors_card_eq_triangleDegree_edge G e]
    exact Fintype.card_of_finset'
      (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
        (Finset.univ : Finset V))
      (by simp)
  omega

/-! ### Endpoint-degree identities -/

lemma edge_endpoint_degree_sum_eq_indicator_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] :
    ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) =
      ∑ v : V, ∑ e ∈ G.edgeFinset, (if v ∈ e then G.degree v else 0) := by
  classical
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro e he
  have h_edge_repr : e = s(e.out.1, e.out.2) := by
    exact Eq.symm (Quot.out_eq e)
  rw [h_edge_repr, Finset.sum_ite]
  rw [Finset.sum_eq_add (Quot.out e |>.1) (Quot.out e |>.2)] <;> simp +decide
  · rw [← h_edge_repr]
  · intro h
    rw [h_edge_repr] at he
    simp +decide [h] at he

lemma edge_endpoint_degree_sum_eq_neighbor_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] :
    ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) =
      ∑ v : V, ∑ _ ∈ G.neighborFinset v, G.degree v := by
  classical
  rw [edge_endpoint_degree_sum_eq_indicator_sum]
  refine Finset.sum_congr rfl ?_
  intro v hv
  calc
    (∑ e ∈ G.edgeFinset, if v ∈ e then G.degree v else 0)
        = ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), G.degree v := by
            rw [Finset.sum_filter]
    _ = ∑ e ∈ G.incidenceFinset v, G.degree v := by
          rw [SimpleGraph.incidenceFinset_eq_filter]
    _ = G.degree v * G.degree v := by
          rw [Finset.sum_const_nat (m := G.degree v) (f := fun _ => G.degree v)]
          · rw [SimpleGraph.card_incidenceFinset_eq_degree, mul_comm]
          · intro x hx
            rfl
    _ = ∑ u ∈ G.neighborFinset v, G.degree v := by
          rw [Finset.sum_const_nat (m := G.degree v) (f := fun _ => G.degree v)]
          · rw [SimpleGraph.degree, mul_comm]
          · intro x hx
            rfl

lemma edge_endpoint_degree_sum_eq_sum_sq
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] :
    ∑ e ∈ G.edgeFinset, (G.degree e.out.1 + G.degree e.out.2) =
      ∑ v : V, G.degree v ^ 2 := by
  simp +decide [edge_endpoint_degree_sum_eq_neighbor_sum, pow_two]

/--
For a fixed edge `e = s(u, v)`, the number of vertices whose adjacency pattern to
`u, v` is concordant is at most `n + 2t(e) - d(u) - d(v)`.

This is the finite-set version of the inclusion-exclusion estimate used in the
Bollobás-Nikiforov counting argument.
-/
lemma concordant_vertex_count_le_card_add_two_mul_triangleDegree_sub_degree [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) :
    (Finset.filter
        (fun y =>
          y ∈ G.commonNeighbors e.out.1 e.out.2 ∨
            (¬G.Adj y e.out.1 ∧ ¬G.Adj y e.out.2))
        (Finset.univ : Finset V)).card ≤
      Fintype.card V + 2 * triangleDegree G e -
        G.degree e.out.1 - G.degree e.out.2 := by
  have concordant_split_bound :
      (Finset.filter
          (fun y =>
            y ∈ G.commonNeighbors e.out.1 e.out.2 ∨
              (¬G.Adj y e.out.1 ∧ ¬G.Adj y e.out.2))
          (Finset.univ : Finset V)).card ≤
        (Finset.univ : Finset V).card -
          (Finset.filter (fun y => G.Adj y e.out.1 ∨ G.Adj y e.out.2)
            (Finset.univ : Finset V)).card +
          (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
            (Finset.univ : Finset V)).card := by
    rw [tsub_add_eq_add_tsub]
    · refine' le_tsub_of_add_le_left _
      rw [← Finset.card_union_add_card_inter]
      refine' add_le_add _ _
      · exact Finset.card_le_univ _
      · refine' Finset.card_le_card _
        intro y hy
        aesop
    · exact Finset.card_le_univ _
  have union_neighbors_card_ge :
      (Finset.filter (fun y => G.Adj y e.out.1 ∨ G.Adj y e.out.2)
        (Finset.univ : Finset V)).card ≥
        G.degree e.out.1 + G.degree e.out.2 -
          (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
            (Finset.univ : Finset V)).card := by
    have union_inclusion_exclusion :
        (Finset.filter (fun y => G.Adj y e.out.1 ∨ G.Adj y e.out.2)
          (Finset.univ : Finset V)).card ≥
          (Finset.filter (fun y => G.Adj y e.out.1) (Finset.univ : Finset V)).card +
            (Finset.filter (fun y => G.Adj y e.out.2) (Finset.univ : Finset V)).card -
            (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
              (Finset.univ : Finset V)).card := by
      rw [← Finset.card_union_add_card_inter]
      simp +decide [SimpleGraph.commonNeighbors]
      simp +decide [Finset.filter_or, Finset.filter_and, SimpleGraph.adj_comm]
    have h_deg_left :
        (Finset.filter (fun y => G.Adj y e.out.1) (Finset.univ : Finset V)).card =
          G.degree e.out.1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := e.out.1)]
      rw [SimpleGraph.neighborFinset_eq_filter]
      simp [SimpleGraph.adj_comm]
    have h_deg_right :
        (Finset.filter (fun y => G.Adj y e.out.2) (Finset.univ : Finset V)).card =
          G.degree e.out.2 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := e.out.2)]
      rw [SimpleGraph.neighborFinset_eq_filter]
      simp [SimpleGraph.adj_comm]
    simpa [h_deg_left, h_deg_right] using union_inclusion_exclusion
  have commonNeighbors_card_eq_triangleDegree :
      (Finset.filter (fun y => y ∈ G.commonNeighbors e.out.1 e.out.2)
        (Finset.univ : Finset V)).card = triangleDegree G e := by
    exact commonNeighbors_card_eq_triangleDegree_edge G e
  have h_univ_card : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have h_degree_bound :
      G.degree e.out.1 + G.degree e.out.2 ≤
        Fintype.card V + 2 * triangleDegree G e := by
    exact edge_degree_add_degree_le_card_add_two_mul_triangleDegree G e
  have h_union_le_univ :
      (Finset.filter (fun y => G.Adj y e.out.1 ∨ G.Adj y e.out.2)
        (Finset.univ : Finset V)).card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ
      (Finset.filter (fun y => G.Adj y e.out.1 ∨ G.Adj y e.out.2)
        (Finset.univ : Finset V))
  omega

lemma concordant_pair_out
    (G : SimpleGraph V) (y a b : V) :
    ((G.Adj y a ∧ G.Adj y b) ∨ (¬ G.Adj y a ∧ ¬ G.Adj y b)) →
      y ∈ G.commonNeighbors (s(a, b)).out.1 (s(a, b)).out.2 ∨
        (¬ G.Adj y (s(a, b)).out.1 ∧ ¬ G.Adj y (s(a, b)).out.2) := by
  intro h
  have hout := Quot.out_eq (s(a, b))
  rcases (Sym2.eq_iff.mp hout) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : (s(a, b)).out.1 = a := by simpa using h1
    have h2' : (s(a, b)).out.2 = b := by simpa using h2
    rw [h1', h2']
    simpa [SimpleGraph.commonNeighbors, SimpleGraph.adj_comm] using h
  · have h1' : (s(a, b)).out.1 = b := by simpa using h1
    have h2' : (s(a, b)).out.2 = a := by simpa using h2
    rw [h1', h2']
    simpa [SimpleGraph.commonNeighbors, SimpleGraph.adj_comm, and_comm] using h

/-
Core injection-based counting bound, extracted from Bollobás-Nikiforov Theorem 1.

In the notation
`k₃ = (cliqueFinset 3).card`, `D = ∑ d(v)^2`, `S = ∑ t(e)`, and
`β = maxTriangleDegree`, the bound is
`n * k₃ + β * D ≤ β * n * m + 2 * β * S`.
-/
-- This proof contains the main finite-set encoding of the combinatorial
-- injection. The heartbeat bump avoids timeouts in the large `simp`/`grind`
-- blocks handling `Sym2` and filtered products.
set_option maxHeartbeats 800000 in
lemma injection_counting_bound [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueFinset 3).card * Fintype.card V +
      maxTriangleDegree G * ∑ v : V, G.degree v ^ 2 ≤
    maxTriangleDegree G * Fintype.card V * G.edgeFinset.card +
      2 * maxTriangleDegree G * ∑ e ∈ G.edgeFinset, triangleDegree G e := by
  revert G
  have injection_inequality (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V * (G.cliqueFinset 3).card ≤
      ∑ e ∈ G.edgeFinset, (triangleDegree G e) *
        (Fintype.card V + 2 * (triangleDegree G e) - G.degree e.out.1 - G.degree e.out.2) := by
    have exists_concordant_edge :
        ∀ T ∈ G.cliqueFinset 3, ∀ y : V,
          ∃ e ∈ G.edgeFinset,
            e ∈ T.sym2 ∧
              (y ∈ G.commonNeighbors e.out.1 e.out.2 ∨
                (¬G.Adj y e.out.1 ∧ ¬G.Adj y e.out.2)) := by
      intro T hT y
      obtain ⟨u, v, w, hu, hv, hw, hT⟩ :
          ∃ u v w : V, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ T = {u, v, w} ∧
            G.Adj u v ∧ G.Adj u w ∧ G.Adj v w := by
        simp_all +decide [SimpleGraph.isNClique_iff]
        rcases Finset.card_eq_three.mp hT.2 with ⟨u, v, w, hu, hv, hw, h⟩
        use u, v, by aesop, w
        aesop
      obtain ⟨e, he⟩ :
          ∃ e ∈ ({s(u, v), s(u, w), s(v, w)} : Finset (Sym2 V)),
            (y ∈ G.commonNeighbors e.out.1 e.out.2 ∨
              (¬G.Adj y e.out.1 ∧ ¬G.Adj y e.out.2)) := by
        by_cases huv_y : (G.Adj y u ↔ G.Adj y v)
        · refine ⟨s(u, v), by simp, concordant_pair_out G y u v ?_⟩
          by_cases hyu : G.Adj y u
          · exact Or.inl ⟨hyu, huv_y.mp hyu⟩
          · exact Or.inr ⟨hyu, fun hyv => hyu (huv_y.mpr hyv)⟩
        · by_cases huw_y : (G.Adj y u ↔ G.Adj y w)
          · refine ⟨s(u, w), by simp, concordant_pair_out G y u w ?_⟩
            by_cases hyu : G.Adj y u
            · exact Or.inl ⟨hyu, huw_y.mp hyu⟩
            · exact Or.inr ⟨hyu, fun hyw => hyu (huw_y.mpr hyw)⟩
          · have hvw_y : G.Adj y v ↔ G.Adj y w := by
              by_cases hyu : G.Adj y u <;>
                by_cases hyv : G.Adj y v <;>
                by_cases hyw : G.Adj y w <;>
                simp_all
            refine ⟨s(v, w), by simp, concordant_pair_out G y v w ?_⟩
            by_cases hyv : G.Adj y v
            · exact Or.inl ⟨hyv, hvw_y.mp hyv⟩
            · exact Or.inr ⟨hyv, fun hyw => hyv (hvw_y.mpr hyw)⟩
      refine' ⟨e, _, _, he.2⟩ <;> simp_all +decide [SimpleGraph.edgeSet]
      · rcases he.1 with (rfl | rfl | rfl) <;> simp +decide [*, SimpleGraph.edgeSetEmbedding]
      · rcases he.1 with (rfl | rfl | rfl) <;> simp +decide [Sym2.mem_iff]
    have concordant_pair_count_le :
        ∀ e ∈ G.edgeFinset,
          (Finset.filter
              (fun p =>
                e ∈ p.1.sym2 ∧
                  (p.2 ∈ G.commonNeighbors e.out.1 e.out.2 ∨
                    (¬G.Adj p.2 e.out.1 ∧ ¬G.Adj p.2 e.out.2)))
              (G.cliqueFinset 3 ×ˢ Finset.univ)).card ≤
              (triangleDegree G e) *
              (Fintype.card V + 2 * (triangleDegree G e) -
                G.degree e.out.1 - G.degree e.out.2) := by
      intro e he
      have concordant_vertex_count_le :=
        concordant_vertex_count_le_card_add_two_mul_triangleDegree_sub_degree G e
      have triangle_count_through_edge_le :
          (Finset.filter (fun T => e ∈ T.sym2) (G.cliqueFinset 3)).card ≤
            triangleDegree G e := by
        rcases e with ⟨u, v⟩
        simp +decide [triangleDegree_mk]
        have triangle_to_commonNeighbor :
            Finset.filter (fun T => u ∈ T ∧ v ∈ T) (G.cliqueFinset 3) ⊆
              Finset.image (fun w => {u, v, w})
                (Finset.filter (fun w => G.Adj u w ∧ G.Adj v w) Finset.univ) := by
          simp +decide [Finset.subset_iff]
          intro T hT hu hv
          have := Finset.card_eq_three.mp hT.2
          obtain ⟨a, b, c, hab, hbc, hac⟩ := this
          simp_all +decide [SimpleGraph.isNClique_iff]
          rcases hu with (rfl | rfl | rfl) <;> rcases hv with (rfl | rfl | rfl) <;>
            simp_all +decide [SimpleGraph.adj_comm]
          grind
          · grind
          · grind
          · grind
          · grind
          · grind
        refine' le_trans (Finset.card_le_card triangle_to_commonNeighbor) _
        refine le_trans Finset.card_image_le ?_
        exact le_of_eq <| (Fintype.card_of_finset'
          (Finset.filter (fun w => G.Adj u w ∧ G.Adj v w) (Finset.univ : Finset V))
          (by simp [SimpleGraph.commonNeighbors])).symm
      refine' le_trans _ (Nat.mul_le_mul triangle_count_through_edge_le concordant_vertex_count_le)
      rw [← Finset.card_product]
      exact Finset.card_le_card fun p hp => by aesop
    have total_pair_count_le :
        (Finset.univ : Finset V).card * (G.cliqueFinset 3).card ≤
          ∑ e ∈ G.edgeFinset,
            (Finset.filter
              (fun p =>
                e ∈ p.1.sym2 ∧
                  (p.2 ∈ G.commonNeighbors e.out.1 e.out.2 ∨
                    (¬G.Adj p.2 e.out.1 ∧ ¬G.Adj p.2 e.out.2)))
              (G.cliqueFinset 3 ×ˢ Finset.univ)).card := by
      have product_card_le_biUnion_card :
          (Finset.univ : Finset V).card * (G.cliqueFinset 3).card ≤
            (Finset.biUnion G.edgeFinset
              (fun e =>
                Finset.filter
                  (fun p =>
                    e ∈ p.1.sym2 ∧
                      (p.2 ∈ G.commonNeighbors e.out.1 e.out.2 ∨
                        (¬G.Adj p.2 e.out.1 ∧ ¬G.Adj p.2 e.out.2)))
                  (G.cliqueFinset 3 ×ˢ Finset.univ))).card := by
        rw [mul_comm, ← Finset.card_product]
        exact Finset.card_le_card fun p hp => by
          obtain ⟨e, he₁, he₂, he₃⟩ :=
            exists_concordant_edge p.1 (Finset.mem_product.mp hp |>.1) p.2
          aesop
      exact product_card_le_biUnion_card.trans (Finset.card_biUnion_le)
    exact total_pair_count_le.trans (Finset.sum_le_sum concordant_pair_count_le)
  have weighted_concordant_sum_le (G : SimpleGraph V) [DecidableRel G.Adj] :
      ∑ e ∈ G.edgeFinset, (triangleDegree G e) *
        (Fintype.card V + 2 * (triangleDegree G e) - G.degree e.out.1 - G.degree e.out.2) ≤
      maxTriangleDegree G * ∑ e ∈ G.edgeFinset,
        (Fintype.card V + 2 * (triangleDegree G e) - G.degree e.out.1 - G.degree e.out.2) := by
    rw [Finset.mul_sum _ _ _]
    gcongr
    exact Finset.le_sup (f := triangleDegree G) ‹_›
  have concordant_count_identity (G : SimpleGraph V) [DecidableRel G.Adj] :
      ∑ e ∈ G.edgeFinset,
          (Fintype.card V + 2 * (triangleDegree G e) - G.degree e.out.1 - G.degree e.out.2) +
        ∑ v : V, G.degree v ^ 2 =
      Fintype.card V * G.edgeFinset.card + 2 * ∑ e ∈ G.edgeFinset, (triangleDegree G e) := by
    have endpoint_degree_sum_le_concordant_bound :
        ∀ x ∈ G.edgeFinset,
          G.degree x.out.1 + G.degree x.out.2 ≤
            Fintype.card V + 2 * triangleDegree G x := by
      intro x hx
      exact edge_degree_add_degree_le_card_add_two_mul_triangleDegree G x
    rw [← edge_endpoint_degree_sum_eq_sum_sq G, Finset.mul_sum _ _ _]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun x hx => by
      rw [tsub_tsub, tsub_add_cancel_of_le]
      linarith [endpoint_degree_sum_le_concordant_bound x hx]]
    simp +decide [mul_comm, Finset.sum_add_distrib]
  intro G _
  nlinarith [injection_inequality G, weighted_concordant_sum_le G, concordant_count_identity G]

/--
Khadžiivanov-Nikiforov counting inequality.

This is the key combinatorial inequality from Section 2 of Bollobás-Nikiforov 2004
(a consequence of their Theorem 1). In notation:
  - `n = Fintype.card V`
  - `m = G.edgeFinset.card`
  - `β = maxTriangleDegree G`
  - `S = ∑ e ∈ G.edgeFinset, triangleDegree G e`
  - `D = ∑ v, G.degree v ^ 2`

The inequality states: `n * S + 3β * D ≤ 6β * S + 3β * n * m`.

It follows from an injection argument: for each triangle `T` and vertex `y`,
by pigeonhole on 3 Boolean adjacency values, there exists an edge of `T` whose
endpoints have the same adjacency to `y` (concordant). The map `(T, y) ↦
(edge, third vertex, y)` is injective into the set of concordant triples,
giving `n * k₃ ≤ ∑ t(e) * a(e)` where `a(e)` is the concordant count. Bounding
`t(e) ≤ β` and using `∑ a(e) = nm + 2S - D` yields the result.
-/
lemma kn_counting_inequality
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V * ∑ e ∈ G.edgeFinset, triangleDegree G e +
      3 * maxTriangleDegree G * ∑ v : V, G.degree v ^ 2 ≤
    6 * maxTriangleDegree G * ∑ e ∈ G.edgeFinset, triangleDegree G e +
      3 * maxTriangleDegree G * Fintype.card V * G.edgeFinset.card := by
  classical
  have h_triangle_incidence := sum_triangleDegree_eq_three_mul_cliqueFinset G
  have h_injection := injection_counting_bound G
  nlinarith

/--
Hard case of the Bollobás-Nikiforov inequality.

The proof combines the KN counting inequality with Cauchy-Schwarz, the
handshaking lemma, and the Turán bound. The key steps are:
1. From Turán: `β > 0` (since `m > n²/4` forces a triangle).
2. From KN: `nS + 3βD ≤ 6βS + 3βnm`.
3. From Cauchy-Schwarz + `4m > n²`: `D > nm`, forcing `6β ≥ n`.
4. Combined with `S ≤ βm`: `3D ≤ 6βm + 2nm`.
-/
theorem bollobas_nikiforov_of_card_gt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    3 * ∑ v : V, G.degree v ^ 2 ≤
      6 * G.edgeFinset.card * maxTriangleDegree G +
        2 * Fintype.card V * G.edgeFinset.card := by
  set n := Fintype.card V with hn_def
  set m := G.edgeFinset.card with hm_def
  set β := maxTriangleDegree G with hβ_def
  set S := ∑ e ∈ G.edgeFinset, triangleDegree G e with hS_def
  set D := ∑ v : V, G.degree v ^ 2 with hD_def
  have h_triangleDegreeSum_le : S ≤ β * m := sum_triangleDegree_le_maxTriangleDegree_mul_edgeFinset G
  have h_beta_pos : 0 < β := maxTriangleDegree_pos_of_quarter_sq_lt_edges G h
  have h_kn_counting : n * S + 3 * β * D ≤ 6 * β * S + 3 * β * n * m :=
    kn_counting_inequality G
  have h_handshake : (∑ v : V, G.degree v) = 2 * m :=
    G.sum_degrees_eq_twice_card_edges
  have h_cauchy_sq : n * D ≥ 4 * m ^ 2 := by
    have h1 := @sq_sum_le_card_mul_sum_sq V ℕ _ _ _ _ Finset.univ (fun v => G.degree v)
    simp at h1
    nlinarith [h_handshake]
  have h_turan_gap : n ^ 2 < 4 * m := by
    omega
  have h_triangleDegreeSum_pos : 0 < S := by
    obtain ⟨e, he, heq⟩ := exists_mem_edgeFinset_triangleDegree_eq_maxTriangleDegree G
      (Finset.card_pos.mp (by omega))
    calc S = ∑ e ∈ G.edgeFinset, triangleDegree G e := rfl
      _ ≥ triangleDegree G e := Finset.single_le_sum (fun _ _ => Nat.zero_le _) he
      _ = β := heq
      _ > 0 := h_beta_pos
  suffices h_key : 3 * β * D ≤ β * (6 * m * β + 2 * n * m) by
    exact Nat.le_of_mul_le_mul_left (by linarith) h_beta_pos
  zify at h_kn_counting h_triangleDegreeSum_le h_beta_pos h_triangleDegreeSum_pos h_turan_gap h_cauchy_sq ⊢
  have h_beta_large_enough : (n : ℤ) ≤ 6 * β := by
    by_contra h_beta_large_enough
    push Not at h_beta_large_enough
    have h_degreeSumSq_gt : (n : ℤ) * m < D := by
      nlinarith
    nlinarith
  have h_nonneg_product : (0 : ℤ) ≤ (6 * β - n) * (β * m - S) := by
    apply mul_nonneg <;> linarith
  nlinarith

/--
The Bollobás-Nikiforov inequality in cross-multiplied form.

For a graph `G` on `n` vertices with `m > n^2 / 4` edges and
maximum triangle-degree `f₃`:

    3 * ∑ d(v)^2 ≤ 6 * m * f₃ + 2 * n * m

This is the main nontrivial external ingredient in the
Bollobás-Nikiforov proof route. Combined with Cauchy-Schwarz
and the handshaking lemma, the rest of the proof is arithmetic.
-/
theorem bollobas_nikiforov
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    3 * ∑ v : V, G.degree v ^ 2 ≤
      6 * G.edgeFinset.card * maxTriangleDegree G +
        2 * Fintype.card V * G.edgeFinset.card := by
  by_cases h_case : Fintype.card V ≤ 3 * maxTriangleDegree G
  · exact bollobas_nikiforov_of_card_le G h_case
  · exact bollobas_nikiforov_of_card_gt G h

/-- Arithmetic consequence of the Bollobás-Nikiforov inequality:
`n < 6 * f₃`. -/
theorem card_lt_six_mul_maxTriangleDegree_of_quarter_sq_lt_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    Fintype.card V < 6 * maxTriangleDegree G := by
  have h_card_pos_orig : 0 < Fintype.card V := by
    have h_edge_count_pos : 0 < G.edgeFinset.card := by
      omega
    obtain ⟨e, he⟩ : G.edgeFinset.Nonempty := Finset.card_pos.mp h_edge_count_pos
    exact Fintype.card_pos_iff.mpr ⟨e.out.1⟩
  set n := Fintype.card V with hn_def
  set m := G.edgeFinset.card with hm_def
  set β := maxTriangleDegree G with hβ_def
  have h_bn : 3 * ∑ v : V, G.degree v ^ 2 ≤
      6 * G.edgeFinset.card * maxTriangleDegree G +
        2 * Fintype.card V * G.edgeFinset.card := bollobas_nikiforov G h
  have h_cauchy :
      (∑ v : V, G.degree v) ^ 2 ≤ n * ∑ v : V, G.degree v ^ 2 := by
    have h_cs :
        ∀ (u v : V → ℚ),
          (∑ x : V, u x * v x) ^ 2 ≤
            (∑ x : V, u x ^ 2) * ∑ x : V, v x ^ 2 :=
      fun u v ↦ Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    simpa [hn_def, ← @Nat.cast_le ℚ] using h_cs 1 (fun v => G.degree v)
  have h_handshake_sq :
      (∑ v : V, G.degree v) ^ 2 = 4 * m ^ 2 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp [hm_def]
    ring
  have h_combined : 12 * m ^ 2 ≤ n * (6 * m * β + 2 * n * m) := by
    nlinarith [h_cauchy, h_handshake_sq, h_bn]
  have h_edge_count_pos : 0 < m := by
    omega
  have h_turan_gap : n ^ 2 < 4 * m := by
    omega
  have h_linear : 6 * m ≤ n * (3 * β + n) := by
    have h_mul :
        (2 * m) * (6 * m) ≤ (2 * m) * (n * (3 * β + n)) := by
      calc
        (2 * m) * (6 * m) = 12 * m ^ 2 := by ring
        _ ≤ n * (6 * m * β + 2 * n * m) := h_combined
        _ = (2 * m) * (n * (3 * β + n)) := by ring
    exact Nat.le_of_mul_le_mul_left h_mul (by omega)
  have h_card_pos : 0 < n := by
    simpa [hn_def] using h_card_pos_orig
  zify at h_turan_gap h_linear h_card_pos ⊢
  nlinarith

/-- Arithmetic consequence of the Bollobás-Nikiforov inequality:
`n / 6 < f₃`. -/
theorem card_div_six_lt_maxTriangleDegree_of_quarter_sq_lt_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    Fintype.card V / 6 < maxTriangleDegree G := by
  have h_strict := card_lt_six_mul_maxTriangleDegree_of_quarter_sq_lt_edges G h
  omega

/-- Arithmetic consequence of the Bollobás-Nikiforov inequality:
`n / 6 ≤ f₃`. -/
theorem card_div_six_le_maxTriangleDegree_of_quarter_sq_lt_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    Fintype.card V / 6 ≤ maxTriangleDegree G := by
  have h_strict := card_div_six_lt_maxTriangleDegree_of_quarter_sq_lt_edges G h
  omega

/--
**Erdős Problem 905** (Bollobás-Erdős conjecture, proved by
Khadžiivanov-Nikiforov in 1979).

Every graph on `n` vertices with more than `⌊n^2 / 4⌋` edges contains an edge
which lies in at least `n / 6` triangles.

The proof uses the auxiliary inequality `bollobas_nikiforov`, then translates
the resulting bound on `maxTriangleDegree G` into the existence of an edge that
attains this maximum.
-/
theorem erdos_905 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Fintype.card V ^ 2 / 4 < G.edgeFinset.card) :
    ∃ e ∈ G.edgeFinset, Fintype.card V / 6 ≤ triangleDegree G e := by
  have hne : G.edgeFinset.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨e, heE, hmax⟩ :=
    exists_mem_edgeFinset_triangleDegree_eq_maxTriangleDegree G hne
  exact ⟨e, heE, hmax ▸
    card_div_six_le_maxTriangleDegree_of_quarter_sq_lt_edges G h⟩

#print axioms erdos_905
-- 'Erdos905.ErdosProblems.P905.erdos_905' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end ErdosProblems.P905

end Erdos905

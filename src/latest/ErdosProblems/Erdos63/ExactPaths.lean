/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.GrowthSchedule
import ErdosProblems.Erdos63.RobustSupplyEventual
import ErdosProblems.Erdos63.Lemma311

/-!
# Exact paths from length adjusters

This file contains the exact combinatorial splice at the end of
Liu--Montgomery Lemma 4.8.  Two vertex-disjoint connector paths are joined by
one of the routes in an adjuster.  The bipartition shows that the difference
between the requested length and the unadjusted route is even, and the range
of the adjuster then removes that difference in steps of two.

The support conditions below are stated using lists.  This is precisely the
form needed by `SimpleGraph.Walk.IsPath.mk'`: after appending two walks, the
support is the support of the first walk followed by the tail of the support
of the second.  In applications these conditions follow from the vertex
disjointness and avoidance conclusions of Corollary 3.15.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

universe u

attribute [local instance] Classical.decEq

variable {V : Type u}
variable {G : SimpleGraph V}

/-- The core of the `22m`-adjuster used in Lemma 4.8 has the source bound
`220m²`. -/
theorem Adjuster.core_card_le_twentyTwo {D m : ℕ}
    (A : Adjuster G D m (22 * m)) : A.core.card ≤ 220 * m ^ 2 := by
  calc
    A.core.card ≤ 10 * m * (22 * m) := A.core_card_le
    _ = 220 * m ^ 2 := by ring

/-- Convert the real-valued minimum-degree convention of Theorem 2.7 to the
natural-valued convention used by the finite graph lemmas. -/
theorem degree_parameter_le_degree [Fintype V] [DecidableRel G.Adj] {d : ℕ}
    (hmin : ∀ v : V, (d : ℝ) ≤ G.degree v) (v : V) :
    d ≤ G.degree v := by
  exact_mod_cast hmin v

/-- The slightly weaker natural-valued minimum-degree hypothesis used by
source Lemma 3.11 follows from the real-valued Theorem 2.7 convention. -/
theorem degree_parameter_pred_le_degree [Fintype V] [DecidableRel G.Adj] {d : ℕ}
    (hmin : ∀ v : V, (d : ℝ) ≤ G.degree v) (v : V) :
    d - 1 ≤ G.degree v :=
  (Nat.sub_le d 1).trans (degree_parameter_le_degree hmin v)

/-- A real-valued minimum-degree hypothesis forces the ambient order above
the natural degree parameter.  This transfers every eventual-in-`n`
numerical estimate to the single eventual threshold `d₀` in Theorem 2.7. -/
theorem degree_parameter_lt_card [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] {d : ℕ}
    (hmin : ∀ v : V, (d : ℝ) ≤ G.degree v) :
    d < Fintype.card V := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hd : d ≤ G.degree v := degree_parameter_le_degree hmin v
  exact hd.trans_lt (G.degree_lt_card_verts v)

/-- A finite graph of minimum degree at least two contains a shortest cycle.

Indeed, if the graph were acyclic, it could be extended to a spanning tree.
The degree-sum formula and the minimum-degree hypothesis give at least as
many edges as vertices, whereas the spanning tree has one fewer edge. -/
theorem exists_shortestCycle_of_minDegree_two [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] (hdegree : ∀ v : V, 2 ≤ G.degree v) :
    ∃ c : V, ∃ C : G.Walk c c, IsShortestCycle C := by
  classical
  have hnotAcyclic : ¬ G.IsAcyclic := by
    intro hacyclic
    obtain ⟨T, hGT, -, hT⟩ :=
      (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
        (G := ⊤) (H := G) le_top hacyclic
    have hsum : (∑ _ : V, 2) ≤ ∑ v : V, G.degree v := by
      apply Finset.sum_le_sum
      intro v _
      exact hdegree v
    have hedgeLower : Fintype.card V ≤ G.edgeFinset.card := by
      have htwice : 2 * Fintype.card V ≤ 2 * G.edgeFinset.card := by
        calc
          2 * Fintype.card V = ∑ _ : V, 2 := by simp [Nat.mul_comm]
          _ ≤ ∑ v : V, G.degree v := hsum
          _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      omega
    have hedgeMono : G.edgeFinset.card ≤ T.edgeFinset.card :=
      Finset.card_mono (SimpleGraph.edgeFinset_mono hGT)
    have htreeEdges : T.edgeFinset.card + 1 = Fintype.card V :=
      hT.card_edgeFinset
    omega
  have hcycle : ∃ c : V, ∃ C : G.Walk c c, C.IsCycle := by
    by_contra hnone
    apply hnotAcyclic
    intro c C hC
    exact hnone ⟨c, C, hC⟩
  obtain ⟨c₀, C₀, hC₀⟩ := hcycle
  obtain ⟨c, C, hC, -⟩ := exists_shortestCycle_of_cycle C₀ hC₀
  exact ⟨c, C, hC⟩

/-- Theorem 2.7's real-valued minimum-degree convention supplies the cycle
seed required by source Lemma 3.11 once the absolute degree threshold is at
least two. -/
theorem exists_shortestCycle_of_degree_parameter [Fintype V] [Nonempty V]
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hmin : ∀ v : V, (d : ℝ) ≤ G.degree v) :
    ∃ c : V, ∃ C : G.Walk c c, IsShortestCycle C := by
  apply exists_shortestCycle_of_minDegree_two
  intro v
  exact hd.trans (degree_parameter_le_degree hmin v)

/-- Threshold form of the eventual concrete Corollary 3.15 package.  The
outer threshold depends only on the ambient order, while the package remains
uniform in every positive `d ≤ n` and every finite graph of order `n`. -/
theorem exists_lm315ConcreteData_threshold :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ d : ℕ, 1 ≤ d → d ≤ n →
      ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
        Fintype.card W = n → Nonempty (LM315ConcreteData J d) := by
  simpa only [Filter.eventually_atTop] using
    eventually_exists_lm315Numerics

/-- Threshold form of the concrete avoiding-ball growth estimates used in
the Lemma 4.7 adjuster induction.  The same ambient-order threshold works for
every positive minimum-degree parameter; in particular there is no separate
large-`d` regime in Theorem 2.7. -/
theorem exists_lmConcreteGrowthBounds_threshold :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ d : ℕ, 1 ≤ d →
      LMConcreteGrowthBounds n d := by
  simpa only [Filter.eventually_atTop] using
    eventually_lmConcreteGrowthBounds

/-- Threshold form of the inflated-order Lemma 4.7 arithmetic package. -/
theorem exists_lm47ScaleBounds_threshold :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, LM47ScaleBounds n := by
  simpa only [Filter.eventually_atTop] using eventually_lm47ScaleBounds

/-- Threshold form of the ambient-order estimates used by the source
Lemma 3.11 numerical certificate. -/
theorem exists_lm311ScaleBounds_threshold :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, LM311ScaleBounds n := by
  simpa only [Filter.eventually_atTop] using eventually_lm311ScaleBounds

/-- Threshold form of the lower exact-path scale estimate.  It is separated
from the graph-theoretic producers so the eventual threshold in Theorem 2.7
can be chosen before the finite graph and its adjuster are introduced. -/
theorem exists_adjuster_exactPath_scale_threshold :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      220 * Parameters.lmRadius (1 / 1024) n ^ 2 +
          22 * Parameters.lmRadius (1 / 1024) n + 1 ≤
        ⌈Real.log (n : ℝ) ^ 7⌉₊ := by
  simpa only [Filter.eventually_atTop] using
    (Parameters.eventually_adjuster_core_le_ceil_log_seven
      (show (0 : ℝ) < 1 / 1024 by norm_num))

/-! ### The two endpoint expansions constructed before the adjuster -/

/-- The two prescribed roots in the source application of Lemma 3.11. -/
def exactPathEndpointEmbedding (x y : V) (hxy : x ≠ y) : Fin 2 ↪ V where
  toFun := ![x, y]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem exactPathEndpointEmbedding_zero (x y : V) (hxy : x ≠ y) :
    exactPathEndpointEmbedding x y hxy (0 : Fin 2) = x := rfl

@[simp] theorem exactPathEndpointEmbedding_one (x y : V) (hxy : x ≠ y) :
    exactPathEndpointEmbedding x y hxy (1 : Fin 2) = y := rfl

/-- Select one expansion at each endpoint from the matrix form of source
Lemma 3.11.  The source family only promises pairwise disjointness after
deleting a common root; because the selected members have different embedded
roots, `disjoint_of_root_ne` upgrades this to full vertex-disjointness. -/
theorem exists_endpointExpansions_of_lm311Family
    {x y : V} (hxy : x ≠ y) {D r m : ℕ} {reserved : Finset V}
    (F : LM311ExpansionFamily G (exactPathEndpointEmbedding x y hxy)
      (fun _ _ ↦ D) r reserved)
    (hroots : Finset.univ.image (exactPathEndpointEmbedding x y hxy) ⊆
      reserved)
    (hrm : r ≤ m) :
    ∃ E₁ : VertexExpansion G x D m,
      ∃ E₂ : VertexExpansion G y D m, Disjoint E₁.verts E₂.verts := by
  let E₁ : VertexExpansion G x D m := by
    simpa using (F.expansion (0 : Fin 2) (0 : Fin 2)).radiusMono hrm
  let E₂ : VertexExpansion G y D m := by
    simpa using (F.expansion (1 : Fin 2) (0 : Fin 2)).radiusMono hrm
  have hpair := F.disjoint_of_root_ne hroots
    (a := ((0 : Fin 2), (0 : Fin 2))) (b := ((1 : Fin 2), (0 : Fin 2)))
    (by decide) (by simpa using hxy)
  refine ⟨E₁, E₂, ?_⟩
  change Disjoint (F.expansion (0 : Fin 2) (0 : Fin 2)).verts
    (F.expansion (1 : Fin 2) (0 : Fin 2)).verts
  exact hpair

/-- Prop-elimination-safe form for the public source Lemma 3.11 API. -/
theorem exists_endpointExpansions_of_nonempty_lm311Family
    {x y : V} (hxy : x ≠ y) {D r m : ℕ} {reserved : Finset V}
    (family : Nonempty (LM311ExpansionFamily G
      (exactPathEndpointEmbedding x y hxy) (fun _ _ ↦ D) r reserved))
    (hroots : Finset.univ.image (exactPathEndpointEmbedding x y hxy) ⊆
      reserved)
    (hrm : r ≤ m) :
    ∃ E₁ : VertexExpansion G x D m,
      ∃ E₂ : VertexExpansion G y D m, Disjoint E₁.verts E₂.verts := by
  obtain ⟨F⟩ := family
  exact exists_endpointExpansions_of_lm311Family hxy F hroots hrm

end Erdos63

namespace SimpleGraph.Walk

universe u

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V}

/-- Three simple paths whose only common vertices are their consecutive
endpoints concatenate to a simple path.  The last path is presented in the
opposite orientation, as it is in the proof of Liu--Montgomery Lemma 4.8. -/
theorem IsPath.append_append_reverse {v₁ v₂ v₃ v₄ : V}
    {p : G.Walk v₁ v₃} {r : G.Walk v₃ v₄} {q : G.Walk v₂ v₄}
    (hp : p.IsPath) (hr : r.IsPath) (hq : q.IsPath)
    (hpr : p.support.Disjoint r.support.tail)
    (hpq : (p.support ++ r.support.tail).Disjoint q.reverse.support.tail) :
    ((p.append r).append q.reverse).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, Walk.support_append, List.nodup_append']
  refine ⟨?_, hq.reverse.support_nodup.tail, hpq⟩
  exact List.nodup_append'.2 ⟨hp.support_nodup, hr.support_nodup.tail, hpr⟩

end SimpleGraph.Walk

namespace Erdos63

universe u

attribute [local instance] Classical.decEq

variable {V : Type u}
variable {G : SimpleGraph V}

/-! ## Parity bookkeeping -/

/-- The difference between two parity-compatible lengths with the same
endpoints is even.  The second length is exhibited by an arbitrary walk; no
simplicity hypothesis is needed for this parity calculation. -/
theorem even_sub_walk_length_of_parityCompatible [Fintype V]
    (B : Bipartition G) {x y : V} {ell : ℕ} (w : G.Walk x y)
    (hell : ParityCompatible B x y ell) (hle : w.length ≤ ell) :
    Even (ell - w.length) := by
  rw [Nat.even_sub hle]
  exact hell.trans (w.parityCompatible B).symm

/-- Parity form specialized to the three-piece walk used in the exact splice. -/
theorem even_three_piece_gap_of_parityCompatible [Fintype V]
    (B : Bipartition G) {v₁ v₂ v₃ v₄ : V} {ell : ℕ}
    (p : G.Walk v₁ v₃) (r : G.Walk v₃ v₄) (q : G.Walk v₂ v₄)
    (hell : ParityCompatible B v₁ v₂ ell)
    (hle : p.length + r.length + q.length ≤ ell) :
    Even (ell - (p.length + r.length + q.length)) := by
  let w : G.Walk v₁ v₂ := (p.append r).append q.reverse
  have hwlen : w.length = p.length + r.length + q.length := by
    simp [w, Walk.length_append, Nat.add_assoc]
  rw [← hwlen]
  exact even_sub_walk_length_of_parityCompatible B w hell (hwlen.trans_le hle)

/-! ## The exact adjustment splice -/

/-- The arithmetic and support-disjointness core of Lemma 4.8.

`base + 2*i` is the family of available middle-route lengths.  The two
connector paths contribute the fixed outer length.  The two list-disjointness
hypotheses are required uniformly over the selected middle route because its
support may depend on `i`. -/
theorem exactPath_of_adjustable_middle
    {v₁ v₂ v₃ v₄ : V} {ell base k : ℕ}
    (p : G.Walk v₁ v₃) (q : G.Walk v₂ v₄)
    (hp : p.IsPath) (hq : q.IsPath)
    (hmiddle : ∀ i : ℕ, i ≤ k →
      ∃ r : G.Walk v₃ v₄, r.IsPath ∧ r.length = base + 2 * i)
    (hleft : ∀ i : ℕ, ∀ hi : i ≤ k, ∀ r : G.Walk v₃ v₄,
      r.IsPath → r.length = base + 2 * i →
        p.support.Disjoint r.support.tail)
    (hright : ∀ i : ℕ, ∀ hi : i ≤ k, ∀ r : G.Walk v₃ v₄,
      r.IsPath → r.length = base + 2 * i →
        (p.support ++ r.support.tail).Disjoint q.reverse.support.tail)
    (hbase : p.length + base + q.length ≤ ell)
    (heven : Even (ell - (p.length + base + q.length)))
    (hwidth : ell - (p.length + base + q.length) ≤ 2 * k) :
    HasPathBetweenLength G v₁ v₂ ell := by
  obtain ⟨i, hi⟩ := heven
  have hik : i ≤ k := by omega
  obtain ⟨r, hr, hrlen⟩ := hmiddle i hik
  let w : G.Walk v₁ v₂ := (p.append r).append q.reverse
  refine ⟨w, ?_, ?_⟩
  · exact hp.append_append_reverse hr hq
      (hleft i hik r hr hrlen) (hright i hik r hr hrlen)
  · have htotal : p.length + (base + 2 * i) + q.length = ell := by
      omega
    simpa [w, Walk.length_append, Walk.length_reverse, hrlen, Nat.add_assoc]
      using htotal

/-- The preceding splice with the parity of the adjustable gap discharged by
the ambient bipartition.  A base middle route is supplied separately solely
for the parity calculation; it is normally `A.basePath`. -/
theorem exactPath_of_adjustable_middle_of_parity [Fintype V]
    (B : Bipartition G) {v₁ v₂ v₃ v₄ : V} {ell base k : ℕ}
    (p : G.Walk v₁ v₃) (q : G.Walk v₂ v₄)
    (hp : p.IsPath) (hq : q.IsPath)
    (r₀ : G.Walk v₃ v₄) (hr₀ : r₀.IsPath) (hr₀len : r₀.length = base)
    (hmiddle : ∀ i : ℕ, i ≤ k →
      ∃ r : G.Walk v₃ v₄, r.IsPath ∧ r.length = base + 2 * i)
    (hleft : ∀ i : ℕ, ∀ hi : i ≤ k, ∀ r : G.Walk v₃ v₄,
      r.IsPath → r.length = base + 2 * i →
        p.support.Disjoint r.support.tail)
    (hright : ∀ i : ℕ, ∀ hi : i ≤ k, ∀ r : G.Walk v₃ v₄,
      r.IsPath → r.length = base + 2 * i →
        (p.support ++ r.support.tail).Disjoint q.reverse.support.tail)
    (hell : ParityCompatible B v₁ v₂ ell)
    (hbase : p.length + base + q.length ≤ ell)
    (hwidth : ell - (p.length + base + q.length) ≤ 2 * k) :
    HasPathBetweenLength G v₁ v₂ ell := by
  have hbase' : p.length + r₀.length + q.length ≤ ell := by
    simpa [hr₀len] using hbase
  have heven : Even (ell - (p.length + base + q.length)) := by
    simpa [hr₀len] using
      even_three_piece_gap_of_parityCompatible B p r₀ q hell hbase'
  exact exactPath_of_adjustable_middle p q hp hq hmiddle hleft hright
    hbase heven hwidth

/-! ## Form specialized to an `Adjuster` -/

/-- Lemma 4.8's final splice, expressed directly with an `Adjuster`.

The upstream connector theorem supplies `p` and `q` together with the two
uniform support-disjointness conditions.  The quantitative part of Lemma 4.8
supplies `hbase` and `hwidth`. -/
theorem lemma4_8_splice [Fintype V] (B : Bipartition G)
    {D m k ell : ℕ} (A : Adjuster G D m k)
    {v₁ v₂ : V}
    (p : G.Walk v₁ A.leftRoot) (q : G.Walk v₂ A.rightRoot)
    (hp : p.IsPath) (hq : q.IsPath)
    (hleft : ∀ i : ℕ, ∀ hi : i ≤ k, ∀ r : G.Walk A.leftRoot A.rightRoot,
      r.IsPath → r.length = A.length + 2 * i →
        p.support.Disjoint r.support.tail)
    (hright : ∀ i : ℕ, ∀ hi : i ≤ k, ∀ r : G.Walk A.leftRoot A.rightRoot,
      r.IsPath → r.length = A.length + 2 * i →
        (p.support ++ r.support.tail).Disjoint q.reverse.support.tail)
    (hell : ParityCompatible B v₁ v₂ ell)
    (hbase : p.length + A.length + q.length ≤ ell)
    (hwidth : ell - (p.length + A.length + q.length) ≤ 2 * k) :
    HasPathBetweenLength G v₁ v₂ ell := by
  obtain ⟨r₀, hr₀, -, hr₀len⟩ := A.basePath
  apply exactPath_of_adjustable_middle_of_parity B p q hp hq r₀ hr₀ hr₀len
  · intro i hi
    obtain ⟨r, hr, -, hrlen⟩ := A.pathLength i hi
    exact ⟨r, hr, hrlen⟩
  · exact hleft
  · exact hright
  · exact hell
  · exact hbase
  · exact hwidth

/-- A directly usable form of the Lemma 4.8 splice.  It replaces the two
list-level disjointness assumptions by the conclusions naturally supplied by
the connector construction: the two outer paths are vertex-disjoint and both
avoid the adjuster core. -/
theorem lemma4_8_splice_of_core_avoiding_connectors [Fintype V]
    (B : Bipartition G) {D m k ell : ℕ} (A : Adjuster G D m k)
    {v₁ v₂ : V}
    (p : G.Walk v₁ A.leftRoot) (q : G.Walk v₂ A.rightRoot)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpq : p.support.Disjoint q.support)
    (hpcore : ∀ z ∈ p.support, z ∉ A.core)
    (hqcore : ∀ z ∈ q.support, z ∉ A.core)
    (hell : ParityCompatible B v₁ v₂ ell)
    (hbase : p.length + A.length + q.length ≤ ell)
    (hwidth : ell - (p.length + A.length + q.length) ≤ 2 * k) :
    HasPathBetweenLength G v₁ v₂ ell := by
  obtain ⟨r₀, hr₀, -, hr₀len⟩ := A.basePath
  have hbase₀ : p.length + r₀.length + q.length ≤ ell := by
    simpa [hr₀len] using hbase
  have heven : Even (ell - (p.length + A.length + q.length)) := by
    simpa [hr₀len] using
      even_three_piece_gap_of_parityCompatible B p r₀ q hell hbase₀
  obtain ⟨i, hi⟩ := heven
  have hik : i ≤ k := by omega
  obtain ⟨r, hr, hrsupp, hrlen⟩ := A.pathLength i hik
  have hpr : p.support.Disjoint r.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzr
    have hzr' : z ∈ r.support := List.tail_subset _ hzr
    have hzallowed := hrsupp z hzr'
    simp only [Finset.mem_insert] at hzallowed
    rcases hzallowed with (rfl | rfl | hzcore)
    · have hstart : A.leftRoot ∉ r.support.tail := by
        have hn := hr.support_nodup
        rw [← r.cons_tail_support, List.nodup_cons] at hn
        exact hn.1
      exact hstart hzr
    · exact (List.disjoint_left.1 hpq) hzp q.end_mem_support
    · exact hpcore z hzp hzcore
  have hpqr : (p.support ++ r.support.tail).Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzleft hzqtail
    have hzqrev : z ∈ q.reverse.support := List.tail_subset _ hzqtail
    have hzq : z ∈ q.support := by
      simpa [Walk.support_reverse] using hzqrev
    rcases List.mem_append.1 hzleft with hzp | hzr
    · exact (List.disjoint_left.1 hpq) hzp hzq
    · have hzr' : z ∈ r.support := List.tail_subset _ hzr
      have hzallowed := hrsupp z hzr'
      simp only [Finset.mem_insert] at hzallowed
      rcases hzallowed with (rfl | rfl | hzcore)
      · exact (List.disjoint_left.1 hpq) p.end_mem_support hzq
      · have hstart : A.rightRoot ∉ q.reverse.support.tail := by
          have hn := hq.reverse.support_nodup
          rw [← q.reverse.cons_tail_support, List.nodup_cons] at hn
          exact hn.1
        exact hstart hzqtail
      · exact hqcore z hzq hzcore
  let w : G.Walk v₁ v₂ := (p.append r).append q.reverse
  refine ⟨w, hp.append_append_reverse hr hq hpr hpqr, ?_⟩
  have htotal : p.length + (A.length + 2 * i) + q.length = ell := by
    omega
  simpa [w, Walk.length_append, Walk.length_reverse, hrlen, Nat.add_assoc]
    using htotal

/-- The numerical form of the preceding splice that consumes the direct
pairing in the output record of Corollary 3.15. -/
theorem lemma4_8_of_adjuster_and_connectorPair [Fintype V]
    (B : Bipartition G) {D m ell : ℕ} (A : Adjuster G D m (22 * m))
    {v₁ v₂ : V} (forbidden : Finset V)
    (hcore : A.core ⊆ forbidden)
    (hfit : 22 * m + A.length ≤ ell)
    (P : DisjointConnectorPair G forbidden v₁ v₂ A.leftRoot A.rightRoot
      (ell - 22 * m - A.length) (ell - 22 * m - A.length + 22 * m))
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  apply lemma4_8_splice_of_core_avoiding_connectors B A
    P.left P.right P.left_isPath P.right_isPath P.disjoint
  · intro z hz hzcore
    exact P.left_avoids z hz (hcore hzcore)
  · intro z hz hzcore
    exact P.right_avoids z hz (hcore hzcore)
  · exact hell
  · have hupper := P.upper_length
    omega
  · have hlower := P.lower_length
    omega

/-- Pairing-insensitive form of the final splice in Lemma 4.8.  Corollary
3.15 is allowed to pair the two outside roots with the adjuster roots in
either order.  In the crossed case we reverse the adjuster; its core and its
least base length are unchanged. -/
theorem lemma4_8_of_adjuster_and_lm315Conclusion [Fintype V]
    (B : Bipartition G) {D m ell : ℕ} (A : Adjuster G D m (22 * m))
    {v₁ v₂ : V} (forbidden : Finset V)
    (hcore : A.core ⊆ forbidden)
    (hfit : 22 * m + A.length ≤ ell)
    (P : LM315Conclusion G forbidden v₁ v₂ A.leftRoot A.rightRoot
      (ell - 22 * m - A.length) m)
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  rcases P with hP | hP
  · obtain ⟨P⟩ := hP
    exact lemma4_8_of_adjuster_and_connectorPair B A forbidden hcore hfit P hell
  · obtain ⟨P⟩ := hP
    apply lemma4_8_of_adjuster_and_connectorPair B A.swap forbidden
    · simpa using hcore
    · simpa using hfit
    · simpa using P
    · exact hell

/-- The form used verbatim in Lemma 4.8: the connector theorem is run after
deleting the ambient forbidden set together with the adjuster core. -/
theorem lemma4_8_of_adjuster_and_lm315Conclusion_coreUnion [Fintype V]
    (B : Bipartition G) {D m ell : ℕ} (A : Adjuster G D m (22 * m))
    {v₁ v₂ : V} (U : Finset V)
    (hfit : 22 * m + A.length ≤ ell)
    (P : LM315Conclusion G (U ∪ A.core) v₁ v₂ A.leftRoot A.rightRoot
      (ell - 22 * m - A.length) m)
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  apply lemma4_8_of_adjuster_and_lm315Conclusion B A (U ∪ A.core)
  · exact Finset.subset_union_right
  · exact hfit
  · exact P
  · exact hell

/-- A source-scale variant in which the lower endpoint of the path window
absorbs the entire adjuster core and the width of Corollary 3.15. -/
theorem lemma4_8_of_adjuster_and_lm315Conclusion_of_scale [Fintype V]
    (B : Bipartition G) {D m ell : ℕ} (A : Adjuster G D m (22 * m))
    {v₁ v₂ : V} (U : Finset V)
    (hscale : 220 * m ^ 2 + 22 * m + 1 ≤ ell)
    (P : LM315Conclusion G (U ∪ A.core) v₁ v₂ A.leftRoot A.rightRoot
      (ell - 22 * m - A.length) m)
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  apply lemma4_8_of_adjuster_and_lm315Conclusion_coreUnion B A U
  · calc
      22 * m + A.length ≤ 22 * m + (10 * m * (22 * m) + 1) :=
        Nat.add_le_add_left A.length_le_ten_mul_add_one (22 * m)
      _ = 220 * m ^ 2 + 22 * m + 1 := by ring
      _ ≤ ell := hscale
  · exact P
  · exact hell

/-- The eventual integer ceiling estimate from `Parameters` implies the
lower-length hypothesis needed by the exact splice for every requested
integer in the Theorem 2.7 window. -/
theorem adjuster_scale_le_of_log_seven_le {n m ell : ℕ}
    (hscale : 220 * m ^ 2 + 22 * m + 1 ≤
      ⌈Real.log (n : ℝ) ^ 7⌉₊)
    (hlower : Real.log (n : ℝ) ^ 7 ≤ ell) :
    220 * m ^ 2 + 22 * m + 1 ≤ ell :=
  hscale.trans (Nat.ceil_le.2 hlower)

/-- The corrected construction order for Lemma 4.8, after all four fresh
endpoint expansions have been produced simultaneously.

The fresh third and fourth expansions have the same roots as `A`, avoid its
core, and are disjoint from the two endpoint expansions.  We replace the old
reservoirs by these fresh ends; `Adjuster.replaceEnds` preserves the roots,
core, least length, and every adjustable route.  Corollary 3.15 may therefore
be run after deleting only `U ∪ A.core`, and its two connectors feed directly
into the exact splice above. -/
theorem lemma4_8_of_adjuster_and_four_fresh_expansions
    [Fintype V] [DecidableRel G.Adj]
    (B : Bipartition G) {epsilon kappa : ℝ}
    (hexp : IsLMExpander G epsilon kappa)
    {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace ell : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    (A : Adjuster G D m (22 * m)) {v₁ v₂ : V}
    (E₁ : VertexExpansion G v₁ D m)
    (E₂ : VertexExpansion G v₂ D m)
    (E₃ : VertexExpansion G A.leftRoot D m)
    (E₄ : VertexExpansion G A.rightRoot D m)
    (U : Finset V)
    (hA₁ : Disjoint E₁.verts (U ∪ A.core))
    (hA₂ : Disjoint E₂.verts (U ∪ A.core))
    (hA₃ : Disjoint E₃.verts (U ∪ A.core))
    (hA₄ : Disjoint E₄.verts (U ∪ A.core))
    (h₁₂ : Disjoint E₁.verts E₂.verts)
    (h₁₃ : Disjoint E₁.verts E₃.verts)
    (h₁₄ : Disjoint E₁.verts E₄.verts)
    (h₂₃ : Disjoint E₂.verts E₃.verts)
    (h₂₄ : Disjoint E₂.verts E₄.verts)
    (h₃₄ : Disjoint E₃.verts E₄.verts)
    (h₁₃fresh :
      (U ∪ A.core).card + 4 * D + (32 * m) * L ≤ freshWorkspace)
    (h₁₃path :
      (U ∪ A.core).card + (8 * m) * (7 * m + 4) ≤ N.routeWorkspace)
    (hcorFresh :
      (U ∪ A.core).card + (ell - 22 * m - A.length) +
          14 * m + 2 * L + 3 ≤ freshWorkspace)
    (hcorPath :
      (U ∪ A.core).card + (ell - 22 * m - A.length) +
          14 * m + 3 ≤ pathWorkspace)
    (hscale : 220 * m ^ 2 + 22 * m + 1 ≤ ell)
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  have hcore₃ : Disjoint A.core E₃.verts :=
    hA₃.symm.mono_left Finset.subset_union_right
  have hcore₄ : Disjoint A.core E₄.verts :=
    hA₄.symm.mono_left Finset.subset_union_right
  let A' : Adjuster G D m (22 * m) :=
    A.replaceEnds E₃ E₄ hcore₃ hcore₄ h₃₄ le_rfl
  have P : LM315Conclusion G (U ∪ A.core) v₁ v₂
      A.leftRoot A.rightRoot (ell - 22 * m - A.length) m :=
    liuMontgomery_corollary3_15_finite G epsilon kappa hexp N
      hdegree (U ∪ A.core) E₁ E₂ E₃ E₄ hA₁ hA₂ hA₃ hA₄
        h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ h₁₃fresh h₁₃path
          hcorFresh hcorPath
  apply lemma4_8_of_adjuster_and_lm315Conclusion_of_scale
    B A' U hscale
  · simpa [A'] using P
  · exact hell

/-- Source-faithful constant-factor repair of Lemma 4.8.

The endpoint expansions are constructed first.  The robust Lemma 4.7
producer is then invoked at a larger internal order `Dlarge`, with their
union in its connector-deletion set.  The internal order is chosen large
enough that this deletion is within the genuine short-connection budget
(the source-scale wrapper uses a logarithmic multiple of `D`).  Proposition
3.10 shrinks the two resulting adjuster ends back to order `D`; the core and
every adjustable route are unchanged.  Thus Corollary 3.15 receives four
genuinely vertex-disjoint order-`D` expansions. -/
theorem lemma4_8_of_endpoint_expansions_and_large_adjuster
    [Fintype V] [DecidableRel G.Adj]
    (B : Bipartition G) {epsilon kappa : ℝ}
    (hexp : IsLMExpander G epsilon kappa)
    {D Dlarge K L m freshRadius pathRadius rounds freshWorkspace
      pathWorkspace ell : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    {v₁ v₂ : V} (E₁ : VertexExpansion G v₁ D m)
    (E₂ : VertexExpansion G v₂ D m) (h₁₂ : Disjoint E₁.verts E₂.verts)
    (A : Adjuster G Dlarge m (22 * m))
    (hEA : Disjoint (E₁.verts ∪ E₂.verts) A.verts)
    (hDpos : 0 < D) (hDlarge : D ≤ Dlarge)
    (h₁₃fresh :
      220 * m ^ 2 + 4 * D + (32 * m) * L ≤ freshWorkspace)
    (h₁₃path :
      220 * m ^ 2 + (8 * m) * (7 * m + 4) ≤ N.routeWorkspace)
    (hcorFresh :
      220 * m ^ 2 + ell + 14 * m + 2 * L + 3 ≤ freshWorkspace)
    (hcorPath :
      220 * m ^ 2 + ell + 14 * m + 3 ≤ pathWorkspace)
    (hscale : 220 * m ^ 2 + 22 * m + 1 ≤ ell)
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  obtain ⟨E₃, hE₃⟩ := A.leftEnd.proposition3_10 hDpos hDlarge
  obtain ⟨E₄, hE₄⟩ := A.rightEnd.proposition3_10 hDpos hDlarge
  have hcore₃ : Disjoint A.core E₃.verts :=
    A.core_disjoint_left.mono_right hE₃
  have hcore₄ : Disjoint A.core E₄.verts :=
    A.core_disjoint_right.mono_right hE₄
  have h₃₄ : Disjoint E₃.verts E₄.verts :=
    A.ends_disjoint.mono hE₃ hE₄
  let A' : Adjuster G D m (22 * m) :=
    A.replaceEnds E₃ E₄ hcore₃ hcore₄ h₃₄ le_rfl
  have hE₁A : Disjoint E₁.verts A.verts :=
    hEA.mono_left Finset.subset_union_left
  have hE₂A : Disjoint E₂.verts A.verts :=
    hEA.mono_left Finset.subset_union_right
  have h₁core : Disjoint E₁.verts A.core :=
    hE₁A.mono_right A.core_subset_verts
  have h₂core : Disjoint E₂.verts A.core :=
    hE₂A.mono_right A.core_subset_verts
  have h₁₃ : Disjoint E₁.verts E₃.verts :=
    hE₁A.mono_right (hE₃.trans A.leftEnd_verts_subset)
  have h₁₄ : Disjoint E₁.verts E₄.verts :=
    hE₁A.mono_right (hE₄.trans A.rightEnd_verts_subset)
  have h₂₃ : Disjoint E₂.verts E₃.verts :=
    hE₂A.mono_right (hE₃.trans A.leftEnd_verts_subset)
  have h₂₄ : Disjoint E₂.verts E₄.verts :=
    hE₂A.mono_right (hE₄.trans A.rightEnd_verts_subset)
  have hcore := A.core_card_le_twentyTwo
  apply lemma4_8_of_adjuster_and_four_fresh_expansions B hexp N hdegree A'
    E₁ E₂ E₃ E₄ ∅
  · simpa [A'] using h₁core
  · simpa [A'] using h₂core
  · simpa [A'] using hcore₃.symm
  · simpa [A'] using hcore₄.symm
  · exact h₁₂
  · exact h₁₃
  · exact h₁₄
  · exact h₂₃
  · exact h₂₄
  · exact h₃₄
  · simpa [A'] using (show
      A.core.card + 4 * D + (32 * m) * L ≤ freshWorkspace by omega)
  · simpa [A'] using (show
      A.core.card + (8 * m) * (7 * m + 4) ≤ N.routeWorkspace by omega)
  · simpa [A'] using (show
      A.core.card + (ell - 22 * m - A.length) + 14 * m + 2 * L + 3 ≤
        freshWorkspace by omega)
  · simpa [A'] using (show
      A.core.card + (ell - 22 * m - A.length) + 14 * m + 3 ≤
        pathWorkspace by omega)
  · exact hscale
  · exact hell

/-- Schedule-free form of the repaired Lemma 4.8 bridge. -/
theorem lemma4_8_of_lm315ConcreteData_and_large_adjuster
    [Fintype V] [DecidableRel G.Adj]
    (B : Bipartition G) {d Dlarge ell : ℕ}
    (data : LM315ConcreteData G d)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    {v₁ v₂ : V}
    (E₁ : VertexExpansion G v₁
      (Parameters.lmExpansionOrder (Fintype.card V))
      (Parameters.lmRadius (1 / 1024) (Fintype.card V)))
    (E₂ : VertexExpansion G v₂
      (Parameters.lmExpansionOrder (Fintype.card V))
      (Parameters.lmRadius (1 / 1024) (Fintype.card V)))
    (h₁₂ : Disjoint E₁.verts E₂.verts)
    (A : Adjuster G Dlarge
      (Parameters.lmRadius (1 / 1024) (Fintype.card V))
      (22 * Parameters.lmRadius (1 / 1024) (Fintype.card V)))
    (hEA : Disjoint (E₁.verts ∪ E₂.verts) A.verts)
    (hDpos : 0 < Parameters.lmExpansionOrder (Fintype.card V))
    (hDlarge : Parameters.lmExpansionOrder (Fintype.card V) ≤ Dlarge)
    (hscale :
      220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 +
          22 * Parameters.lmRadius (1 / 1024) (Fintype.card V) + 1 ≤ ell)
    (hupper : (ell : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ))
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  have hdegree' : ∀ v : V, data.numerics.degreeScale ≤ G.degree v := by
    intro v
    rw [data.degreeScale_eq]
    exact hdegree v
  apply lemma4_8_of_endpoint_expansions_and_large_adjuster B hexp
    data.numerics hdegree' E₁ E₂ h₁₂ A hEA hDpos hDlarge
  · exact data.lemma13_fresh
  · exact data.lemma13_route
  · exact data.long_fresh ell hupper
  · exact data.long_path ell hupper
  · exact hscale
  · exact hell

/-- Source-facing repaired Lemma 4.8, conditional only on the robust
simple-adjuster supply furnished by Lemma 4.3.

The two endpoint expansions are protected throughout the adjuster
construction.  `lemma4_7_twentyTwo_shrunk_of_concreteGrowth` performs every
join at the inflated order `D * m`, charges their union in the ordinary
connector deletion, and shrinks the surviving ends back to order `D`.
Consequently no limited-contact or protected-set hypothesis remains at this
interface. -/
theorem lemma4_8_of_lm315ConcreteData_and_simple_adjuster_supply
    [Fintype V] [DecidableRel G.Adj]
    (B : Bipartition G) {d ell : ℕ}
    (data : LM315ConcreteData G d)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (growth : LMConcreteGrowthBounds (Fintype.card V) d)
    (scales : LM47ScaleBounds (Fintype.card V))
    {v₁ v₂ : V}
    (E₁ : VertexExpansion G v₁
      (Parameters.lmExpansionOrder (Fintype.card V))
      (Parameters.lmRadius (1 / 1024) (Fintype.card V)))
    (E₂ : VertexExpansion G v₂
      (Parameters.lmExpansionOrder (Fintype.card V))
      (Parameters.lmRadius (1 / 1024) (Fintype.card V)))
    (h₁₂ : Disjoint E₁.verts E₂.verts)
    (hsupply : ∀ U : Finset V,
      U.card ≤ lm47SimpleBudget (Fintype.card V) →
      ∃ A : Adjuster G (lm47InflatedOrder (Fintype.card V))
          (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card V)) 1,
        Disjoint U A.verts)
    (hscale :
      220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 +
          22 * Parameters.lmRadius (1 / 1024) (Fintype.card V) + 1 ≤ ell)
    (hupper : (ell : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ))
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  let protectedSet := E₁.verts ∪ E₂.verts
  have hprotected : protectedSet.card ≤
      2 * Parameters.lmExpansionOrder (Fintype.card V) := by
    calc
      protectedSet.card ≤ E₁.verts.card + E₂.verts.card :=
        Finset.card_union_le _ _
      _ = 2 * Parameters.lmExpansionOrder (Fintype.card V) := by
        rw [E₁.card_verts, E₂.card_verts]
        simp [two_mul]
  obtain ⟨A, hA⟩ :=
    AdjusterJoin.lemma4_7_twentyTwo_shrunk_of_concreteGrowth
      hexp hdegree growth scales protectedSet hprotected hsupply
  apply lemma4_8_of_lm315ConcreteData_and_large_adjuster B data hexp hdegree
    E₁ E₂ h₁₂ A
  · simpa [protectedSet] using hA
  · exact scales.endpoint_pos
  · exact le_rfl
  · exact hscale
  · exact hupper
  · exact hell

/-- Complete Lemma 4.8 bridge from the matrix output of source Lemma 3.11.

This declaration fixes the construction order used by Theorem 2.7: first
select disjoint expansions at the two prescribed endpoints from the Lemma
3.11 family, and only then construct the inflated-order adjuster while
protecting their union. -/
theorem lemma4_8_of_lm311Family_and_simple_adjuster_supply
    [Fintype V] [DecidableRel G.Adj]
    (B : Bipartition G) {d ell r : ℕ}
    (data : LM315ConcreteData G d)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (growth : LMConcreteGrowthBounds (Fintype.card V) d)
    (scales : LM47ScaleBounds (Fintype.card V))
    {v₁ v₂ : V} (hv₁v₂ : v₁ ≠ v₂) {reserved : Finset V}
    (family : Nonempty (LM311ExpansionFamily G
      (exactPathEndpointEmbedding v₁ v₂ hv₁v₂)
      (fun _ _ ↦ Parameters.lmExpansionOrder (Fintype.card V))
      r reserved))
    (hroots : Finset.univ.image (exactPathEndpointEmbedding v₁ v₂ hv₁v₂) ⊆
      reserved)
    (hradius : r ≤ Parameters.lmRadius (1 / 1024) (Fintype.card V))
    (hsupply : ∀ U : Finset V,
      U.card ≤ lm47SimpleBudget (Fintype.card V) →
      ∃ A : Adjuster G (lm47InflatedOrder (Fintype.card V))
          (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card V)) 1,
        Disjoint U A.verts)
    (hscale :
      220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 +
          22 * Parameters.lmRadius (1 / 1024) (Fintype.card V) + 1 ≤ ell)
    (hupper : (ell : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ))
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  obtain ⟨E₁, E₂, h₁₂⟩ :=
    exists_endpointExpansions_of_nonempty_lm311Family hv₁v₂ family hroots hradius
  exact lemma4_8_of_lm315ConcreteData_and_simple_adjuster_supply
    B data hexp hdegree growth scales E₁ E₂ h₁₂ hsupply hscale hupper hell

/-- Source Lemma 3.11 and repaired Lemma 4.8 combined at the exact parameters
used in Theorem 2.7.  The only remaining inputs are scalar certificates and
the robust simple-adjuster supply; all graph gadgets are constructed here. -/
theorem lemma4_8_of_lm311Numerics_and_simple_adjuster_supply
    [Fintype V] [DecidableRel G.Adj]
    (B : Bipartition G) {d ell ell₀ m : ℕ}
    (data : LM315ConcreteData G d)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (growth : LMConcreteGrowthBounds (Fintype.card V) d)
    (scales : LM47ScaleBounds (Fintype.card V))
    (num : LM311Numerics (1 / 1024) ((1 / 64) * (d : ℝ))
      (Fintype.card V) 2 d
      (Parameters.lmExpansionOrder (Fintype.card V))
      (Parameters.lmExpansionOrder (Fintype.card V) ^ 2) ell₀ m 0)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    {v₁ v₂ : V} (hv₁v₂ : v₁ ≠ v₂)
    (hradius : 5 * m ≤
      Parameters.lmRadius (1 / 1024) (Fintype.card V))
    (hsupply : ∀ U : Finset V,
      U.card ≤ lm47SimpleBudget (Fintype.card V) →
      ∃ A : Adjuster G (lm47InflatedOrder (Fintype.card V))
          (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card V)) 1,
        Disjoint U A.verts)
    (hscale :
      220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 +
          22 * Parameters.lmRadius (1 / 1024) (Fintype.card V) + 1 ≤ ell)
    (hupper : (ell : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ))
    (hell : ParityCompatible B v₁ v₂ ell) :
    HasPathBetweenLength G v₁ v₂ ell := by
  let root := exactPathEndpointEmbedding v₁ v₂ hv₁v₂
  let D := Parameters.lmExpansionOrder (Fintype.card V)
  have family : Nonempty (LM311ExpansionFamily G root (fun _ _ ↦ D)
      (5 * m) (((∅ : Finset V) ∪ C.support.toFinset) ∪
        Finset.univ.image root)) := by
    apply liuMontgomery_lemma3_11_source G B (1 / 1024)
      ((1 / 64) * (d : ℝ)) hexp 2 d D (D ^ 2) ell₀ m 0 ∅
      (by simp) C hC root (fun _ _ ↦ D)
    · intro v
      exact (Nat.sub_le d 1).trans (hdegree v)
    · intro _ _
      exact scales.endpoint_pos
    · intro _ _
      exact le_rfl
    · simpa [D] using num
  apply lemma4_8_of_lm311Family_and_simple_adjuster_supply B data hexp
    hdegree growth scales hv₁v₂ family
  · exact Finset.subset_union_right
  · exact hradius
  · exact hsupply
  · exact hscale
  · exact hupper
  · exact hell

/-! ## Theorem 2.7 from the robust simple-adjuster supply -/

/-- The precise specialization of Liu--Montgomery Lemma 4.3 consumed by the
exact-path argument.  Its deletion budget and output parameters are exactly
those used by the corrected Lemma 4.7 induction above. -/
def LMRobustSimpleAdjusterSupply : Prop :=
  ∃ d₀ : ℕ, ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj]
      (B : Bipartition J) {d : ℕ},
      d₀ ≤ d →
      IsLMExpander J (1 / 1024) ((1 / 64) * (d : ℝ)) →
      (∀ v : W, d ≤ J.degree v) →
      ¬ oneSubdivisionClique (d / 2) ⊑ J →
      ∀ U : Finset W, U.card ≤ lm47SimpleBudget (Fintype.card W) →
        ∃ A : Adjuster J (lm47InflatedOrder (Fintype.card W))
            (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card W)) 1,
          Disjoint U A.verts

/-- Every ingredient of Theorem 2.7 except Lemma 4.3 is assembled here.

The common threshold dominates the degree threshold of source Lemma 3.11
and each eventual ambient-order estimate.  Minimum degree gives `d < |J|`,
so the same threshold controls all packages whose natural parameter is the
number of vertices. -/
theorem eventually_exact_paths_of_robustSimpleAdjusterSupply
    (hrobust : LMRobustSimpleAdjusterSupply.{u}) :
    ∃ d₀ : ℕ, ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj]
      (B : Bipartition J) {d : ℕ},
      d₀ ≤ d →
      IsLMExpander J (1 / 1024) ((1 / 64) * (d : ℝ)) →
      (∀ v : W, (d : ℝ) ≤ J.degree v) →
      ¬ oneSubdivisionClique (d / 2) ⊑ J →
      ∀ {x y : W} {q : ℕ}, x ≠ y →
        ParityCompatible B x y q →
        Real.log (Fintype.card W : ℝ) ^ 7 ≤ q →
        (q : ℝ) ≤ Parameters.lmPathScale (Fintype.card W : ℝ) →
        HasPathBetweenLength J x y q := by
  obtain ⟨dRobust, hRobust⟩ := hrobust
  obtain ⟨dNum, hNum⟩ := eventually_exists_lm311Numerics
  obtain ⟨nData, hData⟩ := exists_lm315ConcreteData_threshold
  obtain ⟨nGrowth, hGrowth⟩ := exists_lmConcreteGrowthBounds_threshold
  obtain ⟨nScales, hScales⟩ := exists_lm47ScaleBounds_threshold
  obtain ⟨nExact, hExact⟩ := exists_adjuster_exactPath_scale_threshold
  let d₀ := max 2 (max dRobust
    (max dNum (max nData (max nGrowth (max nScales nExact)))))
  refine ⟨d₀, ?_⟩
  intro W _ _ J _ B d hd hexp hdegreeReal hfree x y q hxy hparity
    hlower hupper
  let n := Fintype.card W
  have hdTwo : 2 ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdRobust : dRobust ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdNum : dNum ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdData : nData ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdGrowth : nGrowth ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdScales : nScales ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdExact : nExact ≤ d := by
    dsimp [d₀] at hd
    omega
  have hdN : d < n := by
    simpa [n] using degree_parameter_lt_card hdegreeReal
  have hdn : d ≤ n := hdN.le
  have hnData : nData ≤ n := hdData.trans hdn
  have hnGrowth : nGrowth ≤ n := hdGrowth.trans hdn
  have hnScales : nScales ≤ n := hdScales.trans hdn
  have hnExact : nExact ≤ n := hdExact.trans hdn
  have hdPos : 1 ≤ d := by omega
  obtain ⟨data⟩ := hData n hnData d hdPos hdn W J (by simp [n])
  let growth : LMConcreteGrowthBounds n d := hGrowth n hnGrowth d hdPos
  let scales : LM47ScaleBounds n := hScales n hnScales
  obtain ⟨num, hradius⟩ := hNum d hdNum n hdn
  obtain ⟨c, C, hC⟩ :=
    exists_shortestCycle_of_degree_parameter hdTwo hdegreeReal
  have hdegreeNat : ∀ v : W, d ≤ J.degree v :=
    degree_parameter_le_degree hdegreeReal
  have hsupply : ∀ U : Finset W,
      U.card ≤ lm47SimpleBudget n →
      ∃ A : Adjuster J (lm47InflatedOrder n)
          (2 * Parameters.lmSimpleRadius (1 / 1024) n) 1,
        Disjoint U A.verts := by
    simpa [n] using hRobust J B hdRobust hexp hdegreeNat hfree
  have hscale :
      220 * Parameters.lmRadius (1 / 1024) n ^ 2 +
          22 * Parameters.lmRadius (1 / 1024) n + 1 ≤ q :=
    adjuster_scale_le_of_log_seven_le (hExact n hnExact) (by
      simpa [n] using hlower)
  apply lemma4_8_of_lm311Numerics_and_simple_adjuster_supply
    B data hexp hdegreeNat growth scales num C hC hxy hradius
      hsupply hscale
  · simpa [n] using hupper
  · exact hparity

/-- Liu--Montgomery Theorem 2.7: in every sufficiently large-degree finite
bipartite expander excluding the balanced one-subdivision, every
parity-compatible length in the paper's interval occurs as an exact path
length between any two distinct prescribed vertices. -/
theorem liuMontgomery_theorem2_7 :
    ∃ d₀ : ℕ, ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj]
      (B : Bipartition J) {d : ℕ},
      d₀ ≤ d →
      IsLMExpander J (1 / 1024) ((1 / 64) * (d : ℝ)) →
      (∀ v : W, (d : ℝ) ≤ J.degree v) →
      ¬ oneSubdivisionClique (d / 2) ⊑ J →
      ∀ {x y : W} {q : ℕ}, x ≠ y →
        ParityCompatible B x y q →
        Real.log (Fintype.card W : ℝ) ^ 7 ≤ q →
        (q : ℝ) ≤ Parameters.lmPathScale (Fintype.card W : ℝ) →
        HasPathBetweenLength J x y q := by
  apply eventually_exact_paths_of_robustSimpleAdjusterSupply
  exact SmallSimpleAdjusterCandidate.liuMontgomery_lemma4_3_inflated_supply

end Erdos63

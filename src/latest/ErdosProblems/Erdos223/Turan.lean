/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The Erdős–Stone edge bound used for Erdős Problem 223

This file turns the minimum-degree form of the Erdős–Stone theorem into
an edge-count estimate.  In particular, a graph with no balanced complete
`(p + 1)`-partite subgraph of fixed part size `t` has, eventually in its
number `m` of vertices, at most

`(((p : ℝ) - 1) / (2 * p) + ε) * m²`

edges.  The statement is uniform over the vertex type and graph.
-/

open Filter
open scoped BigOperators SimpleGraph

namespace Erdos223
namespace Turan

open Finset Fintype SimpleGraph

/-- A minimum-degree exclusion estimate gives a quadratic extremal-number bound.

The constant `N²` covers the finitely many orders below the threshold `N`.
Above `N`, delete a minimum-degree vertex and induct. -/
theorem extremalNumber_le_quadratic_of_minDegree
    {W : Type*} (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hmd : ∀ n, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      H.Free G → (G.minDegree : ℝ) < c * n) :
    ∀ n, (extremalNumber n H : ℝ) ≤ (N : ℝ) ^ 2 + c * n * (n + 1) / 2 := by
  intro n
  induction n with
  | zero =>
    conv_lhs => rw [← Fintype.card_fin 0]
    rw [extremalNumber_le_iff_of_nonneg H]
    · intro G _ _
      have he : (#G.edgeFinset : ℕ) ≤ 0 := by
        simpa using G.card_edgeFinset_le_card_choose_two
      have he0 : (#G.edgeFinset : ℝ) = 0 := by
        exact_mod_cast Nat.eq_zero_of_le_zero he
      rw [he0]
      positivity
    · positivity
  | succ n ih =>
    conv_lhs => rw [← Fintype.card_fin (n + 1)]
    rw [extremalNumber_le_iff_of_nonneg H]
    · intro G _ hfree
      norm_num at ⊢
      by_cases hn : N ≤ n + 1
      · let : Nonempty (Fin (n + 1)) := Fin.pos_iff_nonempty.mp (by omega)
        obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        have hdeg : (G.degree v : ℝ) < c * (n + 1) := by
          rw [← hv]
          simpa only [Nat.cast_add, Nat.cast_one] using hmd (n + 1) hn G hfree
        have hdel : (#(G.deleteIncidenceSet v).edgeFinset : ℝ) ≤
            (extremalNumber n H : ℝ) := by
          simpa using G.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
        have hsplit : #G.edgeFinset = #(G.deleteIncidenceSet v).edgeFinset + G.degree v := by
          rw [G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (G.degree_le_card_edgeFinset (v := v))]
        rw [hsplit, Nat.cast_add]
        calc
          (#(G.deleteIncidenceSet v).edgeFinset : ℝ) + G.degree v
              ≤ (extremalNumber n H : ℝ) + G.degree v := add_le_add hdel le_rfl
          _ ≤ ((N : ℝ) ^ 2 + c * n * (n + 1) / 2) + G.degree v :=
            add_le_add ih le_rfl
          _ ≤ (N : ℝ) ^ 2 + c * (n + 1) * (n + 1 + 1) / 2 := by
            nlinarith
      · have hnlt : n + 1 < N := by omega
        calc
          (#G.edgeFinset : ℝ) ≤ (((n + 1).choose 2 : ℕ) : ℝ) := by
            exact_mod_cast (by simpa using G.card_edgeFinset_le_card_choose_two)
          _ ≤ ((N ^ 2 : ℕ) : ℝ) := by
            exact_mod_cast (calc
              (n + 1).choose 2 ≤ (n + 1) ^ 2 := Nat.choose_le_pow _ _
              _ ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) _)
          _ ≤ ((N : ℝ) ^ 2 + c * (n + 1) * (n + 1 + 1) / 2 : ℝ) := by
            norm_num
            positivity
    · positivity

/-- The preceding extremal-number estimate, transferred to a graph on any finite type. -/
theorem card_edgeFinset_le_quadratic_of_minDegree
    {V W : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hmd : ∀ n, N ≤ n → ∀ (J : SimpleGraph (Fin n)) [DecidableRel J.Adj],
      H.Free J → (J.minDegree : ℝ) < c * n)
    (hfree : H.Free G) :
    (#G.edgeFinset : ℝ) ≤
      (N : ℝ) ^ 2 + c * Fintype.card V * (Fintype.card V + 1) / 2 := by
  have hcard : (#G.edgeFinset : ℝ) ≤ (extremalNumber (Fintype.card V) H : ℝ) := by
    exact_mod_cast G.card_edgeFinset_le_extremalNumber hfree
  exact hcard.trans
    (extremalNumber_le_quadratic_of_minDegree H c hc N hmd (Fintype.card V))

/-- Erdős–Stone plus minimum-degree deletion, before absorbing lower-order terms. -/
theorem exists_card_edgeFinset_le_completeEquipartite
    (p t : ℕ) (hp : 0 < p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (completeEquipartiteGraph (p + 1) t).Free G →
      (#G.edgeFinset : ℝ) ≤ (N : ℝ) ^ 2 +
        (1 - 1 / (p : ℝ) + δ) * Fintype.card V * (Fintype.card V + 1) / 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree hδ p t)
  refine ⟨N, fun V _ G _ hfree ↦ card_edgeFinset_le_quadratic_of_minDegree
    (completeEquipartiteGraph (p + 1) t) (1 - 1 / (p : ℝ) + δ) ?_ N ?_ hfree⟩
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have : 1 / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr hp1
    linarith
  · intro n hn J _ hfreeJ
    by_contra hlt
    apply hfreeJ
    exact hN n hn (le_of_not_gt hlt)

/-- A uniform version of the Erdős–Stone edge estimate.

The linear term is absorbed by completing the square, leaving an additive
constant independent of the vertex type and graph. -/
theorem exists_uniform_card_edgeFinset_le_completeEquipartite
    (p t : ℕ) (hp : 0 < p) { η : ℝ } (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (completeEquipartiteGraph (p + 1) t).Free G →
        (#G.edgeFinset : ℝ) ≤
          (((p : ℝ) - 1) / (2 * p) + η) * (Fintype.card V : ℝ) ^ 2 + C := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_completeEquipartite p t hp hη
  let c : ℝ := 1 - 1 / (p : ℝ) + η
  let C : ℝ := (N : ℝ) ^ 2 + c ^ 2 / (8 * η)
  refine ⟨C, by dsimp [C]; positivity, fun V _ G _ hfree ↦ ?_⟩
  let m : ℝ := Fintype.card V
  have hm : 0 ≤ m := by positivity
  have hpℝ : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hb := hN V G hfree
  have hyoung : c / 2 * m - η / 2 * m ^ 2 ≤ c ^ 2 / (8 * η) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * η)).2
    nlinarith [sq_nonneg (2 * η * m - c)]
  have hcoeff : ((p : ℝ) - 1) / (2 * p) = (1 - 1 / (p : ℝ)) / 2 := by
    field_simp
  rw [hcoeff]
  dsimp [m, c] at hyoung
  dsimp [C, c] at ⊢
  nlinarith

/-- The eventual pure quadratic Erdős–Stone edge bound.

For fixed `p` and `t`, every sufficiently large graph avoiding
`completeEquipartiteGraph (p + 1) t` has edge density at most the Turán
coefficient `(p - 1) / (2p)`, up to an arbitrary positive error. -/
theorem eventually_card_edgeFinset_le_completeEquipartite
    (p t : ℕ) (hp : 2 ≤ p) { ε : ℝ } (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ (V : Type*) [Fintype V], Fintype.card V = m →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        (completeEquipartiteGraph (p + 1) t).Free G →
        (#G.edgeFinset : ℝ) ≤
          (((p : ℝ) - 1) / (2 * p) + ε) * (m : ℝ) ^ 2 := by
  obtain ⟨C, _, hbound⟩ :=
    exists_uniform_card_edgeFinset_le_completeEquipartite p t (by omega) (half_pos hε)
  have ht : Tendsto (fun m : ℕ ↦ ε / 2 * (m : ℝ) ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos hε)
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  filter_upwards [tendsto_atTop.1 ht C] with m hm
  intro V _ hcard G _ hfree
  have hb := hbound V G hfree
  rw [hcard] at hb
  nlinarith

end Turan
end Erdos223

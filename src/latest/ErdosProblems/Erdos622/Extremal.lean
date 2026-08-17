/-
Copyright 2026 The Lean-Proofs Authors.

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
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The sharpness construction for Erdős Problem 622

For `n ≥ 2`, the graph constructed here has vertex classes of sizes `n - 1`
and `n + 1`, all cross edges, and a spanning cycle on the larger class.  Thus
every vertex has degree `n + 1`.  This is the extremal family used by
Draganić--Keevash--Müyesser to show that the constant `1 / 2` in the
asymptotic theorem cannot be increased.
-/

namespace Erdos622

open SimpleGraph

/-- The complete bipartite graph with parts of sizes `n - 1` and `n + 1`,
augmented by a spanning cycle on the larger part. -/
def extremalGraph (n : ℕ) : SimpleGraph (Fin (n - 1) ⊕ Fin (n + 1)) where
  Adj
    | .inl _, .inl _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr u, .inr v => (cycleGraph (n + 1)).Adj u v
  symm.symm
    | .inl _, .inl _ => id
    | .inl _, .inr _ => id
    | .inr _, .inl _ => id
    | .inr u, .inr v => (cycleGraph (n + 1)).adj_symm

instance extremalGraph.instDecidableRel (n : ℕ) : DecidableRel (extremalGraph n).Adj := by
  intro u v
  cases u <;> cases v <;> simp only [extremalGraph]
  all_goals infer_instance

@[simp] theorem extremalGraph_adj_inl_inl (n : ℕ) (u v : Fin (n - 1)) :
    ¬(extremalGraph n).Adj (.inl u) (.inl v) := by
  simp [extremalGraph]

@[simp] theorem extremalGraph_adj_inl_inr (n : ℕ) (u : Fin (n - 1))
    (v : Fin (n + 1)) : (extremalGraph n).Adj (.inl u) (.inr v) := by
  simp [extremalGraph]

@[simp] theorem extremalGraph_adj_inr_inl (n : ℕ) (u : Fin (n + 1))
    (v : Fin (n - 1)) : (extremalGraph n).Adj (.inr u) (.inl v) := by
  simp [extremalGraph]

@[simp] theorem extremalGraph_adj_inr_inr (n : ℕ) (u v : Fin (n + 1)) :
    (extremalGraph n).Adj (.inr u) (.inr v) ↔ (cycleGraph (n + 1)).Adj u v := by
  rfl

/-- For positive `n`, the two vertex classes have altogether `2 * n`
vertices. -/
theorem card_extremalVertexType (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Fin (n - 1) ⊕ Fin (n + 1)) = 2 * n := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- The complete bipartite graph between the two displayed classes is a
spanning subgraph of the extremal graph. -/
theorem completeBipartiteGraph_le_extremalGraph (n : ℕ) :
    completeBipartiteGraph (Fin (n - 1)) (Fin (n + 1)) ≤ extremalGraph n := by
  intro u v huv
  cases u <;> cases v <;> simp_all [extremalGraph]

/-- The cycle placed on the larger class embeds as an induced copy in the
extremal graph. -/
def extremalCycleEmbedding (n : ℕ) :
    cycleGraph (n + 1) ↪g extremalGraph n where
  toFun := Sum.inr
  inj' := by
    intro u v h
    exact Sum.inr.inj h
  map_rel_iff' := Iff.rfl

theorem extremalGraph_degree_inl (n : ℕ) (u : Fin (n - 1)) :
    (extremalGraph n).degree (.inl u) = n + 1 := by
  let e : (extremalGraph n).neighborSet (.inl u) ≃ Fin (n + 1) := {
    toFun x := by
      rcases x with ⟨v, hv⟩
      cases v with
      | inl v => exact False.elim (by simpa using hv)
      | inr v => exact v
    invFun v := ⟨.inr v, by simp⟩
    left_inv x := by
      rcases x with ⟨v, hv⟩
      cases v with
      | inl v => exact False.elim (by simpa using hv)
      | inr v => rfl
    right_inv v := rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa using Fintype.card_congr e

theorem extremalGraph_degree_inr (n : ℕ) (hn : 2 ≤ n) (u : Fin (n + 1)) :
    (extremalGraph n).degree (.inr u) = n + 1 := by
  have hcycle : (cycleGraph (n + 1)).degree u = 2 := by
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ k =>
        exact SimpleGraph.cycleGraph_degree_three_le (n := k) (v := u)
  let e : (extremalGraph n).neighborSet (.inr u) ≃
      Fin (n - 1) ⊕ (cycleGraph (n + 1)).neighborSet u := {
    toFun x := by
      rcases x with ⟨v, hv⟩
      cases v with
      | inl v => exact .inl v
      | inr v => exact .inr ⟨v, by simpa using hv⟩
    invFun v := by
      cases v with
      | inl v => exact ⟨.inl v, by simp⟩
      | inr v => exact ⟨.inr v, v.2⟩
    left_inv x := by
      rcases x with ⟨v, hv⟩
      cases v <;> rfl
    right_inv v := by
      cases v <;> rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  calc
    Fintype.card ((extremalGraph n).neighborSet (.inr u)) =
        Fintype.card (Fin (n - 1) ⊕ (cycleGraph (n + 1)).neighborSet u) :=
      Fintype.card_congr e
    _ = (n - 1) + 2 := by
      rw [Fintype.card_sum, Fintype.card_fin,
        SimpleGraph.card_neighborSet_eq_degree, hcycle]
    _ = n + 1 := by omega

/-- The sharpness graph is `(n + 1)`-regular for every `n ≥ 2`. -/
theorem extremalGraph_isRegular (n : ℕ) (hn : 2 ≤ n) :
    (extremalGraph n).IsRegularOfDegree (n + 1) := by
  intro v
  cases v with
  | inl u => exact extremalGraph_degree_inl n u
  | inr u => exact extremalGraph_degree_inr n hn u

/-- A copy of the extremal graph on the canonical vertex type `Fin (2 * n)`. -/
noncomputable def extremalFinGraph (n : ℕ) (hn : 1 ≤ n) :
    SimpleGraph (Fin (2 * n)) :=
  (extremalGraph n).overFin (card_extremalVertexType n hn)

noncomputable instance extremalFinGraph.instDecidableRel (n : ℕ) (hn : 1 ≤ n) :
    DecidableRel (extremalFinGraph n hn).Adj := Classical.decRel _

/-- The canonically relabelled extremal graph remains `(n + 1)`-regular. -/
theorem extremalFinGraph_isRegular (n : ℕ) (hn : 2 ≤ n) :
    (extremalFinGraph n (le_trans (by decide) hn)).IsRegularOfDegree (n + 1) := by
  let e := (extremalGraph n).overFinIso
    (card_extremalVertexType n (le_trans (by decide) hn))
  intro v
  unfold extremalFinGraph
  rw [← e.apply_symm_apply v, e.degree_eq]
  exact extremalGraph_isRegular n hn (e.symm v)

end Erdos622

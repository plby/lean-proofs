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
import ErdosProblems.Erdos622.External.Erdos76.Kahn
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Greedy edge colouring of finite indexed hypergraphs

The conflict graph has one vertex for each indexed hyperedge and joins two
indices exactly when their supports intersect.  A vertex colouring of this
graph is therefore a proper edge colouring of the hypergraph, and every colour
class is a matching.  We construct the colouring directly by finite induction,
using at most one more colour than the maximum conflict degree.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The simple graph on indexed hyperedges whose adjacency relation is support
intersection. -/
def conflictGraph (H : FiniteHypergraph V E) : SimpleGraph E where
  Adj := H.Conflicts
  symm.symm := by
    intro e f h
    exact h.symm
  loopless.irrefl := by
    intro e h
    exact h.1 rfl

/-- A proper edge colouring of an indexed hypergraph by `q` colours. -/
abbrev EdgeColoring (H : FiniteHypergraph V E) (q : ℕ) :=
  H.conflictGraph.Coloring (Fin q)

/-- Maximum number of indexed hyperedges conflicting with one indexed edge. -/
def maxConflictDegree (H : FiniteHypergraph V E) : ℕ :=
  (univ : Finset E).sup H.conflictDegree

lemma conflictDegree_le_maxConflictDegree (H : FiniteHypergraph V E) (e : E) :
    H.conflictDegree e ≤ H.maxConflictDegree := by
  exact Finset.le_sup (f := H.conflictDegree) (mem_univ e)

/-- The indices in `S` which conflict with `e`. -/
private def earlierConflicts (H : FiniteHypergraph V E) (S : Finset E) (e : E) : Finset E :=
  S.filter fun f ↦ H.Conflicts e f

private lemma earlierConflicts_card_le (H : FiniteHypergraph V E) (S : Finset E) (e : E) :
    (H.earlierConflicts S e).card ≤ H.conflictDegree e := by
  apply card_le_card
  intro f hf
  simp only [earlierConflicts, mem_filter] at hf
  exact mem_filter.mpr ⟨mem_univ f, hf.2⟩

/-- Greedy partial-colouring lemma.  The function is total on `E`, but
properness is required only on `S`; this makes insertion induction painless. -/
private lemma exists_coloring_proper_on (H : FiniteHypergraph V E) (q : ℕ)
    (hq : 0 < q) (S : Finset E)
    (hdegree : ∀ e ∈ S, H.conflictDegree e < q) :
    ∃ c : E → Fin q, ∀ ⦃e f : E⦄, e ∈ S → f ∈ S → H.Conflicts e f → c e ≠ c f := by
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨fun _ ↦ ⟨0, hq⟩, by simp⟩
  | @insert e S heS ihS =>
      have hdegreeS : ∀ f ∈ S, H.conflictDegree f < q := by
        intro f hf
        exact hdegree f (mem_insert_of_mem hf)
      obtain ⟨c, hc⟩ := ihS hdegreeS
      let N : Finset E := H.earlierConflicts S e
      let used : Finset (Fin q) := N.image c
      have hNcard : N.card ≤ H.conflictDegree e := H.earlierConflicts_card_le S e
      have husedcard : used.card < q := by
        calc
          used.card ≤ N.card := card_image_le
          _ ≤ H.conflictDegree e := hNcard
          _ < q := hdegree e (mem_insert_self e S)
      have hexists : ∃ a : Fin q, a ∉ used := by
        by_contra hnone
        push Not at hnone
        have hused : used = univ := eq_univ_of_forall hnone
        have : q ≤ used.card := by simp [hused]
        omega
      obtain ⟨a, ha⟩ := hexists
      let c' : E → Fin q := Function.update c e a
      refine ⟨c', ?_⟩
      intro f g hf hg hfg
      by_cases hfe : f = e
      · have hge : g ≠ e := by
          intro hge
          exact hfg.1 (hfe.trans hge.symm)
        have hgS : g ∈ S := by simpa [hge] using hg
        have heg : H.Conflicts e g := hfe ▸ hfg
        have hgN : g ∈ N := by simp [N, earlierConflicts, hgS, heg]
        have hcg : c g ∈ used := mem_image.mpr ⟨g, hgN, rfl⟩
        have hacg : a ≠ c g := by
          intro hacg
          apply ha
          rw [hacg]
          exact hcg
        simpa [c', hfe, hge] using hacg
      · have hfS : f ∈ S := by simpa [hfe] using hf
        by_cases hge : g = e
        · have hef : H.Conflicts e f := (hge ▸ hfg).symm
          have hfN : f ∈ N := by simp [N, earlierConflicts, hfS, hef]
          have hcf : c f ∈ used := mem_image.mpr ⟨f, hfN, rfl⟩
          have hcfa : c f ≠ a := by
            intro hcfa
            apply ha
            rw [← hcfa]
            exact hcf
          simpa [c', hfe, hge] using hcfa
        · have hgS : g ∈ S := by simpa [hge] using hg
          simpa [c', hfe, hge] using hc hfS hgS hfg

/-- A finite indexed hypergraph has a proper edge colouring with one more
colour than its maximum conflict degree. -/
theorem exists_edgeColoring_maxConflictDegree_add_one (H : FiniteHypergraph V E) :
    Nonempty (H.EdgeColoring (H.maxConflictDegree + 1)) := by
  let q := H.maxConflictDegree + 1
  obtain ⟨c, hc⟩ := H.exists_coloring_proper_on q (Nat.succ_pos _)
    (univ : Finset E) (by
      intro e _
      exact Nat.lt_succ_of_le (H.conflictDegree_le_maxConflictDegree e))
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro e f hef
  exact hc (mem_univ e) (mem_univ f) hef

/-- A maximum conflict-degree bound gives a colouring with `Delta + 1`
colours, allowing unused colours. -/
theorem exists_edgeColoring_of_conflictDegree_le (H : FiniteHypergraph V E)
    (Delta : ℕ) (hdegree : ∀ e, H.conflictDegree e ≤ Delta) :
    Nonempty (H.EdgeColoring (Delta + 1)) := by
  obtain ⟨c, hc⟩ := H.exists_coloring_proper_on (Delta + 1) (Nat.succ_pos _)
    (univ : Finset E) (by
      intro e _
      exact Nat.lt_succ_of_le (hdegree e))
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro e f hef
  exact hc (mem_univ e) (mem_univ f) hef

/-- Safe greedy residual bound under uniformity and a maximum edge-degree
bound.  The `+1` is harmless in asymptotic applications. -/
theorem exists_edgeColoring_uniform_degree (H : FiniteHypergraph V E)
    {k D : ℕ} (hunif : H.IsUniform k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    Nonempty (H.EdgeColoring (k * D + 1)) :=
  H.exists_edgeColoring_of_conflictDegree_le (k * D)
    (H.conflictDegree_le_uniform_mul hunif hdegree)

/-- The finite fibre of one edge colour. -/
def EdgeColoring.colorClass {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (i : Fin q) : Finset E :=
  (univ : Finset E).filter fun e ↦ c e = i

/-- Restrict a colour class to an arbitrary selected edge set. -/
def EdgeColoring.restrictedColorClass {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) (i : Fin q) : Finset E :=
  S.filter fun e ↦ c e = i

@[simp] lemma EdgeColoring.mem_colorClass {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (i : Fin q) (e : E) :
    e ∈ c.colorClass i ↔ c e = i := by
  simp [EdgeColoring.colorClass]

@[simp] lemma EdgeColoring.mem_restrictedColorClass {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) (i : Fin q) (e : E) :
    e ∈ c.restrictedColorClass S i ↔ e ∈ S ∧ c e = i := by
  simp [EdgeColoring.restrictedColorClass]

/-- Every colour fibre is a matching of indexed hyperedges. -/
lemma EdgeColoring.colorClass_isMatching {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (i : Fin q) :
    H.IsMatching (c.colorClass i) := by
  intro e he f hf hef
  have hec : c e = i := (c.mem_colorClass i e).mp he
  have hfc : c f = i := (c.mem_colorClass i f).mp hf
  by_contra hdisj
  exact c.valid ⟨hef, hdisj⟩ (hec.trans hfc.symm)

/-- Restricted colour fibres remain matchings. -/
lemma EdgeColoring.restrictedColorClass_isMatching
    {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) (i : Fin q) :
    H.IsMatching (c.restrictedColorClass S i) := by
  intro e he f hf hef
  have hec : c e = i := (c.mem_restrictedColorClass S i e).mp he |>.2
  have hfc : c f = i := (c.mem_restrictedColorClass S i f).mp hf |>.2
  by_contra hdisj
  exact c.valid ⟨hef, hdisj⟩ (hec.trans hfc.symm)

/-- The colour fibres partition any selected family, in cardinality form. -/
lemma EdgeColoring.sum_card_restrictedColorClass
    {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) :
    ∑ i : Fin q, (c.restrictedColorClass S i).card = S.card := by
  symm
  simpa only [EdgeColoring.restrictedColorClass] using
    (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (univ : Finset (Fin q))) (f := fun e ↦ c e) (by simp))

/-- The union of restricted colour fibres is the original selected family. -/
lemma EdgeColoring.biUnion_restrictedColorClass
    {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) :
    (univ : Finset (Fin q)).biUnion (c.restrictedColorClass S) = S := by
  ext e
  simp [EdgeColoring.restrictedColorClass]

/-- Some colour fibre has at least the average cardinality, without division. -/
lemma EdgeColoring.exists_card_le_mul_restrictedColorClass
    {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) (hq : 0 < q) :
    ∃ i : Fin q, S.card ≤ q * (c.restrictedColorClass S i).card := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (univ : Finset (Fin q))
    (fun j ↦ (c.restrictedColorClass S j).card)
      ⟨⟨0, hq⟩, mem_univ _⟩
  refine ⟨i, ?_⟩
  rw [← c.sum_card_restrictedColorClass S]
  calc
    ∑ j : Fin q, (c.restrictedColorClass S j).card ≤
        ∑ _j : Fin q, (c.restrictedColorClass S i).card := by
      exact sum_le_sum fun j _ ↦ hi j (mem_univ j)
    _ = q * (c.restrictedColorClass S i).card := by simp

/-- Real-valued average form used when restricting a PS edge colouring to an
embedded copy of the original hypergraph. -/
lemma EdgeColoring.exists_div_le_card_restrictedColorClass
    {H : FiniteHypergraph V E} {q : ℕ}
    (c : H.EdgeColoring q) (S : Finset E) (hq : 0 < q) :
    ∃ i : Fin q,
      (S.card : ℝ) / (q : ℝ) ≤ (c.restrictedColorClass S i).card := by
  obtain ⟨i, hi⟩ := c.exists_card_le_mul_restrictedColorClass S hq
  refine ⟨i, (div_le_iff₀ (by exact_mod_cast hq)).2 ?_⟩
  exact_mod_cast (by simpa [Nat.mul_comm] using hi)

end FiniteHypergraph

end

end Erdos76

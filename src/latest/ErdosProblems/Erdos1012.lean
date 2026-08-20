/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos746.PathMax
import ErdosProblems.Erdos746.Posa
import ErdosProblems.Erdos916.Blocks
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Grind
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Erdős Problem 1012

Woodall's sharp edge theorem for cycles of prescribed large length.  The
detailed mathematical proof and the Leanization map are in `tex/1012.tex`.
-/

open scoped Sym2
open Finset SimpleGraph
open Erdos746.PathMax

namespace Erdos1012

universe u

attribute [local instance] Classical.propDecidable Classical.decEq

/-- `G` contains a simple cycle with exactly `d` edges. -/
def HasCycleLength {V : Type u} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = d

/-- `G` has a simple cycle with at least `d` edges. -/
def HasCycleAtLeast {V : Type u} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ d ≤ p.length

lemma HasCycleLength.map
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {d : ℕ} (h : HasCycleLength G d) (f : G →g H)
    (hf : Function.Injective f) : HasCycleLength H d := by
  obtain ⟨v, p, hp, hlen⟩ := h
  exact ⟨f v, p.map f, hp.map hf, by simpa using hlen⟩

lemma HasCycleAtLeast.mono {V : Type u} {G : SimpleGraph V} {d e : ℕ}
    (h : HasCycleAtLeast G e) (hde : d ≤ e) : HasCycleAtLeast G d := by
  obtain ⟨v, p, hp, hlen⟩ := h
  exact ⟨v, p, hp, hde.trans hlen⟩

/-- A path together with an external vertex adjacent to both endpoints
closes to a cycle exactly two edges longer than the path. -/
lemma hasCycleLength_add_two_of_path_external
    {V : Type u} {G : SimpleGraph V} {x a b : V} {p : G.Walk a b}
    (hp : p.IsPath) (hpos : 0 < p.length) (hx : x ∉ p.support)
    (hxb : G.Adj x b) (hxa : G.Adj x a) :
    HasCycleLength G (p.length + 2) := by
  let q : G.Walk a x := p.concat hxb.symm
  have hq : q.IsPath := hp.concat hx hxb.symm
  have hqLen : q.length = p.length + 1 := by simp [q]
  have hedge : s(a, x) ∉ q.reverse.edges := by
    intro he
    have he' : s(x, a) ∈ q.reverse.edges := by simpa [Sym2.eq_swap] using he
    have hone := hq.reverse.length_eq_one_of_mem_edges he'
    rw [Walk.length_reverse, hqLen] at hone
    omega
  let c : G.Walk a a := Walk.cons hxa.symm q.reverse
  have hc : c.IsCycle :=
    SimpleGraph.Path.cons_isCycle ⟨q.reverse, hq.reverse⟩ hxa.symm hedge
  refine ⟨a, c, hc, ?_⟩
  simp [c, q]

/-- The preceding construction applied to an initial arc of a cycle. -/
lemma hasCycleLength_add_two_of_cycle_external
    {V : Type u} {G : SimpleGraph V} {x a : V} {c : G.Walk a a}
    (hc : c.IsCycle) (hx : x ∉ c.support) {r : ℕ}
    (hrpos : 0 < r) (hrlt : r < c.length)
    (hxa : G.Adj x a) (hxr : G.Adj x (c.getVert r)) :
    HasCycleLength G (r + 2) := by
  let p := c.take r
  have hp : p.IsPath := hc.isPath_take hrlt
  have hpLen : p.length = r := by simp [p, Nat.min_eq_left hrlt.le]
  have hxP : x ∉ p.support := by
    intro hxp
    rw [Walk.support_take] at hxp
    exact hx ((List.take_prefix (r + 1) c.support).subset hxp)
  have hcycle := hasCycleLength_add_two_of_path_external hp
    (by rw [hpLen]; exact hrpos) hxP (by simpa [p]) hxa
  simpa [hpLen] using hcycle

/-- The cyclic positions `0,…,n-1` of a Hamiltonian cycle are an
equivalence with the vertices. -/
noncomputable def hamiltonianCycleGetVertEquiv
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a : V} {c : G.Walk a a}
    (hc : c.IsHamiltonianCycle) : Fin c.length ≃ V :=
  Equiv.ofBijective (fun i : Fin c.length ↦ c.getVert i.val) <| by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact hc.isCycle.getVert_injOn'
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hij
    · simp [hc.length_eq]

@[simp] lemma hamiltonianCycleGetVertEquiv_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a : V} {c : G.Walk a a}
    (hc : c.IsHamiltonianCycle) (i : Fin c.length) :
    hamiltonianCycleGetVertEquiv hc i = c.getVert i.val := rfl

/-- A segment of a simple cycle whose indices lie strictly after `r`
does not contain the vertex in position `r`. -/
lemma getVert_not_mem_support_drop_take_of_lt
    {V : Type u} {G : SimpleGraph V} {a : V} {c : G.Walk a a}
    (hc : c.IsCycle) {r start len : ℕ} (hrs : r < start)
    (hend : start + len < c.length) :
    c.getVert r ∉ ((c.drop start).take len).support := by
  intro hmem
  obtain ⟨t, ht, htle⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
  have hlen : ((c.drop start).take len).length = len := by
    simp [Nat.min_eq_left (by omega : len ≤ c.length - start)]
  have htlen : t ≤ len := by simpa [hlen] using htle
  have hget : c.getVert (start + t) = c.getVert r := by
    simpa [Walk.take_getVert, Walk.drop_getVert,
      Nat.min_eq_right htlen] using ht
  have heq : start + t = r := by
    exact hc.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hget
  omega

/-- The elementary two-chord splice used in Bondy's degree-sum lemma,
in the case in which the prescribed cyclic shift does not wrap. -/
lemma hasCycleLength_of_two_chords_nowrap
    {V : Type u} {G : SimpleGraph V} {a : V} {c : G.Walk a a}
    (hc : c.IsCycle) {d k f : ℕ}
    (hd : 3 ≤ d) (hk : 2 ≤ k) (hkf : k ≤ f)
    (hf : f < c.length) (hgap : f - k = d - 3)
    (hak : G.Adj (c.getVert 0) (c.getVert k))
    (hbf : G.Adj (c.getVert 1) (c.getVert f)) :
    HasCycleLength G d := by
  let arc := (c.drop k).take (f - k)
  have harc : arc.IsPath := (hc.isPath_drop (by omega)).take _
  have harcLen : arc.length = f - k := by
    simp [arc, Nat.min_eq_left (by omega : f - k ≤ c.length - k)]
  have hbArc : c.getVert 1 ∉ arc.support := by
    exact getVert_not_mem_support_drop_take_of_lt hc (by omega) (by omega)
  have hfb : G.Adj ((c.drop k).getVert (f - k)) (c.getVert 1) := by
    rw [Walk.drop_getVert, show k + (f - k) = f by omega]
    exact hbf.symm
  let q := arc.concat hfb
  have hq : q.IsPath := harc.concat hbArc hfb
  have haArc : c.getVert 0 ∉ arc.support := by
    exact getVert_not_mem_support_drop_take_of_lt hc (by omega) (by omega)
  have hab : c.getVert 0 ≠ c.getVert 1 := by
    intro heq
    have := hc.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) heq
    omega
  have haQ : c.getVert 0 ∉ q.support := by
    simp only [q, Walk.support_concat, List.mem_append, List.mem_singleton]
    exact fun h ↦ h.elim haArc (fun h ↦ hab h)
  have hba : G.Adj (c.getVert 1) (c.getVert 0) := by
    exact (c.adj_getVert_succ (i := 0) (by omega)).symm
  let p := q.concat hba
  have hp : p.IsPath := hq.concat haQ hba
  have hedge : s(c.getVert 0, c.getVert k) ∉ p.edges := by
    intro he
    have he' : s(c.getVert k, c.getVert 0) ∈ p.edges := by
      simpa [Sym2.eq_swap] using he
    have hone : p.length = 1 := hp.length_eq_one_of_mem_edges he'
    have hplen : p.length = (f - k) + 2 := by simp [p, q, harcLen]
    omega
  let z : G.Walk (c.getVert 0) (c.getVert 0) := Walk.cons hak p
  have hz : z.IsCycle :=
    SimpleGraph.Path.cons_isCycle ⟨p, hp⟩ hak hedge
  refine ⟨c.getVert 0, z, hz, ?_⟩
  simp only [z, Walk.length_cons, p, Walk.length_concat, q, harcLen]
  omega

theorem hasCycleLength_iff_isContained {V : Type u} {G : SimpleGraph V}
    {d : ℕ} (hd : 3 ≤ d) :
    HasCycleLength G d ↔ SimpleGraph.cycleGraph d ⊑ G := by
  simpa [HasCycleLength] using (SimpleGraph.cycleGraph_isContained_iff (n := d) (by omega)).symm

/-- The extremal edge count immediately below Woodall's threshold. -/
def woodallBound (n k : ℕ) : ℕ :=
  (n - k - 1).choose 2 + (k + 2).choose 2

/-- The exact assertion demanded at a fixed pair `(n,k)`. -/
def WoodallConclusion (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    woodallBound n k + 1 ≤ G.edgeFinset.card →
      ∀ d, 3 ≤ d → d ≤ n - k → HasCycleLength G d

/-- `N` is a valid eventual cutoff in Erdős Problem 1012. -/
def ValidCutoff (k N : ℕ) : Prop :=
  ∀ n, N ≤ n → WoodallConclusion n k

lemma choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose]
  simp [Nat.add_comm]

lemma choose_two_add_two (m : ℕ) : (m + 2).choose 2 = m.choose 2 + 2 * m + 1 := by
  rw [show m + 2 = (m + 1) + 1 by omega, choose_two_succ, choose_two_succ]
  omega

lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  rw [mul_comm, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self m)]

/-- The quadratic `x ↦ x (n-x)` is minimized at the endpoints of a
symmetric integer interval. -/
lemma concave_product_ge {n q x : ℕ} (hqx : q ≤ x) (hxq : x ≤ n - q) :
    q * (n - q) ≤ x * (n - x) := by
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hqx
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le hxq
  have hnsub : n - (q + y) = q + z := by omega
  rw [hz, hnsub]
  nlinarith [Nat.zero_le (y * z)]

/-- The numerical inequality at the end of Woodall's endpoint-fan
argument.  Here `a` and `b` are the endpoint degrees. -/
lemma endpoint_handshake_bound {N q a b : ℕ}
    (hN : 1 ≤ N) (hqa : q ≤ a) (hqb : q ≤ b) (hab : a + b ≤ N - 1) :
    a * a + b * b + (N - b - a) * (N - 1) ≤
      2 * ((N - q).choose 2 + (q + 1).choose 2) := by
  have hqN : q ≤ N - 1 := by omega
  have haUpper : a ≤ (N - 1) - q := by omega
  have hbUpper : b ≤ (N - 1) - q := by omega
  have hca := concave_product_ge (n := N - 1) hqa haUpper
  have hcb := concave_product_ge (n := N - 1) hqb hbUpper
  have hsubN : N - q + q = N := by omega
  have hsubN1 : N - q - 1 = N - 1 - q := by omega
  have hsubq : N - 1 - q + q = N - 1 := by omega
  have hNqRep : N - q = (N - 1 - q) + 1 := by omega
  have hNRep : N = (N - 1 - q) + q + 1 := by omega
  have hN1Rep : N - 1 = (N - 1 - q) + q := by omega
  have hthreshold :
      2 * ((N - q).choose 2 + (q + 1).choose 2) +
          2 * (q * (N - 1 - q)) = N * (N - 1) := by
    rw [Nat.mul_add, two_mul_choose_two, two_mul_choose_two]
    simp only [Nat.add_sub_cancel]
    calc
      (N - q) * (N - q - 1) + (q + 1) * q +
            2 * (q * (N - 1 - q)) =
          ((N - 1 - q) + 1) * (N - 1 - q) + (q + 1) * q +
            2 * (q * (N - 1 - q)) := by rw [hsubN1, hNqRep]
      _ = ((N - 1 - q) + q + 1) * ((N - 1 - q) + q) := by ring
      _ = N * (N - 1) := by rw [← hNRep, ← hN1Rep]
  have hsubab : N - b - a + b + a = N := by omega
  have hsuba : N - 1 - a + a = N - 1 := by omega
  have hsubb : N - 1 - b + b = N - 1 := by omega
  have hdegreeIdentity :
      a * a + b * b + (N - b - a) * (N - 1) +
          a * (N - 1 - a) + b * (N - 1 - b) = N * (N - 1) := by
    calc
      a * a + b * b + (N - b - a) * (N - 1) +
            a * (N - 1 - a) + b * (N - 1 - b) =
          (N - b - a) * (N - 1) +
            a * (a + (N - 1 - a)) + b * (b + (N - 1 - b)) := by ring
      _ = (N - b - a) * (N - 1) + a * (N - 1) + b * (N - 1) := by
        rw [show a + (N - 1 - a) = N - 1 by omega,
          show b + (N - 1 - b) = N - 1 by omega]
      _ = (N - b - a + b + a) * (N - 1) := by ring
      _ = N * (N - 1) := by rw [hsubab]
  nlinarith

lemma woodallBound_succ_succ {n k : ℕ} (hk : k < n) :
    woodallBound (n + 1) (k + 1) = woodallBound n k + k + 2 := by
  unfold woodallBound
  have hsub : n + 1 - (k + 1) - 1 = n - k - 1 := by omega
  rw [hsub, show k + 1 + 2 = (k + 2) + 1 by omega, choose_two_succ]
  omega

lemma woodallBound_delete_step {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    woodallBound n k - (k + 1) = woodallBound (n - 1) (k - 1) := by
  unfold woodallBound
  have h₁ : n - 1 - (k - 1) - 1 = n - k - 1 := by omega
  have h₂ : k + 2 = (k + 1) + 1 := by omega
  have h₃ : k - 1 + 2 = k + 1 := by omega
  rw [h₁, h₂, h₃, choose_two_succ]
  omega

/-- The edge threshold is attained by two cliques sharing one cut vertex;
this numerical identity is the arithmetic part of sharpness. -/
lemma sharp_order_identity {n k : ℕ} (hn : 2 * k + 3 ≤ n) :
    (n - k - 1) + (k + 2) - 1 = n := by
  omega

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices whose degree is at most `j`. -/
def lowDegreeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.degree v ≤ j

@[simp] lemma mem_lowDegreeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {j : ℕ} {v : V} : v ∈ lowDegreeFinset G j ↔ G.degree v ≤ j := by
  simp [lowDegreeFinset]

/-- Edges having at least one endpoint in `S`. -/
def incidentToFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion (fun v ↦ G.incidenceFinset v)

lemma card_incidentToFinset_le_sum_degree (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    (incidentToFinset G S).card ≤ ∑ v ∈ S, G.degree v := by
  unfold incidentToFinset
  calc
    (S.biUnion (fun v ↦ G.incidenceFinset v)).card ≤
        ∑ v ∈ S, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ S, G.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      exact G.card_incidenceFinset_eq_degree v

lemma edgeFinset_subset_internal_union_incident (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset ⊆
      {e ∈ G.edgeFinset | e.toFinset ⊆ Sᶜ} ∪ incidentToFinset G S := by
  intro e he
  by_cases houtside : e.toFinset ⊆ Sᶜ
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, houtside⟩)
  · apply Finset.mem_union_right
    rw [Finset.not_subset] at houtside
    obtain ⟨v, hve, hvS⟩ := houtside
    have hv : v ∈ S := by simpa using hvS
    have hve' : v ∈ e := by simpa using hve
    rw [incidentToFinset, Finset.mem_biUnion]
    exact ⟨v, hv, by
      simpa [SimpleGraph.mem_incidenceFinset] using
        ⟨(SimpleGraph.mem_edgeFinset.mp he), hve'⟩⟩

/-- The elementary bound
`e(G) ≤ choose (|V|-|S|) 2 + ∑_{v∈S} degree(v)`.
Internal edges of `S` may be counted twice on the right. -/
lemma card_edgeFinset_le_choose_compl_add_sum_degree (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card ≤ (Fintype.card V - S.card).choose 2 + ∑ v ∈ S, G.degree v := by
  have hsub := edgeFinset_subset_internal_union_incident G S
  have hinternal :
      {e ∈ G.edgeFinset | e.toFinset ⊆ Sᶜ}.card ≤
        (Fintype.card V - S.card).choose 2 := by
    rw [G.card_filter_edgeFinset_toFinset_subset Sᶜ]
    calc
      (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card ≤
          (Fintype.card {x // x ∈ Sᶜ}).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = (Fintype.card V - S.card).choose 2 := by
        rw [Fintype.card_coe, Finset.card_compl]
  calc
    G.edgeFinset.card ≤
        ({e ∈ G.edgeFinset | e.toFinset ⊆ Sᶜ} ∪ incidentToFinset G S).card :=
      Finset.card_le_card hsub
    _ ≤ {e ∈ G.edgeFinset | e.toFinset ⊆ Sᶜ}.card +
          (incidentToFinset G S).card := Finset.card_union_le _ _
    _ ≤ (Fintype.card V - S.card).choose 2 + ∑ v ∈ S, G.degree v :=
      Nat.add_le_add hinternal (card_incidentToFinset_le_sum_degree G S)

/-- Lemma 2.2 of the writeup: a set of `s` vertices of degree at most `j`
forces `e(G) ≤ choose (n-s) 2 + s*j`. -/
lemma low_degree_set_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (j : ℕ) (hdeg : ∀ v ∈ S, G.degree v ≤ j) :
    G.edgeFinset.card ≤ (Fintype.card V - S.card).choose 2 + S.card * j := by
  refine (card_edgeFinset_le_choose_compl_add_sum_degree G S).trans ?_
  gcongr
  calc
    ∑ v ∈ S, G.degree v ≤ ∑ _v ∈ S, j :=
      Finset.sum_le_sum fun v hv ↦ hdeg v hv
    _ = S.card * j := by simp

open Function.Embedding in
lemma card_filter_edgeFinset_eq_card_induce_local (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    {e ∈ G.edgeFinset | ∀ v ∈ e, v ∈ S}.card =
      (G.induce S).edgeFinset.card := by
  rw [← Finset.card_map (sym2Map (Function.Embedding.subtype _))]
  congr
  ext e
  cases e using Sym2.inductionOn with
  | _ a b =>
    suffices G.Adj a b ∧ a ∈ S ∧ b ∈ S ↔
        ∃ a' ∈ S, ∃ b', G.Adj a' b' ∧ b' ∈ S ∧
          (a' = a ∧ b' = b ∨ a' = b ∧ b' = a) by
      simpa [Sym2.exists, Function.Embedding.subtype_apply] using this
    simp only [and_or_left, exists_or, ↓existsAndEq]
    tauto

/-- Exact decomposition of the edge set into the edges inside a finite
set, the crossing edges, and the edges inside its complement. -/
lemma card_edgeFinset_decomp_finset (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card = (G.induce S).edgeFinset.card +
      {e ∈ S ×ˢ Sᶜ | G.Adj e.1 e.2}.card +
      (G.induce (Sᶜ : Finset V)).edgeFinset.card := by
  rw [← Finset.card_filter_add_card_filter_not (∀ v ∈ ·, v ∈ S)]
  nth_rw 2 [← Finset.card_filter_add_card_filter_not (∀ v ∈ ·, v ∈ Sᶜ),
    Nat.add_comm]
  rw [← Nat.add_assoc]
  congr!
  · exact card_filter_edgeFinset_eq_card_induce_local G _
  · let f (e : V × V) := s(e.1, e.2)
    have hf : Set.InjOn f ({e ∈ S ×ˢ Sᶜ | G.Adj e.1 e.2} : Finset _) := by
      rintro ⟨v₁, v₂⟩ hv ⟨w₁, w₂⟩ hw h
      grind [Finset.mem_compl]
    rw [← Finset.card_image_of_injOn hf]
    congr
    ext e
    cases e using Sym2.inductionOn with
    | _ a b =>
      simp_rw [Finset.mem_image, Finset.mem_filter, f, Prod.exists,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      suffices (G.Adj a b ∧ (a ∈ S → b ∉ S)) ∧ (a ∉ S → b ∈ S) ↔
          (a ∈ S ∧ b ∉ S) ∧ G.Adj a b ∨
            (b ∈ S ∧ a ∉ S) ∧ G.Adj b a by
        simpa [and_or_left, exists_or]
      tauto
  · rw [Finset.filter_filter]
    rw [← card_filter_edgeFinset_eq_card_induce_local G]
    congr! with e
    cases e using Sym2.inductionOn with
    | _ a b => simp_all

/-- If every edge leaving `S` ends at one exceptional vertex `c`,
then all edges lie in the two complete-graph envelopes on `S ∪ {c}`
and on `Sᶜ`. -/
lemma card_edgeFinset_le_of_cut_side (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (c : V) (hc : c ∉ S)
    (hclosed : ∀ u ∈ S, G.neighborSet u ⊆ (↑(insert c S) : Set V)) :
    G.edgeFinset.card ≤ (S.card + 1).choose 2 +
      (Fintype.card V - S.card).choose 2 := by
  let X : Finset (V × V) := {e ∈ S ×ˢ Sᶜ | G.Adj e.1 e.2}
  have hXsub : X ⊆ S ×ˢ {c} := by
    rintro ⟨u, v⟩ huv
    simp only [X, Finset.mem_filter, Finset.mem_product,
      Finset.mem_compl] at huv
    have hv := hclosed u huv.1.1 huv.2
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe] at hv
    have hvc : v = c := hv.resolve_right fun h ↦ huv.1.2 h
    subst v
    simp [huv.1.1]
  have hXcard : X.card ≤ S.card := by
    calc
      X.card ≤ (S ×ˢ {c}).card := Finset.card_le_card hXsub
      _ = S.card := by simp
  have hinsideS : (G.induce S).edgeFinset.card ≤ S.card.choose 2 := by
    simpa using SimpleGraph.card_edgeFinset_le_card_choose_two
      (G := G.induce (↑S : Set V))
  have hinsideC : (G.induce (Sᶜ : Finset V)).edgeFinset.card ≤
      (Fintype.card V - S.card).choose 2 := by
    calc
      (G.induce (Sᶜ : Finset V)).edgeFinset.card ≤
          (Fintype.card {v // v ∈ Sᶜ}).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = (Fintype.card V - S.card).choose 2 := by
        rw [Fintype.card_coe, Finset.card_compl]
  rw [card_edgeFinset_decomp_finset G S]
  change (G.induce S).edgeFinset.card + X.card +
      (G.induce (Sᶜ : Finset V)).edgeFinset.card ≤ _
  rw [show S.card + 1 = S.card + 1 by rfl, choose_two_succ]
  omega

/-- The two complete-graph envelopes of a one-vertex separation have
at most Woodall's extremal number of edges when both sides have at
least `k+1` vertices. -/
lemma cut_partition_numerics {n k a : ℕ}
    (hn : 2 * k + 3 ≤ n) (ha : k + 1 ≤ a)
    (hb : k + 1 ≤ n - a - 1) :
    (a + 1).choose 2 + (n - a).choose 2 ≤ woodallBound n k := by
  have hxlo : k + 2 ≤ a + 1 := by omega
  have hxhi : a + 1 ≤ n + 1 - (k + 2) := by omega
  have hprod := concave_product_ge (n := n + 1) hxlo hxhi
  have hcompq : n + 1 - (k + 2) = n - k - 1 := by omega
  have hcompx : n + 1 - (a + 1) = n - a := by omega
  rw [hcompq, hcompx] at hprod
  have hsumx : (a + 1) + (n - a) = n + 1 := by omega
  have hsumq : (k + 2) + (n - k - 1) = n + 1 := by omega
  have hxpred : a + 1 - 1 = a := by omega
  have hypred : n - a - 1 = n - a - 1 := rfl
  have hqpred : k + 2 - 1 = k + 1 := by omega
  have hzpred : n - k - 1 - 1 = n - k - 2 := by omega
  have hypred' : n - a - 1 + 1 = n - a := by omega
  have hzpred' : n - k - 2 + 1 = n - k - 1 := by omega
  have htwo :
      2 * ((a + 1).choose 2 + (n - a).choose 2) ≤
        2 * woodallBound n k := by
    unfold woodallBound
    rw [Nat.mul_add, Nat.mul_add, two_mul_choose_two,
      two_mul_choose_two, two_mul_choose_two, two_mul_choose_two]
    rw [hxpred, hqpred, hzpred]
    nlinarith
  omega

/-- Every component side of `G-c` has at least the minimum degree many
vertices: all neighbours of a side vertex stay on that side or are `c`. -/
lemma component_side_card_ge_minDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] (q : ℕ) (hmin : ∀ z, q ≤ G.degree z)
    (c : V) (K : (Erdos916.deleteVertex G c).ConnectedComponent) :
    q ≤ (Erdos916.ComponentEndBlock.side c K).toFinset.card := by
  classical
  let S : Set V := Erdos916.ComponentEndBlock.side c K
  let W : Set V := Erdos916.ComponentEndBlock.verts c K
  obtain ⟨v, hv⟩ := Erdos916.ComponentEndBlock.side_nonempty (G := G) c K
  let z : W := ⟨v, Set.mem_insert_iff.mpr (Or.inr hv)⟩
  have hdeg : (G.induce W).degree z = G.degree v := by
    simpa [W, z] using
      Erdos916.ComponentEndBlock.degree_induce_verts (G := G) K hv
  have hlt := (G.induce W).degree_lt_card_verts z
  have hcnot : c ∉ S := by
    simpa [S] using Erdos916.ComponentEndBlock.cut_not_mem_side (G := G) c K
  have hcardW : Fintype.card W = S.toFinset.card + 1 := by
    calc
      Fintype.card W = Fintype.card S + 1 := by
        simpa [W, S, Erdos916.ComponentEndBlock.verts] using
          Set.card_insert S hcnot
      _ = S.toFinset.card + 1 := by rw [Set.toFinset_card]
  have := hmin v
  rw [hdeg, hcardW] at hlt
  simpa [S] using (show q ≤ S.toFinset.card by omega)

/-- The strict Woodall threshold together with minimum degree `k+1`
forces vertex two-connectivity. -/
def VertexTwoConnected (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ c : V, (G.induce {v : V | v ≠ c}).Connected

theorem vertexTwoConnected_of_woodallBound_of_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (horder : 2 * k + 3 ≤ Fintype.card V)
    (hmin : ∀ z, k + 1 ≤ G.degree z)
    (hedge : woodallBound (Fintype.card V) k + 1 ≤
      G.edgeFinset.card) :
    VertexTwoConnected G := by
  classical
  have hdelPre (c : V) :
      (G.induce {v : V | v ≠ c}).Preconnected := by
    let H : SimpleGraph {v : V // v ≠ c} := Erdos916.deleteVertex G c
    by_contra hpre
    have hpreH : ¬H.Preconnected := by simpa [H, Erdos916.deleteVertex] using hpre
    simp only [SimpleGraph.Preconnected] at hpreH
    push Not at hpreH
    obtain ⟨u, v, huv⟩ := hpreH
    let K : H.ConnectedComponent := H.connectedComponentMk u
    let L : H.ConnectedComponent := H.connectedComponentMk v
    have hKL : K ≠ L := by
      intro h
      exact huv (SimpleGraph.ConnectedComponent.exact h)
    let Sset : Set V := Erdos916.ComponentEndBlock.side c K
    let Tset : Set V := Erdos916.ComponentEndBlock.side c L
    let S : Finset V := Sset.toFinset
    let T : Finset V := Tset.toFinset
    have hScard : k + 1 ≤ S.card := by
      simpa [H, K, S, Sset, Erdos916.deleteVertex] using
        component_side_card_ge_minDegree G (k + 1) hmin c K
    have hTcard : k + 1 ≤ T.card := by
      simpa [H, L, T, Tset, Erdos916.deleteVertex] using
        component_side_card_ge_minDegree G (k + 1) hmin c L
    have hdisj : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxT
      have hxS' : x ∈ Erdos916.ComponentEndBlock.side c K := by
        simpa [S, Sset] using hxS
      have hxT' : x ∈ Erdos916.ComponentEndBlock.side c L := by
        simpa [T, Tset] using hxT
      obtain ⟨hxc, hxK⟩ := hxS'
      obtain ⟨_, hxL⟩ := hxT'
      apply hKL
      exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hxK hxL
    have hcS : c ∉ S := by
      simpa [S, Sset] using
        Erdos916.ComponentEndBlock.cut_not_mem_side (G := G) c K
    have hcT : c ∉ T := by
      simpa [T, Tset] using
        Erdos916.ComponentEndBlock.cut_not_mem_side (G := G) c L
    have hsum : S.card + T.card + 1 ≤ Fintype.card V := by
      have hcST : c ∉ S ∪ T := by simp [hcS, hcT]
      have hle := Finset.card_le_card
        (Finset.subset_univ (insert c (S ∪ T)))
      rw [Finset.card_insert_of_notMem hcST,
        Finset.card_union_of_disjoint hdisj] at hle
      simpa using hle
    have hother : k + 1 ≤ Fintype.card V - S.card - 1 := by omega
    have hclosed : ∀ x ∈ S,
        G.neighborSet x ⊆ (↑(insert c S) : Set V) := by
      intro x hx
      have hx' : x ∈ Erdos916.ComponentEndBlock.side c K := by
        simpa [S, Sset] using hx
      have hs :=
        Erdos916.ComponentEndBlock.neighborSet_subset_verts (G := G) K hx'
      simpa [S, Sset, Erdos916.ComponentEndBlock.verts] using hs
    have hupper := card_edgeFinset_le_of_cut_side G S c hcS hclosed
    have hnum := cut_partition_numerics horder hScard hother
    omega
  have hdelConn (c : V) : (G.induce {v : V | v ≠ c}).Connected := by
    obtain ⟨v, hvc⟩ := Fintype.exists_ne_of_one_lt_card
      (show 1 < Fintype.card V by omega) c
    haveI : Nonempty ↑({v : V | v ≠ c} : Set V) := ⟨⟨v, hvc⟩⟩
    exact ⟨hdelPre c⟩
  have hcard3 : 3 ≤ Fintype.card V := by omega
  have hneV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty V := hneV
  have hconn : G.Connected := by
    refine ⟨?_⟩
    intro u v
    have hcardinal : (3 : Cardinal) ≤ Cardinal.mk V := by
      simpa [Cardinal.mk_fintype] using hcard3
    obtain ⟨c, hcu, hcv⟩ :=
      Cardinal.exists_ne_ne_of_three_le hcardinal u v
    have hr := (hdelConn c).preconnected
      ⟨u, hcu.symm⟩ ⟨v, hcv.symm⟩
    exact hr.map (SimpleGraph.Embedding.induce
      (G := G) (s := {z : V | z ≠ c})).toHom
  exact ⟨hconn, hdelConn⟩

/-- Split a degree sum over two disjoint exceptional sets and their
complement. -/
lemma sum_univ_le_three_parts (f : V → ℕ) (R S : Finset V) (a b c : ℕ)
    (hdisj : Disjoint R S)
    (hR : ∀ x ∈ R, f x ≤ a) (hS : ∀ x ∈ S, f x ≤ b)
    (hall : ∀ x, f x ≤ c) :
    ∑ x, f x ≤ R.card * a + S.card * b +
      (Fintype.card V - R.card - S.card) * c := by
  have hsplit : ∑ x, f x =
      (∑ x ∈ R, f x) + (∑ x ∈ S, f x) +
        ∑ x ∈ (R ∪ S)ᶜ, f x := by
    calc
      ∑ x, f x = ∑ x ∈ (R ∪ S) ∪ (R ∪ S)ᶜ, f x := by
        rw [Finset.union_compl]
      _ = (∑ x ∈ R ∪ S, f x) + ∑ x ∈ (R ∪ S)ᶜ, f x :=
        Finset.sum_union disjoint_compl_right
      _ = (∑ x ∈ R, f x) + (∑ x ∈ S, f x) +
          ∑ x ∈ (R ∪ S)ᶜ, f x := by
        rw [Finset.sum_union hdisj]
  rw [hsplit]
  have hRsum : ∑ x ∈ R, f x ≤ R.card * a := by
    calc
      ∑ x ∈ R, f x ≤ ∑ _x ∈ R, a :=
        Finset.sum_le_sum fun x hx ↦ hR x hx
      _ = R.card * a := by simp
  have hSsum : ∑ x ∈ S, f x ≤ S.card * b := by
    calc
      ∑ x ∈ S, f x ≤ ∑ _x ∈ S, b :=
        Finset.sum_le_sum fun x hx ↦ hS x hx
      _ = S.card * b := by simp
  have hCsum : ∑ x ∈ (R ∪ S)ᶜ, f x ≤
      (Fintype.card V - R.card - S.card) * c := by
    calc
      ∑ x ∈ (R ∪ S)ᶜ, f x ≤ ∑ _x ∈ (R ∪ S)ᶜ, c :=
        Finset.sum_le_sum fun x _hx ↦ hall x
      _ = ((R ∪ S)ᶜ).card * c := by simp
      _ = (Fintype.card V - R.card - S.card) * c := by
        rw [Finset.card_compl, Finset.card_union_of_disjoint hdisj]
        congr 1
        omega
  omega

end Counting

section HamiltonPathCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b}

/-- Along a Hamilton path, every neighbor of the final vertex occurs before
the final position. -/
def pathNeighborIndexBeforeEnd (hpp : p.IsPath)
    (hall : ∀ x : G.neighborFinset b, x.1 ∈ p.support) :
    G.neighborFinset b ↪ Fin p.length where
  toFun x := by
    have hmem : x.1 ∈ p.support := hall x
    have hget : p.getVert (p.support.idxOf x.1) = x.1 :=
      p.getVert_support_idxOf hmem
    have hle : p.support.idxOf x.1 ≤ p.length := by
      have hi := List.idxOf_lt_length_of_mem hmem
      rw [p.length_support] at hi
      omega
    have hne : p.support.idxOf x.1 ≠ p.length := by
      intro hi
      have hxb : x.1 = b := by simpa [hi] using hget.symm
      have hadj : G.Adj b x.1 :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
      exact hadj.ne hxb.symm
    exact ⟨p.support.idxOf x.1, lt_of_le_of_ne hle hne⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    have hmemx : x.1 ∈ p.support := hall x
    have hmemy : y.1 ∈ p.support := hall y
    rw [← p.getVert_support_idxOf hmemx, ← p.getVert_support_idxOf hmemy]
    exact congrArg p.getVert (congrArg Fin.val hxy)

/-- Along a Hamilton path, every neighbor of the initial vertex occurs after
the initial position; subtracting one gives the preceding edge slot. -/
def pathNeighborIndexAfterStart (hpp : p.IsPath)
    (hall : ∀ x : G.neighborFinset a, x.1 ∈ p.support) :
    G.neighborFinset a ↪ Fin p.length where
  toFun x := by
    have hmem : x.1 ∈ p.support := hall x
    have hget : p.getVert (p.support.idxOf x.1) = x.1 :=
      p.getVert_support_idxOf hmem
    have hle : p.support.idxOf x.1 ≤ p.length := by
      have hi := List.idxOf_lt_length_of_mem hmem
      rw [p.length_support] at hi
      omega
    have hpos : 0 < p.support.idxOf x.1 := by
      by_contra hi
      have hxa : x.1 = a := by
        have hi0 : p.support.idxOf x.1 = 0 := by omega
        simpa [hi0] using hget.symm
      have hadj : G.Adj a x.1 :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := a) x.1).mp x.2
      exact hadj.ne hxa.symm
    exact ⟨p.support.idxOf x.1 - 1, by omega⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    have hmemx : x.1 ∈ p.support := hall x
    have hmemy : y.1 ∈ p.support := hall y
    have hxget : p.getVert (p.support.idxOf x.1) = x.1 :=
      p.getVert_support_idxOf hmemx
    have hyget : p.getVert (p.support.idxOf y.1) = y.1 :=
      p.getVert_support_idxOf hmemy
    have hxpos : 0 < p.support.idxOf x.1 := by
      by_contra h
      have hxa : x.1 = a := by
        have h0 : p.support.idxOf x.1 = 0 := by omega
        simpa [h0] using hxget.symm
      have hadj : G.Adj a x.1 :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := a) x.1).mp x.2
      exact hadj.ne hxa.symm
    have hypos : 0 < p.support.idxOf y.1 := by
      by_contra h
      have hya : y.1 = a := by
        have h0 : p.support.idxOf y.1 = 0 := by omega
        simpa [h0] using hyget.symm
      have hadj : G.Adj a y.1 :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := a) y.1).mp y.2
      exact hadj.ne hya.symm
    have hidx : p.support.idxOf x.1 = p.support.idxOf y.1 := by
      have := congrArg Fin.val hxy
      change p.support.idxOf x.1 - 1 = p.support.idxOf y.1 - 1 at this
      omega
    rw [← hxget, ← hyget, hidx]

@[simp] lemma getVert_pathNeighborIndexBeforeEnd (hpp : p.IsPath)
    (hall : ∀ x : G.neighborFinset b, x.1 ∈ p.support)
    (x : G.neighborFinset b) :
    p.getVert (pathNeighborIndexBeforeEnd hpp hall x).val = x.1 := by
  change p.getVert (p.support.idxOf x.1) = x.1
  exact p.getVert_support_idxOf (hall x)

@[simp] lemma getVert_succ_pathNeighborIndexAfterStart (hpp : p.IsPath)
    (hall : ∀ x : G.neighborFinset a, x.1 ∈ p.support)
    (x : G.neighborFinset a) :
    p.getVert ((pathNeighborIndexAfterStart hpp hall x).val + 1) = x.1 := by
  have hmem : x.1 ∈ p.support := hall x
  have hget : p.getVert (p.support.idxOf x.1) = x.1 :=
    p.getVert_support_idxOf hmem
  have hpos : 0 < p.support.idxOf x.1 := by
    by_contra h
    have h0 : p.support.idxOf x.1 = 0 := by omega
    have hxa : x.1 = a := by simpa [h0] using hget.symm
    have hadj : G.Adj a x.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := a) x.1).mp x.2
    exact hadj.ne hxa.symm
  change p.getVert (p.support.idxOf x.1 - 1 + 1) = x.1
  rw [show p.support.idxOf x.1 - 1 + 1 = p.support.idxOf x.1 by omega]
  exact hget

/-- A Hamilton path whose endpoints are adjacent closes to a Hamilton cycle
as soon as the ambient graph has at least three vertices. -/
lemma isHamiltonian_of_hamiltonianPath_of_adj (hn : 3 ≤ Fintype.card V)
    (hp : p.IsHamiltonian) (hba : G.Adj b a) : G.IsHamiltonian := by
  let c : G.Walk b b := Walk.cons hba p
  have hedge : s(b, a) ∉ p.edges := by
    intro hedge
    have hedge' : s(a, b) ∈ p.edges := by simpa [Sym2.eq_swap] using hedge
    have hone := hp.isPath.length_eq_one_of_mem_edges hedge'
    rw [hp.length_eq] at hone
    omega
  have hc : c.IsCycle := by
    exact SimpleGraph.Path.cons_isCycle ⟨p, hp.isPath⟩ hba hedge
  intro _
  refine ⟨b, c, ⟨hc, ?_⟩⟩
  intro v
  simpa [c, Walk.IsHamiltonian] using hp v

/-- Ore's endpoint lemma in path form.  The proof is the usual shifted
neighbor-set pigeonhole argument, with the resulting reordering realized by
the Pósa rotation already developed for Erdős Problem 746. -/
lemma isHamiltonian_of_hamiltonianPath_degree_sum
    (hn : 3 ≤ Fintype.card V) (hp : p.IsHamiltonian)
    (hsum : Fintype.card V ≤ G.degree a + G.degree b) : G.IsHamiltonian := by
  by_cases hba : G.Adj b a
  · exact isHamiltonian_of_hamiltonianPath_of_adj hn hp hba
  have hallEnd : ∀ x : G.neighborFinset b, x.1 ∈ p.support :=
    fun x ↦ hp.mem_support x.1
  have hallStart : ∀ x : G.neighborFinset a, x.1 ∈ p.support :=
    fun x ↦ hp.mem_support x.1
  let A : Finset (Fin p.length) :=
    Finset.univ.map (pathNeighborIndexBeforeEnd hp.isPath hallEnd)
  let B : Finset (Fin p.length) :=
    Finset.univ.map (pathNeighborIndexAfterStart hp.isPath hallStart)
  have hcardA : A.card = G.degree b := by
    simp [A, SimpleGraph.card_neighborFinset_eq_degree]
  have hcardB : B.card = G.degree a := by
    simp [B, SimpleGraph.card_neighborFinset_eq_degree]
  have hnondisj : ¬Disjoint A B := by
    intro hdisj
    have hunion : (A ∪ B).card ≤ p.length := by
      simpa using (Finset.card_le_univ (A ∪ B))
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB] at hunion
    have hlen := hp.length_eq
    omega
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp hnondisj
  obtain ⟨x, _hx, hxi⟩ := Finset.mem_map.mp hiA
  obtain ⟨y, _hy, hyi⟩ := Finset.mem_map.mp hiB
  have hbx : G.Adj b (p.getVert i.val) := by
    have hadj : G.Adj b x.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
    have hget := getVert_pathNeighborIndexBeforeEnd hp.isPath hallEnd x
    rw [hxi] at hget
    simpa [hget] using hadj
  have hay : G.Adj a (p.getVert (i.val + 1)) := by
    have hadj : G.Adj a y.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := a) y.1).mp y.2
    have hget := getVert_succ_pathNeighborIndexAfterStart hp.isPath hallStart y
    rw [hyi] at hget
    simpa [hget] using hadj
  let z : V := p.getVert i.val
  have hzmem : z ∈ p.support := p.getVert_mem_support i.val
  have hza : z ≠ a := by
    intro hza
    apply hba
    simpa [z, hza] using hbx
  have hzb : z ≠ b := by
    intro hzb
    have hinj := hp.isPath.getVert_injOn
    have heq : i.val = p.length := by
      apply hinj
      · simp
      · simp
      · simpa [z, hzb]
    omega
  have hidx : p.support.idxOf z = i.val := by
    have hz : z = x.1 := by
      have hget := getVert_pathNeighborIndexBeforeEnd hp.isPath hallEnd x
      rw [hxi] at hget
      exact hget
    rw [hz]
    exact congrArg Fin.val hxi
  have hsnd : (p.dropUntil z hzmem).snd = p.getVert (i.val + 1) := by
    rw [p.dropUntil_eq_drop hzmem]
    simp [hidx, Walk.drop_getVert]
  let q : G.Walk a (p.dropUntil z hzmem).snd :=
    p.posaRotate z hzmem hza hzb hbx
  have hqp : q.IsPath := p.isPath_posaRotate hp.isPath z hzmem hza hzb hbx
  have hqham : q.IsHamiltonian := by
    apply hqp.isHamiltonian_of_mem
    intro v
    have hv := hp.mem_support v
    exact (p.support_posaRotate_perm z hzmem hza hzb hbx).mem_iff.mpr hv
  have hqa : G.Adj (p.dropUntil z hzmem).snd a := by
    rw [hsnd]
    exact hay.symm
  exact isHamiltonian_of_hamiltonianPath_of_adj hn hqham hqa

end HamiltonPathCounting

section PosaCriterion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Successor positions of a simple path are distinct. -/
def pathSuccessorEmbedding {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    Fin p.length ↪ V where
  toFun i := p.getVert (i.val + 1)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hidx : i.val + 1 = j.val + 1 := hp.getVert_injOn
      (by simp) (by simp) hij
    omega

/-- The vertices in the first `p.length` positions of a simple path are
pairwise distinct.  Composing this embedding with
`pathNeighborIndexAfterStart` gives the predecessors of the neighbors of
the first endpoint. -/
def pathPredecessorEmbedding {a b : V} {p : G.Walk a b} (hp : p.IsPath) :
    Fin p.length ↪ V where
  toFun i := p.getVert i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by simp) (by simp) hij

lemma longestPath_neighbor_mem_support_end {a b : V} {p : G.Walk a b}
    (hp : IsLongestPath p) {x : V} (hbx : G.Adj b x) : x ∈ p.support := by
  by_contra hx
  have hpath : (p.concat hbx).IsPath := hp.isPath.concat hx hbx
  have hle := (isLongestPath_iff.mp hp).2 a x (p.concat hbx) hpath
  simp at hle

lemma longestPath_neighbor_mem_support_start {a b : V} {p : G.Walk a b}
    (hp : IsLongestPath p) {x : V} (hax : G.Adj a x) : x ∈ p.support := by
  by_contra hx
  have hpath : (Walk.cons hax.symm p).IsPath := hp.isPath.cons hx
  have hle := (isLongestPath_iff.mp hp).2 x b (Walk.cons hax.symm p) hpath
  simp at hle

/-- In a connected non-Hamiltonian graph, the endpoint degree sum of a
longest path is at most the path length. -/
lemma degree_add_degree_le_length_of_longestPath
    {a b : V} {p : G.Walk a b} (hp : IsLongestPath p)
    (hlen : 2 ≤ p.length) (hconn : G.Connected) (hnham : ¬G.IsHamiltonian) :
    G.degree a + G.degree b ≤ p.length := by
  have hallEnd : ∀ x : G.neighborFinset b, x.1 ∈ p.support := by
    intro x
    exact longestPath_neighbor_mem_support_end hp
      ((SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2)
  have hallStart : ∀ x : G.neighborFinset a, x.1 ∈ p.support := by
    intro x
    exact longestPath_neighbor_mem_support_start hp
      ((SimpleGraph.mem_neighborFinset (G := G) (v := a) x.1).mp x.2)
  let A : Finset (Fin p.length) :=
    Finset.univ.map (pathNeighborIndexBeforeEnd hp.isPath hallEnd)
  let B : Finset (Fin p.length) :=
    Finset.univ.map (pathNeighborIndexAfterStart hp.isPath hallStart)
  have hcardA : A.card = G.degree b := by
    simp [A, SimpleGraph.card_neighborFinset_eq_degree]
  have hcardB : B.card = G.degree a := by
    simp [B, SimpleGraph.card_neighborFinset_eq_degree]
  by_contra hsum
  have hnondisj : ¬Disjoint A B := by
    intro hdisj
    have hunion : (A ∪ B).card ≤ p.length := by
      simpa using (Finset.card_le_univ (A ∪ B))
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB] at hunion
    omega
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp hnondisj
  obtain ⟨x, _hx, hxi⟩ := Finset.mem_map.mp hiA
  obtain ⟨y, _hy, hyi⟩ := Finset.mem_map.mp hiB
  have hbx : G.Adj b (p.getVert i.val) := by
    have hadj : G.Adj b x.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
    have hget := getVert_pathNeighborIndexBeforeEnd hp.isPath hallEnd x
    rw [hxi] at hget
    simpa [hget] using hadj
  have hay : G.Adj a (p.getVert (i.val + 1)) := by
    have hadj : G.Adj a y.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := a) y.1).mp y.2
    have hget := getVert_succ_pathNeighborIndexAfterStart hp.isPath hallStart y
    rw [hyi] at hget
    simpa [hget] using hadj
  let z : V := p.getVert i.val
  have hzmem : z ∈ p.support := p.getVert_mem_support i.val
  have hza : z ≠ a := by
    intro hza
    have hba : G.Adj b a := by simpa [z, hza] using hbx
    exact (SimpleGraph.Walk.not_adj_end_start_of_longest_path hp.isPath hlen
      (isLongestPath_iff.mp hp).2 hconn hnham) hba
  have hzb : z ≠ b := by
    intro hzb
    have heq : i.val = p.length := hp.isPath.getVert_injOn
      (by simp) (by simp) (by simpa [z, hzb])
    omega
  have hidx : p.support.idxOf z = i.val := by
    have hz : z = x.1 := by
      have hget := getVert_pathNeighborIndexBeforeEnd hp.isPath hallEnd x
      rw [hxi] at hget
      exact hget
    rw [hz]
    exact congrArg Fin.val hxi
  have hsnd : (p.dropUntil z hzmem).snd = p.getVert (i.val + 1) := by
    rw [p.dropUntil_eq_drop hzmem]
    simp [hidx, Walk.drop_getVert]
  let q : G.Walk a (p.dropUntil z hzmem).snd :=
    p.posaRotate z hzmem hza hzb hbx
  have hqp : q.IsPath := p.isPath_posaRotate hp.isPath z hzmem hza hzb hbx
  have hqlen : q.length = p.length := p.length_posaRotate z hzmem hza hzb hbx
  have hmaxq : ∀ (u v : V) (r : G.Walk u v), r.IsPath → r.length ≤ q.length := by
    intro u v r hr
    rw [hqlen]
    exact (isLongestPath_iff.mp hp).2 u v r hr
  have hqa : G.Adj (p.dropUntil z hzmem).snd a := by
    rw [hsnd]
    exact hay.symm
  exact (SimpleGraph.Walk.not_adj_end_start_of_longest_path hqp
    (by rw [hqlen]; exact hlen) hmaxq hconn hnham) hqa

/-- Two crossing endpoint chords close a path after omitting one internal
vertex.  This is the cycle-splicing step in Woodall's endpoint lemma. -/
lemma hasCycleAtLeast_of_path_endpoint_chords
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) (hlen : 3 ≤ p.length)
    {i : ℕ} (hi : i + 2 ≤ p.length)
    (hbi : G.Adj b (p.getVert i))
    (hai : G.Adj a (p.getVert (i + 2))) :
    HasCycleAtLeast G p.length := by
  by_cases hi0 : i = 0
  · have hba : G.Adj b a := by simpa [hi0] using hbi
    let c : G.Walk b b := Walk.cons hba p
    have hedge : s(b, a) ∉ p.edges := by
      intro hedge
      have hedge' : s(a, b) ∈ p.edges := by simpa [Sym2.eq_swap] using hedge
      have := hp.length_eq_one_of_mem_edges hedge'
      omega
    have hc : c.IsCycle := SimpleGraph.Path.cons_isCycle ⟨p, hp⟩ hba hedge
    exact ⟨b, c, hc, by simp [c]⟩
  · let z : V := p.getVert i
    have hzmem : z ∈ p.support := p.getVert_mem_support i
    have hza : z ≠ a := by
      intro hza
      have hzero : p.getVert 0 = a := p.getVert_zero
      have hz_a : p.getVert i = p.getVert 0 := by
        rw [hzero]
        simpa [z] using hza
      have heq : i = 0 := hp.getVert_injOn
        (by change i ≤ p.length; omega)
        (by change 0 ≤ p.length; omega) hz_a
      exact hi0 heq
    have hzb : z ≠ b := by
      intro hzb
      have hend : p.getVert p.length = b := p.getVert_length
      have hz_b : p.getVert i = p.getVert p.length := by
        rw [hend]
        simpa [z] using hzb
      have heq : i = p.length := hp.getVert_injOn
        (by change i ≤ p.length; omega)
        (by change p.length ≤ p.length; exact le_rfl) hz_b
      omega
    have hidx : p.support.idxOf z = i := by
      have hmem := p.getVert_support_idxOf hzmem
      have hgeteq : p.getVert (p.support.idxOf z) = p.getVert i := by
        simpa [z] using hmem
      have heq : p.support.idxOf z = i := hp.getVert_injOn
        (by
          simp only [Set.mem_ofPred_eq]
          have := List.idxOf_lt_length_of_mem hzmem
          rw [p.length_support] at this
          omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hgeteq
      exact heq
    let q : G.Walk a (p.dropUntil z hzmem).snd :=
      p.posaRotate z hzmem hza hzb (by simpa [z] using hbi)
    have hqp : q.IsPath :=
      p.isPath_posaRotate hp z hzmem hza hzb (by simpa [z] using hbi)
    have hqlen : q.length = p.length :=
      p.length_posaRotate z hzmem hza hzb (by simpa [z] using hbi)
    have hqpen : q.penultimate = p.getVert (i + 2) := by
      change q.getVert (q.length - 1) = p.getVert (i + 2)
      rw [hqlen]
      rw [show q = (p.takeUntil z hzmem).append
          (Walk.cons (by simpa [z] using hbi.symm)
            (p.dropUntil z hzmem).tail.reverse) by rfl]
      rw [Walk.getVert_append, if_neg]
      · rw [Walk.length_takeUntil, hidx]
        rw [Walk.getVert_cons _ _ (by omega), Walk.getVert_reverse,
          Walk.getVert_tail]
        rw [p.dropUntil_eq_drop hzmem]
        simp only [Walk.getVert_copy, Walk.drop_getVert, Walk.length_tail]
        simpa [hidx] using congrArg p.getVert
          (show i + ((p.length - i - 1 - (p.length - 1 - i - 1)) + 1) = i + 2 by
            omega)
      · rw [Walk.length_takeUntil, hidx]
        omega
    have hdropPath : q.dropLast.IsPath := hqp.dropLast
    have hclose : G.Adj q.penultimate a := by simpa [hqpen] using hai.symm
    have hedge : s(q.penultimate, a) ∉ q.dropLast.edges := by
      intro hedge
      have hedge' : s(a, q.penultimate) ∈ q.dropLast.edges := by
        simpa [Sym2.eq_swap] using hedge
      have hone := hdropPath.length_eq_one_of_mem_edges hedge'
      rw [Walk.length_dropLast, hqlen] at hone
      omega
    let c : G.Walk q.penultimate q.penultimate := Walk.cons hclose q.dropLast
    have hc : c.IsCycle :=
      SimpleGraph.Path.cons_isCycle ⟨q.dropLast, hdropPath⟩ hclose hedge
    refine ⟨q.penultimate, c, hc, ?_⟩
    simp [c, Walk.length_dropLast, hqlen]
    omega

/-- Adjacent crossing endpoint chords close all of a path. -/
lemma hasCycleAtLeast_succ_of_path_endpoint_chords
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) (hlen : 2 ≤ p.length)
    {i : ℕ} (hi : i + 1 ≤ p.length)
    (hbi : G.Adj b (p.getVert i))
    (hai : G.Adj a (p.getVert (i + 1))) :
    HasCycleAtLeast G (p.length + 1) := by
  by_cases hi0 : i = 0
  · have hba : G.Adj b a := by simpa [hi0] using hbi
    let c : G.Walk b b := Walk.cons hba p
    have hedge : s(b, a) ∉ p.edges := by
      intro hedge
      have hedge' : s(a, b) ∈ p.edges := by simpa [Sym2.eq_swap] using hedge
      have := hp.length_eq_one_of_mem_edges hedge'
      omega
    exact ⟨b, c, SimpleGraph.Path.cons_isCycle ⟨p, hp⟩ hba hedge, by simp [c]⟩
  · let z : V := p.getVert i
    have hzmem : z ∈ p.support := p.getVert_mem_support i
    have hza : z ≠ a := by
      intro hza
      have heq : i = 0 := hp.getVert_injOn
        (by change i ≤ p.length; omega) (by simp)
        (by simpa [z, hza] using p.getVert_zero.symm)
      exact hi0 heq
    have hzb : z ≠ b := by
      intro hzb
      have heq : i = p.length := hp.getVert_injOn
        (by change i ≤ p.length; omega) (by simp)
        (by simpa [z, hzb] using p.getVert_length.symm)
      omega
    have hidx : p.support.idxOf z = i := by
      have hgeteq : p.getVert (p.support.idxOf z) = p.getVert i := by
        simpa [z] using p.getVert_support_idxOf hzmem
      exact hp.getVert_injOn
        (by
          have := List.idxOf_lt_length_of_mem hzmem
          rw [p.length_support] at this
          simp only [Set.mem_ofPred_eq]
          omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hgeteq
    have hsnd : (p.dropUntil z hzmem).snd = p.getVert (i + 1) := by
      rw [p.dropUntil_eq_drop hzmem]
      simp [hidx, Walk.drop_getVert]
    let q : G.Walk a (p.dropUntil z hzmem).snd :=
      p.posaRotate z hzmem hza hzb (by simpa [z] using hbi)
    have hqp : q.IsPath :=
      p.isPath_posaRotate hp z hzmem hza hzb (by simpa [z] using hbi)
    have hqlen : q.length = p.length :=
      p.length_posaRotate z hzmem hza hzb (by simpa [z] using hbi)
    have hqa : G.Adj (p.dropUntil z hzmem).snd a := by
      rw [hsnd]
      exact hai.symm
    let c : G.Walk (p.dropUntil z hzmem).snd (p.dropUntil z hzmem).snd :=
      Walk.cons hqa q
    have hedge : s((p.dropUntil z hzmem).snd, a) ∉ q.edges := by
      intro hedge
      have hedge' : s(a, (p.dropUntil z hzmem).snd) ∈ q.edges := by
        simpa [Sym2.eq_swap] using hedge
      have hone := hqp.length_eq_one_of_mem_edges hedge'
      rw [hqlen] at hone
      omega
    exact ⟨_, c, SimpleGraph.Path.cons_isCycle ⟨q, hqp⟩ hqa hedge, by
      simp [c, hqlen]⟩

/-- Pósa's low-degree distribution hypothesis, written without a parity
split.  The second clause is used only at the middle index. -/
def PosaDegreeCondition (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ j, 2 * j < Fintype.card V - 1 →
      (lowDegreeFinset G j).card ≤ j - 1) ∧
    (∀ j, 2 * j = Fintype.card V - 1 →
      (lowDegreeFinset G j).card ≤ j)

lemma PosaDegreeCondition.not_small_closed
    (hP : PosaDegreeCondition G) (hn : 3 ≤ Fintype.card V)
    (R : Finset V) (hR : R.Nonempty) (hsmall : 2 * R.card ≤ Fintype.card V)
    (hclosed : ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R) : False := by
  let j := R.card - 1
  have hdeg : ∀ x ∈ R, G.degree x ≤ j := by
    intro x hx
    have hsub : G.neighborFinset x ⊆ R.erase x := by
      intro y hy
      have hadj : G.Adj x y :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := x) y).mp hy
      exact Finset.mem_erase.mpr ⟨hadj.ne.symm, hclosed x hx y hadj⟩
    calc
      G.degree x = (G.neighborFinset x).card :=
        (G.card_neighborFinset_eq_degree x).symm
      _ ≤ (R.erase x).card := Finset.card_le_card hsub
      _ = j := by simp [j, hx]
  have hRsub : R ⊆ lowDegreeFinset G j := by
    intro x hx
    exact mem_lowDegreeFinset.mpr (hdeg x hx)
  have hcardlow : R.card ≤ (lowDegreeFinset G j).card :=
    Finset.card_le_card hRsub
  have hjstrict : 2 * j < Fintype.card V - 1 := by
    have hpos : 0 < R.card := Finset.card_pos.mpr hR
    dsimp [j]
    omega
  have := hP.1 j hjstrict
  have hpos : 0 < R.card := Finset.card_pos.mpr hR
  dsimp [j] at this hcardlow
  omega

/-- Pósa's degree-distribution condition forces connectedness. -/
lemma PosaDegreeCondition.connected
    (hP : PosaDegreeCondition G) (hn : 3 ≤ Fintype.card V) : G.Connected := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty V := hne
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  by_contra hconn
  push Not at hconn
  obtain ⟨v, huv⟩ := hconn (Classical.choice hne)
  let u : V := Classical.choice hne
  let S : Finset V := Finset.univ.filter fun x ↦ G.Reachable u x
  let T : Finset V := Finset.univ.filter fun x ↦ G.Reachable v x
  have huS : u ∈ S := by simp [S]
  have hvT : v ∈ T := by simp [T]
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hux : G.Reachable u x := by simpa [S] using hxS
    have hvx : G.Reachable v x := by simpa [T] using hxT
    exact huv (hux.trans hvx.symm)
  have hsum : S.card + T.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  have hSclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
    intro x hx y hxy
    have hux : G.Reachable u x := by simpa [S] using hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hux.trans hxy.reachable
  have hTclosed : ∀ x ∈ T, ∀ y, G.Adj x y → y ∈ T := by
    intro x hx y hxy
    have hvx : G.Reachable v x := by simpa [T] using hx
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvx.trans hxy.reachable
  by_cases hST : S.card ≤ T.card
  · exact hP.not_small_closed hn S ⟨u, huS⟩ (by omega) hSclosed
  · exact hP.not_small_closed hn T ⟨v, hvT⟩ (by omega) hTclosed

/-- Endpoint pairs of longest paths. -/
noncomputable def longestEndpointPairs (G : SimpleGraph V) : Finset (V × V) :=
  Finset.univ.filter fun ab ↦
    ∃ p : G.Walk ab.1 ab.2, IsLongestPath p

@[simp] lemma mem_longestEndpointPairs {ab : V × V} :
    ab ∈ longestEndpointPairs G ↔
      ∃ p : G.Walk ab.1 ab.2, IsLongestPath p := by
  simp [longestEndpointPairs]

lemma longestEndpointPairs_nonempty (hne : Nonempty V) :
    (longestEndpointPairs G).Nonempty := by
  letI : Nonempty V := hne
  obtain ⟨a, b, p, hp⟩ := exists_isLongestPath G
  exact ⟨(a, b), mem_longestEndpointPairs.mpr ⟨p, hp⟩⟩

/-- A Pósa rotation turns each successor of a neighbor of the final
endpoint into the final endpoint of another longest path.  Consequently
maximality of the endpoint degree sum bounds all those successor degrees. -/
lemma degree_pathSuccessor_le_of_maximal_longestPath
    {a b : V} {p : G.Walk a b} (hp : IsLongestPath p)
    (hmax : ∀ {u v : V} {q : G.Walk u v}, IsLongestPath q →
      G.degree u + G.degree v ≤ G.degree a + G.degree b)
    (x : G.neighborFinset b) :
    G.degree
        (pathSuccessorEmbedding hp.isPath
          (pathNeighborIndexBeforeEnd hp.isPath (fun y ↦
            longestPath_neighbor_mem_support_end hp
              ((SimpleGraph.mem_neighborFinset (G := G) (v := b) y.1).mp y.2)) x)) ≤
      G.degree b := by
  let hall : ∀ y : G.neighborFinset b, y.1 ∈ p.support := fun y ↦
    longestPath_neighbor_mem_support_end hp
      ((SimpleGraph.mem_neighborFinset (G := G) (v := b) y.1).mp y.2)
  have hbx : G.Adj b x.1 :=
    (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
  have hxmem : x.1 ∈ p.support := hall x
  by_cases hxa : x.1 = a
  · have hclose : G.Adj b a := by simpa [hxa] using hbx
    have hpnon : ¬p.Nil := Walk.not_nil_of_ne hclose.ne.symm
    have haTail : a ∉ p.tail.support := by
      have hn := hp.isPath.support_nodup
      rw [← p.cons_support_tail hpnon, List.nodup_cons] at hn
      exact hn.1
    let q : G.Walk p.snd a := p.tail.concat hclose
    have hqp : q.IsPath := hp.isPath.tail.concat haTail hclose
    have hqlen : q.length = p.length := by
      dsimp [q]
      rw [Walk.length_concat]
      exact p.length_tail_add_one hpnon
    have hqmax : IsLongestPath q := ⟨hqp, hqlen.trans hp.length_eq⟩
    have hqdeg := hmax hqmax
    have hsuc :
        pathSuccessorEmbedding hp.isPath
            (pathNeighborIndexBeforeEnd hp.isPath hall x) = p.snd := by
      change p.getVert (p.support.idxOf x.1 + 1) = p.getVert 1
      have haidx : p.support.idxOf a = 0 := by
        rw [← p.cons_support_tail hpnon]
        simp
      simp [hxa, haidx]
    rw [hsuc]
    omega
  have hxb : x.1 ≠ b := hbx.ne.symm
  have hsnd : (p.dropUntil x.1 hxmem).snd =
      pathSuccessorEmbedding hp.isPath
        (pathNeighborIndexBeforeEnd hp.isPath hall x) := by
    change (p.dropUntil x.1 hxmem).snd =
      p.getVert (p.support.idxOf x.1 + 1)
    rw [p.dropUntil_eq_drop hxmem]
    simp [Walk.drop_getVert]
  let q : G.Walk a (p.dropUntil x.1 hxmem).snd :=
    p.posaRotate x.1 hxmem hxa hxb hbx
  have hqp : q.IsPath := p.isPath_posaRotate hp.isPath x.1 hxmem hxa hxb hbx
  have hqlen : q.length = p.length := p.length_posaRotate x.1 hxmem hxa hxb hbx
  have hqmax : IsLongestPath q := ⟨hqp, hqlen.trans hp.length_eq⟩
  have hqdeg := hmax hqmax
  rw [hsnd] at hqdeg
  omega

/-- The injective list of successors of the neighbors of the final endpoint
of a longest path. -/
def longestPathEndpointSuccessor {a b : V} {p : G.Walk a b}
    (hp : IsLongestPath p) : G.neighborFinset b ↪ V :=
  (pathNeighborIndexBeforeEnd hp.isPath (fun y ↦
    longestPath_neighbor_mem_support_end hp
      ((SimpleGraph.mem_neighborFinset (G := G) (v := b) y.1).mp y.2))).trans
    (pathSuccessorEmbedding hp.isPath)

/-- The successor fan at the final endpoint of a longest path. -/
def longestPathEndpointFan {a b : V} {p : G.Walk a b}
    (hp : IsLongestPath p) : Finset V :=
  Finset.univ.map (longestPathEndpointSuccessor hp)

@[simp] lemma card_longestPathEndpointFan {a b : V} {p : G.Walk a b}
    (hp : IsLongestPath p) :
    (longestPathEndpointFan hp).card = G.degree b := by
  simp [longestPathEndpointFan, SimpleGraph.card_neighborFinset_eq_degree]

lemma end_mem_longestPathEndpointFan {a b : V} {p : G.Walk a b}
    (hp : IsLongestPath p) (hpos : 0 < p.length) :
    b ∈ longestPathEndpointFan hp := by
  have hpnon : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr hpos
  let x : G.neighborFinset b :=
    ⟨p.penultimate,
      (SimpleGraph.mem_neighborFinset (G := G) (v := b) p.penultimate).mpr
        (p.adj_penultimate hpnon).symm⟩
  apply Finset.mem_map.mpr
  refine ⟨x, Finset.mem_univ _, ?_⟩
  change p.getVert (p.support.idxOf p.penultimate + 1) = b
  have hpen : p.getVert (p.length - 1) = p.penultimate := rfl
  have hidx : p.support.idxOf p.penultimate = p.length - 1 := by
    have hmem : p.penultimate ∈ p.support := by
      rw [← hpen]
      exact p.getVert_mem_support _
    have hget := p.getVert_support_idxOf hmem
    apply hp.isPath.getVert_injOn
    · have := List.idxOf_lt_length_of_mem hmem
      rw [p.length_support] at this
      simp only [Set.mem_ofPred_eq]
      omega
    · simp only [Set.mem_ofPred_eq]
      omega
    · simpa [hpen] using hget
  rw [hidx, show p.length - 1 + 1 = p.length by omega]
  exact p.getVert_length

lemma degree_le_endpoint_of_mem_longestPathEndpointFan
    {a b : V} {p : G.Walk a b} (hp : IsLongestPath p)
    (hmax : ∀ {u v : V} {q : G.Walk u v}, IsLongestPath q →
      G.degree u + G.degree v ≤ G.degree a + G.degree b)
    {z : V} (hz : z ∈ longestPathEndpointFan hp) :
    G.degree z ≤ G.degree b := by
  obtain ⟨x, _hx, hxz⟩ := Finset.mem_map.mp hz
  rw [← hxz]
  exact degree_pathSuccessor_le_of_maximal_longestPath hp hmax x

/-- If no cycle is as long as `H`, the two endpoint rotation fans of a
longest path of length at least `H` are disjoint. -/
lemma disjoint_longestPathEndpointFans_of_no_long_cycle
    {a b : V} {p : G.Walk a b} (hp : IsLongestPath p)
    {H : ℕ} (hH : 3 ≤ H) (hlen : H ≤ p.length)
    (hno : ¬HasCycleAtLeast G H) :
    Disjoint (longestPathEndpointFan hp)
      (longestPathEndpointFan
        (p := p.reverse) ⟨hp.isPath.reverse, by simpa using hp.length_eq⟩) := by
  let hprev : IsLongestPath p.reverse :=
    ⟨hp.isPath.reverse, by simpa using hp.length_eq⟩
  rw [Finset.disjoint_left]
  intro z hzEnd hzStart
  obtain ⟨x, _hx, hxz⟩ := Finset.mem_map.mp hzEnd
  obtain ⟨y, _hy, hyz⟩ := Finset.mem_map.mp hzStart
  let i : Fin p.length :=
    pathNeighborIndexBeforeEnd hp.isPath (fun w ↦
      longestPath_neighbor_mem_support_end hp
        ((SimpleGraph.mem_neighborFinset (G := G) (v := b) w.1).mp w.2)) x
  let j : Fin p.reverse.length :=
    pathNeighborIndexBeforeEnd hprev.isPath (fun w ↦
      longestPath_neighbor_mem_support_end hprev
        ((SimpleGraph.mem_neighborFinset (G := G) (v := a) w.1).mp w.2)) y
  have hfanEq : p.getVert (i.val + 1) = p.reverse.getVert (j.val + 1) := by
    change longestPathEndpointSuccessor hp x =
      longestPathEndpointSuccessor hprev y
    exact hxz.trans hyz.symm
  have hidxEq : i.val + 1 = p.length - (j.val + 1) := by
    apply hp.isPath.getVert_injOn
    · simp only [Set.mem_ofPred_eq]
      omega
    · simp only [Set.mem_ofPred_eq]
      have hj := j.isLt
      simpa using Nat.sub_le p.length (j.val + 1)
    · simpa [Walk.getVert_reverse] using hfanEq
  have hi : i.val + 2 ≤ p.length := by
    have hj : j.val < p.length := by simpa using j.isLt
    omega
  have hbi : G.Adj b (p.getVert i.val) := by
    have hadj : G.Adj b x.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
    have hget := getVert_pathNeighborIndexBeforeEnd hp.isPath
      (fun w ↦ longestPath_neighbor_mem_support_end hp
        ((SimpleGraph.mem_neighborFinset (G := G) (v := b) w.1).mp w.2)) x
    change p.getVert i.val = x.1 at hget
    simpa [hget] using hadj
  have hai : G.Adj a (p.getVert (i.val + 2)) := by
    have hadj : G.Adj a y.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := a) y.1).mp y.2
    have hget := getVert_pathNeighborIndexBeforeEnd hprev.isPath
      (fun w ↦ longestPath_neighbor_mem_support_end hprev
        ((SimpleGraph.mem_neighborFinset (G := G) (v := a) w.1).mp w.2)) y
    change p.reverse.getVert j.val = y.1 at hget
    rw [Walk.getVert_reverse] at hget
    have harith : p.length - j.val = i.val + 2 := by omega
    rw [harith] at hget
    simpa [hget] using hadj
  exact hno ((hasCycleAtLeast_of_path_endpoint_chords hp.isPath
    (by omega) hi hbi hai).mono (by omega))

/-- Under the same no-long-cycle hypothesis, the two disjoint endpoint fans
miss at least one ambient vertex. -/
lemma card_endpointFans_le_card_sub_one_of_no_long_cycle
    {a b : V} {p : G.Walk a b} (hp : IsLongestPath p)
    {H : ℕ} (hH : 3 ≤ H) (hlen : H ≤ p.length)
    (hno : ¬HasCycleAtLeast G H) :
    (longestPathEndpointFan hp).card +
        (longestPathEndpointFan
          (p := p.reverse) ⟨hp.isPath.reverse, by simpa using hp.length_eq⟩).card ≤
      Fintype.card V - 1 := by
  let hprev : IsLongestPath p.reverse :=
    ⟨hp.isPath.reverse, by simpa using hp.length_eq⟩
  let R := longestPathEndpointFan hp
  let S := longestPathEndpointFan hprev
  have hdisj : Disjoint R S := by
    exact disjoint_longestPathEndpointFans_of_no_long_cycle hp hH hlen hno
  have hle : R.card + S.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  by_contra hnot
  change ¬R.card + S.card ≤ Fintype.card V - 1 at hnot
  have hcard : R.card + S.card = Fintype.card V := by omega
  have huniv : R ∪ S = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj]
    exact hcard
  have hpPos : 0 < p.length := by omega
  have haS : a ∈ S := by
    exact end_mem_longestPathEndpointFan hprev (by simpa using hpPos)
  have hbR : b ∈ R := end_mem_longestPathEndpointFan hp hpPos
  have hbS : b ∉ S := Finset.disjoint_left.mp hdisj hbR
  let P : ℕ → Prop := fun t ↦ p.getVert t ∉ S
  have hex : ∃ t, P t := ⟨p.length, by simpa [P] using hbS⟩
  let t := Nat.find hex
  have htP : P t := Nat.find_spec hex
  have htLe : t ≤ p.length := Nat.find_min' hex (by simpa [P] using hbS)
  have htPos : 0 < t := by
    by_contra ht
    have ht0 : t = 0 := by omega
    have : p.getVert 0 ∉ S := by simpa [P, ht0] using htP
    exact this (by simpa using haS)
  let i := t - 1
  have hit : i + 1 = t := by dsimp [i]; omega
  have hiS : p.getVert i ∈ S := by
    by_contra hi
    have hiP : P i := hi
    exact (Nat.find_min hex (by dsimp [i]; omega)) hiP
  have hi1notS : p.getVert (i + 1) ∉ S := by simpa [hit] using htP
  have hi1R : p.getVert (i + 1) ∈ R := by
    have : p.getVert (i + 1) ∈ R ∪ S := by rw [huniv]; simp
    exact (Finset.mem_union.mp this).resolve_right hi1notS
  obtain ⟨x, _hx, hxEq⟩ := Finset.mem_map.mp hi1R
  obtain ⟨y, _hy, hyEq⟩ := Finset.mem_map.mp hiS
  let ix : Fin p.length :=
    pathNeighborIndexBeforeEnd hp.isPath (fun w ↦
      longestPath_neighbor_mem_support_end hp
        ((SimpleGraph.mem_neighborFinset (G := G) (v := b) w.1).mp w.2)) x
  let jy : Fin p.reverse.length :=
    pathNeighborIndexBeforeEnd hprev.isPath (fun w ↦
      longestPath_neighbor_mem_support_end hprev
        ((SimpleGraph.mem_neighborFinset (G := G) (v := a) w.1).mp w.2)) y
  have hix : ix.val = i := by
    apply Nat.add_right_cancel (m := 1)
    apply hp.isPath.getVert_injOn
    · simp only [Set.mem_ofPred_eq]
      omega
    · simp only [Set.mem_ofPred_eq]
      omega
    · change longestPathEndpointSuccessor hp x = p.getVert (i + 1)
      exact hxEq
  have hbi : G.Adj b (p.getVert i) := by
    have hadj : G.Adj b x.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
    have hget := getVert_pathNeighborIndexBeforeEnd hp.isPath
      (fun w ↦ longestPath_neighbor_mem_support_end hp
        ((SimpleGraph.mem_neighborFinset (G := G) (v := b) w.1).mp w.2)) x
    change p.getVert ix.val = x.1 at hget
    rw [hix] at hget
    simpa [hget] using hadj
  have hjEq : p.length - (jy.val + 1) = i := by
    apply hp.isPath.getVert_injOn
    · simp only [Set.mem_ofPred_eq]
      exact Nat.sub_le _ _
    · simp only [Set.mem_ofPred_eq]
      omega
    · change p.reverse.getVert (jy.val + 1) = p.getVert i at hyEq
      simpa [Walk.getVert_reverse] using hyEq
  have hjPred : p.length - jy.val = i + 1 := by
    have hj : jy.val < p.length := by simpa using jy.isLt
    omega
  have hai : G.Adj a (p.getVert (i + 1)) := by
    have hadj : G.Adj a y.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := a) y.1).mp y.2
    have hget := getVert_pathNeighborIndexBeforeEnd hprev.isPath
      (fun w ↦ longestPath_neighbor_mem_support_end hprev
        ((SimpleGraph.mem_neighborFinset (G := G) (v := a) w.1).mp w.2)) y
    change p.reverse.getVert jy.val = y.1 at hget
    rw [Walk.getVert_reverse, hjPred] at hget
    simpa [hget] using hadj
  have hiBound : i + 1 ≤ p.length := by rw [hit]; exact htLe
  exact hno ((hasCycleAtLeast_succ_of_path_endpoint_chords hp.isPath
    (by omega) hiBound hbi hai).mono (by omega))

/-- A longest path in a connected graph of order at least three has at least
two edges. -/
lemma two_le_length_of_longestPath_connected
    {a b : V} {p : G.Walk a b} (hn : 3 ≤ Fintype.card V)
    (hp : IsLongestPath p) (hconn : G.Connected) : 2 ≤ p.length := by
  by_contra hlen
  have hsCard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.isPath.support_nodup, p.length_support]
  have hc : ∃ c : V, c ∉ p.support := by
    by_contra hall
    push Not at hall
    have heq : p.support.toFinset = Finset.univ := by
      ext x
      simp [hall x]
    have := congrArg Finset.card heq
    rw [hsCard, Finset.card_univ] at this
    omega
  obtain ⟨c, hc⟩ := hc
  obtain ⟨q, hq⟩ := hconn.exists_isPath c a
  have hqle := (isLongestPath_iff.mp hp).2 c a q hq
  have hca : c ≠ a := by
    intro hca
    subst c
    exact hc p.start_mem_support
  have hqpos : 0 < q.length := by
    rw [← Walk.not_nil_iff_lt_length]
    exact Walk.not_nil_of_ne hca
  have hplen : p.length = 1 := by omega
  have hqlen : q.length = 1 := by omega
  have hcaAdj : G.Adj c a := q.adj_of_length_eq_one hqlen
  have hrpath : (Walk.cons hcaAdj p).IsPath := hp.isPath.cons hc
  have hrle := (isLongestPath_iff.mp hp).2 c b (Walk.cons hcaAdj p) hrpath
  simp [hplen] at hrle

/-- Woodall's endpoint-fan lemma: the stated minimum degree and edge
threshold force a cycle at least as long as every supplied path. -/
theorem hasCycleAtLeast_of_minDegree_edgeCount_path
    (q H : ℕ) (hH : 3 ≤ H)
    (hmin : ∀ z, q ≤ G.degree z)
    (hedge : (Fintype.card V - q).choose 2 + (q + 1).choose 2 + 1 ≤
      G.edgeFinset.card)
    {u v : V} {w : G.Walk u v} (hw : w.IsPath) (hwlen : H ≤ w.length) :
    HasCycleAtLeast G H := by
  letI : Nonempty V := ⟨u⟩
  obtain ⟨ab, hab, hmax⟩ := (longestEndpointPairs G).exists_max_image
    (fun xy ↦ G.degree xy.1 + G.degree xy.2)
    (longestEndpointPairs_nonempty (G := G) inferInstance)
  rcases ab with ⟨a, b⟩
  obtain ⟨p, hp⟩ := mem_longestEndpointPairs.mp hab
  have hmax' : ∀ {x y : V} {r : G.Walk x y}, IsLongestPath r →
      G.degree x + G.degree y ≤ G.degree a + G.degree b := by
    intro x y r hr
    exact hmax (x, y) (mem_longestEndpointPairs.mpr ⟨r, hr⟩)
  have hpLong : H ≤ p.length := by
    exact hwlen.trans ((isLongestPath_iff.mp hp).2 u v w hw)
  let hprev : IsLongestPath p.reverse :=
    ⟨hp.isPath.reverse, by simpa using hp.length_eq⟩
  have hmaxrev : ∀ {x y : V} {r : G.Walk x y}, IsLongestPath r →
      G.degree x + G.degree y ≤ G.degree b + G.degree a := by
    intro x y r hr
    have := hmax' hr
    omega
  let R : Finset V := longestPathEndpointFan hp
  let S : Finset V := longestPathEndpointFan hprev
  by_contra hno
  have hdisj : Disjoint R S := by
    exact disjoint_longestPathEndpointFans_of_no_long_cycle hp hH hpLong hno
  have hfanCard : R.card + S.card ≤ Fintype.card V - 1 := by
    exact card_endpointFans_le_card_sub_one_of_no_long_cycle hp hH hpLong hno
  have hcardR : R.card = G.degree b := by
    exact card_longestPathEndpointFan hp
  have hcardS : S.card = G.degree a := by
    exact card_longestPathEndpointFan hprev
  have hendSum : G.degree a + G.degree b ≤ Fintype.card V - 1 := by
    rw [hcardR, hcardS] at hfanCard
    omega
  have hRdeg : ∀ z ∈ R, G.degree z ≤ G.degree b := by
    intro z hz
    exact degree_le_endpoint_of_mem_longestPathEndpointFan hp hmax' hz
  have hSdeg : ∀ z ∈ S, G.degree z ≤ G.degree a := by
    intro z hz
    exact degree_le_endpoint_of_mem_longestPathEndpointFan hprev hmaxrev hz
  have hallDeg : ∀ z : V, G.degree z ≤ Fintype.card V - 1 := by
    intro z
    have := G.degree_lt_card_verts z
    omega
  have hdegreeSum := sum_univ_le_three_parts (fun z ↦ G.degree z)
    R S (G.degree b) (G.degree a) (Fintype.card V - 1)
    hdisj hRdeg hSdeg hallDeg
  rw [G.sum_degrees_eq_twice_card_edges, hcardR, hcardS] at hdegreeSum
  have horder : 1 ≤ Fintype.card V := by
    have := hw.length_lt
    omega
  have hnumeric := endpoint_handshake_bound (N := Fintype.card V) (q := q)
    (a := G.degree a) (b := G.degree b) horder (hmin a) (hmin b) hendSum
  have hupper :
      G.degree b * G.degree b + G.degree a * G.degree a +
          (Fintype.card V - G.degree b - G.degree a) *
            (Fintype.card V - 1) ≤
        2 * ((Fintype.card V - q).choose 2 + (q + 1).choose 2) := by
    simpa [Nat.add_comm] using hnumeric
  have htwice : 2 * G.edgeFinset.card ≤
      2 * ((Fintype.card V - q).choose 2 + (q + 1).choose 2) :=
    hdegreeSum.trans hupper
  omega

/-- At Woodall's threshold, connectivity and minimum degree `k+2` force a
cycle of length at least `min n (2(k+2))`.  This is the precise Dirac-type
input needed in the high-minimum-degree branch. -/
theorem hasCycleAtLeast_min_card_twice_shift_of_woodall
    (k : ℕ) (hn : 3 ≤ Fintype.card V) (hconn : G.Connected)
    (hmin : ∀ z, k + 2 ≤ G.degree z)
    (hedge : woodallBound (Fintype.card V) k + 1 ≤
      G.edgeFinset.card) :
    HasCycleAtLeast G (min (Fintype.card V) (2 * (k + 2))) := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ab, hab⟩ := longestEndpointPairs_nonempty (G := G) inferInstance
  rcases ab with ⟨a, b⟩
  obtain ⟨p, hp⟩ := mem_longestEndpointPairs.mp hab
  by_cases hham : G.IsHamiltonian
  · obtain ⟨v, c, hc⟩ := hham (by omega)
    exact ⟨v, c, hc.isCycle, by
      rw [hc.length_eq]
      exact Nat.min_le_left _ _⟩
  have hlen : 2 ≤ p.length :=
    two_le_length_of_longestPath_connected hn hp hconn
  have hsum := degree_add_degree_le_length_of_longestPath hp hlen hconn hham
  change G.degree a + G.degree b ≤ p.length at hsum
  have hpLong : 2 * (k + 2) ≤ p.length := by
    have ha := hmin a
    have hb := hmin b
    omega
  by_cases hnshort : Fintype.card V < 2 * (k + 2)
  · have hpLt := hp.isPath.length_lt
    omega
  · have hnlong : 2 * (k + 2) ≤ Fintype.card V := by omega
    have hmiddle : k + 2 ≤ Fintype.card V - (k + 2) := by omega
    have hthreshold :
        (Fintype.card V - (k + 2)).choose 2 +
            (k + 2 + 1).choose 2 + 1 ≤ G.edgeFinset.card := by
      calc
        (Fintype.card V - (k + 2)).choose 2 +
              (k + 2 + 1).choose 2 + 1 =
            (Fintype.card V - (k + 2)).choose 2 +
              ((k + 2).choose 2 + (k + 2)) + 1 := by
                rw [choose_two_succ (k + 2)]
        _ ≤ ((Fintype.card V - (k + 2)).choose 2 +
              (Fintype.card V - (k + 2))) +
              (k + 2).choose 2 + 1 := by omega
        _ = woodallBound (Fintype.card V) k + 1 := by
          unfold woodallBound
          rw [← choose_two_succ (Fintype.card V - (k + 2))]
          congr 3
          omega
        _ ≤ G.edgeFinset.card := hedge
    have hcycle := hasCycleAtLeast_of_minDegree_edgeCount_path
      (G := G) (k + 2) (2 * (k + 2)) (by omega) hmin hthreshold
      hp.isPath hpLong
    simpa [Nat.min_eq_right hnlong] using hcycle

/-- The rotation-counting core of Pósa's criterion, for a longest path whose
endpoint degree sum is maximal and whose final endpoint has the smaller
degree. -/
lemma hamiltonian_of_posa_of_maximal_longestPath
    {a b : V} {p : G.Walk a b} (hn : 3 ≤ Fintype.card V)
    (hP : PosaDegreeCondition G) (hp : IsLongestPath p)
    (hmax : ∀ {u v : V} {q : G.Walk u v}, IsLongestPath q →
      G.degree u + G.degree v ≤ G.degree a + G.degree b)
    (hba : G.degree b ≤ G.degree a) : G.IsHamiltonian := by
  have hconn := hP.connected hn
  by_contra hnham
  have hlen : 2 ≤ p.length := two_le_length_of_longestPath_connected hn hp hconn
  have hsum := degree_add_degree_le_length_of_longestPath hp hlen hconn hnham
  have hallEnd : ∀ x : G.neighborFinset b, x.1 ∈ p.support := by
    intro x
    exact longestPath_neighbor_mem_support_end hp
      ((SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2)
  let eidx : G.neighborFinset b ↪ Fin p.length :=
    pathNeighborIndexBeforeEnd hp.isPath hallEnd
  let eend : G.neighborFinset b ↪ V :=
    eidx.trans (pathSuccessorEmbedding hp.isPath)
  let R : Finset V := Finset.univ.map eend
  have hcardR : R.card = G.degree b := by
    simp [R, eend, SimpleGraph.card_neighborFinset_eq_degree]
  have hendDeg : ∀ z ∈ R, G.degree z ≤ G.degree b := by
    intro z hz
    obtain ⟨x, _hx, hxz⟩ := Finset.mem_map.mp hz
    have hbx : G.Adj b x.1 :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := b) x.1).mp x.2
    have hxmem : x.1 ∈ p.support := hallEnd x
    have hxa : x.1 ≠ a := by
      intro hxa
      have hbaAdj : G.Adj b a := by simpa [hxa] using hbx
      exact (SimpleGraph.Walk.not_adj_end_start_of_longest_path hp.isPath hlen
        (isLongestPath_iff.mp hp).2 hconn hnham) hbaAdj
    have hxb : x.1 ≠ b := hbx.ne.symm
    have hsnd : (p.dropUntil x.1 hxmem).snd = eend x := by
      rw [p.dropUntil_eq_drop hxmem]
      simp [eend, eidx, pathNeighborIndexBeforeEnd,
        pathSuccessorEmbedding, Walk.drop_getVert]
      rfl
    let q : G.Walk a (p.dropUntil x.1 hxmem).snd :=
      p.posaRotate x.1 hxmem hxa hxb hbx
    have hqp : q.IsPath := p.isPath_posaRotate hp.isPath x.1 hxmem hxa hxb hbx
    have hqlen : q.length = p.length := p.length_posaRotate x.1 hxmem hxa hxb hbx
    have hqmax : IsLongestPath q := ⟨hqp, hqlen.trans hp.length_eq⟩
    have hqdeg := hmax hqmax
    rw [hsnd, hxz] at hqdeg
    omega
  have hRsub : R ⊆ lowDegreeFinset G (G.degree b) := by
    intro z hz
    exact mem_lowDegreeFinset.mpr (hendDeg z hz)
  have hRle : R.card ≤ (lowDegreeFinset G (G.degree b)).card :=
    Finset.card_le_card hRsub
  have hp_lt_card := hp.isPath.length_lt
  have hbpos : 0 < G.degree b := by
    have hpnon : ¬p.Nil := by
      rw [Walk.not_nil_iff_lt_length]
      omega
    exact (p.adj_penultimate hpnon).degree_pos_right
  have htwodeg : 2 * G.degree b ≤ Fintype.card V - 1 := by omega
  rcases htwodeg.lt_or_eq with hstrict | hmiddle
  · have hlow := hP.1 (G.degree b) hstrict
    rw [hcardR] at hRle
    omega
  · have haeq : G.degree a = G.degree b := by
      by_contra hne
      have : G.degree b < G.degree a := lt_of_le_of_ne hba (Ne.symm hne)
      omega
    have haLow : a ∈ lowDegreeFinset G (G.degree b) := by
      exact mem_lowDegreeFinset.mpr (by omega)
    have haR : a ∉ R := by
      intro ha
      obtain ⟨x, _hx, hxa⟩ := Finset.mem_map.mp ha
      have hpos : 0 < p.support.idxOf x.1 + 1 := by omega
      have hget : p.getVert (p.support.idxOf x.1 + 1) = a := by
        change p.getVert (p.support.idxOf x.1 + 1) = a at hxa
        exact hxa
      have hzero : p.getVert 0 = a := p.getVert_zero
      have hidxlt : p.support.idxOf x.1 < p.length := by
        have := (eidx x).isLt
        exact this
      have heq := hp.isPath.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by exact Nat.zero_le _ ) (hget.trans hzero.symm)
      omega
    have hins : insert a R ⊆ lowDegreeFinset G (G.degree b) :=
      Finset.insert_subset haLow hRsub
    have hcardins := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem haR, hcardR] at hcardins
    have hlow := hP.2 (G.degree b) hmiddle
    omega

/-- Pósa--Nash-Williams Hamiltonicity criterion in the exact form used by
Woodall. -/
theorem hamiltonian_of_posaDegreeCondition
    (hn : 3 ≤ Fintype.card V) (hP : PosaDegreeCondition G) :
    G.IsHamiltonian := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨ab, hab, hmax⟩ := (longestEndpointPairs G).exists_max_image
    (fun uv ↦ G.degree uv.1 + G.degree uv.2)
    (longestEndpointPairs_nonempty (G := G) hne)
  rcases ab with ⟨a, b⟩
  obtain ⟨p, hp⟩ := mem_longestEndpointPairs.mp hab
  have hmax' : ∀ {u v : V} {q : G.Walk u v}, IsLongestPath q →
      G.degree u + G.degree v ≤ G.degree a + G.degree b := by
    intro u v q hq
    exact hmax (u, v) (mem_longestEndpointPairs.mpr ⟨q, hq⟩)
  by_cases hba : G.degree b ≤ G.degree a
  · exact hamiltonian_of_posa_of_maximal_longestPath hn hP hp hmax' hba
  · have hprev : IsLongestPath p.reverse := by
      exact ⟨hp.isPath.reverse, by simpa using hp.length_eq⟩
    have hmaxrev : ∀ {u v : V} {q : G.Walk u v}, IsLongestPath q →
        G.degree u + G.degree v ≤ G.degree b + G.degree a := by
      intro u v q hq
      have := hmax' hq
      omega
    exact hamiltonian_of_posa_of_maximal_longestPath
      (a := b) (b := a) (p := p.reverse) hn hP hprev hmaxrev (by omega)

end PosaCriterion

section BondyPancyclic

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- On a simple cycle, the first occurrence of the vertex in position `i`
is exactly position `i`, as long as `i` is before the repeated endpoint. -/
lemma support_idxOf_getVert_eq_of_lt
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) {i : ℕ}
    (hi : i < c.length) : c.support.idxOf (c.getVert i) = i := by
  have hmem : c.getVert i ∈ c.support := Walk.getVert_mem_support c i
  have hidxLe : c.support.idxOf (c.getVert i) ≤ c.length := by
    have h := List.idxOf_lt_length_of_mem hmem
    rw [c.length_support] at h
    omega
  have hget : c.getVert (c.support.idxOf (c.getVert i)) = c.getVert i :=
    c.getVert_support_idxOf hmem
  have hidxLt : c.support.idxOf (c.getVert i) < c.length := by
    by_contra hnot
    have hidxEq : c.support.idxOf (c.getVert i) = c.length := by omega
    have hbase : c.getVert i = a := by
      rw [hidxEq, Walk.getVert_length] at hget
      exact hget.symm
    have hiZero : i = 0 := by
      rcases (hc.getVert_endpoint_iff hi.le).mp hbase with h | h
      · exact h
      · omega
    subst i
    have hzero : c.support.idxOf a = 0 := by
      cases c <;> simp
    rw [Walk.getVert_zero, hzero] at hidxEq
    exact hc.not_nil (Walk.length_eq_zero_iff.mp hidxEq.symm)
  exact hc.getVert_injOn'
    (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) hget

/-- Rotating a simple cycle to position `i` turns position `r` into the
old cyclic position `i+r`.  The formula is stated without `%` by splitting
at the end of the old linear presentation. -/
lemma getVert_rotate_getVert
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) {i r : ℕ}
    (hi : i < c.length) (hr : r ≤ c.length) :
    (c.rotate (c.getVert i) (Walk.getVert_mem_support c i)).getVert r =
      if r < c.length - i then c.getVert (i + r)
      else c.getVert (r - (c.length - i)) := by
  have hidx : c.support.idxOf (c.getVert i) = i :=
    support_idxOf_getVert_eq_of_lt hc hi
  rw [Walk.rotate, c.dropUntil_eq_drop, c.takeUntil_eq_take]
  simp only [Walk.getVert_append, Walk.length_copy, Walk.drop_length,
    Walk.getVert_copy, Walk.drop_getVert, hidx]
  split_ifs with h
  · rfl
  · simp [Walk.take_getVert, hidx,
      Nat.min_eq_right (by omega : r - (c.length - i) ≤ i)]

lemma add_mod_eq_sub_of_lt_two {n a b : ℕ} (hn : 0 < n)
    (ha : a < n) (hb : b < n) (hadd : n ≤ a + b) :
    (a + b) % n = a + b - n := by
  have h := Nat.add_mod_add_of_le_add_mod (a := a) (b := b) (c := n) (by
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hadd)
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  omega

/-- The preceding rotation formula in the usual modular notation. -/
lemma getVert_rotate_getVert_mod
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) {i r : ℕ}
    (hi : i < c.length) (hr : r < c.length) :
    (c.rotate (c.getVert i) (Walk.getVert_mem_support c i)).getVert r =
      c.getVert ((i + r) % c.length) := by
  rw [getVert_rotate_getVert hc hi hr.le]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rw [add_mod_eq_sub_of_lt_two (by omega : 0 < c.length) hi hr (by omega)]
    congr 1
    omega

/-- An external vertex adjacent to positions `i` and `i+r` on a cycle
closes the intervening cyclic arc to a cycle of length `r+2`. -/
lemma hasCycleLength_add_two_of_cycle_external_shift
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hx : x ∉ c.support) {i r : Fin c.length} (hrpos : 0 < r.val)
    (hxi : G.Adj x (c.getVert i.val))
    (hxr : G.Adj x (c.getVert ((finCycle r) i).val)) :
    HasCycleLength G (r.val + 2) := by
  let cr := c.rotate (c.getVert i.val) (Walk.getVert_mem_support c i.val)
  have hcr : cr.IsCycle := by
    exact hc.rotate (Walk.getVert_mem_support c i.val)
  have hxcr : x ∉ cr.support := by
    simpa [cr] using hx
  apply hasCycleLength_add_two_of_cycle_external hcr hxcr hrpos
    (by simpa [cr] using r.isLt) hxi
  have hrot := getVert_rotate_getVert_mod hc i.isLt r.isLt
  rw [show cr = c.rotate (c.getVert i.val)
      (Walk.getVert_mem_support c i.val) by rfl, hrot]
  simpa [finCycle_apply, Fin.add_def] using hxr

/-- Inserting an external vertex into an edge of a simple cycle produces
a cycle one edge longer. -/
lemma hasCycleLength_succ_of_cycle_external_adjacent
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hx : x ∉ c.support) {i : Fin c.length}
    (hxi : G.Adj x (c.getVert i.val))
    (hxis : G.Adj x
      (c.getVert ((finCycle ⟨1, by
        have hthree := hc.three_le_length
        omega⟩) i).val)) :
    HasCycleLength G (c.length + 1) := by
  let cr := c.rotate (c.getVert i.val) (Walk.getVert_mem_support c i.val)
  have hcr : cr.IsCycle := hc.rotate (Walk.getVert_mem_support c i.val)
  have hxcr : x ∉ cr.support := by
    simpa [cr] using hx
  let p := cr.drop 1
  have hp : p.IsPath := hcr.isPath_drop (by
    have hthree := hc.three_le_length
    omega)
  have hpLen : p.length = c.length - 1 := by
    simp [p, cr]
  have hpPos : 0 < p.length := by
    rw [hpLen]
    have hthree := hc.three_le_length
    omega
  have hxP : x ∉ p.support := by
    intro hxp
    have hsuffix : p.support <:+ cr.support := by
      dsimp [p]
      rw [Walk.drop_support_eq_support_drop_min]
      exact List.drop_suffix _ _
    exact hxcr (hsuffix.subset hxp)
  have hstart : cr.getVert 1 =
      c.getVert ((finCycle ⟨1, by
        have hthree := hc.three_le_length
        omega⟩) i).val := by
    have hrot := getVert_rotate_getVert_mod hc i.isLt
      (show 1 < c.length by
        have hthree := hc.three_le_length
        omega)
    simpa [cr, finCycle_apply, Fin.add_def] using hrot
  have hxisStart : G.Adj x (cr.getVert 1) := by
    rw [hstart]
    exact hxis
  have hcycle := hasCycleLength_add_two_of_path_external hp hpPos hxP
    hxi hxisStart
  convert hcycle using 1 <;> omega

/-- Every vertex of a simple cycle has a first occurrence before the
repeated terminal vertex. -/
lemma support_idxOf_lt_length_of_mem_isCycle
    {a y : V} {c : G.Walk a a} (hc : c.IsCycle) (hy : y ∈ c.support) :
    c.support.idxOf y < c.length := by
  have hidxLe : c.support.idxOf y ≤ c.length := by
    have h := List.idxOf_lt_length_of_mem hy
    rw [c.length_support] at h
    omega
  by_contra hnot
  have hidxEq : c.support.idxOf y = c.length := by omega
  have hget : c.getVert (c.support.idxOf y) = y := c.getVert_support_idxOf hy
  have hay : a = y := by simpa [hidxEq] using hget
  have hzero : c.support.idxOf a = 0 := by
    cases c <;> simp
  rw [← hay, hzero] at hidxEq
  exact hc.not_nil (Walk.length_eq_zero_iff.mp hidxEq.symm)

/-- Positions on a cycle occupied by neighbors of `x`. -/
def cycleNeighborPositions {a : V} (c : G.Walk a a) (x : V) :
    Finset (Fin c.length) :=
  Finset.univ.filter fun i ↦ G.Adj x (c.getVert i.val)

@[simp] lemma mem_cycleNeighborPositions
    {a x : V} {c : G.Walk a a} {i : Fin c.length} :
    i ∈ cycleNeighborPositions (G := G) c x ↔
      G.Adj x (c.getVert i.val) := by
  simp [cycleNeighborPositions]

/-- If a cycle contains every vertex other than `x`, its cyclic neighbor
positions count the full degree of `x`. -/
lemma card_cycleNeighborPositions_eq_degree
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hall : ∀ y, y ≠ x → y ∈ c.support) :
    (cycleNeighborPositions (G := G) c x).card = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij
      (fun i _hi ↦ c.getVert i.val)
  · intro i hi
    exact (SimpleGraph.mem_neighborFinset (G := G) (v := x) _).mpr
      (mem_cycleNeighborPositions.mp hi)
  · intro i hi j hj hij
    apply Fin.ext
    apply hc.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)
    exact hij
  · intro y hy
    have hxy : G.Adj x y :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := x) y).mp hy
    have hyc : y ∈ c.support := hall y hxy.ne.symm
    let j : Fin c.length :=
      ⟨c.support.idxOf y, support_idxOf_lt_length_of_mem_isCycle hc hyc⟩
    have hjget : c.getVert j.val = y := by
      exact c.getVert_support_idxOf hyc
    have hjmem : j ∈ cycleNeighborPositions (G := G) c x := by
      exact mem_cycleNeighborPositions.mpr (by simpa [hjget] using hxy)
    refine ⟨j, hjmem, ?_⟩
    exact hjget

/-- More than half of a finite cyclic set meets each of its translates. -/
lemma exists_mem_and_finCycle_mem
    {m : ℕ} (A : Finset (Fin m)) (r : Fin m)
    (hcard : m < 2 * A.card) :
    ∃ i ∈ A, (finCycle r) i ∈ A := by
  by_contra hno
  push_neg at hno
  let B : Finset (Fin m) := A.map (finCycle r).toEmbedding
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨i, hiA, hiz⟩ := Finset.mem_map.mp hzB
    exact hno i hiA (by simpa [← hiz] using hzA)
  have hsub : A ∪ B ⊆ (Finset.univ : Finset (Fin m)) := by simp
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ,
    Fintype.card_fin, show B.card = A.card by simp [B]] at hle
  omega

/-- A vertex outside a cycle and adjacent to more than half of its vertices
creates all cycle lengths obtained by inserting it into cyclic arcs. -/
lemma hasCycleLength_of_external_high_degree
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hx : x ∉ c.support) (hall : ∀ y, y ≠ x → y ∈ c.support)
    (hdeg : c.length < 2 * G.degree x) {d : ℕ}
    (hd : 3 ≤ d) (hdc : d ≤ c.length + 1) :
    HasCycleLength G d := by
  have hrpos : 0 < d - 2 := by omega
  have hrlt : d - 2 < c.length := by omega
  let r : Fin c.length := ⟨d - 2, hrlt⟩
  let A := cycleNeighborPositions (G := G) c x
  have hAcard : A.card = G.degree x := by
    exact card_cycleNeighborPositions_eq_degree hc hall
  obtain ⟨i, hiA, hirA⟩ :=
    exists_mem_and_finCycle_mem A r (by simpa [hAcard] using hdeg)
  have hcycle := hasCycleLength_add_two_of_cycle_external_shift hc hx
    (i := i) (r := r) (by simpa [r] using hrpos)
    (mem_cycleNeighborPositions.mp hiA)
    (mem_cycleNeighborPositions.mp hirA)
  convert hcycle using 1 <;> simp [r] <;> omega

lemma mem_support_drop_take_exists_index
    {a z : V} {c : G.Walk a a} {start len : ℕ}
    (hz : z ∈ ((c.drop start).take len).support) :
    ∃ t ≤ ((c.drop start).take len).length,
      z = c.getVert (start + t) := by
  obtain ⟨t, ht, htle⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  refine ⟨t, htle, ?_⟩
  have htlen : t ≤ len := htle.trans (by simp)
  rw [Walk.take_getVert, Nat.min_eq_right htlen, Walk.drop_getVert] at ht
  exact ht.symm

/-- Two chords with endpoints shifted by two positions splice out the
single intervening vertex and hence give a cycle one shorter.  This is
the non-wrapping case of Bondy's degree-sum argument. -/
lemma hasCycleLength_pred_of_shift_two_chords_nowrap
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k + 2 < c.length)
    (h0k : G.Adj (c.getVert 0) (c.getVert k))
    (h1k : G.Adj (c.getVert 1) (c.getVert (k + 2))) :
    HasCycleLength G (c.length - 1) := by
  let seg := (c.drop 1).take (k - 1)
  have hsegLen : seg.length = k - 1 := by
    simp [seg, Nat.min_eq_left (by omega : k - 1 ≤ c.length - 1)]
  have hsegEnd : (c.drop 1).getVert (k - 1) = c.getVert k := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  let left : G.Walk (c.getVert k) (c.getVert 1) :=
    seg.reverse.copy hsegEnd (by simp [seg])
  have hleft : left.IsPath := by
    simpa [left, seg] using
      (((hc.isPath_drop (n := 1) (by omega)).take (k - 1)).reverse)
  have hleftLen : left.length = k - 1 := by simp [left, hsegLen]
  have hk2NotLeft : c.getVert (k + 2) ∉ left.support := by
    intro hz
    have hzSeg : c.getVert (k + 2) ∈ seg.support := by
      simpa [left, Walk.support_reverse] using hz
    obtain ⟨t, ht, hzt⟩ := mem_support_drop_take_exists_index hzSeg
    have htBound : t ≤ k - 1 := by rw [hsegLen] at ht; exact ht
    have heq := hc.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hzt.symm
    omega
  let p1 := left.concat h1k
  have hp1 : p1.IsPath := hleft.concat hk2NotLeft h1k
  have hp1Len : p1.length = k := by simp [p1, hleftLen]; omega
  let right := c.drop (k + 2)
  have hright : right.IsPath := hc.isPath_drop (by omega)
  have hrightLen : right.length = c.length - (k + 2) := by simp [right]
  have hdisj : p1.support.Disjoint right.support.tail := by
    intro z hzp hzr
    have hzLeft : z ∈ left.support ∨ z = c.getVert (k + 2) := by
      simpa [p1, Walk.support_concat] using hzp
    have hzrSupp : z ∈ right.support := by
      exact (right.mem_support_iff).mpr (Or.inr hzr)
    obtain ⟨t, hzt, ht⟩ := Walk.mem_support_iff_exists_getVert.mp hzrSupp
    have htBound : t ≤ c.length - (k + 2) := by
      rw [hrightLen] at ht
      exact ht
    have hztOrig : z = c.getVert (k + 2 + t) := by
      simpa [right, Walk.drop_getVert] using hzt.symm
    have hzNeStart : z ≠ c.getVert (k + 2) := by
      have hn := hright.support_nodup
      rw [← right.cons_tail_support] at hn
      intro hzEq
      exact (List.nodup_cons.mp hn).1 (by simpa [hzEq] using hzr)
    have htPos : 0 < t := by
      by_contra ht0
      have : t = 0 := by omega
      subst t
      exact hzNeStart (by simpa using hztOrig)
    rcases hzLeft with hzLeft | hzK2
    · have hzSeg : z ∈ seg.support := by
        simpa [left, Walk.support_reverse] using hzLeft
      obtain ⟨s, hs, hzs⟩ := mem_support_drop_take_exists_index hzSeg
      have hsBound : s ≤ k - 1 := by rw [hsegLen] at hs; exact hs
      have heq := hc.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega)
        (hzs.symm.trans hztOrig)
      omega
    · have heq := hc.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega)
        (hzK2.symm.trans hztOrig)
      omega
  let q := p1.append right
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    rw [show q.support = p1.support ++ right.support.tail by
      simp [q, Walk.support_append]]
    exact List.nodup_append'.2
      ⟨hp1.support_nodup, hright.support_nodup.tail, hdisj⟩
  have hqLen : q.length = c.length - 2 := by
    simp [q, hp1Len, hrightLen]
    omega
  have hclose : G.Adj a (c.getVert k) := by simpa using h0k
  have hedge : s(a, c.getVert k) ∉ q.edges := by
    intro he
    have hone : q.length = 1 := hq.length_eq_one_of_mem_edges (by
      simpa [Sym2.eq_swap] using he)
    omega
  let z : G.Walk a a :=
    Walk.cons hclose q
  have hz : z.IsCycle :=
    SimpleGraph.Path.cons_isCycle ⟨q, hq⟩ hclose hedge
  refine ⟨a, z, hz, ?_⟩
  simp [z, hqLen]
  omega

/-- A chord from the initial vertex to the penultimate cycle vertex cuts
off the final vertex and gives a cycle one shorter. -/
lemma hasCycleLength_pred_of_chord_penultimate
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) (hlen : 4 ≤ c.length)
    (hchord : G.Adj (c.getVert 0) (c.getVert (c.length - 2))) :
    HasCycleLength G (c.length - 1) := by
  let p := (c.take (c.length - 2)).reverse
  have hp : p.IsPath := (hc.isPath_take (by omega)).reverse
  have hpLen : p.length = c.length - 2 := by simp [p]
  have hclose : G.Adj a (c.getVert (c.length - 2)) := by
    simpa using hchord
  have hedge : s(a, c.getVert (c.length - 2)) ∉ p.edges := by
    intro he
    have hone : p.length = 1 := hp.length_eq_one_of_mem_edges (by
      simpa [Sym2.eq_swap] using he)
    omega
  let z : G.Walk a a := Walk.cons hclose p
  have hz : z.IsCycle :=
    SimpleGraph.Path.cons_isCycle ⟨p, hp⟩ hclose hedge
  refine ⟨a, z, hz, ?_⟩
  simp [z, hpLen]
  omega

/-- Modular form of the shift-two splice. -/
lemma hasCycleLength_pred_of_shift_two_chords
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) (hlen : 4 ≤ c.length)
    {k : Fin c.length}
    (h0k : G.Adj (c.getVert 0) (c.getVert k.val))
    (h1k : G.Adj (c.getVert 1)
      (c.getVert ((finCycle ⟨2, by omega⟩) k).val)) :
    HasCycleLength G (c.length - 1) := by
  have hk0 : k.val ≠ 0 := by
    intro hk
    apply h0k.ne
    congr 1
    exact hk.symm
  have hkpos : 1 ≤ k.val := by omega
  have hkLast : k.val ≠ c.length - 1 := by
    intro hk
    have hshift : ((finCycle ⟨2, by omega⟩) k).val = 1 := by
      simp only [finCycle_apply, Fin.add_def]
      rw [add_mod_eq_sub_of_lt_two (by omega : 0 < c.length)
        k.isLt (by omega : 2 < c.length) (by omega)]
      omega
    apply h1k.ne
    congr 1
    exact hshift.symm
  have hkle : k.val ≤ c.length - 2 := by omega
  rcases hkle.lt_or_eq with hklt | hkeq
  · have hnowrap : k.val + 2 < c.length := by omega
    apply hasCycleLength_pred_of_shift_two_chords_nowrap hc hkpos hnowrap h0k
    simpa [finCycle_apply, Fin.add_def,
      Nat.mod_eq_of_lt hnowrap] using h1k
  · apply hasCycleLength_pred_of_chord_penultimate hc hlen
    simpa [hkeq] using h0k

lemma exists_mem_inter_of_card_lt_add
    {W : Type*} [Fintype W] [DecidableEq W] (A B : Finset W)
    (hcard : Fintype.card W < A.card + B.card) :
    ∃ x ∈ A, x ∈ B := by
  by_contra hno
  push Not at hno
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr hno
  have hsub : A ∪ B ⊆ (Finset.univ : Finset W) := by simp
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ] at hle
  omega

/-- If a Hamiltonian cycle has no cycle one shorter, the degrees of its
first two consecutive vertices sum to at most the order. -/
lemma degree_zero_add_degree_one_le_of_no_pred_cycle
    {a : V} {c : G.Walk a a} (hc : c.IsHamiltonianCycle)
    (hlen : 4 ≤ c.length) (hno : ¬ HasCycleLength G (c.length - 1)) :
    G.degree (c.getVert 0) + G.degree (c.getVert 1) ≤ c.length := by
  let A := cycleNeighborPositions (G := G) c (c.getVert 0)
  let N1 := cycleNeighborPositions (G := G) c (c.getVert 1)
  let two : Fin c.length := ⟨2, by omega⟩
  let B : Finset (Fin c.length) := N1.map (finCycle two).symm.toEmbedding
  have hAcard : A.card = G.degree (c.getVert 0) := by
    exact card_cycleNeighborPositions_eq_degree hc.isCycle
      (fun y _hy ↦ hc.mem_support y)
  have hN1card : N1.card = G.degree (c.getVert 1) := by
    exact card_cycleNeighborPositions_eq_degree hc.isCycle
      (fun y _hy ↦ hc.mem_support y)
  have hBcard : B.card = G.degree (c.getVert 1) := by
    simp [B, hN1card]
  by_contra hsum
  have hlarge : Fintype.card (Fin c.length) < A.card + B.card := by
    simpa [hAcard, hBcard] using (Nat.lt_of_not_ge hsum)
  obtain ⟨k, hkA, hkB⟩ := exists_mem_inter_of_card_lt_add A B hlarge
  obtain ⟨j, hjN, hjk⟩ := Finset.mem_map.mp hkB
  have hshift : (finCycle two) k = j := by
    calc
      (finCycle two) k = (finCycle two) ((finCycle two).symm j) :=
        congrArg (finCycle two) hjk.symm
      _ = j := (finCycle two).apply_symm_apply j
  apply hno
  apply hasCycleLength_pred_of_shift_two_chords hc.isCycle hlen
  · exact mem_cycleNeighborPositions.mp hkA
  · have hjAdj : G.Adj (c.getVert 1) (c.getVert j.val) :=
      mem_cycleNeighborPositions.mp hjN
    simpa [two, hshift] using hjAdj

/-- The same degree-sum inequality at every consecutive pair of a
Hamiltonian cycle. -/
lemma degree_add_degree_cyclic_succ_le_of_no_pred_cycle
    {a : V} {c : G.Walk a a} (hc : c.IsHamiltonianCycle)
    (hlen : 4 ≤ c.length) (hno : ¬ HasCycleLength G (c.length - 1))
    (i : Fin c.length) :
    G.degree (c.getVert i.val) +
      G.degree (c.getVert ((finCycle ⟨1, by omega⟩) i).val) ≤ c.length := by
  let cr := c.rotate (c.getVert i.val) (Walk.getVert_mem_support c i.val)
  have hcr : cr.IsHamiltonianCycle :=
    hc.rotate (Walk.getVert_mem_support c i.val)
  have hnoCr : ¬ HasCycleLength G (cr.length - 1) := by
    simpa [cr] using hno
  have hsum := degree_zero_add_degree_one_le_of_no_pred_cycle hcr
    (by simpa [cr] using hlen) hnoCr
  have hzero : cr.getVert 0 = c.getVert i.val := by
    have h := getVert_rotate_getVert_mod hc.isCycle i.isLt
      (by omega : 0 < c.length)
    simpa [cr, Nat.mod_eq_of_lt i.isLt] using h
  have hone : cr.getVert 1 =
      c.getVert ((finCycle ⟨1, by omega⟩) i).val := by
    have h := getVert_rotate_getVert_mod hc.isCycle i.isLt
      (by omega : 1 < c.length)
    simpa [cr, finCycle_apply, Fin.add_def] using h
  rw [hzero, hone] at hsum
  simpa [cr] using hsum

/-- If the `(n-1)`-cycle is absent from a Hamiltonian graph, summing the
consecutive degree inequalities gives `4e ≤ n²`. -/
lemma four_mul_card_edges_le_square_of_no_pred_cycle
    {a : V} {c : G.Walk a a} (hc : c.IsHamiltonianCycle)
    (hlen : 4 ≤ c.length) (hno : ¬ HasCycleLength G (c.length - 1)) :
    4 * G.edgeFinset.card ≤ c.length * c.length := by
  let one : Fin c.length := ⟨1, by omega⟩
  have hlocal : ∀ i : Fin c.length,
      G.degree (c.getVert i.val) +
        G.degree (c.getVert ((finCycle one) i).val) ≤ c.length := by
    intro i
    simpa [one] using
      degree_add_degree_cyclic_succ_le_of_no_pred_cycle hc hlen hno i
  have hsum :
      (∑ i : Fin c.length,
        (G.degree (c.getVert i.val) +
          G.degree (c.getVert ((finCycle one) i).val))) ≤
        ∑ _i : Fin c.length, c.length := by
    exact Finset.sum_le_sum fun i _hi ↦ hlocal i
  have hshift :
      (∑ i : Fin c.length, G.degree (c.getVert ((finCycle one) i).val)) =
        ∑ i : Fin c.length, G.degree (c.getVert i.val) := by
    exact Equiv.sum_comp (finCycle one) (fun i : Fin c.length ↦
      G.degree (c.getVert i.val))
  rw [Finset.sum_add_distrib, hshift] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have hvertexSum :
      (∑ i : Fin c.length, G.degree (c.getVert i.val)) =
        ∑ v : V, G.degree v := by
    change
      (∑ i : Fin c.length,
        G.degree (hamiltonianCycleGetVertEquiv hc i)) =
          ∑ v : V, G.degree v
    exact Equiv.sum_comp (hamiltonianCycleGetVertEquiv hc)
      (fun v : V ↦ G.degree v)
  rw [hvertexSum, G.sum_degrees_eq_twice_card_edges] at hsum
  omega

/-- The strict Bondy density inequality forces a Hamiltonian graph to
contain a cycle missing exactly one vertex. -/
lemma hasCycleLength_pred_of_hamiltonianCycle_strict_dense
    {a : V} {c : G.Walk a a} (hc : c.IsHamiltonianCycle)
    (hlen : 4 ≤ c.length)
    (hdense : c.length * c.length < 4 * G.edgeFinset.card) :
    HasCycleLength G (c.length - 1) := by
  by_contra hno
  have hle := four_mul_card_edges_le_square_of_no_pred_cycle hc hlen hno
  omega

/-- A simple cycle has exactly `length` distinct vertices. -/
lemma card_support_toFinset_of_isCycle
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have htail : c.support.tail.toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hc.support_nodup]
    rw [List.length_tail, c.length_support]
    omega
  have hbase : a ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  rw [← c.cons_tail_support, List.toFinset_cons, Finset.insert_eq_of_mem]
  · exact htail
  · simpa using hbase

/-- The length of a simple cycle is at most the order of its ambient graph. -/
lemma hasCycleLength_le_card {d : ℕ} (h : HasCycleLength G d) :
    d ≤ Fintype.card V := by
  obtain ⟨a, c, hc, rfl⟩ := h
  rw [← card_support_toFinset_of_isCycle hc]
  simpa using Finset.card_le_univ c.support.toFinset

/-- The circumference, encoded as the greatest realizable cycle length not
exceeding the order. -/
noncomputable def circumference (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (HasCycleLength G) (Fintype.card V)

lemma le_circumference_of_hasCycleLength {d : ℕ}
    (h : HasCycleLength G d) : d ≤ circumference G := by
  exact Nat.le_findGreatest (hasCycleLength_le_card h) h

lemma hasCycleLength_circumference_of_hasCycleLength {d : ℕ}
    (h : HasCycleLength G d) : HasCycleLength G (circumference G) := by
  exact Nat.findGreatest_spec (hasCycleLength_le_card h) h

/-- Cyclic neighbor positions are in bijection with the neighbors lying on
the support of the cycle. -/
lemma card_cycleNeighborPositions_eq_card_filter_support
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle) :
    (cycleNeighborPositions (G := G) c x).card =
      {y ∈ c.support.toFinset | G.Adj x y}.card := by
  apply Finset.card_bij (fun i _hi ↦ c.getVert i.val)
  · intro i hi
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨Walk.getVert_mem_support c i.val,
      mem_cycleNeighborPositions.mp hi⟩
  · intro i hi j hj hij
    apply Fin.ext
    exact hc.getVert_injOn'
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hij
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyc : y ∈ c.support := by simpa using hy'.1
    let j : Fin c.length :=
      ⟨c.support.idxOf y, support_idxOf_lt_length_of_mem_isCycle hc hyc⟩
    have hjget : c.getVert j.val = y := c.getVert_support_idxOf hyc
    have hjmem : j ∈ cycleNeighborPositions (G := G) c x := by
      exact mem_cycleNeighborPositions.mpr (by simpa [hjget] using hy'.2)
    exact ⟨j, hjmem, hjget⟩

/-- An outside vertex has at most half as many neighbors on a longest
cycle as that cycle has vertices. -/
lemma two_mul_card_cycleNeighborPositions_le_of_maximal
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hx : x ∉ c.support)
    (hmax : ∀ d, HasCycleLength G d → d ≤ c.length) :
    2 * (cycleNeighborPositions (G := G) c x).card ≤ c.length := by
  by_contra hle
  have hstrict : c.length <
      2 * (cycleNeighborPositions (G := G) c x).card := by omega
  let one : Fin c.length := ⟨1, by
    have hthree := hc.three_le_length
    omega⟩
  obtain ⟨i, hi, his⟩ := exists_mem_and_finCycle_mem
    (cycleNeighborPositions (G := G) c x) one hstrict
  have hlonger : HasCycleLength G (c.length + 1) :=
    hasCycleLength_succ_of_cycle_external_adjacent hc hx
      (mem_cycleNeighborPositions.mp hi)
      (by simpa [one] using mem_cycleNeighborPositions.mp his)
  have := hmax (c.length + 1) hlonger
  omega

/-- The number of edges crossing from a longest cycle to its complement is
at most half the product of the two side sizes. -/
lemma two_mul_card_crossing_le_of_maximal_cycle
    {a : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hmax : ∀ d, HasCycleLength G d → d ≤ c.length) :
    2 * {e ∈ c.support.toFinset ×ˢ c.support.toFinsetᶜ |
      G.Adj e.1 e.2}.card ≤
        c.length * (Fintype.card V - c.length) := by
  let S := c.support.toFinset
  let R := Sᶜ
  let Y (x : V) : Finset V := {y ∈ S | G.Adj x y}
  let pairEmbedding (x : V) : V ↪ (V × V) :=
    { toFun := fun y ↦ (y, x)
      inj' := fun _ _ h ↦ congrArg Prod.fst h }
  let T (x : V) : Finset (V × V) := (Y x).map (pairEmbedding x)
  let X : Finset (V × V) := {e ∈ S ×ˢ R | G.Adj e.1 e.2}
  have hX : X = R.biUnion T := by
    ext e
    rcases e with ⟨y, x⟩
    simp only [X, R, T, Y, pairEmbedding, Finset.mem_filter,
      Finset.mem_product, Finset.mem_compl, Finset.mem_biUnion,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hyS, hxS⟩, hyx⟩
      refine ⟨x, hxS, y, ?_, rfl⟩
      exact ⟨hyS, hyx.symm⟩
    · rintro ⟨z, hzR, w, hw, hpair⟩
      have hwz : w = y ∧ z = x := by
        exact Prod.mk.inj hpair
      rcases hwz with ⟨rfl, rfl⟩
      exact ⟨⟨hw.1, hzR⟩, hw.2.symm⟩
  have hT (x : V) : (T x).card =
      (cycleNeighborPositions (G := G) c x).card := by
    rw [show (T x).card = (Y x).card by simp [T]]
    symm
    simpa [Y, S] using card_cycleNeighborPositions_eq_card_filter_support
      (G := G) hc (x := x)
  have houtside (x : V) (hxR : x ∈ R) : x ∉ c.support := by
    simpa [R, S] using hxR
  have hcardUnion : X.card ≤ ∑ x ∈ R, (T x).card := by
    rw [hX]
    exact Finset.card_biUnion_le
  calc
    2 * X.card ≤ 2 * ∑ x ∈ R, (T x).card :=
      Nat.mul_le_mul_left 2 hcardUnion
    _ = ∑ x ∈ R, 2 * (T x).card := by
      simp [Finset.mul_sum]
    _ ≤ ∑ _x ∈ R, c.length := by
      exact Finset.sum_le_sum fun x hxR ↦ by
        rw [hT]
        exact two_mul_card_cycleNeighborPositions_le_of_maximal hc
          (houtside x hxR) hmax
    _ = R.card * c.length := by simp
    _ = c.length * (Fintype.card V - c.length) := by
      rw [Nat.mul_comm]
      congr 1
      calc
        R.card = Fintype.card V - S.card := by
          simpa [R] using Finset.card_compl S
        _ = Fintype.card V - c.length := by
          rw [show S.card = c.length by
            simpa [S] using card_support_toFinset_of_isCycle hc]

/-- A simple cycle becomes Hamiltonian after inducing on precisely its
support. -/
lemma isHamiltonianCycle_induce_support
    {a : V} {c : G.Walk a a} (hc : c.IsCycle) :
    let S := c.support.toFinset
    let W : Set V := ↑S
    let hW : ∀ y : V, y ∈ c.support → y ∈ W := fun y hy ↦ by
      simpa [W, S] using hy
    (c.induce W hW).IsHamiltonianCycle := by
  dsimp only
  let S := c.support.toFinset
  let W : Set V := ↑S
  have hW : ∀ y : V, y ∈ c.support → y ∈ W := by
    intro y hy
    simpa [W, S] using hy
  let cW := c.induce W hW
  have hcW : cW.IsCycle := by
    have hinj : Function.Injective
        (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom :=
      (SimpleGraph.Embedding.induce (G := G) (s := W)).injective
    apply (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (p := cW)
      (f := (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom)
      hinj).mp
    simpa [cW] using hc
  apply SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
  refine ⟨hcW, ?_⟩
  have hlenMap := SimpleGraph.Walk.length_map
    (p := cW)
    (f := (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom)
  have hcWlen : cW.length = c.length := by
    have hrev : c.length = cW.length := by
      simpa [cW] using hlenMap
    exact hrev.symm
  rw [hcWlen]
  symm
  calc
    Fintype.card W = S.card := by simp [W]
    _ = c.length := by
      simpa [S] using card_support_toFinset_of_isCycle hc

/-- A cycle shorter than the order omits an ambient vertex. -/
lemma exists_not_mem_support_of_cycle_length_lt_card
    {a : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hlt : c.length < Fintype.card V) :
    ∃ x : V, x ∉ c.support := by
  have hcard : c.support.toFinset.card < (Finset.univ : Finset V).card := by
    simpa [card_support_toFinset_of_isCycle hc] using hlt
  obtain ⟨x, _hxU, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨x, by simpa using hx⟩

/-- If a cycle has `n-1` vertices, every vertex other than an omitted
one lies on the cycle. -/
lemma mem_support_of_ne_of_cycle_length_pred
    {a x y : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hlen : c.length = Fintype.card V - 1)
    (hx : x ∉ c.support) (hyx : y ≠ x) :
    y ∈ c.support := by
  by_contra hy
  let S := c.support.toFinset
  have hxS : x ∉ S := by simpa [S] using hx
  have hyS : y ∉ S := by simpa [S] using hy
  have hxyS : x ∉ insert y S := by simp [hyx.symm, hxS]
  have hsub : insert x (insert y S) ⊆ (Finset.univ : Finset V) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxyS,
    Finset.card_insert_of_notMem hyS] at hcard
  have hScard : S.card = Fintype.card V - 1 := by
    simpa [S, card_support_toFinset_of_isCycle hc] using hlen
  rw [hScard, Finset.card_univ] at hcard
  have hnpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
  omega

/-- Deleting the unique vertex omitted by an `(n-1)`-cycle makes that
cycle Hamiltonian in the induced graph. -/
lemma isHamiltonianCycle_induce_compl_singleton_of_cycle_length_pred
    {a x : V} {c : G.Walk a a} (hc : c.IsCycle)
    (hlen : c.length = Fintype.card V - 1)
    (hx : x ∉ c.support) :
    let W : Set V := ({x}ᶜ : Set V)
    let hW : ∀ y : V, y ∈ c.support → y ∈ W := fun y hy ↦ by
      simpa [W] using fun hxy : y = x ↦ hx (hxy ▸ hy)
    (c.induce W hW).IsHamiltonianCycle := by
  dsimp only
  let W : Set V := ({x}ᶜ : Set V)
  have hW : ∀ y : V, y ∈ c.support → y ∈ W := by
    intro y hy
    simp only [W, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxy
    subst y
    exact hx hy
  let cW := c.induce W hW
  have hcW : cW.IsCycle := by
    have hinj : Function.Injective
        (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom := by
      exact (SimpleGraph.Embedding.induce (G := G) (s := W)).injective
    apply (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (p := cW)
      (f := (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom)
      hinj).mp
    simpa [cW] using hc
  have hcardW : Fintype.card W = Fintype.card V - 1 := by
    change Fintype.card {y : V // y ≠ x} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl]
    simp
  apply SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
  refine ⟨hcW, ?_⟩
  have hlenMap := SimpleGraph.Walk.length_map
    (p := cW)
    (f := (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom)
  have hcWlen : cW.length = c.length := by
    have hrev : c.length = cW.length := by
      simpa [cW] using hlenMap
    exact hrev.symm
  rw [hcWlen, hlen, hcardW]

/-- Strict Bondy pancyclicity in the form needed below: a Hamiltonian
graph with more than `n²/4` edges has a cycle of every length from `3`
through `n`. -/
theorem hasCycleLength_of_hamiltonian_strict_dense
    (hn : 3 ≤ Fintype.card V) (hham : G.IsHamiltonian)
    (hdense : Fintype.card V * Fintype.card V <
      4 * G.edgeFinset.card) {d : ℕ}
    (hd : 3 ≤ d) (hdn : d ≤ Fintype.card V) :
    HasCycleLength G d := by
  induction hnEq : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      have hn3 : 3 ≤ n := by omega
      obtain ⟨a, c, hc⟩ := hham (by omega)
      have hclen : c.length = n := by
        simpa [hnEq] using hc.length_eq
      by_cases hdnEq : d = n
      · exact ⟨a, c, hc.isCycle, hclen.trans hdnEq.symm⟩
      have hdnPred : d ≤ n - 1 := by omega
      have hn4 : 4 ≤ n := by omega
      have hdenseN : n * n < 4 * G.edgeFinset.card := by
        simpa [hnEq] using hdense
      have hpred : HasCycleLength G (c.length - 1) :=
        hasCycleLength_pred_of_hamiltonianCycle_strict_dense hc
          (by simpa [hclen] using hn4) (by simpa [hclen] using hdenseN)
      obtain ⟨b, q, hq, hqlen0⟩ := hpred
      have hqlen : q.length = n - 1 := by
        rw [hqlen0, hclen]
      have hqlt : q.length < Fintype.card V := by omega
      obtain ⟨x, hx⟩ :=
        exists_not_mem_support_of_cycle_length_lt_card hq hqlt
      have hall : ∀ y : V, y ≠ x → y ∈ q.support := by
        intro y hyx
        exact mem_support_of_ne_of_cycle_length_pred hq
          (by simpa [hnEq] using hqlen) hx hyx
      by_cases hxlow : 2 * G.degree x ≤ n - 1
      · let W : Set V := ({x}ᶜ : Set V)
        let H : SimpleGraph W := G.induce W
        have hcardW : Fintype.card W = n - 1 := by
          change Fintype.card {y : V // y ≠ x} = n - 1
          rw [Fintype.card_subtype_compl]
          simp [hnEq]
        have hcardW3 : 3 ≤ Fintype.card W := by omega
        have hcardWlt : Fintype.card W < n := by omega
        have hHedges : H.edgeFinset.card =
            G.edgeFinset.card - G.degree x := by
          exact (G.card_edgeFinset_induce_compl_singleton x).trans
            (G.card_edgeFinset_deleteIncidenceSet x)
        have hxEdge : G.degree x ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset x
        have hEdecomp : H.edgeFinset.card + G.degree x =
            G.edgeFinset.card := by
          rw [hHedges, Nat.sub_add_cancel hxEdge]
        have hnExpand : n * n =
            (n - 1) * (n - 1) + 2 * (n - 1) + 1 := by
          have hnSucc : n = n - 1 + 1 := by omega
          calc
            n * n = (n - 1 + 1) * (n - 1 + 1) :=
              congrArg₂ (fun r s : ℕ ↦ r * s) hnSucc hnSucc
            _ = (n - 1) * (n - 1) + 2 * (n - 1) + 1 := by ring
        have hHdense : Fintype.card W * Fintype.card W <
            4 * H.edgeFinset.card := by
          rw [hcardW]
          omega
        have hqHam :
            let hW : ∀ y : V, y ∈ q.support → y ∈ W := fun y hy ↦ by
              simpa [W] using fun hyx : y = x ↦ hx (hyx ▸ hy)
            (q.induce W hW).IsHamiltonianCycle := by
          simpa [W] using
            (isHamiltonianCycle_induce_compl_singleton_of_cycle_length_pred
              hq (by simpa [hnEq] using hqlen) hx)
        dsimp only at hqHam
        have hhamH : H.IsHamiltonian := by
          intro _hne
          exact ⟨_, _, by simpa [H] using hqHam⟩
        have hcycleH : HasCycleLength H d :=
          ih _ hcardWlt hcardW3 hhamH hHdense
            (by simpa [hcardW] using hdnPred) rfl
        exact hcycleH.map
          (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom
          (SimpleGraph.Embedding.induce (G := G) (s := W)).injective
      · apply hasCycleLength_of_external_high_degree hq hx hall
          (by omega) hd
        omega

end BondyPancyclic

section UniversalVertex

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Add one new universal vertex, represented by `none`. -/
def apexGraph : SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some u, some v => G.Adj u v
  symm := by
    constructor
    intro x y
    cases x <;> cases y <;> simp [G.adj_comm]
  loopless := by
    constructor
    intro x
    cases x <;> simp

@[simp] lemma apexGraph_adj_none_none : ¬(apexGraph G).Adj none none := by simp [apexGraph]
@[simp] lemma apexGraph_adj_none_some (v : V) :
    (apexGraph G).Adj none (some v) := by simp [apexGraph]
@[simp] lemma apexGraph_adj_some_none (v : V) :
    (apexGraph G).Adj (some v) none := by simp [apexGraph]
@[simp] lemma apexGraph_adj_some_some (u v : V) :
    (apexGraph G).Adj (some u) (some v) ↔ G.Adj u v := by simp [apexGraph]

def someEmbedding : V ↪ Option V :=
  ⟨some, Option.some_injective V⟩

lemma apexGraph_neighborFinset_none :
    (apexGraph G).neighborFinset none =
      (Finset.univ : Finset (Option V)).erase none := by
  ext z
  cases z <;> simp [SimpleGraph.mem_neighborFinset]

lemma apexGraph_neighborFinset_some (v : V) :
    (apexGraph G).neighborFinset (some v) =
      insert none ((G.neighborFinset v).map someEmbedding) := by
  ext z
  cases z with
  | none => simp [SimpleGraph.mem_neighborFinset]
  | some z => simp [SimpleGraph.mem_neighborFinset, someEmbedding]

@[simp] lemma apexGraph_degree_none :
    (apexGraph G).degree none = Fintype.card V := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    apexGraph_neighborFinset_none]
  simp

@[simp] lemma apexGraph_degree_some (v : V) :
    (apexGraph G).degree (some v) = G.degree v + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    apexGraph_neighborFinset_some]
  simp [someEmbedding, SimpleGraph.card_neighborFinset_eq_degree]

lemma apexGraph_card_edgeFinset :
    (apexGraph G).edgeFinset.card =
      G.edgeFinset.card + Fintype.card V := by
  have hsum := (apexGraph G).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option] at hsum
  simp only [apexGraph_degree_none, apexGraph_degree_some,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul, G.sum_degrees_eq_twice_card_edges] at hsum
  omega

/-- Below the apex degree, shifting the cutoff down by one identifies
the low-degree vertices before and after adjoining the apex. -/
lemma lowDegreeFinset_apexGraph (j : ℕ) (hjpos : 0 < j)
    (hjlt : j < Fintype.card V) :
    lowDegreeFinset (apexGraph G) j =
      (lowDegreeFinset G (j - 1)).map someEmbedding := by
  ext z
  cases z with
  | none => simp [lowDegreeFinset, someEmbedding, hjlt]
  | some z =>
      simp only [mem_lowDegreeFinset, apexGraph_degree_some]
      simp [someEmbedding]
      omega

lemma card_lowDegreeFinset_apexGraph (j : ℕ) (hjpos : 0 < j)
    (hjlt : j < Fintype.card V) :
    (lowDegreeFinset (apexGraph G) j).card =
      (lowDegreeFinset G (j - 1)).card := by
  rw [lowDegreeFinset_apexGraph G j hjpos hjlt, Finset.card_map]

/-- Pósa's distribution condition with `r` exceptional vertices.  At
`r = 0` this is exactly `PosaDegreeCondition`. -/
def ShiftedPosaDegreeCondition (r : ℕ) : Prop :=
  (∀ j, 2 * j < Fintype.card V - r - 1 →
      (lowDegreeFinset G j).card ≤ j + r - 1) ∧
    (∀ j, 2 * j = Fintype.card V - r - 1 →
    (lowDegreeFinset G j).card ≤ j + r)

/-- Numerical comparison used to verify the strict half of the
shifted Pósa condition from Woodall's edge threshold. -/
lemma shiftedPosa_strict_numerics {n k j : ℕ}
    (hn : 2 * k + 3 ≤ n) (hjk : k + 1 ≤ j)
    (hj : 2 * j < n - k - 1) :
    (n - (j + k)).choose 2 + (j + k) * j ≤ woodallBound n k := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le
    (show 2 * j + 1 ≤ n - k - 1 by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hjk
  have hsub0 : n - (j + k) = j + t + 2 := by omega
  have hsub1 : n - (j + k) - 1 = j + t + 1 := by omega
  have hsub2 : n - k - 1 = 2 * j + 1 + t := by omega
  have hsub3 : n - k - 1 - 1 = 2 * j + t := by omega
  have hsub4 : k + 2 - 1 = k + 1 := by omega
  have htwo :
      2 * ((n - (j + k)).choose 2 + (j + k) * j) ≤
        2 * woodallBound n k := by
    unfold woodallBound
    rw [Nat.mul_add, Nat.mul_add, two_mul_choose_two,
      two_mul_choose_two, two_mul_choose_two]
    rw [hsub1, hsub0, hsub3, hsub2, hsub4]
    nlinarith
  omega

/-- Numerical comparison used at equality in the shifted Pósa
condition. -/
lemma shiftedPosa_equal_numerics {n k j : ℕ}
    (hn : 2 * k + 3 ≤ n) (hjk : k + 1 ≤ j)
    (hj : 2 * j = n - k - 1) :
    (n - (j + k + 1)).choose 2 + (j + k + 1) * j ≤
      woodallBound n k := by
  have hsub1 : n - (j + k + 1) = j := by omega
  have hsub2 : n - k - 1 = 2 * j := by omega
  have hsub3 : n - k - 1 - 1 = 2 * j - 1 := by omega
  have hsub4 : k + 2 - 1 = k + 1 := by omega
  have hjsub : j - 1 + 1 = j := by omega
  have htwosub : 2 * j - 1 + 1 = 2 * j := by omega
  have htwo :
      2 * ((n - (j + k + 1)).choose 2 + (j + k + 1) * j) ≤
        2 * woodallBound n k := by
    unfold woodallBound
    rw [Nat.mul_add, Nat.mul_add, two_mul_choose_two,
      two_mul_choose_two, two_mul_choose_two]
    rw [hsub1, hsub3, hsub2, hsub4]
    by_cases hj1 : j = k + 1
    · subst j
      have ha : k + 1 - 1 = k := by omega
      have hb : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [ha, hb]
      ring_nf
      exact le_rfl
    by_cases hj2 : j = k + 2
    · subst j
      have ha : k + 2 - 1 = k + 1 := by omega
      have hb : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
      rw [ha, hb]
      ring_nf
      exact le_rfl
    have hj3 : k + 3 ≤ j := by omega
    nlinarith
  omega

/-- Woodall's threshold and minimum degree `k+1` force the shifted
Pósa distribution condition with `k` exceptional vertices. -/
lemma shiftedPosa_of_woodallBound_of_minDegree
    (k : ℕ) (horder : 2 * k + 3 ≤ Fintype.card V)
    (hmin : ∀ z, k + 1 ≤ G.degree z)
    (hedge : woodallBound (Fintype.card V) k + 1 ≤
      G.edgeFinset.card) :
    ShiftedPosaDegreeCondition G k := by
  constructor
  · intro j hj
    by_contra hcard
    have hjk : k + 1 ≤ j := by
      by_contra hnot
      have hjle : j ≤ k := by omega
      have hempty : lowDegreeFinset G j = ∅ := by
        ext z
        have := hmin z
        simp only [mem_lowDegreeFinset]
        simp
        omega
      rw [hempty] at hcard
      simp at hcard
    have hlarge : j + k ≤ (lowDegreeFinset G j).card := by omega
    obtain ⟨S, hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq hlarge
    have hdeg : ∀ z ∈ S, G.degree z ≤ j := by
      intro z hz
      exact mem_lowDegreeFinset.mp (hSsub hz)
    have hupper := low_degree_set_edge_bound G S j hdeg
    rw [hScard] at hupper
    have hnum := shiftedPosa_strict_numerics horder hjk hj
    omega
  · intro j hj
    by_contra hcard
    have hjk : k + 1 ≤ j := by
      by_contra hnot
      have hjle : j ≤ k := by omega
      have hempty : lowDegreeFinset G j = ∅ := by
        ext z
        have := hmin z
        simp only [mem_lowDegreeFinset]
        simp
        omega
      rw [hempty] at hcard
      simp at hcard
    have hlarge : j + k + 1 ≤ (lowDegreeFinset G j).card := by omega
    obtain ⟨S, hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq hlarge
    have hdeg : ∀ z ∈ S, G.degree z ≤ j := by
      intro z hz
      exact mem_lowDegreeFinset.mp (hSsub hz)
    have hupper := low_degree_set_edge_bound G S j hdeg
    rw [hScard] at hupper
    have hnum := shiftedPosa_equal_numerics horder hjk hj
    omega

lemma shiftedPosaDegreeCondition_zero :
    ShiftedPosaDegreeCondition G 0 ↔ PosaDegreeCondition G := by
  rfl

/-- Adding a universal vertex consumes one exceptional vertex in the
shifted Pósa condition. -/
lemma ShiftedPosaDegreeCondition.apexGraph {r : ℕ}
    (hr : 0 < r) (horder : r + 3 ≤ Fintype.card V)
    (hP : ShiftedPosaDegreeCondition G r) :
    ShiftedPosaDegreeCondition (apexGraph G) (r - 1) := by
  have hcard : Fintype.card (Option V) = Fintype.card V + 1 := by simp
  constructor
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      have hempty : lowDegreeFinset (Erdos1012.apexGraph G) 0 = ∅ := by
        ext z
        cases z <;> simp [lowDegreeFinset] <;> omega
      rw [hempty]
      simp
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjlt : j < Fintype.card V := by omega
    have hi := hP.1 (j - 1) (by omega)
    rw [card_lowDegreeFinset_apexGraph G j hjpos hjlt]
    omega
  · intro j hj
    have hjpos : 0 < j := by omega
    have hjlt : j < Fintype.card V := by omega
    have hi := hP.2 (j - 1) (by omega)
    rw [card_lowDegreeFinset_apexGraph G j hjpos hjlt]
    omega

/-- The induced subgraph of the apex graph away from the apex is the
original graph. -/
def apexInduceIso :
    (apexGraph G).induce {z : Option V | z ≠ none} ≃g G where
  toFun z := z.1.get (Option.ne_none_iff_isSome.mp z.2)
  invFun v := ⟨some v, Option.some_ne_none v⟩
  left_inv z := Subtype.ext (Option.some_get _)
  right_inv v := Option.get_some _ _
  map_rel_iff' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    cases x with
    | none => simp at hx
    | some x =>
      cases y with
      | none => simp at hy
      | some y => simp [apexGraph]

lemma length_induce_eq {X : Type*} {H : SimpleGraph X} {s : Set X}
    {u v : X} (w : H.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s) :
    (w.induce s hw).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih =>
      simp only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.length_cons]
      exact congrArg (fun n ↦ n + 1) (ih _)

/-- A cycle in the graph obtained by adjoining an apex yields a path
in the old graph after deleting at most the two cycle edges incident
with the apex. -/
lemma exists_old_path_of_apex_cycle {a : Option V}
    {c : (apexGraph G).Walk a a} (hc : c.IsCycle) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ c.length - 2 ≤ p.length := by
  have hcyclelen : 3 ≤ c.length := hc.three_le_length
  by_cases hnone : none ∈ c.support
  · let cr := c.rotate none hnone
    have hcr : cr.IsCycle := hc.rotate hnone
    let p₀ := cr.tail.dropLast
    have hp₀ : p₀.IsPath := hcr.isPath_tail.dropLast
    have htailNotNil : ¬ cr.tail.Nil := by
      apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
      simp [cr]
      omega
    have hnonep₀ : none ∉ p₀.support := by
      have hnodup := hcr.isPath_tail.support_nodup
      have hs := cr.tail.support_dropLast_concat htailNotNil
      dsimp only [p₀]
      rw [← hs] at hnodup
      exact fun h ↦ (hnodup.disjoint h (by simp))
    have hp₀len : c.length - 2 ≤ p₀.length := by
      simp [p₀, cr]
      omega
    let hstay : ∀ z ∈ p₀.support, z ∈ {z : Option V | z ≠ none} :=
      fun z hz ↦ by exact fun h ↦ hnonep₀ (h ▸ hz)
    let p₁ := p₀.induce {z : Option V | z ≠ none} hstay
    have hp₁ : p₁.IsPath := by
      apply SimpleGraph.Walk.IsPath.of_map
      have hi := SimpleGraph.Walk.map_induce (s := {z : Option V | z ≠ none}) p₀ hstay
      rw [hi]
      exact hp₀
    let p := p₁.map (apexInduceIso G).toHom
    have hp : p.IsPath := hp₁.map (apexInduceIso G).injective
    refine ⟨_, _, p, hp, ?_⟩
    have hlen : p.length = p₀.length := by
      simp only [p, SimpleGraph.Walk.length_map]
      simpa only [p₁] using length_induce_eq p₀ hstay
    omega
  · let p₀ := c.dropLast
    have hp₀ : p₀.IsPath := hc.isPath_dropLast
    have hnonep₀ : none ∉ p₀.support := by
      intro h
      apply hnone
      have hs := c.support_dropLast hc.not_nil
      rw [hs] at h
      exact List.mem_of_mem_dropLast h
    have hp₀len : c.length - 2 ≤ p₀.length := by
      simp [p₀]
      omega
    let hstay : ∀ z ∈ p₀.support, z ∈ {z : Option V | z ≠ none} :=
      fun z hz ↦ by exact fun h ↦ hnonep₀ (h ▸ hz)
    let p₁ := p₀.induce {z : Option V | z ≠ none} hstay
    have hp₁ : p₁.IsPath := by
      apply SimpleGraph.Walk.IsPath.of_map
      have hi := SimpleGraph.Walk.map_induce (s := {z : Option V | z ≠ none}) p₀ hstay
      rw [hi]
      exact hp₀
    let p := p₁.map (apexInduceIso G).toHom
    have hp : p.IsPath := hp₁.map (apexInduceIso G).injective
    refine ⟨_, _, p, hp, ?_⟩
    have hlen : p.length = p₀.length := by
      simp only [p, SimpleGraph.Walk.length_map]
      simpa only [p₁] using length_induce_eq p₀ hstay
    omega

/-- The shifted Pósa condition supplies a cycle missing at most the
`r` exceptional vertices, provided the endpoint-fan edge threshold and
minimum-degree hypotheses hold.  The induction adjoins an apex, applies
Pósa at one smaller shift, deletes the apex from the resulting cycle,
and closes the remaining long path by the endpoint-fan lemma. -/
theorem hasCycleAtLeast_of_shiftedPosa
    (r q : ℕ) (horder : r + 3 ≤ Fintype.card V)
    (hqcard : q + 1 ≤ Fintype.card V)
    (hP : ShiftedPosaDegreeCondition G r)
    (hmin : ∀ z, q ≤ G.degree z)
    (hedge : (Fintype.card V - q).choose 2 + (q + 1).choose 2 + 1 ≤
      G.edgeFinset.card) :
    HasCycleAtLeast G (Fintype.card V - r) := by
  induction r generalizing V q with
  | zero =>
      have hham : G.IsHamiltonian :=
        hamiltonian_of_posaDegreeCondition horder
          (shiftedPosaDegreeCondition_zero G |>.mp hP)
      obtain ⟨a, c, hc⟩ := hham (by omega)
      exact ⟨a, c, hc.isCycle, by simpa using hc.length_eq.ge⟩
  | succ r ih =>
      have hP' : ShiftedPosaDegreeCondition (apexGraph G) r :=
        ShiftedPosaDegreeCondition.apexGraph (G := G)
          (r := r + 1) (by omega) horder hP
      have hmin' : ∀ z, q + 1 ≤ (apexGraph G).degree z := by
        intro z
        cases z with
        | none => simpa using hqcard
        | some z =>
            simp only [apexGraph_degree_some]
            have := hmin z
            omega
      have hedge' :
          (Fintype.card (Option V) - (q + 1)).choose 2 +
              (q + 1 + 1).choose 2 + 1 ≤
            (apexGraph G).edgeFinset.card := by
        rw [apexGraph_card_edgeFinset]
        simp only [Fintype.card_option]
        rw [show Fintype.card V + 1 - (q + 1) =
          Fintype.card V - q by omega]
        rw [show q + 1 + 1 = (q + 1) + 1 by omega,
          choose_two_succ]
        omega
      have hlongA :
          HasCycleAtLeast (apexGraph G) (Fintype.card (Option V) - r) := by
        apply ih (V := Option V) (q := q + 1)
        · simp
          omega
        · simp
          omega
        · exact hP'
        · exact hmin'
        · exact hedge'
      obtain ⟨a, c, hc, hclen⟩ := hlongA
      obtain ⟨u, v, p, hp, hplen⟩ :=
        exists_old_path_of_apex_cycle G hc
      apply hasCycleAtLeast_of_minDegree_edgeCount_path
        (G := G) q (Fintype.card V - (r + 1))
      · omega
      · exact hmin
      · exact hedge
      · exact hp
      · simp only [Fintype.card_option] at hclen
        omega

end UniversalVertex

/-! ## Woodall's induction -/

section WoodallInduction

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Woodall's extremal number is strictly above the Mantel threshold.
The identity behind the inequality is
`4 * woodallBound n k + 4 - n^2 = (n - 2*k - 3)^2 + 3` in the
range `n >= 2*k+3`. -/
lemma square_lt_four_mul_woodallBound_add_one {n k : ℕ}
    (hn : 2 * k + 3 ≤ n) :
    n * n < 4 * (woodallBound n k + 1) := by
  let a := n - k - 1
  let b := k + 2
  have hab : a + b = n + 1 := by
    dsimp [a, b]
    omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hba : b ≤ a := by dsimp [a, b]; omega
  have haPred : a - 1 + 1 = a := by omega
  have hbPred : b - 1 + 1 = b := by omega
  have hchooseA : 2 * a.choose 2 = a * (a - 1) :=
    two_mul_choose_two a
  have hchooseB : 2 * b.choose 2 = b * (b - 1) :=
    two_mul_choose_two b
  have hfour : 4 * ((a.choose 2 + b.choose 2) + 1) =
      2 * (a * (a - 1) + b * (b - 1)) + 4 := by
    nlinarith
  let x := a - b
  have hax : a = b + x := by
    dsimp [x]
    omega
  have hid : 4 * ((a.choose 2 + b.choose 2) + 1) =
      n * n + x * x + 3 := by
    nlinarith
  unfold woodallBound
  change n * n < 4 * ((a.choose 2 + b.choose 2) + 1)
  omega

/-- The exact arithmetic inequality obtained by splitting the edges into
those on a long cycle, those crossing it, and those outside it. -/
lemma maximal_cycle_edge_numerics {n k c : ℕ}
    (hn : 2 * k + 3 ≤ n) (hcn : c ≤ n)
    (hlong : n - k ≤ c)
    (hdirac : min n (2 * (k + 2)) ≤ c) :
    c * c + 2 * c * (n - c) +
        2 * (n - c) * (n - c - 1) <
      4 * (woodallBound n k + 1) := by
  by_cases hnshort : n < 2 * (k + 2)
  · have hc : c = n := by
      have : n ≤ c := by simpa [Nat.min_eq_left (by omega : n ≤ 2 * (k + 2))]
        using hdirac
      omega
    subst c
    simpa using square_lt_four_mul_woodallBound_add_one hn
  · have hnlong : 2 * (k + 2) ≤ n := by omega
    have hcTwo : 2 * (k + 2) ≤ c := by
      simpa [Nat.min_eq_right hnlong] using hdirac
    let a := n - k - 1
    let b := k + 2
    let m := n - c
    let t := c - 2 * b
    have hnm : n = c + m := by dsimp [m]; omega
    have hmb : m ≤ b - 2 := by dsimp [m, b]; omega
    have hcb : 2 * b ≤ c := by simpa [b] using hcTwo
    have hct : c = 2 * b + t := by dsimp [t]; omega
    have hab : a = c + m - b + 1 := by dsimp [a, b, m]; omega
    have ha : 1 ≤ a := by dsimp [a]; omega
    have hb : 1 ≤ b := by dsimp [b]; omega
    have hchooseA : 2 * a.choose 2 = a * (a - 1) :=
      two_mul_choose_two a
    have hchooseB : 2 * b.choose 2 = b * (b - 1) :=
      two_mul_choose_two b
    have hfour : 4 * (woodallBound n k + 1) =
        2 * (a * (a - 1) + b * (b - 1)) + 4 := by
      unfold woodallBound
      change 4 * (a.choose 2 + b.choose 2 + 1) = _
      nlinarith
    have hpositive : 0 < 2 * m * t + 4 * m + t * t + 2 * t + 4 := by
      positivity
    have haPred : a - 1 + 1 = a := by omega
    have hbPred : b - 1 + 1 = b := by omega
    have haFormula : a = b + t + m + 1 := by omega
    change c * c + 2 * c * m + 2 * m * (m - 1) <
      4 * (woodallBound n k + 1)
    rw [hfour]
    by_cases hmzero : m = 0
    · simp only [hmzero, Nat.mul_zero, Nat.zero_sub,
        Nat.add_zero]
      nlinarith
    · have hmPred : m - 1 + 1 = m := by omega
      have haSub : a - 1 = b + t + m := by omega
      have hid :
          2 * (a * (a - 1) + b * (b - 1)) + 4 =
            c * c + 2 * c * m + 2 * m * (m - 1) +
              (2 * m * t + 4 * m + t * t + 2 * t + 4) := by
        rw [haSub, haFormula, hct]
        nlinarith only [hbPred, hmPred]
      rw [hid]
      omega

/-- The high-minimum-degree branch of Woodall's theorem.  A longest cycle
has both the shifted-Pósa lower bound and the Dirac-type lower bound above;
if a requested shorter length were missing, Hamiltonian pancyclicity on the
cycle support and the exact three-part edge decomposition would contradict
Woodall's threshold. -/
theorem hasCycleLength_of_woodall_high_minDegree
    (k : ℕ) (horder : 2 * k + 3 ≤ Fintype.card V)
    (hconn : G.Connected) (hmin : ∀ z, k + 2 ≤ G.degree z)
    (hedge : woodallBound (Fintype.card V) k + 1 ≤
      G.edgeFinset.card)
    (hlong : HasCycleAtLeast G (Fintype.card V - k))
    {d : ℕ} (hd : 3 ≤ d) (hdn : d ≤ Fintype.card V - k) :
    HasCycleLength G d := by
  by_contra hno
  obtain ⟨a₀, c₀, hc₀, hc₀len⟩ := hlong
  have hc₀exact : HasCycleLength G c₀.length := ⟨a₀, c₀, hc₀, rfl⟩
  have hcirc : HasCycleLength G (circumference G) :=
    hasCycleLength_circumference_of_hasCycleLength hc₀exact
  obtain ⟨a, c, hc, hclen⟩ := hcirc
  have hmax : ∀ e, HasCycleLength G e → e ≤ c.length := by
    intro e he
    rw [hclen]
    exact le_circumference_of_hasCycleLength he
  have hlongC : Fintype.card V - k ≤ c.length := by
    calc
      Fintype.card V - k ≤ c₀.length := hc₀len
      _ ≤ c.length := hmax c₀.length hc₀exact
  have hdirac := hasCycleAtLeast_min_card_twice_shift_of_woodall
    (G := G) k (by omega) hconn hmin hedge
  obtain ⟨a₁, c₁, hc₁, hc₁len⟩ := hdirac
  have hc₁exact : HasCycleLength G c₁.length := ⟨a₁, c₁, hc₁, rfl⟩
  have hdiracC : min (Fintype.card V) (2 * (k + 2)) ≤ c.length :=
    hc₁len.trans (hmax c₁.length hc₁exact)
  have hcExact : HasCycleLength G c.length := ⟨a, c, hc, rfl⟩
  have hcCard : c.length ≤ Fintype.card V := hasCycleLength_le_card hcExact
  let S := c.support.toFinset
  let W : Set V := ↑S
  let H : SimpleGraph W := G.induce W
  have hW : ∀ y : V, y ∈ c.support → y ∈ W := by
    intro y hy
    simpa [W, S] using hy
  let cW := c.induce W hW
  have hcW : cW.IsHamiltonianCycle := by
    simpa [S, W, cW, hW] using isHamiltonianCycle_induce_support hc
  have hcardW : Fintype.card W = c.length := by
    calc
      Fintype.card W = S.card := by simp [W]
      _ = c.length := by
        simpa [S] using card_support_toFinset_of_isCycle hc
  have hhamH : H.IsHamiltonian := by
    intro _hne
    exact ⟨_, cW, by simpa [H] using hcW⟩
  have hHupper : 4 * H.edgeFinset.card ≤ c.length * c.length := by
    by_contra hupper
    have hHdense : Fintype.card W * Fintype.card W <
        4 * H.edgeFinset.card := by
      rw [hcardW]
      omega
    have hcycleH : HasCycleLength H d :=
      hasCycleLength_of_hamiltonian_strict_dense
        (G := H) (by rw [hcardW]; omega) hhamH hHdense hd
        (by rw [hcardW]; exact hdn.trans hlongC)
    have hcycleG := hcycleH.map
      (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom
      (SimpleGraph.Embedding.induce (G := G) (s := W)).injective
    exact hno hcycleG
  let R := Sᶜ
  let X : Finset (V × V) := {e ∈ S ×ˢ R | G.Adj e.1 e.2}
  let K : SimpleGraph (↑R : Set V) := G.induce (↑R : Set V)
  have hcross : 2 * X.card ≤
      c.length * (Fintype.card V - c.length) := by
    simpa [X, R, S] using
      two_mul_card_crossing_le_of_maximal_cycle (G := G) hc hmax
  have hcardR : Fintype.card (↑R : Set V) =
      Fintype.card V - c.length := by
    calc
      Fintype.card (↑R : Set V) = R.card := by simp
      _ = Fintype.card V - S.card := by
        simpa [R] using Finset.card_compl S
      _ = Fintype.card V - c.length := by
        rw [show S.card = c.length by
          simpa [S] using card_support_toFinset_of_isCycle hc]
  have hKchoose : K.edgeFinset.card ≤
      (Fintype.card V - c.length).choose 2 := by
    rw [← hcardR]
    exact SimpleGraph.card_edgeFinset_le_card_choose_two
  have hKupper : 2 * K.edgeFinset.card ≤
      (Fintype.card V - c.length) *
        (Fintype.card V - c.length - 1) := by
    have hchoose := two_mul_choose_two (Fintype.card V - c.length)
    nlinarith
  have hdecomp := card_edgeFinset_decomp_finset G S
  change G.edgeFinset.card = H.edgeFinset.card + X.card + K.edgeFinset.card
    at hdecomp
  have hedgeUpper : 4 * G.edgeFinset.card ≤
      c.length * c.length +
        2 * c.length * (Fintype.card V - c.length) +
        2 * (Fintype.card V - c.length) *
          (Fintype.card V - c.length - 1) := by
    nlinarith
  have hnumeric := maximal_cycle_edge_numerics horder hcCard hlongC hdiracC
  have hlower := Nat.mul_le_mul_left 4 hedge
  omega

/-- Woodall's theorem on an arbitrary finite vertex type.  The proof is by
low-degree deletion; in the remaining branch, shifted Pósa gives the target
long cycle and `hasCycleLength_of_woodall_high_minDegree` supplies all its
shorter lengths. -/
theorem woodall_finite_type :
    ∀ (k : ℕ), 2 * k + 3 ≤ Fintype.card V →
      woodallBound (Fintype.card V) k + 1 ≤ G.edgeFinset.card →
      ∀ d, 3 ≤ d → d ≤ Fintype.card V - k →
        HasCycleLength G d := by
  intro k
  induction k generalizing V with
  | zero =>
      intro horder hedge d hd hdn
      have hmin : ∀ z, 1 ≤ G.degree z := by
        intro z
        by_contra hz
        have hzle : G.degree z ≤ 0 := by omega
        let S : Finset V := {z}
        have hupper := low_degree_set_edge_bound G S 0 (by
          intro w hw
          have hwz : w = z := by simpa [S] using hw
          subst w
          exact hzle)
        have hcard : S.card = 1 := by simp [S]
        rw [hcard] at hupper
        simp only [Nat.one_mul, Nat.add_zero] at hupper
        change (Fintype.card V - 1).choose 2 + 1 + 1 ≤
          G.edgeFinset.card at hedge
        omega
      have hP := shiftedPosa_of_woodallBound_of_minDegree
        (G := G) 0 horder (by simpa using hmin) hedge
      have hham : G.IsHamiltonian :=
        hamiltonian_of_posaDegreeCondition horder
          (shiftedPosaDegreeCondition_zero G |>.mp hP)
      apply hasCycleLength_of_hamiltonian_strict_dense horder hham
      · exact (square_lt_four_mul_woodallBound_add_one horder).trans_le
          (Nat.mul_le_mul_left 4 hedge)
      · exact hd
      · simpa using hdn
  | succ k ih =>
      intro horder hedge d hd hdn
      by_cases hlow : ∃ z : V, G.degree z ≤ k + 2
      · obtain ⟨z, hz⟩ := hlow
        let W : Set V := {w : V | w ≠ z}
        let H : SimpleGraph W := G.induce W
        have hcardW : Fintype.card W = Fintype.card V - 1 := by
          change Fintype.card {w : V // w ≠ z} = Fintype.card V - 1
          rw [Fintype.card_subtype_compl]
          simp
        have horderH : 2 * k + 3 ≤ Fintype.card W := by
          rw [hcardW]
          omega
        have hHedges : H.edgeFinset.card =
            G.edgeFinset.card - G.degree z := by
          exact (G.card_edgeFinset_induce_compl_singleton z).trans
            (G.card_edgeFinset_deleteIncidenceSet z)
        have hzEdge : G.degree z ≤ G.edgeFinset.card :=
          G.degree_le_card_edgeFinset z
        have hstep : woodallBound (Fintype.card V) (k + 1) - (k + 2) =
            woodallBound (Fintype.card V - 1) k := by
          simpa using woodallBound_delete_step
            (n := Fintype.card V) (k := k + 1) (by omega) (by omega)
        have hkBound : k + 2 ≤ woodallBound (Fintype.card V) (k + 1) := by
          unfold woodallBound
          rw [show k + 1 + 2 = (k + 2) + 1 by omega,
            choose_two_succ]
          omega
        have hstepAdd : woodallBound (Fintype.card V - 1) k + (k + 2) =
            woodallBound (Fintype.card V) (k + 1) := by
          omega
        have hedgeH : woodallBound (Fintype.card W) k + 1 ≤
            H.edgeFinset.card := by
          rw [hcardW, hHedges]
          omega
        have hdnH : d ≤ Fintype.card W - k := by
          rw [hcardW]
          omega
        have hcycleH : HasCycleLength H d :=
          ih horderH hedgeH d hd hdnH
        exact hcycleH.map
          (SimpleGraph.Embedding.induce (G := G) (s := W)).toHom
          (SimpleGraph.Embedding.induce (G := G) (s := W)).injective
      ·
        have hmin : ∀ z, k + 3 ≤ G.degree z := by
          intro z
          have hznot : ¬ G.degree z ≤ k + 2 := by
            intro hz
            exact hlow ⟨z, hz⟩
          omega
        have hP := shiftedPosa_of_woodallBound_of_minDegree
          (G := G) (k + 1) horder (by
            intro z
            have := hmin z
            omega) hedge
        have hlong : HasCycleAtLeast G (Fintype.card V - (k + 1)) := by
          apply hasCycleAtLeast_of_shiftedPosa (G := G) (k + 1) (k + 2)
          · omega
          · have := G.degree_lt_card_verts (Classical.choice
                (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)))
            omega
          · exact hP
          · intro z
            exact (by have := hmin z; omega)
          · unfold woodallBound at hedge
            rw [show Fintype.card V - (k + 1) - 1 =
                Fintype.card V - (k + 2) by omega,
              show k + 1 + 2 = k + 2 + 1 by omega] at hedge
            exact hedge
        have htwo : VertexTwoConnected G := by
          apply vertexTwoConnected_of_woodallBound_of_minDegree
            G (k + 1) horder
          · intro z
            have := hmin z
            omega
          · simpa [Nat.succ_eq_add_one] using hedge
        exact hasCycleLength_of_woodall_high_minDegree
          (G := G) (k + 1) horder htwo.1
          (by simpa [Nat.add_assoc] using hmin) hedge hlong hd hdn

/-- Woodall's 1972 theorem in the problem's concrete `Fin n` model. -/
theorem woodall {n k : ℕ} (horder : 2 * k + 3 ≤ n)
    (G : SimpleGraph (Fin n))
    (hedge : woodallBound n k + 1 ≤ G.edgeFinset.card) :
    ∀ d, 3 ≤ d → d ≤ n - k → HasCycleLength G d := by
  simpa using woodall_finite_type (G := G) k (by simpa using horder)
    (by simpa using hedge)

/-- The complete resolution of Erdős Problem 1012: `2k+3` is a valid
eventual cutoff, and in fact every cycle length through `n-k` occurs. -/
theorem erdos_1012 : ∀ k : ℕ, ValidCutoff k (2 * k + 3) := by
  intro k n hn
  intro G hedge d hd hdn
  exact woodall hn G hedge d hd hdn

end WoodallInduction

end Erdos1012

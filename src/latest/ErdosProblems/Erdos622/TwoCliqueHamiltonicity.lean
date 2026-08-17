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
import Mathlib
import ErdosProblems.Erdos622.Hamiltonicity
import ErdosProblems.Erdos622.External.Erdos570.BondyChvatal
import ErdosProblems.Erdos58.Structural.SpliceConstruction

/-!
# Hamiltonicity in the almost-two-cliques case

This file proves the deterministic lemma used in the almost-two-cliques
branch of the Draganić--Keevash--Müyesser argument.  The useful input on
each part is exactly what survives a random restriction: a linear minimum
degree and a quadratic upper bound on the number of missing internal edges.

The proof is a short closure argument.  If the Bondy--Chvátal closure of a
graph with minimum degree `δ` is not complete, a nonedge `uv` of closure
degrees `d` and at most `N-d` forces at least
`(δ-1)(N-δ-1)/2` missing edges in the original graph.  To prescribe the
ends of the Hamilton path we add one new vertex adjacent only to those ends.
Once the old vertices form a clique in the closure, the new vertex also
closes up, and deleting it from a Hamilton cycle gives the required path.
-/

open Finset Set
open scoped SimpleGraph

namespace Erdos622.TwoCliqueHamiltonicity

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Cycle splicing across the two parts -/

/-- A path traverses a part exactly when it is simple and its support is
that part. -/
private def IsHamiltonPathOn {G : SimpleGraph V}
    (A : Set V) {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ v, v ∈ p.support ↔ v ∈ A

private lemma IsHamiltonPathOn.length_add_one_eq_ncard
    {G : SimpleGraph V} {A : Set V} {a b : V} {p : G.Walk a b}
    (hp : IsHamiltonPathOn A p) :
    p.length + 1 = A.ncard := by
  have hs : {v : V | v ∈ p.support} = A := Set.ext fun v ↦ hp.2 v
  rw [← hs, Set.ncard_eq_toFinset_card']
  have hfin : ({v : V | v ∈ p.support} : Set V).toFinset =
      p.support.toFinset := by
    ext v
    simp
  rw [hfin, List.toFinset_card_of_nodup hp.1.support_nodup]
  exact (SimpleGraph.Walk.length_support p).symm

/-- Two disjoint cross edges close Hamilton paths through two disjoint parts
to a Hamilton cycle. -/
private theorem isHamiltonian_of_two_cross_edges
    {G : SimpleGraph V}
    (A B : Set V) (hAB : Disjoint A B) (hcover : A ∪ B = Set.univ)
    {a₁ a₂ b₁ b₂ : V}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (hab₁ : G.Adj a₁ b₁) (hab₂ : G.Adj a₂ b₂)
    {c : G.Walk a₁ a₂} (hc : IsHamiltonPathOn A c)
    {d : G.Walk b₁ b₂} (hd : IsHamiltonPathOn B d) :
    G.IsHamiltonian := by
  let L : Erdos58.TwoLinkage G A B :=
    { a₁ := a₁
      a₂ := a₂
      b₁ := b₁
      b₂ := b₂
      p := hab₁.toWalk
      q := hab₂.toWalk
      p_isPath := hab₁.isPath_toWalk
      q_isPath := hab₂.isPath_toWalk
      a₁_mem := ha₁
      a₂_mem := ha₂
      b₁_mem := hb₁
      b₂_mem := hb₂
      disjoint_support := by
        rw [SimpleGraph.Adj.support_toWalk, SimpleGraph.Adj.support_toWalk,
          List.disjoint_left]
        intro x hxP hxQ
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxP hxQ
        rcases hxP with rfl | rfl <;> rcases hxQ with rfl | rfl
        · exact ha rfl
        · exact Set.disjoint_left.1 hAB ha₁ hb₂
        · exact Set.disjoint_left.1 hAB ha₂ hb₁
        · exact hb rfl
      p_interior := by simp [SimpleGraph.Adj.support_toWalk]
      q_interior := by simp [SimpleGraph.Adj.support_toWalk] }
  let w : G.Walk a₁ a₁ := Erdos58.SpliceData.close L.p d L.q c
  have hwCycle : w.IsCycle := by
    exact Erdos58.Structural.linkage_close_isCycle L hAB c d hc.1 hd.1
      (fun x hx ↦ (hc.2 x).mp hx) (fun x hx ↦ (hd.2 x).mp hx)
  have hcard : Fintype.card V = A.ncard + B.ncard := by
    calc
      Fintype.card V = (Set.univ : Set V).ncard := by simp
      _ = (A ∪ B).ncard := by rw [hcover]
      _ = A.ncard + B.ncard := Set.ncard_union_eq hAB
  have hcLen := hc.length_add_one_eq_ncard
  have hdLen := hd.length_add_one_eq_ncard
  have hpLen : L.p.length = 1 := by simp [L]
  have hqLen : L.q.length = 1 := by simp [L]
  intro _
  refine ⟨a₁, w, (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq).2
    ⟨hwCycle, ?_⟩⟩
  simp only [w, Erdos58.SpliceData.length_close]
  rw [hpLen, hqLen, hcard]
  omega

/-! ## The endpoint augmentation -/

/-- Add one fresh vertex, adjacent precisely to `a` and `b`.  A Hamilton
cycle in this augmentation cuts open to a Hamilton `a`--`b` path. -/
def endpointAugment (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some u, some v => G.Adj u v
    | none, some v => v = a ∨ v = b
    | some u, none => u = a ∨ u = b
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x with
    | none =>
        cases y with
        | none => exact h
        | some y => exact h
    | some x =>
        cases y with
        | none => exact h
        | some y => exact (G.adj_comm x y).mp h⟩
  loopless := ⟨by
    intro x h
    cases x with
    | none => exact h
    | some x => exact G.loopless.irrefl x h⟩

@[simp] lemma endpointAugment_adj_some_some
    (G : SimpleGraph V) (a b u v : V) :
    (endpointAugment G a b).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma endpointAugment_adj_none_some
    (G : SimpleGraph V) (a b v : V) :
    (endpointAugment G a b).Adj none (some v) ↔ v = a ∨ v = b := Iff.rfl

@[simp] lemma endpointAugment_adj_some_none
    (G : SimpleGraph V) (a b u : V) :
    (endpointAugment G a b).Adj (some u) none ↔ u = a ∨ u = b := Iff.rfl

@[simp] lemma endpointAugment_not_adj_none_none
    (G : SimpleGraph V) (a b : V) :
    ¬(endpointAugment G a b).Adj none none := by simp [endpointAugment]

/-- The canonical embedding of the old graph into the endpoint
augmentation. -/
def endpointAugmentEmbedding (G : SimpleGraph V) (a b : V) :
    G ↪g endpointAugment G a b where
  toFun := some
  inj' := Option.some_injective V
  map_rel_iff' := Iff.rfl

private lemma degree_le_degree_option_of_old_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : SimpleGraph (Option V)) [DecidableRel K.Adj]
    (hGK : ∀ {u v : V}, G.Adj u v → K.Adj (some u) (some v)) (u : V) :
    G.degree u ≤ K.degree (some u) := by
  let e : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have hsub : (G.neighborFinset u).map e ⊆ K.neighborFinset (some u) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact (K.mem_neighborFinset (some u) (some w)).mpr
      (hGK ((G.mem_neighborFinset u w).mp hw))
  have hcard := Finset.card_le_card hsub
  simpa [SimpleGraph.card_neighborFinset_eq_degree] using hcard

/-! ## Sparse complement forces the old closure to be complete -/

/-- The counting heart of the proof.  The graph `K` is intended to be the
closure of an endpoint augmentation.  Its closure property uses the order
`N+1`, while the missing-edge count and minimum degree concern the old graph
`G` on `N` vertices. -/
private theorem old_complete_of_closed_sparse
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : SimpleGraph (Option V)) [DecidableRel K.Adj]
    (hGK : ∀ {u v : V}, G.Adj u v → K.Adj (some u) (some v))
    (hclosed : ∀ {x y : Option V}, x ≠ y →
      Fintype.card (Option V) ≤ K.degree x + K.degree y → K.Adj x y)
    (δ M : ℕ) (hδtwo : 2 ≤ δ) (hδcard : 2 * δ ≤ Fintype.card V)
    (hmindeg : ∀ v : V, δ ≤ G.degree v)
    (hmissing : Gᶜ.edgeFinset.card ≤ M)
    (hsparse : 2 * M < (δ - 1) * (Fintype.card V - δ - 1)) :
    ∀ {u v : V}, u ≠ v → K.Adj (some u) (some v) := by
  intro u v huv
  by_contra huvK
  let N := Fintype.card V
  let d := K.degree (some u)
  have hdu : δ ≤ d :=
    (hmindeg u).trans (degree_le_degree_option_of_old_edges G K hGK u)
  have hdv : δ ≤ K.degree (some v) :=
    (hmindeg v).trans (degree_le_degree_option_of_old_edges G K hGK v)
  have hsumlt : d + K.degree (some v) < N + 1 := by
    have hne : (some u : Option V) ≠ some v := fun h ↦ huv (Option.some.inj h)
    have hnge : ¬(Fintype.card (Option V) ≤
        K.degree (some u) + K.degree (some v)) := fun h ↦
      huvK (hclosed hne h)
    simpa [N, d] using (Nat.lt_of_not_ge hnge)
  have hdle : d ≤ N - δ := by omega

  let R : Finset V :=
    (Finset.univ.erase u).filter fun w ↦ K.Adj (some u) (some w)
  let Q : Finset V :=
    (Finset.univ.erase u).filter fun w ↦ ¬K.Adj (some u) (some w)
  have hpart : R.card + Q.card = N - 1 := by
    have hunion : R ∪ Q = Finset.univ.erase u := by
      ext w
      simp only [R, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_erase,
        Finset.mem_univ, and_true]
      tauto
    have hdisj : Disjoint R Q := by
      rw [Finset.disjoint_left]
      intro w hwR hwQ
      exact (Finset.mem_filter.mp hwQ).2 (Finset.mem_filter.mp hwR).2
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
  have hRle : R.card ≤ d := by
    let e : V ↪ Option V := ⟨some, Option.some_injective V⟩
    have hsub : R.map e ⊆ K.neighborFinset (some u) := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
      exact (K.mem_neighborFinset (some u) (some w)).mpr
        (Finset.mem_filter.mp hw).2
    have hc := Finset.card_le_card hsub
    simpa [d, SimpleGraph.card_neighborFinset_eq_degree] using hc
  have hQcard : N - 1 - d ≤ Q.card := by omega

  have hQdegree : ∀ w ∈ Q, d - 1 ≤ Gᶜ.degree w := by
    intro w hwQ
    have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_filter.mp hwQ).1).1
    have hnon : ¬K.Adj (some u) (some w) := (Finset.mem_filter.mp hwQ).2
    have hne : (some u : Option V) ≠ some w := fun h ↦ hwu (Option.some.inj h).symm
    have hsumw : d + K.degree (some w) < N + 1 := by
      have hnge : ¬(Fintype.card (Option V) ≤
          K.degree (some u) + K.degree (some w)) := fun h ↦
        hnon (hclosed hne h)
      simpa [N, d] using (Nat.lt_of_not_ge hnge)
    have hGwK : G.degree w ≤ K.degree (some w) :=
      degree_le_degree_option_of_old_edges G K hGK w
    have hcompl := G.degree_compl (v := w)
    have hdeglt := G.degree_lt_card_verts w
    omega
  have hsumQ : Q.card * (d - 1) ≤ ∑ w ∈ Q, Gᶜ.degree w := by
    calc
      Q.card * (d - 1) = ∑ _w ∈ Q, (d - 1) := by simp
      _ ≤ ∑ w ∈ Q, Gᶜ.degree w := by
        exact Finset.sum_le_sum fun w hw ↦ hQdegree w hw
  have hsumAll : (∑ w ∈ Q, Gᶜ.degree w) ≤ ∑ w : V, Gᶜ.degree w := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q)
      (fun _ _ _ ↦ Nat.zero_le _)
  have htotal : (∑ w : V, Gᶜ.degree w) = 2 * Gᶜ.edgeFinset.card := by
    simpa using Gᶜ.sum_degrees_eq_twice_card_edges
  have hprodUpper : (N - 1 - d) * (d - 1) ≤ 2 * M := by
    calc
      (N - 1 - d) * (d - 1) ≤ Q.card * (d - 1) :=
        Nat.mul_le_mul_right (d - 1) hQcard
      _ ≤ ∑ w ∈ Q, Gᶜ.degree w := hsumQ
      _ ≤ ∑ w : V, Gᶜ.degree w := hsumAll
      _ = 2 * Gᶜ.edgeFinset.card := htotal
      _ ≤ 2 * M := Nat.mul_le_mul_left 2 hmissing
  have hprodLower : (δ - 1) * (N - δ - 1) ≤
      (N - 1 - d) * (d - 1) := by
    let A := δ - 1
    let X := d - δ
    let Y := N - d - δ
    have hdForm : d - 1 = A + X := by dsimp [A, X]; omega
    have hleftForm : N - 1 - d = A + Y := by dsimp [A, Y]; omega
    have htargetForm : N - δ - 1 = A + X + Y := by
      dsimp [A, X, Y]
      omega
    rw [hdForm, hleftForm, htargetForm]
    nlinarith [Nat.zero_le (X * Y)]
  have := hsparse
  dsimp only [N] at this hprodLower hprodUpper
  omega

/-! ## From closure completion to a prescribed Hamilton path -/

private theorem endpointAugment_closure_eq_top
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : a ≠ b)
    (δ M : ℕ) (hδtwo : 2 ≤ δ) (hδcard : 2 * δ ≤ Fintype.card V)
    (hmindeg : ∀ v : V, δ ≤ G.degree v)
    (hmissing : Gᶜ.edgeFinset.card ≤ M)
    (hsparse : 2 * M < (δ - 1) * (Fintype.card V - δ - 1)) :
    (endpointAugment G a b).closure = ⊤ := by
  let J := endpointAugment G a b
  let K := J.closure
  have hGK : ∀ {u v : V}, G.Adj u v → K.Adj (some u) (some v) := by
    intro u v huv
    exact SimpleGraph.self_le_closure J huv
  have hold : ∀ {u v : V}, u ≠ v → K.Adj (some u) (some v) :=
    old_complete_of_closed_sparse G K hGK
      (fun hne hdeg ↦ SimpleGraph.closure_spec J hne hdeg)
      δ M hδtwo hδcard hmindeg hmissing hsparse
  rw [eq_top_iff]
  intro x y hxy
  simp only [SimpleGraph.top_adj, ne_eq] at hxy
  change K.Adj x y
  cases x with
  | none =>
      cases y with
      | none => exact (hxy rfl).elim
      | some v =>
          by_cases hnv : K.Adj none (some v)
          · exact hnv
          · apply SimpleGraph.closure_spec J hxy
            have hnone : 2 ≤ K.degree none := by
              have hsub : ({some a, some b} : Finset (Option V)) ⊆ K.neighborFinset none := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl
                · exact (K.mem_neighborFinset none (some a)).mpr
                    (SimpleGraph.self_le_closure J (by simp [J, endpointAugment]))
                · exact (K.mem_neighborFinset none (some b)).mpr
                    (SimpleGraph.self_le_closure J (by simp [J, endpointAugment]))
              have hc := Finset.card_le_card hsub
              have hcardPair : ({some a, some b} : Finset (Option V)).card = 2 := by
                simp [hab]
              simpa [hcardPair, SimpleGraph.card_neighborFinset_eq_degree] using hc
            have hv : Fintype.card V - 1 ≤ K.degree (some v) := by
              let e : V ↪ Option V := ⟨some, Option.some_injective V⟩
              have hsub : ((Finset.univ.erase v).map e) ⊆
                  K.neighborFinset (some v) := by
                intro z hz
                obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
                exact (K.mem_neighborFinset (some v) (some w)).mpr
                  (hold (Finset.mem_erase.mp hw).1.symm)
              have hc := Finset.card_le_card hsub
              simpa [SimpleGraph.card_neighborFinset_eq_degree] using hc
            change Fintype.card (Option V) ≤ K.degree none + K.degree (some v)
            simp only [Fintype.card_option]
            omega
  | some u =>
      cases y with
      | none =>
          exact (K.adj_comm none (some u)).mp (by
            have hne : (none : Option V) ≠ some u := by simp
            have := (show K.Adj none (some u) from by
              by_cases h : K.Adj none (some u)
              · exact h
              · apply SimpleGraph.closure_spec J hne
                have hnone : 2 ≤ K.degree none := by
                  have hsub : ({some a, some b} : Finset (Option V)) ⊆
                      K.neighborFinset none := by
                    intro z hz
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                    rcases hz with rfl | rfl
                    · exact (K.mem_neighborFinset none (some a)).mpr
                        (SimpleGraph.self_le_closure J (by simp [J, endpointAugment]))
                    · exact (K.mem_neighborFinset none (some b)).mpr
                        (SimpleGraph.self_le_closure J (by simp [J, endpointAugment]))
                  have hc := Finset.card_le_card hsub
                  have hp : ({some a, some b} : Finset (Option V)).card = 2 := by
                    simp [hab]
                  simpa [hp, SimpleGraph.card_neighborFinset_eq_degree] using hc
                have hu : Fintype.card V - 1 ≤ K.degree (some u) := by
                  let e : V ↪ Option V := ⟨some, Option.some_injective V⟩
                  have hsub : ((Finset.univ.erase u).map e) ⊆
                      K.neighborFinset (some u) := by
                    intro z hz
                    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
                    exact (K.mem_neighborFinset (some u) (some w)).mpr
                      (hold (Finset.mem_erase.mp hw).1.symm)
                  have hc := Finset.card_le_card hsub
                  simpa [SimpleGraph.card_neighborFinset_eq_degree] using hc
                change Fintype.card (Option V) ≤ K.degree none + K.degree (some u)
                simp only [Fintype.card_option]
                omega)
            exact this)
      | some v => exact hold (fun h ↦ hxy (congrArg some h))

private theorem top_option_isHamiltonian
    (hV : 2 ≤ Fintype.card V) :
    (⊤ : SimpleGraph (Option V)).IsHamiltonian := by
  apply SimpleGraph.dirac_theorem
  · simp only [Fintype.card_option]
    omega
  · intro x
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hnf : (⊤ : SimpleGraph (Option V)).neighborFinset x = {x}ᶜ := by
      ext y
      simp
    rw [hnf, Finset.card_compl]
    simp only [Fintype.card_option, Finset.card_singleton]
    omega

private theorem endpointAugment_isHamiltonian
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : a ≠ b)
    (δ M : ℕ) (hδtwo : 2 ≤ δ) (hδcard : 2 * δ ≤ Fintype.card V)
    (hmindeg : ∀ v : V, δ ≤ G.degree v)
    (hmissing : Gᶜ.edgeFinset.card ≤ M)
    (hsparse : 2 * M < (δ - 1) * (Fintype.card V - δ - 1)) :
    (endpointAugment G a b).IsHamiltonian := by
  let J := endpointAugment G a b
  have htop : J.closure = (⊤ : SimpleGraph (Option V)) :=
    endpointAugment_closure_eq_top G hab δ M hδtwo hδcard hmindeg hmissing hsparse
  apply SimpleGraph.from_closure_iff.mp
  rw [htop]
  apply top_option_isHamiltonian
  omega

private theorem exists_old_preimage {G : SimpleGraph V} {a b x y : V}
    (p : (endpointAugment G a b).Walk (some x) (some y))
    (hold : ∀ z ∈ p.support, z ∈ Set.range (some : V → Option V)) :
    ∃ q : G.Walk x y, q.map (endpointAugmentEmbedding G a b).toHom = p := by
  let e := endpointAugmentEmbedding G a b
  have hold' : ∀ z ∈ p.support, z ∈ Set.range e := by
    intro z hz
    obtain ⟨v, rfl⟩ := hold z hz
    exact ⟨v, rfl⟩
  let p' := p.induce (Set.range e) hold'
  let q₀ := p'.map e.isoInduceRange.symm.toHom
  have hqx : e.isoInduceRange.symm
      ⟨some x, Set.mem_range_self x⟩ = x := e.isoInduceRange.symm_apply_apply x
  have hqy : e.isoInduceRange.symm
      ⟨some y, Set.mem_range_self y⟩ = y := e.isoInduceRange.symm_apply_apply y
  let q : G.Walk x y := q₀.copy hqx hqy
  refine ⟨q, ?_⟩
  apply SimpleGraph.Walk.ext_support
  calc
    (q.map e.toHom).support = (q₀.map e.toHom).support := by simp [q, e]
    _ = p.support := by
      simp only [q₀, SimpleGraph.Walk.support_map, List.map_map]
      change List.map (fun z : Set.range e ↦ e (e.isoInduceRange.symm z))
          p'.support = p.support
      have hfun : (fun z : Set.range e ↦ e (e.isoInduceRange.symm z)) =
          (fun z : Set.range e ↦ (z : Option V)) := by
        funext z
        exact congrArg Subtype.val (e.isoInduceRange.apply_symm_apply z)
      rw [hfun]
      change ((p.induce (Set.range e) hold').support.map Subtype.val) = p.support
      rw [SimpleGraph.Walk.support_induce]
      exact List.attachWith_map_subtype_val hold'

private theorem hamiltonPath_of_endpointAugment_isHamiltonian
    (G : SimpleGraph V) {a b : V} (hab : a ≠ b)
    (hHam : (endpointAugment G a b).IsHamiltonian) :
    ∃ p : G.Walk a b, p.IsHamiltonian := by
  let J := endpointAugment G a b
  letI : Nonempty V := ⟨a⟩
  letI : Nontrivial (Option V) := ⟨none, some a, by simp⟩
  have hcard : Fintype.card (Option V) ≠ 1 := by
    simp only [Fintype.card_option]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a⟩
    omega
  obtain ⟨q, hq⟩ := hHam.exists_isHamiltonianCycle (none : Option V)
  have hqNonNil : ¬q.Nil := hq.isCycle.not_nil
  have htailNonNil : ¬q.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have hthree := hq.isCycle.three_le_length
    simp only [SimpleGraph.Walk.length_tail]
    omega
  have hpen : q.tail.penultimate = q.penultimate := by
    have h := SimpleGraph.Walk.penultimate_cons_of_not_nil
      (q.adj_snd hqNonNil) q.tail htailNonNil
    rw [q.cons_tail_eq hqNonNil] at h
    exact h.symm
  have hleft := q.adj_snd hqNonNil
  have hright := q.adj_penultimate hqNonNil
  cases hs : q.snd with
  | none =>
      rw [hs] at hleft
      have : False := by simpa [J, endpointAugment] using hleft
      exact this.elim
  | some x =>
      cases ht : q.penultimate with
      | none =>
          rw [ht] at hright
          have : False := by simpa [J, endpointAugment] using hright
          exact this.elim
      | some y =>
          have hx : x = a ∨ x = b := by
            rw [hs] at hleft
            simpa [J, endpointAugment] using hleft
          have hy : y = a ∨ y = b := by
            rw [ht] at hright
            simpa [J, endpointAugment] using hright.symm
          have hxy : x ≠ y := by
            intro h
            apply hq.isCycle.snd_ne_penultimate
            rw [hs, ht, h]
          let m₀ := q.tail.dropLast
          have hm₀Path : m₀.IsPath := hq.isCycle.isPath_tail.dropLast
          have hmend : q.tail.penultimate = some y := hpen.trans ht
          let m : (endpointAugment G a b).Walk (some x) (some y) :=
            m₀.copy hs hmend
          have hmOld : ∀ z ∈ m.support,
              z ∈ Set.range (some : V → Option V) := by
            intro z hz
            cases z with
            | some z => exact Set.mem_range_self z
            | none =>
                have hz₀ : (none : Option V) ∈ m₀.support := by simpa [m] using hz
                have hzDrop : (none : Option V) ∈ q.tail.support.dropLast := by
                  simpa [m₀, SimpleGraph.Walk.support_dropLast htailNonNil] using hz₀
                have hn := hq.isCycle.isPath_tail.support_nodup
                have hne := hn.rel_dropLast_getLast hzDrop
                exact (hne (SimpleGraph.Walk.getLast_support q.tail).symm).elim
          obtain ⟨r, hrmap⟩ := exists_old_preimage m hmOld
          have hrPath : r.IsPath := by
            rw [SimpleGraph.Walk.isPath_def]
            have hmNodup : m.support.Nodup := by
              rw [SimpleGraph.Walk.isPath_def] at hm₀Path
              simpa [m] using hm₀Path
            have hsupp := congrArg SimpleGraph.Walk.support hrmap
            simp only [SimpleGraph.Walk.support_map] at hsupp
            change List.map some r.support = m.support at hsupp
            have hmapNodup : (r.support.map some).Nodup := by
              rw [hsupp]
              exact hmNodup
            exact hmapNodup.of_map some
          have hrHam : r.IsHamiltonian := by
            apply hrPath.isHamiltonian_of_mem
            intro v
            have hvq : (some v : Option V) ∈ q.support := hq.mem_support (some v)
            have hvTail : (some v : Option V) ∈ q.tail.support := by
              simpa [SimpleGraph.Walk.support_tail_of_not_nil q hqNonNil] using
                (show (some v : Option V) ∈ q.support.tail from by
                  rw [SimpleGraph.Walk.support_eq_cons] at hvq
                  simp only [List.mem_cons] at hvq
                  exact hvq.resolve_left (by simp))
            have hlast : q.tail.support.getLast (by
                simpa [SimpleGraph.Walk.length_support] using
                  (show 0 < q.tail.support.length by
                    rw [SimpleGraph.Walk.length_support]
                    exact SimpleGraph.Walk.not_nil_iff_lt_length.mp htailNonNil)) = none := by
              exact SimpleGraph.Walk.getLast_support q.tail
            have hvDrop : (some v : Option V) ∈ q.tail.support.dropLast :=
              List.mem_dropLast_of_mem_of_ne_getLast hvTail (by simpa [hlast])
            have hvm : (some v : Option V) ∈ m.support := by
              simpa [m, m₀, SimpleGraph.Walk.support_dropLast htailNonNil] using hvDrop
            have hvm' : (some v : Option V) ∈
                (r.map (endpointAugmentEmbedding G a b).toHom).support := by
              rw [hrmap]
              exact hvm
            rw [SimpleGraph.Walk.support_map] at hvm'
            obtain ⟨w, hw, hwv⟩ := List.mem_map.mp hvm'
            exact Option.some.inj hwv ▸ hw
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact (hxy rfl).elim
          · exact ⟨r, hrHam⟩
          · refine ⟨r.reverse, ?_⟩
            intro v
            simpa [SimpleGraph.Walk.support_reverse] using hrHam v
          · exact (hxy rfl).elim

/-! ## Public deterministic lemmas -/

/-- A sparse-complement graph with linear minimum degree is Hamilton
connected, with an explicit integer inequality.  This is the form directly
used after random restriction in the almost-two-cliques case. -/
theorem exists_hamiltonPath_of_sparse_complement
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (hab : a ≠ b)
    (δ M : ℕ) (hδtwo : 2 ≤ δ) (hδcard : 2 * δ ≤ Fintype.card V)
    (hmindeg : ∀ v : V, δ ≤ G.degree v)
    (hmissing : Gᶜ.edgeFinset.card ≤ M)
    (hsparse : 2 * M < (δ - 1) * (Fintype.card V - δ - 1)) :
    ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply hamiltonPath_of_endpointAugment_isHamiltonian G hab
  exact endpointAugment_isHamiltonian G hab δ M hδtwo hδcard
    hmindeg hmissing hsparse

/-- The full deterministic almost-two-cliques lemma.  Each side has the
sparse-complement/minimum-degree hypotheses above, and two vertex-disjoint
crossing edges splice the prescribed Hamilton paths into a Hamilton cycle. -/
theorem isHamiltonian_of_two_sparse_parts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Set V) (hAB : Disjoint A B) (hcover : A ∪ B = Set.univ)
    {a₁ a₂ b₁ b₂ : V}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (hab₁ : G.Adj a₁ b₁) (hab₂ : G.Adj a₂ b₂)
    (δA MA δB MB : ℕ)
    (hδAtwo : 2 ≤ δA) (hδAcard : 2 * δA ≤ Fintype.card A)
    (hminA : ∀ v : A, δA ≤ (G.induce A).degree v)
    (hmissA : (G.induce A)ᶜ.edgeFinset.card ≤ MA)
    (hsparseA : 2 * MA < (δA - 1) * (Fintype.card A - δA - 1))
    (hδBtwo : 2 ≤ δB) (hδBcard : 2 * δB ≤ Fintype.card B)
    (hminB : ∀ v : B, δB ≤ (G.induce B).degree v)
    (hmissB : (G.induce B)ᶜ.edgeFinset.card ≤ MB)
    (hsparseB : 2 * MB < (δB - 1) * (Fintype.card B - δB - 1)) :
    G.IsHamiltonian := by
  obtain ⟨pA, hpA⟩ := exists_hamiltonPath_of_sparse_complement
    (G.induce A) (a := ⟨a₁, ha₁⟩) (b := ⟨a₂, ha₂⟩)
    (by intro h; exact ha (congrArg Subtype.val h))
    δA MA hδAtwo hδAcard
    hminA hmissA hsparseA
  obtain ⟨pB, hpB⟩ := exists_hamiltonPath_of_sparse_complement
    (G.induce B) (a := ⟨b₁, hb₁⟩) (b := ⟨b₂, hb₂⟩)
    (by intro h; exact hb (congrArg Subtype.val h))
    δB MB hδBtwo hδBcard
    hminB hmissB hsparseB
  let eA : (G.induce A) →g G := (SimpleGraph.Embedding.induce A).toHom
  let eB : (G.induce B) →g G := (SimpleGraph.Embedding.induce B).toHom
  let qA : G.Walk a₁ a₂ := (pA.map eA).copy rfl rfl
  let qB : G.Walk b₁ b₂ := (pB.map eB).copy rfl rfl
  have hqA : IsHamiltonPathOn A qA := by
    refine ⟨hpA.isPath.map
      (SimpleGraph.Embedding.induce (G := G) A).injective, ?_⟩
    intro v
    constructor
    · intro hv
      change v ∈ (pA.map eA).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
      exact z.2
    · intro hv
      change v ∈ (pA.map eA).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨⟨v, hv⟩, hpA.mem_support ⟨v, hv⟩, rfl⟩
  have hqB : IsHamiltonPathOn B qB := by
    refine ⟨hpB.isPath.map
      (SimpleGraph.Embedding.induce (G := G) B).injective, ?_⟩
    intro v
    constructor
    · intro hv
      change v ∈ (pB.map eB).support at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
      exact z.2
    · intro hv
      change v ∈ (pB.map eB).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨⟨v, hv⟩, hpB.mem_support ⟨v, hv⟩, rfl⟩
  exact isHamiltonian_of_two_cross_edges A B hAB hcover
    ha₁ ha₂ hb₁ hb₂ ha hb hab₁ hab₂ hqA hqB

end

end Erdos622.TwoCliqueHamiltonicity

#print axioms Erdos622.TwoCliqueHamiltonicity.exists_hamiltonPath_of_sparse_complement
#print axioms Erdos622.TwoCliqueHamiltonicity.isHamiltonian_of_two_sparse_parts

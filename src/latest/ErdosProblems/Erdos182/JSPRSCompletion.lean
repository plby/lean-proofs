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

import ErdosProblems.Erdos182.AlmostRegular
import ErdosProblems.Erdos182.Foundations
import ErdosProblems.Erdos182.PRSUpper

namespace Erdos182

namespace PRSCompletion

/-- The ordinary graph associated to a two-sorted bipartite graph. -/
def simpleGraph {A B : Type*} (G : BipartiteGraph A B) : SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inr b => G.Adj a b
    | Sum.inr b, Sum.inl a => G.Adj a b
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all⟩
  loopless := ⟨by intro x h; cases x <;> simp_all⟩

noncomputable instance simpleGraph.instDecidableRel {A B : Type*}
    (G : BipartiteGraph A B) : DecidableRel (simpleGraph G).Adj := Classical.decRel _

private theorem succ_le_two_pow : ∀ {a : ℕ}, 1 ≤ a → a + 1 ≤ 2 ^ a := by
  intro a ha
  induction a with
  | zero => omega
  | succ a ih =>
      by_cases ha0 : a = 0
      · subst a
        norm_num
      · have ha' : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        have hia := ih ha'
        calc
          a + 1 + 1 ≤ (a + 1) + (a + 1) := by omega
          _ ≤ 2 ^ a + 2 ^ a := Nat.add_le_add hia hia
          _ = 2 ^ (a + 1) := by rw [pow_succ]; omega

private theorem linear_le_pow_two_of_large (a : ℕ) (ha : 0 < a) :
    ∀ {n : ℕ}, 2 * a + 2 ≤ n → a * n ≤ 2 ^ n := by
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero =>
      have hasucc : a + 1 ≤ 2 ^ a := succ_le_two_pow (Nat.one_le_iff_ne_zero.mpr ha.ne')
      have haa : a ≤ 2 ^ a := a.le_succ.trans hasucc
      calc
        a * (2 * a + 2 + 0) = 2 * (a * (a + 1)) := by ring
        _ ≤ 2 * ((2 ^ a) * (2 ^ a)) := by gcongr
        _ = 2 ^ (2 * a + 1) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ (2 * a + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  | succ d ih =>
      have ih' : a * (2 * a + 2 + d) ≤ 2 ^ (2 * a + 2 + d) :=
        ih (by omega)
      have hbase : 1 ≤ 2 * a + 2 + d := by omega
      have ha_le : a ≤ 2 ^ (2 * a + 2 + d) :=
        (Nat.le_mul_of_pos_right a hbase).trans ih'
      calc
        a * (2 * a + 2 + (d + 1)) =
            a * (2 * a + 2 + d) + a := by ring
        _ ≤ 2 ^ (2 * a + 2 + d) + 2 ^ (2 * a + 2 + d) :=
          Nat.add_le_add ih' ha_le
        _ = 2 ^ (2 * a + 2 + (d + 1)) := by
          rw [show 2 * a + 2 + (d + 1) = (2 * a + 2 + d) + 1 by omega,
            pow_succ]
          omega

/-- A completely explicit threshold after which a logarithm multiplied by
an arbitrary positive coefficient is bounded by the identity function. -/
theorem coeff_log2_le_self_of_pow_threshold (a Δ : ℕ) (ha : 0 < a)
    (hΔ : 2 ^ (2 * a + 2) ≤ Δ) :
    a * Nat.log2 Δ ≤ Δ := by
  have hΔpos : Δ ≠ 0 := by
    intro hzero
    subst Δ
    simp at hΔ
  have hlog : 2 * a + 2 ≤ Nat.log2 Δ := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.le_log_iff_pow_le (by omega) hΔpos).2 hΔ
  exact (linear_le_pow_two_of_large a ha hlog).trans
    (by simpa [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hΔpos)

section Support

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The active left vertices of a bipartite graph. -/
abbrev LeftSupport (G : BipartiteGraph A B) :=
  {a : A // 0 < G.leftDegree a}

/-- The active right vertices of a bipartite graph. -/
abbrev RightSupport (G : BipartiteGraph A B) :=
  {b : B // 0 < G.rightDegree b}

/-- The same bipartite graph after discarding its isolated vertices. -/
def supportGraph (G : BipartiteGraph A B) :
    BipartiteGraph (LeftSupport G) (RightSupport G) :=
  ⟨fun a b ↦ G.Adj a.1 b.1⟩

theorem leftDegree_supportGraph (G : BipartiteGraph A B)
    (a : LeftSupport G) :
    (supportGraph G).leftDegree a = G.leftDegree a.1 := by
  classical
  unfold BipartiteGraph.leftDegree BipartiteGraph.rightNeighbors supportGraph
  let f : {b : RightSupport G // G.Adj a.1 b.1} ≃ {b : B // G.Adj a.1 b} :=
    { toFun := fun b ↦ ⟨b.1.1, b.2⟩
      invFun := fun b ↦ ⟨⟨b.1, by
        unfold BipartiteGraph.rightDegree BipartiteGraph.leftNeighbors
        apply Finset.card_pos.mpr
        exact ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩⟩⟩, b.2⟩
      left_inv := by intro b; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro b; apply Subtype.ext; rfl }
  rw [← Fintype.card_subtype (fun b : RightSupport G ↦ G.Adj a.1 b.1),
    ← Fintype.card_subtype (fun b : B ↦ G.Adj a.1 b)]
  exact Fintype.card_congr f

theorem rightDegree_supportGraph (G : BipartiteGraph A B)
    (b : RightSupport G) :
    (supportGraph G).rightDegree b = G.rightDegree b.1 := by
  classical
  unfold BipartiteGraph.rightDegree BipartiteGraph.leftNeighbors supportGraph
  let f : {a : LeftSupport G // G.Adj a.1 b.1} ≃ {a : A // G.Adj a b.1} :=
    { toFun := fun a ↦ ⟨a.1.1, a.2⟩
      invFun := fun a ↦ ⟨⟨a.1, by
        unfold BipartiteGraph.leftDegree BipartiteGraph.rightNeighbors
        apply Finset.card_pos.mpr
        exact ⟨b.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩⟩, a.2⟩
      left_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro a; apply Subtype.ext; rfl }
  rw [← Fintype.card_subtype (fun a : LeftSupport G ↦ G.Adj a.1 b.1),
    ← Fintype.card_subtype (fun a : A ↦ G.Adj a b.1)]
  exact Fintype.card_congr f

theorem edgeCount_supportGraph (G : BipartiteGraph A B) :
    (supportGraph G).edgeCount = G.edgeCount := by
  rw [BipartiteGraph.edgeCount_eq_sum_leftDegree,
    BipartiteGraph.edgeCount_eq_sum_leftDegree]
  classical
  simp_rw [leftDegree_supportGraph]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a ↦ 0 < G.leftDegree a)
    (by simp) G.leftDegree]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a _ ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  omega

theorem card_supportGraph (G : BipartiteGraph A B) :
    Fintype.card (LeftSupport G ⊕ RightSupport G) = G.supportCard := by
  classical
  simp only [Fintype.card_sum, BipartiteGraph.supportCard,
    Fintype.card_subtype]

theorem degree_simpleGraph_inl (G : BipartiteGraph A B) (a : A) :
    (simpleGraph G).degree (Sum.inl a) = G.leftDegree a := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let f : (simpleGraph G).neighborSet (Sum.inl a) ≃ {b : B // G.Adj a b} :=
    { toFun := fun w ↦ by
        rcases w with ⟨w, hw⟩
        cases w with
        | inl a' => simp [simpleGraph] at hw
        | inr b => exact ⟨b, hw⟩
      invFun := fun b ↦ ⟨Sum.inr b.1, b.2⟩
      left_inv := by
        rintro ⟨w, hw⟩
        cases w with
        | inl a' => simp [simpleGraph] at hw
        | inr b => rfl
      right_inv := by intro b; apply Subtype.ext; rfl }
  calc
    Fintype.card ((simpleGraph G).neighborSet (Sum.inl a)) =
        Fintype.card {b : B // G.Adj a b} := Fintype.card_congr f
    _ = (Finset.univ.filter fun b : B ↦ G.Adj a b).card := Fintype.card_subtype _
    _ = G.leftDegree a := by
      simp [BipartiteGraph.leftDegree, BipartiteGraph.rightNeighbors]

theorem degree_simpleGraph_inr (G : BipartiteGraph A B) (b : B) :
    (simpleGraph G).degree (Sum.inr b) = G.rightDegree b := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let f : (simpleGraph G).neighborSet (Sum.inr b) ≃ {a : A // G.Adj a b} :=
    { toFun := fun w ↦ by
        rcases w with ⟨w, hw⟩
        cases w with
        | inl a => exact ⟨a, hw⟩
        | inr b' => simp [simpleGraph] at hw
      invFun := fun a ↦ ⟨Sum.inl a.1, a.2⟩
      left_inv := by
        rintro ⟨w, hw⟩
        cases w with
        | inl a => rfl
        | inr b' => simp [simpleGraph] at hw
      right_inv := by intro a; apply Subtype.ext; rfl }
  calc
    Fintype.card ((simpleGraph G).neighborSet (Sum.inr b)) =
        Fintype.card {a : A // G.Adj a b} := Fintype.card_congr f
    _ = (Finset.univ.filter fun a : A ↦ G.Adj a b).card := Fintype.card_subtype _
    _ = G.rightDegree b := by
      simp [BipartiteGraph.rightDegree, BipartiteGraph.leftNeighbors]

theorem twice_card_edges_simpleGraph (G : BipartiteGraph A B) :
    2 * (simpleGraph G).edgeFinset.card = 2 * G.edgeCount := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, Fintype.sum_sum_type]
  simp_rw [degree_simpleGraph_inl, degree_simpleGraph_inr]
  rw [← BipartiteGraph.edgeCount_eq_sum_leftDegree,
    ← BipartiteGraph.edgeCount]
  omega

theorem maxDegree_mul_card_le_of_almostRegular
    (G : BipartiteGraph A B) (K : ℕ) (hG : G.IsAlmostRegular K) :
    (simpleGraph (supportGraph G)).maxDegree * G.supportCard ≤
      K * (2 * G.edgeCount) := by
  classical
  have hedge : 0 < (supportGraph G).edgeCount := by
    simpa only [edgeCount_supportGraph] using hG.1
  obtain ⟨a, b, hab⟩ : ∃ a b, (supportGraph G).Adj a b := by
    rw [BipartiteGraph.edgeCount, Finset.sum_pos_iff] at hedge
    obtain ⟨b, _hbmem, hb⟩ := hedge
    rw [BipartiteGraph.rightDegree, Finset.card_pos] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, b, (BipartiteGraph.mem_leftNeighbors _ _ _).mp ha⟩
  letI : Nonempty (LeftSupport G ⊕ RightSupport G) := ⟨Sum.inl a⟩
  rw [← card_supportGraph G, ← edgeCount_supportGraph G,
    ← twice_card_edges_simpleGraph (supportGraph G),
    ← SimpleGraph.sum_degrees_eq_twice_card_edges, Fintype.card_sum,
    Fintype.sum_sum_type, Nat.mul_add, Nat.mul_add]
  apply Nat.add_le_add
  · calc
      (simpleGraph (supportGraph G)).maxDegree * Fintype.card (LeftSupport G) =
          ∑ _a : LeftSupport G, (simpleGraph (supportGraph G)).maxDegree := by
            simp [Nat.mul_comm]
      _ ≤ ∑ a : LeftSupport G, K * (supportGraph G).leftDegree a := by
        apply Finset.sum_le_sum
        intro a _
        apply (simpleGraph (supportGraph G)).maxDegree_le_of_forall_degree_le
        intro u
        cases u with
        | inl u =>
            rw [degree_simpleGraph_inl]
            simpa [BipartiteGraph.vertexDegree, leftDegree_supportGraph] using
              hG.2 (Sum.inl u.1) (Sum.inl a.1) a.2
        | inr u =>
            rw [degree_simpleGraph_inr, rightDegree_supportGraph,
              leftDegree_supportGraph]
            exact hG.2 (Sum.inr u.1) (Sum.inl a.1) a.2
      _ = K * ∑ a : LeftSupport G, (supportGraph G).leftDegree a := by
        rw [Finset.mul_sum]
      _ = K * ∑ a : LeftSupport G,
          (simpleGraph (supportGraph G)).degree (Sum.inl a) := by
        simp_rw [degree_simpleGraph_inl]
  · calc
      (simpleGraph (supportGraph G)).maxDegree * Fintype.card (RightSupport G) =
          ∑ _b : RightSupport G, (simpleGraph (supportGraph G)).maxDegree := by
            simp [Nat.mul_comm]
      _ ≤ ∑ b : RightSupport G, K * (supportGraph G).rightDegree b := by
        apply Finset.sum_le_sum
        intro b _
        apply (simpleGraph (supportGraph G)).maxDegree_le_of_forall_degree_le
        intro u
        cases u with
        | inl u =>
            rw [degree_simpleGraph_inl, leftDegree_supportGraph,
              rightDegree_supportGraph]
            exact hG.2 (Sum.inl u.1) (Sum.inr b.1) b.2
        | inr u =>
            rw [degree_simpleGraph_inr]
            simpa [BipartiteGraph.vertexDegree, rightDegree_supportGraph] using
              hG.2 (Sum.inr u.1) (Sum.inr b.1) b.2
      _ = K * ∑ b : RightSupport G, (supportGraph G).rightDegree b := by
        rw [Finset.mul_sum]
      _ = K * ∑ b : RightSupport G,
          (simpleGraph (supportGraph G)).degree (Sum.inr b) := by
        simp_rw [degree_simpleGraph_inr]

end Support

/-- The exact bounded-maximum-degree input supplied by the PRS theorem. -/
def MaxDegreeLogForcing (k C : ℕ) : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ),
    2 ≤ Δ → (∀ v, G.degree v ≤ Δ) →
      C * (Nat.log2 Δ + 1) * Fintype.card V ≤ 2 * G.edgeFinset.card →
      ContainsRegularSubgraph G k

/-- Copies transport literal regular subgraphs to the target graph. -/
theorem containsRegularSubgraph_of_copy
    {X Y : Type*} [Fintype X] [Fintype Y]
    {J : SimpleGraph X} {G : SimpleGraph Y} {k : ℕ}
    (f : SimpleGraph.Copy J G) (h : ContainsRegularSubgraph J k) :
    ContainsRegularSubgraph G k := by
  classical
  obtain ⟨K, hKne, hKreg⟩ := h
  let K' : G.Subgraph := K.map f.toHom
  let e : K.coe ≃g K'.coe := f.isoSubgraphMap K
  refine ⟨K', ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hKne
    exact ⟨f v, Set.mem_image_of_mem f hv⟩
  · intro v
    obtain ⟨u, hu, huv⟩ := v.2
    let uK : K.verts := ⟨u, hu⟩
    have hev : e uK = v := by
      apply Subtype.ext
      exact huv
    rw [← hev]
    have hncard := Set.ncard_congr' (e.mapNeighborSet uK)
    exact hncard.symm.trans (hKreg uK)

section SupportForcing

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The inclusion of the graph with isolates discarded into the original
bipartite simple graph. -/
def supportCopy (G : BipartiteGraph A B) :
    SimpleGraph.Copy (simpleGraph (supportGraph G)) (simpleGraph G) where
  toHom :=
    { toFun := fun x ↦ match x with
        | Sum.inl a => Sum.inl a.1
        | Sum.inr b => Sum.inr b.1
      map_rel' := by
        intro x y hxy
        cases x <;> cases y <;> exact hxy }
  injective' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' =>
            change Sum.inl a.1 = Sum.inl a'.1 at hxy
            exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hxy))
        | inr b => simp_all
    | inr b =>
        cases y with
        | inl a => simp_all
        | inr b' =>
            change Sum.inr b.1 = Sum.inr b'.1 at hxy
            exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj hxy))

/-- A support-relative `K`-almost-regular graph whose average degree exceeds
an explicit PRS threshold contains the required regular subgraph.  The PRS
theorem itself is an explicit hypothesis; there is no hidden assumption. -/
theorem containsRegularSubgraph_of_almostRegular
    {k C K : ℕ} (hC : 0 < C) (hK : 0 < K)
    (G : BipartiteGraph A B) (hreg : G.IsAlmostRegular K)
    (hforce : ∀ (J : SimpleGraph (LeftSupport G ⊕ RightSupport G))
        [DecidableRel J.Adj] (Δ : ℕ),
      2 ≤ Δ → (∀ v, J.degree v ≤ Δ) →
        C * (Nat.log2 Δ + 1) * Fintype.card (LeftSupport G ⊕ RightSupport G) ≤
          2 * J.edgeFinset.card → ContainsRegularSubgraph J k)
    (havg : 2 ^ (4 * (K * C) + 2) * G.supportCard ≤ 2 * G.edgeCount) :
    ContainsRegularSubgraph (simpleGraph G) k := by
  classical
  let S := simpleGraph (supportGraph G)
  have hedge : 0 < (supportGraph G).edgeCount := by
    simpa only [edgeCount_supportGraph] using hreg.1
  obtain ⟨a, b, hab⟩ : ∃ a b, (supportGraph G).Adj a b := by
    rw [BipartiteGraph.edgeCount, Finset.sum_pos_iff] at hedge
    obtain ⟨b, _hbmem, hb⟩ := hedge
    rw [BipartiteGraph.rightDegree, Finset.card_pos] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, b, (BipartiteGraph.mem_leftNeighbors _ _ _).mp ha⟩
  letI : Nonempty (LeftSupport G ⊕ RightSupport G) := ⟨Sum.inl a⟩
  let Δ := S.maxDegree
  have hsupport : 0 < G.supportCard := by
    rw [← card_supportGraph G]
    exact Fintype.card_pos
  have hsum_le : 2 * G.edgeCount ≤ Δ * G.supportCard := by
    rw [← edgeCount_supportGraph G,
      ← twice_card_edges_simpleGraph (supportGraph G),
      ← SimpleGraph.sum_degrees_eq_twice_card_edges, ← card_supportGraph G]
    calc
      ∑ v, S.degree v ≤ ∑ _v, Δ := by
        apply Finset.sum_le_sum
        intro v _
        exact S.degree_le_maxDegree v
      _ = Δ * Fintype.card (LeftSupport G ⊕ RightSupport G) := by
        simp [Nat.mul_comm]
  have hthreshold_le : 2 ^ (4 * (K * C) + 2) ≤ Δ := by
    apply Nat.le_of_mul_le_mul_right (c := G.supportCard) _ hsupport
    exact havg.trans hsum_le
  have hΔtwo : 2 ≤ Δ := by
    have : 4 ≤ 2 ^ (4 * (K * C) + 2) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (4 * (K * C) + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hlog : (2 * (K * C)) * Nat.log2 Δ ≤ Δ :=
    coeff_log2_le_self_of_pow_threshold (2 * (K * C)) Δ
      (by positivity) (by simpa only [show 2 * (2 * (K * C)) + 2 =
        4 * (K * C) + 2 by ring] using hthreshold_le)
  have hlogpos : 1 ≤ Nat.log2 Δ := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_pos (by omega) (by omega)
  have hlogAdd : (K * C) * (Nat.log2 Δ + 1) ≤ Δ := by
    calc
      (K * C) * (Nat.log2 Δ + 1) ≤
          (K * C) * (Nat.log2 Δ + Nat.log2 Δ) := by gcongr
      _ = (2 * (K * C)) * Nat.log2 Δ := by ring
      _ ≤ Δ := hlog
  have hdensity : C * (Nat.log2 Δ + 1) *
      Fintype.card (LeftSupport G ⊕ RightSupport G) ≤
      2 * S.edgeFinset.card := by
    have hscaled : K * (C * (Nat.log2 Δ + 1) * G.supportCard) ≤
        K * (2 * G.edgeCount) := by
      calc
        K * (C * (Nat.log2 Δ + 1) * G.supportCard) =
            ((K * C) * (Nat.log2 Δ + 1)) * G.supportCard := by ring
        _ ≤ Δ * G.supportCard := Nat.mul_le_mul_right _ hlogAdd
        _ ≤ K * (2 * G.edgeCount) :=
          maxDegree_mul_card_le_of_almostRegular G K hreg
    have hcancel : C * (Nat.log2 Δ + 1) * G.supportCard ≤ 2 * G.edgeCount :=
      Nat.le_of_mul_le_mul_left hscaled hK
    rw [card_supportGraph G, twice_card_edges_simpleGraph (supportGraph G),
      edgeCount_supportGraph G]
    exact hcancel
  have hS : ContainsRegularSubgraph S k := by
    exact hforce S Δ hΔtwo
      (fun v ↦ S.degree_le_maxDegree v) hdensity
  exact containsRegularSubgraph_of_copy (supportCopy G) hS

/-- The specialization used by the Janzer--Sudakov `64`-almost-regular
extraction. -/
theorem containsRegularSubgraph_of_sixtyFourAlmostRegular
    {k C : ℕ} (hC : 0 < C)
    (G : BipartiteGraph A B) (hreg : G.IsAlmostRegular 64)
    (hforce : ∀ (J : SimpleGraph (LeftSupport G ⊕ RightSupport G))
        [DecidableRel J.Adj] (Δ : ℕ),
      2 ≤ Δ → (∀ v, J.degree v ≤ Δ) →
        C * (Nat.log2 Δ + 1) * Fintype.card (LeftSupport G ⊕ RightSupport G) ≤
          2 * J.edgeFinset.card → ContainsRegularSubgraph J k)
    (havg : 2 ^ (256 * C + 2) * G.supportCard ≤ 2 * G.edgeCount) :
    ContainsRegularSubgraph (simpleGraph G) k := by
  apply containsRegularSubgraph_of_almostRegular hC (by norm_num) G hreg hforce
  simpa only [show 4 * (64 * C) + 2 = 256 * C + 2 by ring] using havg

/-- The unconditional PRS completion of the `64`-almost-regular branch.
The constant is supplied by `PRSUpper.prs_upper_nat`; the displayed power is
an explicit threshold depending only on that constant. -/
theorem exists_prsConstant_sixtyFourAlmostRegular (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {A B : Type*} [Fintype A] [Fintype B]
        (G : BipartiteGraph A B),
        G.IsAlmostRegular 64 →
        2 ^ (256 * C + 2) * G.supportCard ≤ 2 * G.edgeCount →
        ContainsRegularSubgraph (simpleGraph G) k := by
  obtain ⟨C, hC, hprs⟩ := PRSUpper.prs_upper_nat k hk
  refine ⟨C, hC, ?_⟩
  intro A B _instA _instB G hreg havg
  classical
  have hedge : 0 < G.edgeCount := hreg.1
  obtain ⟨a, b, hab⟩ : ∃ a b, G.Adj a b := by
    rw [BipartiteGraph.edgeCount, Finset.sum_pos_iff] at hedge
    obtain ⟨b, _hbmem, hb⟩ := hedge
    rw [BipartiteGraph.rightDegree, Finset.card_pos] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, b, (BipartiteGraph.mem_leftNeighbors _ _ _).mp ha⟩
  let aS : LeftSupport G := ⟨a, by
    rw [BipartiteGraph.leftDegree, Finset.card_pos]
    exact ⟨b, (BipartiteGraph.mem_rightNeighbors _ _ _).mpr hab⟩⟩
  letI : Nonempty (LeftSupport G ⊕ RightSupport G) := ⟨Sum.inl aS⟩
  apply containsRegularSubgraph_of_sixtyFourAlmostRegular hC G hreg ?_ havg
  intro J _instAdj Delta hDelta hdegrees hdensity
  apply hprs J Delta hDelta
  · rw [PRSEntry.maximumDegreeNumber, Finset.sup_le_iff]
    intro v _hv
    rw [PRSEntry.degreeNumber_eq_degree]
    exact hdegrees v
  · rw [PRSEntry.edgeNumber_eq_card_edgeFinset]
    exact hdensity

end SupportForcing

section Ambient


variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A two-sorted subgraph between disjoint parts is a copy of a subgraph of
the ambient simple graph. -/
def ambientCopy (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint (A : Set V) (B : Set V))
    (H : BipartiteGraph A B)
    (hHG : ∀ {a : A} {b : B}, H.Adj a b → G.Adj a.1 b.1) :
    SimpleGraph.Copy (simpleGraph H) G where
  toHom :=
    { toFun := fun x ↦ match x with
        | Sum.inl a => a.1
        | Sum.inr b => b.1
      map_rel' := by
        intro x y hxy
        cases x with
        | inl a =>
            cases y with
            | inl a' => exact False.elim hxy
            | inr b => exact hHG hxy
        | inr b =>
            cases y with
            | inl a => exact G.symm.symm _ _ (hHG hxy)
            | inr b' => exact False.elim hxy }
  injective' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' => exact congrArg Sum.inl (Subtype.ext hxy)
        | inr b =>
            exfalso
            change a.1 = b.1 at hxy
            have haB : a.1 ∈ B := by simpa [hxy] using b.2
            exact Set.disjoint_left.mp hAB a.2 haB
    | inr b =>
        cases y with
        | inl a =>
            exfalso
            change b.1 = a.1 at hxy
            have haB : a.1 ∈ B := by simpa [hxy] using b.2
            exact Set.disjoint_left.mp hAB a.2 haB
        | inr b' => exact congrArg Sum.inr (Subtype.ext hxy)

/-- Final ambient form of the PRS application.  `H` is an actual bipartite
subgraph of `G` between disjoint parts; a regular graph found after deleting
the isolates of `H` is transported first to `H` and then to `G`. -/
theorem containsRegularSubgraph_of_almostRegular_subgraph
    {k C K : ℕ} (hC : 0 < C) (hK : 0 < K)
    (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint (A : Set V) (B : Set V))
    (H : BipartiteGraph A B)
    (hHG : ∀ {a : A} {b : B}, H.Adj a b → G.Adj a.1 b.1)
    (hreg : H.IsAlmostRegular K)
    (hforce : ∀ (J : SimpleGraph (LeftSupport H ⊕ RightSupport H))
        [DecidableRel J.Adj] (Δ : ℕ),
      2 ≤ Δ → (∀ v, J.degree v ≤ Δ) →
        C * (Nat.log2 Δ + 1) * Fintype.card (LeftSupport H ⊕ RightSupport H) ≤
          2 * J.edgeFinset.card → ContainsRegularSubgraph J k)
    (havg : 2 ^ (4 * (K * C) + 2) * H.supportCard ≤ 2 * H.edgeCount) :
    ContainsRegularSubgraph G k := by
  apply containsRegularSubgraph_of_copy (ambientCopy G A B hAB H hHG)
  exact containsRegularSubgraph_of_almostRegular hC hK H hreg hforce havg

/-- The unconditional ambient version of the `64`-almost-regular PRS
completion.  The PRS constant is uniform over the ambient finite graph and
the chosen disjoint bipartite parts. -/
theorem exists_prsConstant_sixtyFourAlmostRegular_subgraph
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {W : Type*} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) (A B : Finset W)
        (hAB : Disjoint (A : Set W) (B : Set W))
        (H : BipartiteGraph A B),
        (∀ {a : A} {b : B}, H.Adj a b → G.Adj a.1 b.1) →
        H.IsAlmostRegular 64 →
        2 ^ (256 * C + 2) * H.supportCard ≤ 2 * H.edgeCount →
        ContainsRegularSubgraph G k := by
  obtain ⟨C, hC, hprs⟩ :=
    exists_prsConstant_sixtyFourAlmostRegular k hk
  refine ⟨C, hC, ?_⟩
  intro W _instW _decW G A B hAB H hHG hreg havg
  apply containsRegularSubgraph_of_copy (ambientCopy G A B hAB H hHG)
  exact hprs H hreg havg

end Ambient

end PRSCompletion

end Erdos182

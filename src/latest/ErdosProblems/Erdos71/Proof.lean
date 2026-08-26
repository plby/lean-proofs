/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of Erdős Problem 71, ported from Lean/Mathlib 4.28.0.
Informal author: Béla Bollobás.
Formal authors: Andres Gutierrez, Aristotle, GPT-5.5, Opus 4.7.
Source: https://www.erdosproblems.com/forum/thread/71#post-6635
The exact online-editor source is preserved as andresg535_71 in data/urls.yaml.
This file has been modified for the repository and Lean/Mathlib 4.33.0.
-/
import Mathlib

-- Retain the generated source's proof style and pre-4.29 elaboration behavior.
set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Erdős Problem 71

*Reference:* [erdosproblems.com/71](https://www.erdosproblems.com/71)

> Is it true that for every infinite arithmetic progression `P` which contains
> even numbers there is some constant `c = c(P)` such that every graph with
> average degree at least `c` contains a cycle whose length is in `P`?

Solved affirmatively by Bollobás [Bo77]:

[Bo77] B. Bollobás, *Cycles modulo k*, Bull. London Math. Soc. **9** (1977), 97–98.

## Proof roadmap

1. **Arithmetic lemma** (`double_residues_surjective`): multiplication by 2
   permutes residues modulo an odd `k`.
2. **Dense-subgraph lemma** (`exists_induced_subgraph_minDeg`): a graph with
   `e(G) ≥ c · |V(G)|` contains an induced subgraph of minimum degree ≥ c.
3. **Theorem 1′ — the Bollobás fan lemma** (`bollobas_fan_of_minDeg_s_*`):
   a graph with sufficiently large minimum degree contains a *fan*: a path
   together with `d` internally-disjoint length-`s` branches from a common
   root to vertices on the path. Proved separately for `s = 1`, `s = 2`,
   and `s ≥ 3` via a `d`-ary tree embedding plus a maximal-pair argument.
4. **Bollobás's Theorem 2** (`bollobas_cycles_mod_odd`): from a fan with
   the parameters of step 3, build cycles of every length modulo an odd `k`.
5. **Corollary** (`erdos_71`): for `d` odd we use Theorem 2 directly; for
   `d` even, the AP-contains-an-even-number hypothesis forces `a` even,
   reducing to the fan-cycle construction with `s = a/2`.
-/

open Finset SimpleGraph

namespace Erdos71

/-! ## §1  Core definitions -/

/-- A simple graph `G` has a cycle of length exactly `n`. -/
def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = n

/-- `G` has a cycle whose length is congruent to `r` modulo `k`. -/
def HasCycleOfLengthMod {V : Type*} (G : SimpleGraph V)
    (k : ℕ) (r : ZMod k) : Prop :=
  ∃ n : ℕ, HasCycleOfLength G n ∧ (n : ZMod k) = r

/-- An infinite arithmetic progression of positive integers
`{ a + m · d : m ∈ ℕ }` with `a, d ≥ 1`. -/
structure InfiniteAP where
  /-- First term of the progression. -/
  a : ℕ
  /-- Common difference of the progression. -/
  d : ℕ
  a_pos : 1 ≤ a
  d_pos : 1 ≤ d

namespace InfiniteAP

/-- `n` lies in the progression `P` iff `n = P.a + m · P.d` for some `m : ℕ`. -/
def Mem (P : InfiniteAP) (n : ℕ) : Prop := ∃ m : ℕ, n = P.a + m * P.d

instance : Membership ℕ InfiniteAP where
  mem P n := P.Mem n

@[simp] lemma mem_def {P : InfiniteAP} {n : ℕ} :
    n ∈ P ↔ ∃ m : ℕ, n = P.a + m * P.d := Iff.rfl

/-- An infinite AP *contains an even number* iff some element is even. -/
def ContainsEven (P : InfiniteAP) : Prop := ∃ n ∈ P, Even n

end InfiniteAP

/-- The average degree of a finite simple graph, `2 |E(G)| / |V(G)| : ℚ`. -/
noncomputable def avgDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (2 * G.edgeFinset.card : ℚ) / Fintype.card V

/-! ## §2  The Bollobás constant -/

/-- The Bollobás dense-graph constant.  Chosen large enough that the
dense-subgraph lemma extracts a subgraph whose minimum degree exceeds the
`fanThreshold` for every `1 ≤ s ≤ k`. -/
def bollobasConst (k : ℕ) : ℕ := ((k + 1) ^ k - 1) / k + k

/-! ## §3  Arithmetic lemmas -/

/-- Multiplication by 2 is a bijection on ZMod k when k is odd. -/
lemma ZMod.bijective_mul_two {k : ℕ} (hk : Odd k) (_hk0 : k ≠ 0) :
    Function.Bijective (fun x : ZMod k => 2 * x) :=
  ((ZMod.isUnit_iff_coprime 2 k).mpr (hk.coprime_two_right.symm)).unit.mulLeft_bijective

/-- As s ranges over 1, …, k, the residues 2s mod k cover all of ZMod k,
    when k is odd and k ≥ 1. -/
lemma double_residues_surjective {k : ℕ} (hk : Odd k) (hk_pos : 0 < k) :
    ∀ r : ZMod k, ∃ s : ℕ, 1 ≤ s ∧ s ≤ k ∧ (2 * s : ZMod k) = r := by
  have h_bij : ∀ r : ZMod k, ∃ s : ZMod k, 2 * s = r := by
    exact fun r => by
      obtain ⟨s, hs⟩ := ZMod.bijective_mul_two hk hk_pos.ne' |>.2 r; tauto
  intro r
  obtain ⟨s, hs⟩ := h_bij r
  by_cases hs_zero : s = 0
  · use k; aesop
  · refine ⟨s.val, ?_, ?_, ?_⟩
    · exact Nat.pos_of_ne_zero (by simpa [ZMod.val_eq_zero] using hs_zero)
    · cases k <;> [aesop; exact Nat.le_of_lt (ZMod.val_lt s)]
    · cases k <;> aesop

/-! ## §4  Dense-subgraph lemma -/

/-
**Dense-subgraph lemma.**  If a nonempty finite graph has e(G) ≥ c · |V(G)|,
    then it contains a nonempty induced subgraph whose minimum degree is ≥ c.
-/
lemma exists_induced_subgraph_minDeg {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℕ) (hc : c * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (S : Finset V), S.Nonempty ∧
      ∀ v ∈ S, c ≤ (S.filter (G.Adj v)).card := by
  contrapose! hc with h
  -- Let's choose any ordering of the vertices and define $d_i$ as the number of neighbors of $v_i$ among $v_{i+1}, \ldots, v_n$.
  obtain ⟨v, hv⟩ : ∃ v : Fin (Fintype.card V) → V, Function.Injective v ∧ ∀ i, (Finset.card (Finset.filter (fun w => G.Adj (v i) w) (Finset.image v (Finset.Ioi i)))) < c := by
    -- We can construct such an ordering by induction on the number of vertices.
    have h_ind : ∀ (n : ℕ) (hn : n ≤ Fintype.card V), ∀ (S : Finset V), S.card = n → ∃ v : Fin n → V, Function.Injective v ∧ (∀ i, v i ∈ S) ∧ (∀ i, (Finset.card (Finset.filter (fun w => G.Adj (v i) w) (Finset.image v (Finset.Ioi i)))) < c) := by
      intro n hn S hS_card
      induction' n with n ih generalizing S
      · simp [Function.Injective]
      · obtain ⟨v, hvS, hv⟩ := h S (Finset.card_pos.mp (by linarith))
        obtain ⟨w, hw⟩ := ih (Nat.le_of_succ_le hn) (S.erase v) (by rw [Finset.card_erase_of_mem hvS, hS_card] ; simp)
        refine ⟨Fin.cons v w, ?_, ?_, ?_⟩ <;> simp_all [Fin.forall_fin_succ, Function.Injective]
        · exact ⟨fun i hi => False.elim (hw.2.1 i |>.1 (hi.symm)), fun i j hij => hw.1 hij⟩
        · refine ⟨?_, ?_⟩
          · refine lt_of_le_of_lt ?_ hv
            refine Finset.card_le_card ?_
            simp [Finset.subset_iff]
            exact fun i hi hi' => ⟨by cases i using Fin.inductionOn <;> aesop, hi'⟩
          · intro i
            convert hw.2.2 i using 1
            congr 1 with x ; simp [Fin.exists_fin_succ]
    exact Exists.elim (h_ind (Fintype.card V) le_rfl Finset.univ (by simp)) fun v hv => ⟨v, hv.1, hv.2.2⟩
  -- The number of edges is at most the sum of $d_i$ over all $i$, which is less than $c \cdot n$.
  have h_edges : (Finset.card G.edgeFinset) ≤ ∑ i : Fin (Fintype.card V), (Finset.card (Finset.filter (fun w => G.Adj (v i) w) (Finset.image v (Finset.Ioi i)))) := by
    have h_edges : G.edgeFinset ⊆ Finset.biUnion (Finset.univ : Finset (Fin (Fintype.card V)))
        (fun i => Finset.image (fun w => s(v i, w))
          (Finset.filter (fun w => G.Adj (v i) w) (Finset.image v (Finset.Ioi i)))) := by
      intro e he
      simp_all
      rcases e with ⟨x, y⟩
      have hv_surj : ∀ z : V, z ∈ Finset.image v Finset.univ := by
        intro z
        have := Finset.eq_of_subset_of_card_le
          (show Finset.image v Finset.univ ⊆ Finset.univ from Finset.subset_univ _)
        simp_all [Finset.card_image_of_injective _ hv.1]
      rcases Finset.mem_image.mp (hv_surj x) with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp (hv_surj y) with ⟨j, _, rfl⟩
      cases lt_trichotomy i j <;> simp_all [SimpleGraph.adj_comm]
      · exact ⟨i, j, ⟨by assumption, he⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨j, i, ⟨by aesop, he.symm⟩, by aesop⟩
    exact le_trans (Finset.card_le_card h_edges) (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => Finset.card_image_le))
  exact h_edges.trans_lt (lt_of_lt_of_le (Finset.sum_lt_sum_of_nonempty ⟨⟨0, Fintype.card_pos⟩, Finset.mem_univ _⟩ fun i _ => hv.2 i) (by simp [mul_comm]))

/-! ## §5  Cycle transfer lemma -/

/-- A cycle in an induced subgraph gives a cycle in the original graph. -/
lemma HasCycleOfLength_of_induce {V : Type*} (G : SimpleGraph V)
    (S : Set V) (n : ℕ) (h : HasCycleOfLength (G.induce S) n) :
    HasCycleOfLength G n := by
  obtain ⟨v, w, hcyc, hlen⟩ := h
  let f : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  exact ⟨v.val, w.map f, hcyc.map Subtype.val_injective,
         by rw [Walk.length_map]; exact hlen⟩

/-! ## §6  Theorem 1′ — Bollobás tree / fan lemma -/

/-- The minimum-degree threshold for Theorem 1′:  (d^s − 1) / (d - 1). -/
def fanTreeThreshold (d s : ℕ) : ℕ := (d ^ s - 1) / (d - 1)

/--
Source-faithful witness for the configuration produced by Bollobás Theorem `1'`.

The spine `P` is represented by a path `spine`, and `attachment i` is the unique
vertex where the `i`-th length-`s` branch from `root` meets the spine.
-/
structure BollobasFan {V : Type*} [DecidableEq V] (G : SimpleGraph V) (d s : ℕ) where
  root : V
  spineStart : V
  spineEnd : V
  spine : G.Walk spineStart spineEnd
  spine_isPath : spine.IsPath
  root_not_mem_spine : root ∉ spine.support
  attachment : Fin d → V
  attachment_mem_spine : ∀ i, attachment i ∈ spine.support
  branch : ∀ i, G.Walk root (attachment i)
  branch_isPath : ∀ i, (branch i).IsPath
  branch_length : ∀ i, (branch i).length = s
  branch_spine_inter :
    ∀ i, ((branch i).support.filter fun v => v ∈ spine.support) = [attachment i]
  pairwise_branch_inter :
    ∀ i j, i ≠ j →
      ∀ v, v ∈ (branch i).support → v ∈ (branch j).support → v = root ∨ v ∈ spine.support
  /-- Different branches trace different vertex sets.  This condition is
      automatically satisfied in the mathematical construction and rules out
      the degenerate case where two branches of length 1 happen to be
      the same edge. -/
  branch_support_ne :
    ∀ i j, i ≠ j → (branch i).support ≠ (branch j).support

namespace BollobasFan

/-- Position of an attachment vertex along the spine path. -/
def attachmentPos {V : Type*} [DecidableEq V] {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i : Fin d) : ℕ :=
  (F.spine.takeUntil (F.attachment i) (F.attachment_mem_spine i)).length

end BollobasFan

/-- The minimum-degree threshold for the Bollobás fan lemma (Theorem 1 of the
1977 paper): `(d^s - 1)/(d - 1) + (d - 1)`.  The extra `+ (d - 1)` slack beyond
`fanTreeThreshold d s` is what supplies the `d` distinct attachment vertices
`e_1, ..., e_d ∈ V(Q) - {b}` in the maximal-pair selection step.

For `s = 1` this evaluates to `1 + (d - 1) = d`, matching the maximal-path
argument directly. -/
def fanThreshold (d s : ℕ) : ℕ := fanTreeThreshold d s + (d - 1)

lemma fanTreeThreshold_le_fanThreshold (d s : ℕ) :
    fanTreeThreshold d s ≤ fanThreshold d s := by
  unfold fanThreshold; omega

/-- For `d ≥ 2` and `s ≥ 1`, `d ≤ fanThreshold d s`.  Used to extract a
degree-`d` neighbourhood at embedding-construction sites. -/
lemma d_le_fanThreshold (d s : ℕ) (hd : 2 ≤ d) (hs : 1 ≤ s) :
    d ≤ fanThreshold d s := by
  have hth : 1 ≤ fanTreeThreshold d s := by
    have hge : s ≤ fanTreeThreshold d s := by
      unfold fanTreeThreshold
      rcases d with _ | _ | d
      · omega
      · omega
      · rw [← Nat.geomSum_eq (by omega : 2 ≤ d + 2)]
        calc s = ∑ _ ∈ Finset.range s, 1 := by simp
          _ ≤ ∑ k ∈ Finset.range s, (d + 2) ^ k := by
            refine Finset.sum_le_sum ?_
            intro k _
            exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    omega
  unfold fanThreshold
  omega

/-! ### Intermediate lemmas toward Theorem 1′ -/

/-
A finite nonempty graph has a maximal path (one that cannot be extended).
-/
lemma exists_maximal_path {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      (∀ w : V, G.Adj w u → w ∈ p.support) ∧
      (∀ w : V, G.Adj v w → w ∈ p.support) := by
  by_contra h_contra
  simp +zetaDelta at *
  -- By repeatedly applying the hypothesis `h_contra`, we can construct an infinite sequence of paths, each strictly longer than the previous one.
  have h_infinite_sequence : ∀ n : ℕ, ∃ u v : V, ∃ p : G.Walk u v, p.IsPath ∧ p.length ≥ n := by
    intro n
    induction' n with n ih
    · exact ⟨Classical.arbitrary V, Classical.arbitrary V, SimpleGraph.Walk.nil,
        SimpleGraph.Walk.IsPath.nil, Nat.zero_le _⟩
    obtain ⟨u, v, p, hp, hn⟩ := ih
    by_cases h : ∀ w, G.Adj w u → w ∈ p.support
    · obtain ⟨w, hw₁, hw₂⟩ := h_contra u v p hp h
      refine ⟨u, w, p.append (SimpleGraph.Walk.cons hw₁ SimpleGraph.Walk.nil), ?_, ?_⟩
        <;> simp_all [SimpleGraph.Walk.isPath_def]
      simp_all [SimpleGraph.Walk.support_append]
      grind
    · obtain ⟨w, hw⟩ : ∃ w, G.Adj w u ∧ w ∉ p.support := by push Not at h; exact h
      refine ⟨w, v, SimpleGraph.Walk.cons hw.1 p, ?_, ?_⟩
        <;> simp_all [SimpleGraph.Walk.isPath_def]
  obtain ⟨u, v, p, hp, hp'⟩ := h_infinite_sequence (Fintype.card V)
  have := hp.support_nodup
  have := List.toFinset_card_of_nodup this
  exact absurd (Finset.card_le_univ (p.support.toFinset)) (by simp [this] ; linarith)

/-
The endpoint of a maximal path has all its neighbors on the path.
    In particular, its degree is at most the path length.
-/
lemma maximal_path_endpoint_neighbors_on_path
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (_hp : p.IsPath)
    (hmax : ∀ w : V, G.Adj w u → w ∈ p.support)
    (d : ℕ) (hd : d ≤ G.degree u) :
    ∃ (f : Fin d → V), Function.Injective f ∧
      (∀ i, f i ∈ p.support) ∧
      (∀ i, f i ≠ u) ∧
      (∀ i, G.Adj u (f i)) := by
  -- Since $u$ has degree at least $d$, there are at least $d$ neighbors of $u$.
  have h_neighbor_count : d ≤ (G.neighborFinset u).card := hd
  -- Since there are at least $d$ neighbors of $u$, we can select $d$ distinct neighbors from the neighborFinset.
  obtain ⟨neighbors, h_neighbors⟩ : ∃ neighbors : Finset V, neighbors ⊆ G.neighborFinset u ∧ neighbors.card = d := by
    exact le_card_iff_exists_subset_card.mp h_neighbor_count
  -- Since $neighbors$ is a subset of $G.neighborFinset u$, we can define $f$ as an injective function from $Fin d$ to $neighbors$.
  obtain ⟨f, hf_inj⟩ : ∃ f : Fin d → V, Function.Injective f ∧ ∀ i, f i ∈ neighbors := by
    have h_inj : Nonempty (Fin d ≃ neighbors) := by
      exact ⟨Fintype.equivOfCardEq <| by simp [h_neighbors.2]⟩
    exact ⟨_, Subtype.val_injective.comp h_inj.some.injective, fun i => h_inj.some i |>.2⟩
  refine' ⟨f, hf_inj.1, fun i => hmax _ _, fun i => _, fun i => _⟩ <;> simp_all [SimpleGraph.adj_comm]
  · simpa [SimpleGraph.adj_comm] using h_neighbors.1 (hf_inj.2 i)
  · intro h; have := h_neighbors.1 (hf_inj.2 i) ; simp_all
  · simpa [SimpleGraph.adj_comm] using h_neighbors.1 (hf_inj.2 i)

/-
**Theorem 1′ for `s = 1`.**  With min degree ≥ d, a maximal-path
    argument directly gives a `BollobasFan` with branch length 1.
-/
lemma bollobas_fan_of_minDeg_s_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : d ≥ 2)
    (hG : ∀ v : V, d ≤ G.degree v) :
    Nonempty (BollobasFan G d 1) := by
  obtain ⟨u, v, p, hp, hu, hv⟩ := exists_maximal_path G
  obtain ⟨f, hf_inj, hf_support, hf_ne_u, hf_adj⟩ := maximal_path_endpoint_neighbors_on_path G p hp hu d (hG u)
  rcases p with (_ | ⟨h, p⟩ ) <;> simp_all
  · exact False.elim (hf_support ⟨0, by linarith⟩ )
  · use u
    any_goals tauto
    · aesop
    · cases hp ; aesop
    · aesop
    · intro i j hij; contrapose! hij; aesop

/-!
### Tree-embedding and fan-construction helpers for `s ≥ 2`.

The proof of Theorem 1′ for `s ≥ 2` follows Bollobás:

1. Embed a complete `d`-ary tree of depth `s − 1` at a vertex `b`.
2. Choose the pair `(Q, T)` — path ending at `b`, tree at `b` in `G ∖ (Q ∖ {b})`
   — maximal among such pairs.
3. By maximality, for each first-level subtree `Tᵢ`, some leaf `cᵢ` has
   `< d^(s−1)` neighbours in `G ∖ (Q ∪ Tᵢ)`.
4. Degree-counting shows `cᵢ` has `≥ 1` neighbour on `Q ∖ {b}`.
5. Assemble: branch `Pᵢ = (b → · · · → cᵢ → eᵢ)` with `eᵢ ∈ Q ∖ {b}`,
   length `s`, meeting spine `Q ∖ {b}` only at `eᵢ`.

The intermediate lemmas below isolate each step of the argument.
-/

/--
A star of `d` vertex-disjoint paths from a common root, each of a prescribed
length, embedded in a graph `G`.  This represents the `d` tree-paths from the
root to representative leaves (one per first-level subtree) inside an embedded
complete `d`-ary tree.
-/
structure DisjointPathStar {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d len : ℕ) where
  root : V
  tip  : Fin d → V
  path : ∀ i, G.Walk root (tip i)
  path_isPath : ∀ i, (path i).IsPath
  path_length : ∀ i, (path i).length = len
  tips_ne_root : ∀ i, tip i ≠ root
  paths_internally_disjoint :
    ∀ i j, i ≠ j → ∀ v,
      v ∈ (path i).support → v ∈ (path j).support → v = root

/-
**Fan assembly.**  Given a star of `d` disjoint paths of length `s-1` from
a root, a separate path (the spine) not containing the root, and a witness
that each tip of the star has a neighbour on the spine, we can assemble a
`BollobasFan G d s`.

Each branch is:  `root → (arm of length s−1) → tip_i → e_i`,
where `e_i` is the tip’s neighbour on the spine.
-/
lemma fan_from_components
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V}
    {d s : ℕ} (hd : d ≥ 2) (hs : s ≥ 2)
    {u v : V}
    (P : G.Walk u v) (hP : P.IsPath)
    (S : DisjointPathStar G d (s - 1))
    (hS_disjoint : ∀ i, ∀ w ∈ (S.path i).support, w ∉ P.support)
    (connect : ∀ i : Fin d, ∃ e ∈ P.support, G.Adj (S.tip i) e) :
    Nonempty (BollobasFan G d s) := by
  revert S connect
  -- For each i, use Classical.choice/Exists.choose to pick e_i ∈ P.support and h_adj_i : G.Adj (S.tip i) e_i from (connect i).
  intro S hS_disjoint connect
  set e := fun i : Fin d => Classical.choose (connect i)
  set h_adj := fun i : Fin d => Classical.choose_spec (connect i)
  -- Construct the BollobasFan G d s from the given components.
  use S.root, u, v
  exact hS_disjoint ⟨0, by linarith⟩ _ (SimpleGraph.Walk.start_mem_support _)
  exact e
  exact fun i => h_adj i |>.1
  use fun i => (S.path i).append (SimpleGraph.Walk.cons (h_adj i |>.2) SimpleGraph.Walk.nil)
  · intro i
    have := S.path_isPath i
    simp_all [SimpleGraph.Walk.isPath_def]
    simp_all [SimpleGraph.Walk.support_append]
    grind
  · intro i; rw [SimpleGraph.Walk.length_append] ; simp [S.path_length] ; omega
  · intro i
    simp [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    rw [List.filter_eq_nil_iff.mpr] <;> aesop
  · intro i j hij v hv₁ hv₂
    simp_all [SimpleGraph.Walk.support_append]
    cases hv₁ <;> cases hv₂ <;> simp_all [SimpleGraph.Walk.isPath_def]
    have := S.paths_internally_disjoint i j hij v ‹_› ‹_›; aesop
  · intro i j hij h; have := h_adj i; have := h_adj j; simp_all [SimpleGraph.Walk.support_append]
    have := S.tips_ne_root i; have := S.tips_ne_root j; simp_all
    have := S.paths_internally_disjoint i j hij; simp_all

/-! ### Intermediate lemmas toward the fan construction

The proof of Theorem 1′ for `s ≥ 2` follows Bollobás (1977):

1. Embed a complete `d`-ary tree `T(d,s)` of depth `s−1` at a vertex `b`.
   The tree has `(d^s − 1)/(d − 1)` vertices.
2. Choose a maximal pair `(Q, T)` — path ending at `b`, tree at `b` in
   `G ∖ (Q ∖ {b})` — among such pairs.
3. By maximality, for each first-level subtree `Tᵢ`, some leaf `cᵢ` has
   `< d^(s−1)` neighbours in `G ∖ (Q ∪ Tᵢ)`.
4. Degree-counting shows `cᵢ` has `≥ 2` neighbours on `Q`,
   hence `≥ 1` on `Q ∖ {b}`.

Step 4 is the **Bollobás counting lemma** below.  Steps 1–3 are
formalized in §6 via the explicit `DAryTreeIndex` / `DAryTreeEmbedding`
machinery and the maximal-pair extraction.
-/

/-
**Bollobás counting lemma.**
In the notation of the proof, a selected leaf `cᵢ` satisfies:
  `degree(cᵢ) ≥ M := (d^s − 1)/(d − 1)`,
  `≤ (d^(s−1)−1)/(d−1) − 1` neighbours inside its subtree `Tᵢ`,
  `< d^(s−1)` neighbours outside `Q ∪ Tᵢ`.
Thus `cᵢ` has `≥ 2` neighbours on `Q`.
Since `b` accounts for at most `1`, `cᵢ` has `≥ 1` neighbour on `Q∖{b}`.
-/
lemma bollobas_counting (d s : ℕ) (hd : d ≥ 2) (hs : s ≥ 2) :
    2 ≤ fanTreeThreshold d s -
      ((fanTreeThreshold d (s - 1)) - 1) - (d ^ (s - 1) - 1) := by
  rw [Nat.sub_sub, le_tsub_iff_left]
  · rw [show fanTreeThreshold d s = (d ^ s - 1) / (d - 1) from rfl, show fanTreeThreshold d (s - 1) = (d ^ (s - 1) - 1) / (d - 1) from rfl]
    rw [show d ^ s - 1 = (d ^ (s - 1) - 1) * d + (d - 1) by zify ; cases d <;> cases s <;> norm_num [pow_succ' ] at * ; linarith]
    rw [Nat.le_div_iff_mul_le]
    · have hd1 : 1 ≤ d := by linarith
      have hd_minus_pos : 0 < d - 1 := Nat.sub_pos_of_lt hd
      have h_pow_ge : d ^ (s - 1) - 1 ≥ d - 1 :=
        Nat.le_sub_one_of_lt (lt_of_lt_of_le
          (Nat.sub_lt (by linarith) (by linarith))
          (Nat.le_self_pow (Nat.sub_ne_zero_of_lt hs) _))
      have h_div_pos : 1 ≤ (d ^ (s - 1) - 1) / (d - 1) :=
        Nat.div_pos h_pow_ge hd_minus_pos
      nlinarith [Nat.div_mul_le_self (d ^ (s - 1) - 1) (d - 1),
        Nat.sub_add_cancel h_div_pos, Nat.sub_add_cancel hd1]
    · exact Nat.sub_pos_of_lt hd
  · unfold fanTreeThreshold
    rcases s with (_ | _ | s) <;> simp_all [Nat.pow_succ' ]
    zify
    rw [Int.ofNat_sub]
    · rcases d with (_ | _ | d) <;> norm_num at *
      ring_nf
      rw [Int.le_ediv_iff_mul_le] <;>
        nlinarith [pow_pos (by linarith : 0 < (2 + d : ℤ)) s,
          Int.mul_ediv_add_emod (-1 + d * (2 + d) ^ s + (2 + d) ^ s * 2) (1 + d),
          Int.emod_nonneg (-1 + d * (2 + d) ^ s + (2 + d) ^ s * 2)
            (by linarith : (1 + d : ℤ) ≠ 0),
          Int.emod_lt_of_pos (-1 + d * (2 + d) ^ s + (2 + d) ^ s * 2)
            (by linarith : (1 + d : ℤ) > 0)]
    · exact Nat.div_pos (Nat.le_sub_one_of_lt (by nlinarith [Nat.sub_add_cancel (by linarith : 1 ≤ d), pow_pos (by linarith : 0 < d) s])) (Nat.sub_pos_of_lt hd)

lemma fanTreeThreshold_succ_sub_one (d n : ℕ) (hd : d ≥ 2) :
    fanTreeThreshold d (n + 1) - 1 = d * fanTreeThreshold d n := by
  rw [fanTreeThreshold, ← Nat.geomSum_eq hd]
  rw [fanTreeThreshold, ← Nat.geomSum_eq hd]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ] at ih
      rw [pow_succ]
      rw [Nat.mul_add]
      rw [Nat.mul_comm (d ^ n) d]
      have hA : 1 ≤ ∑ x ∈ Finset.range n, d ^ x + d ^ n := by
        exact Nat.succ_le_of_lt (Nat.add_pos_right _ (pow_pos (by omega : 0 < d) n))
      rw [Nat.sub_add_comm hA]
      rw [← ih]

lemma fanTreeThreshold_pos (d n : ℕ) (hd : d ≥ 2) :
    0 < fanTreeThreshold d (n + 1) := by
  rw [fanTreeThreshold, ← Nat.geomSum_eq hd]
  exact Finset.sum_pos (by intro k _; exact pow_pos (by omega : 0 < d) k)
    ⟨0, by simp⟩

lemma fanTreeThreshold_two (d : ℕ) (hd : d ≥ 2) :
    fanTreeThreshold d 2 = d + 1 := by
  rw [fanTreeThreshold, ← Nat.geomSum_eq hd]
  simp [Finset.sum_range_succ, Nat.add_comm]

lemma fanTreeThreshold_child_room (d n : ℕ) (hd : d ≥ 2) :
    fanTreeThreshold d (n + 1) + d ≤ fanTreeThreshold d (n + 2) := by
  have hsucc := fanTreeThreshold_succ_sub_one d (n + 1) hd
  have hpos : 0 < fanTreeThreshold d (n + 2) :=
    fanTreeThreshold_pos d (n + 1) hd
  have hsucc' : fanTreeThreshold d (n + 2) =
      d * fanTreeThreshold d (n + 1) + 1 := by
    have hsucc'' : fanTreeThreshold d (n + 2) - 1 =
        d * fanTreeThreshold d (n + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsucc
    omega
  rw [hsucc']
  have hnpos : 0 < fanTreeThreshold d (n + 1) :=
    fanTreeThreshold_pos d n hd
  nlinarith

lemma one_add_d_le_fanTreeThreshold_succ_succ (d n : ℕ) (hd : d ≥ 2) :
    1 + d ≤ fanTreeThreshold d (n + 2) := by
  have hroom := fanTreeThreshold_child_room d n hd
  have hpos : 0 < fanTreeThreshold d (n + 1) :=
    fanTreeThreshold_pos d n hd
  omega

lemma exists_injective_neighbors_not_mem {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : V} {forbidden : Finset V} {d : ℕ}
    (hdegree : forbidden.card + d ≤ G.degree x) :
    ∃ tip : Fin d → V,
      Function.Injective tip ∧
      (∀ i, G.Adj x (tip i)) ∧
      (∀ i, tip i ∉ forbidden) := by
  classical
  let available : Finset V := (G.neighborFinset x).filter fun y => y ∉ forbidden
  have hinside :
      ((G.neighborFinset x).filter fun y => y ∈ forbidden).card ≤ forbidden.card := by
    exact Finset.card_le_card (by
      intro y hy
      exact (Finset.mem_filter.mp hy).2)
  have hpartition :
      ((G.neighborFinset x).filter fun y => y ∈ forbidden).card + available.card =
        G.degree x := by
    change ((G.neighborFinset x).filter fun y => y ∈ forbidden).card +
        ((G.neighborFinset x).filter fun y => ¬ y ∈ forbidden).card = G.degree x
    rw [Finset.card_filter_add_card_filter_not]
    rfl
  have havailable : d ≤ available.card := by
    omega
  obtain ⟨t, ht⟩ := Finset.exists_subset_card_eq havailable
  obtain ⟨tip, htip⟩ :
      ∃ tip : Fin d → V, Function.Injective tip ∧ ∀ i, tip i ∈ t := by
    have h_equiv : Nonempty (Fin d ≃ t) := by
      exact ⟨Fintype.equivOfCardEq <| by simp [ht.2]⟩
    exact ⟨_, Subtype.val_injective.comp h_equiv.some.injective,
      fun i => h_equiv.some i |>.2⟩
  refine ⟨tip, htip.1, ?_, ?_⟩
  · intro i
    have hmem_available : tip i ∈ available := ht.1 (htip.2 i)
    exact (G.mem_neighborFinset x (tip i)).mp (Finset.mem_filter.mp hmem_available).1
  · intro i
    have hmem_available : tip i ∈ available := ht.1 (htip.2 i)
    exact (Finset.mem_filter.mp hmem_available).2

lemma exists_childRoots_avoiding_for_successor {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {d height : ℕ} (hd : d ≥ 2)
    {root : V} {forbidden : Finset V}
    (hroot : root ∉ forbidden)
    (hdegree : forbidden.card + fanTreeThreshold d (height + 2) ≤ G.degree root) :
    ∃ childRoot : Fin d → V,
      Function.Injective childRoot ∧
      (∀ i, G.Adj root (childRoot i)) ∧
      (∀ i, childRoot i ∉ insert root forbidden) := by
  have hcard_insert : (insert root forbidden).card = forbidden.card + 1 := by
    rw [Finset.card_insert_of_notMem hroot]
  have hroom :
      (insert root forbidden).card + d ≤ G.degree root := by
    rw [hcard_insert]
    have hthreshold : 1 + d ≤ fanTreeThreshold d (height + 2) :=
      one_add_d_le_fanTreeThreshold_succ_succ d height hd
    omega
  exact exists_injective_neighbors_not_mem
    (G := G) (x := root) (forbidden := insert root forbidden) (d := d) hroom

/-! ### Explicit complete `d`-ary tree indices -/

/--
Vertices of the complete rooted `d`-ary tree of height `height`.

A node is a depth `n ≤ height` together with its sequence of child choices
from the root, represented as a function `Fin n → Fin d`.  This is the
finite rooted tree structure missing from the coarse `FanComponentState`
abstraction below.
-/
@[ext] structure DAryTreeIndex (d height : ℕ) where
  depth : Fin (height + 1)
  coord : Fin depth.val → Fin d
deriving DecidableEq, Fintype

namespace DAryTreeIndex

/-- The root node, represented by the unique coordinate sequence of length `0`. -/
def root (d height : ℕ) : DAryTreeIndex d height :=
  { depth := ⟨0, by omega⟩
    coord := fun i => Fin.elim0 i }

/-- The `i`-th child of a non-leaf node. -/
def child {d height : ℕ} (x : DAryTreeIndex d height) (i : Fin d)
    (h : x.depth.val < height) : DAryTreeIndex d height :=
  { depth := ⟨x.depth.val + 1, by omega⟩
    coord := fun j =>
      if hj : j.val < x.depth.val then x.coord ⟨j.val, hj⟩ else i }

/-- The ancestor of `x` obtained by truncating its coordinate sequence to depth `n`. -/
def ancestor {d height : ℕ} (x : DAryTreeIndex d height) (n : ℕ)
    (h : n ≤ x.depth.val) : DAryTreeIndex d height :=
  { depth := ⟨n, by omega⟩
    coord := fun j => x.coord ⟨j.val, lt_of_lt_of_le j.isLt h⟩ }

@[simp] lemma root_depth (d height : ℕ) :
    (root d height).depth.val = 0 := rfl

@[simp] lemma child_depth {d height : ℕ} (x : DAryTreeIndex d height) (i : Fin d)
    (h : x.depth.val < height) :
    (child x i h).depth.val = x.depth.val + 1 := rfl

@[simp] lemma ancestor_depth {d height : ℕ} (x : DAryTreeIndex d height) (n : ℕ)
    (h : n ≤ x.depth.val) :
    (ancestor x n h).depth.val = n := rfl

lemma ancestor_self {d height : ℕ} (x : DAryTreeIndex d height)
    (h : x.depth.val ≤ x.depth.val := le_rfl) :
    ancestor x x.depth.val h = x := by
  cases x
  rfl

lemma ancestor_zero_eq_root {d height : ℕ} (x : DAryTreeIndex d height)
    (h : 0 ≤ x.depth.val := Nat.zero_le _) :
    ancestor x 0 h = root d height := by
  apply DAryTreeIndex.ext
  · rfl
  · exact heq_of_eq (by
      funext j
      exact Fin.elim0 j)

lemma eq_root_of_depth_eq_zero {d height : ℕ} (x : DAryTreeIndex d height)
    (h : x.depth.val = 0) :
    x = root d height := by
  cases x with
  | mk depth coord =>
      cases depth with
      | mk n hn =>
          simp at h
          subst n
          apply DAryTreeIndex.ext
          · rfl
          · exact heq_of_eq (by
              funext j
              exact Fin.elim0 j)

lemma height_one_eq_root_or_child {d : ℕ} (x : DAryTreeIndex d 1) :
    x = root d 1 ∨ ∃ i : Fin d, x = child (root d 1) i (by simp [root]) := by
  rcases x with ⟨⟨n, hn⟩, coord⟩
  interval_cases n
  · exact Or.inl (eq_root_of_depth_eq_zero _ rfl)
  · refine Or.inr ?_
    let i : Fin d := coord ⟨0, by simp⟩
    refine ⟨i, ?_⟩
    apply DAryTreeIndex.ext
    · rfl
    · exact heq_of_eq (by
        funext j
        have hj0 : j.val = 0 := by omega
        have hj : j = ⟨0, by simp⟩ := Fin.ext hj0
        simp [child, root, i, hj])

lemma height_zero_eq_root {d : ℕ} (x : DAryTreeIndex d 0) :
    x = root d 0 := by
  apply eq_root_of_depth_eq_zero
  have hxlt : x.depth.val < 1 := x.depth.isLt
  omega

@[simp] lemma child_coord_of_lt {d height : ℕ}
    (x : DAryTreeIndex d height) (i : Fin d)
    (h : x.depth.val < height) (j : Fin x.depth.val) :
    (child x i h).coord ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self _)⟩ =
      x.coord j := by
  simp [child]

@[simp] lemma child_coord_last {d height : ℕ}
    (x : DAryTreeIndex d height) (i : Fin d)
    (h : x.depth.val < height) :
    (child x i h).coord ⟨x.depth.val, by simp [child]⟩ = i := by
  simp [child]

/-- A canonical leaf in the first-level branch labelled by `i`.
All later coordinates are also chosen to be `i`; only the first coordinate
matters for separating different first-level branches. -/
def branchLeaf {d : ℕ} (height : ℕ) (i : Fin d) : DAryTreeIndex d height :=
  { depth := ⟨height, by omega⟩
    coord := fun _ => i }

@[simp] lemma branchLeaf_depth {d height : ℕ} (i : Fin d) :
    (branchLeaf height i).depth.val = height := rfl

@[simp] lemma branchLeaf_coord {d height : ℕ} (i : Fin d) (j : Fin height) :
    (branchLeaf height i).coord j = i := rfl

lemma branchLeaf_ne_root {d height : ℕ} (i : Fin d) (hheight : 0 < height) :
    branchLeaf height i ≠ root d height := by
  intro hEq
  have hdepth := congrArg (fun x : DAryTreeIndex d height => x.depth.val) hEq
  simp [branchLeaf, root] at hdepth
  omega

lemma ancestor_branchLeaf_first_coord {d height : ℕ} (i : Fin d)
    {m : ℕ} (hm : m ≤ height) (hmpos : 0 < m) :
    (ancestor (branchLeaf height i) m hm).coord ⟨0, by simp [ancestor]; exact hmpos⟩ = i := by
  simp [ancestor, branchLeaf]

/-- Prefix a node of a height `height - 1` tree by a fixed first child choice. -/
def consFirst {d height : ℕ} (i : Fin d) (y : DAryTreeIndex d (height - 1))
    (hheight : 0 < height) : DAryTreeIndex d height :=
  { depth := ⟨y.depth.val + 1, by
      have hy : y.depth.val < height := by
        have := y.depth.isLt
        omega
      omega⟩
    coord := fun j =>
      if hj : j.val = 0 then i else
        y.coord ⟨j.val - 1, by
          have hjlt : j.val < y.depth.val + 1 := j.isLt
          have hjpos : 0 < j.val := by omega
          omega⟩ }

/-- Drop the first coordinate from a non-root node. -/
def tail {d height : ℕ} (x : DAryTreeIndex d height)
    (hpos : 0 < x.depth.val) : DAryTreeIndex d (height - 1) :=
  { depth := ⟨x.depth.val - 1, by
      have hxlt : x.depth.val < height + 1 := x.depth.isLt
      omega⟩
    coord := fun j =>
      x.coord ⟨j.val + 1, by
        have hjlt : j.val < x.depth.val - 1 := j.isLt
        omega⟩ }

@[simp] lemma consFirst_depth {d height : ℕ} (i : Fin d)
    (y : DAryTreeIndex d (height - 1)) (hheight : 0 < height) :
    (consFirst i y hheight).depth.val = y.depth.val + 1 := rfl

@[simp] lemma tail_depth {d height : ℕ} (x : DAryTreeIndex d height)
    (hpos : 0 < x.depth.val) :
    (tail x hpos).depth.val = x.depth.val - 1 := rfl

@[simp] lemma consFirst_first_coord {d height : ℕ} (i : Fin d)
    (y : DAryTreeIndex d (height - 1)) (hheight : 0 < height) :
    (consFirst i y hheight).coord ⟨0, by simp [consFirst]⟩ = i := by
  simp [consFirst]

lemma tail_consFirst {d height : ℕ} (i : Fin d) (y : DAryTreeIndex d (height - 1))
    (hheight : 0 < height) :
    tail (consFirst i y hheight) (by simp) = y := by
  apply DAryTreeIndex.ext
  · simp [tail, consFirst]
  · exact heq_of_eq (by
      funext j
      simp [tail, consFirst])

lemma child_first_coord_of_pos {d height : ℕ} (x : DAryTreeIndex d height)
    (i : Fin d) (hchild : x.depth.val < height) (hpos : 0 < x.depth.val) :
    (child x i hchild).coord ⟨0, by simp [child]⟩ =
      x.coord ⟨0, hpos⟩ := by
  simp [child, hpos]

lemma consFirst_injective {d height : ℕ} (i : Fin d) (hheight : 0 < height) :
    Function.Injective (fun y : DAryTreeIndex d (height - 1) => consFirst i y hheight) := by
  intro y z hyz
  rw [← tail_consFirst i y hheight, ← tail_consFirst i z hheight]
  congr

/-- A convenient sigma-form equivalence for cardinality and induction work. -/
def equivSigma (d height : ℕ) :
    DAryTreeIndex d height ≃ Σ n : Fin (height + 1), (Fin n.val → Fin d) where
  toFun x := ⟨x.depth, x.coord⟩
  invFun y := { depth := y.1, coord := y.2 }
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl

lemma consFirst_tail {d height : ℕ} (x : DAryTreeIndex d height)
    (hheight : 0 < height) (hpos : 0 < x.depth.val) :
    consFirst (x.coord ⟨0, hpos⟩) (tail x hpos) hheight = x := by
  rcases x with ⟨⟨n, hn⟩, coord⟩
  cases n with
  | zero =>
      simp at hpos
  | succ m =>
      apply DAryTreeIndex.ext
      · rfl
      · exact heq_of_eq (by
          funext j
          by_cases hj0 : j.val = 0
          · have hj : j = ⟨0, by simp⟩ := Fin.ext hj0
            simp [consFirst, tail, hj]
          · have hjpos : 0 < j.val := by omega
            have hjlt : j.val < m + 1 := by
              simpa [consFirst, tail] using j.isLt
            have hidx :
                (⟨j.val - 1 + 1, by
                  omega⟩ : Fin (m + 1)) = ⟨j.val, hjlt⟩ := by
              apply Fin.ext
              exact Nat.sub_add_cancel hjpos
            simp [consFirst, tail, hj0, hidx])

lemma eq_consFirst_of_pos {d height : ℕ} (x : DAryTreeIndex d height)
    (hheight : 0 < height) (hpos : 0 < x.depth.val) :
    x = consFirst (x.coord ⟨0, hpos⟩) (tail x hpos) hheight := by
  exact (consFirst_tail x hheight hpos).symm

lemma tail_child_of_pos {d height : ℕ} (x : DAryTreeIndex d height)
    (i : Fin d) (hchild : x.depth.val < height) (hpos : 0 < x.depth.val) :
    tail (child x i hchild) (by simp [child]) =
      child (tail x hpos) i (by simp [tail]; omega) := by
  rcases x with ⟨⟨n, hn⟩, coord⟩
  cases n with
  | zero =>
      simp at hpos
  | succ m =>
      apply DAryTreeIndex.ext
      · rfl
      · exact heq_of_eq (by
          funext j
          simp [tail, child])

lemma card_eq_sum_pow (d height : ℕ) :
    Fintype.card (DAryTreeIndex d height) = ∑ n : Fin (height + 1), d ^ n.val := by
  rw [Fintype.card_congr (equivSigma d height)]
  rw [Fintype.card_sigma]
  simp

/-- The complete `d`-ary tree of height `height` has the expected size. -/
lemma card_eq_threshold (d height : ℕ) (hd : d ≥ 2) :
    Fintype.card (DAryTreeIndex d height) = fanTreeThreshold d (height + 1) := by
  rw [card_eq_sum_pow, fanTreeThreshold, ← Nat.geomSum_eq hd]
  exact Fin.sum_univ_eq_sum_range (fun n => d ^ n) (height + 1)

end DAryTreeIndex

/--
An embedding of a complete rooted `d`-ary tree of height `height` into a graph.
This is intentionally just the tree object: it does not mention the spine `Q`.
The Bollobás maximal-pair state should eventually carry one of these rather
than an unstructured `Finset` of tree vertices.
-/
structure DAryTreeEmbedding {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d height : ℕ) where
  root : V
  vertex : DAryTreeIndex d height → V
  root_eq : vertex (DAryTreeIndex.root d height) = root
  injective : Function.Injective vertex
  adj_child :
    ∀ (x : DAryTreeIndex d height) (i : Fin d) (h : x.depth.val < height),
      G.Adj (vertex x) (vertex (DAryTreeIndex.child x i h))

namespace DAryTreeEmbedding

/-- All vertices of an embedded tree avoid a forbidden finite set. -/
def Avoids {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (forbidden : Finset V) : Prop :=
  ∀ x : DAryTreeIndex d height, T.vertex x ∉ forbidden

/-- The unique height-zero complete tree embedded at a chosen root vertex. -/
def heightZeroOfVertex {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (v : V) :
    DAryTreeEmbedding G d 0 where
  root := v
  vertex := fun _ => v
  root_eq := rfl
  injective := by
    intro x y _h
    rw [DAryTreeIndex.height_zero_eq_root x, DAryTreeIndex.height_zero_eq_root y]
  adj_child := by
    intro x i hx
    omega

lemma heightZeroOfVertex_avoids {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} {v : V} {forbidden : Finset V}
    (hv : v ∉ forbidden) :
    (heightZeroOfVertex (G := G) (d := d) v).Avoids forbidden := by
  intro x
  simpa [Avoids, heightZeroOfVertex] using hv

/-- The vertex map for a height-one embedded tree with root `v` and children
`tip i`. -/
def heightOneVertex {V : Type*} {d : ℕ}
    (v : V) (tip : Fin d → V) (x : DAryTreeIndex d 1) : V :=
  if h : x.depth.val = 0 then v
  else tip (x.coord ⟨0, by
    have hxlt : x.depth.val < 2 := x.depth.isLt
    omega⟩)

@[simp] lemma heightOneVertex_root {V : Type*} {d : ℕ}
    (v : V) (tip : Fin d → V) :
    heightOneVertex v tip (DAryTreeIndex.root d 1) = v := by
  simp [heightOneVertex, DAryTreeIndex.root]

@[simp] lemma heightOneVertex_child_root {V : Type*} {d : ℕ}
    (v : V) (tip : Fin d → V) (i : Fin d) :
    heightOneVertex v tip
      (DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])) =
      tip i := by
  simp [heightOneVertex, DAryTreeIndex.child, DAryTreeIndex.root]

/-- Build a height-one complete `d`-ary tree from `d` distinct neighbours of
the root. -/
def heightOneOfChildren {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (v : V) (tip : Fin d → V)
    (htip_inj : Function.Injective tip)
    (hadj : ∀ i, G.Adj v (tip i)) :
    DAryTreeEmbedding G d 1 where
  root := v
  vertex := heightOneVertex v tip
  root_eq := by simp
  injective := by
    intro x y hxy
    rcases DAryTreeIndex.height_one_eq_root_or_child x with hx | ⟨i, hx⟩
    · rcases DAryTreeIndex.height_one_eq_root_or_child y with hy | ⟨j, hy⟩
      · rw [hx, hy]
      · exfalso
        have hvtip : v = tip j := by simpa [hx, hy] using hxy
        exact (hadj j).ne hvtip
    · rcases DAryTreeIndex.height_one_eq_root_or_child y with hy | ⟨j, hy⟩
      · exfalso
        have htipv : tip i = v := by simpa [hx, hy] using hxy
        exact (hadj i).ne htipv.symm
      · have hij : i = j := htip_inj (by simpa [hx, hy] using hxy)
        rw [hx, hy, hij]
  adj_child := by
    intro x i hx
    have hxroot : x = DAryTreeIndex.root d 1 := by
      apply DAryTreeIndex.eq_root_of_depth_eq_zero
      omega
    simpa [hxroot] using hadj i

/-- A vertex of degree at least `d` supports a height-one embedded complete
`d`-ary tree. -/
lemma exists_heightOneOfDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) (hv : d ≤ G.degree v) :
    ∃ T : DAryTreeEmbedding G d 1, T.root = v := by
  obtain ⟨t, ht⟩ : ∃ t : Finset V, t.card = d ∧ ∀ w ∈ t, G.Adj v w := by
    exact Exists.elim (Finset.exists_subset_card_eq hv) fun t ht =>
      ⟨_, ht.2, fun w hw => by simpa using ht.1 hw⟩
  obtain ⟨tip, htip⟩ : ∃ tip : Fin d → V, Function.Injective tip ∧ ∀ i, tip i ∈ t := by
    have h_equiv : Nonempty (Fin d ≃ t) := by
      exact ⟨Fintype.equivOfCardEq <| by simp [ht.1]⟩
    exact ⟨_, Subtype.val_injective.comp h_equiv.some.injective,
      fun i => h_equiv.some i |>.2⟩
  refine ⟨heightOneOfChildren v tip htip.1 (fun i => ht.2 _ (htip.2 i)), rfl⟩

/-- The image of the embedded tree as a finite vertex set. -/
def vertexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) :
    Finset V :=
  Finset.univ.image T.vertex

lemma heightOneOfChildren_vertexFinset_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (v : V) (tip : Fin d → V)
    (htip_inj : Function.Injective tip) (hadj : ∀ i, G.Adj v (tip i)) :
    (heightOneOfChildren (G := G) v tip htip_inj hadj).vertexFinset =
      insert v (Finset.univ.image tip) := by
  ext w
  constructor
  · intro hw
    rw [vertexFinset] at hw
    rcases Finset.mem_image.mp hw with ⟨x, _hx, rfl⟩
    rcases DAryTreeIndex.height_one_eq_root_or_child x with hx | ⟨i, hx⟩
    · simp [hx, heightOneOfChildren]
    · simp [hx, heightOneOfChildren]
  · intro hw
    rw [Finset.mem_insert] at hw
    rw [vertexFinset]
    rcases hw with rfl | hw
    · refine Finset.mem_image.mpr ?_
      exact ⟨DAryTreeIndex.root d 1, Finset.mem_univ _, by simp [heightOneOfChildren]⟩
    · rcases Finset.mem_image.mp hw with ⟨i, _hi, rfl⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨DAryTreeIndex.child (DAryTreeIndex.root d 1) i
        (by simp [DAryTreeIndex.root]), Finset.mem_univ _, ?_⟩
      simp [heightOneOfChildren]

lemma heightOne_vertexFinset_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (T : DAryTreeEmbedding G d 1) :
    T.vertexFinset =
      insert T.root (Finset.univ.image fun i : Fin d =>
        T.vertex (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
          (by simp [DAryTreeIndex.root]))) := by
  ext w
  constructor
  · intro hw
    rw [vertexFinset] at hw
    rcases Finset.mem_image.mp hw with ⟨x, _hx, rfl⟩
    rcases DAryTreeIndex.height_one_eq_root_or_child x with hx | ⟨i, hx⟩
    · rw [hx, T.root_eq]
      exact Finset.mem_insert_self _ _
    · rw [hx]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · intro hw
    rw [Finset.mem_insert] at hw
    rw [vertexFinset]
    rcases hw with hwroot | hwchild
    · rw [hwroot, ← T.root_eq]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · rcases Finset.mem_image.mp hwchild with ⟨i, _hi, rfl⟩
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma root_mem_vertexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) :
    T.root ∈ T.vertexFinset := by
  rw [← T.root_eq]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma vertex_mem_vertexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    T.vertex x ∈ T.vertexFinset := by
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma vertexFinset_disjoint_forbidden_of_avoids {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    {forbidden : Finset V} (havoid : T.Avoids forbidden) :
    Disjoint T.vertexFinset forbidden := by
  rw [Finset.disjoint_left]
  intro v hv hforbidden
  rw [vertexFinset] at hv
  rcases Finset.mem_image.mp hv with ⟨x, -, rfl⟩
  exact havoid x hforbidden

lemma avoids_of_vertexFinset_disjoint_forbidden {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    {forbidden : Finset V} (hdisj : Disjoint T.vertexFinset forbidden) :
    T.Avoids forbidden := by
  intro x hx
  rw [Finset.disjoint_left] at hdisj
  exact hdisj (T.vertex_mem_vertexFinset x) hx

lemma avoids_iff_vertexFinset_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (forbidden : Finset V) :
    T.Avoids forbidden ↔ Disjoint T.vertexFinset forbidden := by
  exact ⟨T.vertexFinset_disjoint_forbidden_of_avoids,
    T.avoids_of_vertexFinset_disjoint_forbidden⟩

/-- Data needed to assemble a height-successor embedded complete tree from
`d` rooted child subtrees.  The constructor proof is deliberately separated
from this data so that the recursive existence argument can first build and
reason about the finite family of child subtrees. -/
structure RootedChildSubtreeFamily {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d height : ℕ) where
  root : V
  childRoot : Fin d → V
  childTree : Fin d → DAryTreeEmbedding G d height
  childTree_root : ∀ i, (childTree i).root = childRoot i
  root_adj_child : ∀ i, G.Adj root (childRoot i)
  root_not_mem_child : ∀ i, root ∉ (childTree i).vertexFinset
  child_disjoint :
    ∀ {i j : Fin d}, i ≠ j →
      Disjoint (childTree i).vertexFinset (childTree j).vertexFinset

namespace RootedChildSubtreeFamily

def vertex {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height)
    (x : DAryTreeIndex d (height + 1)) : V :=
  if hroot : x.depth.val = 0 then F.root
  else
    (F.childTree (x.coord ⟨0, by omega⟩)).vertex
      (DAryTreeIndex.tail x (by omega))

@[simp] lemma vertex_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height) :
    F.vertex (DAryTreeIndex.root d (height + 1)) = F.root := by
  simp [vertex, DAryTreeIndex.root]

lemma child_root_tail_eq_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (_F : RootedChildSubtreeFamily G d height) (i : Fin d) :
    DAryTreeIndex.tail
        (DAryTreeIndex.child (DAryTreeIndex.root d (height + 1)) i
          (by simp [DAryTreeIndex.root]))
        (by simp [DAryTreeIndex.child, DAryTreeIndex.root]) =
      DAryTreeIndex.root d height := by
  apply DAryTreeIndex.eq_root_of_depth_eq_zero
  simp [DAryTreeIndex.tail, DAryTreeIndex.child, DAryTreeIndex.root]

@[simp] lemma vertex_child_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height) (i : Fin d) :
    F.vertex
        (DAryTreeIndex.child (DAryTreeIndex.root d (height + 1)) i
          (by simp [DAryTreeIndex.root])) =
      F.childRoot i := by
  rw [vertex]
  simp only [DAryTreeIndex.child_depth, Nat.succ_ne_zero, ↓reduceDIte]
  rw [child_root_tail_eq_root F i]
  exact (F.childTree i).root_eq.trans (F.childTree_root i)

lemma root_adj_child_vertex {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height) (i : Fin d) :
    G.Adj (F.vertex (DAryTreeIndex.root d (height + 1)))
      (F.vertex
        (DAryTreeIndex.child (DAryTreeIndex.root d (height + 1)) i
          (by simp [DAryTreeIndex.root]))) := by
  simpa using F.root_adj_child i

lemma vertex_mem_childTree_of_pos {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height)
    (x : DAryTreeIndex d (height + 1)) (hpos : 0 < x.depth.val) :
    F.vertex x ∈
      (F.childTree (x.coord ⟨0, hpos⟩)).vertexFinset := by
  rw [vertex]
  simp only [show ¬ x.depth.val = 0 by omega, ↓reduceDIte]
  exact (F.childTree (x.coord ⟨0, hpos⟩)).vertex_mem_vertexFinset
    (DAryTreeIndex.tail x hpos)

lemma root_ne_vertex_of_pos {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height)
    (x : DAryTreeIndex d (height + 1)) (hpos : 0 < x.depth.val) :
    F.root ≠ F.vertex x := by
  intro hEq
  have hmem :
      F.root ∈ (F.childTree (x.coord ⟨0, hpos⟩)).vertexFinset := by
    simpa [hEq] using F.vertex_mem_childTree_of_pos x hpos
  exact F.root_not_mem_child (x.coord ⟨0, hpos⟩) hmem

lemma vertex_ne_root_of_pos {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height)
    (x : DAryTreeIndex d (height + 1)) (hpos : 0 < x.depth.val) :
    F.vertex x ≠ F.root := by
  exact (F.root_ne_vertex_of_pos x hpos).symm

lemma first_coord_eq_of_nonroot_vertex_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height)
    {x y : DAryTreeIndex d (height + 1)}
    (hxpos : 0 < x.depth.val) (hypos : 0 < y.depth.val)
    (hxy : F.vertex x = F.vertex y) :
    x.coord ⟨0, hxpos⟩ = y.coord ⟨0, hypos⟩ := by
  by_contra hne
  have hxmem := F.vertex_mem_childTree_of_pos x hxpos
  have hymem : F.vertex x ∈
      (F.childTree (y.coord ⟨0, hypos⟩)).vertexFinset := by
    simpa [hxy] using F.vertex_mem_childTree_of_pos y hypos
  have hdisj := F.child_disjoint hne
  rw [Finset.disjoint_left] at hdisj
  exact hdisj hxmem hymem

/-- Assemble a rooted family of pairwise disjoint child embeddings into the
successor-height complete embedded tree. -/
def toEmbedding {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height) :
    DAryTreeEmbedding G d (height + 1) where
  root := F.root
  vertex := F.vertex
  root_eq := F.vertex_root
  injective := by
    intro x y hxy
    by_cases hxzero : x.depth.val = 0
    · have hxroot : x = DAryTreeIndex.root d (height + 1) :=
        DAryTreeIndex.eq_root_of_depth_eq_zero x hxzero
      by_cases hyzero : y.depth.val = 0
      · have hyroot : y = DAryTreeIndex.root d (height + 1) :=
          DAryTreeIndex.eq_root_of_depth_eq_zero y hyzero
        rw [hxroot, hyroot]
      · have hypos : 0 < y.depth.val := by omega
        exfalso
        exact F.root_ne_vertex_of_pos y hypos (by
          simpa [hxroot] using hxy)
    · have hxpos : 0 < x.depth.val := by omega
      by_cases hyzero : y.depth.val = 0
      · have hyroot : y = DAryTreeIndex.root d (height + 1) :=
          DAryTreeIndex.eq_root_of_depth_eq_zero y hyzero
        exfalso
        exact F.vertex_ne_root_of_pos x hxpos (by
          simpa [hyroot] using hxy)
      · have hypos : 0 < y.depth.val := by omega
        have hfirst :
            x.coord ⟨0, hxpos⟩ = y.coord ⟨0, hypos⟩ :=
          F.first_coord_eq_of_nonroot_vertex_eq hxpos hypos hxy
        have htail :
            DAryTreeIndex.tail x hxpos = DAryTreeIndex.tail y hypos := by
          have hvertex :
              (F.childTree (x.coord ⟨0, hxpos⟩)).vertex
                  (DAryTreeIndex.tail x hxpos) =
                (F.childTree (x.coord ⟨0, hxpos⟩)).vertex
                  (DAryTreeIndex.tail y hypos) := by
            have hxv :
                F.vertex x =
                  (F.childTree (x.coord ⟨0, hxpos⟩)).vertex
                    (DAryTreeIndex.tail x hxpos) := by
              rw [RootedChildSubtreeFamily.vertex]
              rw [dif_neg (show ¬ x.depth.val = 0 by omega)]
            have hyv :
                F.vertex y =
                  (F.childTree (y.coord ⟨0, hypos⟩)).vertex
                    (DAryTreeIndex.tail y hypos) := by
              rw [RootedChildSubtreeFamily.vertex]
              rw [dif_neg (show ¬ y.depth.val = 0 by omega)]
            rw [hxv, hyv] at hxy
            simpa [hfirst] using hxy
          exact (F.childTree (x.coord ⟨0, hxpos⟩)).injective hvertex
        rw [DAryTreeIndex.eq_consFirst_of_pos x (Nat.succ_pos height) hxpos,
          DAryTreeIndex.eq_consFirst_of_pos y (Nat.succ_pos height) hypos,
          hfirst, htail]
  adj_child := by
    intro x i hchild
    by_cases hxzero : x.depth.val = 0
    · have hxroot : x = DAryTreeIndex.root d (height + 1) :=
        DAryTreeIndex.eq_root_of_depth_eq_zero x hxzero
      have hchild_root :
          DAryTreeIndex.child x i hchild =
            DAryTreeIndex.child (DAryTreeIndex.root d (height + 1)) i
              (by simp [DAryTreeIndex.root]) := by
        subst x
        rfl
      simpa [hxroot, hchild_root] using F.root_adj_child_vertex i
    · have hxpos : 0 < x.depth.val := by omega
      have hfirst :
          (DAryTreeIndex.child x i hchild).coord
              ⟨0, by simp [DAryTreeIndex.child]⟩ =
            x.coord ⟨0, hxpos⟩ :=
        DAryTreeIndex.child_first_coord_of_pos x i hchild hxpos
      have hfirst0 :
          (DAryTreeIndex.child x i hchild).coord
              ⟨0, by simp [DAryTreeIndex.child]⟩ =
            x.coord ⟨0, hxpos⟩ := by
        simpa using hfirst
      have htail :
          DAryTreeIndex.tail (DAryTreeIndex.child x i hchild)
              (by simp [DAryTreeIndex.child]) =
            DAryTreeIndex.child (DAryTreeIndex.tail x hxpos) i
              (by simp [DAryTreeIndex.tail]; omega) :=
        DAryTreeIndex.tail_child_of_pos x i hchild hxpos
      have hadj :
          G.Adj
            ((F.childTree (x.coord ⟨0, hxpos⟩)).vertex
              (DAryTreeIndex.tail x hxpos))
            ((F.childTree (x.coord ⟨0, hxpos⟩)).vertex
              (DAryTreeIndex.child (DAryTreeIndex.tail x hxpos) i
                (by simp [DAryTreeIndex.tail]; omega))) :=
        (F.childTree (x.coord ⟨0, hxpos⟩)).adj_child
          (DAryTreeIndex.tail x hxpos) i (by simp [DAryTreeIndex.tail]; omega)
      have hxv :
          F.vertex x =
            (F.childTree (x.coord ⟨0, hxpos⟩)).vertex
              (DAryTreeIndex.tail x hxpos) := by
        rw [RootedChildSubtreeFamily.vertex]
        rw [dif_neg (show ¬ x.depth.val = 0 by omega)]
      have hchildv :
          F.vertex (DAryTreeIndex.child x i hchild) =
            (F.childTree (x.coord ⟨0, hxpos⟩)).vertex
              (DAryTreeIndex.child (DAryTreeIndex.tail x hxpos) i
                (by simp [DAryTreeIndex.tail]; omega)) := by
        rw [RootedChildSubtreeFamily.vertex]
        rw [dif_neg (show ¬ (DAryTreeIndex.child x i hchild).depth.val = 0 by
          simp [DAryTreeIndex.child])]
        rw [htail]
        exact congrArg
          (fun k : Fin d =>
            (F.childTree k).vertex
              (DAryTreeIndex.child (DAryTreeIndex.tail x hxpos) i
                (by simp [DAryTreeIndex.tail]; omega)))
          hfirst0
      rw [hxv, hchildv]
      exact hadj

@[simp] lemma toEmbedding_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height) :
    F.toEmbedding.root = F.root := rfl

@[simp] lemma toEmbedding_vertex {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height)
    (x : DAryTreeIndex d (height + 1)) :
    F.toEmbedding.vertex x = F.vertex x := rfl

lemma toEmbedding_avoids {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ}
    (F : RootedChildSubtreeFamily G d height) {forbidden : Finset V}
    (hroot : F.root ∉ forbidden)
    (hchild : ∀ i, (F.childTree i).Avoids forbidden) :
    F.toEmbedding.Avoids forbidden := by
  intro x
  change F.vertex x ∉ forbidden
  by_cases hzero : x.depth.val = 0
  · simpa [vertex, hzero] using hroot
  · have hpos : 0 < x.depth.val := by omega
    rw [vertex, dif_neg hzero]
    exact hchild (x.coord ⟨0, hpos⟩) (DAryTreeIndex.tail x hpos)
end RootedChildSubtreeFamily

lemma vertexFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) :
    T.vertexFinset.card = Fintype.card (DAryTreeIndex d height) := by
  rw [vertexFinset, Finset.card_image_of_injective _ T.injective, Finset.card_univ]

lemma heightOne_child_image_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (T : DAryTreeEmbedding G d 1) :
    (Finset.univ.image fun i : Fin d =>
      T.vertex (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
        (by simp [DAryTreeIndex.root]))).card = d := by
  let childImage : Finset V :=
    Finset.univ.image fun i : Fin d =>
      T.vertex (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
        (by simp [DAryTreeIndex.root]))
  have htree : T.vertexFinset = insert T.root childImage := by
    simpa [childImage] using heightOne_vertexFinset_eq T
  have hroot_not : T.root ∉ childImage := by
    intro hroot
    rcases Finset.mem_image.mp hroot with ⟨i, _hi, hi⟩
    let child : DAryTreeIndex d 1 :=
      DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
    have hadj : G.Adj T.root (T.vertex child) := by
      rw [← T.root_eq]
      exact T.adj_child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
    exact hadj.ne (by simpa [child] using hi.symm)
  have hcard_insert : (insert T.root childImage).card = childImage.card + 1 := by
    rw [Finset.card_insert_of_notMem hroot_not, Nat.add_comm]
  have hcard_tree : T.vertexFinset.card = d + 1 := by
    rw [T.vertexFinset_card, DAryTreeIndex.card_eq_sum_pow]
    simp
    omega
  have hcard_child_succ : childImage.card + 1 = d + 1 := by
    calc
      childImage.card + 1 = (insert T.root childImage).card := hcard_insert.symm
      _ = T.vertexFinset.card := by rw [htree]
      _ = d + 1 := hcard_tree
  exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hcard_child_succ)

lemma vertexFinset_card_threshold {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (hd : d ≥ 2) :
    T.vertexFinset.card = fanTreeThreshold d (height + 1) := by
  rw [T.vertexFinset_card, DAryTreeIndex.card_eq_threshold d height hd]

/-- Running state of the greedy `(d, h)`-subtree construction below: the first
`n` of `d` child subtrees, with their disjointness invariants. -/
private structure PartialChildSubtrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d h : ℕ)
    (forbiddenAfter : Finset V) (childRoot : Fin d → V) (n : ℕ) where
  subtree : (i : ℕ) → (hi : i < n) → DAryTreeEmbedding G d h
  root_matches : ∀ (i : ℕ) (hi : i < n) (hin : i < d),
      (subtree i hi).root = childRoot ⟨i, hin⟩
  avoids :
    ∀ (i : ℕ) (hi : i < n) (hin : i < d),
      (subtree i hi).Avoids
        (forbiddenAfter ∪ ((Finset.univ.image childRoot).erase (childRoot ⟨i, hin⟩)))
  pairwise :
    ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i ≠ j →
      Disjoint (subtree i hi).vertexFinset (subtree j hj).vertexFinset

/-- **Greedy tree growth.**  If every vertex of `G` has degree at least
`forbidden.card + fanTreeThreshold d (height + 1)`, then for any choice of
`root` outside `forbidden` we can embed a complete `d`-ary tree of `height`
rooted at `root` and avoiding `forbidden`.

This is the inductive Bollobás tree-construction step.  The proof inducts on
`height`; the inductive step picks `d` fresh children of `root` via
`exists_childRoots_avoiding_for_successor`, then sequentially builds each child
subtree.  The arithmetic
`fanTreeThreshold d (h + 2) = d * fanTreeThreshold d (h + 1) + 1` provides
exactly the room needed for the recursion's forbidden-set inflation. -/
lemma exists_DAryTreeEmbedding_avoiding_of_minDeg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : d ≥ 2) :
    ∀ (height : ℕ) (root : V) (forbidden : Finset V),
      root ∉ forbidden →
      (∀ v : V, forbidden.card + fanTreeThreshold d (height + 1) ≤ G.degree v) →
      ∃ T : DAryTreeEmbedding G d height,
        T.root = root ∧ T.Avoids forbidden := by
  intro height
  induction height with
  | zero =>
      intro root forbidden hroot _hdeg
      exact ⟨heightZeroOfVertex (G := G) (d := d) root, rfl,
        heightZeroOfVertex_avoids hroot⟩
  | succ h ih =>
      intro root forbidden hroot hdeg
      have hdeg_root :
          forbidden.card + fanTreeThreshold d (h + 2) ≤ G.degree root := hdeg root
      obtain ⟨childRoot, hchildRoot_inj, hchildRoot_adj, hchildRoot_fresh⟩ :=
        exists_childRoots_avoiding_for_successor (G := G) (d := d) (height := h) hd
          (root := root) (forbidden := forbidden) hroot hdeg_root
      set allChildRoots : Finset V := Finset.univ.image childRoot with hallChildRoots_def
      have hallChildRoots_card : allChildRoots.card = d := by
        rw [hallChildRoots_def, Finset.card_image_of_injective _ hchildRoot_inj]
        simp
      set forbiddenAfter : Finset V := insert root forbidden with hforbiddenAfter_def
      have hforbiddenAfter_card : forbiddenAfter.card = forbidden.card + 1 := by
        rw [hforbiddenAfter_def, Finset.card_insert_of_notMem hroot]
      -- Build the partial state up to any n ≤ d.
      have key : ∀ n : ℕ, n ≤ d →
          Nonempty (PartialChildSubtrees G d h forbiddenAfter childRoot n) := by
        intro n hn
        induction n with
        | zero =>
            refine ⟨⟨fun i hi => absurd hi (by omega), ?_, ?_, ?_⟩⟩
            · intro i hi; exact absurd hi (by omega)
            · intro i hi; exact absurd hi (by omega)
            · intro i j hi _hj _; exact absurd hi (by omega)
        | succ m ihm =>
            have hm_le_d : m ≤ d := Nat.le_of_succ_le hn
            obtain ⟨prev⟩ := ihm hm_le_d
            -- Helper to pull out the `i < m` from a `⟨i, hi⟩ : (Finset.range m).attach`.
            -- Build subtree for index m.
            let priorVerts : Finset V :=
              (Finset.range m).attach.biUnion fun x =>
                (prev.subtree x.val (Finset.mem_range.mp x.property)).vertexFinset
            let curIdx : Fin d := ⟨m, hn⟩
            let curChildRoot := childRoot curIdx
            set bigForb : Finset V :=
              forbiddenAfter ∪ allChildRoots ∪ priorVerts with hbigForb_def
            set recForb : Finset V := bigForb.erase curChildRoot with hrecForb_def
            have h_cur_not_forbAfter : curChildRoot ∉ forbiddenAfter :=
              hchildRoot_fresh curIdx
            have h_cur_in_all : curChildRoot ∈ allChildRoots := by
              rw [hallChildRoots_def]
              exact Finset.mem_image.mpr ⟨curIdx, Finset.mem_univ _, rfl⟩
            have h_cur_in_bigForb : curChildRoot ∈ bigForb := by
              rw [hbigForb_def]
              refine Finset.mem_union.mpr (Or.inl ?_)
              exact Finset.mem_union.mpr (Or.inr h_cur_in_all)
            -- Each prior subtree intersects allChildRoots in only its own root.
            have h_prior_inter : ∀ (i : ℕ) (hi : i < m),
                (prev.subtree i hi).vertexFinset ∩ allChildRoots ⊆
                  {childRoot ⟨i, lt_of_lt_of_le hi hm_le_d⟩} := by
              intro i hi v hv
              rw [Finset.mem_inter] at hv
              rw [Finset.mem_singleton]
              by_contra hne
              have h_av := prev.avoids i hi (lt_of_lt_of_le hi hm_le_d)
              have hv_erase : v ∈ allChildRoots.erase
                  (childRoot ⟨i, lt_of_lt_of_le hi hm_le_d⟩) := by
                rw [Finset.mem_erase]; exact ⟨hne, hv.2⟩
              rw [avoids_iff_vertexFinset_disjoint] at h_av
              exact (Finset.disjoint_left.mp h_av) hv.1 (Finset.mem_union_right _ hv_erase)
            -- curChildRoot is not in any prior subtree.
            have h_cur_not_prior : curChildRoot ∉ priorVerts := by
              intro hmem
              rcases Finset.mem_biUnion.mp hmem with ⟨x, _, hin⟩
              have hi' : x.val < m := Finset.mem_range.mp x.property
              have h_cur_in_inter : curChildRoot ∈
                  (prev.subtree x.val hi').vertexFinset ∩ allChildRoots :=
                Finset.mem_inter.mpr ⟨hin, h_cur_in_all⟩
              have h_in_sing := h_prior_inter x.val hi' h_cur_in_inter
              rw [Finset.mem_singleton] at h_in_sing
              have hieq : (⟨x.val, lt_of_lt_of_le hi' hm_le_d⟩ : Fin d) = curIdx :=
                hchildRoot_inj h_in_sing.symm
              have : x.val = m := by simpa [curIdx] using congrArg Fin.val hieq
              omega
            have h_cur_not_recForb : curChildRoot ∉ recForb := Finset.notMem_erase _ _
            -- Cardinality bound.
            have hcard_priorVerts : priorVerts.card ≤ m * fanTreeThreshold d (h + 1) := by
              calc
                priorVerts.card
                    ≤ ∑ x ∈ (Finset.range m).attach,
                      (prev.subtree x.val (Finset.mem_range.mp x.property)).vertexFinset.card :=
                      Finset.card_biUnion_le
                _ = ∑ _x ∈ (Finset.range m).attach, fanTreeThreshold d (h + 1) := by
                      refine Finset.sum_congr rfl ?_
                      intro x _
                      exact (prev.subtree x.val (Finset.mem_range.mp x.property)).vertexFinset_card_threshold hd
                _ = m * fanTreeThreshold d (h + 1) := by
                      rw [Finset.sum_const]
                      simp [Finset.card_attach]
            -- |allChildRoots ∩ priorVerts| ≥ m.
            have hcard_inter_ge : m ≤ (allChildRoots ∩ priorVerts).card := by
              let f : { x // x ∈ Finset.range m } → V := fun x =>
                childRoot ⟨x.val, lt_of_lt_of_le (Finset.mem_range.mp x.property) hm_le_d⟩
              have hf_inj : Function.Injective f := by
                intro ⟨i, hi⟩ ⟨j, hj⟩ heq
                have hheq : (⟨i, _⟩ : Fin d) = ⟨j, _⟩ := hchildRoot_inj heq
                exact Subtype.ext (by simpa using congrArg Fin.val hheq)
              have hf_image_card : ((Finset.range m).attach.image f).card = m := by
                rw [Finset.card_image_of_injective _ hf_inj]
                simp
              calc m = ((Finset.range m).attach.image f).card := hf_image_card.symm
                _ ≤ (allChildRoots ∩ priorVerts).card := by
                      refine Finset.card_le_card ?_
                      intro v hv
                      rcases Finset.mem_image.mp hv with ⟨x, _, rfl⟩
                      have hi' : x.val < m := Finset.mem_range.mp x.property
                      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
                      · rw [hallChildRoots_def]
                        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
                      · refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_attach _ _, ?_⟩
                        rw [show f x = childRoot ⟨x.val, lt_of_lt_of_le hi' hm_le_d⟩ from rfl,
                          ← prev.root_matches x.val hi' (lt_of_lt_of_le hi' hm_le_d)]
                        exact (prev.subtree x.val hi').root_mem_vertexFinset
            have hcard_all_sdiff : (allChildRoots \ priorVerts).card ≤ d - m := by
              have hsum := Finset.card_sdiff_add_card_inter allChildRoots priorVerts
              rw [hallChildRoots_card] at hsum
              omega
            have hcard_bigForb : bigForb.card ≤
                forbidden.card + 1 + (d - m) + m * fanTreeThreshold d (h + 1) := by
              have h1 : bigForb.card ≤
                  forbiddenAfter.card + (allChildRoots ∪ priorVerts).card := by
                rw [hbigForb_def, Finset.union_assoc]
                exact Finset.card_union_le _ _
              have h2 : (allChildRoots ∪ priorVerts).card ≤
                  priorVerts.card + (allChildRoots \ priorVerts).card := by
                rw [Finset.union_comm]
                rw [show priorVerts ∪ allChildRoots = priorVerts ∪ (allChildRoots \ priorVerts) by
                  ext v
                  simp only [Finset.mem_union, Finset.mem_sdiff]
                  tauto]
                exact Finset.card_union_le _ _
              linarith
            have hcard_recForb_succ : recForb.card + 1 = bigForb.card := by
              rw [hrecForb_def, Finset.card_erase_of_mem h_cur_in_bigForb]
              have : 1 ≤ bigForb.card := Finset.card_pos.mpr ⟨curChildRoot, h_cur_in_bigForb⟩
              omega
            have hth_pos : 0 < fanTreeThreshold d (h + 1) := fanTreeThreshold_pos d h hd
            have hexp : fanTreeThreshold d (h + 2) = d * fanTreeThreshold d (h + 1) + 1 := by
              have hs : fanTreeThreshold d (h + 1 + 1) - 1 = d * fanTreeThreshold d (h + 1) :=
                fanTreeThreshold_succ_sub_one d (h + 1) hd
              have hp : 0 < fanTreeThreshold d (h + 1 + 1) := fanTreeThreshold_pos d (h + 1) hd
              show fanTreeThreshold d (h + 1 + 1) = d * fanTreeThreshold d (h + 1) + 1
              omega
            have hdeg_recForb : ∀ v : V,
                recForb.card + fanTreeThreshold d (h + 1) ≤ G.degree v := by
              intro v
              have hdv : forbidden.card + fanTreeThreshold d (h + 1 + 1) ≤ G.degree v := hdeg v
              rw [show h + 1 + 1 = h + 2 from rfl, hexp] at hdv
              have hmd : m + 1 ≤ d := hn
              have hd_sub_m : 1 ≤ d - m := by omega
              -- recForb.card + 1 ≤ forbidden + 1 + (d-m) + m*t (from hcard_recForb_succ + hcard_bigForb)
              have h_rec_le : recForb.card + 1 ≤
                  forbidden.card + 1 + (d - m) + m * fanTreeThreshold d (h + 1) := by
                rw [hcard_recForb_succ]; exact hcard_bigForb
              -- want recForb.card + t ≤ forbidden + d*t + 1
              -- i.e., recForb.card + 1 + t ≤ forbidden + d*t + 2
              -- need: forbidden + 1 + (d-m) + m*t + t ≤ forbidden + d*t + 2
              -- i.e., (d-m) + (m+1)*t ≤ d*t + 1
              -- since t ≥ 1: (d-m-1)*t + 1 ≥ (d-m-1) + 1 = d-m, so (d-m) ≤ (d-m-1)*t + 1.
              have hgoal : (d - m) + (m + 1) * fanTreeThreshold d (h + 1) ≤
                  d * fanTreeThreshold d (h + 1) + 1 := by
                have hsplit : d * fanTreeThreshold d (h + 1) =
                    (m + 1) * fanTreeThreshold d (h + 1) + (d - m - 1) * fanTreeThreshold d (h + 1) := by
                  rw [← Nat.add_mul]
                  congr 1; omega
                rw [hsplit]
                have : (d - m) ≤ (d - m - 1) * fanTreeThreshold d (h + 1) + 1 := by
                  have : (d - m - 1) ≤ (d - m - 1) * fanTreeThreshold d (h + 1) := by
                    exact Nat.le_mul_of_pos_right _ hth_pos
                  omega
                linarith
              linarith
            -- Recurse to build the m-th subtree.
            obtain ⟨Tm, hTm_root, hTm_avoid⟩ :=
              ih curChildRoot recForb h_cur_not_recForb hdeg_recForb
            refine ⟨⟨?_, ?_, ?_, ?_⟩⟩
            · exact fun i hi => if him : i < m then prev.subtree i him else Tm
            · -- root_matches
              intro i hi hin
              by_cases him : i < m
              · simp only [him, ↓reduceDIte]
                exact prev.root_matches i him hin
              · have hieq : i = m := by omega
                simp only [him, ↓reduceDIte]
                have hidx : (⟨i, hin⟩ : Fin d) = curIdx := Fin.ext hieq
                rw [hTm_root, hidx]
            · -- avoids
              intro i hi hin
              by_cases him : i < m
              · simp only [him, ↓reduceDIte]
                exact prev.avoids i him hin
              · have hieq : i = m := by omega
                simp only [him, ↓reduceDIte]
                have hidx : (⟨i, hin⟩ : Fin d) = curIdx := Fin.ext hieq
                rw [hidx]
                rw [avoids_iff_vertexFinset_disjoint]
                rw [avoids_iff_vertexFinset_disjoint] at hTm_avoid
                refine Finset.disjoint_left.mpr fun w hw hw_in => ?_
                rw [Finset.mem_union] at hw_in
                rcases hw_in with h_fA | h_other
                · have hw_ne_cur : w ≠ curChildRoot := by
                    intro heq; rw [heq] at h_fA; exact h_cur_not_forbAfter h_fA
                  have hw_bigForb : w ∈ bigForb := by
                    rw [hbigForb_def]
                    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h_fA)))
                  have hw_recForb : w ∈ recForb := by
                    rw [hrecForb_def, Finset.mem_erase]
                    exact ⟨hw_ne_cur, hw_bigForb⟩
                  exact (Finset.disjoint_left.mp hTm_avoid) hw hw_recForb
                · rw [Finset.mem_erase] at h_other
                  obtain ⟨hw_ne_cur, hw_all⟩ := h_other
                  have hw_bigForb : w ∈ bigForb := by
                    rw [hbigForb_def]
                    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hw_all)))
                  have hw_recForb : w ∈ recForb := by
                    rw [hrecForb_def, Finset.mem_erase]
                    exact ⟨hw_ne_cur, hw_bigForb⟩
                  exact (Finset.disjoint_left.mp hTm_avoid) hw hw_recForb
            · -- pairwise
              intro i j hi hj hij
              by_cases him : i < m
              · by_cases hjm : j < m
                · simp only [him, hjm, ↓reduceDIte]
                  exact prev.pairwise i j him hjm hij
                · have hjeq : j = m := by omega
                  have hjnotm : ¬ j < m := by omega
                  simp only [him, hjnotm, ↓reduceDIte]
                  refine Finset.disjoint_left.mpr fun w hw hw_Tm => ?_
                  have hw_prior : w ∈ priorVerts :=
                    Finset.mem_biUnion.mpr ⟨⟨i, by simp [Finset.mem_range]; exact him⟩,
                      Finset.mem_attach _ _, hw⟩
                  have hw_bigForb : w ∈ bigForb := by
                    rw [hbigForb_def]
                    exact Finset.mem_union.mpr (Or.inr hw_prior)
                  have hw_ne_cur : w ≠ curChildRoot := by
                    intro heq; rw [heq] at hw_prior; exact h_cur_not_prior hw_prior
                  have hw_recForb : w ∈ recForb := by
                    rw [hrecForb_def, Finset.mem_erase]
                    exact ⟨hw_ne_cur, hw_bigForb⟩
                  rw [avoids_iff_vertexFinset_disjoint] at hTm_avoid
                  exact (Finset.disjoint_left.mp hTm_avoid) hw_Tm hw_recForb
              · have hieq : i = m := by omega
                have hjm : j < m := by omega
                simp only [him, hjm, ↓reduceDIte]
                refine Finset.disjoint_left.mpr fun w hw_Tm hw => ?_
                have hw_prior : w ∈ priorVerts :=
                  Finset.mem_biUnion.mpr ⟨⟨j, by simp [Finset.mem_range]; exact hjm⟩,
                    Finset.mem_attach _ _, hw⟩
                have hw_bigForb : w ∈ bigForb := by
                  rw [hbigForb_def]
                  exact Finset.mem_union.mpr (Or.inr hw_prior)
                have hw_ne_cur : w ≠ curChildRoot := by
                  intro heq; rw [heq] at hw_prior; exact h_cur_not_prior hw_prior
                have hw_recForb : w ∈ recForb := by
                  rw [hrecForb_def, Finset.mem_erase]
                  exact ⟨hw_ne_cur, hw_bigForb⟩
                rw [avoids_iff_vertexFinset_disjoint] at hTm_avoid
                exact (Finset.disjoint_left.mp hTm_avoid) hw_Tm hw_recForb
      -- Apply with n = d.
      obtain ⟨full⟩ := key d le_rfl
      let childTree : Fin d → DAryTreeEmbedding G d h := fun i => full.subtree i.val i.isLt
      have hctroot : ∀ i : Fin d, (childTree i).root = childRoot i := by
        intro i
        exact full.root_matches i.val i.isLt i.isLt
      have hroot_not_mem_child : ∀ i : Fin d, root ∉ (childTree i).vertexFinset := by
        intro i
        have h_av := full.avoids i.val i.isLt i.isLt
        rw [avoids_iff_vertexFinset_disjoint] at h_av
        refine (Finset.disjoint_right.mp h_av) ?_
        refine Finset.mem_union.mpr (Or.inl ?_)
        rw [hforbiddenAfter_def]
        exact Finset.mem_insert_self _ _
      have hpair : ∀ {i j : Fin d}, i ≠ j →
          Disjoint (childTree i).vertexFinset (childTree j).vertexFinset := by
        intro i j hij
        refine full.pairwise i.val j.val i.isLt j.isLt ?_
        intro heq; exact hij (Fin.ext heq)
      let F : RootedChildSubtreeFamily G d h :=
        { root := root
          childRoot := childRoot
          childTree := childTree
          childTree_root := hctroot
          root_adj_child := hchildRoot_adj
          root_not_mem_child := hroot_not_mem_child
          child_disjoint := @hpair }
      refine ⟨F.toEmbedding, F.toEmbedding_root, ?_⟩
      refine F.toEmbedding_avoids hroot ?_
      intro i
      have h_av := full.avoids i.val i.isLt i.isLt
      refine (childTree i).avoids_of_vertexFinset_disjoint_forbidden ?_
      rw [avoids_iff_vertexFinset_disjoint] at h_av
      refine Finset.disjoint_left.mpr fun w hw hw_in => ?_
      have hw_in_big : w ∈ forbiddenAfter ∪
          (allChildRoots.erase (childRoot ⟨i.val, i.isLt⟩)) := by
        refine Finset.mem_union.mpr (Or.inl ?_)
        rw [hforbiddenAfter_def]
        exact Finset.mem_insert_of_mem hw_in
      exact (Finset.disjoint_left.mp h_av) hw hw_in_big

/-- Consecutive ancestors of a node are adjacent in the embedded graph. -/
lemma adj_ancestor_succ {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) (n : ℕ) (hnext : n + 1 ≤ x.depth.val) :
    G.Adj (T.vertex (DAryTreeIndex.ancestor x n (by omega)))
      (T.vertex (DAryTreeIndex.ancestor x (n + 1) hnext)) := by
  convert T.adj_child (DAryTreeIndex.ancestor x n (by omega))
      (x.coord ⟨n, by omega⟩)
      (by rw [DAryTreeIndex.ancestor_depth]; omega) using 2
  apply DAryTreeIndex.ext
  · rfl
  · exact heq_of_eq (by
      funext j
      by_cases hj : j.val < n
      · simp [DAryTreeIndex.ancestor, DAryTreeIndex.child, hj]
      · have hjlt : j.val < n + 1 := by
          simpa [DAryTreeIndex.ancestor] using j.isLt
        have hjn : j.val = n := by omega
        simp [DAryTreeIndex.ancestor, DAryTreeIndex.child, hjn])

/-- The embedded walk following the first `n` ancestor steps from the root toward `x`. -/
def walkToAncestor {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    (n : ℕ) → (h : n ≤ x.depth.val) →
      G.Walk (T.vertex (DAryTreeIndex.ancestor x 0 (Nat.zero_le _)))
        (T.vertex (DAryTreeIndex.ancestor x n h))
  | 0, _ => SimpleGraph.Walk.nil
  | n + 1, h =>
      (walkToAncestor T x n (Nat.le_of_succ_le h)).concat
        (adj_ancestor_succ T x n h)

lemma walkToAncestor_length {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    ∀ (n : ℕ) (h : n ≤ x.depth.val), (walkToAncestor T x n h).length = n
  | 0, _ => by simp [walkToAncestor]
  | n + 1, h => by
      simp [walkToAncestor, walkToAncestor_length T x n (Nat.le_of_succ_le h)]

lemma walkToAncestor_support_subset_vertexFinset
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    ∀ (n : ℕ) (h : n ≤ x.depth.val), ∀ w ∈ (walkToAncestor T x n h).support,
      w ∈ T.vertexFinset
  | 0, _, w, hw => by
      simp [walkToAncestor] at hw
      subst hw
      exact T.vertex_mem_vertexFinset (DAryTreeIndex.ancestor x 0 (Nat.zero_le _))
  | n + 1, h, w, hw => by
      rw [walkToAncestor, SimpleGraph.Walk.support_concat] at hw
      simp at hw
      rcases hw with hw | hw
      · exact walkToAncestor_support_subset_vertexFinset T x n (Nat.le_of_succ_le h) w hw
      · rcases hw with rfl
        exact T.vertex_mem_vertexFinset (DAryTreeIndex.ancestor x (n + 1) h)

lemma walkToAncestor_support_depth_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    ∀ (n : ℕ) (h : n ≤ x.depth.val) (y : DAryTreeIndex d height),
      T.vertex y ∈ (walkToAncestor T x n h).support → y.depth.val ≤ n
  | 0, _, y, hy => by
      simp [walkToAncestor] at hy
      have hidx : y = DAryTreeIndex.ancestor x 0 (Nat.zero_le _) := T.injective hy
      rw [hidx, DAryTreeIndex.ancestor_depth]
  | n + 1, h, y, hy => by
      rw [walkToAncestor, SimpleGraph.Walk.support_concat] at hy
      simp at hy
      rcases hy with hy | hy
      · exact Nat.le_succ_of_le
          (walkToAncestor_support_depth_le T x n (Nat.le_of_succ_le h) y hy)
      · have hidx : y = DAryTreeIndex.ancestor x (n + 1) h := T.injective hy
        rw [hidx, DAryTreeIndex.ancestor_depth]

lemma walkToAncestor_support_eq_ancestor {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    ∀ (n : ℕ) (h : n ≤ x.depth.val) (y : DAryTreeIndex d height),
      T.vertex y ∈ (walkToAncestor T x n h).support →
        ∃ m, ∃ hm : m ≤ n, y = DAryTreeIndex.ancestor x m (le_trans hm h)
  | 0, h, y, hy => by
      simp [walkToAncestor] at hy
      refine ⟨0, le_rfl, ?_⟩
      exact T.injective hy
  | n + 1, h, y, hy => by
      rw [walkToAncestor, SimpleGraph.Walk.support_concat] at hy
      simp at hy
      rcases hy with hy | hy
      · rcases walkToAncestor_support_eq_ancestor T x n (Nat.le_of_succ_le h) y hy with
          ⟨m, hm, hidx⟩
        refine ⟨m, Nat.le_succ_of_le hm, ?_⟩
        rw [hidx]
      · refine ⟨n + 1, le_rfl, ?_⟩
        exact T.injective hy

lemma walkToAncestor_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    ∀ (n : ℕ) (h : n ≤ x.depth.val), (walkToAncestor T x n h).IsPath
  | 0, _ => by
      simp [walkToAncestor]
  | n + 1, h => by
      rw [walkToAncestor]
      refine SimpleGraph.Walk.IsPath.concat
        (walkToAncestor_isPath T x n (Nat.le_of_succ_le h)) ?_
        (adj_ancestor_succ T x n h)
      intro hmem
      have hdepth := walkToAncestor_support_depth_le T x n (Nat.le_of_succ_le h)
        (DAryTreeIndex.ancestor x (n + 1) h) hmem
      rw [DAryTreeIndex.ancestor_depth] at hdepth
      omega

/-- The embedded root-to-node walk, with endpoint copied from the final ancestor to `x`. -/
def rootToNodeWalk {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    G.Walk (T.vertex (DAryTreeIndex.ancestor x 0 (Nat.zero_le _))) (T.vertex x) :=
  (walkToAncestor T x x.depth.val le_rfl).copy rfl
    (by rw [DAryTreeIndex.ancestor_self])

lemma rootToNodeWalk_length {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    (rootToNodeWalk T x).length = x.depth.val := by
  rw [rootToNodeWalk, SimpleGraph.Walk.length_copy]
  exact walkToAncestor_length T x x.depth.val le_rfl

lemma rootToNodeWalk_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    (rootToNodeWalk T x).IsPath := by
  rw [rootToNodeWalk, SimpleGraph.Walk.isPath_copy]
  exact walkToAncestor_isPath T x x.depth.val le_rfl

/-- The root-to-node walk with source copied to the named tree root. -/
def rootToNodeWalkFromRoot {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    G.Walk T.root (T.vertex x) :=
  (rootToNodeWalk T x).copy
    (by rw [← T.root_eq, DAryTreeIndex.ancestor_zero_eq_root])
    rfl

lemma rootToNodeWalkFromRoot_length {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    (rootToNodeWalkFromRoot T x).length = x.depth.val := by
  rw [rootToNodeWalkFromRoot, SimpleGraph.Walk.length_copy]
  exact rootToNodeWalk_length T x

lemma rootToNodeWalkFromRoot_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    (rootToNodeWalkFromRoot T x).IsPath := by
  rw [rootToNodeWalkFromRoot, SimpleGraph.Walk.isPath_copy]
  exact rootToNodeWalk_isPath T x

lemma rootToNodeWalkFromRoot_support_subset_vertexFinset
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) :
    ∀ w ∈ (rootToNodeWalkFromRoot T x).support, w ∈ T.vertexFinset := by
  intro w hw
  rw [rootToNodeWalkFromRoot, SimpleGraph.Walk.support_copy] at hw
  rw [rootToNodeWalk, SimpleGraph.Walk.support_copy] at hw
  exact walkToAncestor_support_subset_vertexFinset T x x.depth.val le_rfl w hw

/-- The canonical root-to-leaf branch path for first-level branch `i`. -/
def branchPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    G.Walk T.root (T.vertex (DAryTreeIndex.branchLeaf height i)) :=
  rootToNodeWalkFromRoot T (DAryTreeIndex.branchLeaf height i)

lemma branchPath_length {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    (branchPath T i).length = height := by
  rw [branchPath, rootToNodeWalkFromRoot_length, DAryTreeIndex.branchLeaf_depth]

lemma branchPath_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    (branchPath T i).IsPath := by
  exact rootToNodeWalkFromRoot_isPath T (DAryTreeIndex.branchLeaf height i)

lemma branchPath_tip_ne_root {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d)
    (hheight : 0 < height) :
    T.vertex (DAryTreeIndex.branchLeaf height i) ≠ T.root := by
  rw [← T.root_eq]
  intro hEq
  exact DAryTreeIndex.branchLeaf_ne_root i hheight (T.injective hEq)

lemma branchPath_support_subset_vertexFinset
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    ∀ w ∈ (branchPath T i).support, w ∈ T.vertexFinset := by
  intro w hw
  exact rootToNodeWalkFromRoot_support_subset_vertexFinset T
    (DAryTreeIndex.branchLeaf height i) w (by simpa [branchPath] using hw)

lemma branchPath_support_eq_ancestor {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d)
    (y : DAryTreeIndex d height) :
    T.vertex y ∈ (branchPath T i).support →
      ∃ m, ∃ hm : m ≤ height,
        y = DAryTreeIndex.ancestor (DAryTreeIndex.branchLeaf height i) m hm := by
  intro hy
  rw [branchPath, rootToNodeWalkFromRoot, SimpleGraph.Walk.support_copy,
    rootToNodeWalk, SimpleGraph.Walk.support_copy] at hy
  exact walkToAncestor_support_eq_ancestor T
    (DAryTreeIndex.branchLeaf height i) height le_rfl y hy

lemma branchPath_support_first_coord {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d)
    (y : DAryTreeIndex d height)
    (hy : T.vertex y ∈ (branchPath T i).support)
    (hypos : 0 < y.depth.val) :
    y.coord ⟨0, hypos⟩ = i := by
  rcases branchPath_support_eq_ancestor T i y hy with ⟨m, hm, hidx⟩
  have hmpos : 0 < m := by
    have hdepth : y.depth.val = m := by
      rw [hidx, DAryTreeIndex.ancestor_depth]
    omega
  subst y
  exact DAryTreeIndex.ancestor_branchLeaf_first_coord i hm hmpos

/-- Generalised version of `branchPath_support_first_coord`: every non-root
ancestor of a leaf `x` in branch `i` (i.e. `x.coord 0 = i`) has first
coordinate equal to `i`. -/
lemma rootToNodeWalkFromRoot_support_first_coord
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (x : DAryTreeIndex d height) (hxpos : 0 < x.depth.val)
    (y : DAryTreeIndex d height)
    (hy : T.vertex y ∈ (rootToNodeWalkFromRoot T x).support)
    (hypos : 0 < y.depth.val) :
    y.coord ⟨0, hypos⟩ = x.coord ⟨0, hxpos⟩ := by
  -- Convert hy: y on rootToNodeWalkFromRoot T x means y on walkToAncestor T x x.depth.val.
  have hyAnc : ∃ m, ∃ hm : m ≤ x.depth.val,
      y = DAryTreeIndex.ancestor x m (le_trans hm le_rfl) := by
    rw [rootToNodeWalkFromRoot, SimpleGraph.Walk.support_copy,
      rootToNodeWalk, SimpleGraph.Walk.support_copy] at hy
    exact walkToAncestor_support_eq_ancestor T x x.depth.val le_rfl y hy
  rcases hyAnc with ⟨m, hm, hidx⟩
  have hmpos : 0 < m := by
    have hdepth : y.depth.val = m := by
      rw [hidx, DAryTreeIndex.ancestor_depth]
    omega
  subst y
  -- ancestor x m hm |>.coord ⟨0, _⟩ = x.coord ⟨0, mpos.trans h⟩.
  unfold DAryTreeIndex.ancestor
  simp

/-- The index set of the first-level subtree labelled by `i`: all non-root
nodes whose first coordinate is `i`. -/
def firstLevelSubtreeIndexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (_T : DAryTreeEmbedding G d height) (i : Fin d) :
    Finset (DAryTreeIndex d height) :=
  Finset.univ.filter fun x => ∃ hpos : 0 < x.depth.val, x.coord ⟨0, hpos⟩ = i

/-- The vertex set of the first-level subtree labelled by `i`. -/
def firstLevelSubtreeVerts {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    Finset V :=
  (firstLevelSubtreeIndexFinset T i).image T.vertex

lemma mem_firstLevelSubtreeIndexFinset_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d)
    (x : DAryTreeIndex d height) :
    x ∈ firstLevelSubtreeIndexFinset T i ↔
      ∃ hpos : 0 < x.depth.val, x.coord ⟨0, hpos⟩ = i := by
  simp [firstLevelSubtreeIndexFinset]

lemma firstLevelSubtreeVerts_subset_vertexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    T.firstLevelSubtreeVerts i ⊆ T.vertexFinset := by
  intro v hv
  rw [firstLevelSubtreeVerts] at hv
  rcases Finset.mem_image.mp hv with ⟨x, -, rfl⟩
  exact T.vertex_mem_vertexFinset x

lemma root_not_mem_firstLevelSubtreeIndexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    DAryTreeIndex.root d height ∉ firstLevelSubtreeIndexFinset T i := by
  rw [mem_firstLevelSubtreeIndexFinset_iff]
  rintro ⟨hpos, -⟩
  simp [DAryTreeIndex.root] at hpos

lemma root_not_mem_firstLevelSubtreeVerts {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height) (i : Fin d) :
    T.root ∉ T.firstLevelSubtreeVerts i := by
  rw [← T.root_eq, firstLevelSubtreeVerts]
  intro h
  rcases Finset.mem_image.mp h with ⟨x, hx, hxroot⟩
  have hidx : x = DAryTreeIndex.root d height := T.injective hxroot
  exact root_not_mem_firstLevelSubtreeIndexFinset T i (hidx ▸ hx)

lemma consFirst_mem_firstLevelSubtreeIndexFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d height)
    (i : Fin d) (hheight : 0 < height) (y : DAryTreeIndex d (height - 1)) :
    DAryTreeIndex.consFirst i y hheight ∈ firstLevelSubtreeIndexFinset T i := by
  rw [mem_firstLevelSubtreeIndexFinset_iff]
  refine ⟨by simp [DAryTreeIndex.consFirst], ?_⟩
  simp [DAryTreeIndex.consFirst]

/-- Extract the `i`-th first-level subtree of a height-`(h + 1)` embedded tree
as a standalone height-`h` embedded tree.  The root of the extracted subtree is
the `i`-th child of the original root. -/
def firstLevelSubtree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d (height + 1))
    (i : Fin d) : DAryTreeEmbedding G d height where
  root := T.vertex (DAryTreeIndex.child (DAryTreeIndex.root d (height + 1)) i
            (by simp [DAryTreeIndex.root]))
  vertex := fun y => T.vertex (DAryTreeIndex.consFirst (height := height + 1) i y (Nat.succ_pos height))
  root_eq := by
    -- consFirst i (root d height) _ = child (root d (height + 1)) i _
    apply congrArg
    apply DAryTreeIndex.ext
    · simp [DAryTreeIndex.consFirst, DAryTreeIndex.child, DAryTreeIndex.root]
    · exact heq_of_eq (by
        funext j
        simp [DAryTreeIndex.consFirst, DAryTreeIndex.child, DAryTreeIndex.root])
  injective := by
    intro x y hxy
    have hcf : DAryTreeIndex.consFirst (height := height + 1) i x (Nat.succ_pos height) =
        DAryTreeIndex.consFirst (height := height + 1) i y (Nat.succ_pos height) := T.injective hxy
    exact DAryTreeIndex.consFirst_injective i (Nat.succ_pos height) hcf
  adj_child := by
    intro x j hx
    -- Need: G.Adj (T.vertex (consFirst i x _)) (T.vertex (consFirst i (child x j hx) _))
    -- Use T.adj_child on (consFirst i x _) with index j.
    have hpos : 0 < (DAryTreeIndex.consFirst (height := height + 1) i x (Nat.succ_pos height)).depth.val := by
      simp [DAryTreeIndex.consFirst]
    have hxlt : (DAryTreeIndex.consFirst (height := height + 1) i x (Nat.succ_pos height)).depth.val < height + 1 := by
      simp [DAryTreeIndex.consFirst]
      omega
    have hadj := T.adj_child (DAryTreeIndex.consFirst (height := height + 1) i x (Nat.succ_pos height)) j hxlt
    -- Now we need to show:
    -- child (consFirst i x _) j _ = consFirst i (child x j hx) _
    have hchild_eq :
        DAryTreeIndex.child (DAryTreeIndex.consFirst (height := height + 1) i x (Nat.succ_pos height)) j hxlt =
          DAryTreeIndex.consFirst (height := height + 1) i (DAryTreeIndex.child x j hx) (Nat.succ_pos height) := by
      apply DAryTreeIndex.ext
      · simp [DAryTreeIndex.child, DAryTreeIndex.consFirst]
      · refine heq_of_eq (funext ?_)
        intro k
        -- k : Fin (x.depth.val + 1 + 1) on both sides after unfolding.
        -- We do a case analysis on k.val.
        rcases Nat.eq_or_lt_of_le (Nat.zero_le k.val) with hk0 | hkpos
        · -- k.val = 0
          have hk0' : k.val = 0 := hk0.symm
          have hk_lt_xpos : (0 : ℕ) < x.depth.val + 1 := Nat.succ_pos _
          simp only [DAryTreeIndex.child, DAryTreeIndex.consFirst, hk0', hk_lt_xpos,
            dif_pos True.intro]
        · -- k.val > 0
          have hkne0 : k.val ≠ 0 := Nat.ne_of_gt hkpos
          simp only [DAryTreeIndex.child, DAryTreeIndex.consFirst]
          -- Outer child: dif on k.val < x.depth.val + 1
          by_cases hkx : k.val < x.depth.val + 1
          · -- LHS: outer dif positive → inner consFirst at coord ⟨k.val, _⟩
            -- inner consFirst dif on k.val = 0 → false → x.coord ⟨k.val - 1, _⟩
            -- RHS: outer dif on k.val = 0 → false → (child x j hx).coord ⟨k.val - 1, _⟩
            -- which is: dif on k.val - 1 < x.depth.val → x.coord ⟨k.val - 1, _⟩
            -- Need k.val - 1 < x.depth.val ↔ k.val < x.depth.val + 1 — have hkx.
            have hk1 : k.val - 1 < x.depth.val := by omega
            rw [dif_pos hkx]
            rw [dif_neg hkne0]
            rw [dif_neg hkne0]
            rw [dif_pos hk1]
          · -- k.val = x.depth.val + 1
            have hk_eq : k.val = x.depth.val + 1 := by
              have : k.val < x.depth.val + 1 + 1 := by
                have := k.isLt
                simpa [DAryTreeIndex.child, DAryTreeIndex.consFirst] using this
              omega
            have hk1_nlt : ¬ k.val - 1 < x.depth.val := by omega
            rw [dif_neg hkx]
            rw [dif_neg hkne0]
            rw [dif_neg hk1_nlt]
    rw [hchild_eq] at hadj
    exact hadj

@[simp] lemma firstLevelSubtree_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d (height + 1))
    (i : Fin d) :
    (T.firstLevelSubtree i).root =
      T.vertex (DAryTreeIndex.child (DAryTreeIndex.root d (height + 1)) i
        (by simp [DAryTreeIndex.root])) := rfl

@[simp] lemma firstLevelSubtree_vertex {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d (height + 1))
    (i : Fin d) (y : DAryTreeIndex d height) :
    (T.firstLevelSubtree i).vertex y =
      T.vertex (DAryTreeIndex.consFirst (height := height + 1) i y (Nat.succ_pos height)) := rfl

/-- The vertex set of the extracted first-level subtree equals the
abstract `firstLevelSubtreeVerts`. -/
lemma firstLevelSubtree_vertexFinset_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d height : ℕ} (T : DAryTreeEmbedding G d (height + 1))
    (i : Fin d) :
    (T.firstLevelSubtree i).vertexFinset = T.firstLevelSubtreeVerts i := by
  ext v
  simp only [vertexFinset, firstLevelSubtreeVerts, Finset.mem_image, Finset.mem_univ,
    true_and, firstLevelSubtree_vertex]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨DAryTreeIndex.consFirst i y (Nat.succ_pos height), ?_, rfl⟩
    exact consFirst_mem_firstLevelSubtreeIndexFinset T i (Nat.succ_pos height) y
  · rintro ⟨x, hx, rfl⟩
    rw [mem_firstLevelSubtreeIndexFinset_iff] at hx
    rcases hx with ⟨hxpos, hxcoord⟩
    refine ⟨DAryTreeIndex.tail x hxpos, ?_⟩
    have hcf := DAryTreeIndex.consFirst_tail x (Nat.succ_pos height) hxpos
    rw [hxcoord] at hcf
    rw [hcf]
end DAryTreeEmbedding
namespace DAryTreeIndex

/-- Index helper: extract a depth-`≤ h` index of the height-`(h + 1)` tree
as a height-`h` index. -/
def ofSucc {d h : ℕ} (x : DAryTreeIndex d (h + 1))
    (hxle : x.depth.val ≤ h) : DAryTreeIndex d h :=
  { depth := ⟨x.depth.val, Nat.lt_succ_of_le hxle⟩
    coord := fun j => x.coord ⟨j.val, by have := j.isLt; omega⟩ }

@[simp] lemma ofSucc_depth {d h : ℕ} (x : DAryTreeIndex d (h + 1))
    (hxle : x.depth.val ≤ h) :
    (x.ofSucc hxle).depth.val = x.depth.val := rfl

/-- The d-ary index's "leaf coordinate": for a depth-`(h+1)` index, the
function `Fin h → Fin d` giving the first `h` coordinates. -/
def leafCoord {d h : ℕ} (x : DAryTreeIndex d (h + 1))
    (_hx : x.depth.val = h + 1) (j : Fin h) : Fin d :=
  x.coord ⟨j.val, by have := j.isLt; omega⟩

/-- The d-ary index's "leaf last coord": for a depth-`(h+1)` index, the
final coordinate in position `h`. -/
def leafLast {d h : ℕ} (x : DAryTreeIndex d (h + 1))
    (hx : x.depth.val = h + 1) : Fin d :=
  x.coord ⟨h, by rw [hx]; exact Nat.lt_succ_self _⟩

end DAryTreeIndex

/-- Data needed to extend a height-`h` embedded tree by one more level
of children at each leaf. -/
structure LeafExtensionData {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h) where
  /-- For each leaf coordinate `c` of `T` and each `j : Fin d`, a new
  vertex that will become the `j`-th child of the leaf encoded by `c`. -/
  ext : (Fin h → Fin d) → Fin d → V
  /-- The new children are adjacent to their respective leaves. -/
  ext_adj : ∀ (c : Fin h → Fin d) (j : Fin d),
    G.Adj (T.vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩) (ext c j)
  /-- New children are distinct across all (leaf, j) pairs. -/
  ext_injective : ∀ (c₁ c₂ : Fin h → Fin d) (j₁ j₂ : Fin d),
    ext c₁ j₁ = ext c₂ j₂ → c₁ = c₂ ∧ j₁ = j₂
  /-- New children do not coincide with any existing tree vertex. -/
  ext_not_mem_tree : ∀ (c : Fin h → Fin d) (j : Fin d),
    ext c j ∉ T.vertexFinset

namespace DAryTreeEmbedding

/-- The vertex function of the height-`(h+1)` extension. -/
def extendVertex {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h)
    (E : LeafExtensionData T) (x : DAryTreeIndex d (h + 1)) : V :=
  if hxle : x.depth.val ≤ h then
    T.vertex (x.ofSucc hxle)
  else
    have hxeq : x.depth.val = h + 1 := by have := x.depth.isLt; omega
    E.ext (x.leafCoord hxeq) (x.leafLast hxeq)

lemma extendVertex_le {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h)
    (E : LeafExtensionData T) (x : DAryTreeIndex d (h + 1))
    (hxle : x.depth.val ≤ h) :
    extendVertex T E x = T.vertex (x.ofSucc hxle) := by
  unfold extendVertex
  rw [dif_pos hxle]

lemma extendVertex_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h)
    (E : LeafExtensionData T) (x : DAryTreeIndex d (h + 1))
    (hxeq : x.depth.val = h + 1) :
    extendVertex T E x = E.ext (x.leafCoord hxeq) (x.leafLast hxeq) := by
  unfold extendVertex
  have hxnle : ¬ x.depth.val ≤ h := by omega
  rw [dif_neg hxnle]

/-- Extend a height-`h` embedded tree by one more level using
`LeafExtensionData`.  The resulting tree has height `h + 1`, the same
root, and contains the original tree as a substructure. -/
def extendByOneLevel {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h)
    (E : LeafExtensionData T) : DAryTreeEmbedding G d (h + 1) where
  root := T.root
  vertex := extendVertex T E
  root_eq := by
    have hroot_le : (DAryTreeIndex.root d (h + 1)).depth.val ≤ h :=
      by simp [DAryTreeIndex.root]
    rw [extendVertex_le T E _ hroot_le]
    have hofs : (DAryTreeIndex.root d (h + 1)).ofSucc hroot_le =
        DAryTreeIndex.root d h := by
      apply DAryTreeIndex.ext
      · apply Fin.ext; rfl
      · refine heq_of_eq (funext ?_)
        intro j
        have hjlt : j.val < 0 := by
          have := j.isLt
          simp [DAryTreeIndex.ofSucc, DAryTreeIndex.root] at this
        exact absurd hjlt (Nat.not_lt_zero _)
    rw [hofs, T.root_eq]
  injective := by
    intro x y hxy
    change extendVertex T E x = extendVertex T E y at hxy
    by_cases hxle : x.depth.val ≤ h
    · by_cases hyle : y.depth.val ≤ h
      · rw [extendVertex_le T E x hxle, extendVertex_le T E y hyle] at hxy
        have hT : x.ofSucc hxle = y.ofSucc hyle := T.injective hxy
        have hdepth_val : x.depth.val = y.depth.val := by
          have := congrArg (fun z : DAryTreeIndex d h => z.depth.val) hT
          simpa [DAryTreeIndex.ofSucc] using this
        -- Cast y to the same depth as x and then use DAryTreeIndex.ext.
        rcases x with ⟨xd, xc⟩
        rcases y with ⟨yd, yc⟩
        simp only at hdepth_val
        have hxdyd : xd = yd := Fin.ext hdepth_val
        subst hxdyd
        have hcoord_eq : xc = yc := by
          have := congrFun (eq_of_heq (DAryTreeIndex.mk.inj hT).2)
          funext j
          have := this ⟨j.val, by simp⟩
          simpa [DAryTreeIndex.ofSucc] using this
        rw [hcoord_eq]
      · have hyeq : y.depth.val = h + 1 := by have := y.depth.isLt; omega
        rw [extendVertex_le T E x hxle, extendVertex_eq T E y hyeq] at hxy
        exfalso
        apply E.ext_not_mem_tree _ _
        rw [← hxy]
        exact T.vertex_mem_vertexFinset _
    · by_cases hyle : y.depth.val ≤ h
      · have hxeq : x.depth.val = h + 1 := by have := x.depth.isLt; omega
        rw [extendVertex_eq T E x hxeq, extendVertex_le T E y hyle] at hxy
        exfalso
        apply E.ext_not_mem_tree _ _
        rw [hxy]
        exact T.vertex_mem_vertexFinset _
      · have hxeq : x.depth.val = h + 1 := by have := x.depth.isLt; omega
        have hyeq : y.depth.val = h + 1 := by have := y.depth.isLt; omega
        rw [extendVertex_eq T E x hxeq, extendVertex_eq T E y hyeq] at hxy
        obtain ⟨hcoord_eq, hlast_eq⟩ := E.ext_injective _ _ _ _ hxy
        rcases x with ⟨xd, xc⟩
        rcases y with ⟨yd, yc⟩
        simp only at hxeq hyeq
        have hxdyd : xd = yd := by apply Fin.ext; omega
        subst hxdyd
        -- Now xd = yd. xc, yc : Fin xd.val → Fin d.  Also xd.val = h + 1.
        -- Convert xd to ⟨h+1, _⟩ so xc, yc have type Fin (h+1) → Fin d.
        obtain ⟨xdv, xdh⟩ := xd
        simp only at hxeq
        subst hxeq
        -- Now xc, yc : Fin (h+1) → Fin d.
        have hcoord_eq' : xc = yc := by
          funext j
          by_cases hjh : j.val < h
          · have := congrFun hcoord_eq ⟨j.val, hjh⟩
            simpa [DAryTreeIndex.leafCoord] using this
          · have hjeq : j.val = h := by have := j.isLt; omega
            have hj_eq : (⟨h, by omega⟩ : Fin (h + 1)) = j := by
              apply Fin.ext; exact hjeq.symm
            rw [← hj_eq]
            simpa [DAryTreeIndex.leafLast] using hlast_eq
        rw [hcoord_eq']
  adj_child := by
    intro x i hx
    by_cases hxlt : x.depth.val < h
    · have hxle : x.depth.val ≤ h := Nat.le_of_lt hxlt
      have hchild_le : (DAryTreeIndex.child x i hx).depth.val ≤ h := by
        simp [DAryTreeIndex.child]; omega
      rw [extendVertex_le T E x hxle, extendVertex_le T E _ hchild_le]
      have hxof_lt : (x.ofSucc hxle).depth.val < h := by
        simpa [DAryTreeIndex.ofSucc] using hxlt
      have hadj := T.adj_child (x.ofSucc hxle) i hxof_lt
      have hchild_match :
          (DAryTreeIndex.child x i hx).ofSucc hchild_le =
            DAryTreeIndex.child (x.ofSucc hxle) i hxof_lt := by
        apply DAryTreeIndex.ext
        · apply Fin.ext; simp [DAryTreeIndex.ofSucc, DAryTreeIndex.child]
        · refine heq_of_eq (funext ?_)
          intro j
          have hjlt : j.val < x.depth.val + 1 := by
            simpa [DAryTreeIndex.ofSucc, DAryTreeIndex.child] using j.isLt
          by_cases hjx : j.val < x.depth.val
          · simp [DAryTreeIndex.ofSucc, DAryTreeIndex.child, hjx]
          · have hje : j.val = x.depth.val := by omega
            simp [DAryTreeIndex.ofSucc, DAryTreeIndex.child, hje]
      rw [hchild_match]
      exact hadj
    · have hxeq : x.depth.val = h := by
        have : x.depth.val < h + 1 := hx
        omega
      have hxle : x.depth.val ≤ h := by omega
      have hchild_eq : (DAryTreeIndex.child x i hx).depth.val = h + 1 := by
        simp [DAryTreeIndex.child]; omega
      rw [extendVertex_le T E x hxle, extendVertex_eq T E _ hchild_eq]
      have hleafc_eq :
          (DAryTreeIndex.child x i hx).leafCoord hchild_eq =
          fun j : Fin h => x.coord ⟨j.val, by rw [hxeq]; exact j.isLt⟩ := by
        funext j
        unfold DAryTreeIndex.leafCoord
        have hjlt : j.val < x.depth.val := by rw [hxeq]; exact j.isLt
        simp [DAryTreeIndex.child, hjlt]
      have hleafl_eq : (DAryTreeIndex.child x i hx).leafLast hchild_eq = i := by
        unfold DAryTreeIndex.leafLast
        have hhge : ¬ h < x.depth.val := by rw [hxeq]; exact Nat.lt_irrefl _
        simp [DAryTreeIndex.child, hhge]
      rw [hleafc_eq, hleafl_eq]
      have hadj := E.ext_adj
        (fun j : Fin h => x.coord ⟨j.val, by rw [hxeq]; exact j.isLt⟩) i
      have hxof_eq :
          x.ofSucc hxle =
          (⟨⟨h, by omega⟩,
            fun j : Fin h => x.coord ⟨j.val, by rw [hxeq]; exact j.isLt⟩⟩ :
            DAryTreeIndex d h) := by
        rcases x with ⟨xd, xc⟩
        rcases xd with ⟨xdv, xdh⟩
        simp only at hxeq
        subst hxeq
        rfl
      rw [hxof_eq]
      exact hadj

@[simp] lemma extendByOneLevel_root {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h)
    (E : LeafExtensionData T) :
    (T.extendByOneLevel E).root = T.root := rfl

/-! ### Greedy `LeafExtensionData` from per-leaf saturation -/

/-- A partial leaf extension: extender data defined on a `Finset` of leaves,
with the disjointness/freshness invariants needed for the greedy construction. -/
private structure PartialLeafExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (T : DAryTreeEmbedding G d h)
    (forbidden : Finset V)
    (processed : Finset (Fin h → Fin d)) where
  ext : (Fin h → Fin d) → Fin d → V
  ext_adj : ∀ c ∈ processed, ∀ j : Fin d,
    G.Adj (T.vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩) (ext c j)
  ext_injective :
    ∀ c₁ ∈ processed, ∀ c₂ ∈ processed, ∀ j₁ j₂ : Fin d,
      ext c₁ j₁ = ext c₂ j₂ → c₁ = c₂ ∧ j₁ = j₂
  ext_not_mem_tree : ∀ c ∈ processed, ∀ j : Fin d,
    ext c j ∉ T.vertexFinset
  ext_not_mem_forbidden : ∀ c ∈ processed, ∀ j : Fin d,
    ext c j ∉ forbidden

/-- Alternative inductive step: extend a partial leaf extension to one more
leaf using a *filtered*-neighborhood hypothesis directly. -/
private lemma PartialLeafExtension.extend_of_filter
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d h : ℕ}
    (T : DAryTreeEmbedding G d h)
    (forbidden : Finset V)
    {processed : Finset (Fin h → Fin d)}
    (P : PartialLeafExtension T forbidden processed)
    (c : Fin h → Fin d) (hc : c ∉ processed)
    (hsat : d * processed.card + d ≤
      ((G.neighborFinset (T.vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩)).filter
        fun y => y ∉ T.vertexFinset ∧ y ∉ forbidden).card) :
    Nonempty (PartialLeafExtension T forbidden (insert c processed)) := by
  classical
  let leaf : V := T.vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩
  let used : Finset V :=
    processed.biUnion fun c' => (Finset.univ.image fun j : Fin d => P.ext c' j)
  let totalForbidden : Finset V := T.vertexFinset ∪ forbidden ∪ used
  let availableFiltered : Finset V :=
    (G.neighborFinset leaf).filter fun y => y ∉ T.vertexFinset ∧ y ∉ forbidden
  let available : Finset V :=
    (G.neighborFinset leaf).filter fun y => y ∉ totalForbidden
  have hused_card : used.card ≤ d * processed.card := by
    calc used.card
        ≤ ∑ c' ∈ processed, (Finset.univ.image fun j : Fin d => P.ext c' j).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _c' ∈ processed, d := by
          refine Finset.sum_le_sum ?_
          intro c' _
          exact le_trans (Finset.card_image_le) (by simp)
      _ = d * processed.card := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- availableFiltered = (N(leaf)) ∩ ¬T ∩ ¬forbidden.
  -- available = (N(leaf)) ∩ ¬(T ∪ forbidden ∪ used) = availableFiltered ∩ ¬used.
  have hsubset : availableFiltered \ used ⊆ available := by
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_filter] at hy
    refine Finset.mem_filter.mpr ⟨hy.1.1, ?_⟩
    intro hbad
    have hbad' : y ∈ T.vertexFinset ∨ y ∈ forbidden ∨ y ∈ used := by
      rcases Finset.mem_union.mp hbad with hUF | hU
      · rcases Finset.mem_union.mp hUF with hT | hF
        · exact Or.inl hT
        · exact Or.inr (Or.inl hF)
      · exact Or.inr (Or.inr hU)
    rcases hbad' with hT | hF | hU
    · exact hy.1.2.1 hT
    · exact hy.1.2.2 hF
    · exact hy.2 hU
  have havailable_ge : d ≤ available.card := by
    have h1 : availableFiltered.card - used.card ≤ (availableFiltered \ used).card := by
      have := Finset.le_card_sdiff used availableFiltered
      omega
    have h2 : (availableFiltered \ used).card ≤ available.card :=
      Finset.card_le_card hsubset
    have h3 : d * processed.card + d ≤ availableFiltered.card := hsat
    omega
  -- Use exists_injective_neighbors_not_mem with forbidden = totalForbidden.
  -- That needs |totalForbidden| + d ≤ G.degree leaf, OR equivalently from
  -- |available| ≥ d we can pick d injective neighbors.
  -- Derive G.degree bound from |available|:
  have hdeg_inside : G.degree leaf - available.card =
      ((G.neighborFinset leaf).filter fun y => y ∈ totalForbidden).card := by
    have hpartition :
        ((G.neighborFinset leaf).filter fun y => y ∈ totalForbidden).card +
          available.card = G.degree leaf := by
      have : ((G.neighborFinset leaf).filter fun y => y ∈ totalForbidden).card +
          ((G.neighborFinset leaf).filter fun y => ¬ y ∈ totalForbidden).card =
            (G.neighborFinset leaf).card :=
        Finset.card_filter_add_card_filter_not (s := G.neighborFinset leaf)
          (fun y => y ∈ totalForbidden)
      simpa [available, SimpleGraph.degree, SimpleGraph.neighborFinset] using this
    omega
  -- Pick d distinct vertices from `available` directly: |available| ≥ d gives us
  -- a Fin d-indexed injection into available.
  classical
  obtain ⟨sChoice, hsCard, hsSub⟩ :
      ∃ s : Finset V, s.card = d ∧ s ⊆ available := by
    refine ⟨available.toList.take d |>.toFinset, ?_, ?_⟩
    · have hnodup : (available.toList.take d).Nodup :=
        (List.take_sublist _ _).nodup available.nodup_toList
      rw [List.toFinset_card_of_nodup hnodup, List.length_take]
      have : d ≤ available.toList.length := by
        rw [Finset.length_toList]; exact havailable_ge
      exact min_eq_left this
    · intro x hx
      have : x ∈ available.toList := by
        rw [List.mem_toFinset] at hx
        exact (List.take_sublist _ _).subset hx
      exact (Finset.mem_toList).mp this
  let eEquiv : Fin d ≃ sChoice := (Finset.equivFinOfCardEq hsCard).symm
  let newTip : Fin d → V := fun j => (eEquiv j).1
  have hinj : Function.Injective newTip := by
    intro a b hab
    exact eEquiv.injective (Subtype.ext hab)
  have hmem : ∀ j, newTip j ∈ available := fun j => hsSub (eEquiv j).2
  have hadj : ∀ j, G.Adj leaf (newTip j) := fun j => by
    have := hmem j
    rw [Finset.mem_filter] at this
    exact (SimpleGraph.mem_neighborFinset _ _ _).mp this.1
  have hfresh : ∀ j, newTip j ∉ totalForbidden := fun j hj => by
    have := hmem j
    rw [Finset.mem_filter] at this
    exact this.2 hj
  let newExt : (Fin h → Fin d) → Fin d → V := fun c' j =>
    if c' = c then newTip j else P.ext c' j
  refine ⟨{
    ext := newExt
    ext_adj := ?_
    ext_injective := ?_
    ext_not_mem_tree := ?_
    ext_not_mem_forbidden := ?_
  }⟩
  · intro c' hc' j
    rcases Finset.mem_insert.mp hc' with rfl | hc'_old
    · simp [newExt, leaf] at hadj ⊢
      exact hadj j
    · have hc'_ne_c : c' ≠ c := fun h => hc (h ▸ hc'_old)
      simp [newExt, hc'_ne_c]
      exact P.ext_adj c' hc'_old j
  · intro c₁ hc₁ c₂ hc₂ j₁ j₂ hext
    by_cases h1 : c₁ = c
    · by_cases h2 : c₂ = c
      · subst h1; subst h2
        have : newTip j₁ = newTip j₂ := by simpa [newExt] using hext
        exact ⟨rfl, hinj this⟩
      · subst h1
        have hc₂_old : c₂ ∈ processed := by
          rcases Finset.mem_insert.mp hc₂ with rfl | h
          · exact absurd rfl h2
          · exact h
        have hne : newTip j₁ = P.ext c₂ j₂ := by
          have ha : newExt c₁ j₁ = newTip j₁ := by simp [newExt]
          have hb : newExt c₂ j₂ = P.ext c₂ j₂ := by simp [newExt, h2]
          rw [ha, hb] at hext; exact hext
        exfalso
        have hmem_used : P.ext c₂ j₂ ∈ used := by
          refine Finset.mem_biUnion.mpr ⟨c₂, hc₂_old, ?_⟩
          exact Finset.mem_image.mpr ⟨j₂, Finset.mem_univ _, rfl⟩
        exact hfresh j₁ (by simp [totalForbidden, hne, hmem_used])
    · have hc₁_old : c₁ ∈ processed := by
        rcases Finset.mem_insert.mp hc₁ with rfl | h
        · exact absurd rfl h1
        · exact h
      by_cases h2 : c₂ = c
      · subst h2
        have hne : P.ext c₁ j₁ = newTip j₂ := by
          have ha : newExt c₁ j₁ = P.ext c₁ j₁ := by simp [newExt, h1]
          have hb : newExt c₂ j₂ = newTip j₂ := by simp [newExt]
          rw [ha, hb] at hext; exact hext
        exfalso
        have hmem_used : P.ext c₁ j₁ ∈ used := by
          refine Finset.mem_biUnion.mpr ⟨c₁, hc₁_old, ?_⟩
          exact Finset.mem_image.mpr ⟨j₁, Finset.mem_univ _, rfl⟩
        exact hfresh j₂ (by simp [totalForbidden, ← hne, hmem_used])
      · have hc₂_old : c₂ ∈ processed := by
          rcases Finset.mem_insert.mp hc₂ with rfl | h
          · exact absurd rfl h2
          · exact h
        have heq : P.ext c₁ j₁ = P.ext c₂ j₂ := by
          have ha : newExt c₁ j₁ = P.ext c₁ j₁ := by simp [newExt, h1]
          have hb : newExt c₂ j₂ = P.ext c₂ j₂ := by simp [newExt, h2]
          rw [ha, hb] at hext; exact hext
        exact P.ext_injective c₁ hc₁_old c₂ hc₂_old j₁ j₂ heq
  · intro c' hc' j
    rcases Finset.mem_insert.mp hc' with rfl | hc'_old
    · simp [newExt]
      intro h
      exact hfresh j (by simp [totalForbidden, h])
    · have hc'_ne : c' ≠ c := fun h => hc (h ▸ hc'_old)
      simp [newExt, hc'_ne]
      exact P.ext_not_mem_tree c' hc'_old j
  · intro c' hc' j
    rcases Finset.mem_insert.mp hc' with rfl | hc'_old
    · simp [newExt]
      intro h
      exact hfresh j (by simp [totalForbidden, h])
    · have hc'_ne : c' ≠ c := fun h => hc (h ▸ hc'_old)
      simp [newExt, hc'_ne]
      exact P.ext_not_mem_forbidden c' hc'_old j

/-- Greedy construction of `LeafExtensionData` from per-leaf filtered
neighborhood size: each leaf has ≥ d^(h+1) neighbours outside both `T` and
`forbidden`. -/
lemma exists_leafExtensionData_of_filter_saturation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d h : ℕ}
    (T : DAryTreeEmbedding G d h) (forbidden : Finset V)
    (hsat : ∀ (c : Fin h → Fin d),
      d ^ (h + 1) ≤
        ((G.neighborFinset (T.vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩)).filter
          fun y => y ∉ T.vertexFinset ∧ y ∉ forbidden).card) :
    ∃ E : LeafExtensionData T,
      (∀ c j, E.ext c j ∉ T.vertexFinset) ∧
      (∀ c j, E.ext c j ∉ forbidden) := by
  classical
  suffices h_all : Nonempty
      (PartialLeafExtension T forbidden (Finset.univ : Finset (Fin h → Fin d))) by
    obtain ⟨P⟩ := h_all
    refine ⟨{
      ext := P.ext
      ext_adj := fun c j => P.ext_adj c (Finset.mem_univ _) j
      ext_injective := fun c₁ c₂ j₁ j₂ h =>
        P.ext_injective c₁ (Finset.mem_univ _) c₂ (Finset.mem_univ _) j₁ j₂ h
      ext_not_mem_tree := fun c j => P.ext_not_mem_tree c (Finset.mem_univ _) j
    }, ?_, ?_⟩
    · intro c j
      exact P.ext_not_mem_tree c (Finset.mem_univ _) j
    · intro c j
      exact P.ext_not_mem_forbidden c (Finset.mem_univ _) j
  have hd_h : Fintype.card (Fin h → Fin d) = d ^ h := by
    rw [Fintype.card_fun]; simp
  suffices step : ∀ (S : Finset (Fin h → Fin d)),
      Nonempty (PartialLeafExtension T forbidden S) by
    exact step Finset.univ
  intro S
  induction S using Finset.induction with
  | empty =>
      refine ⟨{
        ext := fun _ _ => T.root
        ext_adj := fun c hc => absurd hc (Finset.notMem_empty _)
        ext_injective := fun c₁ hc₁ => absurd hc₁ (Finset.notMem_empty _)
        ext_not_mem_tree := fun c hc => absurd hc (Finset.notMem_empty _)
        ext_not_mem_forbidden := fun c hc => absurd hc (Finset.notMem_empty _)
      }⟩
  | @insert c S hcS ih =>
      obtain ⟨P⟩ := ih
      apply P.extend_of_filter T forbidden c hcS
      -- Since c ∉ S, S.card < d^h (strict).
      have hS_lt : S.card < d ^ h := by
        have hins : (insert c S).card ≤ d ^ h := by
          have h1 : (insert c S).card ≤ Fintype.card (Fin h → Fin d) :=
            Finset.card_le_univ _
          rw [hd_h] at h1
          exact h1
        rw [Finset.card_insert_of_notMem hcS] at hins
        omega
      have hbound : d * S.card + d ≤ d ^ (h + 1) := by
        have h1 : d * S.card + d = d * (S.card + 1) := by ring
        have h2 : d * (S.card + 1) ≤ d * d ^ h := Nat.mul_le_mul_left d hS_lt
        have h3 : d * d ^ h = d ^ (h + 1) := by rw [pow_succ, Nat.mul_comm]
        linarith
      exact le_trans hbound (hsat c)

lemma branchPath_internally_disjoint
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height)
    {i j : Fin d} (hij : i ≠ j) :
    ∀ v, v ∈ (branchPath T i).support → v ∈ (branchPath T j).support → v = T.root := by
  intro v hvi hvj
  have hv_tree : v ∈ T.vertexFinset := branchPath_support_subset_vertexFinset T i v hvi
  rw [vertexFinset] at hv_tree
  rcases Finset.mem_image.mp hv_tree with ⟨y, -, hyv⟩
  rw [← hyv] at hvi hvj ⊢
  by_cases hyzero : y.depth.val = 0
  · rw [DAryTreeIndex.eq_root_of_depth_eq_zero y hyzero, T.root_eq]
  · have hypos : 0 < y.depth.val := by omega
    have hi := branchPath_support_first_coord T i y hvi hypos
    have hj := branchPath_support_first_coord T j y hvj hypos
    exact False.elim (hij (hi.symm.trans hj))

/-- The canonical `d` root-to-leaf paths extracted from an embedded complete
`d`-ary tree. -/
def toDisjointPathStar {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {d height : ℕ} (T : DAryTreeEmbedding G d height) (hheight : 0 < height) :
    DisjointPathStar G d height where
  root := T.root
  tip := fun i => T.vertex (DAryTreeIndex.branchLeaf height i)
  path := fun i => branchPath T i
  path_isPath := fun i => branchPath_isPath T i
  path_length := fun i => branchPath_length T i
  tips_ne_root := fun i => branchPath_tip_ne_root T i hheight
  paths_internally_disjoint := fun _ _ hij => branchPath_internally_disjoint T hij
end DAryTreeEmbedding
namespace DisjointPathStar

/-- The vertices currently occupied by a `DisjointPathStar`.  This is the
finite set that serves as the initial seed for Bollobás's `T`-set. -/
def vertexFinset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d len : ℕ} (S : DisjointPathStar G d len) : Finset V :=
  insert S.root <| Finset.biUnion Finset.univ fun i => (S.path i).support.toFinset

lemma root_mem_vertexFinset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d len : ℕ} (S : DisjointPathStar G d len) :
    S.root ∈ S.vertexFinset := by
  simp [vertexFinset]
end DisjointPathStar

lemma Walk.support_dropLast_eq_of_not_nil {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : ¬ p.Nil) :
    p.dropLast.support = p.support.dropLast := by
  have hlen : 1 ≤ p.length := by
    rcases p with _ | ⟨_, _⟩
    · exact (hp (by simp)).elim
    · exact Nat.succ_le_succ (Nat.zero_le _)
  rw [SimpleGraph.Walk.dropLast,
      SimpleGraph.Walk.support_take,
      Nat.sub_add_cancel hlen,
      List.dropLast_eq_take, SimpleGraph.Walk.length_support,
      Nat.add_sub_cancel]

lemma Walk.mem_support_of_mem_dropLast {V : Type*} {G : SimpleGraph V}
    {u v w : V} {p : G.Walk u v} (hw : w ∈ p.dropLast.support) :
    w ∈ p.support := by
  cases p with
  | nil =>
      simpa using hw
  | cons h q =>
      rw [SimpleGraph.Walk.support_dropLast (by simp)] at hw
      exact (List.dropLast_sublist _).subset hw

lemma Walk.mem_support_dropLast_of_mem_ne_end {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v w : V} {p : G.Walk u v}
    (hw : w ∈ p.support) (hne : w ≠ v) :
    w ∈ p.dropLast.support := by
  cases p with
  | nil =>
      have : w = u := by simpa using hw
      exact False.elim (hne this)
  | cons h q =>
      have hmem : w ∈ (SimpleGraph.Walk.cons h q).support.dropLast := by
        exact List.mem_dropLast_of_mem_of_ne_getLast hw <| by
          simpa [SimpleGraph.Walk.getLast_support] using hne
      simpa [Walk.support_dropLast_eq_of_not_nil (p := SimpleGraph.Walk.cons h q) (by simp)] using hmem

lemma Walk.IsPath.dropLast {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.dropLast.IsPath := by
  cases p with
  | nil =>
      simp
  | cons h q =>
      have hnil : ¬ (SimpleGraph.Walk.cons h q).Nil := by simp
      have hadj : G.Adj (SimpleGraph.Walk.cons h q).penultimate _ :=
        (SimpleGraph.Walk.cons h q).adj_penultimate hnil
      have hconcat : (((SimpleGraph.Walk.cons h q).dropLast).concat hadj).IsPath := by
        simpa [SimpleGraph.Walk.concat_dropLast (p := SimpleGraph.Walk.cons h q) hadj] using hp
      simpa [SimpleGraph.Walk.concat_eq_append] using
        (SimpleGraph.Walk.IsPath.of_append_left
          (q := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil) hconcat)

lemma Walk.IsPath.end_not_mem_support_dropLast {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hnil : ¬ p.Nil) :
    v ∉ p.dropLast.support := by
  rw [Walk.support_dropLast_eq_of_not_nil (p := p) hnil]
  have hnodup : (p.support.dropLast ++ [v]).Nodup := by
    have hnodup' := hp.support_nodup
    rw [← List.dropLast_append_getLast (SimpleGraph.Walk.support_ne_nil p)] at hnodup'
    simpa [SimpleGraph.Walk.getLast_support] using hnodup'
  have hdisj : List.Disjoint p.support.dropLast [v] := List.disjoint_of_nodup_append hnodup
  rw [List.disjoint_iff_ne] at hdisj
  intro hv
  exact hdisj v hv v (by simp) rfl

lemma Walk.support_toFinset_append_cons_nil {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)).support.toFinset =
      insert w p.support.toFinset := by
  ext x
  rw [List.mem_toFinset]
  rw [SimpleGraph.Walk.support_append]
  simp [SimpleGraph.Walk.support_cons, or_comm]

/--
State object for the maximal `(Q,T)` argument inside `exists_fan_components`.

`treeVerts` models Bollobás's set `T`, while `spine` models the path `Q` ending
at the root of the current tree embedding.  The next proof attempt should make
this structure the main search object, rather than trying to solve
`exists_fan_components` in one shot.
-/
structure FanComponentState {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (d s : ℕ) where
  star : DisjointPathStar G d (s - 1)
  treeVerts : Finset V
  root_mem_treeVerts : star.root ∈ treeVerts
  star_subset_treeVerts :
    ∀ i, ∀ w ∈ (star.path i).support, w ∈ treeVerts
  tree_card_bound : treeVerts.card ≤ fanTreeThreshold d s
  spineStart : V
  spine : G.Walk spineStart star.root
  spine_isPath : spine.IsPath
  spine_internal_disjoint :
    ∀ w ∈ spine.support, w ≠ star.root → w ∉ treeVerts

/--
Structured version of `FanComponentState` whose tree component is an actual
embedded complete `d`-ary tree.  This is the object needed for Bollobás's
subtree-replacement maximality argument; `FanComponentState` is a coarse
projection consumed by the downstream fan-assembly code.
-/
structure EmbeddedFanComponentState {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d s : ℕ) where
  tree : DAryTreeEmbedding G d (s - 1)
  spineStart : V
  spine : G.Walk spineStart tree.root
  spine_isPath : spine.IsPath
  spine_internal_disjoint :
    ∀ w ∈ spine.support, w ≠ tree.root → w ∉ tree.vertexFinset

namespace FanComponentState

def score {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ} (C : FanComponentState G d s) : ℕ :=
  (C.treeVerts ∪ C.spine.support.toFinset).card

def IsMaximal {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ} (C : FanComponentState G d s) : Prop :=
  ∀ C' : FanComponentState G d s, C'.score ≤ C.score

end FanComponentState

/-- Choice of spine-attachment witnesses once the maximal `(Q,T)` state has been
constructed.  The only fact the downstream fan assembly needs is that every
representative tip sees a non-root vertex of the spine. -/
structure FanComponentAttachments
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ}
    (C : FanComponentState G d s) where
  attach : Fin d → V
  attach_mem_spine : ∀ i, attach i ∈ C.spine.support
  attach_ne_root : ∀ i, attach i ≠ C.star.root
  tip_adj_attach : ∀ i, G.Adj (C.star.tip i) (attach i)

/-- Once non-root spine attachments have been extracted, the final
`exists_fan_components` witness is just the spine with its last vertex removed,
plus the already embedded representative star. -/
lemma fan_component_attachments_to_components
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V}
    {d s : ℕ} (hd : d ≥ 2)
    (C : FanComponentState G d s)
    (A : FanComponentAttachments C) :
    ∃ (u v : V) (P : G.Walk u v),
      P.IsPath ∧
      ∃ (S : DisjointPathStar G d (s - 1)),
        (∀ i, ∀ w ∈ (S.path i).support, w ∉ P.support) ∧
        (∀ i : Fin d, ∃ e ∈ P.support, G.Adj (S.tip i) e) := by
  let i0 : Fin d := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hd⟩
  have hspine_nonnil : ¬ C.spine.Nil := by
    intro hnil
    have hstart : C.spineStart = C.star.root := hnil.eq
    have hsupport : C.spine.support = [C.spineStart] :=
      (SimpleGraph.Walk.nil_iff_support_eq).mp hnil
    have hroot : A.attach i0 = C.star.root := by
      have hmem : A.attach i0 ∈ [C.spineStart] := by
        simpa [hsupport] using A.attach_mem_spine i0
      simpa [hstart] using hmem
    exact (A.attach_ne_root i0) hroot
  refine ⟨C.spineStart, C.spine.penultimate, C.spine.dropLast,
    Walk.IsPath.dropLast (p := C.spine) C.spine_isPath, C.star, ?_, ?_⟩
  · intro i w hw_path hw_spine
    have h_tree : w ∈ C.treeVerts := C.star_subset_treeVerts i w hw_path
    have h_spine : w ∈ C.spine.support :=
      Walk.mem_support_of_mem_dropLast (p := C.spine) hw_spine
    by_cases hroot : w = C.star.root
    · exact
        (Walk.IsPath.end_not_mem_support_dropLast
          (p := C.spine) C.spine_isPath hspine_nonnil) (hroot ▸ hw_spine)
    · exact (C.spine_internal_disjoint w h_spine hroot) h_tree
  · intro i
    refine ⟨A.attach i, ?_, A.tip_adj_attach i⟩
    exact Walk.mem_support_dropLast_of_mem_ne_end
      (p := C.spine) (A.attach_mem_spine i) (A.attach_ne_root i)

namespace EmbeddedFanComponentState

def score {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ} (C : EmbeddedFanComponentState G d s) : ℕ :=
  (C.tree.vertexFinset ∪ C.spine.support.toFinset).card

def IsMaximal {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ} (C : EmbeddedFanComponentState G d s) : Prop :=
  ∀ C' : EmbeddedFanComponentState G d s, C'.score ≤ C.score

lemma heightOne_child_image_disjoint_spine {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (C : EmbeddedFanComponentState G d 2) :
    Disjoint
      (Finset.univ.image fun i : Fin d =>
        C.tree.vertex (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
          (by simp [DAryTreeIndex.root])))
      C.spine.support.toFinset := by
  rw [Finset.disjoint_left]
  intro w hw_child hw_spine
  rcases Finset.mem_image.mp hw_child with ⟨i, _hi, rfl⟩
  let child : DAryTreeIndex d 1 :=
    DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  have htree : C.tree.vertex child ∈ C.tree.vertexFinset :=
    C.tree.vertex_mem_vertexFinset child
  have hadj : G.Adj C.tree.root (C.tree.vertex child) := by
    rw [← C.tree.root_eq]
    exact C.tree.adj_child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  exact C.spine_internal_disjoint (C.tree.vertex child)
    (List.mem_toFinset.mp hw_spine) hadj.ne.symm htree

lemma heightOne_score_eq_spine_card_add {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (C : EmbeddedFanComponentState G d 2) :
    C.score = C.spine.support.toFinset.card + d := by
  let childImage : Finset V :=
    Finset.univ.image fun i : Fin d =>
      C.tree.vertex (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
        (by simp [DAryTreeIndex.root]))
  have htree : C.tree.vertexFinset = insert C.tree.root childImage := by
    simpa [childImage] using DAryTreeEmbedding.heightOne_vertexFinset_eq C.tree
  have hroot_spine : C.tree.root ∈ C.spine.support.toFinset := by
    exact List.mem_toFinset.mpr C.spine.end_mem_support
  have hdisj : Disjoint childImage C.spine.support.toFinset := by
    simpa [childImage] using C.heightOne_child_image_disjoint_spine
  have hchild_card : childImage.card = d := by
    simpa [childImage] using DAryTreeEmbedding.heightOne_child_image_card C.tree
  unfold score
  rw [htree]
  have hroot_union : C.tree.root ∈ childImage ∪ C.spine.support.toFinset := by
    exact Finset.mem_union_right childImage hroot_spine
  rw [Finset.insert_union, Finset.insert_eq_of_mem hroot_union]
  rw [Finset.card_union_of_disjoint hdisj, hchild_card, Nat.add_comm]

/-- Height-one branch-rerooting skeleton.  If an old first-level child has a
fresh height-one child family available, reroot the embedded tree there and
extend the old spine by the old root-child edge.  The cardinal improvement
needed for absorption is separate; this lemma verifies the replacement state
invariants. -/
lemma heightOne_reroot_at_child_state {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (C : EmbeddedFanComponentState G d 2)
    (i : Fin d) (newTip : Fin d → V)
    (htip_inj : Function.Injective newTip)
    (htip_adj :
      ∀ j, G.Adj
        (C.tree.vertex
          (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
            (by simp [DAryTreeIndex.root])))
        (newTip j))
    (htip_avoid_spine_root :
      ∀ j, newTip j ∉ C.spine.support.toFinset ∪ {C.tree.root}) :
    ∃ C' : EmbeddedFanComponentState G d 2,
      C'.tree.root =
        C.tree.vertex
          (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
            (by simp [DAryTreeIndex.root])) ∧
      C.spine.support.toFinset ⊆ C'.spine.support.toFinset ∧
      C'.spine.support.toFinset =
        insert
          (C.tree.vertex
            (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
              (by simp [DAryTreeIndex.root])))
          C.spine.support.toFinset ∧
      (∀ j, newTip j ∈ C'.tree.vertexFinset) := by
  let child : DAryTreeIndex d 1 :=
    DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  let x : V := C.tree.vertex child
  have hroot_child : G.Adj C.tree.root x := by
    rw [← C.tree.root_eq]
    exact C.tree.adj_child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  let newTree : DAryTreeEmbedding G d 1 :=
    DAryTreeEmbedding.heightOneOfChildren x newTip htip_inj htip_adj
  let newSpine : G.Walk C.spineStart newTree.root :=
    (C.spine.append (SimpleGraph.Walk.cons hroot_child SimpleGraph.Walk.nil)).copy rfl (by
      simp [newTree, DAryTreeEmbedding.heightOneOfChildren])
  have hx_tree : x ∈ C.tree.vertexFinset := C.tree.vertex_mem_vertexFinset child
  have hx_ne_root : x ≠ C.tree.root := hroot_child.ne.symm
  have hx_not_spine : x ∉ C.spine.support := by
    intro hx_spine
    exact C.spine_internal_disjoint x hx_spine hx_ne_root hx_tree
  have hpath_append :
      (C.spine.append (SimpleGraph.Walk.cons hroot_child SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    rw [SimpleGraph.Walk.support_append]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons]
    rw [List.nodup_append]
    refine ⟨C.spine_isPath.support_nodup, by simp, ?_⟩
    intro a ha b hb hab
    have hb_eq : b = x := by simpa using hb
    have ha_eq : a = x := hab.trans hb_eq
    exact hx_not_spine (by simpa [ha_eq] using ha)
  have hpath : newSpine.IsPath := by
    simpa [newSpine] using hpath_append
  have hdisj : ∀ w ∈ newSpine.support, w ≠ newTree.root → w ∉ newTree.vertexFinset := by
    intro w hw hw_ne_root hw_tree
    have hw_append :
        w ∈ (C.spine.append (SimpleGraph.Walk.cons hroot_child SimpleGraph.Walk.nil)).support := by
      simpa [newSpine] using hw
    rw [SimpleGraph.Walk.support_append] at hw_append
    simp [SimpleGraph.Walk.support_cons] at hw_append
    rw [DAryTreeEmbedding.heightOneOfChildren_vertexFinset_eq x newTip htip_inj htip_adj] at hw_tree
    rw [Finset.mem_insert] at hw_tree
    rcases hw_tree with hwx | hwtip
    · exact hw_ne_root (by simpa [newTree, DAryTreeEmbedding.heightOneOfChildren] using hwx)
    · rcases Finset.mem_image.mp hwtip with ⟨j, _hj, hjw⟩
      rcases hw_append with hw_spine | hw_tail
      · exact htip_avoid_spine_root j (by
          rw [Finset.mem_union]
          exact Or.inl (List.mem_toFinset.mpr (by simpa [hjw] using hw_spine)))
      · have hwx' : w = x := by simpa using hw_tail
        exact hw_ne_root (by
          simp [newTree, DAryTreeEmbedding.heightOneOfChildren, hwx'])
  have hsupport_eq :
      newSpine.support.toFinset = insert x C.spine.support.toFinset := by
    simpa [newSpine, newTree, DAryTreeEmbedding.heightOneOfChildren] using
      Walk.support_toFinset_append_cons_nil C.spine hroot_child
  refine ⟨{
    tree := newTree
    spineStart := C.spineStart
    spine := newSpine
    spine_isPath := hpath
    spine_internal_disjoint := hdisj
  }, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro w hw
    rw [hsupport_eq]
    exact Finset.mem_insert_of_mem hw
  · exact hsupport_eq
  · intro j
    change newTip j ∈ newTree.vertexFinset
    rw [DAryTreeEmbedding.heightOneOfChildren_vertexFinset_eq x newTip htip_inj htip_adj]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))

/-- The height-one rerooting skeleton is a genuine score improvement as soon
as the replacement tips avoid the old spine and the old root.  They do not need
to be globally fresh: old off-spine tree vertices can be reused by the new
height-one tree. -/
lemma exists_larger_heightOne_reroot_at_child_of_child_family_avoiding_spine_root {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (C : EmbeddedFanComponentState G d 2)
    (i : Fin d) (newTip : Fin d → V)
    (htip_inj : Function.Injective newTip)
    (htip_adj :
      ∀ j, G.Adj
        (C.tree.vertex
          (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
            (by simp [DAryTreeIndex.root])))
        (newTip j))
    (htip_avoid_spine_root :
      ∀ j, newTip j ∉ C.spine.support.toFinset ∪ {C.tree.root}) :
    ∃ C' : EmbeddedFanComponentState G d 2, C.score < C'.score := by
  let child : DAryTreeIndex d 1 :=
    DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  let x : V := C.tree.vertex child
  have hroot_child : G.Adj C.tree.root x := by
    rw [← C.tree.root_eq]
    exact C.tree.adj_child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  have hx_tree : x ∈ C.tree.vertexFinset := C.tree.vertex_mem_vertexFinset child
  have hx_ne_root : x ≠ C.tree.root := hroot_child.ne.symm
  have hx_not_spine : x ∉ C.spine.support.toFinset := by
    intro hx_spine
    exact C.spine_internal_disjoint x (List.mem_toFinset.mp hx_spine) hx_ne_root hx_tree
  obtain ⟨C', _hroot, _hspine_sub, hsupport_eq, _htip_mem⟩ :=
    C.heightOne_reroot_at_child_state i newTip htip_inj htip_adj
      htip_avoid_spine_root
  refine ⟨C', ?_⟩
  rw [C.heightOne_score_eq_spine_card_add, C'.heightOne_score_eq_spine_card_add]
  have hsupport_eq' :
      C'.spine.support.toFinset = insert x C.spine.support.toFinset := by
    simpa [child, x] using hsupport_eq
  rw [hsupport_eq']
  rw [Finset.card_insert_of_notMem hx_not_spine]
  omega

/-- Counting form of the stronger height-one obstruction: in a score-maximal
height-one embedded state, no old first-level child has `d` neighbours outside
the old spine and old root. -/
lemma heightOne_child_neighbors_outside_spine_root_card_lt_of_maximal {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (C : EmbeddedFanComponentState G d 2)
    (hmax : C.IsMaximal) (i : Fin d) :
    ((G.neighborFinset
        (C.tree.vertex
          (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
            (by simp [DAryTreeIndex.root])))).filter
        fun y => y ∉ C.spine.support.toFinset ∪ {C.tree.root}).card < d := by
  classical
  let child : DAryTreeIndex d 1 :=
    DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  let x : V := C.tree.vertex child
  let forbidden : Finset V := C.spine.support.toFinset ∪ {C.tree.root}
  let available : Finset V := (G.neighborFinset x).filter fun y => y ∉ forbidden
  by_contra hnot
  have havailable : d ≤ available.card := by
    exact not_lt.mp (by simpa [child, x, forbidden, available] using hnot)
  obtain ⟨t, ht_subset, ht_card⟩ := Finset.exists_subset_card_eq havailable
  obtain ⟨newTip, htip_inj, htip_mem⟩ :
      ∃ newTip : Fin d → V, Function.Injective newTip ∧ ∀ j, newTip j ∈ t := by
    have h_equiv : Nonempty (Fin d ≃ t) := by
      exact ⟨Fintype.equivOfCardEq (by simp [ht_card])⟩
    exact ⟨fun j => h_equiv.some j,
      Subtype.val_injective.comp h_equiv.some.injective,
      fun j => (h_equiv.some j).2⟩
  have htip_adj : ∀ j, G.Adj x (newTip j) := by
    intro j
    have hmem_available : newTip j ∈ available := ht_subset (htip_mem j)
    exact (G.mem_neighborFinset x (newTip j)).mp
      (Finset.mem_filter.mp hmem_available).1
  have htip_avoid : ∀ j, newTip j ∉ forbidden := by
    intro j
    have hmem_available : newTip j ∈ available := ht_subset (htip_mem j)
    exact (Finset.mem_filter.mp hmem_available).2
  obtain ⟨C', hlt⟩ :=
    C.exists_larger_heightOne_reroot_at_child_of_child_family_avoiding_spine_root
      i newTip htip_inj
      (by simpa [child, x] using htip_adj)
      (by simpa [forbidden] using htip_avoid)
  exact (not_le_of_gt hlt) (hmax C')

/-- Maximality + `fanThreshold d 2` minimum-degree hypothesis force every
first-level child to have at least `d` neighbours on the spine support, away
from the embedded root.

Proof: by min-degree, `2 * d ≤ deg(child_i)`.  By
`heightOne_child_neighbors_outside_spine_root_card_lt_of_maximal`, the number
of neighbours outside `Q.support ∪ {r}` is `< d`.  Subtracting, the number of
neighbours inside `Q.support ∪ {r}` is `≥ d + 1`.  Since `child_i` is adjacent
to the embedded root `r`, that accounts for one of these; the remaining `≥ d`
lie on `Q.support \ {r}`.

This is the crucial structural fact that lets the s = 2 maximal-pair argument
produce its tip attachments directly, without going through the absorption /
closure obligation. -/
lemma heightOne_child_neighbors_on_spine_off_root_card_ge_of_maximal {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (C : EmbeddedFanComponentState G d 2)
    (hd : 2 ≤ d)
    (hmax : C.IsMaximal)
    (hG : ∀ v : V, fanThreshold d 2 ≤ G.degree v) (i : Fin d) :
    d ≤
      ((G.neighborFinset
          (C.tree.vertex
            (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
              (by simp [DAryTreeIndex.root])))).filter
          fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root).card := by
  classical
  let child : DAryTreeIndex d 1 :=
    DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  let x : V := C.tree.vertex child
  -- The min-degree bound and the maximality obstruction together pin down the
  -- count of spine-side neighbours.
  have hdeg : 2 * d ≤ G.degree x := by
    have hthr : fanThreshold d 2 = 2 * d := by
      unfold fanThreshold
      rw [fanTreeThreshold_two d hd]; omega
    have := hG x
    omega
  -- The outside count is < d.
  have houtside : ((G.neighborFinset x).filter
        fun y => y ∉ C.spine.support.toFinset ∪ {C.tree.root}).card < d := by
    simpa [child, x] using
      C.heightOne_child_neighbors_outside_spine_root_card_lt_of_maximal hmax i
  -- Partition neighborFinset into outside ∪ inside (Q.support ∪ {r}).
  have hpart :
      (G.neighborFinset x).card =
        ((G.neighborFinset x).filter
            fun y => y ∉ C.spine.support.toFinset ∪ {C.tree.root}).card +
        ((G.neighborFinset x).filter
            fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root}).card := by
    rw [← Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset x) (p := fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root})]
    omega
  have hdeg_eq : G.degree x = (G.neighborFinset x).card := rfl
  -- Therefore the inside count is ≥ d + 1.
  have hinside :
      d + 1 ≤
        ((G.neighborFinset x).filter
            fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root}).card := by
    have : 2 * d ≤
        ((G.neighborFinset x).filter
            fun y => y ∉ C.spine.support.toFinset ∪ {C.tree.root}).card +
        ((G.neighborFinset x).filter
            fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root}).card := by
      calc 2 * d ≤ G.degree x := hdeg
        _ = (G.neighborFinset x).card := hdeg_eq
        _ = _ := hpart
    omega
  -- `r ∈ N(x)` since `x` is a child of `r` in the embedded tree.  Removing
  -- `r` from the inside set gives the desired ≥ d count on Q.support \ {r}.
  have hr_adj : G.Adj C.tree.root x := by
    rw [← C.tree.root_eq]
    exact C.tree.adj_child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root])
  have hr_mem : C.tree.root ∈ G.neighborFinset x := by
    exact (G.mem_neighborFinset x C.tree.root).mpr hr_adj.symm
  have hr_in_inside : C.tree.root ∈ (G.neighborFinset x).filter
      fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root} := by
    refine Finset.mem_filter.mpr ⟨hr_mem, ?_⟩
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
  -- The inside set partitions further into {r} ∪ (Q.support \ {r}-neighbours).
  -- More precisely, the filter {y ∈ N(x) | y ∈ Q.support ∧ y ≠ r} has size ≥ d.
  have hinside_eq :
      ((G.neighborFinset x).filter
          fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root}).card =
        ((G.neighborFinset x).filter
            fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root).card + 1 := by
    -- Pull out the `r` element.
    have hpartition : ((G.neighborFinset x).filter
          fun y => y ∈ C.spine.support.toFinset ∪ {C.tree.root}) =
        insert C.tree.root ((G.neighborFinset x).filter
            fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hzN, hzU⟩
        rcases hzU with hzQ | hzR
        · by_cases hzr : z = C.tree.root
          · exact Or.inl hzr
          · exact Or.inr ⟨hzN, hzQ, hzr⟩
        · exact Or.inl hzR
      · rintro (hzr | ⟨hzN, hzQ, hzr⟩)
        · refine ⟨?_, Or.inr hzr⟩
          rw [hzr]; exact hr_mem
        · exact ⟨hzN, Or.inl hzQ⟩
    rw [hpartition]
    rw [Finset.card_insert_of_notMem]
    intro hbad
    rcases Finset.mem_filter.mp hbad with ⟨_, _, hne⟩
    exact hne rfl
  have hgoal : d ≤ ((G.neighborFinset x).filter
      fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root).card := by
    omega
  simpa [child, x] using hgoal

/-- For height-one trees, the canonical "first-level child" index `child (root d 1) i`
and the `branchLeaf 1 i` index coincide. -/
lemma DAryTreeIndex.child_root_one_eq_branchLeaf {d : ℕ} (i : Fin d) :
    DAryTreeIndex.child (DAryTreeIndex.root d 1) i (by simp [DAryTreeIndex.root]) =
      DAryTreeIndex.branchLeaf (d := d) 1 i := by
  -- Both are records with depth 1 and constant coord `fun _ => i`.
  unfold DAryTreeIndex.child DAryTreeIndex.root DAryTreeIndex.branchLeaf
  congr 1

/-- Tip-attachment extraction for the height-one case.

Given a score-maximal `EmbeddedFanComponentState G d 2` under the
`fanThreshold` minimum-degree hypothesis, every `branchLeaf` tip of the
embedded tree has a non-root spine attachment.  The proof uses the
score-maximality consequence directly. -/
lemma exists_tip_attachment_of_maximal_heightOne_of_fanThreshold {V : Type*}
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (C : EmbeddedFanComponentState G d 2)
    (hd : 2 ≤ d)
    (hmax : C.IsMaximal)
    (hG : ∀ v : V, fanThreshold d 2 ≤ G.degree v) (i : Fin d) :
    ∃ e, e ∈ C.spine.support ∧ e ≠ C.tree.root ∧
      G.Adj (C.tree.vertex (DAryTreeIndex.branchLeaf 1 i)) e := by
  classical
  -- Use the maximality consequence: at least d neighbours of child_i on Q.support \ {r}.
  have hbound :=
    C.heightOne_child_neighbors_on_spine_off_root_card_ge_of_maximal hd hmax hG i
  -- The filter set is nonempty, so we can pick an element.
  have hpos : 0 < ((G.neighborFinset
        (C.tree.vertex
          (DAryTreeIndex.child (DAryTreeIndex.root d 1) i
            (by simp [DAryTreeIndex.root])))).filter
        fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root).card := by
    exact lt_of_lt_of_le (by omega : 0 < d) hbound
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp he with ⟨he_neigh, he_spine, he_ne_root⟩
  refine ⟨e, ?_, he_ne_root, ?_⟩
  · exact List.mem_toFinset.mp he_spine
  · -- Translate from child (root d 1) i to branchLeaf 1 i.
    rw [DAryTreeIndex.child_root_one_eq_branchLeaf] at he_neigh
    exact (G.mem_neighborFinset _ _).mp he_neigh

/-- **Key rerooting move for `s ≥ 3` absorption.**  Given an embedded state `C`
with tree height `h + 1 ≥ 2`, a branch index `i`, and `LeafExtensionData` for
the `i`-th first-level subtree whose extender vertices avoid both the original
tree and the spine, we can construct a strictly larger embedded state by:
- replacing the tree with `T_i.extendByOneLevel E` (rooted at `b_i`), and
- extending the spine by the edge `r → b_i`.

The score increase relies on the cardinal accounting: the new tree has the
same number of vertices as the old tree (both are complete d-ary trees of
height h + 1), but the new spine has one more vertex (the branch vertex `b_i`),
so the new occupied set has one more element.

Pin down the missing fresh vertex via a chosen leaf extender: it's in
`newTree.vertexFinset` (a new leaf-level extender) but in neither
`C.tree.vertexFinset` nor `C.spine.support.toFinset`. -/
lemma exists_larger_embedded_fan_component_state_of_extendByOneLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (hd : 2 ≤ d)
    (C : EmbeddedFanComponentState G d (h + 2)) (i : Fin d)
    (E : LeafExtensionData (C.tree.firstLevelSubtree i))
    (hE_avoid_spine : ∀ c j, E.ext c j ∉ C.spine.support.toFinset) :
    ∃ C' : EmbeddedFanComponentState G d (h + 2), C.score < C'.score := by
  classical
  let bi : V := C.tree.vertex
    (@DAryTreeIndex.child d (h + 1) (DAryTreeIndex.root d (h + 1)) i (by simp))
  let Ti : DAryTreeEmbedding G d h := C.tree.firstLevelSubtree i
  let newTree : DAryTreeEmbedding G d (h + 1) := Ti.extendByOneLevel E
  have hnewTree_root : newTree.root = bi := by
    simp [newTree, Ti, bi, DAryTreeEmbedding.extendByOneLevel_root,
      DAryTreeEmbedding.firstLevelSubtree_root]
  have hroot_adj_bi : G.Adj C.tree.root bi := by
    change G.Adj C.tree.root (C.tree.vertex _)
    rw [← C.tree.root_eq]
    exact C.tree.adj_child _ i (by simp [DAryTreeIndex.root])
  have hbi_in_tree : bi ∈ C.tree.vertexFinset := C.tree.vertex_mem_vertexFinset _
  have hbi_ne_root : bi ≠ C.tree.root := hroot_adj_bi.ne.symm
  have hbi_not_spine : bi ∉ C.spine.support := by
    intro hbi_spine
    exact C.spine_internal_disjoint bi hbi_spine hbi_ne_root hbi_in_tree
  let newSpine : G.Walk C.spineStart newTree.root :=
    (C.spine.append (SimpleGraph.Walk.cons hroot_adj_bi SimpleGraph.Walk.nil)).copy
      rfl (by rw [hnewTree_root])
  have hpath_append :
      (C.spine.append (SimpleGraph.Walk.cons hroot_adj_bi SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    rw [SimpleGraph.Walk.support_append]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons]
    rw [List.nodup_append]
    refine ⟨C.spine_isPath.support_nodup, by simp, ?_⟩
    intro a ha b hb hab
    have hb_eq : b = bi := by simpa using hb
    have ha_eq : a = bi := hab.trans hb_eq
    exact hbi_not_spine (by simpa [ha_eq] using ha)
  have hpath : newSpine.IsPath := by simpa [newSpine] using hpath_append
  have hsupport_eq : newSpine.support.toFinset = insert bi C.spine.support.toFinset := by
    simpa [newSpine] using Walk.support_toFinset_append_cons_nil C.spine hroot_adj_bi
  have hdisj : ∀ w ∈ newSpine.support, w ≠ newTree.root → w ∉ newTree.vertexFinset := by
    intro w hw hw_ne_root hw_tree
    have hw_append :
        w ∈ (C.spine.append (SimpleGraph.Walk.cons hroot_adj_bi SimpleGraph.Walk.nil)).support :=
      by simpa [newSpine] using hw
    rw [SimpleGraph.Walk.support_append] at hw_append
    simp [SimpleGraph.Walk.support_cons] at hw_append
    rcases hw_append with hw_spine | hw_tail
    · have hw_newTree : w ∈ newTree.vertexFinset := hw_tree
      rw [DAryTreeEmbedding.vertexFinset] at hw_newTree
      rcases Finset.mem_image.mp hw_newTree with ⟨y, _, hyw⟩
      by_cases hyle : y.depth.val ≤ h
      · have hwTi : w ∈ Ti.vertexFinset := by
          rw [← hyw]
          change DAryTreeEmbedding.extendVertex Ti E y ∈ Ti.vertexFinset
          rw [DAryTreeEmbedding.extendVertex_le Ti E y hyle]
          exact Ti.vertex_mem_vertexFinset _
        have hwTi_eq : Ti.vertexFinset = C.tree.firstLevelSubtreeVerts i :=
          DAryTreeEmbedding.firstLevelSubtree_vertexFinset_eq C.tree i
        rw [hwTi_eq] at hwTi
        have hwC : w ∈ C.tree.vertexFinset :=
          C.tree.firstLevelSubtreeVerts_subset_vertexFinset i hwTi
        have hwroot : w = C.tree.root := by
          by_contra hwne
          exact C.spine_internal_disjoint w hw_spine hwne hwC
        rw [hwroot] at hwTi
        exact C.tree.root_not_mem_firstLevelSubtreeVerts i hwTi
      · have hyeq : y.depth.val = h + 1 := by have := y.depth.isLt; omega
        have hw_ext : w = E.ext (y.leafCoord hyeq) (y.leafLast hyeq) := by
          rw [← hyw]
          change DAryTreeEmbedding.extendVertex Ti E y = _
          exact DAryTreeEmbedding.extendVertex_eq Ti E y hyeq
        rw [hw_ext] at hw_spine
        exact hE_avoid_spine _ _ (List.mem_toFinset.mpr hw_spine)
    · have hw_bi : w = bi := by simpa using hw_tail
      exact hw_ne_root (by rw [hw_bi, ← hnewTree_root])
  let C' : EmbeddedFanComponentState G d (h + 2) := {
    tree := newTree
    spineStart := C.spineStart
    spine := newSpine
    spine_isPath := hpath
    spine_internal_disjoint := hdisj
  }
  refine ⟨C', ?_⟩
  -- Score comparison via cardinal calculation.
  -- C and C' trees both have height h+1, so both have fanTreeThreshold d (h+2) vertices.
  -- Each tree's intersection with its spine is the single endpoint (tree.root, newTree.root).
  -- The new spine support has one more vertex than the old (b_i is added).
  -- Therefore C'.score = C.score + 1.
  have hC_card : C.tree.vertexFinset.card = fanTreeThreshold d (h + 2) := by
    have := C.tree.vertexFinset_card_threshold hd
    simpa using this
  have hC'_card : C'.tree.vertexFinset.card = fanTreeThreshold d (h + 2) := by
    have := newTree.vertexFinset_card_threshold hd
    simpa [C', newTree, Ti] using this
  have hC_inter : C.tree.vertexFinset ∩ C.spine.support.toFinset = {C.tree.root} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hwt, hws⟩
      by_contra hwne
      exact C.spine_internal_disjoint w (List.mem_toFinset.mp hws) hwne hwt
    · rintro rfl
      exact ⟨C.tree.root_mem_vertexFinset,
        List.mem_toFinset.mpr C.spine.end_mem_support⟩
  have hC'_inter : C'.tree.vertexFinset ∩ C'.spine.support.toFinset = {newTree.root} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hwt, hws⟩
      by_contra hwne
      exact hdisj w (List.mem_toFinset.mp hws) hwne hwt
    · rintro rfl
      refine ⟨newTree.root_mem_vertexFinset, ?_⟩
      exact List.mem_toFinset.mpr C'.spine.end_mem_support
  have hC_score : C.score = fanTreeThreshold d (h + 2) + C.spine.support.toFinset.card - 1 := by
    unfold EmbeddedFanComponentState.score
    rw [Finset.card_union, hC_card, hC_inter]
    simp
  have hC'_score : C'.score = fanTreeThreshold d (h + 2) + C'.spine.support.toFinset.card - 1 := by
    unfold EmbeddedFanComponentState.score
    rw [Finset.card_union, hC'_card, hC'_inter]
    simp
  have hC'_spine_card : C'.spine.support.toFinset.card = C.spine.support.toFinset.card + 1 := by
    change newSpine.support.toFinset.card = _
    rw [hsupport_eq]
    rw [Finset.card_insert_of_notMem]
    intro hbi_spine
    exact hbi_not_spine (List.mem_toFinset.mp hbi_spine)
  have hspine_pos : 0 < C.spine.support.toFinset.card := by
    rw [Finset.card_pos]
    exact List.toFinset_nonempty_iff _ |>.mpr (List.ne_nil_of_mem C.spine.start_mem_support)
  rw [hC_score, hC'_score, hC'_spine_card]
  have ht_pos : 0 < fanTreeThreshold d (h + 2) := fanTreeThreshold_pos d (h + 1) hd
  omega

/-- **Per-branch maximality consequence.**  In a score-maximal embedded state
`C : EmbeddedFanComponentState G d (h + 2)` with `d ≥ 2`, for every branch `i`,
some leaf of the i-th first-level subtree `T_i` fails to have `d^(h+1)`
neighbours outside `C.tree.vertexFinset ∪ C.spine.support`.

This is the contrapositive of Step A+B: if every leaf were saturated, we
could extend `T_i` and contradict maximality. -/
lemma exists_branch_leaf_unsaturated_of_maximal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d h : ℕ} (hd : 2 ≤ d)
    (C : EmbeddedFanComponentState G d (h + 2)) (hmax : C.IsMaximal)
    (i : Fin d) :
    ∃ c : Fin h → Fin d,
      ((G.neighborFinset
          ((C.tree.firstLevelSubtree i).vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩)).filter
        fun y => y ∉ (C.tree.firstLevelSubtree i).vertexFinset ∧
                 y ∉ C.spine.support.toFinset).card < d ^ (h + 1) := by
  by_contra hcontra
  push Not at hcontra
  -- Every leaf c is saturated.  Apply the greedy lemma to build LeafExtensionData
  -- for T_i with forbidden = C.spine.support.toFinset.
  obtain ⟨E, _hE_avoid_Ti, hE_avoid_spine⟩ :=
    DAryTreeEmbedding.exists_leafExtensionData_of_filter_saturation
      (C.tree.firstLevelSubtree i) C.spine.support.toFinset hcontra
  -- Now apply Step B to derive a larger state — contradicting maximality.
  obtain ⟨C', hlt⟩ :=
    exists_larger_embedded_fan_component_state_of_extendByOneLevel hd C i E hE_avoid_spine
  exact not_le_of_gt hlt (hmax C')

/-- **Per-branch d-attachments from maximality.**  Combining the per-branch
unsaturation consequence with `bollobas_counting` and the min-degree
hypothesis: for every branch `i`, some leaf of `T_i` has at least `d`
neighbours on `C.spine.support \ {C.tree.root}`. -/
lemma exists_branch_leaf_with_d_spine_attachments_of_maximal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d h : ℕ} (hd : 2 ≤ d)
    (C : EmbeddedFanComponentState G d (h + 2)) (hmax : C.IsMaximal)
    (hG : ∀ v : V, fanThreshold d (h + 2) ≤ G.degree v) (i : Fin d) :
    ∃ c : Fin h → Fin d,
      d ≤
        ((G.neighborFinset
            ((C.tree.firstLevelSubtree i).vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩)).filter
          fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root).card := by
  classical
  obtain ⟨c, hcunsat⟩ := exists_branch_leaf_unsaturated_of_maximal hd C hmax i
  refine ⟨c, ?_⟩
  -- Let leaf := (T_i).vertex ⟨⟨h, _⟩, c⟩.
  let Ti := C.tree.firstLevelSubtree i
  let leaf : V := Ti.vertex ⟨⟨h, Nat.lt_succ_self _⟩, c⟩
  -- Decompose N(leaf) into three pieces: in T_i, in spine, in outside (=  ¬T_i ∧ ¬spine).
  -- For the leaf c, leaf ∈ T_i. Use leaf's degree bound.
  -- Step 1: |N(leaf) ∩ T_i| ≤ |T_i| - 1 = M_(h+1) - 1.
  have hleaf_mem_Ti : leaf ∈ Ti.vertexFinset := Ti.vertex_mem_vertexFinset _
  have hTi_card : Ti.vertexFinset.card = fanTreeThreshold d (h + 1) := by
    have := Ti.vertexFinset_card_threshold hd
    simpa using this
  -- Step 2: N(leaf) partition.
  -- N(leaf) = (N(leaf) ∩ T_i \ {leaf}) ⊎ (N(leaf) ∩ spine) ⊎ (N(leaf) ∩ outside)
  -- ⊎ (other overlaps).
  -- More carefully, since N(leaf) ⊆ V and {T_i, spine, outside_total} = V (almost),
  -- decompose: every y ∈ N(leaf) is in (T_i ∪ spine ∪ ¬(T_i ∪ spine)).
  -- |N(leaf) ∩ T_i| + |N(leaf) ∩ (spine \ T_i)| + |N(leaf) ∩ outside| = deg(leaf).
  -- Actually use the partition by membership in T_i ∪ spine.
  -- The "outside" filter: y ∉ T_i ∧ y ∉ spine.
  -- So N(leaf) = (N(leaf) ∩ outside) ⊎ (N(leaf) \ outside)
  --           = (N(leaf) ∩ outside) ⊎ (N(leaf) ∩ (T_i ∪ spine)).
  -- |N(leaf) ∩ outside| < d^(h+1) by hcunsat.
  -- |N(leaf) ∩ (T_i ∪ spine)| = (deg(leaf)) - |N(leaf) ∩ outside| ≥ (M_{h+2} + d - 1) - (d^{h+1} - 1)
  --                          = M_{h+2} + d - d^{h+1}.
  -- |N(leaf) ∩ T_i| ≤ |T_i \ {leaf}| = M_{h+1} - 1 (since leaf is a tree vertex but
  --   N(leaf) is just the neighbors, none of which equal leaf).
  -- So |N(leaf) ∩ spine| ≥ |N(leaf) ∩ (T_i ∪ spine)| - |N(leaf) ∩ T_i|
  --                    ≥ (M_{h+2} + d - d^{h+1}) - (M_{h+1} - 1)
  --                    = M_{h+2} - M_{h+1} - d^{h+1} + d + 1
  --                    = 0 + d + 1 = d + 1.
  -- Subtract the root (which is in both N(leaf) and spine) to get ≥ d.
  set outside : Finset V := (G.neighborFinset leaf).filter
    fun y => y ∉ Ti.vertexFinset ∧ y ∉ C.spine.support.toFinset with houtside_def
  have houtside_lt : outside.card < d ^ (h + 1) := by simpa [outside] using hcunsat
  -- Decomposition: N(leaf) = (filter outside) ∪ (filter ¬outside).
  -- (filter ¬outside) = N(leaf) ∩ (T_i ∪ spine).
  set notOutside : Finset V := (G.neighborFinset leaf).filter
    fun y => y ∈ Ti.vertexFinset ∨ y ∈ C.spine.support.toFinset with hnotOutside_def
  have hpartition_deg :
      outside.card + notOutside.card = G.degree leaf := by
    have h := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset leaf)
      (p := fun y => y ∉ Ti.vertexFinset ∧ y ∉ C.spine.support.toFinset)
    -- Show notOutside = filter (negation).
    have heq : notOutside = (G.neighborFinset leaf).filter
        fun y => ¬ (y ∉ Ti.vertexFinset ∧ y ∉ C.spine.support.toFinset) := by
      apply Finset.filter_congr
      intro y _
      tauto
    rw [heq]
    have : outside.card +
        ((G.neighborFinset leaf).filter
          fun y => ¬ (y ∉ Ti.vertexFinset ∧ y ∉ C.spine.support.toFinset)).card =
      (G.neighborFinset leaf).card := by
      simpa [outside] using h
    have : outside.card +
        ((G.neighborFinset leaf).filter
          fun y => ¬ (y ∉ Ti.vertexFinset ∧ y ∉ C.spine.support.toFinset)).card =
      G.degree leaf := this
    exact this
  -- N(leaf) ∩ T_i is contained in T_i.erase leaf — but actually loopless means leaf ∉ N(leaf),
  -- so N(leaf) ∩ T_i ⊆ T_i.erase leaf.
  set inTi : Finset V := (G.neighborFinset leaf).filter fun y => y ∈ Ti.vertexFinset
    with hinTi_def
  have hinTi_card_le : inTi.card ≤ fanTreeThreshold d (h + 1) - 1 := by
    have hsub : inTi ⊆ Ti.vertexFinset.erase leaf := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyN, hyTi⟩
      refine Finset.mem_erase.mpr ⟨?_, hyTi⟩
      intro hyeq
      have : ¬ G.Adj leaf leaf := G.loopless.irrefl leaf
      exact this (by simpa [hyeq] using (G.mem_neighborFinset _ _).mp hyN)
    calc inTi.card ≤ (Ti.vertexFinset.erase leaf).card := Finset.card_le_card hsub
      _ = fanTreeThreshold d (h + 1) - 1 := by
          rw [Finset.card_erase_of_mem hleaf_mem_Ti, hTi_card]
  -- The filter we care about: in spine, not root.
  set inSpineOffRoot : Finset V := (G.neighborFinset leaf).filter
    fun y => y ∈ C.spine.support.toFinset ∧ y ≠ C.tree.root with hinSpineOffRoot_def
  -- In spine total.
  set inSpine : Finset V := (G.neighborFinset leaf).filter
    fun y => y ∈ C.spine.support.toFinset with hinSpine_def
  -- N(leaf) ∩ (T_i ∪ spine) ⊆ (N(leaf) ∩ T_i) ∪ (N(leaf) ∩ spine).
  have hnotOutside_le : notOutside.card ≤ inTi.card + inSpine.card := by
    have hsub : notOutside ⊆ inTi ∪ inSpine := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyN, hcase⟩
      rcases hcase with hyT | hyS
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyN, hyT⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyN, hyS⟩)
    calc notOutside.card ≤ (inTi ∪ inSpine).card := Finset.card_le_card hsub
      _ ≤ inTi.card + inSpine.card := Finset.card_union_le _ _
  -- inSpine - 1 ≤ inSpineOffRoot if root is in inSpine, else inSpine ≤ inSpineOffRoot.
  -- Specifically: inSpineOffRoot ⊆ inSpine, and the difference is at most 1 (the root).
  have hinSpineOffRoot_ge : inSpine.card ≤ inSpineOffRoot.card + 1 := by
    have hsub : inSpine ⊆ insert C.tree.root inSpineOffRoot := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyN, hyS⟩
      by_cases hyr : y = C.tree.root
      · exact Finset.mem_insert.mpr (Or.inl hyr)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hyN, hyS, hyr⟩))
    calc inSpine.card ≤ (insert C.tree.root inSpineOffRoot).card := Finset.card_le_card hsub
      _ ≤ inSpineOffRoot.card + 1 := Finset.card_insert_le _ _
  -- Min-degree.
  have hdeg : fanThreshold d (h + 2) ≤ G.degree leaf := hG leaf
  have hfan_eq : fanThreshold d (h + 2) = fanTreeThreshold d (h + 2) + (d - 1) := by
    unfold fanThreshold
    have h1 : d ≤ fanTreeThreshold d (h + 2) := by
      have h_step := one_add_d_le_fanTreeThreshold_succ_succ d h hd
      omega
    omega
  -- bollobas_counting: 2 ≤ M_{h+2} - (M_{h+1} - 1) - (d^{h+1} - 1).
  have hcount := bollobas_counting d (h + 2) hd (by omega)
  simp only [show (h + 2) - 1 = h + 1 from rfl] at hcount
  -- Pulling all bounds together:
  -- deg ≥ M_{h+2} + d - 1
  -- deg = outside + notOutside
  -- outside < d^{h+1}
  -- notOutside ≤ inTi + inSpine
  -- inTi ≤ M_{h+1} - 1
  -- inSpine ≤ inSpineOffRoot + 1
  -- Therefore:
  -- M_{h+2} + d - 1 ≤ deg = outside + notOutside
  --                ≤ (d^{h+1} - 1) + (M_{h+1} - 1) + inSpineOffRoot + 1
  --                = d^{h+1} + M_{h+1} - 1 + inSpineOffRoot
  -- So inSpineOffRoot ≥ M_{h+2} + d - 1 - d^{h+1} - M_{h+1} + 1
  --                  = (M_{h+2} - M_{h+1} - d^{h+1}) + d
  --                  ≥ 0 + d = d (using bollobas_counting which gives ≥ 2 of the bracket).
  -- The arithmetic via omega.
  have hMpos : 0 < fanTreeThreshold d (h + 1) := fanTreeThreshold_pos d h hd
  have hM2pos : 0 < fanTreeThreshold d (h + 2) := fanTreeThreshold_pos d (h + 1) hd
  have hdpos : 0 < d := by omega
  have hdpow : 0 < d ^ (h + 1) := pow_pos hdpos (h + 1)
  show d ≤ inSpineOffRoot.card
  -- Reform hcount: 2 + (M_{h+1} - 1) + (d^{h+1} - 1) ≤ M_{h+2}.
  -- I.e., M_{h+1} + d^{h+1} ≤ M_{h+2}.
  have hcount' : fanTreeThreshold d (h + 1) + d ^ (h + 1) ≤ fanTreeThreshold d (h + 2) := by
    have : 2 ≤ fanTreeThreshold d (h + 2) - (fanTreeThreshold d (h + 1) - 1) - (d ^ (h + 1) - 1) :=
      hcount
    omega
  omega

/-! ### Fan construction for `s ≥ 3` via per-branch leaf attachments -/

/-- Per-branch chosen-leaf data extracted from the maximality consequence.
For each branch `i`, we record:
- a leaf coordinate `c i : Fin h → Fin d` indexing some unsaturated leaf of `T_i`
- a spine attachment `e i ∈ C.spine.support` with `e i ≠ C.tree.root` and
  `G.Adj (leaf at c i) (e i)`. -/
structure BranchLeafAttachments {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ} (C : EmbeddedFanComponentState G d (h + 2)) where
  /-- Per-branch chosen leaf coordinate inside the i-th first-level subtree. -/
  c : Fin d → (Fin h → Fin d)
  /-- Per-branch spine attachment vertex. -/
  e : Fin d → V
  e_mem_spine : ∀ i, e i ∈ C.spine.support
  e_ne_root : ∀ i, e i ≠ C.tree.root
  leaf_adj_e : ∀ i, G.Adj
    ((C.tree.firstLevelSubtree i).vertex ⟨⟨h, Nat.lt_succ_self _⟩, c i⟩) (e i)

/-- Extract `BranchLeafAttachments` from the per-branch d-attachments lemma. -/
lemma exists_branchLeafAttachments_of_maximal
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d h : ℕ} (hd : 2 ≤ d)
    (C : EmbeddedFanComponentState G d (h + 2)) (hmax : C.IsMaximal)
    (hG : ∀ v : V, fanThreshold d (h + 2) ≤ G.degree v) :
    Nonempty (BranchLeafAttachments C) := by
  classical
  refine ⟨{
    c := fun i =>
      Classical.choose (exists_branch_leaf_with_d_spine_attachments_of_maximal hd C hmax hG i)
    e := fun i =>
      Classical.choose (Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < d)
        (Classical.choose_spec
          (exists_branch_leaf_with_d_spine_attachments_of_maximal hd C hmax hG i))))
    e_mem_spine := ?_
    e_ne_root := ?_
    leaf_adj_e := ?_
  }⟩
  all_goals (
    intro i
    set hspec := Classical.choose_spec
      (exists_branch_leaf_with_d_spine_attachments_of_maximal hd C hmax hG i)
    set he := Classical.choose_spec (Finset.card_pos.mp
      (lt_of_lt_of_le (by omega : 0 < d) hspec))
    rcases Finset.mem_filter.mp he with ⟨hN, hQ, hRoot⟩
  )
  · exact List.mem_toFinset.mp hQ
  · exact hRoot
  · exact (G.mem_neighborFinset _ _).mp hN

/-- The custom `DisjointPathStar` built from `BranchLeafAttachments` data:
paths are root-to-chosen-leaf walks in `C.tree`; the disjointness follows
because paths to different branches share only the tree root. -/
def BranchLeafAttachments.toDisjointPathStar
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d h : ℕ}
    {C : EmbeddedFanComponentState G d (h + 2)}
    (A : BranchLeafAttachments C) :
    DisjointPathStar G d (h + 1) where
  root := C.tree.root
  tip := fun i =>
    (C.tree.firstLevelSubtree i).vertex ⟨⟨h, Nat.lt_succ_self _⟩, A.c i⟩
  path := fun i =>
    let x : DAryTreeIndex d (h + 1) :=
      DAryTreeIndex.consFirst i ⟨⟨h, Nat.lt_succ_self _⟩, A.c i⟩ (Nat.succ_pos _)
    (DAryTreeEmbedding.rootToNodeWalkFromRoot C.tree x).copy rfl
      (by simp [x, DAryTreeEmbedding.firstLevelSubtree_vertex])
  path_isPath := fun i => by
    simp only
    rw [SimpleGraph.Walk.isPath_copy]
    exact DAryTreeEmbedding.rootToNodeWalkFromRoot_isPath _ _
  path_length := fun i => by
    simp only
    rw [SimpleGraph.Walk.length_copy]
    rw [DAryTreeEmbedding.rootToNodeWalkFromRoot_length]
    simp [DAryTreeIndex.consFirst]
  tips_ne_root := fun i => by
    intro hEq
    have : (C.tree.firstLevelSubtree i).vertex ⟨⟨h, Nat.lt_succ_self _⟩, A.c i⟩ =
        C.tree.vertex (DAryTreeIndex.consFirst i ⟨⟨h, Nat.lt_succ_self _⟩, A.c i⟩
          (Nat.succ_pos _)) := by
      simp [DAryTreeEmbedding.firstLevelSubtree_vertex]
    rw [this] at hEq
    have hroot_eq : C.tree.vertex (DAryTreeIndex.root d (h + 1)) = C.tree.root :=
      C.tree.root_eq
    rw [← hroot_eq] at hEq
    have hidx_eq : (DAryTreeIndex.consFirst i ⟨⟨h, Nat.lt_succ_self _⟩, A.c i⟩
      (Nat.succ_pos _) : DAryTreeIndex d (h + 1)) = DAryTreeIndex.root d (h + 1) :=
      C.tree.injective hEq
    have hdepth :
        (DAryTreeIndex.consFirst i ⟨⟨h, Nat.lt_succ_self _⟩, A.c i⟩ (Nat.succ_pos _)).depth.val =
          (DAryTreeIndex.root d (h + 1)).depth.val :=
      congrArg (fun z : DAryTreeIndex d (h + 1) => z.depth.val) hidx_eq
    simp [DAryTreeIndex.consFirst, DAryTreeIndex.root] at hdepth
  paths_internally_disjoint := fun i j hij v hvi hvj => by
    simp only at hvi hvj
    rw [SimpleGraph.Walk.support_copy] at hvi hvj
    have hv_treei :
        v ∈ C.tree.vertexFinset := by
      exact DAryTreeEmbedding.rootToNodeWalkFromRoot_support_subset_vertexFinset
        C.tree _ v hvi
    rw [DAryTreeEmbedding.vertexFinset] at hv_treei
    rcases Finset.mem_image.mp hv_treei with ⟨y, _, rfl⟩
    by_cases hypos : 0 < y.depth.val
    · have hci :=
        DAryTreeEmbedding.rootToNodeWalkFromRoot_support_first_coord C.tree _ (by
          simp [DAryTreeIndex.consFirst]) y hvi hypos
      have hcj :=
        DAryTreeEmbedding.rootToNodeWalkFromRoot_support_first_coord C.tree _ (by
          simp [DAryTreeIndex.consFirst]) y hvj hypos
      simp [DAryTreeIndex.consFirst] at hci hcj
      exact absurd
        (show i = j by
          first
          | exact hci.trans hcj.symm
          | exact hci.symm.trans hcj) hij
    · have hyzero : y.depth.val = 0 := by omega
      have hyroot := DAryTreeIndex.eq_root_of_depth_eq_zero y hyzero
      rw [hyroot, C.tree.root_eq]

/-- Build a `BollobasFan G d (h + 2)` from `BranchLeafAttachments` data.

The fan is assembled directly from per-branch chosen leaves and their
non-root spine attachments — the maximality consequence packaged in
`BranchLeafAttachments` is precisely what the construction needs.  This
parallels the `s = 2` case handled by
`embedded_fan_component_state_components_of_maximal_heightOne`. -/
lemma BranchLeafAttachments.toBollobasFan
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d h : ℕ} (hd : 2 ≤ d)
    {C : EmbeddedFanComponentState G d (h + 2)}
    (A : BranchLeafAttachments C) :
    Nonempty (BollobasFan G d (h + 2)) := by
  classical
  let star : DisjointPathStar G d (h + 1) := A.toDisjointPathStar
  -- Build a FanComponentState whose star is `star`.
  let cFan : FanComponentState G d (h + 2) := {
    star := by simpa using star
    treeVerts := C.tree.vertexFinset
    root_mem_treeVerts := by
      change star.root ∈ C.tree.vertexFinset
      simp [star, BranchLeafAttachments.toDisjointPathStar]
      exact C.tree.root_mem_vertexFinset
    star_subset_treeVerts := by
      intro i w hw
      -- w ∈ (star.path i).support ⊆ C.tree.vertexFinset.
      change w ∈ (A.toDisjointPathStar.path i).support at hw
      simp only [BranchLeafAttachments.toDisjointPathStar] at hw
      rw [SimpleGraph.Walk.support_copy] at hw
      exact DAryTreeEmbedding.rootToNodeWalkFromRoot_support_subset_vertexFinset
        C.tree _ w hw
    tree_card_bound := by
      have hcard := C.tree.vertexFinset_card_threshold hd
      simp at hcard
      simp [hcard]
    spineStart := C.spineStart
    spine := by
      -- spine has type G.Walk spineStart (star.root) = G.Walk spineStart C.tree.root.
      change G.Walk C.spineStart C.tree.root
      exact C.spine
    spine_isPath := C.spine_isPath
    spine_internal_disjoint := by
      intro w hw hne
      -- hne: w ≠ star.root = C.tree.root.
      change w ≠ C.tree.root at hne
      intro hwtree
      exact C.spine_internal_disjoint w hw hne hwtree
  }
  -- Provide FanComponentAttachments using the A.e attachments.
  let attach : FanComponentAttachments cFan := {
    attach := A.e
    attach_mem_spine := by
      intro i
      exact A.e_mem_spine i
    attach_ne_root := by
      intro i
      simp [cFan, star, BranchLeafAttachments.toDisjointPathStar]
      exact A.e_ne_root i
    tip_adj_attach := by
      intro i
      simp [cFan, star, BranchLeafAttachments.toDisjointPathStar]
      exact A.leaf_adj_e i
  }
  obtain ⟨u, v, P, hP, S, hS_disj, hS_conn⟩ :=
    fan_component_attachments_to_components hd cFan attach
  exact fan_from_components hd (by omega) P hP S hS_disj hS_conn

def star {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ} (C : EmbeddedFanComponentState G d s)
    (hs : s ≥ 2) : DisjointPathStar G d (s - 1) :=
  C.tree.toDisjointPathStar (by omega)

def toFanComponentState {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ} (C : EmbeddedFanComponentState G d s)
    (hd : d ≥ 2) (hs : s ≥ 2) : FanComponentState G d s where
  star := C.star hs
  treeVerts := C.tree.vertexFinset
  root_mem_treeVerts := C.tree.root_mem_vertexFinset
  star_subset_treeVerts := by
    intro i w hw
    exact DAryTreeEmbedding.branchPath_support_subset_vertexFinset C.tree i w hw
  tree_card_bound := by
    have hcard := C.tree.vertexFinset_card_threshold hd
    rw [hcard]
    have hs_eq : s - 1 + 1 = s := Nat.sub_add_cancel (by omega : 1 ≤ s)
    rw [hs_eq]
  spineStart := C.spineStart
  spine := C.spine
  spine_isPath := C.spine_isPath
  spine_internal_disjoint := by
    intro w hw hroot
    exact C.spine_internal_disjoint w hw hroot
end EmbeddedFanComponentState

lemma exists_maximal_embedded_fan_component_state
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d s : ℕ)
    (hinit : Nonempty (EmbeddedFanComponentState G d s)) :
    ∃ C : EmbeddedFanComponentState G d s, C.IsMaximal := by
  have hfinite :
      (EmbeddedFanComponentState.score '' (Set.univ : Set (EmbeddedFanComponentState G d s))).Finite := by
    refine (Set.finite_Iic (Fintype.card V)).subset ?_
    intro n hn
    rcases hn with ⟨C, -, rfl⟩
    exact Finset.card_le_univ _
  obtain ⟨C, hCmax⟩ :=
    Set.Finite.exists_maximalFor'
      (f := EmbeddedFanComponentState.score)
      (s := (Set.univ : Set (EmbeddedFanComponentState G d s)))
      hfinite (by simp)
  refine ⟨C, ?_⟩
  intro C'
  exact hCmax.le (by simp)

lemma exists_initial_embedded_fan_component_state_of_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ}
    (T : DAryTreeEmbedding G d (s - 1)) :
    Nonempty (EmbeddedFanComponentState G d s) := by
  refine ⟨{
    tree := T
    spineStart := T.root
    spine := SimpleGraph.Walk.nil
    spine_isPath := SimpleGraph.Walk.IsPath.nil
    spine_internal_disjoint := ?_
  }⟩
  intro w hw hneq
  simp at hw
  exact (hneq hw).elim

lemma exists_initial_embedded_fan_component_state_height_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d)
    (hG : ∀ v : V, fanThreshold d 2 ≤ G.degree v) :
    Nonempty (EmbeddedFanComponentState G d 2) := by
  let v : V := Classical.arbitrary V
  have hv : d ≤ G.degree v :=
    le_trans (d_le_fanThreshold d 2 hd (by omega)) (hG v)
  obtain ⟨T, -⟩ := DAryTreeEmbedding.exists_heightOneOfDegree G d v hv
  exact exists_initial_embedded_fan_component_state_of_embedding T

/-- **Bollobás fan from min-degree, case `s ≥ 3`.**  Given a graph with
min-degree `≥ fanThreshold d s`, an initial embedded tree of height
`s - 1`, and `s ≥ 3`, construct a `BollobasFan G d s` from the
score-maximality consequence packaged in `BranchLeafAttachments`.

Mirrors `bollobas_fan_of_minDeg_s_two` at higher heights. -/
lemma bollobas_fan_of_minDeg_s_ge_three
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d h : ℕ) (hd : 2 ≤ d)
    (hG : ∀ v : V, fanThreshold d (h + 2) ≤ G.degree v)
    (T : DAryTreeEmbedding G d (h + 1)) :
    Nonempty (BollobasFan G d (h + 2)) := by
  obtain ⟨C, hmax⟩ := exists_maximal_embedded_fan_component_state G d (h + 2)
    (exists_initial_embedded_fan_component_state_of_embedding (by simpa using T))
  obtain ⟨A⟩ := EmbeddedFanComponentState.exists_branchLeafAttachments_of_maximal hd C hmax hG
  exact A.toBollobasFan hd

/-- Direct `FanComponentAttachments` extraction for the maximal s = 2 case.

This is the s = 2 analogue of `maximal_fan_component_state_attachments`, but
uses the maximality consequence
(`heightOne_child_neighbors_on_spine_off_root_card_ge_of_maximal`) directly
instead of going through the closure / absorption obligation. -/
lemma EmbeddedFanComponentState.maximal_heightOne_fan_component_attachments_of_fanThreshold
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (C : EmbeddedFanComponentState G d 2)
    (hd : 2 ≤ d)
    (hmax : C.IsMaximal)
    (hG : ∀ v : V, fanThreshold d 2 ≤ G.degree v) :
    Nonempty (FanComponentAttachments (C.toFanComponentState hd (by omega))) := by
  classical
  refine ⟨{
    attach := fun i =>
      Classical.choose (C.exists_tip_attachment_of_maximal_heightOne_of_fanThreshold
        hd hmax hG i)
    attach_mem_spine := ?_
    attach_ne_root := ?_
    tip_adj_attach := ?_
  }⟩
  · intro i
    exact (Classical.choose_spec
      (C.exists_tip_attachment_of_maximal_heightOne_of_fanThreshold hd hmax hG i)).1
  · intro i
    exact (Classical.choose_spec
      (C.exists_tip_attachment_of_maximal_heightOne_of_fanThreshold hd hmax hG i)).2.1
  · intro i
    -- `C.star.tip i = C.tree.vertex (branchLeaf 1 i)` for s = 2.
    have hspec := (Classical.choose_spec
      (C.exists_tip_attachment_of_maximal_heightOne_of_fanThreshold hd hmax hG i)).2.2
    exact hspec

/-- Extract fan components from a score-maximal `EmbeddedFanComponentState`
in the `s = 2` case, using the maximality consequence directly. -/
lemma embedded_fan_component_state_components_of_maximal_heightOne {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (C : EmbeddedFanComponentState G d 2)
    (hd : 2 ≤ d)
    (hmax : C.IsMaximal)
    (hG : ∀ v : V, fanThreshold d 2 ≤ G.degree v) :
    ∃ (u v : V) (P : G.Walk u v),
      P.IsPath ∧
      ∃ (S : DisjointPathStar G d 1),
        (∀ i, ∀ w ∈ (S.path i).support, w ∉ P.support) ∧
        (∀ i : Fin d, ∃ e ∈ P.support, G.Adj (S.tip i) e) := by
  obtain ⟨A⟩ := C.maximal_heightOne_fan_component_attachments_of_fanThreshold
    hd hmax hG
  exact fan_component_attachments_to_components hd
    (C.toFanComponentState hd (by omega)) A

/-- **Bollobás fan from min-degree, case `s = 2`.**  With minimum degree
`≥ fanThreshold d 2` and `d ≥ 2`, a `BollobasFan G d 2` exists in `G`.

The construction picks a score-maximal `EmbeddedFanComponentState G d 2`
and uses the maximality consequence
(`heightOne_child_neighbors_on_spine_off_root_card_ge_of_maximal`) to
obtain a non-root spine attachment for each first-level child. -/
lemma bollobas_fan_of_minDeg_s_two
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : d ≥ 2)
    (hG : ∀ v : V, fanThreshold d 2 ≤ G.degree v) :
    Nonempty (BollobasFan G d 2) := by
  obtain ⟨C, hmax⟩ :=
    exists_maximal_embedded_fan_component_state G d 2
      (exists_initial_embedded_fan_component_state_height_one G d hd hG)
  obtain ⟨u, v, P, hP, S, hS_disj, hS_conn⟩ :=
    embedded_fan_component_state_components_of_maximal_heightOne
      C hd hmax hG
  exact fan_from_components hd (by omega) P hP S hS_disj hS_conn

/-
Pigeonhole step on the spine positions of `k + 1` attachments.
-/
theorem exists_congruent_attachment_pair
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {k s : ℕ}
    (F : BollobasFan G (k + 1) s)
    (hk : k ≥ 1) :
    ∃ i j : Fin (k + 1), i ≠ j ∧
      ((F.attachmentPos i : ℕ) : ZMod k) = ((F.attachmentPos j : ℕ) : ZMod k) := by
  by_contra h
  -- Consider the set of attachments, which has cardinality $k + 1$.
  set attachments : Finset (ZMod k) := Finset.image (fun i : Fin (k + 1) => (F.attachmentPos i : ZMod k)) Finset.univ
  rcases k with (_ | _ | k) <;> simp_all
  · simp_all [ZMod, Fin.eq_zero]
  · exact absurd (Finset.card_le_univ attachments) (by rw [Finset.card_image_of_injective _ fun i j hij => Classical.not_not.1 fun hi => h i j hi hij] ; simp)

/-! ### Cycle-construction helpers -/

/-
Two paths from `u` to `v` (with `u ≠ v`) whose supports intersect only in
    `{u, v}` yield a cycle of length equal to the sum of their lengths.
-/
lemma cycle_of_two_disjoint_paths {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (p : G.Walk u v) (q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (h_disj : ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v)
    (hlen : 3 ≤ p.length + q.length) :
    HasCycleOfLength G (p.length + q.length) := by
  use u, p.append q.reverse
  constructor
  · constructor
    · constructor
      · simp_all [SimpleGraph.Walk.isTrail_def]
        have h_edges_disjoint : ∀ e ∈ p.edges, e ∈ q.edges → False := by
          intro e he_p he_q
          have h_edge_eq : e = s(u, v) := by
            have h_edge_eq : ∀ e ∈ p.edges, e ∈ q.edges → e = s(u, v) := by
              intro e he_p he_q
              have h_endpoints : ∀ w ∈ e, w = u ∨ w = v := by
                intro w hw
                have h_w_in_p : w ∈ p.support := by
                  exact p.mem_support_of_mem_edges he_p hw
                have h_w_in_q : w ∈ q.support := by
                  exact q.mem_support_of_mem_edges he_q hw
                exact h_disj w h_w_in_p h_w_in_q
              rcases e with ⟨w₁, w₂⟩ ; simp_all
              cases h_endpoints.1 <;> cases h_endpoints.2 <;> simp_all [Sym2.eq_swap]
              · exact absurd he_p (by simpa using p.edges_subset_edgeSet he_p)
              · exact absurd he_p (by simpa using p.edges_subset_edgeSet he_p)
            exact h_edge_eq e he_p he_q
          have h_edge_eq_p : p.length = 1 := by
            rcases p with (_ | ⟨_, _, p⟩ ) <;> simp_all
            rcases he_p with (rfl | ⟨rfl, rfl⟩ | he_p) <;> simp_all [SimpleGraph.Walk.isPath_def]
            have := SimpleGraph.Walk.fst_mem_support_of_mem_edges ‹_› he_p; aesop
          have h_edge_eq_q : q.length = 1 := by
            rcases q with (_ | ⟨_, _, q⟩ ) <;> simp_all
            rcases he_q with (rfl | ⟨rfl, rfl⟩ | he_q) <;> simp_all [SimpleGraph.Walk.isPath_def]
            rename_i k hk₁ hk₂
            have := SimpleGraph.Walk.fst_mem_support_of_mem_edges k he_q; simp_all
          linarith
        rw [List.nodup_append]
        simp +zetaDelta at *
        exact ⟨hp.edges_nodup, hq.edges_nodup, fun a ha b hb hab => h_edges_disjoint a ha <| hab ▸ hb⟩
      · cases p <;> cases q <;> aesop
    · simp_all [SimpleGraph.Walk.support_append, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact hp.support_nodup.tail
      · exact hq.support_nodup.sublist (List.dropLast_sublist _)
      · intro a ha b hb hab; have := h_disj a; simp_all
        cases h_disj b (by simpa using List.mem_of_mem_tail ha) (by simpa using List.mem_of_mem_dropLast hb) <;> simp_all
        · cases p <;> cases q <;> simp_all [SimpleGraph.Walk.support]
        · have := List.mem_iff_get.1 hb; obtain ⟨i, hi⟩ := this; simp_all
          have := List.nodup_iff_injective_get.mp hq.support_nodup; have := @this ⟨i, by
            exact lt_of_lt_of_le i.2 (by simp)⟩ ⟨q.support.length - 1, by
            exact Nat.pred_lt (ne_bot_of_gt (List.length_pos_iff.mpr (by aesop_cat)))⟩ ; simp_all
          exact absurd this (ne_of_lt (Nat.lt_of_lt_of_le i.2 (by simp)))
  · simp [SimpleGraph.Walk.length_append]

/-
In a `BollobasFan`, the only vertices shared between two distinct branches
    are `root` and (when attachments coincide) the common attachment vertex.
-/
lemma BollobasFan.branch_support_inter_subset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d) (hij : i ≠ j)
    (w : V) (hwi : w ∈ (F.branch i).support) (hwj : w ∈ (F.branch j).support) :
    w = F.root ∨ (w = F.attachment i ∧ w = F.attachment j) := by
  by_cases hw : w ∈ (F.spine.support)
  · have h_attach_i : w = F.attachment i := by
      have := F.branch_spine_inter i
      replace this := congr_arg List.toFinset this; rw [Finset.ext_iff] at this; specialize this w; aesop
    have h_attach_j : w = F.attachment j := by
      have := F.branch_spine_inter j
      replace this := congr_arg List.toFinset this; rw [Finset.ext_iff] at this; specialize this w; aesop
    aesop
  · exact Or.inl (F.pairwise_branch_inter i j hij w hwi hwj |> Or.resolve_right <| by tauto)

/-
In a `BollobasFan` with `s ≥ 1`, the root is different from every
    attachment vertex.
-/
lemma BollobasFan.root_ne_attachment {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i : Fin d) : F.root ≠ F.attachment i := by
  exact fun h => F.root_not_mem_spine (h ▸ F.attachment_mem_spine i)

/-
If two branches in a `BollobasFan` share an attachment vertex, then
    `s ≥ 2`.
-/
lemma BollobasFan.s_ge_two_of_same_attachment {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d) (hij : i ≠ j)
    (hatt : F.attachment i = F.attachment j) : s ≥ 2 := by
  contrapose! hij
  interval_cases s
  · cases F
    grind +suggestions
  · cases' F with root spineStart spineEnd spine spine_isPath root_not_mem_spine attachment attachment_mem_spine branch branch_isPath branch_length branch_spine_inter pairwise_branch_inter branch_support_ne
    have h_contradiction : ∀ i : Fin d, (branch i).support = [root, attachment i] := by
      intro i; specialize branch_length i; specialize branch_isPath i; rcases h : branch i with (_ | ⟨_, _, _, _, _⟩ ) <;> simp_all
    grind

/-
In a `BollobasFan`, if `attachment i ≠ attachment j` then the only
    vertex shared by the two branches is `root`.
-/
lemma BollobasFan.branch_inter_eq_root {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d) (hij : i ≠ j)
    (hatt : F.attachment i ≠ F.attachment j)
    (w : V) (hwi : w ∈ (F.branch i).support) (hwj : w ∈ (F.branch j).support) :
    w = F.root := by
  have := BollobasFan.branch_support_inter_subset F i j hij w hwi hwj; cases this <;> aesop

/-
**Case 1:** Same attachment. Two branches from `root` to the same attachment
    vertex, with `s ≥ 2`, give a cycle of length `2 * s`.
-/
lemma cycle_from_same_attachment {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {d s : ℕ}
    (F : BollobasFan G d s)
    (i j : Fin d) (hij : i ≠ j)
    (hatt : F.attachment i = F.attachment j) :
    HasCycleOfLength G (2 * s) := by
  have h_len : 4 ≤ s + s := by
    linarith [F.s_ge_two_of_same_attachment i j hij hatt]
  convert cycle_of_two_disjoint_paths (F.root_ne_attachment i) (F.branch i) (?_) (F.branch_isPath i) ?_ ?_ using 1
  rotate_left
  exact F.branch j |> fun w => w.copy (by simp) (by simp [hatt])
  · convert F.branch_isPath j
    simp [SimpleGraph.Walk.copy]
  · intro w hw hw'; have := F.branch_support_inter_subset i j hij w hw; aesop
  · simp_all [BollobasFan.branch_length]
    grind

/-
On a path, if vertex `w₂` appears at a position ≥ that of `w₁`, then
    `w₂ ∈ (p.dropUntil w₁).support`.
-/
lemma Walk.IsPath.mem_support_dropUntil_of_takeUntil_le
    {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {u v w₁ w₂ : V} {p : G.Walk u v} (hp : p.IsPath)
    (hw₁ : w₁ ∈ p.support) (hw₂ : w₂ ∈ p.support)
    (hle : (p.takeUntil w₁ hw₁).length ≤ (p.takeUntil w₂ hw₂).length) :
    w₂ ∈ (p.dropUntil w₁ hw₁).support := by
  revert w₁ w₂
  induction p <;> simp [ *, SimpleGraph.Walk.takeUntil]
  · aesop
  · intro w₁ w₂ hw₁ hw₂ hle; split_ifs at hle <;> simp_all [SimpleGraph.Walk.dropUntil]
    · aesop
    · aesop
    · aesop
    · grind

/-
On a path, the segment from `w₁` to `w₂` via `dropUntil`/`takeUntil` has
    length equal to the difference of their positions.
-/
lemma Walk.IsPath.length_segment
    {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {u v w₁ w₂ : V} {p : G.Walk u v} (hp : p.IsPath)
    (hw₁ : w₁ ∈ p.support) (hw₂ : w₂ ∈ p.support)
    (hle : (p.takeUntil w₁ hw₁).length ≤ (p.takeUntil w₂ hw₂).length)
    (hmem : w₂ ∈ (p.dropUntil w₁ hw₁).support) :
    ((p.dropUntil w₁ hw₁).takeUntil w₂ hmem).length =
      (p.takeUntil w₂ hw₂).length - (p.takeUntil w₁ hw₁).length := by
  have h_congruent_pairs : ∀ (u v w₁ w₂ : V) (p : G.Walk u v) (_hp : p.IsPath)
      (hw₁ : w₁ ∈ p.support) (hw₂ : w₂ ∈ p.support)
      (_hle : (p.takeUntil w₁ hw₁).length ≤ (p.takeUntil w₂ hw₂).length)
      (hmem : w₂ ∈ (p.dropUntil w₁ hw₁).support),
      ((p.dropUntil w₁ hw₁).takeUntil w₂ hmem).length =
        (p.takeUntil w₂ hw₂).length - (p.takeUntil w₁ hw₁).length := by
    intros u v w₁ w₂ p hp hw₁ hw₂ hle hmem
    induction' p with u v p ih generalizing w₁ w₂
    · grind +suggestions
    · cases eq_or_ne w₁ v <;> cases eq_or_ne w₂ v <;> simp_all [SimpleGraph.Walk.takeUntil]
      · aesop
      · aesop
      · aesop
      · split_ifs <;> simp_all [SimpleGraph.Walk.dropUntil]
        grind
  exact h_congruent_pairs u v w₁ w₂ p hp hw₁ hw₂ hle hmem

/-
On a path, if two distinct vertices have the same `takeUntil` length,
    they must be equal.
-/
lemma Walk.IsPath.takeUntil_length_injective
    {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {u v w₁ w₂ : V} {p : G.Walk u v} (hp : p.IsPath)
    (hw₁ : w₁ ∈ p.support) (hw₂ : w₂ ∈ p.support)
    (heq : (p.takeUntil w₁ hw₁).length = (p.takeUntil w₂ hw₂).length) :
    w₁ = w₂ := by
  have h_detour : (p.dropUntil w₂ hw₂).support.toFinset ⊇ {w₁, v} := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    convert Walk.IsPath.mem_support_dropUntil_of_takeUntil_le hp hw₂ hw₁ _
    rw [heq]
  grind +suggestions

namespace BollobasFan

/-- The segment of the spine from attachment `i` to attachment `j`, assuming
    the `i`-attachment occurs no later than the `j`-attachment. -/
def spineSegment {V : Type*} [DecidableEq V] {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d)
    (hle : F.attachmentPos i ≤ F.attachmentPos j) :
    G.Walk (F.attachment i) (F.attachment j) :=
  let hmem :=
    Walk.IsPath.mem_support_dropUntil_of_takeUntil_le
      F.spine_isPath (F.attachment_mem_spine i) (F.attachment_mem_spine j) hle
  (F.spine.dropUntil (F.attachment i) (F.attachment_mem_spine i)).takeUntil (F.attachment j) hmem

lemma spineSegment_isPath {V : Type*} [DecidableEq V] {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d)
    (hle : F.attachmentPos i ≤ F.attachmentPos j) :
    (F.spineSegment i j hle).IsPath := by
  unfold spineSegment
  simp only
  apply SimpleGraph.Walk.IsPath.takeUntil
  exact F.spine_isPath.dropUntil _

lemma spineSegment_support_subset_spine {V : Type*} [DecidableEq V] {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d)
    (hle : F.attachmentPos i ≤ F.attachmentPos j) :
    (F.spineSegment i j hle).support ⊆ F.spine.support := by
  intro w hw
  unfold spineSegment at hw
  simp only at hw
  exact SimpleGraph.Walk.support_dropUntil_subset_support _ _ <|
    SimpleGraph.Walk.support_takeUntil_subset_support _ _ hw

lemma spineSegment_length {V : Type*} [DecidableEq V] {G : SimpleGraph V} {d s : ℕ}
    (F : BollobasFan G d s) (i j : Fin d)
    (hle : F.attachmentPos i ≤ F.attachmentPos j) :
    (F.spineSegment i j hle).length = F.attachmentPos j - F.attachmentPos i := by
  let hmem :
      F.attachment j ∈
        (F.spine.dropUntil (F.attachment i) (F.attachment_mem_spine i)).support :=
    Walk.IsPath.mem_support_dropUntil_of_takeUntil_le
      F.spine_isPath (F.attachment_mem_spine i) (F.attachment_mem_spine j) hle
  simpa [spineSegment, attachmentPos, hmem] using
    Walk.IsPath.length_segment F.spine_isPath
      (F.attachment_mem_spine i) (F.attachment_mem_spine j) hle hmem

end BollobasFan

/-
**Case 2:** Different attachment. Two branches from `root` to distinct spine
    vertices, plus the spine segment between them, give a cycle whose length
    equals `2 * s` plus the segment length.
-/
lemma cycle_from_diff_attachment {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {d s : ℕ}
    (F : BollobasFan G d s)
    (i j : Fin d) (hij : i ≠ j)
    (hatt : F.attachment i ≠ F.attachment j)
    (hle : F.attachmentPos i ≤ F.attachmentPos j) :
    HasCycleOfLength G (2 * s + (F.attachmentPos j - F.attachmentPos i)) := by
  let spine_seg := F.spineSegment i j hle
  have h_spine_seg_length : spine_seg.length = F.attachmentPos j - F.attachmentPos i := by
    simpa [spine_seg] using F.spineSegment_length i j hle
  convert cycle_of_two_disjoint_paths (F.root_ne_attachment j) (F.branch i |> SimpleGraph.Walk.append <| spine_seg) (F.branch j) _ _ _ _ using 1
  · simp [two_mul, F.branch_length]
    rw [h_spine_seg_length, add_right_comm]
  · simp [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact F.branch_isPath i |> fun h => h.support_nodup
    · exact (F.spineSegment_isPath i j hle).support_nodup.tail
    · intro a ha b hb hab
      have h_contradiction : a ∈ F.spine.support := by
        exact F.spineSegment_support_subset_spine i j hle (hab.symm ▸ List.mem_of_mem_tail hb)
      have := F.branch_spine_inter i; simp_all
      replace this := congr_arg List.toFinset this; rw [Finset.ext_iff] at this; specialize this b; simp_all
      have h_contradiction : ∀ {u v : V} {p : G.Walk u v}, p.IsPath → ∀ {w : V}, w ∈ p.support.tail → w ≠ u := by
        intros u v p hp w hw; induction p <;> simp_all [SimpleGraph.Walk.cons_isPath_iff]
        grind
      exact h_contradiction (F.spineSegment_isPath i j hle) hb rfl
  · exact F.branch_isPath j
  · intro w hw hw'
    by_cases hw'' : w ∈ (F.branch i).support <;> simp_all [SimpleGraph.Walk.support_append]
    · have := F.branch_inter_eq_root i j hij hatt w hw'' hw'; aesop
    · have hw_spine : w ∈ F.spine.support := by
        exact F.spineSegment_support_subset_spine i j hle (List.mem_of_mem_tail hw)
      have hw_spine : w ∈ (F.branch j).support → w = F.root ∨ w = F.attachment j := by
        intro hw''; have := F.branch_spine_inter j; simp_all
        replace this := congr_arg List.toFinset this; rw [Finset.ext_iff] at this; specialize this w; aesop
      exact hw_spine hw'
  · have hs_pos : 1 ≤ s := by
      by_contra hs_pos
      have hs_zero : s = 0 := by omega
      have hlen_zero : (F.branch i).length = 0 := by simpa [hs_zero] using F.branch_length i
      exact (F.root_ne_attachment i) (SimpleGraph.Walk.eq_of_length_eq_zero hlen_zero)
    have hpos_ne : F.attachmentPos i ≠ F.attachmentPos j := by
      intro hEq
      exact hatt <|
        Walk.IsPath.takeUntil_length_injective
          F.spine_isPath (F.attachment_mem_spine i) (F.attachment_mem_spine j) hEq
    have hseg_pos : 1 ≤ F.attachmentPos j - F.attachmentPos i := by
      have hlt : F.attachmentPos i < F.attachmentPos j := lt_of_le_of_ne hle hpos_ne
      omega
    simp [F.branch_length, h_spine_seg_length]
    omega

/-- Fan configuration gives a cycle of residue `2 * s` whose length is at
least `2 * s`.  This is the fan-only part of the length-lower-bound result,
separated from the theorem that constructs the fan. -/
theorem BollobasFan.exists_cycle_mod_with_length_lb
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (k s : ℕ) (hk : k ≥ 2)
    (F : BollobasFan G (k + 1) s) :
    ∃ n, n ≥ 2 * s ∧ HasCycleOfLength G n ∧
      (n : ZMod k) = (2 * s : ZMod k) := by
  obtain ⟨i, j, hij, hpos⟩ :
      ∃ i j : Fin (k + 1), i ≠ j ∧
        ((F.attachmentPos i : ℕ) : ZMod k) =
          ((F.attachmentPos j : ℕ) : ZMod k) := by
    apply exists_congruent_attachment_pair F (by omega)
  by_cases hatti : F.attachment i = F.attachment j
  · -- Same attachment: the two branches glue into a cycle of length exactly 2s.
    exact ⟨2 * s, le_rfl, cycle_from_same_attachment F i j hij hatti, by push_cast; ring⟩
  · -- Different attachments: get a cycle of length 2s + (pos j - pos i).
    wlog hle : F.attachmentPos i ≤ F.attachmentPos j generalizing i j
    · exact this j i hij.symm hpos.symm (Ne.symm hatti) (le_of_not_ge hle)
    refine ⟨2 * s + (F.attachmentPos j - F.attachmentPos i), ?_, ?_, ?_⟩ <;>
      simp_all
    convert cycle_from_diff_attachment F i j hij hatti hle using 1

/-- Length-lower-bound fan-cycle theorem for height one.  This uses the
complete height-one fan construction, so it does not need any replacement
hypothesis. -/
theorem bollobas_fan_cycle_of_minDeg_s_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : k ≥ 2)
    (hG : ∀ v : V, fanThreshold (k + 1) 1 ≤ G.degree v) :
    ∃ n, n ≥ 2 * 1 ∧ HasCycleOfLength G n ∧
      (n : ZMod k) = (2 * 1 : ZMod k) := by
  let F : BollobasFan G (k + 1) 1 :=
    Classical.choice <|
      bollobas_fan_of_minDeg_s_one G (k + 1) (by omega)
        (fun v => le_trans (d_le_fanThreshold (k + 1) 1 (by omega) (by omega)) (hG v))
  simpa using BollobasFan.exists_cycle_mod_with_length_lb k 1 hk F

/-- **Bollobás fan-cycle theorem.**  In a finite graph with minimum
degree `≥ fanThreshold (k+1) s`, for any `k ≥ 2` and `s ≥ 1`, there is a
cycle of length `n ≥ 2s` with `n ≡ 2s (mod k)`.

Splits on `s`: the `s ≥ 3` case uses `bollobas_fan_of_minDeg_s_ge_three`,
`s = 2` uses `bollobas_fan_of_minDeg_s_two`, and `s = 1` uses
`bollobas_fan_cycle_of_minDeg_s_one`. -/
theorem bollobas_fan_cycle_of_minDeg
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k s : ℕ) (hk : k ≥ 2) (hs : s ≥ 1)
    (hG : ∀ v : V, fanThreshold (k + 1) s ≤ G.degree v) :
    ∃ n, n ≥ 2 * s ∧ HasCycleOfLength G n ∧
      (n : ZMod k) = (2 * s : ZMod k) := by
  by_cases hs3 : 3 ≤ s
  · -- s ≥ 3: reparameterise s = h + 2, build an initial tree of height
    -- h + 1, then apply the s ≥ 3 fan construction.
    obtain ⟨h, rfl⟩ : ∃ h, s = h + 2 := ⟨s - 2, by omega⟩
    have hdeg_ge : ∀ v : V,
        (∅ : Finset V).card + fanTreeThreshold (k + 1) (h + 1 + 1) ≤ G.degree v := by
      intro v
      simp only [Finset.card_empty, Nat.zero_add]
      exact (fanTreeThreshold_le_fanThreshold (k + 1) (h + 2)).trans (hG v)
    obtain ⟨T, _, _⟩ :=
      DAryTreeEmbedding.exists_DAryTreeEmbedding_avoiding_of_minDeg
        G (by omega : (k + 1) ≥ 2) (h + 1) (Classical.arbitrary V) ∅
        (Finset.notMem_empty _) hdeg_ge
    let F : BollobasFan G (k + 1) (h + 2) :=
      Classical.choice <|
        bollobas_fan_of_minDeg_s_ge_three G (k + 1) h (by omega) hG T
    exact BollobasFan.exists_cycle_mod_with_length_lb k (h + 2) hk F
  · by_cases hs2 : 2 ≤ s
    · have hs_eq : s = 2 := by omega
      subst s
      let F : BollobasFan G (k + 1) 2 :=
        Classical.choice <|
          bollobas_fan_of_minDeg_s_two
            G (k + 1) (by omega) hG
      exact BollobasFan.exists_cycle_mod_with_length_lb k 2 hk F
    · have hs_eq : s = 1 := by omega
      subst s
      simpa using bollobas_fan_cycle_of_minDeg_s_one G k hk hG

/-! ## §7  Theorem 2 — Odd-modulus theorem -/

/-- The fan threshold is bounded by `bollobasConst k` for `1 ≤ s ≤ k`,
    `k ≥ 2` — the slack that lets a single `c` discharge every residue. -/
lemma fanThreshold_le_bollobasConst (k s : ℕ) (hk : k ≥ 2) (_hs1 : 1 ≤ s) (hs2 : s ≤ k) :
    fanThreshold (k + 1) s ≤ bollobasConst k := by
  unfold fanThreshold bollobasConst
  have h1 : fanTreeThreshold (k + 1) s ≤ ((k + 1) ^ k - 1) / k := by
    exact Nat.div_le_div_right
      (Nat.sub_le_sub_right (pow_le_pow_right₀ (by omega) hs2) _)
  omega

/-- **Bollobás (1977), Theorem 2** — *Cycles modulo k*.

If `G` is a finite simple graph with minimum degree at least
`bollobasConst k` and `k ≥ 3` is odd, then `G` contains a cycle of every
length modulo `k`. -/
theorem bollobas_cycles_mod_odd
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk_odd : Odd k) (hk_ge : k ≥ 3)
    (hdeg : ∀ v : V, bollobasConst k ≤ G.degree v)
    (r : ZMod k) :
    HasCycleOfLengthMod G k r := by
  obtain ⟨s, hs1, hsk, hres⟩ := double_residues_surjective hk_odd (by omega) r
  have hthresh : ∀ v : V, fanThreshold (k + 1) s ≤ G.degree v := by
    intro v
    exact le_trans (fanThreshold_le_bollobasConst k s (by omega) hs1 hsk) (hdeg v)
  -- Apply the fan-cycle theorem.
  obtain ⟨n, _, hcycle, hmod⟩ :=
    bollobas_fan_cycle_of_minDeg G k s (by omega) hs1 hthresh
  refine ⟨n, hcycle, ?_⟩
  rw [hmod, hres]

/-! ## §8  Cycle-length helpers -/

/-- If L ≡ a (mod d) and L ≥ a, then L = a + m·d for some m ∈ ℕ. -/
lemma exists_ap_index_of_mod (a d L : ℕ) (hmod : L ≡ a [MOD d]) (hge : L ≥ a) :
    ∃ m : ℕ, L = a + m * d := by
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hge).mp hmod.symm
  exact ⟨m, by rw [mul_comm]; omega⟩

/-! ## §9  Corollary — Erdős Problem 71 -/

/-
A nonempty graph with min degree ≥ m ≥ 2 has a cycle of length ≥ m + 1.
    (Standard: take longest path; first vertex has ≥ m neighbours on it
    the farthest gives a cycle of length ≥ m + 1.)
-/
theorem exists_long_cycle
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : m ≥ 2)
    (hdeg : ∀ v : V, m ≤ G.degree v) :
    ∃ n : ℕ, n ≥ m + 1 ∧ HasCycleOfLength G n := by
  -- Standard: take longest path, first vertex has ≥ m neighbors on it.
  -- The farthest gives a cycle of length ≥ m + 1.
  obtain ⟨u, v, p, hp⟩ := exists_maximal_path G
  obtain ⟨f, hf_inj, hf_mem, hf_ne, hf_adj⟩ : ∃ f : Fin m → V, Function.Injective f ∧ (∀ i, f i ∈ p.support) ∧ (∀ i, f i ≠ u) ∧ (∀ i, G.Adj u (f i)) := by
    apply maximal_path_endpoint_neighbors_on_path G p hp.left hp.right.left m (hdeg u)
  obtain ⟨i, hi⟩ : ∃ i : Fin m, ∀ j : Fin m, (p.takeUntil (f j) (hf_mem j)).length ≤ (p.takeUntil (f i) (hf_mem i)).length := by
    simpa using Finset.exists_max_image Finset.univ (fun i => (p.takeUntil (f i) (hf_mem i)).length) ⟨⟨0, by linarith⟩, Finset.mem_univ _⟩
  have h_cycle_length : (p.takeUntil (f i) (hf_mem i)).length ≥ m := by
    have h_cycle_length : Finset.card (Finset.image (fun j => (p.takeUntil (f j) (hf_mem j)).length) Finset.univ) ≥ m := by
      rw [Finset.card_image_of_injective _ fun i j hij => _, Finset.card_fin]
      intro i j hij; have := hp.1; exact hf_inj (by have := Walk.IsPath.takeUntil_length_injective this (hf_mem i) (hf_mem j) hij; aesop)
    exact h_cycle_length.trans (Finset.card_le_card (Finset.image_subset_iff.mpr fun j _ => Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
      cases p <;> simp_all [SimpleGraph.Walk.takeUntil]
      · exact absurd (hp.2 _ (hf_adj i)) (hf_ne i)
      · split_ifs <;> simp_all
        exact False.elim (hf_ne j rfl))), hi j⟩ )) |> le_trans <| by simp
  refine ⟨1 + (p.takeUntil (f i) (hf_mem i)).length, by linarith, ?_⟩
  convert cycle_of_two_disjoint_paths
    (show u ≠ f i from Ne.symm (hf_ne i))
    (SimpleGraph.Walk.cons (hf_adj i) SimpleGraph.Walk.nil)
    (p.takeUntil (f i) (hf_mem i)) _ _ _ _ using 1
    <;> simp_all [SimpleGraph.Walk.cons_isPath_iff]
  · exact Ne.symm (hf_ne i)
  · exact hp.1.takeUntil _
  · linarith

/-- If every vertex `v ∈ S` has at least `c` adjacent vertices within `S`,
then the induced subgraph on `S` has minimum degree `≥ c`. -/
private lemma minDeg_induce_of_filter_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {c : ℕ}
    (hS : ∀ v ∈ S, c ≤ (S.filter (G.Adj v)).card) :
    ∀ v : { x : V // x ∈ S }, c ≤ (G.induce (S : Set V)).degree v := by
  simp_all [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
  intro v hv
  convert hS v hv using 1
  rw [← Finset.card_image_of_injective _ Subtype.coe_injective]
  congr
  ext
  aesop

/-! ### Erdős Problem 71 — main result -/

/-- **Erdős Problem 71**, edge-density form.

For every infinite arithmetic progression `P` containing an even number,
there is a constant `c = c(P)` such that every finite simple graph `G`
with `c · |V(G)| ≤ |E(G)|` contains a cycle whose length lies in `P`.

This is the workhorse: it keeps all the bookkeeping in `ℕ`. The headline
`erdos_71` below states the same result with the average-degree hypothesis
`c ≤ avgDegree G`.

The proof splits on the parity of `P.d`:

* **`d` odd, `d = 1`**: every long enough cycle has length in `P`; we use
  `exists_long_cycle`.
* **`d` odd, `d ≥ 3`**: pick `s₀ ∈ [1, d]` with `2·s₀ ≡ a (mod d)` (which
  exists because doubling permutes residues mod odd `d`) and apply
  `bollobas_fan_cycle_of_minDeg` with `s = s₀ + d·a` to ensure the produced
  cycle length is both `≡ a (mod d)` and `≥ a`.
* **`d` even**: the "contains an even number" hypothesis forces `a` even;
  write `a = 2s` and apply `bollobas_fan_cycle_of_minDeg`.
-/
theorem erdos_71_of_edge_density (P : InfiniteAP) (heven : P.ContainsEven) :
    ∃ c : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      c * Fintype.card V ≤ G.edgeFinset.card →
      ∃ n ∈ P, HasCycleOfLength G n := by
  obtain ⟨a, d, ha, hd⟩ := P
  -- After destructuring, `n ∈ P` reduces to `∃ m, n = a + m * d`.
  simp only [InfiniteAP.mem_def] at *
  -- `heven` is now `∃ n, (∃ m, n = a + m * d) ∧ Even n`.
  obtain ⟨_, ⟨m, rfl⟩, hm_even⟩ := heven
  have heven : ∃ m : ℕ, Even (a + m * d) := ⟨m, hm_even⟩
  by_cases hd_odd : Odd d
  · by_cases hd_one : d = 1
    · -- d = 1: every long enough cycle has length ≥ a, so a cycle of length
      -- ≥ a + 3 exists in any induced subgraph of min-degree ≥ a + 3.
      subst d
      use a + 3
      intro V _ _ hV G _ hG
      obtain ⟨S, hS₁, hS₂⟩ := exists_induced_subgraph_minDeg G (a + 3) hG
      let : Nonempty ↑(S : Set V) := ⟨hS₁.choose, hS₁.choose_spec⟩
      have h_min_deg : ∀ v : { x : V // x ∈ S }, a + 2 ≤ (G.induce (S : Set V)).degree v :=
        fun v => Nat.le_of_succ_le (minDeg_induce_of_filter_card_le G hS₂ v)
      obtain ⟨n, hn_ge, hcyc⟩ := exists_long_cycle (G.induce S) (a + 2) (by linarith) h_min_deg
      have h_cycle : HasCycleOfLength G n := HasCycleOfLength_of_induce G S n hcyc
      have han : a ≤ n := by linarith
      exact ⟨n, ⟨n - a, by rw [Nat.mul_one, add_tsub_cancel_of_le han]⟩, h_cycle⟩
    · -- d ≥ 3 odd.  Pick s₀ ∈ [1, d] with 2*s₀ ≡ a (mod d), then set s = s₀ + d*a
      -- so that 2*s = 2*s₀ + 2*d*a ≥ a ensures the cycle length is ≥ a.
      have hd_ge : d ≥ 3 := by
        rcases hd_odd with ⟨t, ht⟩
        subst d
        cases t
        · simp_all
        · omega
      obtain ⟨s₀, hs₀_pos, hs₀_le, hs₀_eq⟩ :
          ∃ s₀ : ℕ, 1 ≤ s₀ ∧ s₀ ≤ d ∧ (2 * s₀ : ZMod d) = (a : ZMod d) :=
        double_residues_surjective hd_odd (by omega) (a : ZMod d)
      set s := s₀ + d * a with hs_def
      use fanThreshold (d + 1) s
      intro V _ _ hV G _ hG
      obtain ⟨S, hS⟩ :
          ∃ S : Finset V, S.Nonempty ∧
            ∀ v ∈ S, fanThreshold (d + 1) s ≤ (S.filter (G.Adj v)).card :=
        exists_induced_subgraph_minDeg G (fanThreshold (d + 1) s) hG
      let : Nonempty ↑(S : Set V) :=
        ⟨⟨hS.1.choose, by simpa using hS.1.choose_spec⟩⟩
      have h_induced_min_deg := minDeg_induce_of_filter_card_le G hS.2
      have hk : d ≥ 2 := by omega
      have hs_pos : s ≥ 1 := by simp [hs_def]; omega
      obtain ⟨n, hn_ge, hcyc, hmod⟩ :=
        bollobas_fan_cycle_of_minDeg
          (G.induce S) d s hk hs_pos h_induced_min_deg
      have h_cycle : HasCycleOfLength G n := HasCycleOfLength_of_induce G S n hcyc
      have hna : n ≥ a := by
        have : n ≥ 2 * s := hn_ge
        have hs_ge : s ≥ a := by simp [hs_def]; nlinarith
        omega
      have hmod_a : (n : ZMod d) = (a : ZMod d) := by
        rw [hmod]
        -- (2 * s : ZMod d) = (a : ZMod d) since 2 * s = 2 * (s₀ + d*a) = 2*s₀ + 2*d*a
        -- and (d : ZMod d) = 0, so 2*s ≡ 2*s₀ ≡ a (mod d).
        have hsz : (s : ZMod d) = (s₀ : ZMod d) := by
          show ((s₀ + d * a : ℕ) : ZMod d) = (s₀ : ZMod d)
          push_cast
          have : (d : ZMod d) = 0 := ZMod.natCast_self d
          rw [this]; ring
        rw [hsz]
        exact_mod_cast hs₀_eq
      obtain ⟨m, hm⟩ : ∃ m : ℕ, n = a + m * d := by
        have h_mod : n ≡ a [MOD d] := (ZMod.natCast_eq_natCast_iff n a d).mp hmod_a
        exact exists_ap_index_of_mod a d n h_mod hna
      exact ⟨n, ⟨m, hm⟩, h_cycle⟩
  · -- d even: a is even (heven says ∃m, Even (a + m*d); for d even, a + m*d ≡ a (mod 2)).
    have hd_even : Even d := Nat.not_odd_iff_even.mp hd_odd
    obtain ⟨m₀, hm₀⟩ := heven
    have ha_even : Even a := by
      rcases hd_even with ⟨k, hk⟩
      rcases hm₀ with ⟨n, hn⟩
      -- a + m₀ * d = n + n, d = k + k, so a + 2*m₀*k = 2*n, so a = 2*(n - m₀*k).
      refine ⟨n - m₀ * k, ?_⟩
      have h1 : m₀ * d = m₀ * k + m₀ * k := by rw [hk]; ring
      omega
    obtain ⟨s, hs⟩ : ∃ s, a = 2 * s := by
      rcases ha_even with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    use fanThreshold (d + 1) s + 1
    intro V _ _ hV G _ h
    obtain ⟨S, hS⟩ :
        ∃ S : Finset V, S.Nonempty ∧
          ∀ v ∈ S, fanThreshold (d + 1) s ≤ (S.filter (G.Adj v)).card := by
      have h' : fanThreshold (d + 1) s * Fintype.card V ≤ G.edgeFinset.card := by linarith
      exact exists_induced_subgraph_minDeg G (fanThreshold (d + 1) s) h'
    have hk : d ≥ 2 := Nat.le_of_dvd hd (even_iff_two_dvd.mp hd_even)
    have hs_pos : s ≥ 1 := by nlinarith
    have h_induced_min_deg := minDeg_induce_of_filter_card_le G hS.2
    let : Nonempty (↑(S : Set V)) := ⟨hS.1.choose, by simpa using hS.1.choose_spec⟩
    -- Apply the fan-cycle theorem.
    obtain ⟨n, hn⟩ :
        ∃ n, n ≥ 2 * s ∧ HasCycleOfLength (G.induce S) n ∧
          (n : ZMod d) = (2 * s : ZMod d) :=
      bollobas_fan_cycle_of_minDeg
        (G.induce S) d s hk hs_pos h_induced_min_deg
    have h_cycle : HasCycleOfLength G n := by
      apply HasCycleOfLength_of_induce G S n hn.2.1
    obtain ⟨m, hm⟩ :=
      exists_ap_index_of_mod (2 * s) d n
        (by simpa [← ZMod.natCast_eq_natCast_iff] using hn.2.2) (by linarith)
    have : n = a + m * d := by omega
    exact ⟨n, ⟨m, this⟩, h_cycle⟩

end Erdos71

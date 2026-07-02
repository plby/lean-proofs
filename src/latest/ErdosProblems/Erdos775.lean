/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 775.
https://www.erdosproblems.com/forum/thread/775

Informal authors:
- Jun Gao

Formal authors:
- Aristotle
- Lorenzo Luccioli

URLs:
- https://www.erdosproblems.com/forum/thread/775#post-5619
- https://gist.githubusercontent.com/LorenzoLuccioli/dc7dac92dff47aac05b50f2562dbe8c1/raw/2c53e497b3d685bc4883c0a2394b5f10ecb367a0/Erdos775.lean
-/
import Mathlib

namespace Erdos775

set_option linter.style.setOption false
set_option linter.flexible false

/-!
# On Cliques in Hypergraphs

Formalization of the main results from "On cliques in hypergraphs" by Jun Gao.

## Main results

* `main_theorem` — **Theorem 1.1**: For any k ≥ 3 and C ≥ 0, there exists N such that
  every k-uniform hypergraph on n ≥ N vertices has at most n − C distinct clique sizes.
* `erdos_problem_775` — The k = 3 specialization, answering Erdős Problem #775.

## Supporting results

* `helly_complete` — **Fact 2.3**: Helly-type property for complete subgraphs.
* `layered_tree_bounded` — **Lemma 2.2**: (k,C)-layered trees have bounded size.
* `tree_from_many_clique_sizes` — Section 3 tree construction.

## Status

All theorems are fully proved (0 placeholder proofs). Only standard logical dependencies are used:
`propext`, `Classical.choice`, `Quot.sound`.
-/

open Finset

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 12800000
-- Several generated hypergraph clique-size arguments time out at the default heartbeat limit.

/-! ========== Defs.lean ========== -/

/-!
# On Cliques in Hypergraphs — Definitions

Formalization of "On cliques in hypergraphs" by Jun Gao.

## Main definitions

* `KUniformHypergraph` — a k-uniform hypergraph on a type α
* `KUniformHypergraph.IsComplete` — a set forms a complete subgraph
* `KUniformHypergraph.IsClique` — a maximal complete subgraph
* `OrderedRootedTree` — a rooted tree on {0, ..., t} given by a parent function
* `IsKCLayeredTree` — the (k,C)-layered tree property (Definition 2.1)
-/

open Finset

noncomputable section

/-! ## K-Uniform Hypergraphs -/

/-- A k-uniform hypergraph on type α: a collection of edges, each of cardinality k. -/
structure KUniformHypergraph (α : Type*) (k : ℕ) where
  edges : Set (Finset α)
  uniform : ∀ e ∈ edges, e.card = k

namespace KUniformHypergraph

variable {α : Type*} [DecidableEq α] {k : ℕ}

/-- A set S forms a complete subgraph if every k-element subset of S is an edge. -/
def IsComplete (H : KUniformHypergraph α k) (S : Finset α) : Prop :=
  ∀ e : Finset α, e ⊆ S → e.card = k → e ∈ H.edges

/-- A clique is a maximal complete subgraph: S is complete and not properly contained
    in any other complete set. -/
def IsClique (H : KUniformHypergraph α k) (S : Finset α) : Prop :=
  H.IsComplete S ∧ ∀ T : Finset α, S ⊂ T → ¬H.IsComplete T

set_option linter.unusedSectionVars false in
omit [DecidableEq α] in
/-- Subsets of complete sets are complete. -/
lemma IsComplete.mono {H : KUniformHypergraph α k} {S T : Finset α}
    (hST : S ⊆ T) (hT : H.IsComplete T) : H.IsComplete S :=
  fun e he hk => hT e (he.trans hST) hk

end KUniformHypergraph

/-! ## Rooted Trees with Ordered Vertices -/

/-- A rooted tree on vertices {0, 1, ..., t}, represented by a parent function.
    Vertex 0 is the root (its own parent), and every other vertex i has parent(i) < i. -/
structure OrderedRootedTree (t : ℕ) where
  parent : Fin (t + 1) → Fin (t + 1)
  root_self : parent ⟨0, Nat.zero_lt_succ t⟩ = ⟨0, Nat.zero_lt_succ t⟩
  parent_lt : ∀ i : Fin (t + 1), 0 < i.val → (parent i).val < i.val

namespace OrderedRootedTree

/-- The depth of a vertex (distance from the root) in the tree. -/
def depth {t : ℕ} (T : OrderedRootedTree t) (i : Fin (t + 1)) : ℕ :=
  if h : i.val = 0 then 0
  else
    have : (T.parent i).val < i.val := T.parent_lt i (Nat.pos_of_ne_zero h)
    T.depth (T.parent i) + 1
termination_by i.val

/-- The number of children of vertex i in the tree. -/
def numChildren {t : ℕ} (T : OrderedRootedTree t) (i : Fin (t + 1)) : ℕ :=
  (Finset.univ.filter (fun j : Fin (t + 1) => T.parent j = i ∧ j ≠ i)).card

/-- The degree of vertex i in the tree (children + parent edge if nonroot). -/
def degree {t : ℕ} (T : OrderedRootedTree t) (i : Fin (t + 1)) : ℕ :=
  T.numChildren i + if 0 < i.val then 1 else 0

end OrderedRootedTree

/-! ## (k,C)-Layered Trees (Definition 2.1) -/

/-- **Definition 2.1**: A tree T with vertex ordering v₀, v₁, ..., vₜ is a (k,C)-layered
    tree if:
    (1) Each vᵢ is adjacent to some vⱼ with j < i (automatic from parent function)
    (2) For all i, dist(v₀, vᵢ) ≤ k
    (3) For all i, deg(vᵢ) ≤ 2^(C+i) -/
def IsKCLayeredTree (k C : ℕ) {t : ℕ} (T : OrderedRootedTree t) : Prop :=
  (∀ i : Fin (t + 1), T.depth i ≤ k) ∧
  (∀ i : Fin (t + 1), T.degree i ≤ 2 ^ (C + i.val))

end

/-! ========== LayeredTree.lean ========== -/

/-!
# Layered Tree Bound (Lemma 2.2)

Helper lemmas and the proof that (k,C)-layered trees have bounded size.
-/

noncomputable section

namespace OrderedRootedTree

/-! ## Basic properties of depth -/

/-- The root has depth 0. -/
lemma depth_root {t : ℕ} (T : OrderedRootedTree t) :
    T.depth ⟨0, Nat.zero_lt_succ t⟩ = 0 := by
  rw [depth]; simp

/-- A nonroot vertex has depth = depth(parent) + 1. -/
lemma depth_pos {t : ℕ} (T : OrderedRootedTree t) (i : Fin (t + 1)) (h : 0 < i.val) :
    T.depth i = T.depth (T.parent i) + 1 := by
  conv_lhs => rw [depth]
  simp only [show ¬(i.val = 0) from by omega, ↓reduceDIte]

/-- A vertex with depth 0 must be the root. -/
lemma depth_zero_is_root {t : ℕ} (T : OrderedRootedTree t) (i : Fin (t + 1))
    (h : T.depth i = 0) : i = ⟨0, Nat.zero_lt_succ t⟩ := by
  by_contra hne
  have hpos : 0 < i.val := by
    obtain ⟨v, hv⟩ := i; simp only [Fin.mk.injEq] at hne; exact Nat.pos_of_ne_zero hne
  rw [T.depth_pos i hpos] at h
  omega

/-- If depth ≤ 0 for all vertices, the tree has only one vertex. -/
lemma all_depth_zero_implies_singleton {t : ℕ} (T : OrderedRootedTree t)
    (h : ∀ i : Fin (t + 1), T.depth i ≤ 0) : t = 0 := by
  by_contra ht
  have : 0 < t := Nat.pos_of_ne_zero ht
  have h1 : T.depth ⟨1, by omega⟩ = 0 := Nat.le_zero.mp (h ⟨1, by omega⟩)
  have h3 := T.depth_zero_is_root ⟨1, by omega⟩ h1
  simp at h3

/-- If i has depth ≤ 1 and i ≠ root, then parent(i) = root. -/
lemma depth_one_parent_is_root {t : ℕ} (T : OrderedRootedTree t)
    (i : Fin (t + 1)) (hi : 0 < i.val) (hd : T.depth i ≤ 1) :
    T.parent i = ⟨0, Nat.zero_lt_succ t⟩ := by
  rw [T.depth_pos i hi] at hd
  have : T.depth (T.parent i) = 0 := by omega
  exact T.depth_zero_is_root _ this

end OrderedRootedTree

/-! ## Layered tree bounds -/

/-- **Base case k=0**: A (0,C)-layered tree has at most 1 vertex. -/
theorem layered_tree_bounded_zero (C : ℕ) :
    ∀ t : ℕ, ∀ T : OrderedRootedTree t,
      IsKCLayeredTree 0 C T → t + 1 ≤ 1 := by
  intro t T ⟨hdepth, _⟩
  have := T.all_depth_zero_implies_singleton hdepth
  omega

/-
**Base case k=1**: A (1,C)-layered tree has at most 2^C + 1 vertices.
    All non-root vertices are children of the root, and the root has degree ≤ 2^C.
-/
theorem layered_tree_bounded_one (C : ℕ) :
    ∀ t : ℕ, ∀ T : OrderedRootedTree t,
      IsKCLayeredTree 1 C T → t + 1 ≤ 2^C + 1 := by
  intro t T hT
  obtain ⟨h_depth, h_degree⟩ := hT
  -- Since every non-root vertex is a child of the root, the non-root vertices
  -- are exactly the children of the root.
  have h_num_children :
      (Finset.univ.filter (fun j => T.parent j = ⟨0, Nat.zero_lt_succ t⟩ ∧
        j ≠ ⟨0, Nat.zero_lt_succ t⟩)).card = t := by
    convert
      Finset.card_erase_of_mem
        (Finset.mem_univ (⟨0, Nat.zero_lt_succ t⟩ : Fin (t + 1)))
      using 2
    · ext j
      by_cases hj : j = ⟨ 0, Nat.zero_lt_succ t ⟩ <;> simp +decide [ hj ]
      exact fun _ =>
        OrderedRootedTree.depth_one_parent_is_root T j
          (Nat.pos_of_ne_zero fun h => hj <| Fin.ext h) (h_depth j)
    · simp +decide [ Finset.card_univ ]
  have h_degree_root :
      (Finset.univ.filter (fun j => T.parent j = ⟨0, Nat.zero_lt_succ t⟩ ∧
        j ≠ ⟨0, Nat.zero_lt_succ t⟩)).card ≤ 2 ^ C := by
    specialize h_degree ⟨0, Nat.zero_lt_succ t⟩
    simpa [OrderedRootedTree.degree, OrderedRootedTree.numChildren] using h_degree
  omega

-- The general `layered_tree_bounded` is proved in LayeredTreeGeneral.lean

end

/-! ========== TreeContraction.lean ========== -/

/-!
# Tree Contraction Helper

The key helper for the layered tree bound: extracting the first block
between the first and second children of the root yields a (k, C+1)-layered tree.
-/

noncomputable section

/-- In an OrderedRootedTree, v₁ is always a child of the root (since parent(1) < 1 means
    parent(1) = 0). -/
lemma first_vertex_is_child_of_root {t : ℕ} (T : OrderedRootedTree t) (ht : 0 < t) :
    T.parent ⟨1, by omega⟩ = ⟨0, Nat.zero_lt_succ t⟩ := by
  have h := T.parent_lt ⟨1, by omega⟩ (by simp)
  ext; simp at h ⊢; omega

/-
The first block {v₁, ..., v_{c₂-1}} (between the first and second children of root)
    forms an OrderedRootedTree that is (k, C+1)-layered.

    Given a (k+1, C)-layered tree T and c₂ (the index of the second child of root,
    or t+1 if there is only one child), the restriction of T to {v₁, ..., v_{c₂-1}}
    with shifted indices is a valid (k, C+1)-layered tree.
-/
theorem first_block_layered {t k C : ℕ} (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T)
    (c₂ : ℕ) (hc₂_ge : 2 ≤ c₂) (hc₂_le : c₂ ≤ t + 1)
    (h_no_child : ∀ j : ℕ, 1 < j → j < c₂ →
      (hj : j < t + 1) → T.parent ⟨j, hj⟩ ≠ ⟨0, Nat.zero_lt_succ t⟩) :
    ∃ T' : OrderedRootedTree (c₂ - 2), IsKCLayeredTree k (C + 1) T' := by
  -- Define the new tree T' with vertices {0, 1, ..., c₂-2} and parent
  -- function T'.parent(i) = (T.parent ⟨i+1, _⟩).val - 1.
  set T' : OrderedRootedTree (c₂ - 2) := ⟨fun i => ⟨(T.parent ⟨i.val + 1, by
    omega⟩).val - 1, by
    all_goals generalize_proofs at *
    have := T.parent_lt ⟨ i + 1, by linarith ⟩ ( Nat.succ_pos _ )
    grind⟩, by
    have := first_vertex_is_child_of_root T ( by omega ) ; aesop;, by
    intro i hi
    have := T.parent_lt
      ⟨ i + 1, by
        linarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 2 ≤ c₂ ) ] ⟩
      ( by simp )
    grind⟩
  generalize_proofs at *
  refine ⟨ T', ⟨ ?_, ?_ ⟩ ⟩ <;> intro i <;> simp_all +decide [ IsKCLayeredTree ]
  · have h_depth_T' : ∀ i : Fin (c₂ - 2 + 1), T'.depth i + 1 ≤ T.depth ⟨i.val + 1, by
      grind⟩ := by
      intro i
      rcases i with ⟨i, hi⟩
      generalize_proofs at *
      induction i using Nat.strong_induction_on with
      | h i ih =>
        generalize_proofs at *
        unfold OrderedRootedTree.depth; simp +decide [ * ]
        split_ifs <;> (simp_all +decide; try omega)
        convert ih (T'.parent ⟨i, hi⟩).val
          _
          (Nat.le_of_lt_succ (T'.parent ⟨i, hi⟩).isLt)
          (by
            have hp_lt := (T'.parent ⟨i, hi⟩).isLt
            omega) using 1
        all_goals generalize_proofs at *
        · congr! 1
          generalize_proofs at *
          exact Eq.symm ( Fin.ext <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero <| by
            exact fun h =>
              h_no_child ( i + 1 )
                ( Nat.succ_lt_succ ( Nat.pos_of_ne_zero ‹_› ) )
                ( by omega ) ( by omega ) ( Fin.ext <| by aesop ) )
        · exact T'.parent_lt ⟨i, hi⟩ (Nat.pos_of_ne_zero (by assumption))
    generalize_proofs at *
    linarith [
      h_depth_T' i,
      hT.1 ⟨ i + 1, by
        linarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 2 ≤ c₂ ) ] ⟩ ]
  · refine le_trans ?_
      ( pow_le_pow_right₀ ( by decide )
        ( show C + 1 + ( i : ℕ ) ≥ C + ( i + 1 : ℕ ) by linarith ) )
    refine le_trans ?_
      ( hT.2 ⟨ i + 1, by
        linarith [ Fin.is_lt i, Nat.sub_add_cancel ( by linarith : 2 ≤ c₂ ) ] ⟩ )
    refine add_le_add ?_ ?_
    · refine le_trans
        (b := (Finset.image
          ( fun j : Fin ( c₂ - 2 + 1 ) =>
            ⟨ j + 1, by
              linarith [ Fin.is_lt j, Nat.sub_add_cancel ( by linarith : 2 ≤ c₂ ) ] ⟩ )
          ( Finset.filter ( fun j : Fin ( c₂ - 2 + 1 ) =>
            T'.parent j = i ∧ j ≠ i ) Finset.univ )).card)
        ?_ ( Finset.card_mono ?_ )
      · rw [
          Finset.card_image_of_injective _ fun x y hxy => by
            simpa [ Fin.ext_iff ] using hxy ]
        aesop
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨j, hj, rfl⟩
        rcases hj with ⟨hj_parent, hj_ne⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · ext
          let jUp : Fin (t + 1) :=
            ⟨j.val + 1, by
              have hc₂ : 2 ≤ c₂ := by linarith
              linarith [Fin.is_lt j, Nat.sub_add_cancel hc₂]⟩
          have hparent_val :
              (T.parent jUp).val - 1 = i.val := by
            simpa [jUp] using congrArg Fin.val hj_parent
          have hj_pos : 0 < j.val := by
            by_contra hj_nonpos
            have hj_zero : j = ⟨0, by omega⟩ := by
              ext
              exact Nat.eq_zero_of_not_pos hj_nonpos
            have hi_zero : i = ⟨0, by omega⟩ := by
              have hroot : T'.parent j = ⟨0, by omega⟩ := by
                simpa [hj_zero] using T'.root_self
              exact hj_parent ▸ hroot
            exact hj_ne (by simp [hj_zero, hi_zero])
          have hparent_ne_root :
              T.parent jUp ≠ ⟨0, Nat.zero_lt_succ t⟩ := by
            simpa [jUp] using h_no_child (j.val + 1) (by omega) (by omega) (by omega)
          have hparent_pos :
              0 < (T.parent jUp).val := by
            exact Nat.pos_of_ne_zero (fun h0 => hparent_ne_root (Fin.ext h0))
          change
            (T.parent jUp).val = i.val + 1
          calc
            (T.parent jUp).val = (T.parent jUp).val - 1 + 1 := by
              exact (Nat.succ_pred_eq_of_pos hparent_pos).symm
            _ = i.val + 1 := by rw [hparent_val]
        · intro hx_eq
          exact hj_ne (Fin.ext (by
            have := congrArg Fin.val hx_eq
            simp at this
            omega))
    · grind (gen := 12)

end

/-! ========== ContractionHelper.lean ========== -/

/-!
# Contraction Construction Helper

Helper definitions for the full contraction in LayeredTreeGeneral.
-/

noncomputable section

variable {t : ℕ} (T : OrderedRootedTree t)

/-- The set of "kept" vertices: those that are root (val = 0) or non-root-children
(parent ≠ root). These are the vertices that survive the contraction. -/
def keptVertices : Finset (Fin (t + 1)) :=
  Finset.univ.filter (fun j => j.val = 0 ∨ (T.parent j).val ≠ 0)

lemma keptVertices_card :
    (keptVertices T).card = t + 1 - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ := by
  have h_complement : keptVertices T = Finset.univ \
      Finset.univ.filter (fun j => j ≠ ⟨0, Nat.zero_lt_succ t⟩ ∧
        T.parent j = ⟨0, Nat.zero_lt_succ t⟩) := by
    ext j; simp [keptVertices]; tauto
  rw [h_complement, Finset.card_sdiff]; norm_num; congr; grind

lemma root_mem_keptVertices :
    (⟨0, Nat.zero_lt_succ t⟩ : Fin (t + 1)) ∈ keptVertices T := by
  simp [keptVertices]

/-- The contraction parent function. For kept vertex i:
    - Look up original vertex v = φ(i)
    - Get p = T.parent v
    - If p is kept: return φ⁻¹(p)
    - If p is not kept (root child): return 0 -/
def contractionParentFn
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1) →
    Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1) := by
  set m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
  have hcard' : (keptVertices T).card = t - m + 1 := by
    have := keptVertices_card T; omega
  set φ := (keptVertices T).orderIsoOfFin hcard'
  exact fun i =>
    let p := T.parent (φ i).val
    if hp : p ∈ keptVertices T then
      φ.symm ⟨p, hp⟩
    else
      ⟨0, by omega⟩

/-
φ(0) = root.
-/
lemma phi_zero_eq_root (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    let m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
    let hcard' : (keptVertices T).card = t - m + 1 := by
      have := keptVertices_card T; omega
    let φ := (keptVertices T).orderIsoOfFin hcard'
    (φ ⟨0, by omega⟩).val = ⟨0, Nat.zero_lt_succ t⟩ := by
  let m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
  let hcard' : (keptVertices T).card = t - m + 1 := by
    have := keptVertices_card T
    omega
  let φ := (keptVertices T).orderIsoOfFin hcard'
  change (φ ⟨0, by omega⟩).val = ⟨0, Nat.zero_lt_succ t⟩
  let s : Finset (Fin (t + 1)) := keptVertices T
  have hs : s.Nonempty := ⟨⟨0, Nat.zero_lt_succ t⟩, root_mem_keptVertices T⟩
  have hmin : s.min' hs = ⟨0, Nat.zero_lt_succ t⟩ := by
    refine le_antisymm (Finset.min'_le s _ (root_mem_keptVertices T)) ?_
    exact Finset.le_min' s hs _ (fun y _ => Fin.zero_le y)
  calc
    (φ ⟨0, by omega⟩).val = s.min' hs := by
      change (s.orderEmbOfFin hcard') ⟨0, by omega⟩ = s.min' hs
      exact Finset.orderEmbOfFin_zero hcard' (by omega)
    _ = ⟨0, Nat.zero_lt_succ t⟩ := hmin

/-
parent(0) = 0 for the contraction parent function.
-/
lemma contractionParentFn_root_self
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    contractionParentFn T hm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  let m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
  let hcard' : (keptVertices T).card = t - m + 1 := by
    have := keptVertices_card T
    omega
  let φ := (keptVertices T).orderIsoOfFin hcard'
  change
    (let p := T.parent (φ (0 : Fin (t - m + 1))).val
      if hp : p ∈ keptVertices T then φ.symm ⟨p, hp⟩ else 0) = 0
  have hφ : (φ (0 : Fin (t - m + 1))).val = ⟨0, Nat.zero_lt_succ t⟩ := by
    change (((keptVertices T).orderIsoOfFin hcard') (0 : Fin (t - m + 1))).val =
      ⟨0, Nat.zero_lt_succ t⟩
    exact phi_zero_eq_root T hm
  have hp_eq : T.parent (φ (0 : Fin (t - m + 1))).val = ⟨0, Nat.zero_lt_succ t⟩ := by
    rw [hφ, T.root_self]
  rw [hp_eq]
  change
    (if hp : (⟨0, Nat.zero_lt_succ t⟩ : Fin (t + 1)) ∈ keptVertices T then
        φ.symm ⟨⟨0, Nat.zero_lt_succ t⟩, hp⟩
      else 0) = 0
  simp only [root_mem_keptVertices, ↓reduceDIte]
  rw [show (⟨⟨0, Nat.zero_lt_succ t⟩, root_mem_keptVertices T⟩ : (keptVertices T)) =
      φ (0 : Fin (t - m + 1)) by
    ext
    exact congrArg Fin.val hφ.symm]
  exact OrderIso.symm_apply_apply φ 0

/-
parent(i) < i for i > 0 in the contraction.
-/
lemma contractionParentFn_parent_lt
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    ∀ i : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
      0 < i.val → (contractionParentFn T hm i).val < i.val := by
  intro i hi
  let m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
  let hcard' : (keptVertices T).card = t - m + 1 := by
    have := keptVertices_card T
    omega
  let φ := (keptVertices T).orderIsoOfFin hcard'
  change
    (let p := T.parent (φ i).val
      if hp : p ∈ keptVertices T then φ.symm ⟨p, hp⟩ else 0).val < i.val
  by_cases hp : T.parent (φ i).val ∈ keptVertices T
  · rw [dif_pos hp]
    have hφ0 : (φ (0 : Fin (t - m + 1))).val = ⟨0, Nat.zero_lt_succ t⟩ := by
      change (((keptVertices T).orderIsoOfFin hcard') (0 : Fin (t - m + 1))).val =
        ⟨0, Nat.zero_lt_succ t⟩
      exact phi_zero_eq_root T hm
    have hv_pos : 0 < (φ i).val.val := by
      have hlt_sub : φ (0 : Fin (t - m + 1)) < φ i := φ.strictMono hi
      have hlt_fin : (φ (0 : Fin (t - m + 1))).val < (φ i).val := hlt_sub
      simpa [hφ0] using hlt_fin
    have h_parent_lt : (⟨T.parent (φ i).val, hp⟩ : (keptVertices T)) < φ i := by
      exact T.parent_lt (φ i).val hv_pos
    exact (OrderIso.symm_apply_lt φ).2 h_parent_lt
  · rw [dif_neg hp]
    exact hi

/-- The contraction of T as an OrderedRootedTree. -/
def contractionTree (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    OrderedRootedTree (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩) :=
  ⟨contractionParentFn T hm,
   by exact_mod_cast contractionParentFn_root_self T hm,
   contractionParentFn_parent_lt T hm⟩

/-
The contraction depth bound.
-/
lemma contractionTree_depth_le (k C : ℕ) (hT : IsKCLayeredTree (k + 1) C T)
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    ∀ i : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
      (contractionTree T hm).depth i ≤ k := by
  intro i
  have h_ind :
      ∀ j : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
        j.val > 0 →
        (contractionTree T hm).depth j + 1 ≤
          T.depth ((keptVertices T).orderIsoOfFin (by
            convert keptVertices_card T using 1
            omega) j).val := by
    intro j hj_pos
    rcases j with ⟨j, hj⟩
    change j > 0 at hj_pos
    generalize_proofs at *
    revert hj hj_pos
    induction j using Nat.strong_induction_on
    rename_i j ih
    intro hj hj_pos
    generalize_proofs at *
    by_cases h_case : (T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val) ∈ keptVertices T
    · -- Let $p$ be the parent of $j$ in the contraction tree.
      obtain ⟨p, hp⟩ :
          ∃ p : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
            (contractionTree T hm).parent ⟨j, hj⟩ = p ∧
              (keptVertices T).orderIsoOfFin ‹_› p =
                T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val := by
        let φ := (keptVertices T).orderIsoOfFin ‹_›
        refine ⟨φ.symm ⟨T.parent (φ ⟨j, hj⟩).val, h_case⟩, ?_, ?_⟩
        · unfold contractionTree contractionParentFn
          change
            (if h : T.parent (φ ⟨j, hj⟩).val ∈ keptVertices T then
                φ.symm ⟨T.parent (φ ⟨j, hj⟩).val, h⟩
              else 0) =
              φ.symm ⟨T.parent (φ ⟨j, hj⟩).val, h_case⟩
          split_ifs with h
          · rfl
          · exact False.elim (h h_case)
        · exact congrArg Subtype.val
            (OrderIso.apply_symm_apply φ ⟨T.parent (φ ⟨j, hj⟩).val, h_case⟩)
      generalize_proofs at *
      by_cases hp_pos : p.val > 0
      · have h_ind :
            (contractionTree T hm).depth p + 1 ≤
              T.depth ((keptVertices T).orderIsoOfFin ‹_› p).val := by
          apply_assumption
          · generalize_proofs at *
            have := contractionParentFn_parent_lt T hm ⟨ j, hj ⟩ hj_pos
            aesop
          · generalize_proofs at *
            exact hp_pos
        generalize_proofs at *
        have h_depth_j :
            (contractionTree T hm).depth ⟨j, hj⟩ =
              (contractionTree T hm).depth p + 1 := by
          rw [ ← hp.1, OrderedRootedTree.depth_pos ] ; aesop
        generalize_proofs at *
        have h_depth_j :
            T.depth ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val =
              T.depth
                (T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val) + 1 := by
          apply OrderedRootedTree.depth_pos
          have h_order_iso :
              ∀ i j : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
                i < j →
                ((keptVertices T).orderIsoOfFin ‹_› i).val <
                  ((keptVertices T).orderIsoOfFin ‹_› j).val := by
            exact fun i j hij => ((keptVertices T).orderIsoOfFin ‹_›).strictMono hij
          generalize_proofs at *
          exact lt_of_le_of_lt ( Nat.zero_le _ )
            ( h_order_iso ⟨ 0, by linarith ⟩ ⟨ j, hj ⟩
              ( Nat.pos_of_ne_zero ( by aesop ) ) )
        generalize_proofs at *
        grind +ring
      · have h_contra :
            T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val =
              ⟨0, Nat.zero_lt_succ t⟩ := by
          have hp_zero : p = ⟨0, by omega⟩ := by
            ext
            exact Nat.eq_zero_of_not_pos hp_pos
          rw [← hp.2, hp_zero]
          simpa using phi_zero_eq_root T hm
        generalize_proofs at *
        have h_contra : ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val > 0 := by
          have h_contra :
              ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val >
                ((keptVertices T).orderIsoOfFin ‹_› ⟨0, by omega⟩).val := by
            exact ( keptVertices T ).orderIsoOfFin ‹_› |>.strictMono hj_pos
          generalize_proofs at *
          exact lt_of_le_of_lt ( Nat.zero_le _ ) h_contra
        generalize_proofs at *
        grind +locals
    · have h_contra : (contractionTree T hm).depth ⟨j, hj⟩ = 1 := by
        rw [ OrderedRootedTree.depth_pos ] <;> norm_num [ h_case ]
        · convert OrderedRootedTree.depth_root ( contractionTree T hm ) using 1
          generalize_proofs at *
          unfold contractionTree contractionParentFn; aesop
        · exact hj_pos
      have h_contra : T.depth (T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val) ≥ 1 := by
        have h_contra : (T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val).val ≠ 0 := by
          intro h; simp_all +decide [ keptVertices ]
        have h_contra : ∀ i : Fin (t + 1), i.val ≠ 0 → T.depth i ≥ 1 := by
          intros i hi_nonzero
          have h_contra : T.depth i = T.depth (T.parent i) + 1 := by
            exact OrderedRootedTree.depth_pos T i ( Nat.pos_of_ne_zero hi_nonzero )
          exact h_contra.symm ▸ Nat.succ_pos _
        exact h_contra _ ‹_›
      have h_contra :
          T.depth ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val =
            T.depth (T.parent ((keptVertices T).orderIsoOfFin ‹_› ⟨j, hj⟩).val) +
              1 := by
        apply OrderedRootedTree.depth_pos
        generalize_proofs at *
        grind +suggestions
      linarith
  generalize_proofs at *
  by_cases hi : 0 < i.val
  · simp_all +decide [IsKCLayeredTree]
    exact Nat.le_of_lt_succ (lt_of_lt_of_le (h_ind i hi) (hT.1 _))
  · have hi0 : i = ⟨0, by omega⟩ := by
      ext
      exact Nat.eq_zero_of_not_pos hi
    rw [hi0, OrderedRootedTree.depth_root]
    exact Nat.zero_le k

/-
For non-root vertices, degree in contraction ≤ 2^(C + 2^C + i).
-/
lemma contractionTree_degree_nonroot (k C : ℕ) (hT : IsKCLayeredTree (k + 1) C T)
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    ∀ i : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
      i.val > 0 →
      (contractionTree T hm).degree i ≤ 2 ^ (C + 2 ^ C + i.val) := by
  intro i hi
  have h_deg_le :
      (contractionTree T hm).degree i ≤
        T.degree (Fin.mk ((keptVertices T).orderIsoOfFin (by
          convert keptVertices_card T using 1
          omega) i).val (by
          exact Nat.lt_succ_of_le ( Fin.is_le _ ))) := by
    all_goals generalize_proofs at *
    unfold OrderedRootedTree.degree contractionTree
    split_ifs with h_contract h_original <;> simp_all +decide
    · refine le_trans
        (b := (Finset.image
          ( fun j => ( keptVertices T ).orderEmbOfFin ‹_› j )
          ( Finset.filter
            ( fun j =>
              ( if h :
                  T.parent ( ( keptVertices T ).orderEmbOfFin ‹_› j ) ∈ keptVertices T
                then
                  ( keptVertices T ).orderIsoOfFin ‹_› |>.symm
                    ⟨ T.parent ( ( keptVertices T ).orderEmbOfFin ‹_› j ), h ⟩
                else
                  0 ) = i ∧ ¬j = i )
            ( Finset.univ :
              Finset ( Fin ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ + 1 ) ) ) )).card)
        ?_ ( Finset.card_mono ?_ )
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ]
        exact le_rfl
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rcases hx with ⟨j, hj, rfl⟩
        rcases hj with ⟨hj_parent, hj_ne⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        let φ := (keptVertices T).orderIsoOfFin ‹_›
        constructor
        · by_cases hkeep :
              T.parent ((keptVertices T).orderEmbOfFin ‹_› j) ∈ keptVertices T
          · have hj_parent' := hj_parent
            rw [dif_pos hkeep] at hj_parent'
            have hsymm :
                φ.symm ⟨T.parent ((keptVertices T).orderEmbOfFin ‹_› j), hkeep⟩ = i := by
              simpa [φ] using hj_parent'
            calc
              T.parent ((keptVertices T).orderEmbOfFin ‹_› j) =
                  (⟨T.parent ((keptVertices T).orderEmbOfFin ‹_› j), hkeep⟩ :
                    keptVertices T).val := rfl
              _ =
                  (φ (φ.symm
                    ⟨T.parent ((keptVertices T).orderEmbOfFin ‹_› j), hkeep⟩)).val := by
                rw [OrderIso.apply_symm_apply]
              _ = (φ i).val := by rw [hsymm]
          · have hj_parent' := hj_parent
            rw [dif_neg hkeep] at hj_parent'
            have hi_zero : i.val = 0 := by
              simpa using congrArg Fin.val hj_parent'.symm
            omega
        · intro hx_eq
          exact hj_ne (((keptVertices T).orderEmbOfFin ‹_›).injective hx_eq)
    · exfalso
      have hφi_root :
          ((keptVertices T).orderIsoOfFin ‹_› i).val = ⟨0, Nat.zero_lt_succ t⟩ := by
        simpa using h_original
      have hφ0_root :
          ((keptVertices T).orderIsoOfFin ‹_› ⟨0, by omega⟩).val =
            ⟨0, Nat.zero_lt_succ t⟩ := by
        simpa using phi_zero_eq_root T hm
      have hi_zero : i = ⟨0, by omega⟩ := by
        exact ((keptVertices T).orderIsoOfFin ‹_›).injective (Subtype.ext (by
          rw [hφi_root, hφ0_root]))
      exact (Nat.ne_of_gt h_contract) (by
        simpa using congrArg Fin.val hi_zero)
  generalize_proofs at *
  have h_deg_le : T.degree (Fin.mk ((keptVertices T).orderIsoOfFin (by
  assumption) i).val (by
  assumption)) ≤ 2 ^ (C + ((keptVertices T).orderIsoOfFin (by
  assumption) i).val.val) := by
    exact hT.2 _
  generalize_proofs at *
  have h_deg_le : ((keptVertices T).orderIsoOfFin (by
  assumption) i).val.val ≤ i.val + T.numChildren ⟨0, Nat.zero_lt_succ t⟩ := by
    have h_card_le :
        Finset.card
          (Finset.filter
            (fun j =>
              j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val ∧
                j.val ≠ 0 ∧ (T.parent j).val = 0)
            (Finset.univ : Finset (Fin (t + 1)))) ≤
          T.numChildren ⟨0, Nat.zero_lt_succ t⟩ := by
      refine le_trans
        (b := (Finset.filter
          ( fun j => T.parent j = ⟨ 0, Nat.zero_lt_succ t ⟩ ∧
            j ≠ ⟨ 0, Nat.zero_lt_succ t ⟩ )
          Finset.univ).card)
        ( Finset.card_le_card ?_ ) ?_
      · grind
      · exact Finset.card_le_card fun x hx => by aesop
    generalize_proofs at *
    have h_card_le :
        Finset.card
          (Finset.filter
            (fun j =>
              j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val ∧
                (j.val = 0 ∨ (T.parent j).val ≠ 0))
            (Finset.univ : Finset (Fin (t + 1)))) ≤ i.val + 1 := by
      have h_card_le :
          Finset.card
            (Finset.filter
              (fun j =>
                j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val ∧
                  (j.val = 0 ∨ (T.parent j).val ≠ 0))
              (Finset.univ : Finset (Fin (t + 1)))) ≤
            Finset.card
              (Finset.filter
                (fun j => j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val)
                (keptVertices T)) := by
        refine Finset.card_mono ?_
        simp +contextual [ Finset.subset_iff, keptVertices ]
      generalize_proofs at *
      refine le_trans h_card_le ?_
      rw [
        show
          ( Finset.filter
            ( fun j : Fin ( t + 1 ) =>
              ( j : ℕ ) ≤ ( ( keptVertices T ).orderIsoOfFin ‹_› i : Fin ( t + 1 ) ) )
            ( keptVertices T ) ) =
            Finset.image
              ( fun j : Fin ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ + 1 ) =>
                ( keptVertices T ).orderIsoOfFin ‹_› j )
              ( Finset.Iic i ) from ?_ ]
      · change (((Finset.image
          (fun j : Fin ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ + 1 ) =>
            (keptVertices T).orderIsoOfFin ‹_› j)
          (Finset.Iic i)) >>= fun a => pure (a : Fin (t + 1))).card ≤ i.val + 1)
        simp only [Finset.bind_def, Finset.pure_def, Finset.sup_singleton_apply]
        letI : DecidableEq (Fin (t + 1)) := Classical.decEq _
        refine Finset.card_image_le.trans ?_
        letI : DecidableEq (Fin (t + 1)) := instDecidableEqFin (t + 1)
        refine Finset.card_image_le.trans ?_
        rw [Fin.card_Iic]
      · ext x
        simp
        let φ := (keptVertices T).orderIsoOfFin ‹_›
        constructor
        · intro h
          let y : (keptVertices T) := ⟨x, h.1⟩
          let j := φ.symm y
          have hj : j ≤ i := (OrderIso.symm_apply_le φ).2 h.2
          refine ⟨j, hj, ?_⟩
          change x = (φ (φ.symm y)).val
          exact (congrArg Subtype.val (OrderIso.apply_symm_apply φ y)).symm
        · rintro ⟨j, hj, rfl⟩
          exact ⟨(φ j).property, (OrderIso.le_iff_le φ).2 hj⟩
    generalize_proofs at *
    have h_card_le :
        Finset.card
          (Finset.filter
            (fun j => j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val)
            (Finset.univ : Finset (Fin (t + 1)))) ≤
          i.val + 1 + T.numChildren ⟨0, Nat.zero_lt_succ t⟩ := by
      have h_card_le :
          Finset.card
            (Finset.filter
              (fun j => j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val)
              (Finset.univ : Finset (Fin (t + 1)))) ≤
            Finset.card
              (Finset.filter
                (fun j =>
                  j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val ∧
                    (j.val = 0 ∨ (T.parent j).val ≠ 0))
                (Finset.univ : Finset (Fin (t + 1)))) +
              Finset.card
                (Finset.filter
                  (fun j =>
                    j.val ≤ ((keptVertices T).orderIsoOfFin ‹_› i).val.val ∧
                      j.val ≠ 0 ∧ (T.parent j).val = 0)
                  (Finset.univ : Finset (Fin (t + 1)))) := by
        rw [ ← Finset.card_union_add_card_inter ]
        exact le_add_right ( Finset.card_le_card fun x hx => by
          by_cases hx' : ( x : ℕ ) = 0 <;>
            by_cases hx'' : ( T.parent x : ℕ ) = 0 <;>
              aesop )
      generalize_proofs at *
      linarith
    generalize_proofs at *
    contrapose! h_card_le
    rw [
      show
        ( Finset.filter
          ( fun j : Fin ( t + 1 ) =>
            ( j : ℕ ) ≤ ( ( keptVertices T ).orderIsoOfFin ‹_› i : Fin ( t + 1 ) ) )
          Finset.univ ) =
          Finset.Iic ( ( keptVertices T ).orderIsoOfFin ‹_› i : Fin ( t + 1 ) ) by
        ext
        aesop ]
    simp +arith +decide
    linarith!
  generalize_proofs at *
  have h_deg_le : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ 2 ^ C := by
    have := hT.2 ⟨ 0, Nat.zero_lt_succ t ⟩ ; simp_all +decide [ OrderedRootedTree.degree ]
  generalize_proofs at *
  exact le_trans ‹_› ( le_trans ‹_› ( pow_le_pow_right₀ ( by decide ) ( by linarith ) ) )

end

/-! ========== SuperRootBound.lean ========== -/

/-!
# Super-root Degree Bound

Proves the degree bound for vertex 0 (the super-root) in the contracted tree.
-/

noncomputable section

variable {t : ℕ}

/-! ## Auxiliary arithmetic -/

lemma Nat.le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

/-! ## Prefix Subtree -/

/-- Restrict T to vertices {0, ..., s}. -/
def prefixSubtree (T : OrderedRootedTree t) (s : ℕ) (hs : s ≤ t) :
    OrderedRootedTree s where
  parent i := ⟨(T.parent ⟨i.val, by omega⟩).val, by
    by_cases h : i.val = 0
    · have h_eq : (⟨i.val, (by omega : i.val < t + 1)⟩ : Fin (t + 1)) =
          ⟨0, Nat.zero_lt_succ t⟩ := Fin.ext h
      rw [h_eq, T.root_self]; exact Nat.zero_lt_succ s
    · exact Nat.lt_trans (T.parent_lt ⟨i.val, by omega⟩ (Nat.pos_of_ne_zero h)) i.isLt⟩
  root_self := by
    ext
    change (T.parent ⟨(0 : Fin (s + 1)).val, by omega⟩).val = (0 : Fin (s + 1)).val
    have := T.root_self
    exact congrArg Fin.val this
  parent_lt := fun i hi => by
    change (T.parent ⟨i.val, by omega⟩).val < i.val
    exact T.parent_lt ⟨i.val, by omega⟩ hi

/-- Parent in prefix = parent in full tree (at the value level). -/
@[simp]
lemma prefixSubtree_parent_val (T : OrderedRootedTree t) (s : ℕ) (hs : s ≤ t)
    (i : Fin (s + 1)) :
    ((prefixSubtree T s hs).parent i).val = (T.parent ⟨i.val, by omega⟩).val := rfl

/-
Depth in prefix equals depth in full tree.
-/
lemma prefixSubtree_depth (T : OrderedRootedTree t) (s : ℕ) (hs : s ≤ t)
    (i : Fin (s + 1)) :
    (prefixSubtree T s hs).depth i = T.depth ⟨i.val, by omega⟩ := by
  rcases i with ⟨i, hi⟩
  revert hi
  induction i using Nat.strong_induction_on
  rename_i i ih
  intro hi
  by_cases hi : 0 < i
  · unfold OrderedRootedTree.depth
    split_ifs <;> simp_all +decide
    have hp_lt : ((prefixSubtree T s hs).parent ⟨i, by omega⟩).val < i :=
      (prefixSubtree T s hs).parent_lt ⟨i, by omega⟩ hi
    have hp_le : ((prefixSubtree T s hs).parent ⟨i, by omega⟩).val ≤ s :=
      Nat.le_of_lt_succ (Fin.is_lt _)
    have hih := ih ((prefixSubtree T s hs).parent ⟨i, by omega⟩).val hp_lt hp_le
    simpa [prefixSubtree] using congrArg Nat.succ hih
  · unfold OrderedRootedTree.depth; aesop

/-
The prefix subtree inherits the layered property.
-/
lemma prefixSubtree_layered (T : OrderedRootedTree t) {k C : ℕ}
    (hT : IsKCLayeredTree k C T) (s : ℕ) (hs : s ≤ t) :
    IsKCLayeredTree k C (prefixSubtree T s hs) := by
  exact ⟨ fun i => prefixSubtree_depth T s hs i ▸ hT.1 _, fun i => by
    -- The degree in the prefix subtree is less than or equal to the degree in the full tree.
    have h_deg_le : (prefixSubtree T s hs).degree i ≤ T.degree ⟨i.val, by omega⟩ := by
      unfold OrderedRootedTree.degree
      simp +decide [ OrderedRootedTree.numChildren ]
      refine le_trans
        (b := (Finset.image
          ( fun j : Fin ( s + 1 ) => ⟨ j, by linarith [ Fin.is_lt j ] ⟩ )
          ( Finset.filter
            ( fun j : Fin ( s + 1 ) => ( prefixSubtree T s hs ).parent j = i ∧ ¬j = i )
            Finset.univ )).card)
        ?_ ( Finset.card_le_card ?_ )
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ]
      · simp +decide [ Finset.subset_iff ]
        rintro x j hj₁ hj₂ rfl; simp_all +decide [ Fin.ext_iff, prefixSubtree ]
    exact le_trans h_deg_le ( hT.2 _ ) ⟩

/-! ## Root Children -/

/-- The finset of root children of T. -/
def rootChildrenFinset (T : OrderedRootedTree t) : Finset (Fin (t + 1)) :=
  Finset.univ.filter (fun j =>
    T.parent j = ⟨0, Nat.zero_lt_succ t⟩ ∧ j ≠ ⟨0, Nat.zero_lt_succ t⟩)

lemma rootChildrenFinset_card (T : OrderedRootedTree t) :
    (rootChildrenFinset T).card = T.numChildren ⟨0, Nat.zero_lt_succ t⟩ := by
  simp [rootChildrenFinset, OrderedRootedTree.numChildren]

/-- The root has at most 2^C children in a (k, C)-layered tree. -/
lemma root_children_le' {k C : ℕ} (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree k C T) :
    T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ 2 ^ C := by
  have h_root : T.degree ⟨0, Nat.zero_lt_succ t⟩ ≤ 2 ^ (C + 0) := hT.2 _
  unfold OrderedRootedTree.degree at h_root; simp at h_root; exact h_root

/-! ## Contraction root degree bound -/

/-
The set of vertices whose parent is a root child, counted via biUnion,
    has cardinality equal to the sum of numChildren.
-/
lemma card_children_of_rootChildren (T : OrderedRootedTree t) :
    (Finset.univ.filter (fun v : Fin (t + 1) =>
      (T.parent v) ∈ rootChildrenFinset T ∧ v ≠ T.parent v)).card =
    ∑ x ∈ rootChildrenFinset T, T.numChildren x := by
  rw [ eq_comm, Finset.sum_congr rfl ]
  rotate_right
  · exact fun x => ∑ i ∈ Finset.univ, if T.parent i = x ∧ i ≠ x then 1 else 0
  · rw [ ← Finset.sum_product' ]
    simp +zetaDelta at *
    refine Finset.card_bij ( fun x hx => x.2 ) ?_ ?_ ?_ <;> aesop
  · unfold OrderedRootedTree.numChildren; aesop

/-
Each child of root 0 in the contraction has image under φ
    in the set of children of root children.
-/
set_option linter.unusedVariables false in
lemma contraction_children_zero_inject (T : OrderedRootedTree t)
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    let m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
    let hcard : (keptVertices T).card = t - m + 1 := by
      have := keptVertices_card T; omega
    let φ := (keptVertices T).orderIsoOfFin hcard
    (Finset.univ.filter (fun j : Fin (t - m + 1) =>
      (contractionTree T hm).parent j = ⟨0, by omega⟩ ∧ j ≠ ⟨0, by omega⟩)).card ≤
    (Finset.univ.filter (fun v : Fin (t + 1) =>
      (T.parent v) ∈ rootChildrenFinset T ∧ v ≠ T.parent v)).card := by
  let hcard :
      (keptVertices T).card =
        t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1 := by
    have := keptVertices_card T
    omega
  let φ := (keptVertices T).orderIsoOfFin hcard
  have h_inj :
      ∀ j : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1),
        (contractionTree T hm).parent j =
          ⟨0, Nat.zero_lt_succ (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩)⟩ →
        j ≠
          ⟨0, Nat.zero_lt_succ (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩)⟩ →
        (φ j).val ∈
          Finset.univ.filter (fun v : Fin (t + 1) =>
            T.parent v ∈ rootChildrenFinset T ∧ v ≠ T.parent v) := by
    intros j hj hj_ne_zero
    have h_parent : T.parent (φ j).val ∉ keptVertices T := by
      contrapose! hj
      have h_contra :
          φ.symm ⟨T.parent (φ j).val, hj⟩ ≠
            ⟨0, Nat.zero_lt_succ (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩)⟩ := by
        intro h
        have h_contra : T.parent (φ j).val = ⟨0, Nat.zero_lt_succ t⟩ := by
          have h_contra : φ (φ.symm ⟨T.parent (φ j).val, hj⟩) = ⟨T.parent (φ j).val, hj⟩ := by
            exact φ.apply_symm_apply _
          have := phi_zero_eq_root T hm; aesop
        have h_root_child : (φ j).val ∈ rootChildrenFinset T := by
          simp only [rootChildrenFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨h_contra, ?_⟩
          intro hφj_root
          apply hj_ne_zero
          have hφ0_root : (φ ⟨0, by omega⟩).val = ⟨0, Nat.zero_lt_succ t⟩ := by
            change (((keptVertices T).orderIsoOfFin hcard)
                (0 : Fin (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩ + 1))).val =
              ⟨0, Nat.zero_lt_succ t⟩
            exact phi_zero_eq_root T hm
          exact φ.injective (Subtype.ext (by
            rw [hφj_root, hφ0_root]))
        have h_not_kept : (φ j).val ∉ keptVertices T := by
          unfold rootChildrenFinset at h_root_child
          unfold keptVertices
          aesop
        exact h_not_kept <| φ j |>.2
      convert h_contra using 1
      exact dif_pos hj
    simp_all +decide [ keptVertices, rootChildrenFinset ]
    grind
  convert
    Finset.card_le_card
      ( show
          Finset.image
            ( fun j : Fin ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ + 1 ) =>
              ( φ j : Fin ( t + 1 ) ) )
            ( Finset.filter
              ( fun j : Fin ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ + 1 ) =>
                ( contractionTree T hm ).parent j =
                    ⟨ 0, Nat.zero_lt_succ
                      ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ ) ⟩ ∧
                  j ≠
                    ⟨ 0, Nat.zero_lt_succ
                      ( t - T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ ) ⟩ )
              Finset.univ ) ⊆
            Finset.filter
              ( fun v : Fin ( t + 1 ) =>
                T.parent v ∈ rootChildrenFinset T ∧ v ≠ T.parent v )
              Finset.univ from ?_ )
    using 1
  · rw [
      Finset.card_image_of_injective _ fun x y hxy => by
        simpa [ Fin.ext_iff ] using φ.injective <| Subtype.ext hxy ]
  · grind

/-- Key combinatorial lemma: numChildren of root in contraction ≤
    sum of numChildren of root children in T. -/
lemma contraction_root_numChildren_le (T : OrderedRootedTree t)
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    (contractionTree T hm).numChildren ⟨0, by omega⟩ ≤
    ∑ x ∈ rootChildrenFinset T, T.numChildren x := by
  calc (contractionTree T hm).numChildren ⟨0, by omega⟩
      ≤ (Finset.univ.filter (fun v : Fin (t + 1) =>
          (T.parent v) ∈ rootChildrenFinset T ∧ v ≠ T.parent v)).card := by
        exact contraction_children_zero_inject T hm
    _ = ∑ x ∈ rootChildrenFinset T, T.numChildren x :=
        card_children_of_rootChildren T

/-
Each root child x has numChildren ≤ 2^(C + x.val).
-/
lemma rootChild_numChildren_le {k C : ℕ} (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T) (x : Fin (t + 1))
    (_hx : x ∈ rootChildrenFinset T) :
    T.numChildren x ≤ 2 ^ (C + x.val) := by
  -- From the layered tree condition, the degree of x is at most 2^(C + x.val).
  have h_deg : T.degree x ≤ 2 ^ (C + x.val) := by
    exact hT.2 x
  exact le_trans ( Nat.le_add_right _ _ ) h_deg

/-
Contraction root degree ≤ sum of 2^(C + x.val) over root children.
-/
lemma contraction_root_degree_le_sum {k C : ℕ} (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T)
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    (contractionTree T hm).degree ⟨0, by omega⟩ ≤
    ∑ x ∈ rootChildrenFinset T, 2 ^ (C + x.val) := by
  change (contractionTree T hm).numChildren ⟨0, by omega⟩ ≤
    ∑ x ∈ rootChildrenFinset T, 2 ^ (C + x.val)
  exact
    (contraction_root_numChildren_le T hm).trans
      (Finset.sum_le_sum fun x hx => rootChild_numChildren_le T hT x hx)

/-! ## Iterative position bound -/

/-- Helper: the iterative bound function. -/
def iterBoundFn (C : ℕ) (boundK : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.rec (0 : ℕ) (fun j prev => prev + 2 ^ (C + (boundK (2 ^ C + C + prev) + j))) j

lemma iterBoundFn_zero (C : ℕ) (boundK : ℕ → ℕ) : iterBoundFn C boundK 0 = 0 := rfl

lemma iterBoundFn_succ (C : ℕ) (boundK : ℕ → ℕ) (j : ℕ) :
    iterBoundFn C boundK (j + 1) =
    iterBoundFn C boundK j + 2 ^ (C + (boundK (2 ^ C + C + iterBoundFn C boundK j) + j)) := rfl

/-
The contraction of a prefix subtree is (k, 2^C + C + S)-layered
    when S bounds the sum of 2^(C + x.val) over root children of the prefix.
-/
lemma prefix_contraction_layered {k C : ℕ}
    (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T)
    (s : ℕ) (hs : s ≤ t)
    (hm_pref : (prefixSubtree T s hs).numChildren ⟨0, Nat.zero_lt_succ s⟩ ≤ s)
    (S : ℕ)
    (hS : ∑ x ∈ rootChildrenFinset (prefixSubtree T s hs),
        2 ^ (C + x.val) ≤ S) :
    IsKCLayeredTree k (2 ^ C + C + S)
      (contractionTree (prefixSubtree T s hs) hm_pref) := by
  constructor
  · apply contractionTree_depth_le
    exact prefixSubtree_layered T hT s hs
  · intro i
    by_cases hi : i.val = 0
    · cases i with
      | mk iv hiv =>
        simp at hi
        subst iv
        change
          (contractionTree (prefixSubtree T s hs) hm_pref).degree
              ⟨0, Nat.zero_lt_succ (s - (prefixSubtree T s hs).numChildren ⟨0, Nat.zero_lt_succ s⟩)⟩ ≤
            2 ^ (2 ^ C + C + S + 0)
        refine (contraction_root_degree_le_sum
            (prefixSubtree T s hs) (prefixSubtree_layered T hT s hs) hm_pref).trans ?_
        exact hS.trans
          ((Nat.le_two_pow_self S).trans
            (Nat.pow_le_pow_right (by decide)
              (show S ≤ 2 ^ C + C + S + 0 by
                have hnonneg : 0 ≤ 2 ^ C + C := Nat.zero_le _
                omega)))
    · refine le_trans
        ( contractionTree_degree_nonroot
          ( prefixSubtree T s hs ) k C ?_ hm_pref i ( Nat.pos_of_ne_zero hi ) ) ?_
      · exact prefixSubtree_layered T hT s hs
      · exact pow_le_pow_right₀ ( by decide ) ( by linarith [ Nat.zero_le S ] )

/-
Root children of the prefix tree correspond to root children of T
    with index ≤ s (at the Fin.val level).
-/
lemma prefix_rootChildren_sum_eq (T : OrderedRootedTree t) (s : ℕ) (hs : s ≤ t) (f : ℕ → ℕ) :
    ∑ x ∈ rootChildrenFinset (prefixSubtree T s hs), f x.val =
    ∑ x ∈ (rootChildrenFinset T).filter (fun x => x.val ≤ s), f x.val := by
  unfold rootChildrenFinset
  refine Finset.sum_bij ( fun x hx => ⟨ x, by omega ⟩ ) ?_ ?_ ?_ ?_ <;> simp_all +decide
  · intro a ha ha'; have := congr_arg Fin.val ha; simp_all +decide [ prefixSubtree ]
    exact Nat.le_of_lt_succ a.2
  · exact fun a₁ ha₁ ha₂ a₂ ha₃ ha₄ h => Fin.ext h
  · intro b hb hb' hb''; use ⟨ b, by linarith [ Fin.is_lt b ] ⟩ ; aesop

/-
Root children of the prefix have count = root children of T with index ≤ s.
-/
lemma prefix_numChildren_root_eq (T : OrderedRootedTree t) (s : ℕ) (hs : s ≤ t) :
    (prefixSubtree T s hs).numChildren ⟨0, Nat.zero_lt_succ s⟩ =
    ((rootChildrenFinset T).filter (fun x => x.val ≤ s)).card := by
  refine Finset.card_bij ?_ ?_ ?_ ?_
  · use fun a ha => ⟨ a.val, by linarith [ Fin.is_lt a ] ⟩
  · simp +contextual [ prefixSubtree, rootChildrenFinset ]
    exact fun a ha₁ ha₂ => Nat.le_of_lt_succ a.2
  · grind +splitImp
  · intro x hx
    use ⟨ x.val, by aesop ⟩
    unfold rootChildrenFinset at hx; aesop

/-
Root children have positive val.
-/
lemma rootChild_val_pos (T : OrderedRootedTree t) (x : Fin (t + 1))
    (hx : x ∈ rootChildrenFinset T) : 0 < x.val := by
  exact Nat.pos_of_ne_zero ( by rintro h; simp_all +decide [ rootChildrenFinset ] )

/-
m distinct positive integers ≤ n implies m ≤ n.
-/
lemma rootChildren_card_le_max (T : OrderedRootedTree t)
    (x_max : Fin (t + 1)) (_hx_max : x_max ∈ rootChildrenFinset T)
    (hmax : ∀ x ∈ rootChildrenFinset T, x ≤ x_max) :
    (rootChildrenFinset T).card ≤ x_max.val := by
  have h_card_le :
      (rootChildrenFinset T).card ≤
        Finset.card
          (Finset.image (fun x : Fin (t + 1) => x.val - 1) (rootChildrenFinset T)) := by
    rw [ Finset.card_image_of_injOn ]
    exact fun x hx y hy hxy => Fin.ext <| by
      linarith [
        Nat.sub_add_cancel <| show 1 ≤ ( x : ℕ ) from rootChild_val_pos T x hx,
        Nat.sub_add_cancel <| show 1 ≤ ( y : ℕ ) from rootChild_val_pos T y hy ]
  exact h_card_le.trans
    ( le_trans
      ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx =>
        Finset.mem_Ico.mpr
          ⟨ Nat.zero_le _,
            Nat.lt_of_lt_of_le
              ( Nat.sub_lt ( rootChild_val_pos T x hx ) zero_lt_one )
              ( hmax x hx ) ⟩ )
      <| by simp )

theorem sum_rootChildren_le_iterBound {k C : ℕ}
    (boundK : ℕ → ℕ)
    (hBoundK : ∀ (C' : ℕ) (t' : ℕ) (T' : OrderedRootedTree t'),
      IsKCLayeredTree k C' T' → t' + 1 ≤ boundK C')
    (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T) :
    ∑ x ∈ rootChildrenFinset T, 2 ^ (C + x.val) ≤
    iterBoundFn C boundK (T.numChildren ⟨0, Nat.zero_lt_succ t⟩) := by
  revert T
  induction t using Nat.strong_induction_on generalizing k C
  rename_i t ih
  intros T hT
  by_cases hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ = 0
  · rw [ show rootChildrenFinset T = ∅ from _ ]
    · aesop
    · exact Finset.eq_empty_of_forall_notMem fun x hx => hm.not_gt <| Finset.card_pos.mpr ⟨ x, hx ⟩
  · obtain ⟨x_max, hx_max⟩ :
        ∃ x_max ∈ rootChildrenFinset T, ∀ x ∈ rootChildrenFinset T, x ≤ x_max := by
      have h_nonempty : rootChildrenFinset T ≠ ∅ := by
        exact Finset.Nonempty.ne_empty <| Finset.card_pos.mp <| by
          simpa [ rootChildrenFinset_card ] using Nat.pos_of_ne_zero hm
      exact
        ⟨ Finset.max' _ <| Finset.nonempty_of_ne_empty h_nonempty,
          Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
    -- Let $s = x_max.val - 1$ and $P = \text{prefixSubtree } T s$.
    set s := x_max.val - 1
    set P := prefixSubtree T s (by
    exact Nat.sub_le_of_le_add <| by linarith [ Fin.is_lt x_max ] ;)
    generalize_proofs at *
    -- Use the induction hypothesis on the prefix tree.
    have h_ind :
        ∑ x ∈ rootChildrenFinset P, 2 ^ (C + x.val) ≤
          iterBoundFn C boundK (P.numChildren ⟨0, Nat.zero_lt_succ s⟩) := by
      apply
        ih s (by
          exact lt_of_lt_of_le
            ( Nat.pred_lt ( ne_bot_of_gt ( rootChild_val_pos T x_max hx_max.1 ) ) )
            ( Nat.le_of_lt_succ ( Fin.is_lt x_max ) )) hBoundK P (by
          exact prefixSubtree_layered T hT s ‹_›)
    -- Split off the maximal root child from the sum.
    have h_sum_split :
        ∑ x ∈ rootChildrenFinset T, 2 ^ (C + x.val) =
          ∑ x ∈ rootChildrenFinset P, 2 ^ (C + x.val) + 2 ^ (C + x_max.val) := by
      have h_sum_split :
          ∑ x ∈ rootChildrenFinset T, 2 ^ (C + x.val) =
            ∑ x ∈ (rootChildrenFinset T).filter (fun x => x.val ≤ s),
                2 ^ (C + x.val) +
              2 ^ (C + x_max.val) := by
        rw [ ← Finset.sum_erase_add _ _ hx_max.1, add_comm ]
        rw [ add_comm, Finset.sum_filter ]
        rw [ ← Finset.sum_erase_add _ _ hx_max.1 ]
        rw [ Finset.sum_congr rfl fun x hx => if_pos <| ?_, if_neg <| ?_ ]
        · norm_num
        · exact Nat.not_le_of_gt
            ( Nat.pred_lt ( ne_bot_of_gt ( rootChild_val_pos T x_max hx_max.1 ) ) )
        · grind +splitIndPred
      convert h_sum_split using 2
      convert prefix_rootChildren_sum_eq T s ‹_› _ using 1
      any_goals exact fun x => 2 ^ ( C + x )
      · rfl
      · convert rfl
    -- The prefix has one fewer root child than T.
    have h_numChildren_P :
        P.numChildren ⟨0, Nat.zero_lt_succ s⟩ =
          T.numChildren ⟨0, Nat.zero_lt_succ t⟩ - 1 := by
      rw [ prefix_numChildren_root_eq ]
      rw [
        show
          ( Finset.filter ( fun x : Fin ( t + 1 ) => ( x : ℕ ) ≤ s )
            ( rootChildrenFinset T ) ) =
            rootChildrenFinset T \ { x_max } from ?_,
        Finset.card_sdiff ] <;> norm_num [ hx_max ]
      · exact congr_arg₂ _ ( rootChildrenFinset_card T ) rfl
      · ext x; simp
        intro hx; rw [ le_tsub_iff_right ] <;> norm_num [ Fin.ext_iff ]
        · exact
            ⟨ fun h => ne_of_lt h,
              fun h => lt_of_le_of_ne ( hx_max.2 x hx )
                ( by simpa [ Fin.ext_iff ] using h ) ⟩
        · exact Nat.pos_of_ne_zero fun h => by have := rootChild_val_pos T x_max hx_max.1; aesop
    have h_pos_bound :
        x_max.val ≤
          boundK
            (2 ^ C + C +
              iterBoundFn C boundK (T.numChildren ⟨0, Nat.zero_lt_succ t⟩ - 1)) +
            (T.numChildren ⟨0, Nat.zero_lt_succ t⟩ - 1) := by
      have h_pos_bound :
          x_max.val ≤
            boundK
              (2 ^ C + C +
                iterBoundFn C boundK (T.numChildren ⟨0, Nat.zero_lt_succ t⟩ - 1)) +
              (T.numChildren ⟨0, Nat.zero_lt_succ t⟩ - 1) := by
        have h_contraction :
            IsKCLayeredTree k
              (2 ^ C + C +
                iterBoundFn C boundK (T.numChildren ⟨0, Nat.zero_lt_succ t⟩ - 1))
              (contractionTree P (by
                have h_card_le_s : (rootChildrenFinset T).card ≤ x_max.val := by
                  apply rootChildren_card_le_max T x_max hx_max.left hx_max.right
                rw [ rootChildrenFinset_card ] at h_card_le_s
                omega)) := by
          all_goals generalize_proofs at *
          convert prefix_contraction_layered T hT s ‹_› ‹_› _ _ using 1
          aesop
        have := hBoundK _ _ _ h_contraction
        omega
      generalize_proofs at *
      exact h_pos_bound
    rw [
      show T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ =
          T.numChildren ⟨ 0, Nat.zero_lt_succ t ⟩ - 1 + 1 from by
        rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hm ) ] ]
    simp_all +decide [ iterBoundFn_succ ]
    exact add_le_add h_ind ( pow_le_pow_right₀ ( by decide ) ( by linarith ) )

/-
Monotonicity of iterBoundFn.
-/
lemma iterBoundFn_mono (C : ℕ) (boundK : ℕ → ℕ) : Monotone (iterBoundFn C boundK) := by
  refine monotone_nat_of_le_succ ?_
  exact fun n => Nat.le_add_right _ _

/-! ## Final bound -/

/-- **Super-root degree bound**: The degree of vertex 0 in the contraction tree
    is at most 2^C' where C' = 2^C + C + iterBoundFn(2^C). -/
theorem contractionTree_root_degree_bound {k C : ℕ}
    (boundK : ℕ → ℕ)
    (hBoundK : ∀ (C' : ℕ) (t' : ℕ) (T' : OrderedRootedTree t'),
      IsKCLayeredTree k C' T' → t' + 1 ≤ boundK C')
    (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T)
    (hm : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t) :
    (contractionTree T hm).degree ⟨0, by omega⟩ ≤
    2 ^ (2 ^ C + C + iterBoundFn C boundK (2 ^ C)) := by
  have h_root_le := root_children_le' T ⟨hT.1, hT.2⟩
  have hm_le := contraction_root_degree_le_sum T hT hm
  have h_iter := sum_rootChildren_le_iterBound boundK hBoundK T hT
  have h_mono := iterBoundFn_mono C boundK h_root_le
  have h_pow := Nat.le_two_pow_self (2 ^ C + C + iterBoundFn C boundK (2 ^ C))
  calc (contractionTree T hm).degree ⟨0, by omega⟩
      ≤ ∑ x ∈ rootChildrenFinset T, 2 ^ (C + x.val) := hm_le
    _ ≤ iterBoundFn C boundK (T.numChildren ⟨0, Nat.zero_lt_succ t⟩) := h_iter
    _ ≤ iterBoundFn C boundK (2 ^ C) := h_mono
    _ ≤ 2 ^ C + C + iterBoundFn C boundK (2 ^ C) := by omega
    _ ≤ 2 ^ (2 ^ C + C + iterBoundFn C boundK (2 ^ C)) := h_pow

end

/-! ========== LayeredTreeGeneral.lean ========== -/

/-!
# General Layered Tree Bound (Lemma 2.2)

For any k and C, there exists N₀ such that every (k,C)-layered tree has at most N₀ vertices.
-/

noncomputable section

/-- A (k, C)-layered tree is also (k, C')-layered for C' ≥ C. -/
lemma IsKCLayeredTree.mono_C {k C C' : ℕ} {t : ℕ} {T : OrderedRootedTree t}
    (hT : IsKCLayeredTree k C T) (hCC' : C ≤ C') : IsKCLayeredTree k C' T :=
  ⟨hT.1, fun i => le_trans (hT.2 i) (Nat.pow_le_pow_right (by omega) (by omega))⟩

/-- The root has at most 2^C children in a (k, C)-layered tree. -/
lemma root_children_le {k C t : ℕ} (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree k C T) :
    T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ 2 ^ C :=
  root_children_le' T hT

/-- The number of root children is at most t. -/
lemma root_children_le_t {t : ℕ} (T : OrderedRootedTree t) :
    T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t := by
  refine le_trans
    (b := (Finset.univ.erase ⟨0, Nat.zero_lt_succ t⟩ : Finset (Fin (t + 1))).card)
    ?_ ?_
  · unfold OrderedRootedTree.numChildren
    refine Finset.card_le_card ?_
    intro x hx
    simp_all +decide
  · simp

/-- **Full contraction lemma**: Given a (k+1, C)-layered tree T on t+1
    vertices, there exists a (k, C')-layered tree on t - m + 1 vertices
    (m = numChildren of root), where C' depends only on k, C, and boundK. -/
theorem full_contraction {k C : ℕ}
    (boundK : ℕ → ℕ)
    (hBoundK : ∀ (C' : ℕ) (t' : ℕ) (T' : OrderedRootedTree t'),
      IsKCLayeredTree k C' T' → t' + 1 ≤ boundK C')
    (C' : ℕ)
    (hC' : C' = 2 ^ C + C + iterBoundFn C boundK (2 ^ C))
    {t : ℕ} (T : OrderedRootedTree t)
    (hT : IsKCLayeredTree (k + 1) C T) (_ht : t ≥ 1) :
    let m := T.numChildren ⟨0, Nat.zero_lt_succ t⟩
    ∃ (T' : OrderedRootedTree (t - m)),
      IsKCLayeredTree k C' T' := by
  intro m
  have hm_le_t : m ≤ t := root_children_le_t T
  refine ⟨contractionTree T hm_le_t, ?_⟩
  constructor
  · exact contractionTree_depth_le T k C hT hm_le_t
  · intro i
    by_cases hi : i.val > 0
    · have h1 := contractionTree_degree_nonroot T k C hT hm_le_t i hi
      have hC'_ge : C' ≥ C + 2 ^ C := by subst hC'; omega
      exact le_trans h1 (Nat.pow_le_pow_right (by omega) (by omega))
    · push Not at hi
      have hi0 : i.val = 0 := by omega
      rw [show i = ⟨0, by omega⟩ from Fin.ext hi0]
      rw [hC']
      exact contractionTree_root_degree_bound boundK hBoundK T hT hm_le_t

/-- **Lemma 2.2 (General)**: For any k and C, there exists N₀ such that every
    (k,C)-layered tree has at most N₀ vertices. -/
theorem layered_tree_bounded (k C : ℕ) :
    ∃ N₀ : ℕ, ∀ t : ℕ, ∀ T : OrderedRootedTree t,
      IsKCLayeredTree k C T → t + 1 ≤ N₀ := by
  induction k generalizing C with
  | zero => exact ⟨1, layered_tree_bounded_zero C⟩
  | succ k ih =>
    choose boundK hBoundK using ih
    set C' := 2 ^ C + C + iterBoundFn C boundK (2 ^ C)
    use boundK C' + 2 ^ C
    intro t T hT
    by_cases ht : t = 0
    · subst ht; have : 2 ^ C ≥ 1 := Nat.one_le_two_pow; omega
    · have ht1 : t ≥ 1 := by omega
      have hm_le : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ 2 ^ C := root_children_le T hT
      have hm_le_t : T.numChildren ⟨0, Nat.zero_lt_succ t⟩ ≤ t := root_children_le_t T
      obtain ⟨T', hT'⟩ := full_contraction boundK hBoundK C' rfl T hT ht1
      have hT'_bound := hBoundK C' (t - T.numChildren ⟨0, Nat.zero_lt_succ t⟩) T' hT'
      omega

end

/-! ========== HypergraphClique.lean ========== -/

/-!
# On Cliques in Hypergraphs — Main Theorems

Formalization of the main results from "On cliques in hypergraphs" by Jun Gao.

## Main results

* `helly_complete` — **Fact 2.3**: Helly-type property for complete subgraphs.
* `tree_from_many_clique_sizes` — The tree construction from Section 3.
* `main_theorem` — **Theorem 1.1**: The all-k clique-size bound.
* `erdos_problem_775` — The k=3 specialization answering Erdős's question.
-/

noncomputable section

/-! ## Fact 2.3: Helly-type property for complete subgraphs -/

variable {α : Type*} [DecidableEq α]

/-- **Fact 2.3**: Helly-type property for complete subgraphs of k-uniform hypergraphs. -/
theorem helly_complete {k : ℕ} (H : KUniformHypergraph α k)
    (S : Fin (k + 1) → Finset α)
    (h : ∀ i : Fin (k + 1),
      H.IsComplete (Finset.biUnion Finset.univ (fun j => if j = i then ∅ else S j))) :
    H.IsComplete (Finset.biUnion Finset.univ S) := by
  intro e he hek
  by_contra h_contra
  have h_exists_x : ∀ i : Fin (k + 1), ∃ x ∈ e, x ∉ Finset.biUnion (Finset.univ.erase i) S := by
    intro i
    by_contra h_contra_i
    push Not at h_contra_i
    refine h_contra ( h i e ?_ ?_ )
    · intro x hx; specialize h_contra_i x hx; aesop
    · exact hek
  choose f hf using h_exists_x
  have h_distinct : ∀ i j : Fin (k + 1), i ≠ j → f i ≠ f j := by
    grind
  exact absurd ( Finset.card_le_card ( show Finset.image f Finset.univ ⊆ e from
    Finset.image_subset_iff.2 fun i _ => hf i |>.1 ) ) ( by
    rw [ Finset.card_image_of_injective _ fun i j hij =>
      not_imp_not.1 ( h_distinct i j ) hij, Finset.card_fin ]
    simp +decide [ hek ] )

/-! ## Tree construction infrastructure (Section 3) -/

/-- Walk-down helper for finding the parent of a new vertex. -/
def walkDownAux {n : ℕ} (X : ℕ → Finset (Fin n))
    {bound : ℕ}
    (prevState : (j : ℕ) → j < bound → ℕ × Finset (Fin n) × Finset (Fin n))
    (u : ℕ) (hu : u < bound) : ℕ → {v : ℕ // v < bound}
  | 0 => ⟨u, hu⟩
  | fuel + 1 =>
    let Bu := (prevState u hu).2.2
    if h : ∃ (v : ℕ) (hv : v < bound),
        (prevState v hv).1 = u ∧ v ≠ u ∧ X v ∩ Bu = X bound ∩ Bu
    then walkDownAux X prevState h.choose h.choose_spec.choose fuel
    else ⟨u, hu⟩

/-- Full tree state (parent, A-set, B-set) defined by well-founded recursion. -/
def clTreeState {n : ℕ} (X : ℕ → Finset (Fin n)) :
    ℕ → ℕ × Finset (Fin n) × Finset (Fin n) :=
  WellFounded.fix Nat.lt_wfRel.wf fun i rec =>
    if hi : i = 0 then (0, X 0, Finset.univ \ X 0)
    else
      let p := walkDownAux X rec 0 (by omega) i
      let Ap := (rec p.val p.prop).2.1
      (p.val, Ap ∩ X i, Ap \ (Ap ∩ X i))

def clParent {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) : ℕ := (clTreeState X i).1
def clSetA {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) : Finset (Fin n) := (clTreeState X i).2.1
def clSetB {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) : Finset (Fin n) := (clTreeState X i).2.2

/-! ### Basic properties of the tree construction -/

lemma clParent_zero {n : ℕ} (X : ℕ → Finset (Fin n)) : clParent X 0 = 0 := by
  unfold clParent clTreeState; rw [WellFounded.fix_eq]; simp

lemma clParent_lt {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) (hi : 0 < i) :
    clParent X i < i := by
  unfold clParent clTreeState; rw [WellFounded.fix_eq]
  split
  · omega
  · exact (walkDownAux X _ 0 _ i).prop

lemma clSetB_sub_compl {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) :
    clSetB X i ⊆ (Finset.univ : Finset (Fin n)) \ X i := by
  unfold clSetB clTreeState; rw [WellFounded.fix_eq]
  split
  next h => subst h; rfl
  next h =>
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hx
    exact fun hxi => hx.2 ⟨hx.1, hxi⟩

lemma clSetB_card_le {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) :
    (clSetB X i).card ≤ n - (X i).card := by
  calc (clSetB X i).card
      ≤ ((Finset.univ : Finset (Fin n)) \ X i).card :=
        Finset.card_le_card (clSetB_sub_compl X i)
    _ = n - (X i).card := by rw [Finset.card_sdiff]; simp

/-! ### Helper: lower bound for order isomorphism values -/

/-- Strictly increasing f : Fin m → ℕ satisfies f(i) ≥ i. -/
lemma orderIso_val_ge (s : Finset ℕ) (m : ℕ) (hs : s.card = m) (i : Fin m) :
    (Finset.orderIsoOfFin s hs i : ℕ) ≥ i.val := by
  have hm := (Finset.orderIsoOfFin s hs).strictMono
  suffices h : ∀ (j : ℕ) (hj : j < m),
      (Finset.orderIsoOfFin s hs ⟨j, hj⟩ : ℕ) ≥ j from h i.val i.isLt
  intro j hj
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have h1 := ih (by omega : j < m)
    have h2 : (Finset.orderIsoOfFin s hs ⟨j, by omega⟩ : ℕ) <
              (Finset.orderIsoOfFin s hs ⟨j + 1, hj⟩ : ℕ) :=
      hm (by simp [Fin.lt_def])
    omega

/-! ### Construction of the OrderedRootedTree from cliques -/

/-- Build an OrderedRootedTree on t+1 vertices from the walk-down parent function. -/
def clTree {n : ℕ} (X : ℕ → Finset (Fin n)) (t : ℕ) : OrderedRootedTree t where
  parent := fun i =>
    ⟨clParent X i.val, by
      rcases Nat.eq_zero_or_pos i.val with hi | hi
      · simp [hi, clParent_zero]
      · exact Nat.lt_of_lt_of_le (clParent_lt X i.val hi) (by omega)⟩
  root_self := by
    ext; simp [clParent_zero]
  parent_lt := by
    intro i hi
    simp only []
    exact clParent_lt X i.val hi

/-! ### Walk-down stopping condition -/

/-- walkDownAux visits strictly increasing vertices: result ≥ start. -/
lemma walkDownAux_ge {n bound : ℕ} (X : ℕ → Finset (Fin n))
    (rec : (j : ℕ) → j < bound → ℕ × Finset (Fin n) × Finset (Fin n))
    (h_parent_le : ∀ (v : ℕ) (hv : v < bound), (rec v hv).1 ≤ v)
    (u : ℕ) (hu : u < bound) (fuel : ℕ) :
    u ≤ (walkDownAux X rec u hu fuel).val := by
  induction fuel generalizing u hu
  · exact le_rfl
  · rename_i fuel ih
    unfold walkDownAux
    dsimp only
    split
    · rename_i h
      let v := Classical.choose h
      let hv := Classical.choose (Classical.choose_spec h)
      have hv_spec := Classical.choose_spec (Classical.choose_spec h)
      change u ≤ (walkDownAux X rec v hv fuel).val
      have hu_le_v : u ≤ v := by
        rw [← hv_spec.1]
        exact h_parent_le v hv
      have hu_ne_v : u ≠ v := Ne.symm hv_spec.2.1
      exact le_trans (lt_of_le_of_ne hu_le_v hu_ne_v).le (ih v hv)
    · exact le_rfl

/-- With sufficient fuel (≥ bound − u), walkDownAux terminates at p where
    no child of p has matching B-encoding. -/
lemma walkDownAux_stopping {n bound : ℕ} (X : ℕ → Finset (Fin n))
    (rec : (j : ℕ) → j < bound → ℕ × Finset (Fin n) × Finset (Fin n))
    (h_parent_le : ∀ (v : ℕ) (hv : v < bound), (rec v hv).1 ≤ v)
    (u : ℕ) (hu : u < bound) (fuel : ℕ) (h_fuel : fuel ≥ bound - u) :
    let p := walkDownAux X rec u hu fuel
    ¬∃ (v : ℕ) (hv : v < bound),
      (rec v hv).1 = p.val ∧ v ≠ p.val ∧
      X v ∩ (rec p.val p.prop).2.2 = X bound ∩ (rec p.val p.prop).2.2 := by
  induction fuel generalizing u hu <;>
    simp +decide [*, walkDownAux] at *
  · omega
  · rename_i fuel fuel_ih
    split_ifs
    · grind
    · grind

/-- The walk-down stopping condition for clParent: when clParent X i = p,
    no existing child of p has the same B-encoding as vertex i. -/
lemma clParent_stopping {n : ℕ} (X : ℕ → Finset (Fin n))
    (i : ℕ) (hi : 0 < i) :
    ∀ v, v < i → clParent X v = clParent X i → v ≠ clParent X i →
    X v ∩ clSetB X (clParent X i) ≠ X i ∩ clSetB X (clParent X i) := by
  intro v hv h_eq h_neq h_inter_eq
  have h_walk_down : clParent X i =
      (walkDownAux X (fun j hj => clTreeState X j) 0 (by omega) i).val := by
    unfold clParent clTreeState; rw [WellFounded.fix_eq]; grind
  convert walkDownAux_stopping X (fun j hj => clTreeState X j) _ 0
    (by omega) i (by omega) _ using 1
  · intro v hv
    by_cases hv_zero : v = 0
    · subst v
      have h0 : (clTreeState X 0).1 = 0 := by
        simpa [clTreeState, clParent] using clParent_zero X
      omega
    · simpa [clParent] using
        Nat.le_of_lt (clParent_lt X v (Nat.pos_of_ne_zero hv_zero))
  · unfold clParent at *; aesop

/-! ### Key structural lemmas for the walk-down tree -/

/-- Children of vertex i in the walk-down tree have distinct B-encodings. -/
lemma walkdown_children_distinct_encoding {n : ℕ} (X : ℕ → Finset (Fin n))
    (t : ℕ) (i j₁ j₂ : Fin (t + 1))
    (hj₁_par : (clTree X t).parent j₁ = i) (hj₁_ne : j₁ ≠ i)
    (hj₂_par : (clTree X t).parent j₂ = i) (hj₂_ne : j₂ ≠ i)
    (hj₁j₂ : j₁ ≠ j₂) :
    X j₁.val ∩ clSetB X i.val ≠ X j₂.val ∩ clSetB X i.val := by
  unfold clTree at *
  cases lt_or_gt_of_ne (Fin.val_injective.ne hj₁j₂) <;> simp_all +decide [Fin.ext_iff]
  · have := clParent_stopping X j₂ (by exact Nat.pos_of_ne_zero (by aesop)) j₁
      (by assumption)
    aesop
  · have := clParent_stopping X j₁
      (by linarith [show (j₂ : ℕ) < j₁ from by assumption]) j₂
      (by linarith [show (j₂ : ℕ) < j₁ from by assumption])
    aesop

/-- The number of children of vertex i is at most 2^|B(i)| − 1. -/
lemma walkdown_numChildren_le {n : ℕ} (X : ℕ → Finset (Fin n))
    (t : ℕ) (i : Fin (t + 1))
    (h_distinct : ∀ j₁ j₂ : Fin (t + 1),
      (clTree X t).parent j₁ = i → j₁ ≠ i →
      (clTree X t).parent j₂ = i → j₂ ≠ i → j₁ ≠ j₂ →
      X j₁.val ∩ clSetB X i.val ≠ X j₂.val ∩ clSetB X i.val)
    (h_nonempty : ∀ j : Fin (t + 1),
      (clTree X t).parent j = i → j ≠ i →
      (X j.val ∩ clSetB X i.val).Nonempty) :
    (clTree X t).numChildren i ≤ 2 ^ (clSetB X i.val).card - 1 := by
  have h_children_subset :
      Finset.image (fun j : Fin (t + 1) => X j.val ∩ clSetB X i.val)
        (Finset.univ.filter (fun j : Fin (t + 1) =>
          (clTree X t).parent j = i ∧ j ≠ i)) ⊆
      Finset.powerset (clSetB X i.val) \ {∅} := by grind
  have := Finset.card_mono h_children_subset
  rw [Finset.card_image_of_injOn] at this
  · change
      (Finset.univ.filter (fun j : Fin (t + 1) =>
        (clTree X t).parent j = i ∧ j ≠ i)).card ≤
        2 ^ (clSetB X i.val).card - 1
    simpa [Finset.card_sdiff] using this
  · exact fun x hx y hy hxy =>
      Classical.not_not.1 fun h =>
        h_distinct x y (by aesop) (by aesop) (by aesop) (by aesop) h hxy

/-! ### Basic A-set / B-set identities -/

lemma clSetA_zero {n : ℕ} (X : ℕ → Finset (Fin n)) : clSetA X 0 = X 0 := by
  unfold clSetA clTreeState; rw [WellFounded.fix_eq]; simp

lemma clSetB_zero {n : ℕ} (X : ℕ → Finset (Fin n)) :
    clSetB X 0 = Finset.univ \ X 0 := by
  unfold clSetB clTreeState; rw [WellFounded.fix_eq]; simp

lemma clSetA_pos {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) (hi : 0 < i) :
    clSetA X i = clSetA X (clParent X i) ∩ X i := by
  rw [ clSetA, clParent ]
  rw [ clTreeState ]
  rw [ WellFounded.fix_eq ]
  split_ifs
  · simp_all +decide
  · rfl

lemma clSetB_pos {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) (hi : 0 < i) :
    clSetB X i = clSetA X (clParent X i) \ (clSetA X (clParent X i) ∩ X i) := by
  rw [ clSetB, clSetA, clParent ]
  rw [ clTreeState ]
  grind +suggestions

lemma clSetA_sub_X {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) :
    clSetA X i ⊆ X i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [clSetA_zero]
  · rw [clSetA_pos X i hi]; exact Finset.inter_subset_right

lemma clSetA_union_clSetB {n : ℕ} (X : ℕ → Finset (Fin n)) (i : ℕ) (hi : 0 < i) :
    clSetA X i ∪ clSetB X i = clSetA X (clParent X i) := by
  rw [clSetA_pos X i hi, clSetB_pos X i hi]
  ext x; simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto

/-! ### Walk-down matching infrastructure -/

/-
**Walk-down matching at result's parent**: If walkDownAux from u returns i > u,
    then the matching condition holds at parent(i):
    X(i) ∩ B(parent(i)) = X(bound) ∩ B(parent(i)).
    This is because the last step of the walk was from parent(i) to i.
-/
lemma walkDownAux_matching_at_result_parent {n bound : ℕ} (X : ℕ → Finset (Fin n))
    (rec : (j : ℕ) → j < bound → ℕ × Finset (Fin n) × Finset (Fin n))
    (h_parent_le : ∀ (v : ℕ) (hv : v < bound), (rec v hv).1 ≤ v)
    (u : ℕ) (hu : u < bound) (fuel : ℕ)
    (h_result_gt : u < (walkDownAux X rec u hu fuel).val) :
    let r := walkDownAux X rec u hu fuel
    X r.val ∩ (rec ((rec r.val r.prop).1)
      (lt_of_le_of_lt (h_parent_le r.val r.prop) r.prop)).2.2 =
    X bound ∩ (rec ((rec r.val r.prop).1)
      (lt_of_le_of_lt (h_parent_le r.val r.prop) r.prop)).2.2 := by
  induction fuel generalizing u hu <;> simp +decide [ *, walkDownAux ] at *
  rename_i fuel fuel_ih
  split_ifs at * <;> norm_num at *
  have := ‹
    ∃ v, ( ∃ hv, ( rec v hv ).1 = u ) ∧ ¬v = u ∧
      X v ∩ ( rec u hu ).2.2 = X bound ∩ ( rec u hu ).2.2
  ›.choose_spec.1
  obtain ⟨ hv₁, hv₂ ⟩ := this
  have := walkDownAux_ge X rec ( fun v hv => h_parent_le v hv ) _ hv₁ fuel
  grind

/-
**Matching at grandparent**: When parent(j) = i > 0,
    X(j) ∩ B(parent(i)) = X(i) ∩ B(parent(i)).
    Follows from the walk-down for j passing through parent(i) on the way to i.
-/
lemma walkdown_B_matching_at_parent {n : ℕ} (X : ℕ → Finset (Fin n))
    (i j : ℕ) (hj : 0 < j) (hi : 0 < i) (hi_lt_j : i < j)
    (hpar_j : clParent X j = i) :
    X j ∩ clSetB X (clParent X i) = X i ∩ clSetB X (clParent X i) := by
  have h_walkDownAux :
      clParent X j =
        (walkDownAux X (fun j' hj' => clTreeState X j') 0
          (by omega : 0 < j) j).val := by
    unfold clParent clTreeState
    rw [ WellFounded.fix_eq ] ; aesop
  -- Apply the walkDownAux_matching_at_result_parent lemma with bound := i.
  have h_walkDownAux_matching :
      X i ∩ (clTreeState X ((clTreeState X i).1)).2.2 =
        X j ∩ (clTreeState X ((clTreeState X i).1)).2.2 := by
    rw [ ← hpar_j, h_walkDownAux ]
    apply walkDownAux_matching_at_result_parent
    · intro v hv; exact (by
      by_cases hv_zero : v = 0
      · subst v
        have h0 : (clTreeState X 0).1 = 0 := by
          simpa [clParent] using clParent_zero X
        omega
      · exact Nat.le_of_lt ( clParent_lt X v ( Nat.pos_of_ne_zero hv_zero ) ))
    · linarith
  exact h_walkDownAux_matching.symm

/-! ### Ancestor chain monotonicity -/

lemma clParent_le {n : ℕ} (X : ℕ → Finset (Fin n)) (v : ℕ) : clParent X v ≤ v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [clParent_zero]
  · exact Nat.le_of_lt (clParent_lt X v hv)

lemma clParent_iterate_le {n : ℕ} (X : ℕ → Finset (Fin n)) (r d : ℕ) :
    (clParent X)^[d] r ≤ r := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc (clParent X)^[d.succ] r
        = clParent X ((clParent X)^[d] r) := Function.iterate_succ_apply' _ _ _
      _ ≤ (clParent X)^[d] r := clParent_le X _
      _ ≤ r := ih

lemma clParent_iterate_lt' {n : ℕ} (X : ℕ → Finset (Fin n)) (r d : ℕ)
    (hd : 0 < (clParent X)^[d] r) :
    (clParent X)^[d + 1] r < (clParent X)^[d] r := by
  change (clParent X)^[d.succ] r < _
  rw [Function.iterate_succ_apply']
  exact clParent_lt X _ hd

lemma clParent_iterate_strict_anti {n : ℕ} (X : ℕ → Finset (Fin n)) (r : ℕ)
    {d₁ d₂ : ℕ} (h : d₁ < d₂) (hd : 0 < (clParent X)^[d₁] r) :
    (clParent X)^[d₂] r < (clParent X)^[d₁] r := by
  -- By induction on $d₂ - d₁$, the iterated parent strictly decreases.
  have h_ind :
      ∀ d₁ d₂, d₁ < d₂ → 0 < (clParent X)^[d₁] r →
        (clParent X)^[d₂] r < (clParent X)^[d₁] r := by
    intros d₁ d₂ h_lt h_pos
    induction h_lt
    · simpa only [ Function.iterate_succ_apply' ] using clParent_iterate_lt' X r d₁ h_pos
    · rename_i d₂ h_lt ih
      rw [ Function.iterate_succ_apply' ]
      exact lt_of_le_of_lt ( clParent_le _ _ ) ih
  exact h_ind d₁ d₂ h hd

lemma clParent_iterate_injective {n : ℕ} (X : ℕ → Finset (Fin n)) (r : ℕ)
    {d₁ d₂ : ℕ} (h : (clParent X)^[d₁] r = (clParent X)^[d₂] r)
    (h_pos : 0 < (clParent X)^[d₁] r) :
    d₁ = d₂ := by
  by_contra h_contra
  cases lt_or_gt_of_ne h_contra <;> simp_all +decide
  · exact absurd h ( ne_of_gt ( clParent_iterate_strict_anti X r ‹_› ( by linarith ) ) )
  · exact absurd h ( ne_of_lt ( clParent_iterate_strict_anti X r ‹_› h_pos ) )

/-! ### Walk-down descendant property -/

/-
walkDownAux from u returns a descendant of u: u appears as an iterated parent
    of the result. Proof by induction on fuel.
-/
set_option linter.unusedVariables false in
lemma walkDownAux_result_descendant {n : ℕ} (X : ℕ → Finset (Fin n))
    (b : ℕ) (u : ℕ) (hu : u < b) (fuel : ℕ) :
    ∃ d : ℕ, (clParent X)^[d]
      (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val = u := by
  induction fuel generalizing u hu
  · exact ⟨ 0, rfl ⟩
  · rename_i fuel ih
    by_cases h : ∃ (v : ℕ) (hv : v < b),
      (clTreeState X v).fst = u ∧ v ≠ u ∧
      X v ∩ (clTreeState X u).snd.snd = X b ∩ (clTreeState X u).snd.snd
    · unfold walkDownAux
      obtain ⟨ d, hd ⟩ := ih _ ( h.choose_spec.choose )
      use d + 1
      simp_all +decide [ Function.iterate_succ_apply' ]
      split_ifs <;> simp_all +decide [ clParent ]
      · grind +splitIndPred
      · exact False.elim <| ‹
          ∀ x, ( clTreeState X x ).1 = u → ¬x = u → x < b →
            ¬X x ∩ ( clTreeState X u ).2.2 = X b ∩ ( clTreeState X u ).2.2
        › _ h.choose_spec.choose_spec.1
          h.choose_spec.choose_spec.2.1
          h.choose_spec.choose
          h.choose_spec.choose_spec.2.2
    · use 0; simp [walkDownAux]
      grind

/-
Ancestor chain squeeze: if position d₀+1 has value u, and position d+1 has value
    strictly between u and position d₀, then d = d₀.
-/
lemma ancestor_chain_squeeze {n : ℕ} (X : ℕ → Finset (Fin n))
    (r u : ℕ) {d d₀ : ℕ}
    (hd₀ : (clParent X)^[d₀ + 1] r = u)
    (h_lt : (clParent X)^[d + 1] r < (clParent X)^[d₀] r)
    (h_ge : u ≤ (clParent X)^[d + 1] r)
    (hd_pos : 0 < (clParent X)^[d] r) :
    d = d₀ := by
  -- By contradiction, assume $d \ne d₀$.
  by_contra h_neq
  cases lt_or_gt_of_ne h_neq <;> simp_all +decide [ Function.iterate_succ_apply' ]
  · contrapose! h_lt
    rw [ ← Nat.sub_add_cancel ( by linarith : d + 1 ≤ d₀ ), Function.iterate_add_apply ]
    induction ( d₀ - ( d + 1 ) ) <;> simp_all +decide [ Function.iterate_succ_apply' ]
    rename_i k hk
    exact le_trans ( clParent_le _ _ ) hk
  · -- Since $d > d₀$, we have $(clParent X)^[d] r \leq (clParent X)^[d₀+1] r$.
    have h_le : (clParent X)^[d] r ≤ (clParent X)^[d₀ + 1] r := by
      exact Nat.le_induction ( by aesop )
        ( fun k hk ih => by
          simpa only [ Function.iterate_succ_apply' ] using
            le_trans ( clParent_le _ _ ) ih )
        _ ( show d₀ + 1 ≤ d from by linarith )
    simp_all +decide [ Function.iterate_succ_apply' ]
    linarith [
      show clParent X ( ( clParent X ) ^[ d ] r ) <
          ( clParent X ) ^[ d ] r from
        clParent_lt X _ hd_pos ]

/-
**All-ancestors matching for walkDownAux**: at each ancestor of the walk result
    within the walk's range, the intermediate matching holds.
    Proof by induction on fuel.
-/
set_option linter.unusedVariables false in
lemma walkDownAux_ancestors_matching {n : ℕ} (X : ℕ → Finset (Fin n))
    (b : ℕ) (u : ℕ) (hu : u < b) (fuel : ℕ)
    (h_gt : u < (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val)
    (d : ℕ)
    (hd_pos : 0 < (clParent X)^[d]
      (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val)
    (hu_anc : u ≤ (clParent X)^[d + 1]
      (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val) :
    X ((clParent X)^[d]
        (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val) ∩
      clSetB X ((clParent X)^[d + 1]
        (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val) =
    X b ∩ clSetB X ((clParent X)^[d + 1]
        (walkDownAux X (fun j hj => clTreeState X j) u hu fuel).val) := by
  revert h_gt
  revert d hd_pos hu_anc
  induction fuel generalizing u hu
  · simp +decide [ walkDownAux ]
  · rename_i fuel ih
    intro d hd_pos hd_anc hd_gt
    rw [walkDownAux] at *
    split_ifs at *
    · have := ‹
        ∃ v, ∃ hv : v < b, ( clTreeState X v ).1 = u ∧ v ≠ u ∧
          X v ∩ ( clTreeState X u ).2.2 = X b ∩ ( clTreeState X u ).2.2
      ›.choose_spec.choose_spec
      by_cases h_case :
          (‹
            ∃ v, ∃ hv : v < b, ( clTreeState X v ).1 = u ∧ v ≠ u ∧
              X v ∩ ( clTreeState X u ).2.2 =
                X b ∩ ( clTreeState X u ).2.2
          ›.choose : ℕ) ≤
            (clParent X)^[d + 1]
              (walkDownAux X (fun j hj => clTreeState X j)
                ‹
                  ∃ v, ∃ hv : v < b, ( clTreeState X v ).1 = u ∧ v ≠ u ∧
                    X v ∩ ( clTreeState X u ).2.2 =
                      X b ∩ ( clTreeState X u ).2.2
                ›.choose
                ‹
                  ∃ v, ∃ hv : v < b, ( clTreeState X v ).1 = u ∧ v ≠ u ∧
                    X v ∩ ( clTreeState X u ).2.2 =
                      X b ∩ ( clTreeState X u ).2.2
                ›.choose_spec.choose fuel).val
      · rename_i h
        simp_all
        obtain ⟨w, h⟩ := h
        obtain ⟨w_1, h⟩ := h
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        obtain ⟨left_2, right_1⟩ := this
        obtain ⟨left_3, right_1⟩ := right_1
        subst left
        apply ih
        · exact hd_pos
        · exact h_case
        · exact lt_of_le_of_lt h_case (by
            rw [← Function.iterate_succ_apply]
            exact lt_of_lt_of_le (clParent_iterate_lt' X _ d hd_pos) (clParent_iterate_le X _ d))
      · have := walkDownAux_result_descendant X b
          ‹
            ∃ v, ∃ hv : v < b, ( clTreeState X v ).1 = u ∧ v ≠ u ∧
              X v ∩ ( clTreeState X u ).2.2 =
                X b ∩ ( clTreeState X u ).2.2
          ›.choose
          ‹
            ∃ v, ∃ hv : v < b, ( clTreeState X v ).1 = u ∧ v ≠ u ∧
              X v ∩ ( clTreeState X u ).2.2 =
                X b ∩ ( clTreeState X u ).2.2
          ›.choose_spec.choose fuel
        obtain ⟨ d₀, hd₀ ⟩ := this
        have := ancestor_chain_squeeze X _ _
          ( show
              ( clParent X )^[d₀ + 1]
                ( walkDownAux X ( fun j hj => clTreeState X j ) _ _ fuel ).val =
                u from ?_ )
          ?_ ?_ hd_pos
        · simp_all +decide [ Function.iterate_succ_apply' ]
          convert ‹
            ( clTreeState X _ ).1 = u ∧ ¬_ ∧
              X _ ∩ ( clTreeState X u ).2.2 = X b ∩ ( clTreeState X u ).2.2
          ›.2.2 using 1
          · congr! 2
            exact congr_arg ( fun x => ( clTreeState X x ).2.2 ) ( by tauto )
          · congr! 2
            exact congr_arg ( fun x => ( clTreeState X x ).2.2 ) ( by tauto )
        · simp_all +decide [ Function.iterate_succ_apply' ]
          exact this.1
        · grind
        · exact hd_anc
    · exact False.elim <| hd_gt.ne rfl

/-
Intermediate matching: for b > 0 with r = clParent X b > 0, at each ancestor of r,
    the matching holds. This connects walkDownAux_ancestors_matching to clParent.
-/
lemma walkdown_intermediate_matching {n : ℕ} (X : ℕ → Finset (Fin n))
    (b : ℕ) (hb : 0 < b) (d : ℕ)
    (hd : 0 < (clParent X)^[d] (clParent X b)) :
    X ((clParent X)^[d] (clParent X b)) ∩
        clSetB X ((clParent X)^[d + 1] (clParent X b)) =
      X b ∩ clSetB X ((clParent X)^[d + 1] (clParent X b)) := by
  nontriviality
  revert b
  intro b hb hd_pos
  have h_walkDownAux :
      (walkDownAux X (fun j hj => clTreeState X j) 0 (by omega : 0 < b) b).val =
        clParent X b := by
    unfold clParent clTreeState
    rw [ WellFounded.fix_eq ] ; aesop
  by_cases h :
      0 < (walkDownAux X (fun j hj => clTreeState X j) 0 hb b).val <;>
    simp_all +decide [ Function.iterate_succ_apply' ]
  · convert walkDownAux_ancestors_matching X b 0 hb b _ d _ _ using 1
    · rw [ h_walkDownAux ]
      rw [ Function.iterate_succ_apply' ]
    · rw [ h_walkDownAux, Function.iterate_succ_apply' ]
    · exact h_walkDownAux.symm ▸ h
    · grind +splitIndPred
    · exact Nat.zero_le _
  · exact absurd hd_pos ( by
      erw [ Function.iterate_fixed ( show clParent X 0 = 0 from clParent_zero X ) ]
      norm_num )

/-
**Matching at all ancestors**: For j with parent(j) = i and any strict ancestor v of i,
    X(j) ∩ B(v) = X(i) ∩ B(v).
    Both walks (for j and i) share the intermediate vertex (clParent X)^[d-1] i
    at level (clParent X)^[d] i, by `walkdown_intermediate_matching`.
-/
lemma walkdown_ancestor_matching {n : ℕ} (X : ℕ → Finset (Fin n))
    (i j : ℕ) (hj : 0 < j) (hi : 0 < i) (hi_lt_j : i < j)
    (hpar_j : clParent X j = i)
    (d : ℕ) (hd : 0 < d) :
    X j ∩ clSetB X ((clParent X)^[d] i) = X i ∩ clSetB X ((clParent X)^[d] i) := by
  induction hd
  · simpa [Function.iterate_succ_apply'] using
      walkdown_B_matching_at_parent X i j hj hi hi_lt_j hpar_j
  · rename_i d hd ih
    by_cases h : 0 < ( clParent X ) ^[ d ] i <;>
      simp_all +decide [ Function.iterate_succ_apply' ]
    · have := walkdown_intermediate_matching X j hj d
      simp_all +decide [ ← Function.iterate_succ_apply' ]
      have := walkdown_intermediate_matching X i hi ( d - 1 )
      rcases d <;> simp_all +decide [ Function.iterate_succ_apply' ]
      simp_all +decide [ ← Function.iterate_succ_apply' ]
    · rw [ clParent_zero ] ; aesop

/-
**Subset when encoding is empty**: If parent(j) = i and X(j) ∩ B(i) = ∅,
    then X(j) ⊆ X(i). Uses matching at all ancestors + the partition of univ
    into A(i) and B-sets along the ancestor chain.
-/
lemma walkdown_empty_encoding_subset {n : ℕ} (X : ℕ → Finset (Fin n))
    (i j : ℕ) (hj : 0 < j) (hi_lt_j : i < j)
    (hpar : clParent X j = i) (hempty : X j ∩ clSetB X i = ∅) :
    X j ⊆ X i := by
  -- Since X j ∩ clSetB X i is empty, x cannot be in clSetB X i.
  intro x hx
  by_cases hxA : x ∈ clSetA X i
  · exact Finset.mem_of_subset ( clSetA_sub_X X i ) hxA
  · -- Use ancestor matching after locating x in one of the B-sets.
    have hwalkdown :
        x ∈ clSetB X i ∨ ∃ d > 0, x ∈ clSetB X ((clParent X)^[d] i) := by
      have h_ind :
          ∀ i, x ∉ clSetA X i →
            x ∈ clSetB X i ∨ ∃ d > 0, x ∈ clSetB X ((clParent X)^[d] i) := by
        intro i hi
        induction i using Nat.strong_induction_on
        rename_i i ih
        by_cases hi0 : 0 < i <;> simp_all +decide [ clSetB_pos ]
        · by_cases hxA : x ∈ clSetA X (clParent X i) <;> simp_all +decide [ clSetA_pos ]
          specialize ih ( clParent X i ) ( clParent_lt X i hi0 ) hxA
          rcases ih with ( ih | ⟨ d, hd, ih ⟩ ) <;>
            [ exact ⟨ 1, by norm_num, ih ⟩
            ; exact ⟨ d + 1, Nat.succ_pos _, ih ⟩ ]
        · simp_all +decide [ clSetA_zero, clSetB_zero ]
      exact h_ind i hxA
    obtain ⟨d, hd_pos, hd⟩ : ∃ d > 0, x ∈ clSetB X ((clParent X)^[d] i) := by
      exact hwalkdown.resolve_left fun h =>
        Finset.notMem_empty x <| hempty ▸ Finset.mem_inter_of_mem hx h
    have hwalkdown : x ∈ X j ∩ clSetB X ((clParent X)^[d] i) := by
      aesop
    by_cases hi_pos : 0 < i
    · exact Finset.mem_of_mem_inter_left
        ((walkdown_ancestor_matching X i j hj hi_pos hi_lt_j hpar d hd_pos) ▸ hwalkdown)
    · exfalso; push Not at hi_pos; have hi0 : i = 0 := by omega
      have h_iter_zero : (clParent X)^[d] 0 = 0 := Function.iterate_fixed (clParent_zero X) d
      rw [hi0] at hempty hd
      rw [h_iter_zero] at hd; rw [clSetB_zero] at hd hempty
      exact absurd (Finset.mem_inter_of_mem hx hd) (hempty ▸ Finset.notMem_empty x)

/-! ### Helper lemmas for the depth-bound pigeonhole argument -/

/-- A-set monotonicity along the parent chain: A(v) ⊆ A(parent(v)) for v > 0. -/
lemma clSetA_mono_parent {n : ℕ} (X : ℕ → Finset (Fin n)) (v : ℕ) (hv : 0 < v) :
    clSetA X v ⊆ clSetA X (clParent X v) := by
  rw [clSetA_pos X v hv]; exact Finset.inter_subset_left

/-
A-set monotonicity along iterated parents: A(y_m) ⊆ A(y_{m+d}).
-/
lemma clSetA_iterate_mono {n : ℕ} (X : ℕ → Finset (Fin n)) (v : ℕ)
    (m₁ m₂ : ℕ) (h : m₁ ≤ m₂)
    (h_pos : ∀ m, m₁ ≤ m → m < m₂ → 0 < (clParent X)^[m] v) :
    clSetA X ((clParent X)^[m₁] v) ⊆ clSetA X ((clParent X)^[m₂] v) := by
  induction h
  · grind
  · rename_i k hk₁ hk₂
    refine Finset.Subset.trans
      ( hk₂ fun m hm₁ hm₂ => h_pos m hm₁ ( Nat.lt_succ_of_lt hm₂ ) ) ?_
    convert clSetA_mono_parent X ( ( clParent X ) ^[ k ] v )
      ( h_pos k hk₁ ( Nat.lt_succ_self k ) ) using 1
    rw [ Function.iterate_succ_apply' ]

/-
Depth implies path positivity: if depth ≥ m+1, then the m-th ancestor is positive.
-/
lemma path_iterate_pos_of_depth {n t : ℕ} (X : ℕ → Finset (Fin n))
    (i : Fin (t + 1)) (m : ℕ) (hm : m + 1 ≤ (clTree X t).depth i) :
    0 < (clParent X)^[m] i.val := by
  contrapose! hm
  induction m generalizing i <;> simp_all +decide [ Function.iterate_succ_apply' ]
  · unfold OrderedRootedTree.depth; aesop
  · rename_i m ih
    rw [ OrderedRootedTree.depth ]
    split_ifs <;> simp_all +decide
    convert ih ⟨ clParent X i.val, _ ⟩ _ using 1
    · apply congrArg (clTree X t).depth
      ext
      rfl
    · rw [← Function.iterate_succ_apply (f := clParent X) (n := m) (x := i.val)]
      rw [Function.iterate_succ_apply' (f := clParent X) (n := m) (x := i.val)]
      exact hm

/-
Chain matching: if x ∈ X(parent(v)) ∩ B(y_s) for s ≥ 2, then x ∈ X(y_r)
    for any r ≤ s-1. Uses walkdown_ancestor_matching at each step.
-/
lemma matching_chain_gives_membership {n : ℕ} (X : ℕ → Finset (Fin n))
    (v : ℕ) (hv : 0 < v) (h_parent_pos : 0 < clParent X v)
    (s : ℕ) (hs : 2 ≤ s)
    (h_path_pos : ∀ m, 1 ≤ m → m ≤ s - 1 → 0 < (clParent X)^[m] v)
    (x : Fin n)
    (hx1 : x ∈ X (clParent X v))
    (hxB : x ∈ clSetB X ((clParent X)^[s] v))
    (r : ℕ) (hr : r ≤ s - 1) :
    x ∈ X ((clParent X)^[r] v) := by
  induction r
  · have h_chain_matching :
        X v ∩ clSetB X ((clParent X)^[s] v) =
          X (clParent X v) ∩ clSetB X ((clParent X)^[s] v) := by
      convert
        walkdown_ancestor_matching X ( clParent X v ) v hv h_parent_pos
          ( by linarith [ clParent_lt X v hv ] ) rfl
          ( s - 1 ) ( Nat.sub_pos_of_lt hs )
        using 1
      · cases s <;> aesop
      · cases s <;> aesop
    replace h_chain_matching := Finset.ext_iff.mp h_chain_matching x; aesop
  · rename_i r ih
    have h_chain_matching_step :
        X ((clParent X)^[r] v) ∩ clSetB X ((clParent X)^[s] v) =
          X ((clParent X)^[r + 1] v) ∩ clSetB X ((clParent X)^[s] v) := by
      have := walkdown_ancestor_matching X
        ( ( clParent X ) ^[ r + 1 ] v ) ( ( clParent X ) ^[ r ] v ) ?_ ?_ ?_ ?_
      · convert this ( s - r - 1 ) ( Nat.sub_pos_of_lt ( by omega ) ) using 1
        · rw [ ← Function.iterate_add_apply, Nat.sub_sub, Nat.sub_add_cancel ( by omega ) ]
        · rw [ ← Function.iterate_add_apply, Nat.sub_sub, Nat.sub_add_cancel ( by omega ) ]
      · exact if hr0 : r = 0 then by
          aesop
        else
          h_path_pos r ( Nat.pos_of_ne_zero hr0 ) ( by linarith )
      · exact h_path_pos _ le_add_self hr
      · convert clParent_lt X _ _ using 1
        · exact Function.iterate_succ_apply' _ _ _
        · exact if hr0 : 1 ≤ r then h_path_pos r hr0 ( by linarith ) else by aesop
      · rw [ Function.iterate_succ_apply' ]
    exact Finset.mem_of_mem_inter_left
      ( h_chain_matching_step ▸
        Finset.mem_inter_of_mem ( ih ( Nat.le_of_succ_le hr ) ) hxB )

/-
Element a is in X of all path cliques except X(parent(i)).
-/
lemma a_in_ancestor_clique {n : ℕ} (X : ℕ → Finset (Fin n))
    (v : ℕ) (_hv : 0 < v) (h_parent_pos : 0 < clParent X v)
    (a : Fin n) (ha_Xi : a ∈ X v) (ha_B : a ∈ clSetB X (clParent X v))
    (m : ℕ) (hm : m ≠ 1) (hm_pos : m = 0 ∨ 0 < (clParent X)^[m - 1] v) :
    a ∈ X ((clParent X)^[m] v) := by
  by_cases hm : m = 0
  · aesop
  · -- Since $m \geq 2`, apply `clSetA_iterate_mono` with m₁ = 2 and m₂ = m.
    have h_clSetA_iterate_mono :
        clSetA X ((clParent X)^[2] v) ⊆ clSetA X ((clParent X)^[m] v) := by
      apply clSetA_iterate_mono
      · exact Nat.lt_of_le_of_ne ( Nat.pos_of_ne_zero hm ) ( Ne.symm ‹_› )
      · intros m_1 hm_1 hm_1_lt_m
        have h_iterate_pos : (clParent X)^[m_1] v ≥ (clParent X)^[m - 1] v := by
          have h_iterate_pos :
              ∀ j, m_1 ≤ j → j ≤ m - 1 →
                (clParent X)^[j] v ≤ (clParent X)^[m_1] v := by
            intros j hj₁ hj₂
            induction hj₁
            · rfl
            · rename_i j hj ih
              simpa only [ Function.iterate_succ_apply' ] using
                le_trans ( clParent_le _ _ ) ( ih ( Nat.le_of_succ_le hj₂ ) )
          exact h_iterate_pos _ ( by omega ) ( by omega )
        exact lt_of_lt_of_le ( hm_pos.resolve_left hm ) h_iterate_pos
    refine Finset.mem_of_subset ( clSetA_sub_X _ _ ) ( h_clSetA_iterate_mono ?_ )
    rw [ clSetB_pos ] at ha_B
    · exact Finset.mem_sdiff.mp ha_B |>.1
    · assumption

/-
Partition contradiction: if x ∉ A(v) and x ∉ B(y_s) for every s, then False.
    Uses the telescoping partition univ = A(v) ∪ ⋃ B(y_s).
-/
lemma partition_contradiction {n : ℕ} (X : ℕ → Finset (Fin n)) (v : ℕ)
    (x : Fin n)
    (hA : x ∉ clSetA X v)
    (hB : ∀ s, x ∉ clSetB X ((clParent X)^[s] v)) :
    False := by
  -- By induction on m, show x is not in A((clParent X)^[m] v).
  have h_ind : ∀ m, x ∉ clSetA X ((clParent X)^[m] v) := by
    intro m
    induction m <;> simp_all +decide [ Function.iterate_succ_apply' ]
    rename_i m ih
    by_cases h : 0 < ( clParent X ) ^[ m ] v <;> simp_all +decide [ clSetA_pos ]
    · exact fun hx => hB m <| by rw [ clSetB_pos _ _ h ] ; aesop
    · simpa [clParent_zero] using ih
  -- Since v is positive, the iterated parent chain eventually reaches 0.
  obtain ⟨D, hD⟩ : ∃ D, (clParent X)^[D] v = 0 := by
    by_contra h_contra; push Not at h_contra; (
    -- The iterated parent chain is strictly decreasing while nonzero.
    have h_seq_decreasing : StrictAnti (fun m => (clParent X)^[m] v) := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      simpa only [ Function.iterate_succ_apply' ] using
        clParent_lt X _ ( Nat.pos_of_ne_zero ( h_contra m ) )
    exact absurd ( Set.infinite_range_of_injective h_seq_decreasing.injective )
      ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr
        ⟨ _, Set.forall_mem_range.mpr fun m => h_seq_decreasing.antitone m.zero_le ⟩ ))
  -- Apply the induction hypothesis to D to get x ∉ clSetA X 0.
  have h_x_not_in_X0 : x ∉ clSetA X 0 := by
    simpa [ hD ] using h_ind D
  exact hB D ( by
    rw [ hD ]
    rw [ clSetB_zero ]
    exact Finset.mem_sdiff.mpr
      ⟨ Finset.mem_univ _,
        fun h => h_x_not_in_X0 <| by simpa [ clSetA_zero ] using h ⟩ )

/-
Weak chain matching: if x ∈ X(parent(v)) ∩ B(y_s), x ∈ X(y_r) for r ≤ s-1,
    only requiring positivity up to r (not s-1).
-/
lemma matching_chain_weak {n : ℕ} (X : ℕ → Finset (Fin n))
    (v : ℕ) (hv : 0 < v) (h_parent_pos : 0 < clParent X v)
    (s : ℕ) (hs : 2 ≤ s)
    (x : Fin n)
    (hx1 : x ∈ X (clParent X v))
    (hxB : x ∈ clSetB X ((clParent X)^[s] v))
    (r : ℕ) (hr : r ≤ s - 1)
    (h_path_pos : ∀ m, 1 ≤ m → m ≤ r → 0 < (clParent X)^[m] v) :
    x ∈ X ((clParent X)^[r] v) := by
  rcases r with ( _ | r ) <;> simp_all +decide [ Function.iterate_succ_apply' ]
  · -- Apply the walkdown_ancestor_matching lemma with d = s - 1.
    have h_walkdown :
        X v ∩ clSetB X ((clParent X)^[s] v) =
          X (clParent X v) ∩ clSetB X ((clParent X)^[s] v) := by
      convert
        walkdown_ancestor_matching X ( clParent X v ) v hv h_parent_pos
          ( by linarith [ clParent_lt X v hv ] ) rfl
          ( s - 1 ) ( Nat.sub_pos_of_lt hs )
        using 1
      cases s <;> aesop ( simp_config := { decide := true } )
      cases s <;> aesop ( simp_config := { decide := true } )
    replace h_walkdown := Finset.ext_iff.mp h_walkdown x; aesop
  · induction r
    · aesop
    · rename_i r ih
      have h_walkdown :
          X (clParent X ((clParent X)^[r] v)) ∩ clSetB X ((clParent X)^[s] v) =
            X (clParent X ((clParent X)^[r + 1] v)) ∩
              clSetB X ((clParent X)^[s] v) := by
        convert
          walkdown_ancestor_matching X
            ( clParent X ( ( clParent X ) ^[ r + 1 ] v ) )
            ( clParent X ( ( clParent X ) ^[ r ] v ) )
            _ _ _ _ ( s - ( r + 1 ) - 1 ) _
          using 1 <;> norm_num [ Function.iterate_succ_apply' ]
        any_goals omega
        · rw [
            show s = r + 1 + ( s - ( r + 1 ) ) by
              rw [
                Nat.add_sub_cancel' ( by
                  linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ s ) ] )
              ]
          ]
          simp +decide [ Function.iterate_add_apply,
            Function.iterate_succ_apply' ]
          rcases k : s - ( r + 1 ) with ( _ | k ) <;>
            simp_all +decide [ Function.iterate_succ_apply' ]
          · omega
          · simp +decide [ ← Function.iterate_succ_apply' ]
            rw [ ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply ]
        · rw [
            show s = s - ( r + 1 ) - 1 + ( r + 1 ) + 1 by omega
          ]
          simp +decide [ Function.iterate_add_apply,
            Function.iterate_succ_apply' ]
          simp +decide [ Nat.sub_sub, add_comm ]
          exact congr_arg _ ( congr_arg _ ( by
            exact Function.iterate_succ_apply' ( clParent X ) _ _ ▸ rfl ) )
        · simpa [ ← Function.iterate_succ_apply' ] using
            h_path_pos ( r + 1 ) ( by linarith ) ( by linarith )
        · convert h_path_pos ( r + 2 ) ( by linarith ) ( by linarith ) using 1
          simp +decide [ Function.iterate_succ_apply' ]
        · convert clParent_lt X _ _ using 1
          simpa only [ ← Function.iterate_succ_apply' ] using
            h_path_pos ( r + 1 ) ( by linarith ) ( by linarith )
      exact Finset.mem_of_mem_inter_left
        ( h_walkdown ▸
          Finset.mem_inter.mpr
            ⟨ ih ( by linarith ) (fun m hm₁ hm₂ =>
                h_path_pos m hm₁ ( by linarith )),
              hxB ⟩ )

/-
If x ∈ B(y_s) and y_s > 0, then x ∈ X(y_r) for r ≥ s+1
    (via A-set nesting: B(y_s) ⊆ A(y_{s+1}) ⊆ A(y_r) ⊆ X(y_r)).
-/
lemma B_set_to_X_via_A {n : ℕ} (X : ℕ → Finset (Fin n))
    (v : ℕ) (s r : ℕ) (hs_pos : 0 < (clParent X)^[s] v) (hr : s + 1 ≤ r)
    (h_pos : ∀ m, s ≤ m → m < r → 0 < (clParent X)^[m] v)
    (x : Fin n) (hxB : x ∈ clSetB X ((clParent X)^[s] v)) :
    x ∈ X ((clParent X)^[r] v) := by
  by_contra h_contra
  -- By definition of clSetB, if x ∈ clSetB X ((clParent X)^[s] v),
  -- then x ∈ clSetA X ((clParent X)^[s+1] v).
  have hxA : x ∈ clSetA X ((clParent X)^[s + 1] v) := by
    have hxA :
        clSetA X ((clParent X)^[s] v) ∪ clSetB X ((clParent X)^[s] v) =
          clSetA X ((clParent X)^[s + 1] v) := by
      convert clSetA_union_clSetB X _ _ using 1
      · rw [ Function.iterate_succ_apply' ]
      · assumption
    exact hxA ▸ Finset.mem_union_right _ hxB
  apply h_contra
  apply clSetA_sub_X X ((clParent X)^[r] v) |> fun h =>
    h (clSetA_iterate_mono X v (s + 1) r (by linarith)
      (fun m hm₁ hm₂ => h_pos m (by linarith) (by linarith))
      hxA)

/-
Two misses on the path lead to contradiction: if x ∈ X(parent(v)) misses
    X(y_p) and X(y_q) for distinct p, q ≠ 1, then False.
-/
lemma not_miss_two_path_cliques {n : ℕ} (X : ℕ → Finset (Fin n))
    (v : ℕ) (hv : 0 < v) (h_parent_pos : 0 < clParent X v)
    (p q : ℕ) (hp : p ≠ 1) (hq : q ≠ 1) (hpq : p ≠ q)
    (h_path_pos_p : ∀ m, 1 ≤ m → m ≤ p → 0 < (clParent X)^[m] v)
    (h_path_pos_q : ∀ m, 1 ≤ m → m ≤ q → 0 < (clParent X)^[m] v)
    (x : Fin n)
    (hx1 : x ∈ X (clParent X v))
    (hxp : x ∉ X ((clParent X)^[p] v))
    (hxq : x ∉ X ((clParent X)^[q] v)) :
    False := by
  apply partition_contradiction X v x
  · contrapose! hxp
    have := clSetA_iterate_mono X v 0 p ( Nat.zero_le _ )
    simp_all +decide [ Finset.subset_iff ]
    exact
      Finset.mem_of_subset ( clSetA_sub_X _ _ )
        ( this
          ( fun m mn =>
            if hm : m = 0 then by
              aesop
            else
              h_path_pos_p m ( Nat.pos_of_ne_zero hm ) ( Nat.le_of_lt mn ) )
          hxp ) |>
        fun h => by aesop
  · intro s hs; by_cases hs0 : s = 0 <;> simp_all +decide
    · have hB_subset_A : clSetB X v ⊆ clSetA X (clParent X v) := by
        exact Finset.subset_iff.mpr fun x hx => by
          have := clSetA_union_clSetB X v hv
          exact this.symm ▸ Finset.mem_union_right _ hx
      have hA_subset_A : clSetA X (clParent X v) ⊆ clSetA X ((clParent X)^[2] v) := by
        apply clSetA_iterate_mono X v 1 2 (by norm_num) (by
        exact fun m hm₁ hm₂ => by interval_cases m ; assumption;)
      have hA_subset_X : clSetA X ((clParent X)^[2] v) ⊆ X ((clParent X)^[p] v) := by
        by_cases hp2 : p ≥ 2
        · have hA_subset_X : clSetA X ((clParent X)^[2] v) ⊆ clSetA X ((clParent X)^[p] v) := by
            apply clSetA_iterate_mono
            · grind
            · grind
          exact Finset.Subset.trans hA_subset_X ( clSetA_sub_X _ _ )
        · interval_cases p <;> simp_all +decide [ Function.iterate_succ_apply' ]
          have hA_subset_X : clSetA X (clParent X (clParent X v)) ⊆ X ((clParent X)^[q] v) := by
            have hA_subset_X :
                clSetA X (clParent X (clParent X v)) ⊆
                  clSetA X ((clParent X)^[q] v) := by
              apply clSetA_iterate_mono X v 2 q (by
              exact Nat.lt_of_le_of_ne ( Nat.pos_of_ne_zero ( by tauto ) ) ( Ne.symm hq )) (by
              grind)
            exact hA_subset_X.trans ( clSetA_sub_X _ _ )
          exact False.elim <| hxq <| hA_subset_X <| hA_subset_A <| hB_subset_A hs
      exact hxp <| hA_subset_X <| hA_subset_A <| hB_subset_A hs
    · -- Since $s \geq 2$, we can apply the matching_chain_weak lemma.
      by_cases hps : p < s
      · have := matching_chain_weak X v hv h_parent_pos s (by
        contrapose! hp; interval_cases s <;> simp_all +decide
        exact absurd ( clSetB_sub_compl X ( clParent X v ) hs ) ( by aesop )) x hx1 hs p (by
        exact Nat.le_pred_of_lt hps) (by
        grind +qlia)
        contradiction
      · by_cases hqs : q < s
        · have := matching_chain_weak X v hv h_parent_pos s (by
          contrapose! hq; interval_cases s <;> simp_all +decide
          exact absurd ( clSetB_sub_compl X ( clParent X v ) hs ) ( by aesop )) x hx1 hs q (by
          exact Nat.le_pred_of_lt hqs) (by
          exact h_path_pos_q)
          contradiction
        · cases lt_or_gt_of_ne hpq <;> simp_all +decide
          · have := B_set_to_X_via_A X v s q ( by
              exact h_path_pos_p s ( Nat.pos_of_ne_zero hs0 ) hps ) ( by
              linarith ) ( by
              exact fun m hm₁ hm₂ =>
                h_path_pos_q m
                  ( by linarith [ Nat.pos_of_ne_zero hs0 ] )
                  ( by linarith ) ) x hs
            aesop
          · contrapose! hxq; have := B_set_to_X_via_A X v s p ( by
              exact h_path_pos_p s ( Nat.pos_of_ne_zero hs0 ) hps ) ( by
              grind ) ( by
              exact fun m hm₁ hm₂ =>
                h_path_pos_p m
                  ( by linarith [ Nat.pos_of_ne_zero hs0 ] )
                  ( by linarith ) ) x hs
            aesop

/-
Two colliding misses give False, handling the depth=k edge case.
-/
lemma two_misses_false {k n t : ℕ} (hk : k ≥ 3)
    (X : ℕ → Finset (Fin n))
    (i : Fin (t + 1)) (hi_pos : 0 < i.val)
    (h_depth : (clTree X t).depth i ≥ k)
    (h_parent_pos : 0 < clParent X i.val)
    (m₁ m₂ : ℕ) (hm₁ : m₁ ≤ k) (hm₂ : m₂ ≤ k)
    (hne₁ : m₁ ≠ 1) (hne₂ : m₂ ≠ 1) (hne : m₁ ≠ m₂)
    (x : Fin n) (hx1 : x ∈ X (clParent X i.val))
    (hxm₁ : x ∉ X ((clParent X)^[m₁] i.val))
    (hxm₂ : x ∉ X ((clParent X)^[m₂] i.val)) :
    False := by
  -- Assume without loss of generality that $m₁ < m₂$.
  suffices h_wlog :
      ∀ {m₁ m₂ : ℕ}, m₁ < m₂ → m₁ ≤ k → m₂ ≤ k →
        m₁ ≠ 1 → m₂ ≠ 1 → m₁ ≠ m₂ →
        ∀ (x : Fin n), x ∈ X (clParent X i.val) →
          x ∉ X ((clParent X)^[m₁] i.val) →
          x ∉ X ((clParent X)^[m₂] i.val) → False by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact h_wlog h hm₁ hm₂ hne₁ hne₂ hne x hx1 hxm₁ hxm₂
    · exact h_wlog h hm₂ hm₁ hne₂ hne₁ (Ne.symm hne) x hx1 hxm₂ hxm₁
  intros m₁ m₂ hlt hm₁ hm₂ hne₁ hne₂ hne x hx1 hxm₁ hxm₂
  -- Since $m₂ = k$, we have $(clParent X)^[k] i.val = 0$.
  have h_yk_zero : (clParent X)^[k] i.val = 0 := by
    by_contra h_nonzero
    have h_all_pos : ∀ m, 1 ≤ m → m ≤ k → 0 < (clParent X)^[m] i.val := by
      intro m hm1 hmk
      rcases eq_or_lt_of_le hmk with rfl | hlt
      · exact Nat.pos_of_ne_zero h_nonzero
      · exact path_iterate_pos_of_depth X i m (by omega)
    exact not_miss_two_path_cliques X i.val hi_pos h_parent_pos m₁ m₂ hne₁ hne₂ hne
      (fun m a b => h_all_pos m a (le_trans b hm₁))
      (fun m a b => h_all_pos m a (le_trans b hm₂))
      x hx1 hxm₁ hxm₂
  -- Since $m₁ < k$, we have $x \in clSetB X ((clParent X)^[k] i.val)$.
  have hx_B : x ∈ clSetB X ((clParent X)^[k] i.val) := by
    cases eq_or_lt_of_le ( show m₂ ≤ k from hm₂ ) <;> simp_all +decide
    · rw [ clSetB_zero ]
      exact Finset.mem_sdiff.mpr ⟨ Finset.mem_univ _, hxm₂ ⟩
    · have :=
        not_miss_two_path_cliques X i.val hi_pos h_parent_pos m₁ m₂ hne₁ hne₂
          hne
          ( fun m hm₁ hm₂ =>
            path_iterate_pos_of_depth X i m ( by linarith ) )
          ( fun m hm₁ hm₂ =>
            path_iterate_pos_of_depth X i m ( by linarith ) )
          x hx1 hxm₁ hxm₂
      aesop
  -- Apply matching_chain_weak with v = i.val, s = k ≥ 2, r = m₁ ≤ k - 1.
  have :=
    matching_chain_weak X i.val hi_pos h_parent_pos k (by linarith) x hx1
      hx_B m₁ (by omega) (by
        exact fun m hm₁ hm₂ =>
          path_iterate_pos_of_depth X i m ( by linarith ))
  contradiction

/-
Main pigeonhole case: when depth ≥ k and a ∈ e, show e ∈ H.edges.
-/
lemma depth_bound_pigeonhole {k n t : ℕ} (hk : k ≥ 3)
    (H : KUniformHypergraph (Fin n) k) (X : ℕ → Finset (Fin n))
    (hX_clique : ∀ v : Fin (t + 1), H.IsClique (X v.val))
    (i : Fin (t + 1)) (hi_pos : 0 < i.val)
    (h_depth : (clTree X t).depth i ≥ k)
    (a : Fin n) (ha_Xi : a ∈ X i.val)
    (ha_B : a ∈ clSetB X (clParent X i.val))
    (_ha_not_pi : a ∉ X (clParent X i.val))
    (e : Finset (Fin n)) (he_sub : e ⊆ X (clParent X i.val) ∪ {a})
    (he_card : e.card = k) (ha_e : a ∈ e) :
    e ∈ H.edges := by
  -- parent is positive
  have h_parent_pos : 0 < clParent X i.val :=
    path_iterate_pos_of_depth X i 1 (by omega)
  -- Find m ∈ {0,2,...,k} with e ⊆ X(y_m)
  suffices h_exists : ∃ m, m ≤ k ∧ m ≠ 1 ∧ e ⊆ X ((clParent X)^[m] i.val) by
    obtain ⟨m, hm_le, hm_ne, hm_sub⟩ := h_exists
    have hm_lt : (clParent X)^[m] i.val < t + 1 :=
      lt_of_le_of_lt (clParent_iterate_le X i.val m) i.isLt
    exact (hX_clique ⟨_, hm_lt⟩).1 e hm_sub he_card
  -- By contradiction: if no such m exists, pigeonhole gives two colliding misses
  by_contra h_no_m
  push Not at h_no_m
  -- h_no_m : ∀ m, m ≤ k → m ≠ 1 → ¬(e ⊆ X(y_m))
  -- For each m ∈ {0,2,...,k}, find a witness in e\{a} missing X(y_m)
  have h_witness : ∀ m, m ≤ k → m ≠ 1 →
      ∃ x ∈ e \ {a}, x ∉ X ((clParent X)^[m] i.val) := by
    intro m hm_le hm_ne
    have ha_in : a ∈ X ((clParent X)^[m] i.val) :=
      a_in_ancestor_clique X i.val hi_pos h_parent_pos a ha_Xi ha_B m hm_ne
        (by rcases m with _ | _ | m
            · left; rfl
            · simp at hm_ne
            · right; rw [show m + 2 - 1 = m + 1 from by omega]
              exact path_iterate_pos_of_depth X i (m + 1) (by omega))
    obtain ⟨x', hx'_e, hx'_miss⟩ := Finset.not_subset.mp (h_no_m m hm_le hm_ne)
    have hx'_ne_a : x' ≠ a := fun h => hx'_miss (h ▸ ha_in)
    exact ⟨x', Finset.mem_sdiff.mpr ⟨hx'_e, by simp [hx'_ne_a]⟩, hx'_miss⟩
  -- Pigeonhole: k-1 elements, k indices, some index hit twice
  -- By pigeonhole, two steps m₁ and m₂ choose the same x.
  obtain ⟨m₁, m₂, hm₁m₂, hm₁, hm₂⟩ :
      ∃ m₁ m₂ : ℕ,
        m₁ ≤ k ∧ m₂ ≤ k ∧ m₁ ≠ m₂ ∧ m₁ ≠ 1 ∧ m₂ ≠ 1 ∧
          ∃ x ∈ e \ {a},
            x ∉ X ((clParent X)^[m₁] i.val) ∧
              x ∉ X ((clParent X)^[m₂] i.val) := by
    have h_pigeonhole :
        Finset.card
          (Finset.biUnion (Finset.range (k + 1) \ {1}) (fun m =>
            Finset.filter (fun x => x ∉ X ((clParent X)^[m] i.val))
              (e \ {a}))) ≤ k - 1 := by
      exact
        le_trans
          ( Finset.card_le_card <|
            Finset.biUnion_subset.mpr fun m hm => Finset.filter_subset _ _ )
          ( by simp [ Finset.card_sdiff, * ] )
    contrapose! h_pigeonhole
    rw [ Finset.card_biUnion ]
    · refine lt_of_lt_of_le ?_ ( Finset.sum_le_sum fun m hm => Finset.card_pos.mpr ?_ )
      · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Finset.card_sdiff ]
      · exact Exists.elim
          ( h_witness m
            ( Finset.mem_range_succ_iff.mp
              ( Finset.mem_sdiff.mp hm |>.1 ) )
            ( by aesop ) )
          fun x hx => ⟨ x, by aesop ⟩
    · intros m hm m' hm' h; simp_all +decide [ Finset.disjoint_left ]
      exact fun x hx hx' hx'' => h_pigeonhole m m' hm.1 hm'.1 h hm.2 hm'.2 x hx hx' hx''
  obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := hm₂.2.2.2
  apply two_misses_false hk X i hi_pos h_depth h_parent_pos m₁ m₂ hm₁m₂
    hm₁ hm₂.2.1 hm₂.2.2.1 hm₂.1 x (by
      grind) hx₂ hx₃

/-! ### Core walk-down properties -/

/-
**Nonempty encoding**: Every child j of parent i has X(j) ∩ B(i) nonempty.
    If X(j) ∩ B(i) = ∅, then by `walkdown_empty_encoding_subset`, X(j) ⊆ X(i).
    Since X(j) and X(i) have distinct cardinalities, X(j) ⊊ X(i).
    But X(i) is complete (it's a clique), so X(j) is contained in a strictly
    larger complete set, contradicting X(j) being maximal.
-/
lemma walkdown_nonempty_encoding {k n : ℕ} (_hk : k ≥ 3)
    (H : KUniformHypergraph (Fin n) k) (X : ℕ → Finset (Fin n)) (t : ℕ)
    (hX_clique : ∀ v : Fin (t + 1), H.IsClique (X v.val))
    (hX_distinct_card : ∀ v w : Fin (t + 1), v ≠ w →
      (X v.val).card ≠ (X w.val).card)
    (i j : Fin (t + 1)) (hpar : (clTree X t).parent j = i) (hne : j ≠ i) :
    (X j.val ∩ clSetB X i.val).Nonempty := by
  by_contra h_empty
  have hj_pos : 0 < j.val := by
    by_contra hj_nonpos
    have hj_zero : j = ⟨0, Nat.zero_lt_succ t⟩ := by
      ext
      exact Nat.eq_zero_of_not_pos hj_nonpos
    have hi_zero : i = ⟨0, Nat.zero_lt_succ t⟩ := by
      rw [hj_zero] at hpar
      simpa [clTree, clParent_zero] using hpar.symm
    exact hne (by simp [hj_zero, hi_zero])
  have h_subset : X j ⊆ X i := by
    apply walkdown_empty_encoding_subset
    · exact hj_pos
    · simpa [hpar] using (clTree X t).parent_lt j hj_pos
    · exact congr_arg Fin.val hpar
    · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
  have h_compatible : H.IsComplete (X i) := by
    exact hX_clique i |>.1
  exact hX_clique j |>.2 _
    ( Finset.ssubset_iff_subset_ne.mpr
      ⟨ h_subset, by
        specialize hX_distinct_card j i
        aesop ⟩ )
    h_compatible

/-- **Core walk-down properties** (Section 3 of the paper):
    (1) **Depth bound**: every vertex has depth ≤ k−1.
        Uses the matching-along-paths property and a pigeonhole argument:
        if depth ≥ k, take path y₀,...,yₖ with k+1 cliques. Each element of
        X(yₖ₋₁) ∪ {a} (where a ∈ X(yₖ) ∩ B(yₖ₋₁)) misses at most 1 clique.
        By pigeonhole (k elements, k+1 cliques), some clique contains all of e.
        So X(yₖ₋₁) ∪ {a} is complete, contradicting maximality.
    (2) **Nonempty encodings**: every child j of vertex i has X(j) ∩ B(i) ≠ ∅.
        Uses `walkdown_nonempty_encoding` (proved from `walkdown_empty_encoding_subset`).

    Part 2 is fully proved via `walkdown_nonempty_encoding`.
    Part 1 (depth bound) uses `walkdown_ancestor_matching` and the pigeonhole
    argument via `depth_bound_pigeonhole`, which chains matching lemmas along
    the ancestor path and applies `not_miss_two_path_cliques` to derive
    a contradiction. Both parts are fully proved. -/
lemma walkdown_core_properties {k n : ℕ} (hk : k ≥ 3)
    (H : KUniformHypergraph (Fin n) k) (X : ℕ → Finset (Fin n)) (t : ℕ)
    (hX_clique : ∀ v : Fin (t + 1), H.IsClique (X v.val))
    (hX_distinct_card : ∀ v w : Fin (t + 1), v ≠ w →
      (X v.val).card ≠ (X w.val).card) :
    (∀ i : Fin (t + 1), (clTree X t).depth i ≤ k - 1) ∧
    (∀ i j : Fin (t + 1), (clTree X t).parent j = i → j ≠ i →
      (X j.val ∩ clSetB X i.val).Nonempty) := by
  have hne := walkdown_nonempty_encoding hk H X t hX_clique hX_distinct_card
  refine ⟨fun i => ?_, hne⟩
  -- Depth bound by contradiction: if depth ≥ k, X(parent(i)) ∪ {a} is complete.
  by_contra h_depth
  push Not at h_depth
  -- depth(i) ≥ k ≥ 3
  have h_di : (clTree X t).depth i ≥ k := by omega
  -- Extract parent and grandparent
  have hi_pos : 0 < i.val := by
    by_contra h; push Not at h; simp at h
    have : (clTree X t).depth i = 0 := by
      unfold OrderedRootedTree.depth; simp [h]
    omega
  -- parent vertex
  set pi := (clTree X t).parent i with hpi_def
  -- Get a ∈ X(i) ∩ B(parent(i))
  have hi_ne_pi : i ≠ pi := by
    intro heq; have := (clTree X t).parent_lt i hi_pos
    exact absurd (congr_arg Fin.val heq) (by omega)
  obtain ⟨a, ha⟩ := hne pi i (hpi_def ▸ rfl) hi_ne_pi
  -- a ∈ X(i) and a ∈ B(parent(i))
  have ha_Xi : a ∈ X i.val := (Finset.mem_inter.mp ha).1
  have ha_B : a ∈ clSetB X pi.val := (Finset.mem_inter.mp ha).2
  -- a ∉ X(parent(i))
  have ha_not_pi : a ∉ X pi.val := by
    intro h; exact absurd h (Finset.mem_sdiff.mp (clSetB_sub_compl X pi.val ha_B)).2
  -- X(parent(i)) is maximal: X(pi) ⊂ T → ¬IsComplete T
  have hpi_max := (hX_clique pi).2
  -- Show contradiction by proving X(pi) ∪ {a} is complete
  apply hpi_max (X pi.val ∪ {a})
  · -- X(pi) ⊂ X(pi) ∪ {a}
    constructor
    · exact Finset.subset_union_left
    · intro h; exact ha_not_pi (h (Finset.mem_union_right _ (Finset.mem_singleton_self a)))
  · -- IsComplete (X(pi) ∪ {a})
    intro e he_sub he_card
    -- If a ∉ e, then e ⊆ X(pi), done by completeness
    by_cases ha_e : a ∈ e
    · -- a ∈ e: use pigeonhole on path cliques
      have hpi_eq : pi.val = clParent X i.val := by
        unfold clTree at hpi_def; exact congr_arg Fin.val hpi_def
      exact depth_bound_pigeonhole hk H X hX_clique i hi_pos h_di a ha_Xi
        (hpi_eq ▸ ha_B) (hpi_eq ▸ ha_not_pi) e (hpi_eq ▸ he_sub) he_card ha_e
    · -- a ∉ e: e ⊆ X(pi)
      exact (hX_clique pi).1 e (fun x hx => by
        rcases Finset.mem_union.mp (he_sub hx) with h | h
        · exact h
        · exact absurd (Finset.mem_singleton.mp h ▸ hx) ha_e) he_card

/-! ## Tree construction from clique sizes (Section 3 of the paper) -/

/-- **Tree construction (Section 3)**: If a k-uniform hypergraph (k ≥ 3) on n vertices
    has more than n − C distinct clique sizes, then there exists a (k−1, C)-layered tree
    with at least n − C vertices. -/
theorem tree_from_many_clique_sizes (k : ℕ) (hk : k ≥ 3) (C n : ℕ)
    (H : KUniformHypergraph (Fin n) k)
    (sizes : Finset ℕ)
    (h_realized : ∀ s ∈ sizes, ∃ S : Finset (Fin n), H.IsClique S ∧ S.card = s)
    (h_many : sizes.card > n - C) :
    ∃ t : ℕ, ∃ T : OrderedRootedTree t,
      IsKCLayeredTree (k - 1) C T ∧ t + 1 = sizes.card := by
  -- Setup: m = sizes.card, t = m − 1
  set m := sizes.card with hm_def
  have hm_pos : m ≥ 1 := by omega
  use m - 1
  -- Order sizes decreasingly using orderIsoOfFin composed with Fin.rev
  let f := Finset.orderIsoOfFin sizes rfl
  let g : Fin m → ℕ := fun i => (f (Fin.rev i) : ℕ)
  have hg_mem : ∀ i : Fin m, g i ∈ sizes := fun i => (f (Fin.rev i)).prop
  have hg_strict_anti : StrictAnti g := by
    intro i j hij
    exact (Finset.orderIsoOfFin sizes rfl).strictMono (Fin.rev_lt_rev.mpr hij)
  -- Choose a clique for each ordered size
  let X' : Fin m → Finset (Fin n) := fun i => (h_realized (g i) (hg_mem i)).choose
  have hX'_clique : ∀ i : Fin m, H.IsClique (X' i) :=
    fun i => (h_realized (g i) (hg_mem i)).choose_spec.1
  have hX'_card : ∀ i : Fin m, (X' i).card = g i :=
    fun i => (h_realized (g i) (hg_mem i)).choose_spec.2
  -- Extend X' to ℕ → Finset (Fin n)
  let X : ℕ → Finset (Fin n) := fun i => if h : i < m then X' ⟨i, h⟩ else ∅
  have hX_eq : ∀ (i : Fin m), X i.val = X' i := fun i => by simp [X, i.isLt]
  -- Build the tree
  set t := m - 1 with ht_def
  have htm : t + 1 = m := by omega
  let T := clTree X t
  -- Clique and distinctness properties for X restricted to Fin (t+1)
  have hXc : ∀ v : Fin (t + 1), H.IsClique (X v.val) := by
    intro v; rw [hX_eq ⟨v.val, by omega⟩]; exact hX'_clique _
  have hXd : ∀ v w : Fin (t + 1), v ≠ w → (X v.val).card ≠ (X w.val).card := by
    intro v w hvw
    rw [hX_eq ⟨v.val, by omega⟩, hX_eq ⟨w.val, by omega⟩,
        hX'_card ⟨v.val, by omega⟩, hX'_card ⟨w.val, by omega⟩]
    intro h
    exact hvw (Fin.ext (by simpa using congr_arg Fin.val (hg_strict_anti.injective h)))
  -- Extract core walk-down properties
  obtain ⟨h_depth, h_nonempty⟩ := walkdown_core_properties hk H X t hXc hXd
  use T
  refine ⟨⟨h_depth, ?_⟩, by omega⟩
  -- Degree bound: degree(i) ≤ 2^(C + i)
  intro i
  have h_nc := walkdown_numChildren_le X t i
    (walkdown_children_distinct_encoding X t i) (h_nonempty i)
  have h_B : (clSetB X i.val).card ≤ C + i.val := by
    have h1 := clSetB_card_le X i.val
    rw [hX_eq ⟨i.val, by omega⟩, hX'_card ⟨i.val, by omega⟩] at h1
    have h2 : g ⟨i.val, by omega⟩ ≥ m - 1 - i.val := by
      calc (f (Fin.rev ⟨i.val, by omega⟩) : ℕ)
          ≥ (Fin.rev ⟨i.val, (by omega : i.val < m)⟩).val :=
            orderIso_val_ge sizes m rfl _
        _ = m - 1 - i.val := by simp [Fin.rev]; omega
    omega
  unfold OrderedRootedTree.degree
  have h_pow_pos : 2 ^ (clSetB X i.val).card ≥ 1 := Nat.one_le_two_pow
  calc (clTree X t).numChildren i + (if 0 < i.val then 1 else 0)
      ≤ (2 ^ (clSetB X i.val).card - 1) + 1 := by split <;> omega
    _ = 2 ^ (clSetB X i.val).card := by omega
    _ ≤ 2 ^ (C + i.val) := Nat.pow_le_pow_right (by omega) h_B

/-! ## Theorem 1.1: Main Theorem -/

theorem main_theorem (k : ℕ) (hk : k ≥ 3) (C : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ H : KUniformHypergraph (Fin n) k,
        ∀ sizes : Finset ℕ,
          (∀ s ∈ sizes, ∃ S : Finset (Fin n), H.IsClique S ∧ S.card = s) →
          sizes.card ≤ n - C := by
  obtain ⟨N₀, hN₀⟩ := layered_tree_bounded (k - 1) C
  use N₀ + C + 1
  intro n hn H sizes h_realized
  by_contra h_neg
  push Not at h_neg
  obtain ⟨t, T, hT_layered, hT_card⟩ :=
    tree_from_many_clique_sizes k hk C n H sizes h_realized h_neg
  have h_bound := hN₀ t T hT_layered
  omega

/-! ## k = 3 Corollary: Erdős Problem #775 -/

theorem erdos_problem_775 (C : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ H : KUniformHypergraph (Fin n) 3,
        ∀ sizes : Finset ℕ,
          (∀ s ∈ sizes, ∃ S : Finset (Fin n), H.IsClique S ∧ S.card = s) →
          sizes.card ≤ n - C :=
  main_theorem 3 (by omega) C

#print axioms erdos_problem_775
-- 'Erdos775.erdos_problem_775' depends on axioms: [propext, choice, Quot.sound]

end

end Erdos775

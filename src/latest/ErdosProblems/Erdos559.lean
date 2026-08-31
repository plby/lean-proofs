/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 559.
https://www.erdosproblems.com/forum/thread/559

Informal authors:
- Vojtěch Rödl
- Endre Szemerédi

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos559.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Util.Ramsey

/-!
# Erdős Problem 559

The problem asked whether the size Ramsey number of every bounded-degree graph is linear in
its number of vertices, with a constant depending only on the degree bound.  Rödl and
Szemerédi disproved this already for maximum degree three.  The detailed mathematical proof
and the Leanization plan used here are in `tex/559.tex`.

This file formalizes the ordinary, non-induced, two-colour size Ramsey number and proves the
exact negative answer at degree three by a deterministic finite version of the
root-scarcity/high-degree-colouring construction.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos559

attribute [local instance] Classical.propDecidable

/-- A uniform finite enumeration of graph copies, used so that all subtype
cardinalities below share the same canonical `Fintype` instances. -/
noncomputable local instance (priority := 2000) copyFintype
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Fintype (G.Copy H) :=
  Fintype.ofInjective (fun f : G.Copy H ↦ (f : V → W)) fun f g h ↦ by
    apply SimpleGraph.Copy.ext
    intro v
    exact congr_fun h v

/-! ## Size Ramsey definitions -/

/-- `H` is Ramsey for `G` if every red spanning subgraph `R ≤ H` contains a copy of `G`,
or the complementary set of host edges contains a copy of `G`.  Containment `⊑` is ordinary
(not necessarily induced) graph containment. -/
def IsRamseyFor {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph V, R ≤ H → G ⊑ R ∨ G ⊑ (H \ R)

/-- The number of unordered edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} [Finite V] (H : SimpleGraph V) : ℕ :=
  Nat.card H.edgeSet

lemma edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : edgeCount H = H.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

/-- There is a finite Ramsey host for every finite graph. -/
lemma ramseyHost_exists {W : Type*} [Finite W] (G : SimpleGraph W) :
    ∃ (N : ℕ) (H : SimpleGraph (Fin N)), IsRamseyFor H G := by
  let _ : Fintype W := Fintype.ofFinite W
  let n := Fintype.card W
  obtain ⟨N, hN⟩ := Ramsey.ramseyProperty_exists n n
  refine ⟨N, ⊤, ?_⟩
  intro R _
  have hor : ¬ R.CliqueFree n ∨ ¬ R.IndepSetFree n := not_and_or.mp (hN R)
  let G' : SimpleGraph (Fin n) := G.overFin rfl
  let e : G ≃g G' := SimpleGraph.overFinIso (G := G) rfl
  have hGtop : G ⊑ (⊤ : SimpleGraph (Fin n)) :=
    e.isContained.trans (SimpleGraph.IsContained.of_le le_top)
  rcases hor with hred | hblue
  · left
    have htop : (⊤ : SimpleGraph (Fin n)) ⊑ R := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hred
    exact hGtop.trans htop
  · right
    have hblue' : ¬ Rᶜ.CliqueFree n := by
      simpa only [SimpleGraph.cliqueFree_compl] using hblue
    have htop : (⊤ : SimpleGraph (Fin n)) ⊑ Rᶜ := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hblue'
    have hdiff : (⊤ \ R : SimpleGraph (Fin N)) = Rᶜ := by
      ext u v
      simp [SimpleGraph.compl_adj]
    rw [hdiff]
    exact hGtop.trans htop

/-- A natural number is realized as the edge count of a finite Ramsey host for `G`. -/
def HasRamseyHostWithEdges {W : Type*} [Fintype W] (G : SimpleGraph W) (m : ℕ) : Prop :=
  ∃ (N : ℕ) (H : SimpleGraph (Fin N)), IsRamseyFor H G ∧ edgeCount H = m

lemma ramseyHostEdgeCount_exists {W : Type*} [Fintype W] (G : SimpleGraph W) :
    ∃ m, HasRamseyHostWithEdges G m := by
  obtain ⟨N, H, hH⟩ := ramseyHost_exists G
  exact ⟨edgeCount H, N, H, hH, rfl⟩

/-- The size Ramsey number: the least number of edges in a finite graph Ramsey for `G`. -/
noncomputable def sizeRamseyNumber {W : Type*} [Fintype W] (G : SimpleGraph W) : ℕ :=
  Nat.find (ramseyHostEdgeCount_exists G)

lemma sizeRamseyNumber_spec {W : Type*} [Fintype W] (G : SimpleGraph W) :
    HasRamseyHostWithEdges G (sizeRamseyNumber G) := by
  exact Nat.find_spec (ramseyHostEdgeCount_exists G)

lemma sizeRamseyNumber_le_of_ramsey {W : Type*} [Fintype W] (G : SimpleGraph W)
    {N : ℕ} {H : SimpleGraph (Fin N)} (hH : IsRamseyFor H G) :
    sizeRamseyNumber G ≤ edgeCount H := by
  exact Nat.find_min' (ramseyHostEdgeCount_exists G) ⟨N, H, hH, rfl⟩

lemma ramsey_edgeCount_ge_sizeRamseyNumber {W : Type*} [Fintype W]
    (G : SimpleGraph W) {N : ℕ} {H : SimpleGraph (Fin N)} (hH : IsRamseyFor H G) :
    sizeRamseyNumber G ≤ edgeCount H :=
  sizeRamseyNumber_le_of_ramsey G hH

/-- The proposed uniform linear size-Ramsey bound at one fixed maximum degree. -/
def FixedDegreeLinearSizeRamsey (d : ℕ) : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.maxDegree ≤ d → sizeRamseyNumber G ≤ C * Fintype.card V

/-- The assertion asked for in Erdős Problem 559. -/
def Erdos559Statement : Prop :=
  ∀ d : ℕ, FixedDegreeLinearSizeRamsey d

/-! ## The bounded-degree target family -/

/-- The matching which pairs the two halves of `Fin (K + K)`, after applying `σ`. -/
def matchingGraph (K : ℕ) (σ : Equiv.Perm (Fin (K + K))) :
    SimpleGraph (Fin (K + K)) :=
  SimpleGraph.fromRel fun u v ↦
    ∃ i : Fin K, u = σ (Fin.castAdd K i) ∧ v = σ (Fin.natAdd K i)

/-- A path with one permuted perfect matching superimposed on it. -/
def componentGraph (K : ℕ) (σ : Equiv.Perm (Fin (K + K))) :
    SimpleGraph (Fin (K + K)) :=
  SimpleGraph.pathGraph (K + K) ⊔ matchingGraph K σ

/-- The disjoint union of all the labelled components `componentGraph K σ`. -/
def targetGraph (K : ℕ) :
    SimpleGraph (Equiv.Perm (Fin (K + K)) × Fin (K + K)) where
  Adj x y := x.1 = y.1 ∧ (componentGraph K x.1).Adj x.2 y.2
  symm.symm x y h := by
    exact ⟨h.1.symm, h.1 ▸ h.2.symm⟩
  loopless.irrefl x h := by
    exact h.2.ne rfl

lemma matchingGraph_adj_iff {K : ℕ} {σ : Equiv.Perm (Fin (K + K))}
    {u v : Fin (K + K)} :
    (matchingGraph K σ).Adj u v ↔
      (∃ i : Fin K, u = σ (Fin.castAdd K i) ∧ v = σ (Fin.natAdd K i)) ∨
      (∃ i : Fin K, v = σ (Fin.castAdd K i) ∧ u = σ (Fin.natAdd K i)) := by
  rw [matchingGraph, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with ⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩
    · have hx := σ.injective (hi.symm.trans hi')
      have := congr_arg Fin.val hx
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · have hx := σ.injective (hi'.symm.trans hi)
      have := congr_arg Fin.val hx
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega

lemma matchingGraph_neighbor_unique {K : ℕ} (σ : Equiv.Perm (Fin (K + K)))
    {u v w : Fin (K + K)} (huv : (matchingGraph K σ).Adj u v)
    (huw : (matchingGraph K σ).Adj u w) : v = w := by
  rw [matchingGraph_adj_iff] at huv huw
  rcases huv with ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ <;>
    rcases huw with ⟨j, h₁, h₂⟩ | ⟨j, h₁, h₂⟩
  · have hij : i = j := by
      apply Fin.ext
      have := σ.injective h₁.symm
      exact (congr_arg Fin.val this).symm
    subst j
    exact h₂.symm
  · have hx := σ.injective h₂
    have hx' := congr_arg Fin.val hx
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hx'
    omega
  · have hx := σ.injective h₁
    have hx' := congr_arg Fin.val hx
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hx'
    omega
  · have hij : i = j := by
      apply Fin.ext
      have := σ.injective h₂.symm
      have hx := congr_arg Fin.val this
      simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hx.symm
    subst j
    exact h₁.symm

lemma matchingGraph_degree_le_one {K : ℕ} (σ : Equiv.Perm (Fin (K + K)))
    (u : Fin (K + K)) : (matchingGraph K σ).degree u ≤ 1 := by
  rw [← (matchingGraph K σ).card_neighborSet_eq_degree u]
  let e : (matchingGraph K σ).neighborSet u ↪ Fin 1 :=
    ⟨fun _ ↦ 0, by
      intro v w _
      apply Subtype.ext
      exact matchingGraph_neighbor_unique σ v.2 w.2⟩
  simpa using Fintype.card_le_of_injective e e.injective

lemma pathGraph_degree_le_two {L : ℕ} (u : Fin L) :
    (SimpleGraph.pathGraph L).degree u ≤ 2 := by
  rw [← (SimpleGraph.pathGraph L).card_neighborSet_eq_degree u]
  let e : (SimpleGraph.pathGraph L).neighborSet u ↪ Bool :=
    ⟨fun v ↦ decide (v.1.1 < u.1), by
      intro v w he
      apply Subtype.ext
      have hv : (SimpleGraph.pathGraph L).Adj u v.1 := v.2
      have hw : (SimpleGraph.pathGraph L).Adj u w.1 := w.2
      rw [SimpleGraph.pathGraph_adj] at hv hw
      change decide (v.1.val < u.val) = decide (w.1.val < u.val) at he
      by_cases hvu : v.1.val < u.val <;> by_cases hwu : w.1.val < u.val
      · omega
      · simp [hvu, hwu] at he
      · simp [hvu, hwu] at he
      · omega⟩
  simpa only [Fintype.card_bool] using
    Fintype.card_le_of_injective e e.injective

lemma componentGraph_degree_le_three {K : ℕ} (σ : Equiv.Perm (Fin (K + K)))
    (u : Fin (K + K)) : (componentGraph K σ).degree u ≤ 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, componentGraph,
    SimpleGraph.neighborFinset_sup]
  have hp : ((SimpleGraph.pathGraph (K + K)).neighborFinset u).card ≤ 2 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using pathGraph_degree_le_two u
  have hm : ((matchingGraph K σ).neighborFinset u).card ≤ 1 := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      matchingGraph_degree_le_one σ u
  calc
    ((SimpleGraph.pathGraph (K + K)).neighborFinset u ∪
        (matchingGraph K σ).neighborFinset u).card
        ≤ ((SimpleGraph.pathGraph (K + K)).neighborFinset u).card +
            ((matchingGraph K σ).neighborFinset u).card := Finset.card_union_le _ _
    _ ≤ 2 + 1 := Nat.add_le_add hp hm
    _ = 3 := rfl

lemma targetGraph_degree_le_three (K : ℕ)
    (x : Equiv.Perm (Fin (K + K)) × Fin (K + K)) :
    (targetGraph K).degree x ≤ 3 := by
  let e : (targetGraph K).neighborSet x ↪
      (componentGraph K x.1).neighborSet x.2 :=
    ⟨fun y ↦ ⟨y.1.2, by
        have hy : (targetGraph K).Adj x y.1 := y.2
        change x.1 = y.1.1 ∧ (componentGraph K x.1).Adj x.2 y.1.2 at hy
        exact hy.2⟩, by
      rintro ⟨y, hy⟩ ⟨z, hz⟩ he
      apply Subtype.ext
      have hy' := (show (targetGraph K).Adj x y from hy)
      have hz' := (show (targetGraph K).Adj x z from hz)
      change x.1 = y.1 ∧ (componentGraph K x.1).Adj x.2 y.2 at hy'
      change x.1 = z.1 ∧ (componentGraph K x.1).Adj x.2 z.2 at hz'
      apply Prod.ext
      · exact hy'.1.symm.trans hz'.1
      · exact congr_arg Subtype.val he⟩
  calc
    (targetGraph K).degree x = Fintype.card ((targetGraph K).neighborSet x) :=
      ((targetGraph K).card_neighborSet_eq_degree x).symm
    _ ≤ Fintype.card ((componentGraph K x.1).neighborSet x.2) :=
      Fintype.card_le_of_injective e e.injective
    _ = (componentGraph K x.1).degree x.2 :=
      (componentGraph K x.1).card_neighborSet_eq_degree x.2
    _ ≤ 3 := componentGraph_degree_le_three x.1 x.2

lemma targetGraph_maxDegree_le_three (K : ℕ) : (targetGraph K).maxDegree ≤ 3 := by
  exact (targetGraph K).maxDegree_le_of_forall_degree_le 3 (targetGraph_degree_le_three K)

@[simp] lemma targetGraph_card (K : ℕ) :
    Fintype.card (Equiv.Perm (Fin (K + K)) × Fin (K + K)) =
      Nat.factorial (K + K) * (K + K) := by
  rw [Fintype.card_prod, Fintype.card_perm]
  simp

/-! ## Counting rooted path copies -/

/-- Copies of a path with `n` edges whose first vertex has prescribed image `v`. -/
def RootedPathCopy {V : Type*} [Fintype V] (n : ℕ) (Q : SimpleGraph V) (v : V) :=
  {f : (SimpleGraph.pathGraph (n + 1)).Copy Q // f 0 = v}

noncomputable instance rootedPathCopyFintype {V : Type*} [Fintype V] (n : ℕ)
    (Q : SimpleGraph V) (v : V) : Fintype (RootedPathCopy n Q v) :=
  inferInstanceAs (Fintype {f : (SimpleGraph.pathGraph (n + 1)).Copy Q // f 0 = v})

/-- The initial `n+1` vertices of the path on `n+2` vertices. -/
def pathPrefixCopy (n : ℕ) :
    (SimpleGraph.pathGraph (n + 1)).Copy (SimpleGraph.pathGraph (n + 2)) :=
  ⟨⟨Fin.castSucc, by
      intro a b hab
      rw [SimpleGraph.pathGraph_adj] at hab ⊢
      simpa using hab⟩, Fin.castSucc_injective (n + 1)⟩

@[simp] lemma pathPrefixCopy_apply (n : ℕ) (i : Fin (n + 1)) :
    pathPrefixCopy n i = Fin.castSucc i := rfl

/-- Restriction of a rooted path copy to its initial subpath. -/
def rootedPathPrefix {V : Type*} [Fintype V] {n : ℕ} {Q : SimpleGraph V} {v : V}
    (f : RootedPathCopy (n + 1) Q v) : RootedPathCopy n Q v :=
  ⟨f.1.comp (pathPrefixCopy n), by simpa using f.2⟩

@[simp] lemma rootedPathPrefix_apply {V : Type*} [Fintype V] {n : ℕ}
    {Q : SimpleGraph V} {v : V} (f : RootedPathCopy (n + 1) Q v)
    (i : Fin (n + 1)) : (rootedPathPrefix f).1 i = f.1 (Fin.castSucc i) := rfl

/-- The new last vertex in the one-edge extension of a rooted path copy. -/
def rootedPathLast {V : Type*} [Fintype V] {n : ℕ} {Q : SimpleGraph V} {v : V}
    (f : RootedPathCopy (n + 1) Q v) :
    Q.neighborSet ((rootedPathPrefix f).1 (Fin.last n)) := by
  refine ⟨f.1 (Fin.last (n + 1)), ?_⟩
  apply f.1.toHom.map_rel'
  rw [SimpleGraph.pathGraph_adj]
  left
  simp

@[simp] lemma rootedPathLast_val {V : Type*} [Fintype V] {n : ℕ}
    {Q : SimpleGraph V} {v : V} (f : RootedPathCopy (n + 1) Q v) :
    (rootedPathLast f).1 = f.1 (Fin.last (n + 1)) := rfl

/-- A rooted copy of a path extended by one edge is determined by its prefix and last image. -/
def rootedPathStepEmbedding {V : Type*} [Fintype V] {n : ℕ}
    {Q : SimpleGraph V} {v : V} :
    RootedPathCopy (n + 1) Q v ↪
      (Σ p : RootedPathCopy n Q v, Q.neighborSet (p.1 (Fin.last n))) where
  toFun f := ⟨rootedPathPrefix f, rootedPathLast f⟩
  inj' := by
    intro f g h
    have hp : rootedPathPrefix f = rootedPathPrefix g := congr_arg Sigma.fst h
    have hl : (rootedPathLast f).1 = (rootedPathLast g).1 :=
      congr_arg (fun z ↦ z.2.1) h
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro i
    cases i using Fin.lastCases with
    | last => simpa using hl
    | cast j =>
        have := congr_arg (fun p : RootedPathCopy n Q v ↦ p.1 j) hp
        simpa using this

/-- In a graph of maximum degree at most `D`, at most `D^n` rooted copies of an
`n`-edge path can start at a fixed vertex. -/
lemma card_rootedPathCopy_le_pow {V : Type*} [Fintype V] (Q : SimpleGraph V)
    (D : ℕ) (hdeg : Q.maxDegree ≤ D) (v : V) :
    ∀ n : ℕ, Fintype.card (RootedPathCopy n Q v) ≤ D ^ n := by
  intro n
  induction n with
  | zero =>
      let e : RootedPathCopy 0 Q v ↪ Fin 1 :=
        ⟨fun _ ↦ 0, by
          intro f g _
          apply Subtype.ext
          apply SimpleGraph.Copy.ext
          intro i
          have hi : i = 0 := Fin.ext (by omega)
          subst i
          exact f.2.trans g.2.symm⟩
      simpa using Fintype.card_le_of_injective e e.injective
  | succ n ih =>
      calc
        Fintype.card (RootedPathCopy (n + 1) Q v) ≤
            Fintype.card (Σ p : RootedPathCopy n Q v,
              Q.neighborSet (p.1 (Fin.last n))) :=
          Fintype.card_le_of_injective rootedPathStepEmbedding
            rootedPathStepEmbedding.injective
        _ = ∑ p : RootedPathCopy n Q v, Q.degree (p.1 (Fin.last n)) := by
          rw [Fintype.card_sigma]
          apply Finset.sum_congr rfl
          intro p _
          exact Q.card_neighborSet_eq_degree _
        _ ≤ ∑ _p : RootedPathCopy n Q v, D := by
          apply Finset.sum_le_sum
          intro p _
          exact (Q.degree_le_maxDegree _).trans hdeg
        _ = Fintype.card (RootedPathCopy n Q v) * D := by simp [Nat.mul_comm]
        _ ≤ D ^ n * D := Nat.mul_le_mul_right D ih
        _ = D ^ (n + 1) := by rw [pow_succ]

/-! ## Compatible matching permutations -/

/-- The first path vertex, written with an explicit proof that the half-size is positive. -/
def firstVertex (K : ℕ) (hK : 0 < K) : Fin (K + K) := ⟨0, by omega⟩

/-- Rooted copies of the `2K`-vertex path, in the form used by the components. -/
def LongRootedPathCopy {V : Type*} [Fintype V] (K : ℕ) (hK : 0 < K)
    (Q : SimpleGraph V) (v : V) :=
  {f : (SimpleGraph.pathGraph (K + K)).Copy Q // f (firstVertex K hK) = v}

noncomputable instance longRootedPathCopyFintype {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (v : V) :
    Fintype (LongRootedPathCopy K hK Q v) :=
  inferInstanceAs (Fintype
    {f : (SimpleGraph.pathGraph (K + K)).Copy Q // f (firstVertex K hK) = v})

lemma card_startRootedPathCopy_le {V : Type*} [Fintype V] (L : ℕ) (hL : 0 < L)
    (Q : SimpleGraph V) (D : ℕ) (hdeg : Q.maxDegree ≤ D) (v : V) :
    Fintype.card {f : (SimpleGraph.pathGraph L).Copy Q // f ⟨0, hL⟩ = v} ≤
      D ^ (L - 1) := by
  cases L with
  | zero => omega
  | succ n =>
      let e :
          {f : (SimpleGraph.pathGraph (n + 1)).Copy Q // f ⟨0, hL⟩ = v} ≃
            RootedPathCopy n Q v := {
        toFun := fun f => ⟨f.1, by simpa [RootedPathCopy] using f.2⟩
        invFun := fun f => ⟨f.1, by simpa [RootedPathCopy] using f.2⟩
        left_inv := by
          intro f
          apply Subtype.ext
          rfl
        right_inv := by
          intro f
          apply Subtype.ext
          rfl
      }
      rw [Fintype.card_congr e]
      simpa only [Nat.succ_sub_one] using card_rootedPathCopy_le_pow Q D hdeg v n

lemma card_longRootedPathCopy_le {V : Type*} [Fintype V] (K : ℕ) (hK : 0 < K)
    (Q : SimpleGraph V) (D : ℕ) (hdeg : Q.maxDegree ≤ D) (v : V) :
    Fintype.card (LongRootedPathCopy K hK Q v) ≤ D ^ (K + K - 1) := by
  have hL : 0 < K + K := by omega
  let e : LongRootedPathCopy K hK Q v ≃
      {f : (SimpleGraph.pathGraph (K + K)).Copy Q // f ⟨0, hL⟩ = v} := {
    toFun := fun f => ⟨f.1, by simpa [firstVertex] using f.2⟩
    invFun := fun f => ⟨f.1, by simpa [firstVertex] using f.2⟩
    left_inv := by
      intro f
      apply Subtype.ext
      rfl
    right_inv := by
      intro f
      apply Subtype.ext
      rfl
  }
  rw [Fintype.card_congr e]
  exact card_startRootedPathCopy_le (K + K) hL Q D hdeg v

/-- An ordered pair of path positions whose images under `p` are adjacent in the host. -/
def CopyGoodPair {V : Type*} [Fintype V] {L : ℕ} (Q : SimpleGraph V)
    (p : (SimpleGraph.pathGraph L).Copy Q) :=
  Σ a : Fin L, {b : Fin L // Q.Adj (p a) (p b)}

noncomputable instance copyGoodPairFintype {V : Type*} [Fintype V] {L : ℕ}
    (Q : SimpleGraph V) (p : (SimpleGraph.pathGraph L).Copy Q) :
    Fintype (CopyGoodPair Q p) :=
  inferInstanceAs (Fintype (Σ a : Fin L, {b : Fin L // Q.Adj (p a) (p b)}))

lemma card_copyGoodPair_le {V : Type*} [Fintype V] {L D : ℕ}
    (Q : SimpleGraph V) (p : (SimpleGraph.pathGraph L).Copy Q)
    (hdeg : Q.maxDegree ≤ D) :
    Fintype.card (CopyGoodPair Q p) ≤ L * D := by
  change Fintype.card (Σ a : Fin L, {b : Fin L // Q.Adj (p a) (p b)}) ≤ L * D
  rw [Fintype.card_sigma]
  calc
    (∑ a : Fin L, Fintype.card {b : Fin L // Q.Adj (p a) (p b)}) ≤
        ∑ _a : Fin L, D := by
      apply Finset.sum_le_sum
      intro a _
      let e : {b : Fin L // Q.Adj (p a) (p b)} ↪ Q.neighborSet (p a) :=
        ⟨fun b ↦ ⟨p b.1, b.2⟩, by
          intro b c h
          apply Subtype.ext
          exact p.injective (congr_arg Subtype.val h)⟩
      calc
        Fintype.card {b : Fin L // Q.Adj (p a) (p b)} ≤
            Fintype.card (Q.neighborSet (p a)) :=
          Fintype.card_le_of_injective e e.injective
        _ = Q.degree (p a) := Q.card_neighborSet_eq_degree _
        _ ≤ D := (Q.degree_le_maxDegree _).trans hdeg
    _ = L * D := by simp

/-- Permutations whose matching pairs are all sent to host edges by the path copy `p`. -/
def CompatiblePerm {V : Type*} [Fintype V] (K : ℕ) (Q : SimpleGraph V)
    (p : (SimpleGraph.pathGraph (K + K)).Copy Q) :=
  {σ : Equiv.Perm (Fin (K + K)) //
    ∀ i : Fin K, Q.Adj (p (σ (Fin.castAdd K i))) (p (σ (Fin.natAdd K i)))}

noncomputable instance compatiblePermFintype {V : Type*} [Fintype V]
    (K : ℕ) (Q : SimpleGraph V) (p : (SimpleGraph.pathGraph (K + K)).Copy Q) :
    Fintype (CompatiblePerm K Q p) :=
  inferInstanceAs (Fintype {σ : Equiv.Perm (Fin (K + K)) //
    ∀ i : Fin K, Q.Adj (p (σ (Fin.castAdd K i))) (p (σ (Fin.natAdd K i)))})

/-- Record, for every matching edge, its two path positions.  This record determines
the permutation. -/
def compatiblePermEmbedding {V : Type*} [Fintype V] (K : ℕ) (Q : SimpleGraph V)
    (p : (SimpleGraph.pathGraph (K + K)).Copy Q) :
    CompatiblePerm K Q p ↪ (Fin K → CopyGoodPair Q p) where
  toFun σ i := ⟨σ.1 (Fin.castAdd K i),
    ⟨σ.1 (Fin.natAdd K i), σ.2 i⟩⟩
  inj' := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    refine Fin.addCases (m := K) (n := K) (fun i ↦ ?_) (fun i ↦ ?_) x
    · have hi := congr_fun h i
      exact congr_arg Sigma.fst hi
    · have hi := congr_fun h i
      exact congr_arg (fun z ↦ z.2.1) hi

lemma card_compatiblePerm_le {V : Type*} [Fintype V] (K D : ℕ)
    (Q : SimpleGraph V) (p : (SimpleGraph.pathGraph (K + K)).Copy Q)
    (hdeg : Q.maxDegree ≤ D) :
    Fintype.card (CompatiblePerm K Q p) ≤ ((K + K) * D) ^ K := by
  calc
    Fintype.card (CompatiblePerm K Q p) ≤
        Fintype.card (Fin K → CopyGoodPair Q p) :=
      Fintype.card_le_of_injective (compatiblePermEmbedding K Q p)
        (compatiblePermEmbedding K Q p).injective
    _ = Fintype.card (CopyGoodPair Q p) ^ K := by simp
    _ ≤ ((K + K) * D) ^ K :=
      Nat.pow_le_pow_left (card_copyGoodPair_le Q p hdeg) K

/-! ## Root scarcity for the component family -/

/-- Copies of one component with its distinguished first path vertex sent to `v`. -/
def RootedComponentCopy {V : Type*} [Fintype V] (K : ℕ) (hK : 0 < K)
    (Q : SimpleGraph V) (v : V) (σ : Equiv.Perm (Fin (K + K))) :=
  {f : (componentGraph K σ).Copy Q // f (firstVertex K hK) = v}

noncomputable instance rootedComponentCopyFintype {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (v : V)
    (σ : Equiv.Perm (Fin (K + K))) : Fintype (RootedComponentCopy K hK Q v σ) :=
  inferInstanceAs (Fintype
    {f : (componentGraph K σ).Copy Q // f (firstVertex K hK) = v})

/-- Forget the matching edges in a rooted component copy. -/
def rootedComponentPath {V : Type*} [Fintype V] {K : ℕ} {hK : 0 < K}
    {Q : SimpleGraph V} {v : V} {σ : Equiv.Perm (Fin (K + K))}
    (f : RootedComponentCopy K hK Q v σ) : LongRootedPathCopy K hK Q v :=
  ⟨f.1.comp (SimpleGraph.Copy.ofLE _ _ le_sup_left), by
    change f.1 (firstVertex K hK) = v
    exact f.2⟩

@[simp] lemma rootedComponentPath_apply {V : Type*} [Fintype V] {K : ℕ}
    {hK : 0 < K} {Q : SimpleGraph V} {v : V}
    {σ : Equiv.Perm (Fin (K + K))} (f : RootedComponentCopy K hK Q v σ)
    (i : Fin (K + K)) : (rootedComponentPath f).1 i = f.1 i := rfl

/-- The permutation of a component copy is compatible with its underlying path copy. -/
def rootedComponentCompatible {V : Type*} [Fintype V] {K : ℕ} {hK : 0 < K}
    {Q : SimpleGraph V} {v : V} {σ : Equiv.Perm (Fin (K + K))}
    (f : RootedComponentCopy K hK Q v σ) :
    CompatiblePerm K Q (rootedComponentPath f).1 :=
  ⟨σ, fun i ↦ by
    change Q.Adj (f.1 (σ (Fin.castAdd K i))) (f.1 (σ (Fin.natAdd K i)))
    apply f.1.toHom.map_rel'
    exact Or.inr (matchingGraph_adj_iff.mpr (Or.inl ⟨i, rfl, rfl⟩))⟩

/-- The permutations whose rooted component has a copy at `v`. -/
def RootSupportedPerm {V : Type*} [Fintype V] (K : ℕ) (hK : 0 < K)
    (Q : SimpleGraph V) (v : V) :=
  {σ : Equiv.Perm (Fin (K + K)) // Nonempty (RootedComponentCopy K hK Q v σ)}

noncomputable instance rootSupportedPermFintype {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (v : V) :
    Fintype (RootSupportedPerm K hK Q v) :=
  inferInstanceAs (Fintype {σ : Equiv.Perm (Fin (K + K)) //
    Nonempty (RootedComponentCopy K hK Q v σ)})

/-- Choose one rooted copy for each supported permutation. -/
noncomputable def chosenRootedComponent {V : Type*} [Fintype V]
    {K : ℕ} {hK : 0 < K} {Q : SimpleGraph V} {v : V}
    (σ : RootSupportedPerm K hK Q v) : RootedComponentCopy K hK Q v σ.1 :=
  Classical.choice σ.2

/-- Encode a supported permutation by its rooted path copy and compatible matching record. -/
noncomputable def rootSupportedPermEmbedding {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (v : V) :
    RootSupportedPerm K hK Q v ↪
      (Σ p : LongRootedPathCopy K hK Q v, CompatiblePerm K Q p.1) where
  toFun σ :=
    ⟨rootedComponentPath (chosenRootedComponent σ),
      rootedComponentCompatible (chosenRootedComponent σ)⟩
  inj' := by
    intro σ τ h
    apply Subtype.ext
    exact congr_arg (fun z ↦ z.2.1) h

/-- Root scarcity: in a degree-`D` host, a fixed vertex can root only the stated
number of the factorially many components. -/
lemma card_rootSupportedPerm_le {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (D : ℕ)
    (hdeg : Q.maxDegree ≤ D) (v : V) :
    Fintype.card (RootSupportedPerm K hK Q v) ≤
      D ^ (K + K - 1) * (((K + K) * D) ^ K) := by
  calc
    Fintype.card (RootSupportedPerm K hK Q v) ≤
        Fintype.card (Σ p : LongRootedPathCopy K hK Q v,
          CompatiblePerm K Q p.1) :=
      Fintype.card_le_of_injective (rootSupportedPermEmbedding K hK Q v)
        (rootSupportedPermEmbedding K hK Q v).injective
    _ = ∑ p : LongRootedPathCopy K hK Q v,
          Fintype.card (CompatiblePerm K Q p.1) := by rw [Fintype.card_sigma]
    _ ≤ ∑ _p : LongRootedPathCopy K hK Q v, (((K + K) * D) ^ K) := by
      apply Finset.sum_le_sum
      intro p _
      exact card_compatiblePerm_le K D Q p.1 hdeg
    _ = Fintype.card (LongRootedPathCopy K hK Q v) * (((K + K) * D) ^ K) := by
      simp [Nat.mul_comm]
    _ ≤ D ^ (K + K - 1) * (((K + K) * D) ^ K) :=
      Nat.mul_le_mul_right _ (card_longRootedPathCopy_le K hK Q D hdeg v)

/-! ## The factorial margin -/

lemma factorial_margin_of {C D K : ℕ} (hK : 0 < K) (hD : 0 < D)
    (hfac : 16 * C * D * (4 * D * D * D) ^ K < Nat.factorial K) :
    8 * C * (K + K) * D *
        (D ^ (K + K - 1) * (((K + K) * D) ^ K)) < Nat.factorial (K + K) := by
  have hDpow : D ^ (K + K - 1) ≤ D ^ (K + K) :=
    Nat.pow_le_pow_right hD (Nat.sub_le _ _)
  have hKpow : K ≤ 2 ^ K := K.lt_two_pow_self.le
  calc
    8 * C * (K + K) * D *
        (D ^ (K + K - 1) * (((K + K) * D) ^ K))
        ≤ 8 * C * (K + K) * D *
            (D ^ (K + K) * (((K + K) * D) ^ K)) := by gcongr
    _ = (16 * C * D * K) * K ^ K * (2 * D * D * D) ^ K := by
      simp only [mul_pow, pow_add]
      ring
    _ ≤ (16 * C * D * (2 ^ K)) * K ^ K * (2 * D * D * D) ^ K := by
      gcongr
    _ = (16 * C * D * (4 * D * D * D) ^ K) * K ^ K := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      simp only [mul_pow]
      ring
    _ < Nat.factorial K * K ^ K :=
      Nat.mul_lt_mul_of_pos_right hfac (Nat.pow_pos hK)
    _ ≤ Nat.factorial K * (K + 1) ^ K := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ K) K)
    _ ≤ Nat.factorial (K + K) := by
      simpa only using
        (Nat.factorial_mul_pow_le_factorial (m := K) (n := K))

/-- For every proposed linear constant there is a positive half-size for which the
factorially many components dominate the root-scarcity error term. -/
lemma exists_factorial_margin (C : ℕ) :
    ∃ K : ℕ, 0 < K ∧
      let D := 16 * (C + 1)
      8 * C * (K + K) * D *
          (D ^ (K + K - 1) * (((K + K) * D) ^ K)) < Nat.factorial (K + K) := by
  let D := 16 * (C + 1)
  have hD : 0 < D := by simp [D]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Nat.eventually_mul_pow_lt_factorial_sub
      (16 * C * D) (4 * D * D * D) 0)
  let K := max N 1
  have hK : 0 < K := by simp [K]
  have hfac : 16 * C * D * (4 * D * D * D) ^ K < Nat.factorial K := by
    simpa using hN K (le_max_left _ _)
  exact ⟨K, hK, by
    dsimp only
    exact factorial_margin_of hK hD hfac⟩

/-! ## Low-degree hosts and handshaking bounds -/

lemma edgeCount_mono {V : Type*} [Finite V] {G H : SimpleGraph V} (hGH : G ≤ H) :
    edgeCount G ≤ edgeCount H := by
  let _ : Fintype V := Fintype.ofFinite V
  classical
  rw [edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset]
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)

/-- Delete every edge having an endpoint whose degree in `H` is greater than `D`. -/
def lowGraph {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ H.degree u ≤ D ∧ H.degree v ≤ D
  symm.symm _u _v h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _u h := h.1.ne rfl

lemma lowGraph_le {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) :
    lowGraph H D ≤ H := fun _ _ h ↦ h.1

lemma lowGraph_maxDegree_le {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) :
    (lowGraph H D).maxDegree ≤ D := by
  apply (lowGraph H D).maxDegree_le_of_forall_degree_le D
  intro v
  by_cases hv : H.degree v ≤ D
  · have hsub : (lowGraph H D).neighborFinset v ⊆ H.neighborFinset v := by
      intro w hw
      have hw' : (lowGraph H D).Adj v w := by simpa using hw
      simpa using hw'.1
    exact (Finset.card_le_card hsub).trans hv
  · have hempty : (lowGraph H D).neighborFinset v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hw' : (lowGraph H D).Adj v w := by simpa using hw
      exact hv hw'.2.1
    simp [← SimpleGraph.card_neighborFinset_eq_degree, hempty]

/-- The vertices deleted when passing to `lowGraph`. -/
def highVertices {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ D < H.degree v

lemma highVertices_spec {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) (v : V) :
    v ∈ highVertices H D ↔ D < H.degree v := by simp [highVertices]

/-- Handshaking bounds the number of vertices of degree greater than `D`. -/
lemma mul_card_highVertices_le {V : Type*} [Fintype V]
    (H : SimpleGraph V) (D : ℕ) :
    D * (highVertices H D).card ≤ 2 * edgeCount H := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  calc
    D * (highVertices H D).card = ∑ _v ∈ highVertices H D, D := by
      simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highVertices H D, H.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (highVertices_spec H D v).mp hv |>.le
    _ ≤ ∑ v : V, H.degree v := by
      apply Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges

lemma card_support_le_twice_edgeCount {V : Type*} [Fintype V] (H : SimpleGraph V) :
    H.support.toFinset.card ≤ 2 * edgeCount H := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  calc
    H.support.toFinset.card = ∑ _v ∈ H.support, 1 := by simp
    _ ≤ ∑ v ∈ H.support, H.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (H.degree_pos_iff_mem_support v).mpr (by simpa using hv)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_support_eq_twice_card_edges

/-! ## Incidences between components and possible roots -/

def secondVertex (K : ℕ) (hK : 0 < K) : Fin (K + K) := ⟨1, by omega⟩

lemma rootedComponentRoot_mem_support {V : Type*} [Fintype V]
    {K : ℕ} {hK : 0 < K} {Q : SimpleGraph V} {v : V}
    {σ : Equiv.Perm (Fin (K + K))}
    (h : Nonempty (RootedComponentCopy K hK Q v σ)) : v ∈ Q.support := by
  obtain ⟨f⟩ := h
  have hadjSource :
      (componentGraph K σ).Adj (firstVertex K hK) (secondVertex K hK) := by
    left
    rw [SimpleGraph.pathGraph_adj]
    left
    rfl
  have hadj := f.1.toHom.map_rel' hadjSource
  change Q.Adj (f.1 (firstVertex K hK)) (f.1 (secondVertex K hK)) at hadj
  rw [f.2] at hadj
  exact hadj.mem_support_left

/-- Possible root images for one fixed component. -/
def ComponentRoot {V : Type*} [Fintype V] (K : ℕ) (hK : 0 < K)
    (Q : SimpleGraph V) (σ : Equiv.Perm (Fin (K + K))) :=
  {v : V // Nonempty (RootedComponentCopy K hK Q v σ)}

noncomputable instance componentRootFintype {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V)
    (σ : Equiv.Perm (Fin (K + K))) : Fintype (ComponentRoot K hK Q σ) :=
  inferInstanceAs (Fintype {v : V // Nonempty (RootedComponentCopy K hK Q v σ)})

/-- Swap the order of summation in the component/root incidence relation. -/
noncomputable def rootIncidenceEquiv {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) :
    (Σ σ : Equiv.Perm (Fin (K + K)), ComponentRoot K hK Q σ) ≃
      (Σ v : Q.support, RootSupportedPerm K hK Q v.1) where
  toFun x :=
    ⟨⟨x.2.1, rootedComponentRoot_mem_support x.2.2⟩, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1.1, x.2.2⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

lemma card_rootIncidence_le {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (D : ℕ)
    (hdeg : Q.maxDegree ≤ D) :
    Fintype.card (Σ σ : Equiv.Perm (Fin (K + K)), ComponentRoot K hK Q σ) ≤
      2 * edgeCount Q *
        (D ^ (K + K - 1) * (((K + K) * D) ^ K)) := by
  let r := D ^ (K + K - 1) * (((K + K) * D) ^ K)
  calc
    Fintype.card (Σ σ : Equiv.Perm (Fin (K + K)), ComponentRoot K hK Q σ) =
        Fintype.card (Σ v : Q.support, RootSupportedPerm K hK Q v.1) :=
      Fintype.card_congr (rootIncidenceEquiv K hK Q)
    _ = ∑ v : Q.support, Fintype.card (RootSupportedPerm K hK Q v.1) := by
      rw [Fintype.card_sigma]
    _ ≤ ∑ _v : Q.support, r := by
      apply Finset.sum_le_sum
      intro v _
      exact card_rootSupportedPerm_le K hK Q D hdeg v.1
    _ = Fintype.card Q.support * r := by simp [Nat.mul_comm]
    _ ≤ (2 * edgeCount Q) * r := by
      apply Nat.mul_le_mul_right r
      simpa only [Set.toFinset_card] using card_support_le_twice_edgeCount Q
    _ = 2 * edgeCount Q *
        (D ^ (K + K - 1) * (((K + K) * D) ^ K)) := rfl

lemma exists_card_mul_le_of_sum_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℕ) (S : ℕ) (h : ∑ a, f a ≤ S) :
    ∃ a : α, Fintype.card α * f a ≤ S := by
  by_contra! hn
  have hlt : (∑ _a : α, S) < ∑ a : α, Fintype.card α * f a := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro a _
    exact hn a
  have hlt' : Fintype.card α * S < Fintype.card α * ∑ a : α, f a := by
    simpa [Finset.mul_sum] using hlt
  have hle : Fintype.card α * ∑ a : α, f a ≤ Fintype.card α * S :=
    Nat.mul_le_mul_left _ h
  omega

/-- Some component has few possible roots in the low-degree graph. -/
lemma exists_component_with_few_roots {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V) (D : ℕ)
    (hdeg : Q.maxDegree ≤ D) :
    ∃ σ : Equiv.Perm (Fin (K + K)),
      Nat.factorial (K + K) * Fintype.card (ComponentRoot K hK Q σ) ≤
        2 * edgeCount Q *
          (D ^ (K + K - 1) * (((K + K) * D) ^ K)) := by
  have hsum :
      (∑ σ : Equiv.Perm (Fin (K + K)), Fintype.card (ComponentRoot K hK Q σ)) ≤
        2 * edgeCount Q *
          (D ^ (K + K - 1) * (((K + K) * D) ^ K)) := by
    rw [← Fintype.card_sigma]
    exact card_rootIncidence_le K hK Q D hdeg
  obtain ⟨σ, hσ⟩ := exists_card_mul_le_of_sum_le
    (fun σ : Equiv.Perm (Fin (K + K)) ↦ Fintype.card (ComponentRoot K hK Q σ)) _ hsum
  refine ⟨σ, ?_⟩
  simpa only [Fintype.card_perm, Fintype.card_fin] using hσ

/-! ## The adversarial colouring -/

/-- The vertices which can be images of the root of component `σ`. -/
noncomputable def componentRootFinset {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V)
    (σ : Equiv.Perm (Fin (K + K))) : Finset V :=
  Finset.univ.filter fun v ↦ Nonempty (RootedComponentCopy K hK Q v σ)

@[simp] lemma mem_componentRootFinset {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V)
    (σ : Equiv.Perm (Fin (K + K))) (v : V) :
    v ∈ componentRootFinset K hK Q σ ↔
      Nonempty (RootedComponentCopy K hK Q v σ) := by
  simp [componentRootFinset]

lemma card_componentRootFinset {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (Q : SimpleGraph V)
    (σ : Equiv.Perm (Fin (K + K))) :
    (componentRootFinset K hK Q σ).card = Fintype.card (ComponentRoot K hK Q σ) := by
  symm
  exact Fintype.card_subtype _

/-- Keep precisely the edges of `H` incident with `A`. -/
def incidentGraph {V : Type*} (H : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ (u ∈ A ∨ v ∈ A)
  symm.symm _u _v h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _u h := h.1.ne rfl

lemma incidentGraph_le {V : Type*} (H : SimpleGraph V) (A : Set V) :
    incidentGraph H A ≤ H := fun _ _ h ↦ h.1

/-- Red consists of all host edges incident with a high-degree vertex or a possible
root of the selected component. -/
def redGraph {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) (A : Finset V) :
    SimpleGraph V :=
  incidentGraph H (↑(highVertices H D ∪ A) : Set V)

lemma redGraph_le {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ) (A : Finset V) :
    redGraph H D A ≤ H := incidentGraph_le _ _

lemma redGraph_adj_iff {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ)
    (A : Finset V) {u v : V} :
    (redGraph H D A).Adj u v ↔ H.Adj u v ∧
      (D < H.degree u ∨ u ∈ A ∨ D < H.degree v ∨ v ∈ A) := by
  simp only [redGraph, incidentGraph, Finset.mem_coe,
    Finset.mem_union, highVertices_spec]
  tauto

lemma blue_le_lowGraph {V : Type*} [Fintype V]
    (H : SimpleGraph V) (D : ℕ) (A : Finset V) :
    H \ redGraph H D A ≤ lowGraph H D := by
  intro u v huv
  rw [SimpleGraph.sdiff_adj] at huv
  refine ⟨huv.1, ?_, ?_⟩
  · apply Nat.le_of_not_lt
    intro hu
    exact huv.2 ((redGraph_adj_iff H D A).mpr ⟨huv.1, Or.inl hu⟩)
  · apply Nat.le_of_not_lt
    intro hv
    exact huv.2 ((redGraph_adj_iff H D A).mpr ⟨huv.1, Or.inr (Or.inr (Or.inl hv))⟩)

/-- The canonical copy of one labelled component in the disjoint union. -/
def targetComponentCopy (K : ℕ) (σ : Equiv.Perm (Fin (K + K))) :
    (componentGraph K σ).Copy (targetGraph K) :=
  ⟨⟨fun i ↦ (σ, i), by
      intro u v huv
      exact ⟨rfl, huv⟩⟩, by
    intro u v h
    exact congr_arg Prod.snd h⟩

/-- Blue cannot contain the selected component, hence cannot contain the whole target. -/
lemma target_not_isContained_blue {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (H : SimpleGraph V) (D : ℕ)
    (σ : Equiv.Perm (Fin (K + K)))
    (Q : SimpleGraph V) (hQ : Q = lowGraph H D)
    (A : Finset V) (hA : A = componentRootFinset K hK Q σ) :
    ¬ targetGraph K ⊑ (H \ redGraph H D A) := by
  rintro ⟨f⟩
  let pBlue : (componentGraph K σ).Copy (H \ redGraph H D A) :=
    f.comp (targetComponentCopy K σ)
  let pLow : (componentGraph K σ).Copy (lowGraph H D) :=
    (SimpleGraph.Copy.ofLE _ _ (blue_le_lowGraph H D A)).comp pBlue
  let v := pLow (firstVertex K hK)
  have hrootQ : Nonempty (RootedComponentCopy K hK Q v σ) := by
    subst Q
    exact ⟨⟨pLow, rfl⟩⟩
  have hvA : v ∈ A := by
    subst A
    exact (mem_componentRootFinset K hK Q σ v).mpr hrootQ
  have hadjSource :
      (componentGraph K σ).Adj (firstVertex K hK) (secondVertex K hK) := by
    left
    rw [SimpleGraph.pathGraph_adj]
    left
    rfl
  have hblue := pBlue.toHom.map_rel' hadjSource
  rw [SimpleGraph.sdiff_adj] at hblue
  apply hblue.2
  apply (redGraph_adj_iff H D A).mpr
  refine ⟨hblue.1, Or.inr (Or.inl ?_)⟩
  exact hvA

/-! ## A red copy would force too many high-degree vertices -/

def BadComponent {V : Type*} [Fintype V] (K : ℕ) (H : SimpleGraph V) (D : ℕ)
    (A : Finset V) (f : (targetGraph K).Copy (redGraph H D A)) :=
  {σ : Equiv.Perm (Fin (K + K)) // ∃ i : Fin K,
    f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
    f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D}

noncomputable instance badComponentFintype {V : Type*} [Fintype V]
    (K : ℕ) (H : SimpleGraph V) (D : ℕ) (A : Finset V)
    (f : (targetGraph K).Copy (redGraph H D A)) :
    Fintype (BadComponent K H D A f) :=
  inferInstanceAs (Fintype {σ : Equiv.Perm (Fin (K + K)) // ∃ i : Fin K,
    f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
    f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D})

noncomputable def badWitnessIndex {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (σ : BadComponent K H D A f) : Fin K := Classical.choose σ.2

lemma badWitnessIndex_spec {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (σ : BadComponent K H D A f) :
    f (σ.1, σ.1 (Fin.castAdd K (badWitnessIndex σ))) ∉ highVertices H D ∧
    f (σ.1, σ.1 (Fin.natAdd K (badWitnessIndex σ))) ∉ highVertices H D :=
  Classical.choose_spec σ.2

noncomputable def badChosenSource {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (σ : BadComponent K H D A f) :
    Equiv.Perm (Fin (K + K)) × Fin (K + K) :=
  let i := badWitnessIndex σ
  let left := (σ.1, σ.1 (Fin.castAdd K i))
  let right := (σ.1, σ.1 (Fin.natAdd K i))
  if f left ∈ A then left else right

@[simp] lemma badChosenSource_fst {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (σ : BadComponent K H D A f) : (badChosenSource σ).1 = σ.1 := by
  simp only [badChosenSource]
  split_ifs <;> rfl

lemma badChosenSource_image_mem {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (σ : BadComponent K H D A f) : f (badChosenSource σ) ∈ A := by
  let i := badWitnessIndex σ
  let left : Equiv.Perm (Fin (K + K)) × Fin (K + K) :=
    (σ.1, σ.1 (Fin.castAdd K i))
  let right : Equiv.Perm (Fin (K + K)) × Fin (K + K) :=
    (σ.1, σ.1 (Fin.natAdd K i))
  have hadjSource : (targetGraph K).Adj left right := by
    refine ⟨rfl, Or.inr ?_⟩
    exact matchingGraph_adj_iff.mpr (Or.inl ⟨i, rfl, rfl⟩)
  have hred := f.toHom.map_rel' hadjSource
  have hcases := (redGraph_adj_iff H D A).mp hred |>.2
  have hnleft : ¬D < H.degree (f left) := by
    simpa only [← highVertices_spec H D] using (badWitnessIndex_spec σ).1
  have hnright : ¬D < H.degree (f right) := by
    simpa only [← highVertices_spec H D] using (badWitnessIndex_spec σ).2
  change f (if f left ∈ A then left else right) ∈ A
  split_ifs with hleft
  · exact hleft
  · tauto

/-- A bad component chooses a distinct possible-root vertex in `A`. -/
noncomputable def badComponentEmbedding {V : Type*} [Fintype V]
    (K : ℕ) (H : SimpleGraph V) (D : ℕ) (A : Finset V)
    (f : (targetGraph K).Copy (redGraph H D A)) :
    BadComponent K H D A f ↪ A where
  toFun σ := ⟨f (badChosenSource σ), badChosenSource_image_mem σ⟩
  inj' := by
    intro σ τ h
    apply Subtype.ext
    have himage : f (badChosenSource σ) = f (badChosenSource τ) :=
      congr_arg Subtype.val h
    have hsource := f.injective himage
    exact (badChosenSource_fst σ).symm.trans
      ((congr_arg Prod.fst hsource).trans (badChosenSource_fst τ))

def GoodComponent {V : Type*} [Fintype V] (K : ℕ) (H : SimpleGraph V) (D : ℕ)
    (A : Finset V) (f : (targetGraph K).Copy (redGraph H D A)) :=
  {σ : Equiv.Perm (Fin (K + K)) // ¬∃ i : Fin K,
    f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
    f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D}

noncomputable instance goodComponentFintype {V : Type*} [Fintype V]
    (K : ℕ) (H : SimpleGraph V) (D : ℕ) (A : Finset V)
    (f : (targetGraph K).Copy (redGraph H D A)) :
    Fintype (GoodComponent K H D A f) :=
  inferInstanceAs (Fintype {σ : Equiv.Perm (Fin (K + K)) // ¬∃ i : Fin K,
    f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
    f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D})

lemma goodComponent_matching_high {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (σ : GoodComponent K H D A f) (i : Fin K) :
    f (σ.1, σ.1 (Fin.castAdd K i)) ∈ highVertices H D ∨
    f (σ.1, σ.1 (Fin.natAdd K i)) ∈ highVertices H D := by
  by_contra hn
  rw [not_or] at hn
  exact σ.2 ⟨i, hn.1, hn.2⟩

noncomputable def goodHighSource {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (x : GoodComponent K H D A f × Fin K) :
    Equiv.Perm (Fin (K + K)) × Fin (K + K) :=
  let σ := x.1.1
  let i := x.2
  let left := (σ, σ (Fin.castAdd K i))
  let right := (σ, σ (Fin.natAdd K i))
  if f left ∈ highVertices H D then left else right

@[simp] lemma goodHighSource_fst {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (x : GoodComponent K H D A f × Fin K) :
    (goodHighSource x).1 = x.1.1 := by
  simp only [goodHighSource]
  split_ifs <;> rfl

lemma goodHighSource_image_mem {V : Type*} [Fintype V]
    {K : ℕ} {H : SimpleGraph V} {D : ℕ} {A : Finset V}
    {f : (targetGraph K).Copy (redGraph H D A)}
    (x : GoodComponent K H D A f × Fin K) :
    f (goodHighSource x) ∈ highVertices H D := by
  change f (if f (x.1.1, x.1.1 (Fin.castAdd K x.2)) ∈ highVertices H D then
      (x.1.1, x.1.1 (Fin.castAdd K x.2))
    else (x.1.1, x.1.1 (Fin.natAdd K x.2))) ∈ highVertices H D
  split_ifs with h
  · exact h
  · exact (goodComponent_matching_high x.1 x.2).resolve_left h

/-- Distinct matching edges in distinct good components force distinct high vertices. -/
noncomputable def goodHighEmbedding {V : Type*} [Fintype V]
    (K : ℕ) (H : SimpleGraph V) (D : ℕ) (A : Finset V)
    (f : (targetGraph K).Copy (redGraph H D A)) :
    GoodComponent K H D A f × Fin K ↪ highVertices H D where
  toFun x := ⟨f (goodHighSource x), goodHighSource_image_mem x⟩
  inj' := by
    intro x y h
    have himage : f (goodHighSource x) = f (goodHighSource y) := congr_arg Subtype.val h
    have hsource := f.injective himage
    apply Prod.ext
    · apply Subtype.ext
      exact (goodHighSource_fst x).symm.trans
        ((congr_arg Prod.fst hsource).trans (goodHighSource_fst y))
    · apply Fin.ext
      have hσ : x.1.1 = y.1.1 :=
        (goodHighSource_fst x).symm.trans
          ((congr_arg Prod.fst hsource).trans (goodHighSource_fst y))
      have hpos := congr_arg Prod.snd hsource
      simp only [goodHighSource] at hpos
      rw [← hσ] at hpos
      split_ifs at hpos
      all_goals
        have hp := x.1.1.injective hpos
        have hv := congr_arg Fin.val hp
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega

lemma red_copy_forces_many_high {V : Type*} [Fintype V]
    (K : ℕ) (hK : 0 < K) (H : SimpleGraph V) (D : ℕ) (A : Finset V)
    (f : (targetGraph K).Copy (redGraph H D A))
    (hsmall : 4 * A.card < Nat.factorial (K + K)) :
    Nat.factorial (K + K) * K < 2 * (highVertices H D).card := by
  have hbad : Fintype.card (BadComponent K H D A f) ≤ A.card :=
    by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective (badComponentEmbedding K H D A f)
          (badComponentEmbedding K H D A f).injective
  have hbad4 : 4 * Fintype.card (BadComponent K H D A f) <
      Nat.factorial (K + K) := (Nat.mul_le_mul_left 4 hbad).trans_lt hsmall
  have hgood : Fintype.card (GoodComponent K H D A f) =
      Nat.factorial (K + K) - Fintype.card (BadComponent K H D A f) := by
    change Fintype.card {σ : Equiv.Perm (Fin (K + K)) // ¬∃ i : Fin K,
        f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
        f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D} =
      Nat.factorial (K + K) -
        Fintype.card {σ : Equiv.Perm (Fin (K + K)) // ∃ i : Fin K,
          f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
          f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D}
    rw [Fintype.card_subtype_compl, Fintype.card_perm, Fintype.card_fin]
  have hgoodHalf : Nat.factorial (K + K) <
      2 * Fintype.card (GoodComponent K H D A f) := by
    have hbadle : Fintype.card (BadComponent K H D A f) ≤
        Nat.factorial (K + K) := by
      change Fintype.card {σ : Equiv.Perm (Fin (K + K)) // ∃ i : Fin K,
          f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
          f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D} ≤ Nat.factorial (K + K)
      simpa only [Fintype.card_perm, Fintype.card_fin] using
        Fintype.card_subtype_le (fun σ : Equiv.Perm (Fin (K + K)) ↦
          ∃ i : Fin K,
            f (σ, σ (Fin.castAdd K i)) ∉ highVertices H D ∧
            f (σ, σ (Fin.natAdd K i)) ∉ highVertices H D)
    omega
  have hforce : Fintype.card (GoodComponent K H D A f) * K ≤
      (highVertices H D).card := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective (goodHighEmbedding K H D A f)
        (goodHighEmbedding K H D A f).injective
  calc
    Nat.factorial (K + K) * K <
        (2 * Fintype.card (GoodComponent K H D A f)) * K :=
      Nat.mul_lt_mul_of_pos_right hgoodHalf hK
    _ = 2 * (Fintype.card (GoodComponent K H D A f) * K) := by ring
    _ ≤ 2 * (highVertices H D).card := Nat.mul_le_mul_left 2 hforce

/-! ## No sparse host is Ramsey for the constructed target -/

theorem target_not_ramsey_of_edgeCount_le {V : Type*} [Finite V]
    (C K : ℕ) (hK : 0 < K)
    (hmargin :
      let D := 16 * (C + 1)
      8 * C * (K + K) * D *
          (D ^ (K + K - 1) * (((K + K) * D) ^ K)) < Nat.factorial (K + K))
    (H : SimpleGraph V)
    (hedges : edgeCount H ≤
      C * Fintype.card (Equiv.Perm (Fin (K + K)) × Fin (K + K))) :
    ¬ IsRamseyFor H (targetGraph K) := by
  let _ : Fintype V := Fintype.ofFinite V
  let D := 16 * (C + 1)
  let Q := lowGraph H D
  let r := D ^ (K + K - 1) * (((K + K) * D) ^ K)
  have hQdeg : Q.maxDegree ≤ D := by
    exact lowGraph_maxDegree_le H D
  obtain ⟨σ, hσ⟩ := exists_component_with_few_roots K hK Q D hQdeg
  let A := componentRootFinset K hK Q σ
  have hAcard : A.card ≤ 2 * C * (K + K) * r := by
    have hQedges : edgeCount Q ≤ edgeCount H := by
      exact edgeCount_mono (by exact (lowGraph_le H D))
    have htargetCard :
        Fintype.card (Equiv.Perm (Fin (K + K)) × Fin (K + K)) =
          Nat.factorial (K + K) * (K + K) := targetGraph_card K
    have hprod : Nat.factorial (K + K) * A.card ≤
        Nat.factorial (K + K) * (2 * C * (K + K) * r) := by
      calc
        Nat.factorial (K + K) * A.card =
            Nat.factorial (K + K) * Fintype.card (ComponentRoot K hK Q σ) := by
          rw [card_componentRootFinset]
        _ ≤ 2 * edgeCount Q * r := hσ
        _ ≤ 2 * edgeCount H * r := by gcongr
        _ ≤ 2 * (C * (Nat.factorial (K + K) * (K + K))) * r := by
          rw [← htargetCard]
          gcongr
        _ = Nat.factorial (K + K) * (2 * C * (K + K) * r) := by ring
    exact le_of_mul_le_mul_left hprod (Nat.factorial_pos _)
  have hAsmall : 4 * A.card < Nat.factorial (K + K) := by
    calc
      4 * A.card ≤ 4 * (2 * C * (K + K) * r) := Nat.mul_le_mul_left 4 hAcard
      _ = 8 * C * (K + K) * r := by ring
      _ ≤ 8 * C * (K + K) * D * r := by
        have hDone : 1 ≤ D := by dsimp [D]; omega
        calc
          8 * C * (K + K) * r ≤ (8 * C * (K + K) * r) * D :=
            Nat.le_mul_of_pos_right _ (by omega)
          _ = 8 * C * (K + K) * D * r := by ring
      _ < Nat.factorial (K + K) := by
        simpa only [D, r] using hmargin
  let R := redGraph H D A
  have hRle : R ≤ H := redGraph_le H D A
  have hblue : ¬targetGraph K ⊑ H \ R := by
    exact target_not_isContained_blue K hK H D σ Q rfl A rfl
  have hred : ¬targetGraph K ⊑ R := by
    rintro ⟨f⟩
    have hforce : Nat.factorial (K + K) * K < 2 * (highVertices H D).card :=
      red_copy_forces_many_high K hK H D A f hAsmall
    have hhand : D * (highVertices H D).card ≤ 2 * edgeCount H :=
      mul_card_highVertices_le H D
    have hupper : 2 * D * (highVertices H D).card ≤
        8 * C * (Nat.factorial (K + K) * K) := by
      calc
        2 * D * (highVertices H D).card =
            2 * (D * (highVertices H D).card) := by ring
        _ ≤ 2 * (2 * edgeCount H) := Nat.mul_le_mul_left 2 hhand
        _ ≤ 2 * (2 * (C *
            Fintype.card (Equiv.Perm (Fin (K + K)) × Fin (K + K)))) := by
          gcongr
        _ = 8 * C * (Nat.factorial (K + K) * K) := by
          rw [targetGraph_card]
          ring
    have hforcedD : D * (Nat.factorial (K + K) * K) <
        2 * D * (highVertices H D).card := by
      calc
        D * (Nat.factorial (K + K) * K) < D * (2 * (highVertices H D).card) :=
          Nat.mul_lt_mul_of_pos_left hforce (by simp [D])
        _ = 2 * D * (highVertices H D).card := by ring
    have hDC : 8 * C < D := by simp [D]; omega
    have hpositive : 0 < Nat.factorial (K + K) * K :=
      Nat.mul_pos (Nat.factorial_pos _) hK
    have : 8 * C * (Nat.factorial (K + K) * K) <
        D * (Nat.factorial (K + K) * K) :=
      Nat.mul_lt_mul_of_pos_right hDC hpositive
    omega
  intro hRamsey
  exact (hRamsey R hRle).elim hred hblue

theorem target_sizeRamsey_lower_bound (C K : ℕ) (hK : 0 < K)
    (hmargin :
      let D := 16 * (C + 1)
      8 * C * (K + K) * D *
          (D ^ (K + K - 1) * (((K + K) * D) ^ K)) < Nat.factorial (K + K)) :
    C * Fintype.card (Equiv.Perm (Fin (K + K)) × Fin (K + K)) <
      sizeRamseyNumber (targetGraph K) := by
  by_contra hn
  have hle : sizeRamseyNumber (targetGraph K) ≤
      C * Fintype.card (Equiv.Perm (Fin (K + K)) × Fin (K + K)) :=
    Nat.le_of_not_gt hn
  obtain ⟨N, H, hRamsey, hcount⟩ := sizeRamseyNumber_spec (targetGraph K)
  have hnot := target_not_ramsey_of_edgeCount_le C K hK hmargin H (by
    simpa only [hcount] using hle)
  exact hnot hRamsey

/-- The proposed linear bound already fails for maximum degree three. -/
theorem erdos_559_fixed_degree_three : ¬FixedDegreeLinearSizeRamsey 3 := by
  rintro ⟨C, hC⟩
  obtain ⟨K, hK, hmargin⟩ := exists_factorial_margin C
  have hupper := hC
    (Equiv.Perm (Fin (K + K)) × Fin (K + K)) (targetGraph K)
    (targetGraph_maxDegree_le_three K)
  have hlower := target_sizeRamsey_lower_bound C K hK hmargin
  omega

/-- Negative resolution of Erdős Problem 559 (Rödl--Szemerédi): the fixed-degree
linear size-Ramsey assertion is false. -/
theorem not_erdos_559 : ¬(∀ d : ℕ, Erdos559.FixedDegreeLinearSizeRamsey d) := by
  intro h
  exact erdos_559_fixed_degree_three (h 3)

end Erdos559

#print axioms Erdos559.not_erdos_559

alias _root_.Erdos559.erdos_559 := _root_.Erdos559.not_erdos_559

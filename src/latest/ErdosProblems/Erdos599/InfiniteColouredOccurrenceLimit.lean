/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.InfiniteColouredOccurrenceWord
import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch
import Mathlib.Data.Set.Finite.Lattice

/-!
# Omega limits of finite coloured occurrence words

A strictly length-increasing chain of literal finite prefixes determines an
infinite occurrence word.  Its vertex and coloured-edge relations are exactly
the unions of the finite stages.  If every finite stage is interval-safe and
the reference warp has finite character, safeness passes to the limit: on
each finite reference owner the increasing removed-edge relation is already
attained at one finite stage.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- An omega-chain of genuine finite prefixes whose lengths grow at every
successor step. -/
structure FiniteColouredOccurrencePrefixChain (W Y : Set Gamma.DPath) where
  stage : ℕ → FiniteColouredOccurrenceWord W Y
  grows : ∀ n : ℕ, (stage n).Prefix (stage (n + 1))
  length_strict : ∀ n : ℕ, (stage n).length < (stage (n + 1)).length

namespace FiniteColouredOccurrencePrefixChain

variable (C : FiniteColouredOccurrencePrefixChain W Y)

theorem index_le_length : ∀ n, n ≤ (C.stage n).length := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      exact (Nat.succ_le_succ ih).trans (C.length_strict n)

theorem prefix_le {m n : ℕ} (hmn : m ≤ n) :
    (C.stage m).Prefix (C.stage n) := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact FiniteColouredOccurrenceWord.Prefix.refl _
  | succ n ih =>
      by_cases hmn' : m = n + 1
      · subst m
        exact FiniteColouredOccurrenceWord.Prefix.refl _
      · have hmn0 : m ≤ n := by omega
        exact (ih hmn0).trans (C.grows n)

private def limitVertex (n : ℕ) : V :=
  (C.stage n).vertex ⟨n, by
    have h := C.index_le_length n
    omega⟩

private def limitDirection (n : ℕ) : Direction :=
  (C.stage (n + 1)).direction ⟨n, by
    have h := C.index_le_length (n + 1)
    omega⟩

private theorem limitVertex_eq_stage (n k : ℕ) (hnk : n ≤ k) :
    C.limitVertex n = (C.stage k).vertex ⟨n, by
      have h := C.index_le_length k
      omega⟩ := by
  let i : Fin ((C.stage n).length + 1) := ⟨n, by
    have h := C.index_le_length n
    omega⟩
  have hprefix := C.prefix_le hnk
  exact (hprefix.vertex_eq i).symm

private theorem limitDirection_eq_stage (n k : ℕ) (hnk : n + 1 ≤ k) :
    C.limitDirection n = (C.stage k).direction ⟨n, by
      have h := C.index_le_length k
      omega⟩ := by
  let i : Fin (C.stage (n + 1)).length := ⟨n, by
    have h := C.index_le_length (n + 1)
    omega⟩
  have hprefix := C.prefix_le hnk
  exact (hprefix.direction_eq i).symm

private theorem limitActualEdge_eq_stage (n k : ℕ) (hnk : n + 1 ≤ k) :
    (match C.limitDirection n with
      | .forward => (C.limitVertex n, C.limitVertex (n + 1))
      | .backward => (C.limitVertex (n + 1), C.limitVertex n)) =
    (C.stage k).actualEdge ⟨n, by
      have h := C.index_le_length k
      omega⟩ := by
  have hv0 := C.limitVertex_eq_stage n k (by omega)
  have hv1 := C.limitVertex_eq_stage (n + 1) k hnk
  have hd := C.limitDirection_eq_stage n k hnk
  cases hdir : C.limitDirection n with
  | forward =>
      have hstage : (C.stage k).direction ⟨n, by
          have h := C.index_le_length k
          omega⟩ = .forward := hd.symm.trans hdir
      simp only [FiniteColouredOccurrenceWord.actualEdge, hstage]
      exact Prod.ext hv0 hv1
  | backward =>
      have hstage : (C.stage k).direction ⟨n, by
          have h := C.index_le_length k
          omega⟩ = .backward := hd.symm.trans hdir
      simp only [FiniteColouredOccurrenceWord.actualEdge, hstage]
      exact Prod.ext hv1 hv0

/-- The literal infinite word determined by the chain. -/
def limit : InfiniteColouredOccurrenceWord W Y where
  vertex := C.limitVertex
  direction := C.limitDirection
  actualEdge_spec := by
    intro n
    have hedge := (C.stage (n + 1)).actualEdge_spec ⟨n, by
      have h := C.index_le_length (n + 1)
      omega⟩
    have heq := C.limitActualEdge_eq_stage n (n + 1) (le_rfl)
    cases hdir : C.limitDirection n with
    | forward =>
        have hstage : (C.stage (n + 1)).direction ⟨n, by
            have h := C.index_le_length (n + 1)
            omega⟩ = .forward :=
          (C.limitDirection_eq_stage n (n + 1) le_rfl).symm.trans hdir
        simp only [hdir] at heq
        rw [heq]
        simpa [FiniteColouredOccurrenceWord.actualEdge, hstage] using hedge
    | backward =>
        have hstage : (C.stage (n + 1)).direction ⟨n, by
            have h := C.index_le_length (n + 1)
            omega⟩ = .backward :=
          (C.limitDirection_eq_stage n (n + 1) le_rfl).symm.trans hdir
        simp only [hdir] at heq
        rw [heq]
        simpa [FiniteColouredOccurrenceWord.actualEdge, hstage] using hedge
  occurrence_injective := by
    intro i j hij
    let k := max (i + 1) (j + 1)
    have hik : i + 1 ≤ k := le_max_left _ _
    have hjk : j + 1 ≤ k := le_max_right _ _
    let ii : Fin (C.stage k).length := ⟨i, by
      have h := C.index_le_length k
      omega⟩
    let jj : Fin (C.stage k).length := ⟨j, by
      have h := C.index_le_length k
      omega⟩
    have hijFin : ii = jj := (C.stage k).occurrence_injective (Prod.ext
      ((C.limitDirection_eq_stage i k hik).symm.trans
        ((congrArg Prod.fst hij).trans (C.limitDirection_eq_stage j k hjk)))
      ((C.limitActualEdge_eq_stage i k hik).symm.trans
        ((congrArg Prod.snd hij).trans (C.limitActualEdge_eq_stage j k hjk))))
    exact congrArg Fin.val hijFin

@[simp] theorem limit_vertex (n : ℕ) : C.limit.vertex n = C.limitVertex n := rfl

@[simp] theorem limit_direction (n : ℕ) :
    C.limit.direction n = C.limitDirection n := rfl

/-- Every finite-stage vertex occurrence is the occurrence at the same
coordinate in the omega limit. -/
theorem stage_vertex_eq_limit (n : ℕ)
    (i : Fin ((C.stage n).length + 1)) :
    (C.stage n).vertex i = C.limit.vertex i.1 := by
  let k := max n i.1
  have hnk : n ≤ k := le_max_left _ _
  have hik : i.1 ≤ k := le_max_right _ _
  have hstage := (C.prefix_le hnk).vertex_eq i
  have hlimit := C.limitVertex_eq_stage i.1 k hik
  exact hstage.symm.trans hlimit.symm

theorem stage_vertexSet_subset_limit (n : ℕ) :
    (C.stage n).vertexSet ⊆ C.limit.vertexSet := by
  rintro x ⟨i, rfl⟩
  refine ⟨i.1, ?_⟩
  have hnk : n ≤ max n i.1 := le_max_left _ _
  have hik : i.1 ≤ max n i.1 := le_max_right _ _
  have hstage := (C.prefix_le hnk).vertex_eq i
  have hlimit := C.limitVertex_eq_stage i.1 (max n i.1) hik
  exact hlimit.trans hstage

theorem limit_vertexSet_eq_iUnion :
    C.limit.vertexSet = ⋃ n, (C.stage n).vertexSet := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, ⟨⟨n, by
      have h := C.index_le_length n
      omega⟩, rfl⟩⟩
  · rintro x hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hx⟩
    exact C.stage_vertexSet_subset_limit n hx

private theorem stageActualEdge_eq_limit (n : ℕ)
    (i : Fin (C.stage n).length) :
    C.limit.actualEdge i.1 = (C.stage n).actualEdge i := by
  let k := max n (i.1 + 1)
  have hnk : n ≤ k := le_max_left _ _
  have hik : i.1 + 1 ≤ k := le_max_right _ _
  have hstage := (C.prefix_le hnk).actualEdge_eq i
  exact (C.limitActualEdge_eq_stage i.1 k hik).trans hstage

theorem stage_forwardEdges_subset_limit (n : ℕ) :
    (C.stage n).forwardEdges ⊆ C.limit.forwardEdges := by
  rintro e ⟨⟨i, hi⟩, rfl⟩
  let j : C.limit.ForwardIndex := ⟨i.1, by
    let k := max n (i.1 + 1)
    have hnk : n ≤ k := le_max_left _ _
    have hik : i.1 + 1 ≤ k := le_max_right _ _
    have hstage := (C.prefix_le hnk).direction_eq i
    have hlimit := C.limitDirection_eq_stage i.1 k hik
    exact hlimit.trans (hstage.trans hi)⟩
  exact ⟨j, by simpa [j, InfiniteColouredOccurrenceWord.forwardEdge,
    FiniteColouredOccurrenceWord.forwardEdge] using
    C.stageActualEdge_eq_limit n i⟩

theorem stage_backwardEdges_subset_limit (n : ℕ) :
    (C.stage n).backwardEdges ⊆ C.limit.backwardEdges := by
  rintro e ⟨⟨i, hi⟩, rfl⟩
  let j : C.limit.BackwardIndex := ⟨i.1, by
    intro hj
    let k := max n (i.1 + 1)
    have hnk : n ≤ k := le_max_left _ _
    have hik : i.1 + 1 ≤ k := le_max_right _ _
    have hstage := (C.prefix_le hnk).direction_eq i
    have hlimit := C.limitDirection_eq_stage i.1 k hik
    exact hi (hstage.symm.trans (hlimit.symm.trans hj))⟩
  exact ⟨j, by simpa [j, InfiniteColouredOccurrenceWord.backwardEdge,
    FiniteColouredOccurrenceWord.backwardEdge] using
    C.stageActualEdge_eq_limit n i⟩

theorem limit_forwardEdges_eq_iUnion :
    C.limit.forwardEdges = ⋃ n, (C.stage n).forwardEdges := by
  apply Set.Subset.antisymm
  · rintro e ⟨i, rfl⟩
    refine Set.mem_iUnion.2 ⟨i.1 + 1, ?_⟩
    let j : Fin (C.stage (i.1 + 1)).length := ⟨i.1, by
      have h := C.index_le_length (i.1 + 1)
      omega⟩
    have hj : (C.stage (i.1 + 1)).direction j = .forward :=
      (C.limitDirection_eq_stage i.1 (i.1 + 1) le_rfl).symm.trans i.2
    refine ⟨⟨j, hj⟩, ?_⟩
    change (C.stage (i.1 + 1)).actualEdge j = C.limit.actualEdge i.1
    change (C.stage (i.1 + 1)).actualEdge j =
      match C.limitDirection i.1 with
      | .forward => (C.limitVertex i.1, C.limitVertex (i.1 + 1))
      | .backward => (C.limitVertex (i.1 + 1), C.limitVertex i.1)
    convert (C.limitActualEdge_eq_stage i.1 (i.1 + 1) le_rfl).symm using 1
  · rintro e he
    rcases Set.mem_iUnion.1 he with ⟨n, he⟩
    exact C.stage_forwardEdges_subset_limit n he

theorem limit_backwardEdges_eq_iUnion :
    C.limit.backwardEdges = ⋃ n, (C.stage n).backwardEdges := by
  apply Set.Subset.antisymm
  · rintro e ⟨i, rfl⟩
    refine Set.mem_iUnion.2 ⟨i.1 + 1, ?_⟩
    let j : Fin (C.stage (i.1 + 1)).length := ⟨i.1, by
      have h := C.index_le_length (i.1 + 1)
      omega⟩
    have hj : (C.stage (i.1 + 1)).direction j ≠ .forward := by
      intro hj
      exact i.2 ((C.limitDirection_eq_stage i.1 (i.1 + 1) le_rfl).trans hj)
    refine ⟨⟨j, hj⟩, ?_⟩
    change (C.stage (i.1 + 1)).actualEdge j = C.limit.actualEdge i.1
    change (C.stage (i.1 + 1)).actualEdge j =
      match C.limitDirection i.1 with
      | .forward => (C.limitVertex i.1, C.limitVertex (i.1 + 1))
      | .backward => (C.limitVertex (i.1 + 1), C.limitVertex i.1)
    convert (C.limitActualEdge_eq_stage i.1 (i.1 + 1) le_rfl).symm using 1
  · rintro e he
    rcases Set.mem_iUnion.1 he with ⟨n, he⟩
    exact C.stage_backwardEdges_subset_limit n he

theorem forwardEdges_mono : Monotone (fun n ↦ (C.stage n).forwardEdges) := by
  intro m n hmn
  exact (C.prefix_le hmn).forwardEdges_subset

theorem backwardEdges_mono : Monotone (fun n ↦ (C.stage n).backwardEdges) := by
  intro m n hmn
  exact (C.prefix_le hmn).backwardEdges_subset

end FiniteColouredOccurrencePrefixChain

namespace InfiniteColouredOccurrenceWord

/-- Infinite counterpart of the finite relational safeness invariant. -/
structure IsIntervalSafe (Q : InfiniteColouredOccurrenceWord W Y) : Prop where
  incoming_removed : ∀ {a b x : V}, (a, x) ∈ Q.forwardEdges →
    (b, x) ∈ familyEdges Y → (b, x) ∈ Q.backwardEdges
  outgoing_removed : ∀ {x a b : V}, (x, a) ∈ Q.forwardEdges →
    (x, b) ∈ familyEdges Y → (x, b) ∈ Q.backwardEdges
  intervals : ∀ p ∈ Y, IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
  endpoint_pure : ∀ {x y : V}, (x, y) ∈ Q.forwardEdges →
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y

end InfiniteColouredOccurrenceWord

namespace FiniteColouredOccurrencePrefixChain

private theorem exists_iUnion_inter_eq_of_finite
    (A : ℕ → Set (V × V)) (hmono : Monotone A)
    (E : Set (V × V)) (hE : E.Finite) :
    ∃ N, (⋃ n, A n) ∩ E = A N ∩ E := by
  let S := (⋃ n, A n) ∩ E
  have hS : S.Finite := hE.subset Set.inter_subset_right
  have hSsub : S ⊆ ⋃ n, A n := Set.inter_subset_left
  obtain ⟨I, hIfin, hI⟩ := Set.finite_subset_iUnion hS hSsub
  obtain ⟨N, hN⟩ := hIfin.bddAbove
  refine ⟨N, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hx' := hI hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨i, hiI, hxi⟩ := hx'
    exact ⟨hmono (hN hiI) hxi, hx.2⟩
  · rintro x ⟨hxA, hxE⟩
    exact ⟨Set.mem_iUnion.2 ⟨N, hxA⟩, hxE⟩

/-- Interval safeness is closed under a strict omega-chain of genuine
prefixes when every reference owner is finite. -/
theorem limit_isIntervalSafe
    (C : FiniteColouredOccurrencePrefixChain W Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hsafe : ∀ n, (C.stage n).IsIntervalSafe) :
    C.limit.IsIntervalSafe := by
  constructor
  · intro a b x hax hbx
    rw [C.limit_forwardEdges_eq_iUnion] at hax
    rcases Set.mem_iUnion.1 hax with ⟨n, hax⟩
    rw [C.limit_backwardEdges_eq_iUnion]
    exact Set.mem_iUnion.2 ⟨n, (hsafe n).incoming_removed hax hbx⟩
  · intro x a b hxa hxb
    rw [C.limit_forwardEdges_eq_iUnion] at hxa
    rcases Set.mem_iUnion.1 hxa with ⟨n, hxa⟩
    rw [C.limit_backwardEdges_eq_iUnion]
    exact Set.mem_iUnion.2 ⟨n, (hsafe n).outgoing_removed hxa hxb⟩
  · intro p hpY
    obtain ⟨q, hpq⟩ := hYfin hpY
    subst p
    obtain ⟨N, hN⟩ := exists_iUnion_inter_eq_of_finite
      (fun n ↦ (C.stage n).backwardEdges) C.backwardEdges_mono
      (DirectedPath.Path.edgeSet (Sum.inl q : Gamma.DPath))
      (Erdos599.Alternating.FinitePath.edgeSet_finite q)
    rw [C.limit_backwardEdges_eq_iUnion, hN]
    exact (hsafe N).intervals (.inl q) hpY
  · intro x y hxy
    rw [C.limit_forwardEdges_eq_iUnion] at hxy
    rcases Set.mem_iUnion.1 hxy with ⟨n, hxy⟩
    exact (hsafe n).endpoint_pure hxy

#print axioms FiniteColouredOccurrencePrefixChain.limit_forwardEdges_eq_iUnion
#print axioms FiniteColouredOccurrencePrefixChain.limit_backwardEdges_eq_iUnion
#print axioms FiniteColouredOccurrencePrefixChain.stage_vertex_eq_limit
#print axioms FiniteColouredOccurrencePrefixChain.limit_isIntervalSafe

end FiniteColouredOccurrencePrefixChain
end Erdos599.Alternating

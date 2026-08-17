/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.BoundedExpansions

/-!
# Erdős Problem 63: length adjusters

This file formalizes the finite routing gadget from Definition 4.1 of
Liu--Montgomery.  An adjuster has two disjoint bounded vertex expansions and a
small core.  Inside the core, together with the two roots, there are paths of
length `ell, ell + 2, ..., ell + 2 * k`.  The public `length` is the least
possible `ell`, exactly as in the paper.

The construction lemmas separate the graph-geometric work from the bookkeeping
needed later.  `simpleAdjusterOfTwoRoutes` is the final step of Lemma 4.2 once
the two routes around a shortest even cycle have been constructed.
`Adjuster.ofJoinRoutes` is the route-composition step in Lemma 4.7.  The
concrete expander constructions are carried out in `AdjusterBase` and
`AdjusterJoin`.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V}

/-- A path whose vertices all lie in a prescribed finite set. -/
def HasSupportedPathLength (G : SimpleGraph V) (allowed : Finset V)
    (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.Walk x y,
    p.IsPath ∧ (∀ z ∈ p.support, z ∈ allowed) ∧ p.length = n

namespace HasSupportedPathLength

theorem toHasPathBetweenLength {allowed : Finset V} {x y : V} {n : ℕ}
    (h : HasSupportedPathLength G allowed x y n) :
    HasPathBetweenLength G x y n := by
  obtain ⟨p, hp, -, hlen⟩ := h
  exact ⟨p, hp, hlen⟩

theorem mono_allowed {S T : Finset V} {x y : V} {n : ℕ}
    (h : HasSupportedPathLength G S x y n) (hST : S ⊆ T) :
    HasSupportedPathLength G T x y n := by
  obtain ⟨p, hp, hsupp, hlen⟩ := h
  exact ⟨p, hp, fun z hz ↦ hST (hsupp z hz), hlen⟩

theorem reverse {allowed : Finset V} {x y : V} {n : ℕ}
    (h : HasSupportedPathLength G allowed x y n) :
    HasSupportedPathLength G allowed y x n := by
  obtain ⟨p, hp, hsupp, hlen⟩ := h
  refine ⟨p.reverse, hp.reverse, ?_, by simpa using hlen⟩
  intro z hz
  apply hsupp z
  simpa using hz

/-- A supported exact path remains one after adding graph edges. -/
theorem mono_graph {G' : SimpleGraph V} {allowed : Finset V}
    {x y : V} {n : ℕ} (hGG' : G ≤ G')
    (h : HasSupportedPathLength G allowed x y n) :
    HasSupportedPathLength G' allowed x y n := by
  obtain ⟨p, hp, hsupp, hlen⟩ := h
  refine ⟨p.mapLe hGG', hp.mapLe hGG', ?_, by simpa using hlen⟩
  intro z hz
  apply hsupp z
  simpa only [Walk.support_mapLe_eq_support] using hz

/-- Package an already verified simple concatenation as a supported exact
path.  The separate `IsPath` premise is the support-separation obligation
discharged by the avoiding-connection lemmas. -/
theorem appendWalk {S T : Finset V} {x y z : V} {a b : ℕ}
    (p : G.Walk x y) (q : G.Walk y z)
    (hpq : (p.append q).IsPath)
    (hp : ∀ w ∈ p.support, w ∈ S)
    (hq : ∀ w ∈ q.support, w ∈ T)
    (hplen : p.length = a) (hqlen : q.length = b) :
    HasSupportedPathLength G (S ∪ T) x z (a + b) := by
  refine ⟨p.append q, hpq, ?_, ?_⟩
  · intro w hw
    rw [Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · exact Finset.mem_union_left _ (hp w hw)
    · exact Finset.mem_union_right _ (hq w hw)
  · simpa [Walk.length_append, hplen, hqlen]

end HasSupportedPathLength

/-- Definition 4.1 of Liu--Montgomery.

The final field only asserts that at least one base length works.  The
definition `Adjuster.length` below chooses the least one, so the formal object
also records the paper's convention for the length of an adjuster. -/
structure Adjuster (G : SimpleGraph V) (D m k : ℕ) where
  leftRoot : V
  rightRoot : V
  leftEnd : VertexExpansion G leftRoot D m
  rightEnd : VertexExpansion G rightRoot D m
  core : Finset V
  core_disjoint_left : Disjoint core leftEnd.verts
  core_disjoint_right : Disjoint core rightEnd.verts
  ends_disjoint : Disjoint leftEnd.verts rightEnd.verts
  core_card_le : core.card ≤ 10 * m * k
  exists_baseLength : ∃ ell : ℕ, ∀ i : ℕ, i ≤ k →
    HasSupportedPathLength G (insert leftRoot (insert rightRoot core))
      leftRoot rightRoot (ell + 2 * i)

/-- Source terminology for a `(D,m,1)`-adjuster. -/
abbrev SimpleAdjuster (G : SimpleGraph V) (D m : ℕ) := Adjuster G D m 1

namespace Adjuster

variable {D m k : ℕ}

/-- All vertices occupied by an adjuster, including its two ends. -/
noncomputable def verts (A : Adjuster G D m k) : Finset V :=
  A.leftEnd.verts ∪ A.rightEnd.verts ∪ A.core

@[simp] theorem leftRoot_mem_verts (A : Adjuster G D m k) :
    A.leftRoot ∈ A.verts := by
  classical
  simp [verts, A.leftEnd.root_mem]

@[simp] theorem rightRoot_mem_verts (A : Adjuster G D m k) :
    A.rightRoot ∈ A.verts := by
  classical
  simp [verts, A.rightEnd.root_mem]

theorem leftEnd_verts_subset (A : Adjuster G D m k) :
    A.leftEnd.verts ⊆ A.verts := by
  classical
  intro z hz
  simp [verts, hz]

theorem rightEnd_verts_subset (A : Adjuster G D m k) :
    A.rightEnd.verts ⊆ A.verts := by
  classical
  intro z hz
  simp [verts, hz]

theorem core_subset_verts (A : Adjuster G D m k) : A.core ⊆ A.verts := by
  classical
  intro z hz
  simp [verts, hz]

/-- The length of an adjuster is the least base length supporting all its
required routes. -/
noncomputable def length (A : Adjuster G D m k) : ℕ :=
  Nat.find A.exists_baseLength

/-- Every required adjusted route exists at the least base length. -/
theorem pathLength (A : Adjuster G D m k) (i : ℕ) (hi : i ≤ k) :
    HasSupportedPathLength G (insert A.leftRoot (insert A.rightRoot A.core))
      A.leftRoot A.rightRoot (A.length + 2 * i) := by
  exact (Nat.find_spec A.exists_baseLength) i hi

/-- Minimality of `Adjuster.length`. -/
theorem length_minimal (A : Adjuster G D m k) {ell : ℕ}
    (hell : ∀ i : ℕ, i ≤ k →
      HasSupportedPathLength G (insert A.leftRoot (insert A.rightRoot A.core))
        A.leftRoot A.rightRoot (ell + 2 * i)) :
    A.length ≤ ell := by
  exact Nat.find_min' A.exists_baseLength hell

/-- The unadjusted route. -/
theorem basePath (A : Adjuster G D m k) :
    HasSupportedPathLength G (insert A.leftRoot (insert A.rightRoot A.core))
      A.leftRoot A.rightRoot A.length := by
  simpa using A.pathLength 0 (Nat.zero_le k)

/-- Forgetting the support information gives an exact path in the ambient
graph. -/
theorem hasPathBetweenLength (A : Adjuster G D m k) (i : ℕ) (hi : i ≤ k) :
    HasPathBetweenLength G A.leftRoot A.rightRoot (A.length + 2 * i) :=
  (A.pathLength i hi).toHasPathBetweenLength

/-- An adjuster occupies at most the sum of the sizes of its two ends and its
core. -/
theorem card_verts_le (A : Adjuster G D m k) :
    A.verts.card ≤ 2 * D + 10 * m * k := by
  classical
  have hleftRight := Finset.card_union_le A.leftEnd.verts A.rightEnd.verts
  have hwithCore :=
    Finset.card_union_le (A.leftEnd.verts ∪ A.rightEnd.verts) A.core
  calc
    A.verts.card ≤ A.leftEnd.verts.card + A.rightEnd.verts.card + A.core.card := by
      simp only [verts]
      omega
    _ = D + D + A.core.card := by simp
    _ ≤ D + D + 10 * m * k := Nat.add_le_add_left A.core_card_le (D + D)
    _ = 2 * D + 10 * m * k := by omega

/-- The paper's elementary estimate `length(A) ≤ |A| + 1`. -/
theorem length_le_core_card_add_one (A : Adjuster G D m k) :
    A.length ≤ A.core.card + 1 := by
  classical
  obtain ⟨p, hp, hsupp, hplen⟩ := A.basePath
  have hsupport : p.support.toFinset ⊆
      insert A.leftRoot (insert A.rightRoot A.core) := by
    intro z hz
    exact hsupp z (List.mem_toFinset.mp hz)
  have hcard_support : p.length + 1 = p.support.toFinset.card := by
    rw [← p.length_support, List.toFinset_card_of_nodup hp.support_nodup]
  have hallowed :
      (insert A.leftRoot (insert A.rightRoot A.core)).card ≤ A.core.card + 2 := by
    have hright := Finset.card_insert_le A.rightRoot A.core
    have hleft := Finset.card_insert_le A.leftRoot (insert A.rightRoot A.core)
    omega
  have htotal : p.length + 1 ≤ A.core.card + 2 := by
    rw [hcard_support]
    exact (Finset.card_le_card hsupport).trans hallowed
  omega

/-- The coarser size estimate used in Lemma 4.8. -/
theorem length_le_ten_mul_add_one (A : Adjuster G D m k) :
    A.length ≤ 10 * m * k + 1 :=
  (A.length_le_core_card_add_one).trans (Nat.add_le_add_right A.core_card_le 1)

/-- Reverse an adjuster, interchanging its two ends. -/
noncomputable def swap (A : Adjuster G D m k) : Adjuster G D m k where
  leftRoot := A.rightRoot
  rightRoot := A.leftRoot
  leftEnd := A.rightEnd
  rightEnd := A.leftEnd
  core := A.core
  core_disjoint_left := A.core_disjoint_right
  core_disjoint_right := A.core_disjoint_left
  ends_disjoint := A.ends_disjoint.symm
  core_card_le := A.core_card_le
  exists_baseLength := by
    obtain ⟨ell, hell⟩ := A.exists_baseLength
    refine ⟨ell, ?_⟩
    intro i hi
    simpa [Finset.insert_comm] using (hell i hi).reverse

@[simp] theorem swap_leftRoot (A : Adjuster G D m k) :
    A.swap.leftRoot = A.rightRoot := rfl

@[simp] theorem swap_rightRoot (A : Adjuster G D m k) :
    A.swap.rightRoot = A.leftRoot := rfl

@[simp] theorem swap_core (A : Adjuster G D m k) : A.swap.core = A.core := rfl

@[simp] theorem swap_verts (A : Adjuster G D m k) : A.swap.verts = A.verts := by
  classical
  change A.rightEnd.verts ∪ A.leftEnd.verts ∪ A.core =
    A.leftEnd.verts ∪ A.rightEnd.verts ∪ A.core
  rw [Finset.union_comm A.rightEnd.verts A.leftEnd.verts]

@[simp] theorem swap_length (A : Adjuster G D m k) : A.swap.length = A.length := by
  apply Nat.le_antisymm
  · apply A.swap.length_minimal
    intro i hi
    simpa [Finset.insert_comm] using (A.pathLength i hi).reverse
  · apply A.length_minimal
    intro i hi
    simpa [Finset.insert_comm] using (A.swap.pathLength i hi).reverse

/-- Increasing the permitted end radius preserves an adjuster. -/
noncomputable def radiusMono (A : Adjuster G D m k) {m' : ℕ} (hmm' : m ≤ m')
    : Adjuster G D m' k where
  leftRoot := A.leftRoot
  rightRoot := A.rightRoot
  leftEnd := A.leftEnd.radiusMono hmm'
  rightEnd := A.rightEnd.radiusMono hmm'
  core := A.core
  core_disjoint_left := by simpa using A.core_disjoint_left
  core_disjoint_right := by simpa using A.core_disjoint_right
  ends_disjoint := by simpa using A.ends_disjoint
  core_card_le := by
    exact A.core_card_le.trans
      (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 10 hmm'))
  exists_baseLength := A.exists_baseLength

@[simp] theorem radiusMono_leftRoot (A : Adjuster G D m k) {m' : ℕ}
    (hmm' : m ≤ m') : (A.radiusMono hmm').leftRoot = A.leftRoot := rfl

@[simp] theorem radiusMono_rightRoot (A : Adjuster G D m k) {m' : ℕ}
    (hmm' : m ≤ m') : (A.radiusMono hmm').rightRoot = A.rightRoot := rfl

@[simp] theorem radiusMono_core (A : Adjuster G D m k) {m' : ℕ}
    (hmm' : m ≤ m') : (A.radiusMono hmm').core = A.core := rfl

@[simp] theorem radiusMono_length (A : Adjuster G D m k) {m' : ℕ}
    (hmm' : m ≤ m') : (A.radiusMono hmm').length = A.length := rfl

@[simp] theorem radiusMono_verts (A : Adjuster G D m k) {m' : ℕ}
    (hmm' : m ≤ m') : (A.radiusMono hmm').verts = A.verts := by
  classical
  simp [radiusMono, verts]

/-! ## Changing and transporting the ends -/

/-- Replace both ends of an adjuster by expansions about the same roots.

The adjustable routes only use the core and the two roots, so they remain
valid verbatim.  The radius may increase; this only weakens the core-size
bound.  This is the bookkeeping operation used after the end-expansion
steps in Lemmas 4.3 and 4.8. -/
noncomputable def replaceEnds {D₀ D m m' : ℕ}
    (A : Adjuster G D₀ m k)
    (left : VertexExpansion G A.leftRoot D m')
    (right : VertexExpansion G A.rightRoot D m')
    (hcoreLeft : Disjoint A.core left.verts)
    (hcoreRight : Disjoint A.core right.verts)
    (hends : Disjoint left.verts right.verts)
    (hmm' : m ≤ m') : Adjuster G D m' k where
  leftRoot := A.leftRoot
  rightRoot := A.rightRoot
  leftEnd := left
  rightEnd := right
  core := A.core
  core_disjoint_left := hcoreLeft
  core_disjoint_right := hcoreRight
  ends_disjoint := hends
  core_card_le := A.core_card_le.trans
    (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 10 hmm'))
  exists_baseLength := A.exists_baseLength

@[simp] theorem replaceEnds_leftRoot {D₀ D m m' : ℕ}
    (A : Adjuster G D₀ m k)
    (left : VertexExpansion G A.leftRoot D m')
    (right : VertexExpansion G A.rightRoot D m')
    (hcoreLeft : Disjoint A.core left.verts)
    (hcoreRight : Disjoint A.core right.verts)
    (hends : Disjoint left.verts right.verts)
    (hmm' : m ≤ m') :
    (A.replaceEnds left right hcoreLeft hcoreRight hends hmm').leftRoot =
      A.leftRoot := rfl

@[simp] theorem replaceEnds_rightRoot {D₀ D m m' : ℕ}
    (A : Adjuster G D₀ m k)
    (left : VertexExpansion G A.leftRoot D m')
    (right : VertexExpansion G A.rightRoot D m')
    (hcoreLeft : Disjoint A.core left.verts)
    (hcoreRight : Disjoint A.core right.verts)
    (hends : Disjoint left.verts right.verts)
    (hmm' : m ≤ m') :
    (A.replaceEnds left right hcoreLeft hcoreRight hends hmm').rightRoot =
      A.rightRoot := rfl

@[simp] theorem replaceEnds_core {D₀ D m m' : ℕ}
    (A : Adjuster G D₀ m k)
    (left : VertexExpansion G A.leftRoot D m')
    (right : VertexExpansion G A.rightRoot D m')
    (hcoreLeft : Disjoint A.core left.verts)
    (hcoreRight : Disjoint A.core right.verts)
    (hends : Disjoint left.verts right.verts)
    (hmm' : m ≤ m') :
    (A.replaceEnds left right hcoreLeft hcoreRight hends hmm').core =
      A.core := rfl

@[simp] theorem replaceEnds_length {D₀ D m m' : ℕ}
    (A : Adjuster G D₀ m k)
    (left : VertexExpansion G A.leftRoot D m')
    (right : VertexExpansion G A.rightRoot D m')
    (hcoreLeft : Disjoint A.core left.verts)
    (hcoreRight : Disjoint A.core right.verts)
    (hends : Disjoint left.verts right.verts)
    (hmm' : m ≤ m') :
    (A.replaceEnds left right hcoreLeft hcoreRight hends hmm').length =
      A.length := rfl

/-- Passing to a supergraph preserves an adjuster without changing any of
its vertex data. -/
noncomputable def monoGraph {H : SimpleGraph V} (A : Adjuster H D m k)
    (hHG : H ≤ G) : Adjuster G D m k where
  leftRoot := A.leftRoot
  rightRoot := A.rightRoot
  leftEnd := A.leftEnd.monoGraph hHG
  rightEnd := A.rightEnd.monoGraph hHG
  core := A.core
  core_disjoint_left := by simpa using A.core_disjoint_left
  core_disjoint_right := by simpa using A.core_disjoint_right
  ends_disjoint := by simpa using A.ends_disjoint
  core_card_le := A.core_card_le
  exists_baseLength := by
    obtain ⟨ell, hell⟩ := A.exists_baseLength
    exact ⟨ell, fun i hi ↦ (hell i hi).mono_graph hHG⟩

@[simp] theorem monoGraph_leftRoot {H : SimpleGraph V}
    (A : Adjuster H D m k) (hHG : H ≤ G) :
    (A.monoGraph hHG).leftRoot = A.leftRoot := rfl

@[simp] theorem monoGraph_rightRoot {H : SimpleGraph V}
    (A : Adjuster H D m k) (hHG : H ≤ G) :
    (A.monoGraph hHG).rightRoot = A.rightRoot := rfl

@[simp] theorem monoGraph_core {H : SimpleGraph V}
    (A : Adjuster H D m k) (hHG : H ≤ G) :
    (A.monoGraph hHG).core = A.core := rfl

@[simp] theorem monoGraph_verts {H : SimpleGraph V}
    (A : Adjuster H D m k) (hHG : H ≤ G) :
    (A.monoGraph hHG).verts = A.verts := by
  classical
  simp [monoGraph, verts]

/-- Transport an adjuster through an induced graph embedding. -/
noncomputable def mapEmbedding {W : Type v} [DecidableEq W]
    {H : SimpleGraph W} (A : Adjuster G D m k) (f : G ↪g H) :
    Adjuster H D m k where
  leftRoot := f A.leftRoot
  rightRoot := f A.rightRoot
  leftEnd := A.leftEnd.mapEmbedding f
  rightEnd := A.rightEnd.mapEmbedding f
  core := A.core.map ⟨f, f.injective⟩
  core_disjoint_left := by
    simpa using (Finset.disjoint_map ⟨f, f.injective⟩).2 A.core_disjoint_left
  core_disjoint_right := by
    simpa using (Finset.disjoint_map ⟨f, f.injective⟩).2 A.core_disjoint_right
  ends_disjoint := by
    simpa using (Finset.disjoint_map ⟨f, f.injective⟩).2 A.ends_disjoint
  core_card_le := by simpa using A.core_card_le
  exists_baseLength := by
    obtain ⟨ell, hell⟩ := A.exists_baseLength
    refine ⟨ell, ?_⟩
    intro i hi
    obtain ⟨p, hp, hsupp, hlen⟩ := hell i hi
    refine ⟨p.map f.toHom, hp.map f.injective, ?_, by simpa using hlen⟩
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    have hallowed := hsupp w hw
    simp only [Finset.mem_insert] at hallowed ⊢
    rcases hallowed with hwleft | hwright | hwcore
    · subst w
      exact Or.inl rfl
    · subst w
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Finset.mem_map.2 ⟨w, hwcore, rfl⟩))

@[simp] theorem mapEmbedding_leftRoot {W : Type v} [DecidableEq W]
    {H : SimpleGraph W} (A : Adjuster G D m k) (f : G ↪g H) :
    (A.mapEmbedding f).leftRoot = f A.leftRoot := rfl

@[simp] theorem mapEmbedding_rightRoot {W : Type v} [DecidableEq W]
    {H : SimpleGraph W} (A : Adjuster G D m k) (f : G ↪g H) :
    (A.mapEmbedding f).rightRoot = f A.rightRoot := rfl

@[simp] theorem mapEmbedding_core {W : Type v} [DecidableEq W]
    {H : SimpleGraph W} (A : Adjuster G D m k) (f : G ↪g H) :
    (A.mapEmbedding f).core = A.core.map ⟨f, f.injective⟩ := rfl

@[simp] theorem mapEmbedding_verts {W : Type v} [DecidableEq W]
    {H : SimpleGraph W} (A : Adjuster G D m k) (f : G ↪g H) :
    (A.mapEmbedding f).verts = A.verts.map ⟨f, f.injective⟩ := by
  classical
  simp [mapEmbedding, verts, Finset.map_union]

end Adjuster

/-! ## Simple adjusters: the core of Lemmas 4.2 and 4.3 -/

/-- The final graph-theoretic step of Liu--Montgomery Lemma 4.2.

Once the two end expansions and the two routes around the chosen shortest
even cycle have been constructed, this packages them as a simple adjuster. -/
noncomputable def simpleAdjusterOfTwoRoutes {D m ell : ℕ} {x y : V}
    (left : VertexExpansion G x D m) (right : VertexExpansion G y D m)
    (core : Finset V)
    (hcoreLeft : Disjoint core left.verts)
    (hcoreRight : Disjoint core right.verts)
    (hends : Disjoint left.verts right.verts)
    (hcard : core.card ≤ 10 * m)
    (hshort : HasSupportedPathLength G (insert x (insert y core)) x y ell)
    (hlong : HasSupportedPathLength G (insert x (insert y core)) x y (ell + 2)) :
    Adjuster G D m 1 := by
  refine
    { leftRoot := x
      rightRoot := y
      leftEnd := left
      rightEnd := right
      core := core
      core_disjoint_left := hcoreLeft
      core_disjoint_right := hcoreRight
      ends_disjoint := hends
      core_card_le := by simpa using hcard
      exists_baseLength := ⟨ell, ?_⟩ }
  intro i hi
  interval_cases i
  · simpa using hshort
  · simpa [Nat.add_assoc] using hlong

/-! ## Joining adjusters -/

/-- The routing certificate needed to join two adjusters while retaining the
right end of each.  Expansion lemmas construct this certificate from a short
path between the discarded left ends. -/
structure AdjusterJoinRoutes {D m k₁ k₂ : ℕ}
    (A : Adjuster G D m k₁) (B : Adjuster G D m k₂) where
  core : Finset V
  core_disjoint_left : Disjoint core A.rightEnd.verts
  core_disjoint_right : Disjoint core B.rightEnd.verts
  ends_disjoint : Disjoint A.rightEnd.verts B.rightEnd.verts
  core_card_le : core.card ≤ 10 * m * (k₁ + k₂)
  baseLength : ℕ
  routes : ∀ i j : ℕ, i ≤ k₁ → j ≤ k₂ →
    HasSupportedPathLength G
      (insert A.rightRoot (insert B.rightRoot core))
      A.rightRoot B.rightRoot (baseLength + 2 * (i + j))

namespace Adjuster

variable {D m k₁ k₂ : ℕ}

/-- Route composition in Lemma 4.7: a routing certificate for two adjusters
produces one adjuster whose adjustment ranges add. -/
def ofJoinRoutes (A : Adjuster G D m k₁) (B : Adjuster G D m k₂)
    (J : AdjusterJoinRoutes A B) : Adjuster G D m (k₁ + k₂) where
  leftRoot := A.rightRoot
  rightRoot := B.rightRoot
  leftEnd := A.rightEnd
  rightEnd := B.rightEnd
  core := J.core
  core_disjoint_left := J.core_disjoint_left
  core_disjoint_right := J.core_disjoint_right
  ends_disjoint := J.ends_disjoint
  core_card_le := J.core_card_le
  exists_baseLength := by
    refine ⟨J.baseLength, ?_⟩
    intro s hs
    by_cases hsk : s ≤ k₁
    · simpa using J.routes s 0 hsk (Nat.zero_le k₂)
    · have hk₁s : k₁ ≤ s := by omega
      let j := s - k₁
      have hj : j ≤ k₂ := by
        dsimp [j]
        omega
      have hsum : k₁ + j = s := by
        dsimp [j]
        exact Nat.add_sub_of_le hk₁s
      simpa [hsum] using J.routes k₁ j (le_refl k₁) hj

@[simp] theorem ofJoinRoutes_leftRoot (A : Adjuster G D m k₁)
    (B : Adjuster G D m k₂) (J : AdjusterJoinRoutes A B) :
    (A.ofJoinRoutes B J).leftRoot = A.rightRoot := rfl

@[simp] theorem ofJoinRoutes_rightRoot (A : Adjuster G D m k₁)
    (B : Adjuster G D m k₂) (J : AdjusterJoinRoutes A B) :
    (A.ofJoinRoutes B J).rightRoot = B.rightRoot := rfl

@[simp] theorem ofJoinRoutes_core (A : Adjuster G D m k₁)
    (B : Adjuster G D m k₂) (J : AdjusterJoinRoutes A B) :
    (A.ofJoinRoutes B J).core = J.core := rfl

@[simp] theorem ofJoinRoutes_verts (A : Adjuster G D m k₁)
    (B : Adjuster G D m k₂) (J : AdjusterJoinRoutes A B) :
    (A.ofJoinRoutes B J).verts =
      A.rightEnd.verts ∪ B.rightEnd.verts ∪ J.core := rfl

end Adjuster

end Erdos63

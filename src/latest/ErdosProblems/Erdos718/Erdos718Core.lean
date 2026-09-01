/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file contains the shared graph-theoretic foundation for the Lean
formalization of the resolution of Erdős Problem 718.
https://www.erdosproblems.com/718

Informal authors:
- János Komlós and Endre Szemerédi
- Béla Bollobás and Andrew Thomason
- Robin Thomas and Paul Wollan (linkedness theorem used in the proof)

Formal authors:
- Codex

The accompanying detailed proof and Leanization plan is `tex/718.tex`.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos599.Countable
open Function Set
open SimpleGraph

/- Compatibility names used by elaborated order/algebra tactics in this development. -/
namespace Prod
@[instance_reducible]
def «instLE_.lake» {α β : Type*} [LE α] [LE β] : LE (α × β) := inferInstance
end Prod

namespace Nat
@[instance_reducible]
def «instPartialOrder_.lake» : PartialOrder Nat := Nat.instPartialOrder
end Nat

namespace Erdos718

/-! ### Clique subdivisions -/

/-- One ordered representative `(i,j)` with `i < j` for every edge of `K_r`. -/
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

/-- The internal vertices of a walk, excluding its two endpoints. -/
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/-- A faithful path model of a subdivision of `K_r` in `G`.

The branch vertices are distinct.  Every clique edge is represented by a
simple path between its two branch vertices.  Path interiors avoid all branch
vertices and distinct clique edges have disjoint interiors. -/
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

/-- `G` contains a subdivision of `K_r`. -/
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

theorem mem_walkInteriorSet_iff {V : Type*} {G : SimpleGraph V} {u v x : V}
    {p : G.Walk u v} :
    x ∈ walkInteriorSet p ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := by
  rfl

theorem walkInteriorSet_subset_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    walkInteriorSet p ⊆ {x | x ∈ p.support} := by
  intro x hx
  exact hx.1

theorem start_not_mem_walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    u ∉ walkInteriorSet p := by
  intro hu
  exact hu.2.1 rfl

theorem end_not_mem_walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    v ∉ walkInteriorSet p := by
  intro hv
  exact hv.2.2 rfl

@[simp]
theorem walkInteriorSet_mapLe {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    {u v : V} (p : G.Walk u v) :
    walkInteriorSet (p.mapLe h) = walkInteriorSet p := by
  ext x
  simp only [walkInteriorSet, Set.mem_ofPred_eq, Walk.support_mapLe_eq_support]

/-- A clique subdivision persists when edges are added. -/
def CliqueSubdivision.mapLe {V : Type*} {G H : SimpleGraph V} {r : ℕ}
    (s : CliqueSubdivision G r) (h : G ≤ H) : CliqueSubdivision H r where
  branch := s.branch
  path e := (s.path e).mapLe h
  path_isPath e := (s.path_isPath e).mapLe h
  interior_avoids_branch e := by
    simpa only [walkInteriorSet_mapLe] using s.interior_avoids_branch e
  interior_pairwise e f hef := by
    simpa only [walkInteriorSet_mapLe] using s.interior_pairwise hef

theorem ContainsCliqueSubdivision.mono {V : Type*} {G H : SimpleGraph V} {r : ℕ}
    (hG : ContainsCliqueSubdivision G r) (h : G ≤ H) :
    ContainsCliqueSubdivision H r := by
  exact hG.map fun s => s.mapLe h

theorem containsCliqueSubdivision_zero {V : Type*} (G : SimpleGraph V) :
    ContainsCliqueSubdivision G 0 := by
  refine ⟨{
    branch := Function.Embedding.ofIsEmpty
    path := fun e => Fin.elim0 e.1.1
    path_isPath := fun e => Fin.elim0 e.1.1
    interior_avoids_branch := fun e => Fin.elim0 e.1.1
    interior_pairwise := fun e => Fin.elim0 e.1.1
  }⟩

private theorem CliqueEdge.one_isEmpty (e : CliqueEdge 1) : False := by
  omega

theorem containsCliqueSubdivision_one {V : Type*} (G : SimpleGraph V) (v : V) :
    ContainsCliqueSubdivision G 1 := by
  let branch : Fin 1 ↪ V :=
    ⟨fun _ => v, fun a b _ => Subsingleton.elim a b⟩
  refine ⟨{
    branch := branch
    path := fun e => (CliqueEdge.one_isEmpty e).elim
    path_isPath := fun e => (CliqueEdge.one_isEmpty e).elim
    interior_avoids_branch := fun e => (CliqueEdge.one_isEmpty e).elim
    interior_pairwise := fun e => (CliqueEdge.one_isEmpty e).elim
  }⟩

theorem containsCliqueSubdivision_one_of_nonempty {V : Type*} [Nonempty V]
    (G : SimpleGraph V) : ContainsCliqueSubdivision G 1 := by
  exact containsCliqueSubdivision_one G (Classical.choice inferInstance)

/-! ### Disjoint linkages -/

/-- Pairwise disjoint paths joining a prescribed family of terminal pairs.

The terminals are supplied by one embedding of `Sum ι ι`: `inl i` is paired
with `inr i`.  Interiors avoid the distinguished set `X`, and the complete
supports of paths for distinct indices are disjoint. -/
structure PairLinkage {V ι : Type*} (G : SimpleGraph V) (X : Set V)
    (terminal : Sum ι ι ↪ V) where
  path : ∀ i, G.Walk (terminal (.inl i)) (terminal (.inr i))
  isPath : ∀ i, (path i).IsPath
  avoids : ∀ i, Disjoint (walkInteriorSet (path i)) X
  disjoint : Pairwise fun i j =>
    Disjoint {v | v ∈ (path i).support} {v | v ∈ (path j).support}

/-- A linkage persists when edges are added. -/
def PairLinkage.mapLe {V ι : Type*} {G H : SimpleGraph V} {X : Set V}
    {terminal : Sum ι ι ↪ V} (L : PairLinkage G X terminal) (h : G ≤ H) :
    PairLinkage H X terminal where
  path i := (L.path i).mapLe h
  isPath i := (L.isPath i).mapLe h
  avoids i := by simpa only [walkInteriorSet_mapLe] using L.avoids i
  disjoint i j hij := by
    simpa only [Walk.support_mapLe_eq_support] using L.disjoint hij

/-- Every finite prescribed pairing of distinct vertices in `X` has a
linkage whose internal vertices avoid `X`. -/
def IsLinkedSet {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∀ (ι : Type) [Fintype ι] (terminal : Sum ι ι ↪ V),
    Set.range terminal ⊆ X → Nonempty (PairLinkage G X terminal)

/-- A graph is `k`-linked when each set of at most `2*k` vertices is linked. -/
def IsKLinked {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ X : Set V, X.Finite → X.ncard ≤ 2 * k → IsLinkedSet G X

theorem IsLinkedSet.mono {V : Type*} {G H : SimpleGraph V} {X : Set V}
    (hX : IsLinkedSet G X) (h : G ≤ H) : IsLinkedSet H X := by
  intro ι _ terminal hterminal
  exact (hX ι terminal hterminal).map fun L => L.mapLe h

def PairLinkage.of_isEmpty {V ι : Type*} [IsEmpty ι] (G : SimpleGraph V)
    (X : Set V) (terminal : Sum ι ι ↪ V) : PairLinkage G X terminal where
  path i := isEmptyElim i
  isPath i := isEmptyElim i
  avoids i := isEmptyElim i
  disjoint i := isEmptyElim i

theorem isLinkedSet_empty {V : Type*} (G : SimpleGraph V) :
    IsLinkedSet G ∅ := by
  intro ι _ terminal hrange
  let _ : IsEmpty ι := ⟨fun i => by
    have hi : terminal (.inl i) ∈ (∅ : Set V) :=
      hrange ⟨.inl i, rfl⟩
    exact hi.elim⟩
  exact ⟨PairLinkage.of_isEmpty G ∅ terminal⟩

theorem isKLinked_zero {V : Type*} (G : SimpleGraph V) : IsKLinked G 0 := by
  intro X hX hcard
  have hzero : X.ncard = 0 := by omega
  have hEmpty : X = ∅ := Set.ncard_eq_zero hX |>.mp hzero
  simpa [hEmpty] using isLinkedSet_empty G

/-! ### The finite set form of Menger's theorem -/

/-- An explicitly `k`-indexed family of fully vertex-disjoint `A`--`B`
paths. -/
structure ABLinkage {V : Type} (G : SimpleGraph V) (A B : Set V) (k : ℕ) where
  left : Fin k → V
  right : Fin k → V
  path : ∀ i, G.Walk (left i) (right i)
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ B
  isPath : ∀ i, (path i).IsPath
  disjoint : Pairwise fun i j =>
    Disjoint {v | v ∈ (path i).support} {v | v ∈ (path j).support}

/-- The finite specialization of the proved Erdős--Menger theorem in
`ErdosProblems.Erdos599`. -/
theorem finite_hasErdosMengerPair {V : Type} [Finite V]
    (G : SimpleGraph V) (A B : Set V) :
    Erdos599.Countable.HasErdosMengerPair G A B := by
  exact Erdos599.Countable.hasErdosMengerPair_of_safePathRemoval_of_countable
    Erdos599.Countable.safePathRemoval G A B (Set.toFinite A).countable

theorem finite_pathHypergraph_hasKonigPair {V : Type} [Finite V]
    (G : SimpleGraph V) (A B : Set V) :
    Erdos599.Countable.HasKonigPair (Erdos599.Countable.pathHypergraph G A B) := by
  exact Erdos599.Countable.hasKonigPair_pathHypergraph_of_hasErdosMengerPair
    (finite_hasErdosMengerPair G A B)

/-- Weak duality for finite hypergraph packings and covers. -/
theorem packing_ncard_le_cover_ncard {V : Type} {F P : Set (Set V)}
    {S : Set V} (hP : Erdos599.Countable.IsPacking F P) (hS : Erdos599.Countable.IsCover F S)
    (hPfinite : P.Finite) (hSfinite : S.Finite) : P.ncard ≤ S.ncard := by
  classical
  have hex (e : P) : ∃ v, v ∈ (e : Set V) ∧ v ∈ S :=
    hS (e : Set V) (hP.1 e.property)
  choose chosen hchosen_edge hchosen_S using hex
  let point : P → S := fun e => ⟨chosen e, hchosen_S e⟩
  have hpoint_injective : Function.Injective point := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    have hd := hP.2 (e : Set V) e.property (f : Set V) f.property hne
    have hval : chosen e = chosen f := congrArg Subtype.val hef
    exact Set.disjoint_left.mp hd (hchosen_edge e) (hval ▸ hchosen_edge f)
  let _ : Fintype P := hPfinite.fintype
  let _ : Fintype S := hSfinite.fintype
  rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
  exact Fintype.card_le_of_injective point hpoint_injective

/-- A finite structural König pair has equally large packing and cover. -/
theorem ncard_eq_of_hasKonigPair {V : Type} [Finite V]
    {F : Set (Set V)} (h : Erdos599.Countable.HasKonigPair F) :
    ∃ P S, Erdos599.Countable.IsPacking F P ∧ Erdos599.Countable.IsCover F S ∧
      P.ncard = S.ncard := by
  classical
  rcases h with ⟨P, S, hPF, hdisj, hSsub, horth, hcover⟩
  have hPfinite : P.Finite := Set.toFinite P
  have hSfinite : S.Finite := Set.toFinite S
  let _ : Fintype P := hPfinite.fintype
  let _ : Fintype S := hSfinite.fintype
  have hex (e : P) : ∃ v, v ∈ S ∧ v ∈ (e : Set V) :=
    (horth (e : Set V) e.property).exists
  choose chosen hchosen_S hchosen_edge using hex
  let point : P → S := fun e => ⟨chosen e, hchosen_S e⟩
  have hpoint_injective : Function.Injective point := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    have hd := hdisj (e : Set V) e.property (f : Set V) f.property hne
    have hval : chosen e = chosen f := congrArg Subtype.val hef
    exact Set.disjoint_left.mp hd (hchosen_edge e) (hval ▸ hchosen_edge f)
  have hpoint_surjective : Function.Surjective point := by
    intro s
    rcases hSsub s.property with ⟨e, heP, hse⟩
    let i : P := ⟨e, heP⟩
    refine ⟨i, Subtype.ext ?_⟩
    exact (horth e heP).unique ⟨hchosen_S i, hchosen_edge i⟩
      ⟨s.property, hse⟩
  refine ⟨P, S, ⟨hPF, hdisj⟩, hcover, ?_⟩
  rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
  exact Fintype.card_congr (Equiv.ofBijective point
    ⟨hpoint_injective, hpoint_surjective⟩)

/-- Numerical finite vertex Menger for the `A`--`B` path hypergraph. -/
theorem finite_pathHypergraph_minmax {V : Type} [Finite V]
    (G : SimpleGraph V) (A B : Set V) :
    ∃ P S,
      Erdos599.Countable.IsPacking (Erdos599.Countable.pathHypergraph G A B) P ∧
      Erdos599.Countable.IsCover (Erdos599.Countable.pathHypergraph G A B) S ∧
      P.ncard = S.ncard ∧
      (∀ Q, Erdos599.Countable.IsPacking (Erdos599.Countable.pathHypergraph G A B) Q →
        Q.ncard ≤ P.ncard) ∧
      (∀ T, Erdos599.Countable.IsCover (Erdos599.Countable.pathHypergraph G A B) T →
        S.ncard ≤ T.ncard) := by
  rcases ncard_eq_of_hasKonigPair
      (finite_pathHypergraph_hasKonigPair G A B) with
    ⟨P, S, hP, hS, hcard⟩
  refine ⟨P, S, hP, hS, hcard, ?_, ?_⟩
  · intro Q hQ
    simpa [hcard] using packing_ncard_le_cover_ncard hQ hS
      (Set.toFinite Q) (Set.toFinite S)
  · intro T hT
    simpa [hcard] using packing_ncard_le_cover_ncard hP hT
      (Set.toFinite P) (Set.toFinite T)

/-- If every `A`--`B` separator has at least `k` vertices, there are `k`
fully vertex-disjoint `A`--`B` paths. -/
theorem exists_abLinkage_of_forall_separator_ncard_ge {V : Type} [Finite V]
    (G : SimpleGraph V) (A B : Set V) (k : ℕ)
    (hsep : ∀ S, Erdos599.Countable.Separates G A B S → k ≤ S.ncard) :
    Nonempty (ABLinkage G A B k) := by
  classical
  rcases finite_pathHypergraph_minmax G A B with
    ⟨P, S, hP, hS, hcard, _hmax, _hmin⟩
  have hkP : k ≤ P.ncard := by
    rw [hcard]
    exact hsep S (Erdos599.Countable.isCover_pathHypergraph_iff.mp hS)
  have hPfinite : P.Finite := Set.toFinite P
  let _ : Fintype P := hPfinite.fintype
  have hkcard : Fintype.card (Fin k) ≤ Fintype.card P := by
    simpa [Set.fintypeCard_eq_ncard] using hkP
  rcases Function.Embedding.nonempty_of_card_le hkcard with ⟨emb⟩
  have hedge (i : Fin k) : (emb i : Set V) ∈
      Erdos599.Countable.pathHypergraph G A B := hP.1 (emb i).property
  let q (i : Fin k) : Erdos599.Countable.ABPath G A B := Classical.choose (hedge i)
  have hq (i : Fin k) : (q i).vertices = (emb i : Set V) :=
    Classical.choose_spec (hedge i)
  refine ⟨{
    left := fun i => (q i).left
    right := fun i => (q i).right
    path := fun i => (q i).walk
    left_mem := fun i => (q i).left_mem
    right_mem := fun i => (q i).right_mem
    isPath := fun i => (q i).isPath
    disjoint := ?_ }⟩
  intro i j hij
  have hne : (emb i : Set V) ≠ (emb j : Set V) := by
    intro h
    apply hij
    apply emb.injective
    exact Subtype.ext h
  have hd := hP.2 (emb i : Set V) (emb i).property
    (emb j : Set V) (emb j).property hne
  change Disjoint (q i).vertices (q j).vertices
  rw [hq i, hq j]
  exact hd

/-! ### Finite separations and vertex connectivity -/

/-- A vertex separation: the two sides cover the graph, and no edge crosses
between their strict parts. -/
structure Separation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  cover : left ∪ right = Finset.univ
  not_adj : ∀ ⦃u v⦄, u ∈ left → u ∉ right → v ∈ right → v ∉ left → ¬G.Adj u v

namespace Separation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The separator is the intersection of the two sides. -/
def separator (s : Separation G) : Finset V := s.left ∩ s.right

/-- The order of a separation. -/
def order (s : Separation G) : ℕ := s.separator.card

/-- Both strict sides of a proper separation are nonempty. -/
def Proper (s : Separation G) : Prop :=
  (s.left \ s.right).Nonempty ∧ (s.right \ s.left).Nonempty

end Separation

/-- Separation-based vertex connectivity.  For finite graphs this is the
standard equivalent form of survival of connectedness after deleting fewer
than `k` vertices. -/
def IsKConnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ s : Separation G, s.Proper → k ≤ s.order

namespace Separation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma mem_left_or_mem_right (s : Separation G) (v : V) :
    v ∈ s.left ∨ v ∈ s.right := by
  have h : v ∈ s.left ∪ s.right := by
    rw [s.cover]
    exact Finset.mem_univ v
  exact Finset.mem_union.mp h

lemma strict_left_disjoint_strict_right (s : Separation G) :
    Disjoint (s.left \ s.right) (s.right \ s.left) := by
  apply Finset.disjoint_left.2
  intro v hvL hvR
  rw [Finset.mem_sdiff] at hvL hvR
  exact hvL.2 hvR.1

lemma left_eq_strictLeft_union_separator (s : Separation G) :
    s.left = (s.left \ s.right) ∪ s.separator := by
  ext v
  simp [separator]
  tauto

lemma right_eq_strictRight_union_separator (s : Separation G) :
    s.right = (s.right \ s.left) ∪ s.separator := by
  ext v
  simp [separator]
  tauto

lemma univ_eq_strictLeft_union_separator_union_strictRight (s : Separation G) :
    Finset.univ = (s.left \ s.right) ∪ s.separator ∪ (s.right \ s.left) := by
  ext v
  have hv := s.mem_left_or_mem_right v
  simp [separator]
  tauto

lemma strictLeft_card_add_order_add_strictRight_card (s : Separation G) :
    (s.left \ s.right).card + s.order + (s.right \ s.left).card =
      Fintype.card V := by
  rw [← Finset.card_univ, s.univ_eq_strictLeft_union_separator_union_strictRight]
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint]
    · rfl
    · apply Finset.disjoint_left.2
      intro v hvL hvS
      rw [Finset.mem_sdiff] at hvL
      exact hvL.2 (Finset.mem_inter.1 hvS).2
  · apply Finset.disjoint_left.2
    intro v hvUS hvR
    rw [Finset.mem_union] at hvUS
    rw [Finset.mem_sdiff] at hvR
    rcases hvUS with hvL | hvS
    · exact hvR.2 (Finset.mem_sdiff.1 hvL).1
    · exact hvR.2 (Finset.mem_inter.1 hvS).1

lemma not_adj_strict (s : Separation G) {u v : V}
    (hu : u ∈ s.left \ s.right) (hv : v ∈ s.right \ s.left) :
    ¬ G.Adj u v := by
  rw [Finset.mem_sdiff] at hu hv
  exact s.not_adj hu.1 hu.2 hv.1 hv.2

/-- Every walk from one strict side of a separation to the other meets its
separator. -/
lemma walk_meets_separator (s : Separation G) {u v : V} (p : G.Walk u v)
    (hu : u ∈ s.left \ s.right) (hv : v ∈ s.right \ s.left) :
    ∃ x, x ∈ p.support ∧ x ∈ s.separator := by
  induction p with
  | nil =>
      rw [Finset.mem_sdiff] at hu hv
      exact (hv.2 hu.1).elim
  | @cons u w v huw p ih =>
      rw [Finset.mem_sdiff] at hu hv
      rcases s.mem_left_or_mem_right w with hwL | hwR
      · by_cases hwR : w ∈ s.right
        · exact ⟨w, by simp, Finset.mem_inter.2 ⟨hwL, hwR⟩⟩
        · obtain ⟨x, hxp, hxs⟩ := ih (Finset.mem_sdiff.2 ⟨hwL, hwR⟩)
            (Finset.mem_sdiff.2 hv)
          exact ⟨x, by simp [hxp], hxs⟩
      · by_cases hwL : w ∈ s.left
        · exact ⟨w, by simp, Finset.mem_inter.2 ⟨hwL, hwR⟩⟩
        · exact (s.not_adj hu.1 hu.2 hwR hwL huw).elim

/-- The separation isolating a vertex from all of its non-neighbours. -/
def isolate [DecidableRel G.Adj] (v : V) : Separation G where
  left := insert v (G.neighborFinset v)
  right := Finset.univ.erase v
  cover := by
    ext x
    simp
    tauto
  not_adj := by
    intro u w huL huR hwR hwL
    have huv : u = v := by simpa using huR
    subst u
    rw [Finset.mem_insert] at hwL
    have hwn : w ∉ G.neighborFinset v := fun h => hwL (Or.inr h)
    simpa [G.mem_neighborFinset] using hwn

@[simp] lemma separator_isolate [DecidableRel G.Adj] (v : V) :
    (isolate (G := G) v).separator = G.neighborFinset v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [separator, isolate, G.notMem_neighborFinset_self]
  · simp [separator, isolate, hw]

@[simp] lemma order_isolate [DecidableRel G.Adj] (v : V) :
    (isolate (G := G) v).order = G.degree v := by
  simp [order]

lemma proper_isolate [DecidableRel G.Adj] (v : V)
    (hcard : G.degree v + 1 < Fintype.card V) :
    (isolate (G := G) v).Proper := by
  constructor
  · exact ⟨v, by simp [isolate, G.notMem_neighborFinset_self]⟩
  · have hleft : (insert v (G.neighborFinset v)).card <
        (Finset.univ : Finset V).card := by
      simpa [G.notMem_neighborFinset_self] using hcard
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hleft
    exact ⟨w, by simpa [isolate] using hw⟩

/-- Add a deleted vertex set to both sides of a separation of the graph
induced on its complement. -/
def liftDelete (S : Finset V)
    (t : Separation (G.induce {v : V | v ∉ S})) : Separation G where
  left := S ∪ t.left.image Subtype.val
  right := S ∪ t.right.image Subtype.val
  cover := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    by_cases hv : v ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
    · let w : {v : V // v ∉ S} := ⟨v, hv⟩
      have hw := t.mem_left_or_mem_right w
      rcases hw with hw | hw
      · exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
          Finset.mem_image.2 ⟨w, hw, rfl⟩
      · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
          Finset.mem_image.2 ⟨w, hw, rfl⟩
  not_adj := by
    intro u v huL huR hvR hvL
    have huS : u ∉ S := fun hu => huR (Finset.mem_union_left _ hu)
    have hvS : v ∉ S := fun hv => hvL (Finset.mem_union_left _ hv)
    let u' : {v : V // v ∉ S} := ⟨u, huS⟩
    let v' : {v : V // v ∉ S} := ⟨v, hvS⟩
    have huLt : u' ∈ t.left := by
      rw [Finset.mem_union] at huL
      rcases huL with huL | huL
      · exact (huS huL).elim
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 huL
        have hwu : w = u' := Subtype.ext hw
        simpa [hwu] using hwt
    have huRt : u' ∉ t.right := by
      intro h
      apply huR
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u', h, rfl⟩)
    have hvRt : v' ∈ t.right := by
      rw [Finset.mem_union] at hvR
      rcases hvR with hvR | hvR
      · exact (hvS hvR).elim
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 hvR
        have hwv : w = v' := Subtype.ext hw
        simpa [hwv] using hwt
    have hvLt : v' ∉ t.left := by
      intro h
      apply hvL
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨v', h, rfl⟩)
    exact fun huv => t.not_adj huLt huRt hvRt hvLt (by simpa [u', v'] using huv)

@[simp] lemma separator_liftDelete (S : Finset V)
    (t : Separation (G.induce {v : V | v ∉ S})) :
    (liftDelete S t).separator = S ∪ t.separator.image Subtype.val := by
  ext v
  by_cases hv : v ∈ S
  · simp [separator, liftDelete, hv]
  · simp only [separator, liftDelete, Finset.mem_inter, Finset.mem_union,
      Finset.mem_image, hv, false_or]
    constructor
    · rintro ⟨⟨u, huL, huv⟩, ⟨w, hwR, hwv⟩⟩
      have huw : u = w := Subtype.ext (huv.trans hwv.symm)
      subst w
      exact ⟨u, ⟨huL, hwR⟩, huv⟩
    · rintro ⟨u, hu, huv⟩
      exact ⟨⟨u, hu.1, huv⟩, ⟨u, hu.2, huv⟩⟩

lemma order_liftDelete (S : Finset V)
    (t : Separation (G.induce {v : V | v ∉ S})) :
    (liftDelete S t).order = S.card + t.order := by
  rw [order, separator_liftDelete, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective]
    · rfl
    · exact Subtype.val_injective
  · apply Finset.disjoint_left.2
    intro v hvS hvI
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hvI
    exact w.property hvS

lemma proper_liftDelete (S : Finset V)
    (t : Separation (G.induce {v : V | v ∉ S})) (ht : t.Proper) :
    (liftDelete S t).Proper := by
  rw [Proper] at ht ⊢
  rcases ht with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  rw [Finset.mem_sdiff] at hu hv
  rcases hu with ⟨huL, huR⟩
  rcases hv with ⟨hvR, hvL⟩
  constructor
  · refine ⟨u.1, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, huL, rfl⟩)
    · intro hu
      simp only [liftDelete, Finset.mem_union] at hu
      rcases hu with huS | hu
      · exact u.property huS
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 hu
        have hwu : w = u := Subtype.ext hw
        exact huR (hwu ▸ hwt)
  · refine ⟨v.1, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨v, hvR, rfl⟩)
    · intro hv
      simp only [liftDelete, Finset.mem_union] at hv
      rcases hv with hvS | hv
      · exact v.property hvS
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 hv
        have hwv : w = v := Subtype.ext hw
        exact hvL (hwv ▸ hwt)

/-- The zero-order separation into the component reachable from `u` and its
complement. -/
noncomputable def reachableSeparation (G : SimpleGraph V) (u : V) : Separation G := by
  classical
  let L : Finset V := Finset.univ.filter (G.Reachable u)
  exact
    { left := L
      right := Lᶜ
      cover := Finset.union_compl L
      not_adj := by
        intro x y hxL _ hyR _ hxy
        have hux : G.Reachable u x := by simpa [L] using hxL
        have huy : ¬G.Reachable u y := by simpa [L] using hyR
        exact huy (hux.trans hxy.reachable) }

@[simp] lemma separator_reachableSeparation (G : SimpleGraph V) (u : V) :
    (reachableSeparation G u).separator = ∅ := by
  classical
  ext x
  simp [separator, reachableSeparation]

@[simp] lemma order_reachableSeparation (G : SimpleGraph V) (u : V) :
    (reachableSeparation G u).order = 0 := by
  simp [order]

lemma proper_reachableSeparation (G : SimpleGraph V) {u v : V}
    (huv : ¬G.Reachable u v) : (reachableSeparation G u).Proper := by
  classical
  rw [Proper]
  constructor
  · refine ⟨u, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩ <;>
      simp [reachableSeparation, SimpleGraph.Reachable.rfl]
  · refine ⟨v, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩ <;>
      simp [reachableSeparation, huv]

end Separation

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_deleteVertices (S : Finset V) :
    Fintype.card {v : V // v ∉ S} = Fintype.card V - S.card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_subtype_compl (fun v : V => v ∈ S))

lemma IsKConnected.degree_ge {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hG : IsKConnected G k) (v : V) : k ≤ G.degree v := by
  by_contra h
  have hdeg : G.degree v < k := Nat.lt_of_not_ge h
  have hproper : (Separation.isolate (G := G) v).Proper := by
    apply Separation.proper_isolate
    exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hdeg) hG.1
  have := hG.2 (Separation.isolate (G := G) v) hproper
  exact (Nat.not_le_of_lt hdeg) (by simpa using this)

/-- Deleting `m < k` vertices from a `k`-connected graph leaves a
`(k-m)`-connected graph. -/
lemma IsKConnected.induce_delete {G : SimpleGraph V} {k : ℕ}
    (hG : IsKConnected G k) (S : Finset V) (hS : S.card < k) :
    IsKConnected (G.induce {v : V | v ∉ S}) (k - S.card) := by
  constructor
  · change k - S.card < Fintype.card {v : V // v ∉ S}
    rw [card_deleteVertices]
    have hk := hG.1
    omega
  · intro t ht
    have h := hG.2 (Separation.liftDelete S t)
      (Separation.proper_liftDelete S t ht)
    rw [Separation.order_liftDelete] at h
    omega

lemma IsKConnected.preconnected {G : SimpleGraph V} {k : ℕ}
    (hG : IsKConnected G k) (hk : 0 < k) : G.Preconnected := by
  intro u v
  by_contra huv
  have h := hG.2 (Separation.reachableSeparation G u)
    (Separation.proper_reachableSeparation G huv)
  rw [Separation.order_reachableSeparation] at h
  omega

/-! ### Numerical finite Menger consequences -/

/-- Threshold form of finite vertex Menger: either `q` fully disjoint
`A`--`B` paths exist, or fewer than `q` vertices meet every `A`--`B` path. -/
theorem finite_vertex_menger {V : Type} [Finite V]
    (G : SimpleGraph V) (A B : Set V) (q : ℕ) :
    Nonempty (ABLinkage G A B q) ∨
      ∃ S : Set V, S.Finite ∧ S.ncard < q ∧ Erdos599.Countable.Separates G A B S := by
  classical
  by_cases hlarge : ∀ S, Erdos599.Countable.Separates G A B S → q ≤ S.ncard
  · exact Or.inl (exists_abLinkage_of_forall_separator_ncard_ge G A B q hlarge)
  · push Not at hlarge
    obtain ⟨S, hsep, hsmall⟩ := hlarge
    exact Or.inr ⟨S, Set.toFinite S, hsmall, hsep⟩

/-- The separator of a finite separation meets every path between its strict
sides. -/
theorem separation_separator_separates_strict_sides
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (s : Separation G) :
    Erdos599.Countable.Separates G
      (s.left \ s.right : Finset V)
      (s.right \ s.left : Finset V)
      (s.separator : Finset V) := by
  classical
  intro a ha b hb p _hp
  obtain ⟨x, hxp, hxs⟩ := s.walk_meets_separator p ha hb
  exact ⟨x, hxp, hxs⟩

/-- A path separator disjoint from nonempty source and target sets induces a
proper separation whose separator has the same cardinality. -/
theorem exists_proper_separation_of_path_separator
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B S : Set V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hsep : Erdos599.Countable.Separates G A B S) :
    ∃ s : Separation G, s.Proper ∧ s.separator.card = S.ncard := by
  classical
  let H := Erdos599.Countable.outsideGraph G S
  let R : Finset V := Finset.univ.filter fun v => ∃ a ∈ A, H.Reachable a v
  have source_strict (a : V) (ha : a ∈ A) :
      a ∈ (S.toFinset ∪ R) \ (S.toFinset ∪ (Finset.univ \ R)) := by
    have haS : a ∉ S := Set.disjoint_left.mp hAS ha
    have haR : a ∈ R := by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, SimpleGraph.Reachable.refl a⟩
    simp only [Finset.mem_sdiff, Finset.mem_union, Set.mem_toFinset,
      Finset.mem_univ, true_and]
    exact ⟨Or.inr haR, fun h => h.elim haS (fun hnotR => hnotR haR)⟩
  have target_strict (b : V) (hb : b ∈ B) :
      b ∈ (S.toFinset ∪ (Finset.univ \ R)) \ (S.toFinset ∪ R) := by
    have hbS : b ∉ S := Set.disjoint_left.mp hBS hb
    have hbR : b ∉ R := by
      intro hbR
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hbR
      rcases hbR with ⟨a, ha, hab⟩
      rcases hab.exists_isPath with ⟨q, hq⟩
      let qG := q.mapLe (Erdos599.Countable.outsideGraph_le G S)
      rcases hsep a ha b hb qG (hq.mapLe _) with ⟨x, hxqG, hxS⟩
      have hxq : x ∈ q.support := by
        simpa [qG, Walk.support_mapLe_eq_support] using hxqG
      have haS : a ∉ S := Set.disjoint_left.mp hAS ha
      exact (Erdos599.Countable.Walk.vertex_not_mem_of_outsideGraph q haS hxq) hxS
    simp only [Finset.mem_sdiff, Finset.mem_union, Set.mem_toFinset,
      Finset.mem_univ, true_and]
    exact ⟨Or.inr hbR, fun h => h.elim hbS hbR⟩
  let s : Separation G := {
    left := S.toFinset ∪ R
    right := S.toFinset ∪ (Finset.univ \ R)
    cover := by
      ext v
      simp only [Finset.mem_union, Set.mem_toFinset, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      tauto
    not_adj := by
      intro u v huL huR hvR hvL huv
      have huS : u ∉ S := by
        intro huS
        exact huR (Finset.mem_union_left _ (Set.mem_toFinset.mpr huS))
      have huReach : u ∈ R := by
        rcases Finset.mem_union.mp huL with huSin | huRin
        · exact (huS (Set.mem_toFinset.mp huSin)).elim
        · exact huRin
      have hvS : v ∉ S := by
        intro hvS
        exact hvL (Finset.mem_union_left _ (Set.mem_toFinset.mpr hvS))
      have hvNotReach : v ∉ R := by
        intro hvReach
        exact hvL (Finset.mem_union_right _ hvReach)
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at huReach
      rcases huReach with ⟨a, ha, hau⟩
      have huvH : H.Adj u v := ⟨huv, huS, hvS⟩
      apply hvNotReach
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, hau.trans huvH.reachable⟩
  }
  refine ⟨s, ?_, ?_⟩
  · constructor
    · rcases hA with ⟨a, ha⟩
      exact ⟨a, source_strict a ha⟩
    · rcases hB with ⟨b, hb⟩
      exact ⟨b, target_strict b hb⟩
  · rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp only [Separation.separator, s, Finset.mem_inter,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Set.mem_toFinset]
    tauto

/-- In a `k`-connected graph, every separator between two sets of cardinality
at least `k` has cardinality at least `k`. -/
theorem separator_ncard_ge_of_isKConnected
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B S : Set V} {k : ℕ}
    (hconn : IsKConnected G k)
    (hAcard : k ≤ A.ncard) (hBcard : k ≤ B.ncard)
    (hsep : Erdos599.Countable.Separates G A B S) :
    k ≤ S.ncard := by
  by_contra hSk
  have hSlt : S.ncard < k := Nat.lt_of_not_ge hSk
  have hA0 : (A \ S).Nonempty := by
    by_contra hne
    have hsub : A ⊆ S := by
      intro a ha
      by_contra haS
      exact hne ⟨a, ha, haS⟩
    have hcard := Set.ncard_le_ncard hsub
    omega
  have hB0 : (B \ S).Nonempty := by
    by_contra hne
    have hsub : B ⊆ S := by
      intro b hb
      by_contra hbS
      exact hne ⟨b, hb, hbS⟩
    have hcard := Set.ncard_le_ncard hsub
    omega
  have hsep0 : Erdos599.Countable.Separates G (A \ S) (B \ S) S := by
    intro a ha b hb p hp
    exact hsep a ha.1 b hb.1 p hp
  rcases exists_proper_separation_of_path_separator hA0 hB0
      Set.disjoint_sdiff_left Set.disjoint_sdiff_left hsep0 with
    ⟨s, hsproper, hsorder⟩
  have hkorder : k ≤ s.separator.card := hconn.2 s hsproper
  rw [hsorder] at hkorder
  omega

/-- The finite vertex-Menger consequence in the separation-based connectivity
language used throughout this file. -/
theorem abLinkage_of_isKConnected
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B : Set V} {k : ℕ}
    (hconn : IsKConnected G k)
    (hAcard : k ≤ A.ncard) (hBcard : k ≤ B.ncard) :
    Nonempty (ABLinkage G A B k) :=
  exists_abLinkage_of_forall_separator_ncard_ge G A B k fun _S hsep =>
    separator_ncard_ge_of_isKConnected hconn hAcard hBcard hsep

/-! ### Assembling a clique subdivision from a linked dense core -/

omit [Fintype V] [DecidableEq V] in
private lemma walkInteriorSet_cons_concat_subset {G : SimpleGraph V}
    {a x y b : V} {hax : G.Adj a x} {p : G.Walk x y}
    {hyb : G.Adj y b} :
    walkInteriorSet ((p.cons hax).concat hyb) ⊆ {v | v ∈ p.support} := by
  intro v hv
  rcases hv with ⟨hv, hva, hvb⟩
  simp only [SimpleGraph.Walk.support_concat, SimpleGraph.Walk.support_cons,
    List.mem_append, List.mem_cons] at hv
  rcases hv with ((rfl | hv) | hv)
  · exact (hva rfl).elim
  · exact hv
  · rcases hv with rfl | hv
    · exact (hvb rfl).elim
    · simp at hv

private def induceInclusion {G : SimpleGraph V} (S : Set V) :
    G.induce S →g G where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact huv

omit [Fintype V] [DecidableEq V] in
@[simp] private lemma induceInclusion_apply {G : SimpleGraph V}
    (S : Set V) (x : S) :
    induceInclusion (G := G) S x = (x : V) := rfl

/-- A clique subdivision in an induced graph is also one in the host graph. -/
def CliqueSubdivision.liftInduce {G : SimpleGraph V} {S : Set V} {r : ℕ}
    (s : CliqueSubdivision (G.induce S) r) : CliqueSubdivision G r := by
  let inclusion : G.induce S →g G := induceInclusion S
  let valueEmbedding : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let branch : Fin r ↪ V := s.branch.trans valueEmbedding
  let mappedPath (e : CliqueEdge r) := (s.path e).map inclusion
  have branch_apply (i : Fin r) : branch i = (s.branch i : V) := by
    rfl
  have path_preimage (e : CliqueEdge r) {x : V}
      (hx : x ∈ walkInteriorSet (mappedPath e)) :
      ∃ y ∈ walkInteriorSet (s.path e), (y : V) = x := by
    rcases hx with ⟨hxsupp, hxstart, hxend⟩
    rw [SimpleGraph.Walk.support_map] at hxsupp
    obtain ⟨y, hysupp, hyx⟩ := List.mem_map.mp hxsupp
    have hyx' : (y : V) = x := by
      simpa [inclusion] using hyx
    refine ⟨y, ⟨hysupp, ?_, ?_⟩, hyx'⟩
    · intro hy
      subst y
      apply hxstart
      simpa [inclusion, branch_apply] using hyx'.symm
    · intro hy
      subst y
      apply hxend
      simpa [inclusion, branch_apply] using hyx'.symm
  refine {
    branch := branch
    path := mappedPath
    path_isPath := fun e => (s.path_isPath e).map Subtype.val_injective
    interior_avoids_branch := ?_
    interior_pairwise := ?_
  }
  · intro e
    rw [Set.disjoint_left]
    intro x hx hxbranch
    obtain ⟨y, hy, hyx⟩ := path_preimage e hx
    obtain ⟨i, hix⟩ := hxbranch
    have hybranch : y = s.branch i := by
      apply Subtype.ext
      rw [hyx, ← hix]
      exact branch_apply i
    exact (Set.disjoint_left.mp (s.interior_avoids_branch e)) hy
      ⟨i, hybranch.symm⟩
  · intro e e' hee'
    rw [Set.disjoint_left]
    intro x hxe hxe'
    obtain ⟨y, hye, hyx⟩ := path_preimage e hxe
    obtain ⟨y', hye', hy'x⟩ := path_preimage e' hxe'
    have hyy' : y = y' := Subtype.ext (hyx.trans hy'x.symm)
    subst y'
    exact (Set.disjoint_left.mp (s.interior_pairwise hee')) hye hye'

omit [Fintype V] [DecidableEq V] in
theorem ContainsCliqueSubdivision.liftInduce {G : SimpleGraph V}
    {S : Set V} {r : ℕ}
    (hS : ContainsCliqueSubdivision (G.induce S) r) :
    ContainsCliqueSubdivision G r :=
  hS.map CliqueSubdivision.liftInduce

private def privateTerminal {r : ℕ}
    (branch : Fin r ↪ V)
    (neighbor : Sum (CliqueEdge r) (CliqueEdge r) ↪ V)
    (hprivate : ∀ z, neighbor z ∉ Set.range branch) :
    Sum (CliqueEdge r) (CliqueEdge r) ↪
      {v : V // v ∉ Set.range branch} where
  toFun z := ⟨neighbor z, hprivate z⟩
  inj' := by
    intro z z' h
    apply neighbor.injective
    exact congrArg Subtype.val h

omit [Fintype V] [DecidableEq V] in
@[simp] private lemma privateTerminal_apply {r : ℕ}
    (branch : Fin r ↪ V)
    (neighbor : Sum (CliqueEdge r) (CliqueEdge r) ↪ V)
    (hprivate : ∀ z, neighbor z ∉ Set.range branch)
    (z : Sum (CliqueEdge r) (CliqueEdge r)) :
    ((privateTerminal branch neighbor hprivate z :
      {v : V // v ∉ Set.range branch}) : V) = neighbor z := rfl

omit [Fintype V] [DecidableEq V] in
/-- Distinct private neighbors and a linkage in the graph left after deleting
the branch vertices assemble to a subdivision of `K_r`. -/
theorem subdivision_of_linked_private_neighbors {G : SimpleGraph V} {r : ℕ}
    (branch : Fin r ↪ V)
    (neighbor : Sum (CliqueEdge r) (CliqueEdge r) ↪ V)
    (hprivate : ∀ z, neighbor z ∉ Set.range branch)
    (hadj_left : ∀ e, G.Adj (branch e.1.1) (neighbor (.inl e)))
    (hadj_right : ∀ e, G.Adj (neighbor (.inr e)) (branch e.1.2))
    (hlinked : IsKLinked (G.induce {v | v ∉ Set.range branch})
      (Fintype.card (CliqueEdge r))) :
    ContainsCliqueSubdivision G r := by
  let R : Set V := {v | v ∉ Set.range branch}
  let terminal : Sum (CliqueEdge r) (CliqueEdge r) ↪ R :=
    privateTerminal branch neighbor hprivate
  have terminal_coe (z : Sum (CliqueEdge r) (CliqueEdge r)) :
      (terminal z : V) = neighbor z := by
    rfl
  have hrange_fin : (Set.range terminal).Finite := Set.finite_range terminal
  have hrange_card : (Set.range terminal).ncard =
      2 * Fintype.card (CliqueEdge r) := by
    rw [Set.ncard_range_of_injective terminal.injective]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum]
    omega
  have hterminal_linked : IsLinkedSet (G.induce R) (Set.range terminal) := by
    apply hlinked (Set.range terminal) hrange_fin
    rw [hrange_card]
  obtain ⟨linkage⟩ := hterminal_linked (CliqueEdge r) terminal (by rfl)
  let inclusion : G.induce R →g G := induceInclusion R
  let middle (e : CliqueEdge r) := (linkage.path e).map inclusion
  have hadjL (e : CliqueEdge r) :
      G.Adj (branch e.1.1) (inclusion (terminal (.inl e))) := by
    rw [induceInclusion_apply, terminal_coe]
    exact hadj_left e
  have hadjR (e : CliqueEdge r) :
      G.Adj (inclusion (terminal (.inr e))) (branch e.1.2) := by
    rw [induceInclusion_apply, terminal_coe]
    exact hadj_right e
  let cliquePath (e : CliqueEdge r) :
      G.Walk (branch e.1.1) (branch e.1.2) :=
    ((middle e).cons (hadjL e)).concat (hadjR e)
  refine ⟨{
    branch := branch
    path := cliquePath
    path_isPath := ?_
    interior_avoids_branch := ?_
    interior_pairwise := ?_
  }⟩
  · intro e
    have hmiddle_path : (middle e).IsPath := by
      exact (linkage.isPath e).map Subtype.val_injective
    have hleft_absent : branch e.1.1 ∉ (middle e).support := by
      intro hmem
      rw [SimpleGraph.Walk.support_map] at hmem
      obtain ⟨z, _hz, hzval⟩ := List.mem_map.mp hmem
      have hzR : (z : V) ∉ Set.range branch := z.property
      have hzval' : (z : V) = branch e.1.1 := by
        simpa [inclusion] using hzval
      exact hzR ⟨e.1.1, hzval'.symm⟩
    have hcons_path : ((middle e).cons (hadjL e)).IsPath :=
      hmiddle_path.cons hleft_absent
    apply hcons_path.concat
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    rintro (heq | hmem)
    · have hij : e.1.1 ≠ e.1.2 := ne_of_lt e.2
      exact hij (branch.injective heq.symm)
    · rw [SimpleGraph.Walk.support_map] at hmem
      obtain ⟨z, _hz, hzval⟩ := List.mem_map.mp hmem
      have hzR : (z : V) ∉ Set.range branch := z.property
      have hzval' : (z : V) = branch e.1.2 := by
        simpa [inclusion] using hzval
      exact hzR ⟨e.1.2, hzval'.symm⟩
  · intro e
    rw [Set.disjoint_left]
    intro v hv hvbranch
    have hvmiddle : v ∈ (middle e).support :=
      walkInteriorSet_cons_concat_subset hv
    rw [SimpleGraph.Walk.support_map] at hvmiddle
    obtain ⟨z, _hz, hzval⟩ := List.mem_map.mp hvmiddle
    have hzval' : (z : V) = v := by
      simpa [inclusion] using hzval
    exact z.property (hzval' ▸ hvbranch)
  · intro e f hef
    apply Disjoint.mono
      (walkInteriorSet_cons_concat_subset (G := G))
      (walkInteriorSet_cons_concat_subset (G := G))
    rw [Set.disjoint_left]
    intro v hve hvf
    change v ∈ ((linkage.path e).map inclusion).support at hve
    change v ∈ ((linkage.path f).map inclusion).support at hvf
    rw [SimpleGraph.Walk.support_map] at hve
    rw [SimpleGraph.Walk.support_map] at hvf
    obtain ⟨ze, hze, hzeval⟩ := List.mem_map.mp hve
    obtain ⟨zf, hzf, hzfval⟩ := List.mem_map.mp hvf
    have heqz : ze = zf := by
      apply Subtype.ext
      simpa [inclusion] using hzeval.trans hzfval.symm
    subst zf
    exact (Set.disjoint_left.mp (linkage.disjoint hef)) hze hzf

lemma card_cliqueEdge (r : ℕ) :
    Fintype.card (CliqueEdge r) = Nat.choose r 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin r))

lemma card_sum_cliqueEdge (r : ℕ) :
    Fintype.card (Sum (CliqueEdge r) (CliqueEdge r)) = r * r - r := by
  rw [Fintype.card_sum, card_cliqueEdge]
  rw [Nat.choose_two_right, ← two_mul, mul_comm 2,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r), Nat.mul_sub_one]

private def terminalSource {r : ℕ} :
    Sum (CliqueEdge r) (CliqueEdge r) → Fin r
  | .inl e => e.1.1
  | .inr e => e.1.2

omit [Fintype V] [DecidableEq V] in
/-- Minimum degree at least `r^2` supplies globally distinct private
neighbors, one at each end of every prospective clique edge. -/
theorem exists_private_neighbors {G : SimpleGraph V} [G.LocallyFinite]
    {r : ℕ} (branch : Fin r ↪ V)
    (hdegree : ∀ v, r * r ≤ G.degree v) :
    ∃ neighbor : Sum (CliqueEdge r) (CliqueEdge r) ↪ V,
      (∀ z, neighbor z ∉ Set.range branch) ∧
      (∀ e, G.Adj (branch e.1.1) (neighbor (.inl e))) ∧
      (∀ e, G.Adj (neighbor (.inr e)) (branch e.1.2)) := by
  classical
  let B : Finset V := Finset.univ.map branch
  let candidate (z : Sum (CliqueEdge r) (CliqueEdge r)) : Finset V :=
    G.neighborFinset (branch (terminalSource z)) \ B
  have hBcard : B.card = r := by
    simp [B]
  have hcandidate (z : Sum (CliqueEdge r) (CliqueEdge r)) :
      r * r - r ≤ (candidate z).card := by
    rw [show candidate z = G.neighborFinset (branch (terminalSource z)) \ B by rfl,
      Finset.card_sdiff]
    have hinter : (B ∩ G.neighborFinset (branch (terminalSource z))).card ≤ r := by
      calc
        (B ∩ G.neighborFinset (branch (terminalSource z))).card ≤ B.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = r := hBcard
    have hN : r * r ≤ (G.neighborFinset (branch (terminalSource z))).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact hdegree _
    omega
  have hHall (s : Finset (Sum (CliqueEdge r) (CliqueEdge r))) :
      s.card ≤ (s.biUnion candidate).card := by
    by_cases hs : s.Nonempty
    · obtain ⟨z, hzs⟩ := hs
      calc
        s.card ≤ Fintype.card (Sum (CliqueEdge r) (CliqueEdge r)) :=
          Finset.card_le_univ s
        _ = r * r - r := card_sum_cliqueEdge r
        _ ≤ (candidate z).card := hcandidate z
        _ ≤ (s.biUnion candidate).card := by
          apply Finset.card_le_card
          intro x hx
          exact Finset.mem_biUnion.mpr ⟨z, hzs, hx⟩
    · simp only [Finset.not_nonempty_iff_eq_empty] at hs
      simp [hs]
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' candidate).mp hHall
  let neighbor : Sum (CliqueEdge r) (CliqueEdge r) ↪ V := ⟨f, hf_inj⟩
  refine ⟨neighbor, ?_, ?_, ?_⟩
  · intro z hzrange
    have hznotB : f z ∉ B := (Finset.mem_sdiff.mp (hf_mem z)).2
    apply hznotB
    obtain ⟨i, hi⟩ := hzrange
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩
  · intro e
    have hzN := (Finset.mem_sdiff.mp (hf_mem (.inl e))).1
    exact G.mem_neighborFinset (branch e.1.1) (f (.inl e)) |>.mp hzN
  · intro e
    have hzN := (Finset.mem_sdiff.mp (hf_mem (.inr e))).1
    exact (G.mem_neighborFinset (branch e.1.2) (f (.inr e)) |>.mp hzN).symm

/-- The finite assembly after the density/core lemma and Thomas--Wollan.

`hconn` is the `r^2`-connectivity conclusion of the dense-core lemma.
`hresidual_connected` and `hresidual_dense` are the standard estimates for
the graph obtained after deleting the `r` branch vertices.
`hthomas_wollan` is precisely the specialization of the Thomas--Wollan
linkedness theorem used below. -/
theorem conditional_core_assembly {G : SimpleGraph V}
    {r : ℕ} (hr : 1 ≤ r)
    (hconn : IsKConnected G (r * r))
    (hresidual_connected : ∀ branch : Fin r ↪ V,
      IsKConnected (G.induce {v | v ∉ Set.range branch})
        (2 * Fintype.card (CliqueEdge r)))
    (hresidual_dense : ∀ branch : Fin r ↪ V,
      8 * Fintype.card (CliqueEdge r) *
          Fintype.card {v : V // v ∉ Set.range branch} ≤
        (G.induce {v | v ∉ Set.range branch}).edgeSet.ncard)
    (hthomas_wollan : ∀ branch : Fin r ↪ V,
      IsKConnected (G.induce {v | v ∉ Set.range branch})
          (2 * Fintype.card (CliqueEdge r)) →
      8 * Fintype.card (CliqueEdge r) *
          Fintype.card {v : V // v ∉ Set.range branch} ≤
        (G.induce {v | v ∉ Set.range branch}).edgeSet.ncard →
      IsKLinked (G.induce {v | v ∉ Set.range branch})
        (Fintype.card (CliqueEdge r))) :
    ContainsCliqueSubdivision G r := by
  classical
  have hr_sq : r ≤ r * r := by
    simpa only [mul_one] using Nat.mul_le_mul_left r hr
  have hrcard : r ≤ Fintype.card V :=
    hr_sq.trans (Nat.le_of_lt hconn.1)
  have hcardfin : Fintype.card (Fin r) ≤ Fintype.card V := by
    simpa using hrcard
  obtain ⟨branch : Fin r ↪ V⟩ :=
    Function.Embedding.nonempty_of_card_le (α := Fin r) (β := V) hcardfin
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  let : G.LocallyFinite := fun _ => inferInstance
  have hdegree : ∀ v, r * r ≤ G.degree v :=
    hconn.degree_ge
  obtain ⟨neighbor, hprivate, hadj_left, hadj_right⟩ :=
    exists_private_neighbors branch hdegree
  have hlinked : IsKLinked (G.induce {v | v ∉ Set.range branch})
      (Fintype.card (CliqueEdge r)) :=
    hthomas_wollan branch (hresidual_connected branch) (hresidual_dense branch)
  exact subdivision_of_linked_private_neighbors branch neighbor hprivate
    hadj_left hadj_right hlinked

/-! ### Mader's dense highly connected induced subgraph lemma -/


open scoped Sym2
open Finset

namespace MaderPrototype

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card

def degreeOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  ((G.edgeFinset.filter fun e => e.toFinset ⊆ S).filter fun e => v ∈ e.toFinset).card

lemma edgesOn_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgesOn G univ = #G.edgeFinset := by
  unfold edgesOn
  simp

lemma edgesOn_eq_induce (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgesOn G S = #(G.induce (S : Set V)).edgeFinset := by
  unfold edgesOn
  exact G.card_filter_edgeFinset_toFinset_subset S

lemma edgesOn_le_square (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgesOn G S ≤ #S ^ 2 := by
  rw [edgesOn_eq_induce]
  calc
    #(G.induce (S : Set V)).edgeFinset ≤ (Fintype.card (S : Set V)).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    _ = (#S).choose 2 := by simp
    _ ≤ #S ^ 2 := Nat.choose_le_pow _ _

lemma edgesOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : S ⊆ T) :
    edgesOn G S ≤ edgesOn G T := by
  unfold edgesOn
  apply Finset.card_le_card
  intro e he
  simp only [mem_filter] at he ⊢
  exact ⟨he.1, he.2.trans hST⟩

lemma edgesOn_erase_add_degreeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (_hv : v ∈ S) :
    edgesOn G (S.erase v) + degreeOn G S v = edgesOn G S := by
  unfold edgesOn degreeOn
  let F := G.edgeFinset.filter fun e => e.toFinset ⊆ S
  calc
    #({e ∈ G.edgeFinset | e.toFinset ⊆ S.erase v}) +
          #({e ∈ F | v ∈ e.toFinset}) =
        #({e ∈ F | v ∉ e.toFinset}) + #({e ∈ F | ¬v ∉ e.toFinset}) := by
      congr 1
      · apply congrArg card
        ext e
        simp only [F, mem_filter]
        constructor
        · rintro ⟨heG, heSub⟩
          refine ⟨⟨heG, ?_⟩, ?_⟩
          · intro x hx
            exact (mem_erase.mp (heSub hx)).2
          · intro hve
            exact (mem_erase.mp (heSub hve)).1 rfl
        · rintro ⟨⟨heG, heSub⟩, hev⟩
          refine ⟨heG, ?_⟩
          intro x hx
          exact mem_erase.mpr ⟨fun hxv => hev (hxv ▸ hx), heSub hx⟩
      · apply congrArg card
        ext e
        simp only [mem_filter, not_not]
    _ = #F := card_filter_add_card_filter_not (s := F) (p := fun e => v ∉ e.toFinset)

lemma existsUnique_other_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} {v : V} (he : e ∈ G.edgeFinset) (hv : v ∈ e.toFinset) :
    ∃! w : V, e = s(v, w) := by
  rw [Sym2.mem_toFinset] at hv
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv
  refine ⟨w, rfl, ?_⟩
  intro y hy
  have hadj : G.Adj v w := by simpa using (mem_edgeFinset.mp he)
  rw [Sym2.eq_iff] at hy
  rcases hy with h | h
  · exact h.2.symm
  · exact (hadj.ne h.2.symm).elim

lemma degreeOn_lt_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) : degreeOn G S v < #S := by
  let I := (G.edgeFinset.filter fun e => e.toFinset ⊆ S).filter fun e => v ∈ e.toFinset
  have hother (e : I) : ∃! w : V, (e : Sym2 V) = s(v, w) := by
    apply existsUnique_other_endpoint G
    · exact (mem_filter.mp (mem_filter.mp e.property).1).1
    · exact (mem_filter.mp e.property).2
  let f : I → (S.erase v : Finset V) := fun e => by
    let w := Classical.choose (hother e)
    have heq : (e : Sym2 V) = s(v, w) := (Classical.choose_spec (hother e)).1
    have hsub := (mem_filter.mp (mem_filter.mp e.property).1).2
    have heG := (mem_filter.mp (mem_filter.mp e.property).1).1
    have hadj : G.Adj v w := by
      rw [heq] at heG
      simpa using (mem_edgeFinset.mp heG)
    refine ⟨w, mem_erase.mpr ⟨hadj.ne.symm, ?_⟩⟩
    exact hsub (by rw [heq]; simp)
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hval : (f e₁ : V) = f e₂ := congrArg Subtype.val h
    have heq₁ := (Classical.choose_spec (hother e₁)).1
    have heq₂ := (Classical.choose_spec (hother e₂)).1
    exact heq₁.trans ((congrArg (fun w => s(v, w)) hval).trans heq₂.symm)
  have hc : #I ≤ #(S.erase v) := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  rw [card_erase_of_mem hv] at hc
  unfold degreeOn
  change #I < #S
  have hS : 0 < #S := card_pos.mpr ⟨v, hv⟩
  omega

def NoCross (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬G.Adj x y

omit [Fintype V] in
lemma NoCross.symm {G : SimpleGraph V} {A B : Finset V} (h : NoCross G A B) :
    NoCross G B A := by
  intro x hx y hy hxy
  exact h y hy x hx hxy.symm

lemma degreeOn_union_eq_left (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {x : V} (hx : x ∈ A \ B) (hcross : NoCross G A B) :
    degreeOn G (A ∪ B) x = degreeOn G A x := by
  unfold degreeOn
  apply congrArg card
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨heG, heSub⟩, hxe⟩
    refine ⟨⟨heG, ?_⟩, hxe⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using (mem_edgeFinset.mp heG)
      have hvu : G.Adj v u := huv.symm
      simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff, Finset.mem_union] at heSub ⊢
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
        Finset.mem_singleton] at hxe
      simp only [NoCross, Finset.mem_sdiff] at hcross
      simp only [Finset.mem_sdiff] at hx
      rcases hxe with rfl | rfl
      · refine ⟨hx.1, ?_⟩
        rcases heSub.2 with hvA | hvB
        · exact hvA
        · by_contra hvA
          exact hcross _ hx _ ⟨hvB, hvA⟩ huv
      · refine ⟨?_, hx.1⟩
        rcases heSub.1 with huA | huB
        · exact huA
        · by_contra huA
          exact hcross _ hx _ ⟨huB, huA⟩ hvu
  · rintro ⟨⟨heG, heSub⟩, hxe⟩
    exact ⟨⟨heG, heSub.trans Finset.subset_union_left⟩, hxe⟩

lemma degreeOn_union_eq_right (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {x : V} (hx : x ∈ B \ A) (hcross : NoCross G A B) :
    degreeOn G (A ∪ B) x = degreeOn G B x := by
  rw [Finset.union_comm]
  exact degreeOn_union_eq_left G hx hcross.symm

lemma edgesOn_union_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hcross : NoCross G A B) :
    edgesOn G (A ∪ B) ≤ edgesOn G A + edgesOn G B := by
  unfold edgesOn
  let EA := G.edgeFinset.filter fun e => e.toFinset ⊆ A
  let EB := G.edgeFinset.filter fun e => e.toFinset ⊆ B
  calc
    #({e ∈ G.edgeFinset | e.toFinset ⊆ A ∪ B}) ≤ #(EA ∪ EB) := by
      apply Finset.card_le_card
      intro e he
      have heG : e ∈ G.edgeFinset := (mem_filter.mp he).1
      have heAB : e.toFinset ⊆ A ∪ B := (mem_filter.mp he).2
      by_cases heA : e.toFinset ⊆ A
      · exact mem_union_left EB (mem_filter.mpr ⟨heG, heA⟩)
      by_cases heB : e.toFinset ⊆ B
      · exact mem_union_right EA (mem_filter.mpr ⟨heG, heB⟩)
      exfalso
      induction e using Sym2.inductionOn with
      | hf x y =>
        have hxy : G.Adj x y := by simpa using (mem_edgeFinset.mp heG)
        simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff, Finset.mem_union] at heAB heA heB
        simp only [NoCross, Finset.mem_sdiff] at hcross
        have hyx : G.Adj y x := hxy.symm
        rcases heAB with ⟨huA | huB, hvA | hvB⟩
        · exact heA ⟨huA, hvA⟩
        · have huNotB : x ∉ B := by
            intro hxB
            exact heB ⟨hxB, hvB⟩
          have hvNotA : y ∉ A := by
            intro hyA
            exact heA ⟨huA, hyA⟩
          exact hcross x ⟨huA, huNotB⟩ y ⟨hvB, hvNotA⟩ hxy
        · have huNotA : x ∉ A := by
            intro hxA
            exact heA ⟨hxA, hvA⟩
          have hvNotB : y ∉ B := by
            intro hyB
            exact heB ⟨huB, hyB⟩
          exact hcross y ⟨hvA, hvNotB⟩ x ⟨huB, huNotA⟩ hyx
        · exact heB ⟨huB, hvB⟩
    _ ≤ #EA + #EB := card_union_le EA EB

lemma edgesOn_of_eq_union_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {S A B : Finset V} (hS : A ∪ B = S) (hcross : NoCross G A B) :
    edgesOn G S ≤ edgesOn G A + edgesOn G B := by
  rw [← hS]
  exact edgesOn_union_le G hcross

def Good (G : SimpleGraph V) [DecidableRel G.Adj]
    (q N E : ℕ) (S : Finset V) : Prop :=
  2 * q ≤ #S ∧ E * (#S - q) < N * edgesOn G S

def MoreThanQConnectedOn (G : SimpleGraph V) (q : ℕ) (S : Finset V) : Prop :=
  q < #S ∧ ∀ A B : Finset V, A ∪ B = S → (A \ B).Nonempty → (B \ A).Nonempty →
    NoCross G A B → q < #(A ∩ B)

theorem exists_dense_highlyConnectedOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hV : 0 < Fintype.card V)
    (hE : 5 * q * Fintype.card V ≤ #G.edgeFinset) :
    ∃ S : Finset V,
      4 * q * #S < edgesOn G S ∧ MoreThanQConnectedOn G q S := by
  let N := Fintype.card V
  let E := #G.edgeFinset
  have hEmax : E ≤ N ^ 2 := by
    calc
      E ≤ N.choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ ≤ N ^ 2 := Nat.choose_le_pow _ _
  have h5prod : 5 * q * N ≤ N * N := by
    simpa [E, N, pow_two] using hE.trans hEmax
  have h5qN : 5 * q ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := N)
    · simpa [mul_assoc, mul_comm, mul_left_comm] using h5prod
    · exact hV
  have h2qN : 2 * q ≤ N := by omega
  have hEpos : 0 < E := by
    have : 0 < 5 * q * N := by positivity
    exact this.trans_le hE
  have hunivGood : Good G q N E (univ : Finset V) := by
    constructor
    · simpa [N] using h2qN
    · rw [card_univ, edgesOn_univ]
      have hsub : N - q < N := Nat.sub_lt hV hq
      calc
        E * (N - q) < E * N := Nat.mul_lt_mul_of_pos_left hsub hEpos
        _ = N * E := mul_comm _ _
  let _ : DecidablePred (Good G q N E) := Classical.decPred _
  let candidates := (univ : Finset (Finset V)).filter (Good G q N E)
  have hcandidates : candidates.Nonempty := by
    refine ⟨univ, ?_⟩
    simpa [candidates] using (mem_filter.mpr ⟨mem_univ (univ : Finset V), hunivGood⟩)
  obtain ⟨S, hScand, hmin⟩ := candidates.exists_min_image card hcandidates
  have hSGood : Good G q N E S := by
    have : S ∈ (univ : Finset (Finset V)).filter (Good G q N E) := by
      simpa [candidates] using hScand
    exact (mem_filter.mp this).2
  have hS2 : 2 * q ≤ #S := hSGood.1
  have hSpot : E * (#S - q) < N * edgesOn G S := hSGood.2
  have hS2strict : 2 * q < #S := by
    by_contra hn
    have hSeq : #S = 2 * q := by omega
    have hp : N * (5 * q * q) < N * edgesOn G S := by
      calc
        N * (5 * q * q) = (5 * q * N) * q := by ring
        _ ≤ E * q := Nat.mul_le_mul_right q hE
        _ = E * (#S - q) := by
          rw [hSeq]
          congr 1
          omega
        _ < N * edgesOn G S := hSpot
    have hdense : 5 * q * q < edgesOn G S := Nat.lt_of_mul_lt_mul_left hp
    have hsquare := edgesOn_le_square G S
    rw [hSeq] at hsquare
    nlinarith
  have hdegScaled : ∀ v ∈ S, E < N * degreeOn G S v := by
    intro v hv
    by_contra hn
    have hle : N * degreeOn G S v ≤ E := by omega
    have herase2 : 2 * q ≤ #(S.erase v) := by
      rw [card_erase_of_mem hv]
      omega
    have herasePot : E * (#(S.erase v) - q) < N * edgesOn G (S.erase v) := by
      have hcount := edgesOn_erase_add_degreeOn G S hv
      have hsplit : #S - q = (#(S.erase v) - q) + 1 := by
        rw [card_erase_of_mem hv]
        omega
      rw [hsplit, mul_add, mul_one] at hSpot
      rw [← hcount, mul_add] at hSpot
      omega
    have heraseGood : Good G q N E (S.erase v) := ⟨herase2, herasePot⟩
    have heraseCand : S.erase v ∈ candidates :=
      mem_filter.mpr ⟨mem_univ _, heraseGood⟩
    have hminErase := hmin (S.erase v) heraseCand
    rw [card_erase_of_mem hv] at hminErase
    omega
  have hdeg5 : ∀ v ∈ S, 5 * q < degreeOn G S v := by
    intro v hv
    have hp : N * (5 * q) < N * degreeOn G S v := by
      calc
        N * (5 * q) = 5 * q * N := by ring
        _ ≤ E := hE
        _ < N * degreeOn G S v := hdegScaled v hv
    exact Nat.lt_of_mul_lt_mul_left hp
  have hS5 : 5 * q < #S := by
    obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < #S)
    exact (hdeg5 v hv).trans (degreeOn_lt_card G S hv)
  have hcoef : 4 * q * #S ≤ 5 * q * (#S - q) := by
    have hqS : q ≤ #S := by omega
    have hdecomp := Nat.sub_add_cancel hqS
    nlinarith
  have hdenseS : 4 * q * #S < edgesOn G S := by
    have hp : N * (4 * q * #S) < N * edgesOn G S := by
      calc
        N * (4 * q * #S) ≤ N * (5 * q * (#S - q)) := Nat.mul_le_mul_left N hcoef
        _ = (5 * q * N) * (#S - q) := by ring
        _ ≤ E * (#S - q) := Nat.mul_le_mul_right (#S - q) hE
        _ < N * edgesOn G S := hSpot
    exact Nat.lt_of_mul_lt_mul_left hp
  refine ⟨S, hdenseS, ?_⟩
  refine ⟨by omega, ?_⟩
  intro A B hAB hAne hBne hcross
  by_contra hn
  have hinter : #(A ∩ B) ≤ q := by omega
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have hAS : A ⊆ S := by rw [← hAB]; exact subset_union_left
  have hBS : B ⊆ S := by rw [← hAB]; exact subset_union_right
  have haS : a ∈ S := hAS (mem_sdiff.mp ha).1
  have hbS : b ∈ S := hBS (mem_sdiff.mp hb).1
  have hA5 : 5 * q < #A := by
    have heq : degreeOn G S a = degreeOn G A a := by
      rw [← hAB]
      exact degreeOn_union_eq_left G ha hcross
    have hh := hdeg5 a haS
    rw [heq] at hh
    exact hh.trans (degreeOn_lt_card G A (mem_sdiff.mp ha).1)
  have hB5 : 5 * q < #B := by
    have heq : degreeOn G S b = degreeOn G B b := by
      rw [← hAB]
      exact degreeOn_union_eq_right G hb hcross
    have hh := hdeg5 b hbS
    rw [heq] at hh
    exact hh.trans (degreeOn_lt_card G B (mem_sdiff.mp hb).1)
  have hA2 : 2 * q ≤ #A := by omega
  have hB2 : 2 * q ≤ #B := by omega
  have hAlt : #A < #S := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hAS, ?_⟩
    intro hEq
    have : b ∈ A := hEq.symm ▸ hbS
    exact (mem_sdiff.mp hb).2 this
  have hBlt : #B < #S := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hBS, ?_⟩
    intro hEq
    have : a ∈ B := hEq.symm ▸ haS
    exact (mem_sdiff.mp ha).2 this
  have hAnot : ¬Good G q N E A := by
    intro hAgood
    have hAcand : A ∈ candidates := mem_filter.mpr ⟨mem_univ _, hAgood⟩
    exact (not_le_of_gt hAlt) (hmin A hAcand)
  have hBnot : ¬Good G q N E B := by
    intro hBgood
    have hBcand : B ∈ candidates := mem_filter.mpr ⟨mem_univ _, hBgood⟩
    exact (not_le_of_gt hBlt) (hmin B hBcand)
  have hApot : N * edgesOn G A ≤ E * (#A - q) := by
    simp only [Good, hA2, true_and, not_lt] at hAnot
    exact hAnot
  have hBpot : N * edgesOn G B ≤ E * (#B - q) := by
    simp only [Good, hB2, true_and, not_lt] at hBnot
    exact hBnot
  have hedge := edgesOn_of_eq_union_le G hAB hcross
  have hcards := card_union_add_card_inter A B
  rw [hAB] at hcards
  have hsubs : (#A - q) + (#B - q) ≤ #S - q := by omega
  have hcontra : N * edgesOn G S ≤ E * (#S - q) := by
    calc
      N * edgesOn G S ≤ N * (edgesOn G A + edgesOn G B) := Nat.mul_le_mul_left N hedge
      _ = N * edgesOn G A + N * edgesOn G B := by rw [mul_add]
      _ ≤ E * (#A - q) + E * (#B - q) := Nat.add_le_add hApot hBpot
      _ = E * ((#A - q) + (#B - q)) := by rw [mul_add]
      _ ≤ E * (#S - q) := Nat.mul_le_mul_left E hsubs
  omega

theorem exists_induced_dense_highlyConnectedOn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hV : 0 < Fintype.card V)
    (hE : 5 * q * Fintype.card V ≤ #G.edgeFinset) :
    ∃ S : Finset V,
      4 * q * #S < #(G.induce (S : Set V)).edgeFinset ∧
        MoreThanQConnectedOn G q S := by
  obtain ⟨S, hS, hconn⟩ := exists_dense_highlyConnectedOn G q hq hV hE
  refine ⟨S, ?_, hconn⟩
  rwa [← edgesOn_eq_induce]

end MaderPrototype


namespace MaderPrototype

lemma MoreThanQConnectedOn.isKConnected_induce
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (q : ℕ) (S : Finset V)
    (h : MoreThanQConnectedOn G q S) :
    Erdos718.IsKConnected (G.induce (S : Set V)) q := by
  let emb : (S : Set V) ↪ V := Function.Embedding.subtype _
  constructor
  · simpa using h.1
  · intro s hs
    let A : Finset V := s.left.map emb
    let B : Finset V := s.right.map emb
    have hAB : A ∪ B = S := by
      ext x
      constructor
      · intro hx
        rcases mem_union.mp hx with hx | hx
        · obtain ⟨u, _, rfl⟩ := mem_map.mp hx
          exact u.property
        · obtain ⟨u, _, rfl⟩ := mem_map.mp hx
          exact u.property
      · intro hx
        let u : (S : Set V) := ⟨x, hx⟩
        have hu : u ∈ s.left ∪ s.right := by rw [s.cover]; exact mem_univ _
        rcases mem_union.mp hu with hu | hu
        · exact mem_union_left B (mem_map.mpr ⟨u, hu, rfl⟩)
        · exact mem_union_right A (mem_map.mpr ⟨u, hu, rfl⟩)
    have hcross : NoCross G A B := by
      intro x hx y hy hxy
      rcases mem_sdiff.mp hx with ⟨hxA, hxB⟩
      rcases mem_sdiff.mp hy with ⟨hyB, hyA⟩
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hxA
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hyB
      have hunr : u ∉ s.right := by
        intro hur
        exact hxB (mem_map.mpr ⟨u, hur, rfl⟩)
      have hvnl : v ∉ s.left := by
        intro hvl
        exact hyA (mem_map.mpr ⟨v, hvl, rfl⟩)
      have hnot := s.not_adj hu hunr hv hvnl
      change G.Adj (u : V) (v : V) at hxy
      exact hnot hxy
    have hAne : (A \ B).Nonempty := by
      obtain ⟨u, hu⟩ := hs.1
      refine ⟨u, mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · exact mem_map.mpr ⟨u, (mem_sdiff.mp hu).1, rfl⟩
      · intro hh
        obtain ⟨v, hv, huv⟩ := mem_map.mp hh
        have : v = u := emb.injective huv
        subst v
        exact (mem_sdiff.mp hu).2 hv
    have hBne : (B \ A).Nonempty := by
      obtain ⟨u, hu⟩ := hs.2
      refine ⟨u, mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · exact mem_map.mpr ⟨u, (mem_sdiff.mp hu).1, rfl⟩
      · intro hh
        obtain ⟨v, hv, huv⟩ := mem_map.mp hh
        have : v = u := emb.injective huv
        subst v
        exact (mem_sdiff.mp hu).2 hv
    have hlarge := h.2 A B hAB hAne hBne hcross
    have hinter : (s.left ∩ s.right).map emb = A ∩ B := by
      simpa [A, B] using Finset.map_inter (f := emb) s.left s.right
    have hcard : #(A ∩ B) = #(s.left ∩ s.right) := by
      rw [← hinter, card_map]
    rw [hcard] at hlarge
    change q ≤ #(s.left ∩ s.right)
    omega

theorem exists_induced_dense_isKConnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 0 < q) (hV : 0 < Fintype.card V)
    (hE : 5 * q * Fintype.card V ≤ #G.edgeFinset) :
    ∃ S : Finset V,
      4 * q * #S < #(G.induce (S : Set V)).edgeFinset ∧
        Erdos718.IsKConnected (G.induce (S : Set V)) q := by
  obtain ⟨S, hdense, hconn⟩ :=
    exists_induced_dense_highlyConnectedOn G q hq hV hE
  exact ⟨S, hdense, hconn.isKConnected_induce G q S⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma isKConnected_induce_congr_pred (G : SimpleGraph V) (k : ℕ)
    (p q : V → Prop) [dp : DecidablePred p] [dq : DecidablePred q]
    (hpq : ∀ v, p v ↔ q v) :
    IsKConnected (G.induce {v | p v}) k ↔
      IsKConnected (G.induce {v | q v}) k := by
  have hpq' : p = q := funext fun v => propext (hpq v)
  subst q
  have hd : dq = dp := Subsingleton.elim _ _
  subst dq
  rfl

omit [Fintype V] [DecidableEq V] in
lemma ncard_edgeSet_induce_congr (G : SimpleGraph V) {A B : Set V}
    (hAB : A = B) :
    (G.induce A).edgeSet.ncard = (G.induce B).edgeSet.ncard := by
  subst B
  rfl

omit [DecidableEq V] in
lemma card_edgeFinset_eq_ncard_edgeSet (G : SimpleGraph V)
    [DecidableRel G.Adj] : #G.edgeFinset = G.edgeSet.ncard := by
  classical
  simpa only [SimpleGraph.edgeFinset] using
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm

/-- Deleting a finite vertex set loses at most `|B| |S|` edges from the
graph induced on `S`. -/
lemma edgesOn_le_edgesOn_sdiff_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (S B : Finset V) :
    edgesOn G S ≤ edgesOn G (S \ B) + #B * #S := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert v B hvB ih =>
      by_cases hvS : v ∈ S
      · have hvSB : v ∈ S \ B := Finset.mem_sdiff.mpr ⟨hvS, hvB⟩
        have hcount := edgesOn_erase_add_degreeOn G (S \ B) hvSB
        have hdeg : degreeOn G (S \ B) v ≤ #S := by
          have hlt := degreeOn_lt_card G (S \ B) hvSB
          have hsub : #(S \ B) ≤ #S := Finset.card_le_card Finset.sdiff_subset
          omega
        have hset : S \ insert v B = (S \ B).erase v := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        rw [Finset.card_insert_of_notMem hvB, hset]
        calc
          edgesOn G S ≤ edgesOn G (S \ B) + #B * #S := ih
          _ = edgesOn G ((S \ B).erase v) + degreeOn G (S \ B) v +
                #B * #S := by rw [hcount]
          _ ≤ edgesOn G ((S \ B).erase v) + #S + #B * #S := by omega
          _ = edgesOn G ((S \ B).erase v) + (#B + 1) * #S := by ring
      · have hset : S \ insert v B = S \ B := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hxS, hx⟩
            exact ⟨hxS, fun hxB => hx (Or.inr hxB)⟩
          · rintro ⟨hxS, hxB⟩
            refine ⟨hxS, ?_⟩
            rintro (rfl | hxB')
            · exact hvS hxS
            · exact hxB hxB'
        rw [Finset.card_insert_of_notMem hvB, hset]
        rw [Nat.add_mul, one_mul]
        omega

omit [DecidableEq V] in
lemma edgeFinset_le_delete_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) :
    #G.edgeFinset ≤ (G.induce {v : V | v ∉ B}).edgeSet.ncard +
      #B * Fintype.card V := by
  classical
  have h := edgesOn_le_edgesOn_sdiff_add G (Finset.univ : Finset V) B
  rw [edgesOn_univ, edgesOn_eq_induce] at h
  have hset : ((Finset.univ \ B : Finset V) : Set V) = {v : V | v ∉ B} := by
    ext v
    simp
  calc
    #G.edgeFinset ≤
        #(G.induce ((Finset.univ \ B : Finset V) : Set V)).edgeFinset +
          #B * Fintype.card V := by simpa using h
    _ = (G.induce ((Finset.univ \ B : Finset V) : Set V)).edgeSet.ncard +
          #B * Fintype.card V := by
      rw [card_edgeFinset_eq_ncard_edgeSet]
    _ = (G.induce {v : V | v ∉ B}).edgeSet.ncard +
          #B * Fintype.card V := by
      rw [ncard_edgeSet_induce_congr G hset]

/-- Mader's dense core remains sufficiently connected and dense after the
`r` prospective branch vertices are deleted. -/
theorem exists_induced_dense_core_with_robust_residual
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 2 ≤ r) (hV : 0 < Fintype.card V)
    (hE : 5 * (r * r) * Fintype.card V ≤ #G.edgeFinset) :
    ∃ S : Finset V,
      IsKConnected (G.induce (S : Set V)) (r * r) ∧
      ∀ branch : Fin r ↪ (S : Set V),
        IsKConnected
            ((G.induce (S : Set V)).induce
              {v | v ∉ Set.range branch})
            (2 * Fintype.card (CliqueEdge r)) ∧
        8 * Fintype.card (CliqueEdge r) *
              Fintype.card {v : (S : Set V) // v ∉ Set.range branch} ≤
            ((G.induce (S : Set V)).induce
              {v | v ∉ Set.range branch}).edgeSet.ncard := by
  classical
  obtain ⟨S, hdense, hconn⟩ :=
    exists_induced_dense_isKConnected G (r * r) (by positivity) hV hE
  refine ⟨S, hconn, ?_⟩
  intro branch
  let H : SimpleGraph (S : Set V) := G.induce (S : Set V)
  let B : Finset (S : Set V) :=
    Finset.univ.filter fun v => v ∈ Set.range branch
  have hBeq : B = Finset.univ.map branch := by
    ext v
    simp [B]
  have hBcard : #B = r := by
    rw [hBeq, Finset.card_map, Finset.card_univ]
    simp
  have hBmem (v : (S : Set V)) : v ∈ B ↔ v ∈ Set.range branch := by
    simp [B]
  have hBpred (v : (S : Set V)) : (v ∉ B) ↔ v ∉ Set.range branch :=
    not_congr (hBmem v)
  have hBlt : #B < r * r := by
    rw [hBcard]
    calc
      r = r * 1 := by omega
      _ < r * r := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hconnected0 := hconn.induce_delete B hBlt
  have htwo : 2 * Fintype.card (CliqueEdge r) = r * r - r := by
    rw [Nat.two_mul, ← Fintype.card_sum, card_sum_cliqueEdge]
  have hconnected :
      IsKConnected (H.induce {v | v ∉ Set.range branch})
        (2 * Fintype.card (CliqueEdge r)) := by
    have hc : IsKConnected (H.induce {v | v ∉ B})
        (2 * Fintype.card (CliqueEdge r)) := by
      simpa only [H, hBcard, htwo] using hconnected0
    exact (isKConnected_induce_congr_pred H _
      (fun v => v ∉ B) (fun v => v ∉ Set.range branch) hBpred).mp hc
  refine ⟨hconnected, ?_⟩
  have hloss := edgeFinset_le_delete_add H B
  have hncard :
      (H.induce {v | v ∉ B}).edgeSet.ncard =
        (H.induce {v | v ∉ Set.range branch}).edgeSet.ncard := by
    apply ncard_edgeSet_induce_congr H
    ext v
    exact hBpred v
  have hloss' :
      #H.edgeFinset ≤
        (H.induce {v | v ∉ Set.range branch}).edgeSet.ncard +
          r * Fintype.card (S : Set V) := by
    calc
      #H.edgeFinset ≤ (H.induce {v | v ∉ B}).edgeSet.ncard +
          #B * Fintype.card (S : Set V) := hloss
      _ = (H.induce {v | v ∉ Set.range branch}).edgeSet.ncard +
          r * Fintype.card (S : Set V) := by
        rw [hncard, hBcard]
  have hScard : #S = Fintype.card (S : Set V) := by simp
  have hdense' :
      4 * (r * r) * Fintype.card (S : Set V) < #H.edgeFinset := by
    simpa only [H, hScard] using hdense
  have hrescard :
      Fintype.card {v : (S : Set V) // v ∉ Set.range branch} =
        Fintype.card (S : Set V) - r := by
    rw [show Fintype.card {v : (S : Set V) // v ∉ Set.range branch} =
        Fintype.card (S : Set V) - #B by
      simpa only [hBmem] using card_deleteVertices B]
    rw [hBcard]
  rw [hrescard]
  rw [card_cliqueEdge]
  have hchoose : 2 * r.choose 2 = r * r - r := by
    simpa only [card_cliqueEdge] using htwo
  have hrq : r ≤ r * r := by
    calc
      r = r * 1 := by omega
      _ ≤ r * r := Nat.mul_le_mul_left r (by omega)
  have hchoose' : 2 * r.choose 2 + r = r * r := by omega
  have harith :
      8 * r.choose 2 * (Fintype.card (S : Set V) - r) +
          r * Fintype.card (S : Set V) ≤
        4 * (r * r) * Fintype.card (S : Set V) := by
    calc
      8 * r.choose 2 * (Fintype.card (S : Set V) - r) +
            r * Fintype.card (S : Set V) ≤
          8 * r.choose 2 * Fintype.card (S : Set V) +
            r * Fintype.card (S : Set V) := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left (8 * r.choose 2) (Nat.sub_le _ _)) _
      _ ≤ 8 * r.choose 2 * Fintype.card (S : Set V) +
            4 * r * Fintype.card (S : Set V) := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right (Fintype.card (S : Set V))
            (Nat.le_mul_of_pos_left r (by omega))) _
      _ = 4 * (r * r) * Fintype.card (S : Set V) := by
        rw [← hchoose']
        ring
  have htotal :
      4 * (r * r) * Fintype.card (S : Set V) ≤ #H.edgeFinset :=
    Nat.le_of_lt hdense'
  have hsum :
      8 * r.choose 2 * (Fintype.card (S : Set V) - r) +
          r * Fintype.card (S : Set V) ≤
        (H.induce {v | v ∉ Set.range branch}).edgeSet.ncard +
          r * Fintype.card (S : Set V) :=
    harith.trans (htotal.trans hloss')
  exact Nat.le_of_add_le_add_right hsum

end MaderPrototype

end Erdos718

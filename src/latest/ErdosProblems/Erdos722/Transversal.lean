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
import Mathlib.LinearAlgebra.Lagrange
import Mathlib

/-!
# Transversal polynomial decompositions

The algebraic exchange gadget in the short proof of design existence starts
from two decompositions of a finite-field blow-up.  This file proves its
basic interpolation component: graphs of degree-`< r` polynomial functions
partition the transversal `r`-sets.
-/

namespace Erdos722.Transversal

open Finset Polynomial

noncomputable section

variable {I F : Type*} [Fintype I] [DecidableEq I]
  [Field F] [Fintype F] [DecidableEq F]

/-- Graph of a function on a finite index type. -/
def graph (f : I → F) : Finset (I × F) :=
  Finset.univ.image fun i ↦ (i, f i)

omit [Field F] [Fintype F] in
@[simp] theorem mem_graph {f : I → F} {i : I} {x : F} :
    (i, x) ∈ graph f ↔ x = f i := by
  simp [graph, eq_comm]

omit [Field F] [Fintype F] in
@[simp] theorem card_graph (f : I → F) :
    (graph f).card = Fintype.card I := by
  calc
    (graph f).card = (Finset.univ : Finset I).card :=
      Finset.card_image_iff.mpr (by
        intro i _ j _ h
        exact congrArg Prod.fst h)
    _ = Fintype.card I := Finset.card_univ

/-- An `r`-set using each index part at most once. -/
def transversalHost (r : ℕ) : Finset (Finset (I × F)) :=
  ((Finset.univ : Finset (I × F)).powersetCard r).filter fun A ↦
    (A.image Prod.fst).card = r

omit [Field F] [DecidableEq F] in
@[simp] theorem mem_transversalHost {r : ℕ} {A : Finset (I × F)} :
    A ∈ transversalHost (I := I) (F := F) r ↔
      A.card = r ∧ Set.InjOn (fun z : I × F ↦ z.1) (↑A : Set (I × F)) := by
  rw [transversalHost, Finset.mem_filter, Finset.mem_powersetCard]
  simp only [Finset.subset_univ, true_and]
  constructor
  · rintro ⟨hcard, himage⟩
    exact ⟨hcard, Finset.card_image_iff.mp (himage.trans hcard.symm)⟩
  · rintro ⟨hcard, hinj⟩
    exact ⟨hcard, (Finset.card_image_iff.mpr hinj).trans hcard⟩

omit [Field F] [DecidableEq F] in
/-- Coarse finite bound for the base blowup host.  The exact count is
`choose (card I) r * (card F)^r`; this bound is sufficient for all later
finite-size estimates and does not require choosing an ordering of a
transversal set. -/
theorem card_transversalHost_le_pow (r : ℕ) :
    (transversalHost (I := I) (F := F) r).card ≤
      (Fintype.card I * Fintype.card F) ^ r := by
  calc
    (transversalHost (I := I) (F := F) r).card ≤
        ((Finset.univ : Finset (I × F)).powersetCard r).card :=
      Finset.card_filter_le _ _
    _ = Nat.choose (Fintype.card I * Fintype.card F) r := by simp
    _ ≤ (Fintype.card I * Fintype.card F) ^ r := Nat.choose_le_pow _ _

/-- Functions obtained by evaluating the coefficient vectors `Fin r → F`
on the fixed nodes `y`. -/
def polynomialFunctions (y : I → F) (r : ℕ) : Finset (I → F) :=
  (Finset.univ : Finset (Fin r → F)).image fun u i ↦
    (Polynomial.ofFn r u).eval (y i)

/-- The corresponding graph blocks. -/
def polynomialBlocks (y : I → F) (r : ℕ) : Finset (Finset (I × F)) :=
  (polynomialFunctions y r).image graph

/-- The value paired with `i` by a transversal set, or zero if the part is
unused. -/
def valueAt (A : Finset (I × F)) (i : I) : F :=
  if h : ∃ x, (i, x) ∈ A then Classical.choose h else 0

omit [Fintype I] in
theorem valueAt_eq_of_mem {A : Finset (I × F)}
    (hinj : Set.InjOn (fun z : I × F ↦ z.1) (↑A : Set (I × F)))
    {i : I} {x : F} (hx : (i, x) ∈ A) :
    valueAt A i = x := by
  let h : ∃ x : F, (i, x) ∈ A := ⟨x, hx⟩
  rw [valueAt, dif_pos h]
  have hc : (i, Classical.choose h) ∈ A := Classical.choose_spec h
  have hp : (i, Classical.choose h) = (i, x) :=
    hinj hc hx rfl
  exact congrArg Prod.snd hp

/-- The interpolation function through a transversal `r`-set. -/
def interpolatingFunction (y : I → F) (A : Finset (I × F)) : I → F :=
  fun i ↦ (Lagrange.interpolate (A.image Prod.fst) y (valueAt A)).eval (y i)

theorem interpolatingFunction_mem
    {y : I → F} (hy : Function.Injective y)
    {r : ℕ} {A : Finset (I × F)} (hA : A ∈ transversalHost (I := I) (F := F) r) :
    interpolatingFunction y A ∈ polynomialFunctions y r := by
  classical
  let P : F[X] := Lagrange.interpolate (A.image Prod.fst) y (valueAt A)
  have hScard : (A.image Prod.fst).card = r := by
    rw [Finset.card_image_iff.mpr (mem_transversalHost.mp hA).2,
      (mem_transversalHost.mp hA).1]
  have hdeg : P.degree < r := by
    have h := Lagrange.degree_interpolate_lt (valueAt A)
      (hy.injOn : Set.InjOn y (A.image Prod.fst))
    rw [hScard] at h
    exact h
  let u : Fin r → F := Polynomial.toFn r P
  have hPu : Polynomial.ofFn r u = P := by
    by_cases hP : P = 0
    · calc
        Polynomial.ofFn r u = Polynomial.ofFn r (Polynomial.toFn r P) := rfl
        _ = Polynomial.ofFn r (Polynomial.toFn r 0) := by rw [hP]
        _ = 0 := by simp
        _ = P := hP.symm
    · exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        ((Polynomial.natDegree_lt_iff_degree_lt hP).mpr hdeg)
  rw [polynomialFunctions]
  apply Finset.mem_image.mpr
  refine ⟨u, Finset.mem_univ _, ?_⟩
  funext i
  simp only [interpolatingFunction, P, hPu]

theorem subset_graph_interpolatingFunction
    {y : I → F} (hy : Function.Injective y)
    {r : ℕ} {A : Finset (I × F)} (hA : A ∈ transversalHost (I := I) (F := F) r) :
    A ⊆ graph (interpolatingFunction y A) := by
  classical
  intro z hz
  rcases z with ⟨i, x⟩
  rw [mem_graph, interpolatingFunction]
  rw [Lagrange.eval_interpolate_at_node (valueAt A)
    (hy.injOn : Set.InjOn y (A.image Prod.fst))]
  · exact (valueAt_eq_of_mem (mem_transversalHost.mp hA).2 hz).symm
  · exact Finset.mem_image.mpr ⟨(i, x), hz, rfl⟩

theorem polynomialFunction_eq_interpolatingFunction
    {y : I → F} (hy : Function.Injective y)
    {r : ℕ} {A : Finset (I × F)} (hA : A ∈ transversalHost (I := I) (F := F) r)
    {f : I → F} (hf : f ∈ polynomialFunctions y r) (hAf : A ⊆ graph f) :
    f = interpolatingFunction y A := by
  classical
  rw [polynomialFunctions] at hf
  obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hf
  let Q : F[X] := Polynomial.ofFn r u
  let P : F[X] := Lagrange.interpolate (A.image Prod.fst) y (valueAt A)
  have hScard : (A.image Prod.fst).card = r := by
    rw [Finset.card_image_iff.mpr (mem_transversalHost.mp hA).2,
      (mem_transversalHost.mp hA).1]
  have hQdeg : Q.degree < (A.image Prod.fst).card := by
    rw [hScard]
    exact Polynomial.ofFn_degree_lt u
  have hQeval : ∀ i ∈ A.image Prod.fst, Q.eval (y i) = valueAt A i := by
    intro i hi
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    rcases z with ⟨j, x⟩
    simp only at hzi
    subst j
    have hxgraph := hAf hz
    have hxf : x = Q.eval (y i) := by simpa [Q] using (mem_graph.mp hxgraph)
    rw [valueAt_eq_of_mem (mem_transversalHost.mp hA).2 hz]
    exact hxf.symm
  have hQP : Q = P := by
    exact Lagrange.eq_interpolate_of_eval_eq (valueAt A)
      (hy.injOn : Set.InjOn y (A.image Prod.fst)) hQdeg hQeval
  funext i
  simp only [interpolatingFunction, P, Q] at hQP ⊢
  rw [hQP]

theorem existsUnique_polynomialFunction
    {y : I → F} (hy : Function.Injective y)
    {r : ℕ} {A : Finset (I × F)} (hA : A ∈ transversalHost (I := I) (F := F) r) :
    ∃! f : I → F, f ∈ polynomialFunctions y r ∧ A ⊆ graph f := by
  refine ⟨interpolatingFunction y A, ⟨
    interpolatingFunction_mem hy hA,
    subset_graph_interpolatingFunction hy hA⟩, ?_⟩
  intro f hf
  exact polynomialFunction_eq_interpolatingFunction hy hA hf.1 hf.2

/-- Uniform clique-decomposition predicate on an arbitrary finite vertex
type, used locally for the algebraic blow-up. -/
def IsUniformDecomposition {V : Type*} [DecidableEq V]
    (host blocks : Finset (Finset V)) (q r : ℕ) : Prop :=
  (∀ B ∈ blocks, B.card = q) ∧
    (∀ B ∈ blocks, B.powersetCard r ⊆ host) ∧
    ∀ A ∈ host, (blocks.filter fun B ↦ A ⊆ B).card = 1

/-- Two decompositions of the same host form a clique trade. -/
def IsUniformTrade {V : Type*} [DecidableEq V]
    (positive negative : Finset (Finset V)) (q r : ℕ) : Prop :=
  ∃ host : Finset (Finset V),
    IsUniformDecomposition host positive q r ∧
      IsUniformDecomposition host negative q r

/-- Number of blocks of a family containing a fixed set. -/
def incidenceCount {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (A : Finset V) : ℕ :=
  (blocks.filter fun B ↦ A ⊆ B).card

theorem IsUniformDecomposition.incidenceCount_eq_indicator
    {V : Type*} [DecidableEq V]
    {host blocks : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformDecomposition host blocks q r)
    {A : Finset V} (hAcard : A.card = r) :
    incidenceCount blocks A = if A ∈ host then 1 else 0 := by
  classical
  by_cases hA : A ∈ host
  · rw [if_pos hA]
    exact h.2.2 A hA
  · rw [if_neg hA, incidenceCount, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro B hB
    have hm := Finset.mem_filter.mp hB
    exact hA (h.2.1 B hm.1 (Finset.mem_powersetCard.mpr
      ⟨hm.2, hAcard⟩))

/-- The two sides of a trade have identical incidence at every `r`-edge,
not merely at edges explicitly listed in the common host. -/
theorem IsUniformTrade.incidenceCount_eq
    {V : Type*} [DecidableEq V]
    {positive negative : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformTrade positive negative q r)
    {A : Finset V} (hAcard : A.card = r) :
    incidenceCount positive A = incidenceCount negative A := by
  obtain ⟨host, hpositive, hnegative⟩ := h
  rw [hpositive.incidenceCount_eq_indicator hAcard,
    hnegative.incidenceCount_eq_indicator hAcard]

/-- Integer boundary of a signed block vector on an arbitrary vertex
type. -/
def signedIncidence {V : Type*} [DecidableEq V]
    (blocks : Finset (Finset V)) (coeff : Finset V → ℤ)
    (A : Finset V) : ℤ :=
  ∑ B ∈ blocks, if A ⊆ B then coeff B else 0

theorem IsUniformTrade.signedIncidence_add_trade
    {V : Type*} [DecidableEq V]
    {positive negative support : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformTrade positive negative q r)
    (coeff : Finset V → ℤ) (z : ℤ)
    {A : Finset V} (hAcard : A.card = r) :
    signedIncidence support coeff A +
        z * (incidenceCount positive A : ℤ) -
        z * (incidenceCount negative A : ℤ) =
      signedIncidence support coeff A := by
  rw [h.incidenceCount_eq hAcard]
  ring

/-- Apply an injective relabelling to every vertex in a family of sets. -/
def mapFamily {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (family : Finset (Finset V)) : Finset (Finset W) :=
  family.map (Finset.mapEmbedding f).toEmbedding

@[simp] theorem mem_mapFamily {V W : Type*} [DecidableEq V] [DecidableEq W]
    {f : V ↪ W} {family : Finset (Finset V)} {B : Finset W} :
    B ∈ mapFamily f family ↔ ∃ A ∈ family, A.map f = B := by
  simp [mapFamily]

@[simp] theorem card_mapFamily {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (family : Finset (Finset V)) :
    (mapFamily f family).card = family.card := by
  simp [mapFamily]

theorem mapFamily_powersetCard {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (A : Finset V) (r : ℕ) :
    mapFamily f (A.powersetCard r) = (A.map f).powersetCard r := by
  simpa [mapFamily] using (Finset.powersetCard_map f r A).symm

/-- A decomposition covers no hidden edges: its host is precisely the
union of the complete `r`-graphs on its blocks. -/
theorem IsUniformDecomposition.host_eq_biUnion
    {V : Type*} [DecidableEq V]
    {host blocks : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformDecomposition host blocks q r)
    (huniform : ∀ A ∈ host, A.card = r) :
    host = blocks.biUnion fun B ↦ B.powersetCard r := by
  classical
  ext A
  constructor
  · intro hA
    have hpos : 0 < (blocks.filter fun B ↦ A ⊆ B).card := by
      rw [h.2.2 A hA]
      decide
    obtain ⟨B, hB⟩ := Finset.card_pos.mp hpos
    have hm := Finset.mem_filter.mp hB
    apply Finset.mem_biUnion.mpr
    exact ⟨B, hm.1, Finset.mem_powersetCard.mpr
      ⟨hm.2, huniform A hA⟩⟩
  · intro hA
    obtain ⟨B, hB, hAB⟩ := Finset.mem_biUnion.mp hA
    exact h.2.1 B hB hAB

/-- A uniform family whose distinct blocks have disjoint complete
`r`-boundaries is the canonical decomposition of the union of those
boundaries. -/
theorem IsUniformDecomposition.of_pairwise_powersetCard
    {V : Type*} [DecidableEq V]
    {blocks : Finset (Finset V)} {q r : ℕ}
    (huniform : ∀ B ∈ blocks, B.card = q)
    (hpair : ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' →
      Disjoint (B.powersetCard r) (B'.powersetCard r)) :
    IsUniformDecomposition
      (blocks.biUnion fun B ↦ B.powersetCard r) blocks q r := by
  classical
  refine ⟨huniform, ?_, ?_⟩
  · intro B hB e he
    exact Finset.mem_biUnion.mpr ⟨B, hB, he⟩
  · intro e he
    obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he
    have hecard : e.card = r := (Finset.mem_powersetCard.mp heB).2
    have hfilter : blocks.filter (fun Q ↦ e ⊆ Q) = {B} := by
      ext Q
      constructor
      · intro hQ
        have hQdata := Finset.mem_filter.mp hQ
        have heQ : e ∈ Q.powersetCard r :=
          Finset.mem_powersetCard.mpr ⟨hQdata.2, hecard⟩
        have hQB : Q = B := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (hpair B hB Q hQdata.1 (fun h ↦ hne h.symm)) heB heQ
        exact Finset.mem_singleton.mpr hQB
      · intro hQ
        have hQB : Q = B := Finset.mem_singleton.mp hQ
        subst Q
        exact Finset.mem_filter.mpr
          ⟨hB, (Finset.mem_powersetCard.mp heB).1⟩
    rw [hfilter]
    simp

/-- Injective relabelling preserves a uniform clique decomposition. -/
theorem IsUniformDecomposition.map
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {host blocks : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformDecomposition host blocks q r) (f : V ↪ W) :
    IsUniformDecomposition (mapFamily f host) (mapFamily f blocks) q r := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := mem_mapFamily.mp hB
    simpa using h.1 A hA
  · intro B hB E hE
    obtain ⟨A, hA, rfl⟩ := mem_mapFamily.mp hB
    rw [← mapFamily_powersetCard f A r] at hE
    obtain ⟨D, hD, rfl⟩ := mem_mapFamily.mp hE
    exact mem_mapFamily.mpr ⟨D, h.2.1 A hA hD, rfl⟩
  · intro E hE
    obtain ⟨D, hD, rfl⟩ := mem_mapFamily.mp hE
    have hfilter :
        (mapFamily f blocks).filter (fun B ↦ D.map f ⊆ B) =
          mapFamily f (blocks.filter fun A ↦ D ⊆ A) := by
      ext B
      simp only [Finset.mem_filter, mem_mapFamily]
      constructor
      · rintro ⟨⟨A, hA, rfl⟩, hsub⟩
        exact ⟨A, ⟨hA, Finset.map_subset_map.mp hsub⟩, rfl⟩
      · rintro ⟨A, hA, rfl⟩
        exact ⟨⟨A, hA.1, rfl⟩,
          Finset.map_subset_map.mpr hA.2⟩
    rw [hfilter, mapFamily, Finset.card_map, h.2.2 D hD]

/-- Injective relabelling preserves both sides of a trade. -/
theorem IsUniformTrade.map
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {positive negative : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformTrade positive negative q r) (f : V ↪ W) :
    IsUniformTrade (mapFamily f positive) (mapFamily f negative) q r := by
  obtain ⟨host, hpos, hneg⟩ := h
  exact ⟨mapFamily f host, hpos.map f, hneg.map f⟩

/-- In a genuine decomposition two blocks containing the same host edge
are equal. -/
theorem IsUniformDecomposition.blocks_eq_of_common_edge
    {V : Type*} [DecidableEq V]
    {host blocks : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformDecomposition host blocks q r)
    {A B C : Finset V} (hB : B ∈ blocks) (hC : C ∈ blocks)
    (hAB : A ∈ B.powersetCard r) (hAC : A ∈ C.powersetCard r) :
    B = C := by
  classical
  have hAhost : A ∈ host := h.2.1 B hB hAB
  have hcard := h.2.2 A hAhost
  obtain ⟨D, hD⟩ := Finset.card_eq_one.mp hcard
  have hBfilter : B ∈ blocks.filter fun Q ↦ A ⊆ Q :=
    Finset.mem_filter.mpr ⟨hB, (Finset.mem_powersetCard.mp hAB).1⟩
  have hCfilter : C ∈ blocks.filter fun Q ↦ A ⊆ Q :=
    Finset.mem_filter.mpr ⟨hC, (Finset.mem_powersetCard.mp hAC).1⟩
  rw [hD] at hBfilter hCfilter
  exact (Finset.mem_singleton.mp hBfilter).trans
    (Finset.mem_singleton.mp hCfilter).symm

/-- Removing one block removes exactly its complete `r`-graph and leaves
a decomposition of the residual host. -/
theorem IsUniformDecomposition.erase
    {V : Type*} [DecidableEq V]
    {host blocks : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformDecomposition host blocks q r)
    (huniform : ∀ A ∈ host, A.card = r)
    {B : Finset V} (hB : B ∈ blocks) :
    IsUniformDecomposition (host \ B.powersetCard r) (blocks.erase B) q r := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    exact h.1 C (Finset.mem_of_mem_erase hC)
  · intro C hC A hA
    have hCblocks : C ∈ blocks := Finset.mem_of_mem_erase hC
    apply Finset.mem_sdiff.mpr
    refine ⟨h.2.1 C hCblocks hA, ?_⟩
    intro hAB
    have hCB := h.blocks_eq_of_common_edge hCblocks hB hA hAB
    exact (Finset.ne_of_mem_erase hC) hCB
  · intro A hA
    have hAhost : A ∈ host := (Finset.mem_sdiff.mp hA).1
    have hAnot : A ∉ B.powersetCard r := (Finset.mem_sdiff.mp hA).2
    have hAB : ¬ A ⊆ B := by
      intro hsub
      exact hAnot (Finset.mem_powersetCard.mpr
        ⟨hsub, huniform A hAhost⟩)
    rw [Finset.filter_erase]
    have hBnot : B ∉ blocks.filter fun C ↦ A ⊆ C := by simp [hAB]
    rw [Finset.erase_eq_of_notMem hBnot]
    exact h.2.2 A hAhost

/-- Removing any subfamily of blocks removes exactly the union of their
complete edge sets and leaves a decomposition of the residual host. -/
theorem IsUniformDecomposition.sdiff_blocks
    {V : Type*} [DecidableEq V]
    {host blocks removed : Finset (Finset V)} {q r : ℕ}
    (h : IsUniformDecomposition host blocks q r)
    (huniform : ∀ A ∈ host, A.card = r)
    (hremoved : removed ⊆ blocks) :
    IsUniformDecomposition
      (host \ removed.biUnion (fun B ↦ B.powersetCard r))
      (blocks \ removed) q r := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    exact h.1 B (Finset.mem_sdiff.mp hB).1
  · intro B hB A hA
    have hBblocks : B ∈ blocks := (Finset.mem_sdiff.mp hB).1
    have hBnot : B ∉ removed := (Finset.mem_sdiff.mp hB).2
    apply Finset.mem_sdiff.mpr
    refine ⟨h.2.1 B hBblocks hA, ?_⟩
    intro hAremoved
    obtain ⟨C, hCremoved, hAC⟩ := Finset.mem_biUnion.mp hAremoved
    have hCblocks : C ∈ blocks := hremoved hCremoved
    have hBC := h.blocks_eq_of_common_edge hBblocks hCblocks hA hAC
    exact hBnot (hBC ▸ hCremoved)
  · intro A hA
    have hAhost : A ∈ host := (Finset.mem_sdiff.mp hA).1
    have hAnot := (Finset.mem_sdiff.mp hA).2
    have hremovedNone : ∀ C ∈ removed, ¬A ⊆ C := by
      intro C hC hAC
      apply hAnot
      apply Finset.mem_biUnion.mpr
      exact ⟨C, hC, Finset.mem_powersetCard.mpr
        ⟨hAC, huniform A hAhost⟩⟩
    have hfilter :
        (blocks \ removed).filter (fun B ↦ A ⊆ B) =
          blocks.filter (fun B ↦ A ⊆ B) := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · exact fun hB ↦ ⟨hB.1.1, hB.2⟩
      · intro hB
        exact ⟨⟨hB.1, fun hBr ↦ hremovedNone B hBr hB.2⟩, hB.2⟩
    rw [hfilter]
    exact h.2.2 A hAhost

/-- Decompositions of edge-disjoint uniform hosts have disjoint block
families when every block contains an `r`-edge. -/
theorem IsUniformDecomposition.disjoint_blocks
    {V : Type*} [DecidableEq V]
    {host₁ host₂ blocks₁ blocks₂ : Finset (Finset V)} {q r : ℕ}
    (h₁ : IsUniformDecomposition host₁ blocks₁ q r)
    (h₂ : IsUniformDecomposition host₂ blocks₂ q r)
    (hhost : Disjoint host₁ host₂) (hrq : r ≤ q) :
    Disjoint blocks₁ blocks₂ := by
  classical
  apply Finset.disjoint_left.mpr
  intro B hB₁ hB₂
  have hrB : r ≤ B.card := by simpa [h₁.1 B hB₁] using hrq
  obtain ⟨A, hA⟩ := Finset.powersetCard_nonempty.mpr hrB
  exact Finset.disjoint_left.mp hhost
    (h₁.2.1 B hB₁ hA) (h₂.2.1 B hB₂ hA)

/-- Edge-disjoint uniform decompositions combine. -/
theorem IsUniformDecomposition.union
    {V : Type*} [DecidableEq V]
    {host₁ host₂ blocks₁ blocks₂ : Finset (Finset V)} {q r : ℕ}
    (h₁ : IsUniformDecomposition host₁ blocks₁ q r)
    (h₂ : IsUniformDecomposition host₂ blocks₂ q r)
    (huniform₁ : ∀ A ∈ host₁, A.card = r)
    (huniform₂ : ∀ A ∈ host₂, A.card = r)
    (hhost : Disjoint host₁ host₂) (hrq : r ≤ q) :
    IsUniformDecomposition (host₁ ∪ host₂) (blocks₁ ∪ blocks₂) q r := by
  classical
  have hblocks : Disjoint blocks₁ blocks₂ :=
    h₁.disjoint_blocks h₂ hhost hrq
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · exact h₁.1 B hB
    · exact h₂.1 B hB
  · intro B hB A hA
    rcases Finset.mem_union.mp hB with hB | hB
    · exact Finset.mem_union_left _ (h₁.2.1 B hB hA)
    · exact Finset.mem_union_right _ (h₂.2.1 B hB hA)
  · intro A hA
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    · rcases Finset.mem_union.mp hA with hA₁ | hA₂
      · have hz : (blocks₂.filter fun B ↦ A ⊆ B).card = 0 := by
          rw [Finset.card_eq_zero]
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro B hB
          have hm := Finset.mem_filter.mp hB
          have hA₂ : A ∈ host₂ := h₂.2.1 B hm.1
            (Finset.mem_powersetCard.mpr ⟨hm.2, huniform₁ A hA₁⟩)
          exact Finset.disjoint_left.mp hhost hA₁ hA₂
        rw [h₁.2.2 A hA₁, hz]
      · have hz : (blocks₁.filter fun B ↦ A ⊆ B).card = 0 := by
          rw [Finset.card_eq_zero]
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro B hB
          have hm := Finset.mem_filter.mp hB
          have hA₁ : A ∈ host₁ := h₁.2.1 B hm.1
            (Finset.mem_powersetCard.mpr ⟨hm.2, huniform₂ A hA₂⟩)
          exact Finset.disjoint_left.mp hhost hA₁ hA₂
        rw [hz, h₂.2.2 A hA₂]
    · exact Disjoint.mono (Finset.filter_subset _ _)
        (Finset.filter_subset _ _) hblocks

/-- Canonical edge-boundary decompositions combine when every block on the
left has edge-disjoint boundary from every block on the right. -/
theorem IsUniformDecomposition.union_canonical
    {V : Type*} [DecidableEq V]
    {blocks₁ blocks₂ : Finset (Finset V)} {q r : ℕ}
    (h₁ : IsUniformDecomposition
      (blocks₁.biUnion fun B ↦ B.powersetCard r) blocks₁ q r)
    (h₂ : IsUniformDecomposition
      (blocks₂.biUnion fun B ↦ B.powersetCard r) blocks₂ q r)
    (hcross : ∀ B ∈ blocks₁, ∀ B' ∈ blocks₂,
      ∀ e, e ∈ B.powersetCard r → e ∈ B'.powersetCard r → False)
    (hrq : r ≤ q) :
    IsUniformDecomposition
      ((blocks₁ ∪ blocks₂).biUnion fun B ↦ B.powersetCard r)
      (blocks₁ ∪ blocks₂) q r := by
  have hhost : Disjoint
      (blocks₁.biUnion fun B ↦ B.powersetCard r)
      (blocks₂.biUnion fun B ↦ B.powersetCard r) := by
    apply Finset.disjoint_left.mpr
    intro e he₁ he₂
    obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he₁
    obtain ⟨B', hB', heB'⟩ := Finset.mem_biUnion.mp he₂
    exact hcross B hB B' hB' e heB heB'
  have huniform₁ : ∀ e ∈
      blocks₁.biUnion (fun B ↦ B.powersetCard r), e.card = r := by
    intro e he
    obtain ⟨B, _hB, heB⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_powersetCard.mp heB).2
  have huniform₂ : ∀ e ∈
      blocks₂.biUnion (fun B ↦ B.powersetCard r), e.card = r := by
    intro e he
    obtain ⟨B, _hB, heB⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_powersetCard.mp heB).2
  have hbi : (blocks₁ ∪ blocks₂).biUnion
      (fun B ↦ B.powersetCard r) =
      (blocks₁.biUnion fun B ↦ B.powersetCard r) ∪
        (blocks₂.biUnion fun B ↦ B.powersetCard r) := by
    ext e
    constructor
    · intro he
      obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he
      rcases Finset.mem_union.mp hB with hB | hB
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨B, hB, heB⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hB, heB⟩)
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr
          ⟨B, Finset.mem_union_left _ hB, heB⟩
      · obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr
          ⟨B, Finset.mem_union_right _ hB, heB⟩
  rw [hbi]
  exact h₁.union h₂ huniform₁ huniform₂ hhost hrq

/-- Pairwise edge-disjoint decompositions may be assembled over a finite
index set. -/
theorem IsUniformDecomposition.biUnion
    {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (S : Finset ι) (host blocks : ι → Finset (Finset V))
    {q r : ℕ}
    (hdecomp : ∀ i ∈ S, IsUniformDecomposition (host i) (blocks i) q r)
    (huniform : ∀ i ∈ S, ∀ e ∈ host i, e.card = r)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (host i) (host j))
    (hrq : r ≤ q) :
    IsUniformDecomposition (S.biUnion host) (S.biUnion blocks) q r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [IsUniformDecomposition]
  | @insert a S ha ih =>
      have haDecomp : IsUniformDecomposition (host a) (blocks a) q r :=
        hdecomp a (by simp)
      have htailDecomp :
          IsUniformDecomposition (S.biUnion host) (S.biUnion blocks) q r := by
        apply ih
        · intro i hi
          exact hdecomp i (by simp [hi])
        · intro i hi e he
          exact huniform i (by simp [hi]) e he
        · intro i hi j hj hij
          exact hpair i (by simp [hi]) j (by simp [hj]) hij
      have htailUniform : ∀ e ∈ S.biUnion host, e.card = r := by
        intro e he
        obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
        exact huniform i (by simp [hi]) e hei
      have hdis : Disjoint (host a) (S.biUnion host) := by
        apply Finset.disjoint_left.mpr
        intro e hea hetail
        obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp hetail
        have haj : a ≠ j := by
          intro heq
          subst j
          exact ha hj
        exact Finset.disjoint_left.mp
          (hpair a (by simp) j (by simp [hj]) haj) hea hej
      simpa using haDecomp.union htailDecomp
        (huniform a (by simp)) htailUniform hdis hrq

/-! ### Gluing two trades along designated blocks -/

/-- Concrete vertex type for gluing `V₁` to `V₂` along a designated
finite set `Q₂`: vertices of `Q₂` are represented on the left and all
other right vertices remain tagged. -/
abbrev GluedVertex (V₁ V₂ : Type*) [DecidableEq V₂] (Q₂ : Finset V₂) :=
  V₁ ⊕ {v : V₂ // v ∉ Q₂}

def glueLeftEmbedding (V₁ V₂ : Type*) [DecidableEq V₂] (Q₂ : Finset V₂) :
    V₁ ↪ GluedVertex V₁ V₂ Q₂ :=
  ⟨Sum.inl, Sum.inl_injective⟩

def glueRightFun {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂) (v : V₂) :
    GluedVertex V₁ V₂ Q₂ :=
  if hv : v ∈ Q₂ then Sum.inl (equiv.symm ⟨v, hv⟩).1
  else Sum.inr ⟨v, hv⟩

theorem glueRightFun_injective
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂) :
    Function.Injective (glueRightFun equiv) := by
  intro v w hvw
  by_cases hv : v ∈ Q₂ <;> by_cases hw : w ∈ Q₂
  · simpa [glueRightFun, hv, hw] using hvw
  · simp [glueRightFun, hv, hw] at hvw
  · simp [glueRightFun, hv, hw] at hvw
  · simpa [glueRightFun, hv, hw] using hvw

def glueRightEmbedding
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂) :
    V₂ ↪ GluedVertex V₁ V₂ Q₂ :=
  ⟨glueRightFun equiv, glueRightFun_injective equiv⟩

theorem glueRightEmbedding_mem_map_left_iff
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂)
    (A : Finset V₁) (y : V₂) :
    glueRightEmbedding equiv y ∈
        A.map (glueLeftEmbedding V₁ V₂ Q₂) ↔
      ∃ hy : y ∈ Q₂, (equiv.symm ⟨y, hy⟩).1 ∈ A := by
  constructor
  · intro hyMap
    obtain ⟨x, hxA, hxy⟩ := Finset.mem_map.mp hyMap
    by_cases hyQ : y ∈ Q₂
    · refine ⟨hyQ, ?_⟩
      have hval : (equiv.symm ⟨y, hyQ⟩).1 = x := by
        simpa [glueRightEmbedding, glueRightFun, glueLeftEmbedding, hyQ]
          using hxy.symm
      exact hval.symm ▸ hxA
    · simp [glueRightEmbedding, glueRightFun, glueLeftEmbedding, hyQ] at hxy
  · rintro ⟨hyQ, hxA⟩
    apply Finset.mem_map.mpr
    refine ⟨(equiv.symm ⟨y, hyQ⟩).1, hxA, ?_⟩
    simp [glueRightEmbedding, glueRightFun, glueLeftEmbedding, hyQ]

/-- Under the concrete gluing embeddings, equality of two mapped sets
forces both originals to lie in the designated sets. -/
theorem eq_map_glue_imp_subsets
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂)
    {A₁ : Finset V₁} {A₂ : Finset V₂}
    (heq : A₁.map (glueLeftEmbedding V₁ V₂ Q₂) =
      A₂.map (glueRightEmbedding equiv)) :
    A₁ ⊆ Q₁ ∧ A₂ ⊆ Q₂ := by
  constructor
  · intro v hv
    have hmap : Sum.inl v ∈ A₂.map (glueRightEmbedding equiv) := by
      rw [← heq]
      exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hweq⟩ := Finset.mem_map.mp hmap
    by_cases hwQ : w ∈ Q₂
    · have hleft : (equiv.symm ⟨w, hwQ⟩).1 = v :=
        by simpa [glueRightEmbedding, glueRightFun, hwQ] using hweq
      exact hleft ▸ (equiv.symm ⟨w, hwQ⟩).2
    · simp [glueRightEmbedding, glueRightFun, hwQ] at hweq
  · intro w hw
    by_contra hwQ
    have hmap : glueRightEmbedding equiv w ∈
        A₁.map (glueLeftEmbedding V₁ V₂ Q₂) := by
      rw [heq]
      exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hveq⟩ := Finset.mem_map.mp hmap
    simp [glueLeftEmbedding, glueRightEmbedding, glueRightFun, hwQ] at hveq

theorem mapFamily_sdiff
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (s t : Finset (Finset V)) :
    mapFamily f (s \ t) = mapFamily f s \ mapFamily f t := by
  ext A
  simp only [Finset.mem_sdiff, mem_mapFamily]
  constructor
  · rintro ⟨B, ⟨hBs, hBnot⟩, rfl⟩
    refine ⟨⟨B, hBs, rfl⟩, ?_⟩
    rintro ⟨C, hCt, hCB⟩
    have hCB' : C = B := (Finset.map_injective f) hCB
    exact hBnot (hCB' ▸ hCt)
  · rintro ⟨⟨B, hBs, rfl⟩, hnot⟩
    refine ⟨B, ⟨hBs, ?_⟩, rfl⟩
    intro hBt
    exact hnot ⟨B, hBt, rfl⟩

theorem mapFamily_mono
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {f : V ↪ W} {s t : Finset (Finset V)} (hst : s ⊆ t) :
    mapFamily f s ⊆ mapFamily f t := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := mem_mapFamily.mp hA
  exact mem_mapFamily.mpr ⟨B, hst hB, rfl⟩

theorem map_glue_designated_eq
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂) :
    Q₁.map (glueLeftEmbedding V₁ V₂ Q₂) =
      Q₂.map (glueRightEmbedding equiv) := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
    let w : ↥Q₂ := equiv ⟨v, hv⟩
    apply Finset.mem_map.mpr
    refine ⟨w.1, w.2, ?_⟩
    simp [glueLeftEmbedding, glueRightEmbedding, glueRightFun, w]
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    apply Finset.mem_map.mpr
    refine ⟨(equiv.symm ⟨w, hw⟩).1, (equiv.symm ⟨w, hw⟩).2, ?_⟩
    simp [glueLeftEmbedding, glueRightEmbedding, glueRightFun, hw]

theorem mapFamily_glue_designated_powersetCard_eq
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂) (r : ℕ) :
    mapFamily (glueLeftEmbedding V₁ V₂ Q₂) (Q₁.powersetCard r) =
      mapFamily (glueRightEmbedding equiv) (Q₂.powersetCard r) := by
  rw [mapFamily_powersetCard, mapFamily_powersetCard,
    map_glue_designated_eq equiv]

private theorem union_sdiff_common {X : Type*} [DecidableEq X]
    {s t u : Finset X} (hus : u ⊆ s) (hut : u ⊆ t) :
    s ∪ (t \ u) = (s \ u) ∪ t := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hs | ⟨ht, hnu⟩)
    · by_cases hu : x ∈ u
      · exact Or.inr (hut hu)
      · exact Or.inl ⟨hs, hu⟩
    · exact Or.inr ht
  · rintro (⟨hs, hnu⟩ | ht)
    · exact Or.inl hs
    · by_cases hu : x ∈ u
      · exact Or.inl (hus hu)
      · exact Or.inr ⟨ht, hu⟩

theorem glued_host_eq
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {host₁ : Finset (Finset V₁)} {host₂ : Finset (Finset V₂)}
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} {r : ℕ}
    (equiv : ↥Q₁ ≃ ↥Q₂)
    (hQ₁ : Q₁.powersetCard r ⊆ host₁)
    (hQ₂ : Q₂.powersetCard r ⊆ host₂) :
    mapFamily (glueLeftEmbedding V₁ V₂ Q₂) host₁ ∪
        mapFamily (glueRightEmbedding equiv) (host₂ \ Q₂.powersetCard r) =
      mapFamily (glueLeftEmbedding V₁ V₂ Q₂) (host₁ \ Q₁.powersetCard r) ∪
        mapFamily (glueRightEmbedding equiv) host₂ := by
  rw [mapFamily_sdiff, mapFamily_sdiff]
  let E := mapFamily (glueLeftEmbedding V₁ V₂ Q₂) (Q₁.powersetCard r)
  have hE : E = mapFamily (glueRightEmbedding equiv) (Q₂.powersetCard r) :=
    mapFamily_glue_designated_powersetCard_eq equiv r
  have hE₁ : E ⊆ mapFamily (glueLeftEmbedding V₁ V₂ Q₂) host₁ :=
    mapFamily_mono hQ₁
  have hE₂ : E ⊆ mapFamily (glueRightEmbedding equiv) host₂ := by
    rw [hE]
    exact mapFamily_mono hQ₂
  rw [← hE]
  exact union_sdiff_common hE₁ hE₂

/-- Gluing never uses more edges than the sum of the two input hosts. -/
theorem card_gluedHost_le
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    (host₁ : Finset (Finset V₁)) (host₂ : Finset (Finset V₂))
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} (equiv : ↥Q₁ ≃ ↥Q₂) (r : ℕ) :
    (mapFamily (glueLeftEmbedding V₁ V₂ Q₂) host₁ ∪
      mapFamily (glueRightEmbedding equiv) (host₂ \ Q₂.powersetCard r)).card ≤
        host₁.card + host₂.card := by
  calc
    _ ≤ (mapFamily (glueLeftEmbedding V₁ V₂ Q₂) host₁).card +
          (mapFamily (glueRightEmbedding equiv)
            (host₂ \ Q₂.powersetCard r)).card :=
      Finset.card_union_le _ _
    _ = host₁.card + (host₂ \ Q₂.powersetCard r).card := by simp
    _ ≤ host₁.card + host₂.card := Nat.add_le_add_left (Finset.card_le_card
      (Finset.sdiff_subset)) host₁.card

theorem uniform_mapFamily
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    {host : Finset (Finset V)} {r : ℕ}
    (huniform : ∀ A ∈ host, A.card = r) (f : V ↪ W) :
    ∀ A ∈ mapFamily f host, A.card = r := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := mem_mapFamily.mp hA
  simpa using huniform B hB

theorem disjoint_glue_left_right_residual
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {host₁ : Finset (Finset V₁)} {host₂ : Finset (Finset V₂)}
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} {r : ℕ}
    (equiv : ↥Q₁ ≃ ↥Q₂) (huniform₂ : ∀ A ∈ host₂, A.card = r) :
    Disjoint (mapFamily (glueLeftEmbedding V₁ V₂ Q₂) host₁)
      (mapFamily (glueRightEmbedding equiv) (host₂ \ Q₂.powersetCard r)) := by
  apply Finset.disjoint_left.mpr
  intro E hE₁ hE₂
  obtain ⟨A₁, _hA₁, hA₁E⟩ := mem_mapFamily.mp hE₁
  obtain ⟨A₂, hA₂, hA₂E⟩ := mem_mapFamily.mp hE₂
  have hmaps : A₁.map (glueLeftEmbedding V₁ V₂ Q₂) =
      A₂.map (glueRightEmbedding equiv) := hA₁E.trans hA₂E.symm
  have hA₂Q := (eq_map_glue_imp_subsets equiv hmaps).2
  exact (Finset.mem_sdiff.mp hA₂).2 (Finset.mem_powersetCard.mpr
    ⟨hA₂Q, huniform₂ A₂ (Finset.mem_sdiff.mp hA₂).1⟩)

/-- Any edge of a glued host which is supported entirely on the old (left)
vertex universe already comes from the old host.  The right residual cannot
contribute such an edge because all-right edges supported on the gluing
clique were erased. -/
theorem exists_left_preimage_of_mem_gluedHost_of_subset_left
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    [Fintype V₁]
    {host₁ : Finset (Finset V₁)} {host₂ : Finset (Finset V₂)}
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} {r : ℕ}
    (equiv : ↥Q₁ ≃ ↥Q₂)
    (huniform₂ : ∀ A ∈ host₂, A.card = r)
    {A : Finset (GluedVertex V₁ V₂ Q₂)}
    (hA : A ∈ mapFamily (glueLeftEmbedding V₁ V₂ Q₂) host₁ ∪
      mapFamily (glueRightEmbedding equiv) (host₂ \ Q₂.powersetCard r))
    (hsub : A ⊆ (Finset.univ : Finset V₁).map
      (glueLeftEmbedding V₁ V₂ Q₂)) :
    ∃ A₁ ∈ host₁,
      A₁.map (glueLeftEmbedding V₁ V₂ Q₂) = A := by
  rcases Finset.mem_union.mp hA with hleft | hright
  · obtain ⟨A₁, hA₁, hmap⟩ := mem_mapFamily.mp hleft
    exact ⟨A₁, hA₁, hmap⟩
  · obtain ⟨A₂, hA₂, hmap₂⟩ := mem_mapFamily.mp hright
    obtain ⟨A₁, hA₁univ, hmap₁⟩ := Finset.subset_map_iff.mp hsub
    have hmaps : A₁.map (glueLeftEmbedding V₁ V₂ Q₂) =
        A₂.map (glueRightEmbedding equiv) := hmap₁.symm.trans hmap₂.symm
    have hA₂Q := (eq_map_glue_imp_subsets equiv hmaps).2
    exact False.elim ((Finset.mem_sdiff.mp hA₂).2
      (Finset.mem_powersetCard.mpr
        ⟨hA₂Q, huniform₂ A₂ (Finset.mem_sdiff.mp hA₂).1⟩))

theorem disjoint_glue_left_residual_right
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {host₁ : Finset (Finset V₁)} {host₂ : Finset (Finset V₂)}
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} {r : ℕ}
    (equiv : ↥Q₁ ≃ ↥Q₂) (huniform₁ : ∀ A ∈ host₁, A.card = r) :
    Disjoint
      (mapFamily (glueLeftEmbedding V₁ V₂ Q₂) (host₁ \ Q₁.powersetCard r))
      (mapFamily (glueRightEmbedding equiv) host₂) := by
  apply Finset.disjoint_left.mpr
  intro E hE₁ hE₂
  obtain ⟨A₁, hA₁, hA₁E⟩ := mem_mapFamily.mp hE₁
  obtain ⟨A₂, _hA₂, hA₂E⟩ := mem_mapFamily.mp hE₂
  have hmaps : A₁.map (glueLeftEmbedding V₁ V₂ Q₂) =
      A₂.map (glueRightEmbedding equiv) := hA₁E.trans hA₂E.symm
  have hA₁Q := (eq_map_glue_imp_subsets equiv hmaps).1
  exact (Finset.mem_sdiff.mp hA₁).2 (Finset.mem_powersetCard.mpr
    ⟨hA₁Q, huniform₁ A₁ (Finset.mem_sdiff.mp hA₁).1⟩)

/-- The abstract gluing operation from the exchange-gadget construction.
The negative designated block of the first trade is identified with the
positive designated block of the second; the two cancelling copies are
then erased. -/
theorem glue_uniform_trades
    {V₁ V₂ : Type*} [DecidableEq V₁] [DecidableEq V₂]
    {host₁ positive₁ negative₁ : Finset (Finset V₁)}
    {host₂ positive₂ negative₂ : Finset (Finset V₂)}
    {Q₁ : Finset V₁} {Q₂ : Finset V₂} {q r : ℕ}
    (hpositive₁ : IsUniformDecomposition host₁ positive₁ q r)
    (hnegative₁ : IsUniformDecomposition host₁ negative₁ q r)
    (hpositive₂ : IsUniformDecomposition host₂ positive₂ q r)
    (hnegative₂ : IsUniformDecomposition host₂ negative₂ q r)
    (huniform₁ : ∀ A ∈ host₁, A.card = r)
    (huniform₂ : ∀ A ∈ host₂, A.card = r)
    (hQ₁ : Q₁ ∈ negative₁) (hQ₂ : Q₂ ∈ positive₂)
    (equiv : ↥Q₁ ≃ ↥Q₂) (hrq : r ≤ q) :
    IsUniformTrade
      (mapFamily (glueLeftEmbedding V₁ V₂ Q₂) positive₁ ∪
        mapFamily (glueRightEmbedding equiv) (positive₂.erase Q₂))
      (mapFamily (glueLeftEmbedding V₁ V₂ Q₂) (negative₁.erase Q₁) ∪
        mapFamily (glueRightEmbedding equiv) negative₂) q r := by
  let left := glueLeftEmbedding V₁ V₂ Q₂
  let right := glueRightEmbedding equiv
  let gluedHost := mapFamily left host₁ ∪
    mapFamily right (host₂ \ Q₂.powersetCard r)
  have hleftUniform : ∀ A ∈ mapFamily left host₁, A.card = r :=
    uniform_mapFamily huniform₁ left
  have hrightResidualUniform :
      ∀ A ∈ mapFamily right (host₂ \ Q₂.powersetCard r), A.card = r :=
    uniform_mapFamily (fun A hA ↦ huniform₂ A (Finset.mem_sdiff.mp hA).1) right
  have hpositive : IsUniformDecomposition gluedHost
      (mapFamily left positive₁ ∪ mapFamily right (positive₂.erase Q₂)) q r := by
    exact (hpositive₁.map left).union
      ((hpositive₂.erase huniform₂ hQ₂).map right)
      hleftUniform hrightResidualUniform
      (disjoint_glue_left_right_residual equiv huniform₂) hrq
  have hleftResidualUniform :
      ∀ A ∈ mapFamily left (host₁ \ Q₁.powersetCard r), A.card = r :=
    uniform_mapFamily (fun A hA ↦ huniform₁ A (Finset.mem_sdiff.mp hA).1) left
  have hrightUniform : ∀ A ∈ mapFamily right host₂, A.card = r :=
    uniform_mapFamily huniform₂ right
  have hnegative' : IsUniformDecomposition
      (mapFamily left (host₁ \ Q₁.powersetCard r) ∪ mapFamily right host₂)
      (mapFamily left (negative₁.erase Q₁) ∪ mapFamily right negative₂) q r := by
    exact ((hnegative₁.erase huniform₁ hQ₁).map left).union
      (hnegative₂.map right) hleftResidualUniform hrightUniform
      (disjoint_glue_left_residual_right equiv huniform₁) hrq
  have hhosts : gluedHost =
      mapFamily left (host₁ \ Q₁.powersetCard r) ∪ mapFamily right host₂ := by
    exact glued_host_eq equiv (hnegative₁.2.1 Q₁ hQ₁)
      (hpositive₂.2.1 Q₂ hQ₂)
  refine ⟨gluedHost, hpositive, ?_⟩
  exact hhosts.symm ▸ hnegative'

/-- Graphs of degree-`< r` polynomial functions decompose every
transversal `r`-set exactly once. -/
theorem polynomialBlocks_decompose
    {y : I → F} (hy : Function.Injective y) (r : ℕ) :
    IsUniformDecomposition (transversalHost (I := I) (F := F) r)
      (polynomialBlocks y r) (Fintype.card I) r := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hB
    exact card_graph f
  · intro B hB A hA
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hB
    have hAsub : A ⊆ graph f := (Finset.mem_powersetCard.mp hA).1
    have hAcard : A.card = r := (Finset.mem_powersetCard.mp hA).2
    apply mem_transversalHost.mpr
    refine ⟨hAcard, ?_⟩
    intro z hz w hw hfst
    rcases z with ⟨i, x⟩
    rcases w with ⟨j, t⟩
    simp only at hfst
    subst j
    have hzx := mem_graph.mp (hAsub hz)
    have hwt := mem_graph.mp (hAsub hw)
    simp only [Prod.mk.injEq, true_and]
    exact hzx.trans hwt.symm
  · intro A hA
    have huniq := existsUnique_polynomialFunction hy hA
    obtain ⟨f, hf, hfunique⟩ := huniq
    have heq :
        (polynomialBlocks y r).filter (fun B ↦ A ⊆ B) = {graph f} := by
      ext B
      constructor
      · intro hB
        have hm := Finset.mem_filter.mp hB
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hm.1
        have hgf : g = f := hfunique g ⟨hg, hm.2⟩
        simp [hgf]
      · intro hB
        have hBf : B = graph f := Finset.mem_singleton.mp hB
        subst B
        exact Finset.mem_filter.mpr ⟨
          Finset.mem_image.mpr ⟨f, hf.1, rfl⟩, hf.2⟩
    rw [heq]
    simp

/-- Translate the field coordinate in each part by `-b i`. -/
def shiftVertex (b : I → F) (z : I × F) : I × F :=
  (z.1, z.2 - b z.1)

def shiftVertices (b : I → F) (A : Finset (I × F)) : Finset (I × F) :=
  A.image (shiftVertex b)

omit [Fintype I] [DecidableEq I] [Fintype F] [DecidableEq F] in
theorem shiftVertex_injective (b : I → F) :
    Function.Injective (shiftVertex b) := by
  rintro ⟨i, x⟩ ⟨j, t⟩ h
  simp only [shiftVertex, Prod.mk.injEq] at h ⊢
  constructor
  · exact h.1
  · cases h.1
    exact sub_left_inj.mp h.2

omit [Fintype I] [Fintype F] in
theorem mem_shiftVertices_iff {b : I → F} {A : Finset (I × F)} {i : I} {x : F} :
    (i, x) ∈ shiftVertices b A ↔ (i, x + b i) ∈ A := by
  constructor
  · intro h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp h
    rcases z with ⟨j, t⟩
    simp only [shiftVertex, Prod.mk.injEq] at hzx
    have hz' : (i, t) ∈ A := by simpa [hzx.1] using hz
    have ht : t = x + b i := (sub_eq_iff_eq_add).mp (by
      simpa [hzx.1] using hzx.2)
    simpa [ht] using hz'
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(i, x + b i), h, ?_⟩
    simp [shiftVertex]

theorem shiftVertices_mem_transversalHost {b : I → F}
    {r : ℕ} {A : Finset (I × F)}
    (hA : A ∈ transversalHost (I := I) (F := F) r) :
    shiftVertices b A ∈ transversalHost (I := I) (F := F) r := by
  classical
  apply mem_transversalHost.mpr
  constructor
  · rw [shiftVertices, Finset.card_image_iff.mpr (shiftVertex_injective b).injOn,
      (mem_transversalHost.mp hA).1]
  · intro z hz w hw hfst
    obtain ⟨z', hz', hzz⟩ := Finset.mem_image.mp hz
    obtain ⟨w', hw', hww⟩ := Finset.mem_image.mp hw
    have hparts : z'.1 = w'.1 := by
      have : (shiftVertex b z').1 = (shiftVertex b w').1 := by
        rw [hzz, hww]
        exact hfst
      simpa [shiftVertex] using this
    have hzw : z' = w' := (mem_transversalHost.mp hA).2 hz' hw' hparts
    exact hzz.symm.trans ((congrArg (shiftVertex b) hzw).trans hww)

/-- Affine translates of the polynomial function family. -/
def shiftedPolynomialFunctions (y b : I → F) (r : ℕ) : Finset (I → F) :=
  (polynomialFunctions y r).image fun f i ↦ b i + f i

def shiftedPolynomialBlocks (y b : I → F) (r : ℕ) :
    Finset (Finset (I × F)) :=
  (shiftedPolynomialFunctions y b r).image graph

theorem existsUnique_shiftedPolynomialFunction
    {y : I → F} (hy : Function.Injective y) (b : I → F)
    {r : ℕ} {A : Finset (I × F)}
    (hA : A ∈ transversalHost (I := I) (F := F) r) :
    ∃! g : I → F, g ∈ shiftedPolynomialFunctions y b r ∧ A ⊆ graph g := by
  classical
  let A' := shiftVertices b A
  have hA' : A' ∈ transversalHost (I := I) (F := F) r :=
    shiftVertices_mem_transversalHost hA
  obtain ⟨f, hf, hfunique⟩ := existsUnique_polynomialFunction hy hA'
  let g : I → F := fun i ↦ b i + f i
  have hgmem : g ∈ shiftedPolynomialFunctions y b r :=
    Finset.mem_image.mpr ⟨f, hf.1, rfl⟩
  have hAg : A ⊆ graph g := by
    intro z hz
    rcases z with ⟨i, x⟩
    have hshift : (i, x - b i) ∈ A' := by
      rw [mem_shiftVertices_iff]
      simpa only [sub_add_cancel]
    have hfg := mem_graph.mp (hf.2 hshift)
    rw [mem_graph]
    change x = b i + f i
    rw [← hfg]
    ring
  refine ⟨g, ⟨hgmem, hAg⟩, ?_⟩
  intro g' hg'
  obtain ⟨f', hf'mem, hf'g⟩ := Finset.mem_image.mp hg'.1
  have hA'f' : A' ⊆ graph f' := by
    intro z hz
    rcases z with ⟨i, x⟩
    have horig : (i, x + b i) ∈ A := mem_shiftVertices_iff.mp hz
    have hgraph := hg'.2 horig
    have hval : x + b i = g' i := mem_graph.mp hgraph
    rw [mem_graph]
    have hgf : g' i = b i + f' i := by
      exact congrFun hf'g i |>.symm
    rw [hgf] at hval
    exact add_left_cancel (by simpa [add_comm] using hval)
  have hff' : f' = f := hfunique f' ⟨hf'mem, hA'f'⟩
  funext i
  change g' i = b i + f i
  rw [← hff']
  exact congrFun hf'g i |>.symm

/-- Every affine translate is a second decomposition of the same
transversal host. -/
theorem shiftedPolynomialBlocks_decompose
    {y : I → F} (hy : Function.Injective y) (b : I → F) (r : ℕ) :
    IsUniformDecomposition (transversalHost (I := I) (F := F) r)
      (shiftedPolynomialBlocks y b r) (Fintype.card I) r := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hB
    exact card_graph g
  · intro B hB A hA
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hB
    have hAsub : A ⊆ graph g := (Finset.mem_powersetCard.mp hA).1
    have hAcard : A.card = r := (Finset.mem_powersetCard.mp hA).2
    apply mem_transversalHost.mpr
    refine ⟨hAcard, ?_⟩
    intro z hz w hw hfst
    rcases z with ⟨i, x⟩
    rcases w with ⟨j, t⟩
    simp only at hfst
    subst j
    have hzx := mem_graph.mp (hAsub hz)
    have hwt := mem_graph.mp (hAsub hw)
    simp only [Prod.mk.injEq, true_and]
    exact hzx.trans hwt.symm
  · intro A hA
    obtain ⟨g, hg, hgunique⟩ := existsUnique_shiftedPolynomialFunction hy b hA
    have heq :
        (shiftedPolynomialBlocks y b r).filter (fun B ↦ A ⊆ B) = {graph g} := by
      ext B
      constructor
      · intro hB
        have hm := Finset.mem_filter.mp hB
        obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hm.1
        have hgg' : g' = g := hgunique g' ⟨hg', hm.2⟩
        simp [hgg']
      · intro hB
        have hBg : B = graph g := Finset.mem_singleton.mp hB
        subst B
        exact Finset.mem_filter.mpr ⟨
          Finset.mem_image.mpr ⟨g, hg.1, rfl⟩, hg.2⟩
    rw [heq]
    simp

/-! ### A distance-refined shift

The zero/one shift used in the paper is enough for the trace-isolation
argument.  For later collision bookkeeping it is convenient to use the
standard Reed--Solomon refinement: evaluate the degree-`r` polynomial
vanishing on the first `r` nodes.  Its difference from any polynomial of
degree less than `r` has at most `r` roots. -/

/-- The common `r`-edge supported on the first `r` parts. -/
def zeroPrefixEdge (q r : ℕ) : Finset (Fin q × F) :=
  ((Finset.univ : Finset (Fin q)).filter fun i ↦ i.val < r).image
    fun i ↦ (i, 0)

/-- The monic polynomial whose roots are the first `r` interpolation
nodes. -/
def prefixPolynomial {q : ℕ} (y : Fin q → F) (r : ℕ) : F[X] :=
  ∏ j ∈ (Finset.univ : Finset (Fin q)).filter (fun j ↦ j.val < r),
    (Polynomial.X - Polynomial.C (y j))

/-- Evaluation of `prefixPolynomial` on the interpolation nodes. -/
def prefixShift {q : ℕ} (y : Fin q → F) (r : ℕ) : Fin q → F :=
  fun i ↦ (prefixPolynomial y r).eval (y i)

omit [Fintype F] [DecidableEq F] in
theorem prefixPolynomial_natDegree {q r : ℕ} (y : Fin q → F)
    (hrq : r ≤ q) : (prefixPolynomial y r).natDegree = r := by
  rw [prefixPolynomial, Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    simpa [Nat.min_eq_right hrq] using
      (Fin.card_filter_val_lt (n := q) (m := r))
  · intro i hi
    exact Polynomial.X_sub_C_ne_zero _

omit [Fintype F] [DecidableEq F] in
theorem prefixShift_eq_zero_iff {q r : ℕ} {y : Fin q → F}
    (hy : Function.Injective y) (i : Fin q) :
    prefixShift y r i = 0 ↔ i.val < r := by
  simp [prefixShift, prefixPolynomial, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff, sub_eq_zero, hy.eq_iff]

/-- A degree-less-than-`r` polynomial graph agrees with the refined shift
on at most `r` nodes. -/
theorem graph_inter_prefixShift_card_le {q r : ℕ} {y : Fin q → F}
    (hy : Function.Injective y) (hrq : r ≤ q)
    {f : Fin q → F} (hf : f ∈ polynomialFunctions y r) :
    (graph f ∩ graph (prefixShift y r)).card ≤ r := by
  rw [polynomialFunctions] at hf
  obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hf
  let P : F[X] := Polynomial.ofFn r u
  let V : F[X] := prefixPolynomial y r
  let A := graph (fun i ↦ P.eval (y i)) ∩ graph (prefixShift y r)
  let I := A.image Prod.fst
  let Y := I.image y
  have hfst : Set.InjOn Prod.fst (↑A : Set (Fin q × F)) := by
    intro z hz w hw hzw
    rcases z with ⟨i, x⟩
    rcases w with ⟨j, t⟩
    simp only at hzw
    subst j
    have hx := mem_graph.mp (Finset.mem_inter.mp hz).1
    have ht := mem_graph.mp (Finset.mem_inter.mp hw).1
    simp only [Prod.mk.injEq, true_and]
    exact hx.trans ht.symm
  have hcardI : I.card = A.card :=
    Finset.card_image_iff.mpr hfst
  have hcardY : Y.card = I.card :=
    Finset.card_image_iff.mpr hy.injOn
  have hroot : Y ⊆ (V - P).roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    rcases z with ⟨j, t⟩
    simp only at hzi
    subst j
    have hPval := mem_graph.mp (Finset.mem_inter.mp hz).1
    have hVval := mem_graph.mp (Finset.mem_inter.mp hz).2
    simp only [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots']
    refine ⟨?_, ?_⟩
    · intro hzero
      have hdeg : V.natDegree = r := prefixPolynomial_natDegree y hrq
      have hVP : V = P := sub_eq_zero.mp hzero
      rw [hVP] at hdeg
      by_cases hr0 : r = 0
      · have hPzero : P = 0 := by
          apply Polynomial.degree_eq_bot.mp
          apply Nat.WithBot.lt_zero_iff.mp
          simpa [hr0, P] using (Polynomial.ofFn_degree_lt u)
        have hVne : V ≠ 0 := by
          dsimp [V, prefixPolynomial]
          exact Finset.prod_ne_zero_iff.mpr fun i hi ↦
            Polynomial.X_sub_C_ne_zero _
        exact hVne (hVP.trans hPzero)
      · have hPlt : P.natDegree < r := by
          by_cases hP : P = 0
          · simp [hP, Nat.pos_of_ne_zero hr0]
          · exact (Polynomial.natDegree_lt_iff_degree_lt hP).2
              (Polynomial.ofFn_degree_lt u)
        omega
    · change (V - P).eval (y i) = 0
      rw [Polynomial.eval_sub]
      apply sub_eq_zero.mpr
      change prefixShift y r i = P.eval (y i)
      exact hVval.symm.trans hPval
  have hPdegree : P.natDegree ≤ r := by
    by_cases hP : P = 0
    · simp [hP]
    · exact ((Polynomial.natDegree_lt_iff_degree_lt hP).2
        (Polynomial.ofFn_degree_lt u)).le
  have hdiffDegree : (V - P).natDegree ≤ r := by
    exact (Polynomial.natDegree_sub_le V P).trans
      (max_le (prefixPolynomial_natDegree y hrq).le hPdegree)
  change A.card ≤ r
  rw [← hcardI, ← hcardY]
  exact (Finset.card_le_card hroot).trans
    ((Multiset.toFinset_card_le (V - P).roots).trans
      ((Polynomial.card_roots' (V - P)).trans hdiffDegree))

theorem prefixShift_graph_mem_shiftedPolynomialBlocks
    {q : ℕ} (y : Fin q → F) (r : ℕ) :
    graph (prefixShift y r) ∈ shiftedPolynomialBlocks y (prefixShift y r) r := by
  apply Finset.mem_image.mpr
  refine ⟨prefixShift y r, ?_, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨fun _ ↦ (0 : F), ?_, ?_⟩
  · rw [polynomialFunctions]
    apply Finset.mem_image.mpr
    refine ⟨fun _ ↦ (0 : F), Finset.mem_univ _, ?_⟩
    funext i
    change (Polynomial.ofFn r (0 : Fin r → F)).eval (y i) = 0
    rw [Polynomial.ofFn_zero]
    simp
  funext i
  simp

omit [Fintype F] in
theorem zero_graph_inter_prefixShift {q r : ℕ} {y : Fin q → F}
    (hy : Function.Injective y) :
    graph (fun _ : Fin q ↦ (0 : F)) ∩ graph (prefixShift y r) =
      zeroPrefixEdge (F := F) q r := by
  ext z
  rcases z with ⟨i, x⟩
  simp only [Finset.mem_inter, mem_graph]
  simp [zeroPrefixEdge, ← prefixShift_eq_zero_iff hy i, eq_comm]
  constructor <;> aesop

/-- The step vector used for the two designated cliques of the base
exchange trade: it is zero in the first `r` parts and one afterwards. -/
def stepShift {q : ℕ} (r : ℕ) : Fin q → F :=
  fun i ↦ if i.val < r then 0 else 1

theorem zero_function_mem_polynomialFunctions
    {q : ℕ} (y : Fin q → F) (r : ℕ) :
    (fun _ ↦ (0 : F)) ∈ polynomialFunctions y r := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨fun _ ↦ (0 : F), Finset.mem_univ _, ?_⟩
  funext i
  change (Polynomial.ofFn r (0 : Fin r → F)).eval (y i) = 0
  rw [Polynomial.ofFn_zero]
  simp

theorem zero_graph_mem_polynomialBlocks
    {q : ℕ} (y : Fin q → F) (r : ℕ) :
    graph (fun _ ↦ (0 : F)) ∈ polynomialBlocks y r := by
  classical
  exact Finset.mem_image.mpr
    ⟨fun _ ↦ (0 : F), zero_function_mem_polynomialFunctions y r, rfl⟩

theorem step_graph_mem_shiftedPolynomialBlocks
    {q : ℕ} (y : Fin q → F) (r : ℕ) :
    graph (stepShift (F := F) r) ∈
      shiftedPolynomialBlocks y (stepShift (F := F) r) r := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨stepShift (F := F) r, ?_, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨fun _ ↦ (0 : F), zero_function_mem_polynomialFunctions y r, ?_⟩
  funext i
  simp

omit [Fintype F] in
theorem zero_graph_inter_step_graph {q r : ℕ} :
    graph (fun _ : Fin q ↦ (0 : F)) ∩ graph (stepShift (F := F) r) =
      zeroPrefixEdge (F := F) q r := by
  classical
  ext z
  rcases z with ⟨i, x⟩
  by_cases hir : i.val < r
  · simp [stepShift, zeroPrefixEdge, graph, hir]
  · constructor
    · intro hz
      have hx0 : x = 0 := by
        simpa only [mem_graph] using (Finset.mem_inter.mp hz).1
      have hx1 : x = 1 := by
        have hm := (Finset.mem_inter.mp hz).2
        rw [mem_graph] at hm
        simpa [stepShift, hir] using hm
      exact (zero_ne_one (hx0.symm.trans hx1)).elim
    · intro hz
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hz
      have hjr : j.val < r := (Finset.mem_filter.mp hj).2
      have hji : j = i := congrArg Prod.fst hjx
      exact (hir (hji ▸ hjr)).elim

omit [Fintype F] in
@[simp] theorem card_zeroPrefixEdge {q r : ℕ} (hrq : r ≤ q) :
    (zeroPrefixEdge (F := F) q r).card = r := by
  classical
  rw [zeroPrefixEdge, Finset.card_image_iff.mpr]
  · simpa [Nat.min_eq_right hrq] using (Fin.card_filter_val_lt (n := q) (m := r))
  · intro i _ j _ hij
    exact congrArg Prod.fst hij

/-- The two base decompositions contain designated cliques whose vertex
intersection is exactly their common `r`-edge. -/
theorem polynomial_stepShift_designated
    {q r : ℕ} (y : Fin q → F) (hrq : r ≤ q) :
    ∃ Qplus ∈ polynomialBlocks y r,
      ∃ Qminus ∈ shiftedPolynomialBlocks y (stepShift (F := F) r) r,
        Qplus ∩ Qminus = zeroPrefixEdge (F := F) q r ∧
          (Qplus ∩ Qminus).card = r := by
  refine ⟨graph (fun _ ↦ (0 : F)), zero_graph_mem_polynomialBlocks y r,
    graph (stepShift (F := F) r), step_graph_mem_shiftedPolynomialBlocks y r,
    zero_graph_inter_step_graph, ?_⟩
  rw [zero_graph_inter_step_graph, card_zeroPrefixEdge hrq]

/-- The unshifted and shifted polynomial graph families are the two sides
of a finite-field clique trade. -/
theorem polynomial_shift_trade
    {y : I → F} (hy : Function.Injective y) (b : I → F) (r : ℕ) :
    IsUniformTrade (polynomialBlocks y r) (shiftedPolynomialBlocks y b r)
      (Fintype.card I) r := by
  exact ⟨transversalHost r, polynomialBlocks_decompose hy r,
    shiftedPolynomialBlocks_decompose hy b r⟩

section ZMod

/-- The first `k` residue classes in `ZMod p`. -/
def zmodNodes (k p : ℕ) : Fin k → ZMod p :=
  fun i ↦ (i.val : ZMod p)

theorem zmodNodes_injective {k p : ℕ} (hkp : k ≤ p) :
    Function.Injective (zmodNodes k p) := by
  intro i j hij
  apply Fin.ext
  change (i.val : ZMod p) = (j.val : ZMod p) at hij
  have hval := congrArg ZMod.val hij
  rw [ZMod.val_natCast_of_lt (i.isLt.trans_le hkp),
    ZMod.val_natCast_of_lt (j.isLt.trans_le hkp)] at hval
  exact hval

/-- Prime-field instance of the polynomial trade.  Bertrand's postulate
supplies such a prime with `k < p ≤ 2k`. -/
theorem zmod_polynomial_shift_trade (p k r : ℕ) [Fact p.Prime]
    (hkp : k ≤ p) (b : Fin k → ZMod p) :
    IsUniformTrade (polynomialBlocks (zmodNodes k p) r)
      (shiftedPolynomialBlocks (zmodNodes k p) b r) k r := by
  simpa using polynomial_shift_trade
    (zmodNodes_injective hkp) b r

/-- Complete prime-field base exchange: the two decompositions are a
trade and their designated zero/step cliques meet in exactly one
`r`-edge. -/
theorem zmod_base_exchange (p q r : ℕ) [Fact p.Prime]
    (hqp : q ≤ p) (hrq : r ≤ q) :
    IsUniformTrade (polynomialBlocks (zmodNodes q p) r)
        (shiftedPolynomialBlocks (zmodNodes q p)
          (stepShift (F := ZMod p) r) r) q r ∧
      ∃ Qplus ∈ polynomialBlocks (zmodNodes q p) r,
        ∃ Qminus ∈ shiftedPolynomialBlocks (zmodNodes q p)
            (stepShift (F := ZMod p) r) r,
          Qplus ∩ Qminus = zeroPrefixEdge (F := ZMod p) q r ∧
            (Qplus ∩ Qminus).card = r := by
  exact ⟨zmod_polynomial_shift_trade p q r hqp
      (stepShift (F := ZMod p) r),
    polynomial_stepShift_designated (zmodNodes q p) hrq⟩

/-- The base-exchange conclusion with the prime proof made explicit, so
it can occur underneath an existential quantifier over `p`. -/
def HasZModBaseExchange (p q r : ℕ) (hp : p.Prime) : Prop :=
  let _fact : Fact p.Prime := ⟨hp⟩
  IsUniformTrade (polynomialBlocks (zmodNodes q p) r)
      (shiftedPolynomialBlocks (zmodNodes q p)
        (stepShift (F := ZMod p) r) r) q r ∧
    ∃ Qplus ∈ polynomialBlocks (zmodNodes q p) r,
      ∃ Qminus ∈ shiftedPolynomialBlocks (zmodNodes q p)
          (stepShift (F := ZMod p) r) r,
        Qplus ∩ Qminus = zeroPrefixEdge (F := ZMod p) q r ∧
          (Qplus ∩ Qminus).card = r

/-- Bertrand's postulate supplies a field of order between `q` and `2q`,
so the base exchange exists with the quantitative vertex range used in
the short proof. -/
theorem exists_zmod_base_exchange (q r : ℕ) (hq : 0 < q) (hrq : r ≤ q) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      q < p ∧ p ≤ 2 * q ∧ HasZModBaseExchange p q r hp := by
  obtain ⟨p, hp, hqp, hpq⟩ :=
    Nat.exists_prime_lt_and_le_two_mul q hq.ne'
  refine ⟨p, hp, hqp, hpq, ?_⟩
  let _fact : Fact p.Prime := ⟨hp⟩
  simpa [HasZModBaseExchange] using zmod_base_exchange p q r hqp.le hrq

end ZMod

end

end Erdos722.Transversal

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
import ErdosProblems.Erdos722.ExchangePattern
import ErdosProblems.Erdos722.RootedFamilyAsymptotic
import Mathlib

/-!
# Sparse rooted copies of the full exchange

This file specializes the cardinality-generic rooted embedding theorem to
the finite full-exchange gadget.  Each prescribed `k`-set is the exact image
of the positive root clique; all non-root gadget edges avoid the fixed
forbidden `r`-graph, are separated between distinct roots, and obey the final
codimension-one load cap.
-/

namespace Erdos722.ExchangeEmbedding

open Finset Filter
open Erdos722.Reserve
open Erdos722.Transversal
open Erdos722.Exchange
open Erdos722.RootedEmbedding
open Erdos722.ExchangePattern
open Erdos722.RootedFamilyEmbedding
open Erdos722.RootedFamilyMultiEmbedding
open Erdos722.RootedFamilyAsymptotic
open Erdos722.LocalDecoderAsymptotic

noncomputable section

def fullExchangeData {k r : ℕ} (hrk : r < k) :
    RelabeledFullExchange k r :=
  Classical.choose (exists_relabeledFullExchange_with_trace_and_disjoint hrk)

/-- The special negative clique produced in the final gluing round of the
canonical exchange. -/
def fullExchangeRootEdge {k r : ℕ} (hrk : r < k) : RootEdge k r :=
  Classical.choose
    (Classical.choose_spec
      (exists_relabeledFullExchange_with_trace_and_disjoint hrk))

theorem fullExchangeData_trace_and_bound {k r : ℕ} (hrk : r < k) :
    (fullExchangeData hrk).SpecialTraceIsolated
        (fullExchangeRootEdge hrk) ∧
      (fullExchangeData hrk).SpecialPositiveInterBounded
        (fullExchangeRootEdge hrk) :=
  let h := Classical.choose_spec
    (Classical.choose_spec
      (exists_relabeledFullExchange_with_trace_and_disjoint hrk))
  ⟨h.1, h.2.1⟩

theorem fullExchangeData_disjoint {k r : ℕ} (hrk : r < k) :
    Disjoint (fullExchangeData hrk).positive
      (fullExchangeData hrk).negative :=
  (Classical.choose_spec
    (Classical.choose_spec
      (exists_relabeledFullExchange_with_trace_and_disjoint hrk))).2.2

theorem fullExchangeData_trace {k r : ℕ} (hrk : r < k) :
    (fullExchangeData hrk).SpecialTraceIsolated
      (fullExchangeRootEdge hrk) :=
  (fullExchangeData_trace_and_bound hrk).1

theorem fullExchangeData_positive_inter_special {k r : ℕ}
    (hrk : r < k) :
    (fullExchangeData hrk).SpecialPositiveInterBounded
      (fullExchangeRootEdge hrk) :=
  (fullExchangeData_trace_and_bound hrk).2

@[simp] theorem fullExchangeData_root_card {k r : ℕ} (hrk : r < k) :
    (fullExchangeData hrk).pattern.root.card = k :=
  (fullExchangeData hrk).root_card

theorem fullExchangeData_root_nonempty {k r : ℕ} (hr : 0 < r)
    (hrk : r < k) : (fullExchangeData hrk).pattern.root.Nonempty :=
  (fullExchangeData hrk).root_nonempty (by omega)

theorem fullExchangeData_root_card_lt_v {k r : ℕ} (hrk : r < k) :
    (fullExchangeData hrk).pattern.root.card < (fullExchangeData hrk).v :=
  (fullExchangeData hrk).root_card_lt_v hrk

/-- Simultaneous sparse copies of one fixed full exchange, rooted at an
arbitrary power-bounded family of `k`-sets. -/
theorem eventually_exists_boundedFullExchangeEmbeddings
    (hr : 0 < r) (hrk : r < k) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots forbidden : Finset (Finset (Fin n))),
      (∀ Q ∈ roots, Q.card = k) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedRootedFamilyEmbeddings
        (fullExchangeData hrk).pattern roots forbidden
        (decoderPathCap (fullExchangeData hrk).v r d n)) := by
  let E := fullExchangeData hrk
  have hmain :=
    eventually_exists_boundedRootedFamilyEmbeddings_of_power_bound
      E.pattern hr (E.root_nonempty (by omega))
        (E.root_card_lt_v hrk) (by simpa [E] using hrk.le) hd
  filter_upwards [hmain] with n hn
  intro roots forbidden hroots hforbidden hrootDegree hforbiddenDegree
  apply hn roots forbidden
  · intro Q hQ
    simpa [E] using hroots Q hQ
  · exact hforbidden
  · exact hrootDegree
  · exact hforbiddenDegree

/-- Simultaneous sparse copies of a fixed positive number of full exchanges
at every prescribed `k`-set. -/
theorem eventually_exists_boundedMultiFullExchangeEmbeddings_twoScale
    {dInput dPath : ℕ}
    (hr : 0 < r) (hrk : r < k)
    (hdInput : 0 < dInput) (hdPath : 0 < dPath)
    (hgap : dInput < 2 * dPath)
    (multiplicity : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots forbidden : Finset (Finset (Fin n))),
      (∀ Q ∈ roots, Q.card = k) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ dInput ≤ n ^ (dInput - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ dInput ≤
          n ^ (dInput - 1)) →
      Nonempty (BoundedMultiRootedFamilyEmbeddings
        (fullExchangeData hrk).pattern roots forbidden multiplicity
        (scaledDecoderPathCap multiplicity
          (fullExchangeData hrk).v r dPath n)) := by
  let E := fullExchangeData hrk
  have hmain :=
    eventually_exists_boundedMultiRootedFamilyEmbeddings_of_two_power_bounds
      E.pattern hr (E.root_nonempty (by omega))
        (E.root_card_lt_v hrk) (by simpa [E] using hrk.le)
        hdInput hdPath hgap multiplicity
  filter_upwards [hmain] with n hn
  intro roots forbidden hroots hforbidden hrootDegree hforbiddenDegree
  apply hn roots forbidden
  · intro Q hQ
    simpa [E] using hroots Q hQ
  · exact hforbidden
  · exact hrootDegree
  · exact hforbiddenDegree

/-- Equal-denominator compatibility wrapper. -/
theorem eventually_exists_boundedMultiFullExchangeEmbeddings
    (hr : 0 < r) (hrk : r < k) (hd : 0 < d)
    (multiplicity : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (roots forbidden : Finset (Finset (Fin n))),
      (∀ Q ∈ roots, Q.card = k) →
      (∀ e ∈ forbidden, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree roots J) ^ d ≤ n ^ (d - 1)) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree forbidden J) ^ d ≤ n ^ (d - 1)) →
      Nonempty (BoundedMultiRootedFamilyEmbeddings
        (fullExchangeData hrk).pattern roots forbidden multiplicity
        (scaledDecoderPathCap multiplicity
          (fullExchangeData hrk).v r d n)) := by
  simpa using
    (eventually_exists_boundedMultiFullExchangeEmbeddings_twoScale
      hr hrk hd hd (by omega) multiplicity)

def mappedPositive (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    Finset (Finset (Fin n)) :=
  mapFamily φ E.positive

def mappedNegative (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    Finset (Finset (Fin n)) :=
  mapFamily φ E.negative

theorem mappedPositive_disjoint_mappedNegative
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (hdisjoint : Disjoint E.positive E.negative) :
    Disjoint (mappedPositive E φ) (mappedNegative E φ) := by
  simpa [mappedPositive, mappedNegative, mapFamily] using
    (Finset.disjoint_map (Finset.mapEmbedding φ).toEmbedding).2 hdisjoint

def mappedHost (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    Finset (Finset (Fin n)) :=
  mapFamily φ E.pattern.edges

def mappedSpecial (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) (e : RootEdge k r) : Finset (Fin n) :=
  mapEdge φ (E.special e)

/-- The negative blocks meeting the distinguished root in an entire
`r`-edge.  These are exactly the labelled special blocks of the exchange. -/
def mappedNearNegative (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (RootEdge k r)).image fun e ↦
    mappedSpecial E φ e

/-- The remaining negative blocks of one rooted exchange. -/
def mappedFarNegative (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) : Finset (Finset (Fin n)) :=
  mappedNegative E φ \ mappedNearNegative E φ

theorem mappedPositive_decomp (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) :
    IsUniformDecomposition (mappedHost E φ) (mappedPositive E φ) k r := by
  exact E.positive_decomp.map φ

theorem mappedNegative_decomp (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) :
    IsUniformDecomposition (mappedHost E φ) (mappedNegative E φ) k r := by
  exact E.negative_decomp.map φ

theorem mappedRoot_mem_mappedPositive (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) :
    mapEdge φ E.pattern.root ∈ mappedPositive E φ := by
  apply mem_mapFamily.mpr
  refine ⟨E.pattern.root, ?_, rfl⟩
  simpa [E.root_eq] using E.root_mem

theorem mappedSpecial_mem_mappedNegative
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (e : RootEdge k r) :
    mappedSpecial E φ e ∈ mappedNegative E φ := by
  apply mem_mapFamily.mpr
  exact ⟨E.special e, E.special_mem e, rfl⟩

theorem mappedNearNegative_subset_mappedNegative
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    mappedNearNegative E φ ⊆ mappedNegative E φ := by
  intro B hB
  obtain ⟨e, _he, rfl⟩ := Finset.mem_image.mp hB
  exact mappedSpecial_mem_mappedNegative E φ e

theorem mappedFarNegative_decomp
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    IsUniformDecomposition
      (mappedHost E φ \ (mappedNearNegative E φ).biUnion
        (fun B ↦ B.powersetCard r))
      (mappedFarNegative E φ) k r := by
  have huniform : ∀ g ∈ mappedHost E φ, g.card = r := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := mem_mapFamily.mp hg
    simpa using E.pattern.uniform g₀ hg₀
  exact (mappedNegative_decomp E φ).sdiff_blocks huniform
    (mappedNearNegative_subset_mappedNegative E φ)

@[simp] theorem mappedSpecial_card
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (e : RootEdge k r) : (mappedSpecial E φ e).card = k := by
  simp [mappedSpecial,
    E.negative_decomp.1 (E.special e) (E.special_mem e)]

theorem mappedSpecial_inter_mappedRoot
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (e : RootEdge k r) :
    mappedSpecial E φ e ∩ mapEdge φ E.pattern.root =
      mapEdge (E.rootEmbedding.trans φ) e.1 := by
  unfold mappedSpecial mapEdge
  rw [← Finset.map_inter, E.root_eq, E.special_inter_root e]
  exact (mappedRootEdge_trans E.rootEmbedding φ e.1).symm

theorem mappedPositive_inter_mappedSpecial_card_le
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    {Q : Finset (Fin n)} (hQ : Q ∈ mappedPositive E φ)
    (e : RootEdge k r) :
    (Q ∩ mappedSpecial E φ e).card ≤ r := by
  obtain ⟨Q₀, hQ₀, rfl⟩ := mem_mapFamily.mp hQ
  simpa [mappedSpecial, mapEdge, ← Finset.map_inter] using
    E.positive_inter_special_card_le e Q₀ hQ₀

/-- A non-root positive block can meet an entire special edge in at most one
of the labelled special cliques.  This is the mapped form of the global
trace-separation invariant from Lemma 3.1(ii). -/
theorem mappedPositive_special_unique
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    {Q : Finset (Fin n)} (hQ : Q ∈ mappedPositive E φ)
    (hQroot : Q ≠ mapEdge φ E.pattern.root)
    (e e' : RootEdge k r)
    (he : ∃ g ∈ Q.powersetCard r,
      g ∈ (mappedSpecial E φ e).powersetCard r)
    (he' : ∃ g ∈ Q.powersetCard r,
      g ∈ (mappedSpecial E φ e').powersetCard r) :
    e = e' := by
  classical
  obtain ⟨Q₀, hQ₀, hQmap⟩ := mem_mapFamily.mp hQ
  subst Q
  have hQ₀root : Q₀ ≠ E.pattern.root := by
    intro hEq
    apply hQroot
    simp [hEq, mapEdge]
  have pullEdge (a : RootEdge k r)
      (ha : ∃ g ∈ (Q₀.map φ).powersetCard r,
        g ∈ (mappedSpecial E φ a).powersetCard r) :
      ∃ g₀ ∈ Q₀.powersetCard r,
        g₀ ∈ (E.special a).powersetCard r := by
    obtain ⟨g, hgQ, hgS⟩ := ha
    let g₀ := g.preimage φ φ.injective.injOn
    have hgRange : g ⊆ Q₀.map φ :=
      (Finset.mem_powersetCard.mp hgQ).1
    have hg₀map : g₀.map φ = g := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
        rw [← hyx]
        exact Finset.mem_preimage.mp hy
      · intro hx
        obtain ⟨y, hyQ, hyx⟩ := Finset.mem_map.mp (hgRange hx)
        apply Finset.mem_map.mpr
        refine ⟨y, ?_, hyx⟩
        apply Finset.mem_preimage.mpr
        simpa [hyx] using hx
    have hg₀Q : g₀ ⊆ Q₀ := by
      apply Finset.map_subset_map.mp
      rw [hg₀map]
      exact hgRange
    have hg₀S : g₀ ⊆ E.special a := by
      apply Finset.map_subset_map.mp
      rw [hg₀map]
      simpa [mappedSpecial, mapEdge] using
        (Finset.mem_powersetCard.mp hgS).1
    have hg₀card : g₀.card = r := by
      rw [← Finset.card_map φ, hg₀map]
      exact (Finset.mem_powersetCard.mp hgQ).2
    exact ⟨g₀, Finset.mem_powersetCard.mpr ⟨hg₀Q, hg₀card⟩,
      Finset.mem_powersetCard.mpr ⟨hg₀S, hg₀card⟩⟩
  exact E.positive_special_unique Q₀ hQ₀
    (by simpa [E.root_eq] using hQ₀root) e e'
      (pullEdge e he) (pullEdge e' he')

/-- Every root edge is covered by its labelled near negative block. -/
theorem mappedRootBoundary_subset_mappedNearBoundary
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    (mapEdge φ E.pattern.root).powersetCard r ⊆
      (mappedNearNegative E φ).biUnion (fun B ↦ B.powersetCard r) := by
  intro g hg
  have hgData := Finset.mem_powersetCard.mp hg
  have hgMap : g ⊆
      (Finset.univ : Finset (Fin k)).map (E.rootEmbedding.trans φ) := by
    simpa [mapEdge, E.root_eq, mappedRoot, Finset.map_map] using hgData.1
  obtain ⟨e, heuniv, hemap⟩ := Finset.subset_map_iff.mp hgMap
  have hecard : e.card = r := by
    simpa [hemap] using hgData.2
  let eroot : RootEdge k r :=
    ⟨e, Finset.mem_powersetCard.mpr ⟨heuniv, hecard⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨mappedSpecial E φ eroot, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨eroot, Finset.mem_univ _, rfl⟩
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hgData.2⟩
    have hinter := mappedSpecial_inter_mappedRoot E φ eroot
    have hmap : mapEdge (E.rootEmbedding.trans φ) e = g := by
      simpa [mapEdge] using hemap.symm
    have hgInter : g ⊆
        mappedSpecial E φ eroot ∩ mapEdge φ E.pattern.root := by
      rw [hinter]
      simpa [eroot, hmap]
    exact hgInter.trans Finset.inter_subset_left

theorem mapped_incidence_eq (E : RelabeledFullExchange k r)
    (φ : Fin E.v ↪ Fin n) {g : Finset (Fin n)} (hg : g.card = r) :
    incidenceCount (mappedPositive E φ) g =
      incidenceCount (mappedNegative E φ) g := by
  rw [(mappedPositive_decomp E φ).incidenceCount_eq_indicator hg,
    (mappedNegative_decomp E φ).incidenceCount_eq_indicator hg]

lemma incidenceCount_erase_of_mem
    {family : Finset (Finset (Fin n))} {Q g : Finset (Fin n)}
    (hQ : Q ∈ family) :
    incidenceCount (family.erase Q) g =
      incidenceCount family g - if g ⊆ Q then 1 else 0 := by
  classical
  unfold incidenceCount
  by_cases hgQ : g ⊆ Q
  · rw [if_pos hgQ]
    have hQfilter : Q ∈ family.filter fun B ↦ g ⊆ B :=
      Finset.mem_filter.mpr ⟨hQ, hgQ⟩
    rw [Finset.filter_erase, Finset.card_erase_of_mem hQfilter]
  · rw [if_neg hgQ]
    have hQfilter : Q ∉ family.filter fun B ↦ g ⊆ B := by
      simp [hgQ]
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hQfilter, Nat.sub_zero]

/-- Removing the designated positive root and one isolated negative block
from the two equal decompositions gives the exact signed difference of the
two root cliques.  This is the algebraic two-root elimination move. -/
theorem mappedFullExchange_signed_root_sub_special
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (e : RootEdge k r) {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount
        ((mappedNegative E φ).erase (mappedSpecial E φ e)) g : ℤ) -
      (incidenceCount
        ((mappedPositive E φ).erase (mapEdge φ E.pattern.root)) g : ℤ) =
      (if g ⊆ mapEdge φ E.pattern.root then (1 : ℤ) else 0) -
        (if g ⊆ mappedSpecial E φ e then (1 : ℤ) else 0) := by
  have hnegErase := incidenceCount_erase_of_mem
    (g := g) (mappedSpecial_mem_mappedNegative E φ e)
  have hposErase := incidenceCount_erase_of_mem
    (g := g) (mappedRoot_mem_mappedPositive E φ)
  have heq := mapped_incidence_eq E φ hg
  by_cases hroot : g ⊆ mapEdge φ E.pattern.root
  · have hhost : g ∈ mappedHost E φ :=
      (mappedPositive_decomp E φ).2.1
        (mapEdge φ E.pattern.root) (mappedRoot_mem_mappedPositive E φ)
        (Finset.mem_powersetCard.mpr ⟨hroot, hg⟩)
    have hpos : incidenceCount (mappedPositive E φ) g = 1 := by
      simpa [hhost] using
        (mappedPositive_decomp E φ).incidenceCount_eq_indicator hg
    have hneg : incidenceCount (mappedNegative E φ) g = 1 := by omega
    by_cases hspecial : g ⊆ mappedSpecial E φ e
    · rw [hneg, if_pos hspecial] at hnegErase
      rw [hpos, if_pos hroot] at hposErase
      simp [hroot, hspecial]
      norm_num at hnegErase hposErase
      omega
    · rw [hneg, if_neg hspecial] at hnegErase
      rw [hpos, if_pos hroot] at hposErase
      simp [hroot, hspecial]
      norm_num at hnegErase hposErase
      omega
  · by_cases hspecial : g ⊆ mappedSpecial E φ e
    · have hhost : g ∈ mappedHost E φ :=
        (mappedNegative_decomp E φ).2.1
          (mappedSpecial E φ e) (mappedSpecial_mem_mappedNegative E φ e)
          (Finset.mem_powersetCard.mpr ⟨hspecial, hg⟩)
      have hneg : incidenceCount (mappedNegative E φ) g = 1 := by
        simpa [hhost] using
          (mappedNegative_decomp E φ).incidenceCount_eq_indicator hg
      have hpos : incidenceCount (mappedPositive E φ) g = 1 := by omega
      rw [hneg, if_pos hspecial] at hnegErase
      rw [hpos, if_neg hroot] at hposErase
      simp [hroot, hspecial]
      norm_num at hnegErase hposErase
      omega
    · rw [if_neg hspecial] at hnegErase
      rw [if_neg hroot] at hposErase
      simp [hroot, hspecial]
      simp at hnegErase hposErase
      omega

/-- One rooted full exchange represents the positive incidence vector of
its root clique as `mappedNegative - (mappedPositive \ {root})`. -/
theorem mappedFullExchange_signed_root
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount (mappedNegative E φ) g : ℤ) -
        (incidenceCount
          ((mappedPositive E φ).erase (mapEdge φ E.pattern.root)) g : ℤ) =
      if g ⊆ mapEdge φ E.pattern.root then 1 else 0 := by
  have herase := incidenceCount_erase_of_mem
    (g := g) (mappedRoot_mem_mappedPositive E φ)
  have heq := mapped_incidence_eq E φ hg
  by_cases hroot : g ⊆ mapEdge φ E.pattern.root
  · rw [if_pos hroot]
    have hhost : g ∈ mappedHost E φ :=
      (mappedPositive_decomp E φ).2.1
        (mapEdge φ E.pattern.root) (mappedRoot_mem_mappedPositive E φ)
        (Finset.mem_powersetCard.mpr ⟨hroot, hg⟩)
    have hpos : incidenceCount (mappedPositive E φ) g = 1 := by
      simpa [hhost] using
        (mappedPositive_decomp E φ).incidenceCount_eq_indicator hg
    have hneg : incidenceCount (mappedNegative E φ) g = 1 := by omega
    rw [hpos, if_pos hroot] at herase
    norm_num at herase
    rw [hneg, herase]
    norm_num
  · rw [if_neg hroot]
    rw [if_neg hroot] at herase
    simp at herase
    omega

theorem mappedHost_sdiff_root_eq_freeEdges
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    mappedHost E φ \ (mapEdge φ E.pattern.root).powersetCard r =
      imageFreeEdges E.pattern φ := by
  classical
  ext g
  constructor
  · intro hg
    have hgData := Finset.mem_sdiff.mp hg
    obtain ⟨e, he, heg⟩ := mem_mapFamily.mp hgData.1
    subst g
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    intro heroot
    apply hgData.2
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.map_subset_map.mpr heroot, ?_⟩
    simpa [mapEdge] using E.pattern.uniform e he
  · intro hg
    obtain ⟨e, he, heg⟩ := Finset.mem_image.mp hg
    subst g
    have heData := Finset.mem_filter.mp he
    apply Finset.mem_sdiff.mpr
    constructor
    · exact mem_mapFamily.mpr ⟨e, heData.1, rfl⟩
    · intro hrootEdge
      have hsubMap := (Finset.mem_powersetCard.mp hrootEdge).1
      exact heData.2 (Finset.map_subset_map.mp hsubMap)

/-- An edge of a mapped host is either contained in its prescribed root or
is one of the free edges charged to the rooted embedding. -/
theorem mem_mappedRootBoundary_or_imageFreeEdges
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    {g : Finset (Fin n)} (hgHost : g ∈ mappedHost E φ) :
    g ∈ (mapEdge φ E.pattern.root).powersetCard r ∨
      g ∈ imageFreeEdges E.pattern φ := by
  by_cases hgRoot : g ∈ (mapEdge φ E.pattern.root).powersetCard r
  · exact Or.inl hgRoot
  · exact Or.inr (by
      rw [← mappedHost_sdiff_root_eq_freeEdges E φ]
      exact Finset.mem_sdiff.mpr ⟨hgHost, hgRoot⟩)

/-- After removing all near special blocks, the residual negative host is
supported on free (non-root) edges. -/
theorem mappedFarHost_subset_freeEdges
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    mappedHost E φ \ (mappedNearNegative E φ).biUnion
        (fun B ↦ B.powersetCard r) ⊆
      imageFreeEdges E.pattern φ := by
  rw [← mappedHost_sdiff_root_eq_freeEdges E φ]
  intro g hg
  apply Finset.mem_sdiff.mpr
  refine ⟨(Finset.mem_sdiff.mp hg).1, ?_⟩
  intro hgRoot
  exact (Finset.mem_sdiff.mp hg).2
    (mappedRootBoundary_subset_mappedNearBoundary E φ hgRoot)

/-- Every edge of a far negative block is a free edge of the rooted copy. -/
theorem mappedFarNegative_edges_subset_freeEdges
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    {B : Finset (Fin n)} (hB : B ∈ mappedFarNegative E φ) :
    B.powersetCard r ⊆ imageFreeEdges E.pattern φ := by
  exact fun _g hg ↦ mappedFarHost_subset_freeEdges E φ
    ((mappedFarNegative_decomp E φ).2.1 B hB hg)

/-- Far negative blocks coming from distinct preallocated rooted copies have
edge-disjoint clique boundaries. -/
theorem mappedFarNegative_multi_edgeDisjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    {I I' : ↥roots × Fin multiplicity} (hII' : I ≠ I')
    {B B' : Finset (Fin n)}
    (hB : B ∈ mappedFarNegative E
      (S.embedding I.1.1 I.1.2 I.2))
    (hB' : B' ∈ mappedFarNegative E
      (S.embedding I'.1.1 I'.1.2 I'.2)) :
    Disjoint (B.powersetCard r) (B'.powersetCard r) := by
  apply Finset.disjoint_left.mpr
  intro g hgB hgB'
  have hgFree := mappedFarNegative_edges_subset_freeEdges E _ hB hgB
  have hgFree' := mappedFarNegative_edges_subset_freeEdges E _ hB' hgB'
  have hlabel : (I.1.1, (I.2 : ℕ)) ≠ (I'.1.1, (I'.2 : ℕ)) := by
    intro hEq
    apply hII'
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hEq)
    · exact Fin.ext (congrArg Prod.snd hEq)
  exact Finset.disjoint_left.mp
    (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
      hlabel) hgFree hgFree'

/-- Every edge of a near special block is either its unique root edge or a
free edge of that rooted copy. -/
theorem mappedSpecial_edge_eq_or_free
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (e : RootEdge k r) {g : Finset (Fin n)}
    (hg : g ∈ (mappedSpecial E φ e).powersetCard r) :
    g = mapEdge (E.rootEmbedding.trans φ) e.1 ∨
      g ∈ imageFreeEdges E.pattern φ := by
  have hgData := Finset.mem_powersetCard.mp hg
  by_cases hroot : g ⊆ mapEdge φ E.pattern.root
  · left
    have hsub : g ⊆ mapEdge (E.rootEmbedding.trans φ) e.1 := by
      have hinter := mappedSpecial_inter_mappedRoot E φ e
      rw [← hinter]
      exact fun x hx ↦ Finset.mem_inter.mpr ⟨hgData.1 hx, hroot hx⟩
    apply Finset.eq_of_subset_of_card_le hsub
    rw [card_mapEdge, RootEdge.card, hgData.2]
  · right
    rw [← mappedHost_sdiff_root_eq_freeEdges E φ]
    apply Finset.mem_sdiff.mpr
    refine ⟨(mappedNegative_decomp E φ).2.1
      (mappedSpecial E φ e) (mappedSpecial_mem_mappedNegative E φ e)
      hg, ?_⟩
    intro hgRoot
    exact hroot (Finset.mem_powersetCard.mp hgRoot).1

theorem mappedPositive_erase_decomp
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    IsUniformDecomposition (imageFreeEdges E.pattern φ)
      ((mappedPositive E φ).erase (mapEdge φ E.pattern.root)) k r := by
  have huniform : ∀ g ∈ mappedHost E φ, g.card = r := by
    intro g hg
    obtain ⟨e, he, rfl⟩ := mem_mapFamily.mp hg
    simpa using E.pattern.uniform e he
  have h := (mappedPositive_decomp E φ).erase huniform
    (mappedRoot_mem_mappedPositive E φ)
  simpa [mappedHost_sdiff_root_eq_freeEdges E φ] using h

/-- Erasing one designated negative special block leaves a decomposition of
the mapped host with precisely that block's clique deleted. -/
theorem mappedNegative_erase_special_decomp
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n)
    (e : RootEdge k r) :
    IsUniformDecomposition
      (mappedHost E φ \ (mappedSpecial E φ e).powersetCard r)
      ((mappedNegative E φ).erase (mappedSpecial E φ e)) k r := by
  have huniform : ∀ g ∈ mappedHost E φ, g.card = r := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := mem_mapFamily.mp hg
    simpa using E.pattern.uniform g₀ hg₀
  exact (mappedNegative_decomp E φ).erase huniform
    (mappedSpecial_mem_mappedNegative E φ e)

def splitFreeHost {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C) :
    Finset (Finset (Fin n)) :=
  roots.attach.biUnion fun Q ↦
    imageFreeEdges E.pattern (S.embedding Q.1 Q.2)

def splitNegativeBlocks {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C) :
    Finset (Finset (Fin n)) :=
  roots.attach.biUnion fun Q ↦
    (mappedPositive E (S.embedding Q.1 Q.2)).erase Q.1

def splitPositiveBlocks {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C) :
    Finset (Finset (Fin n)) :=
  roots.attach.biUnion fun Q ↦ mappedNegative E (S.embedding Q.1 Q.2)

theorem splitFreeHost_subset_freeUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C) :
    splitFreeHost S ⊆ S.freeUnion := by
  intro g hg
  obtain ⟨Q, hQ, hgQ⟩ := Finset.mem_biUnion.mp hg
  exact S.image_subset_freeUnion Q.1 Q.2 hgQ

theorem splitNegativeBlocks_decomp
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (hrk : r ≤ k) :
    IsUniformDecomposition (splitFreeHost S) (splitNegativeBlocks S) k r := by
  let host : ↥roots → Finset (Finset (Fin n)) := fun Q ↦
    imageFreeEdges E.pattern (S.embedding Q.1 Q.2)
  let blocks : ↥roots → Finset (Finset (Fin n)) := fun Q ↦
    (mappedPositive E (S.embedding Q.1 Q.2)).erase Q.1
  have hroot (Q : ↥roots) :
      mapEdge (S.embedding Q.1 Q.2) E.pattern.root = Q.1 :=
    S.root_image Q.1 Q.2
  have hdecomp : ∀ Q ∈ roots.attach,
      IsUniformDecomposition (host Q) (blocks Q) k r := by
    intro Q hQ
    dsimp [host, blocks]
    simpa [hroot Q] using mappedPositive_erase_decomp E
      (S.embedding Q.1 Q.2)
  have huniform : ∀ Q ∈ roots.attach, ∀ g ∈ host Q, g.card = r := by
    intro Q hQ g hg
    exact imageFreeEdges_uniform E.pattern (S.embedding Q.1 Q.2) hg
  have hpair : ∀ Q ∈ roots.attach, ∀ Q' ∈ roots.attach, Q ≠ Q' →
      Disjoint (host Q) (host Q') := by
    intro Q hQ Q' hQ' hne
    apply S.free_pairwise Q.1 Q.2 Q'.1 Q'.2
    intro hval
    apply hne
    exact Subtype.ext hval
  have h := IsUniformDecomposition.biUnion roots.attach host blocks
    hdecomp huniform hpair hrk
  simpa [splitFreeHost, splitNegativeBlocks, host, blocks] using h

theorem splitFreeHost_degree_le
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (J : Finset (Fin n)) (hJ : J.card = r - 1) :
    Reserve.localDegree (splitFreeHost S) J ≤ E.pattern.freeEdges.card * C := by
  exact (Finset.card_le_card (Finset.filter_subset_filter _
    (splitFreeHost_subset_freeUnion S))).trans (S.free_degree_le J hJ)

lemma exists_powersetCard_not_subset
    {B R : Finset (Fin n)} (hr : 0 < r) (hrB : r ≤ B.card)
    (hnot : ¬B ⊆ R) :
    ∃ g ∈ B.powersetCard r, ¬g ⊆ R := by
  classical
  obtain ⟨x, hxB, hxR⟩ := Finset.not_subset.mp hnot
  have hle : r - 1 ≤ (B.erase x).card := by
    rw [Finset.card_erase_of_mem hxB]
    omega
  obtain ⟨t, htB, htcard⟩ := Finset.exists_subset_card_eq hle
  let g := insert x t
  have hxt : x ∉ t := by
    intro hxt
    exact (Finset.mem_erase.mp (htB hxt)).1 rfl
  have hgB : g ⊆ B := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyt
    · exact hxB
    · exact Finset.mem_of_mem_erase (htB hyt)
  have hgcard : g.card = r := by
    simp [g, hxt, htcard, Nat.sub_add_cancel (by omega : 1 ≤ r)]
  refine ⟨g, Finset.mem_powersetCard.mpr ⟨hgB, hgcard⟩, ?_⟩
  intro hgR
  exact hxR (hgR (by simp [g]))

theorem mappedRoot_not_mem_mappedNegative
    (E : RelabeledFullExchange k r) (hrk : r < k)
    (φ : Fin E.v ↪ Fin n) :
    mapEdge φ E.pattern.root ∉ mappedNegative E φ := by
  intro hroot
  obtain ⟨B, hB, hmap⟩ := mem_mapFamily.mp hroot
  apply E.root_not_mem_negative hrk
  have hEq : B = E.pattern.root := by
    apply Finset.map_injective φ
    simpa [mapEdge] using hmap
  simpa [hEq] using hB

theorem exists_freeEdge_of_mem_mappedNegative
    (E : RelabeledFullExchange k r) (hr : 0 < r) (hrk : r < k)
    (φ : Fin E.v ↪ Fin n) {B : Finset (Fin n)}
    (hB : B ∈ mappedNegative E φ) :
    ∃ g ∈ B.powersetCard r, g ∈ imageFreeEdges E.pattern φ := by
  have hBcard : B.card = k := (mappedNegative_decomp E φ).1 B hB
  have hrootCard : (mapEdge φ E.pattern.root).card = k := by
    simpa [E.root_card] using card_mapEdge φ E.pattern.root
  have hnot : ¬B ⊆ mapEdge φ E.pattern.root := by
    intro hsub
    have hEq : B = mapEdge φ E.pattern.root :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact mappedRoot_not_mem_mappedNegative E hrk φ (hEq ▸ hB)
  obtain ⟨g, hgB, hgnot⟩ :=
    exists_powersetCard_not_subset hr (by omega : r ≤ B.card) hnot
  have hghost : g ∈ mappedHost E φ :=
    (mappedNegative_decomp E φ).2.1 B hB hgB
  refine ⟨g, hgB, ?_⟩
  rw [← mappedHost_sdiff_root_eq_freeEdges E φ]
  exact Finset.mem_sdiff.mpr ⟨hghost, fun hgroot ↦
    hgnot (Finset.mem_powersetCard.mp hgroot).1⟩

def rootBoundary (roots : Finset (Finset (Fin n))) (r : ℕ) :
    Finset (Finset (Fin n)) :=
  roots.biUnion fun Q ↦ Q.powersetCard r

theorem mappedNegative_pairwise_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {Q Q' : Finset (Fin n)} (hQ : Q ∈ roots) (hQ' : Q' ∈ roots)
    (hQQ' : Q ≠ Q') :
    Disjoint (mappedNegative E (S.embedding Q hQ))
      (mappedNegative E (S.embedding Q' hQ')) := by
  apply Finset.disjoint_left.mpr
  intro B hBQ hBQ'
  obtain ⟨g, hgB, hgfreeQ⟩ :=
    exists_freeEdge_of_mem_mappedNegative E hr hrk _ hBQ
  have hgcard : g.card = r := (Finset.mem_powersetCard.mp hgB).2
  have hgNotForbidden : g ∉ forbidden := fun hgf ↦
    Finset.disjoint_left.mp (S.free_disjoint_forbidden Q hQ) hgfreeQ hgf
  have hgNotRoot : ¬g ⊆ Q' := by
    intro hgQ'
    apply hgNotForbidden
    apply hrootForbidden
    apply Finset.mem_biUnion.mpr
    exact ⟨Q', hQ', Finset.mem_powersetCard.mpr ⟨hgQ', hgcard⟩⟩
  have hgHostQ' : g ∈ mappedHost E (S.embedding Q' hQ') :=
    (mappedNegative_decomp E _).2.1 B hBQ' hgB
  have hgFreeQ' : g ∈ imageFreeEdges E.pattern (S.embedding Q' hQ') := by
    rw [← mappedHost_sdiff_root_eq_freeEdges E (S.embedding Q' hQ')]
    apply Finset.mem_sdiff.mpr
    refine ⟨hgHostQ', ?_⟩
    intro hgRootImage
    apply hgNotRoot
    rw [← S.root_image Q' hQ']
    exact (Finset.mem_powersetCard.mp hgRootImage).1
  exact Finset.disjoint_left.mp
    (S.free_pairwise Q hQ Q' hQ' hQQ') hgfreeQ hgFreeQ'

theorem mappedPositiveErase_pairwise_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (hrk : r ≤ k)
    {Q Q' : Finset (Fin n)} (hQ : Q ∈ roots) (hQ' : Q' ∈ roots)
    (hQQ' : Q ≠ Q') :
    Disjoint
      ((mappedPositive E (S.embedding Q hQ)).erase Q)
      ((mappedPositive E (S.embedding Q' hQ')).erase Q') := by
  have hrootQ := S.root_image Q hQ
  have hrootQ' := S.root_image Q' hQ'
  have hdecQ : IsUniformDecomposition
      (imageFreeEdges E.pattern (S.embedding Q hQ))
      ((mappedPositive E (S.embedding Q hQ)).erase Q) k r := by
    simpa [hrootQ] using mappedPositive_erase_decomp E (S.embedding Q hQ)
  have hdecQ' : IsUniformDecomposition
      (imageFreeEdges E.pattern (S.embedding Q' hQ'))
      ((mappedPositive E (S.embedding Q' hQ')).erase Q') k r := by
    simpa [hrootQ'] using mappedPositive_erase_decomp E (S.embedding Q' hQ')
  exact hdecQ.disjoint_blocks hdecQ'
    (S.free_pairwise Q hQ Q' hQ' hQQ') hrk

theorem mappedNegative_pairwiseDisjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden) :
    (↑roots.attach : Set ↥roots).PairwiseDisjoint fun Q ↦
      mappedNegative E (S.embedding Q.1 Q.2) := by
  intro Q hQ Q' hQ' hne
  apply mappedNegative_pairwise_disjoint S hr hrk hrootForbidden
    Q.2 Q'.2
  intro hval
  exact hne (Subtype.ext hval)

theorem mappedPositiveErase_pairwiseDisjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (hrk : r ≤ k) :
    (↑roots.attach : Set ↥roots).PairwiseDisjoint fun Q ↦
      (mappedPositive E (S.embedding Q.1 Q.2)).erase Q.1 := by
  intro Q hQ Q' hQ' hne
  apply mappedPositiveErase_pairwise_disjoint S hrk Q.2 Q'.2
  intro hval
  exact hne (Subtype.ext hval)

/-- Summing any selected set of separated rooted exchanges gives exactly
the sum of the selected root-clique incidence vectors. -/
theorem selectedFullExchanges_signed_roots
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))} {C : ℕ}
    (S : BoundedRootedFamilyEmbeddings E.pattern roots forbidden C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (chosen : Finset ↥roots) {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount
        (chosen.biUnion fun Q ↦ mappedNegative E (S.embedding Q.1 Q.2)) g : ℤ) -
      (incidenceCount
        (chosen.biUnion fun Q ↦
          (mappedPositive E (S.embedding Q.1 Q.2)).erase Q.1) g : ℤ) =
      ∑ Q ∈ chosen, if g ⊆ Q.1 then (1 : ℤ) else 0 := by
  let neg : ↥roots → Finset (Finset (Fin n)) := fun Q ↦
    mappedNegative E (S.embedding Q.1 Q.2)
  let posErase : ↥roots → Finset (Finset (Fin n)) := fun Q ↦
    (mappedPositive E (S.embedding Q.1 Q.2)).erase Q.1
  have hnegPair : (↑chosen : Set ↥roots).PairwiseDisjoint neg := by
    intro Q hQ Q' hQ' hne
    exact mappedNegative_pairwise_disjoint S hr hrk hrootForbidden
      Q.2 Q'.2 (fun hval ↦ hne (Subtype.ext hval))
  have hposPair : (↑chosen : Set ↥roots).PairwiseDisjoint posErase := by
    intro Q hQ Q' hQ' hne
    exact mappedPositiveErase_pairwise_disjoint S hrk.le Q.2 Q'.2
      (fun hval ↦ hne (Subtype.ext hval))
  have hnegFilter : (↑chosen : Set ↥roots).PairwiseDisjoint fun Q ↦
      (neg Q).filter fun B ↦ g ⊆ B := by
    intro Q hQ Q' hQ' hne
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hnegPair hQ hQ' hne)
  have hposFilter : (↑chosen : Set ↥roots).PairwiseDisjoint fun Q ↦
      (posErase Q).filter fun B ↦ g ⊆ B := by
    intro Q hQ Q' hQ' hne
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hposPair hQ hQ' hne)
  rw [incidenceCount, Finset.filter_biUnion, Finset.card_biUnion hnegFilter,
    incidenceCount, Finset.filter_biUnion, Finset.card_biUnion hposFilter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hsingle := mappedFullExchange_signed_root E
    (S.embedding Q.1 Q.2) hg
  simpa [neg, posErase, incidenceCount, S.root_image Q.1 Q.2] using hsingle

lemma multiIndex_label_ne
    {roots : Finset (Finset (Fin n))} {multiplicity : ℕ}
    {I I' : ↥roots × Fin multiplicity} (hII' : I ≠ I') :
    (I.1.1, (I.2 : ℕ)) ≠ (I'.1.1, (I'.2 : ℕ)) := by
  intro hlabel
  apply hII'
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hlabel)
  · exact Fin.ext (congrArg Prod.snd hlabel)

/-- Near special blocks from distinct bank copies which carry the same
input edge meet in exactly that edge.  Edge separation is enough: any
additional common vertex would create a second common `r`-edge. -/
theorem mappedSpecial_multi_inter_card_of_same_edge
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {I I' : ↥roots × Fin multiplicity} (hII' : I ≠ I')
    (e e' : RootEdge k r)
    (hsame : mapEdge
        (E.rootEmbedding.trans (S.embedding I.1.1 I.1.2 I.2)) e.1 =
      mapEdge
        (E.rootEmbedding.trans (S.embedding I'.1.1 I'.1.2 I'.2)) e'.1) :
    (mappedSpecial E (S.embedding I.1.1 I.1.2 I.2) e ∩
      mappedSpecial E (S.embedding I'.1.1 I'.1.2 I'.2) e').card = r := by
  let φ := S.embedding I.1.1 I.1.2 I.2
  let φ' := S.embedding I'.1.1 I'.1.2 I'.2
  let g := mapEdge (E.rootEmbedding.trans φ) e.1
  have hgcard : g.card = r := by
    simp [g, RootEdge.card]
  have hgB : g ⊆ mappedSpecial E φ e := by
    intro x hx
    have hxInter : x ∈ mappedSpecial E φ e ∩
        mapEdge φ E.pattern.root := by
      rw [mappedSpecial_inter_mappedRoot E φ e]
      exact hx
    exact (Finset.mem_inter.mp hxInter).1
  have hgB' : g ⊆ mappedSpecial E φ' e' := by
    intro x hx
    have hx' : x ∈ mapEdge (E.rootEmbedding.trans φ') e'.1 := by
      rw [← hsame]
      exact hx
    have hxInter : x ∈ mappedSpecial E φ' e' ∩
        mapEdge φ' E.pattern.root := by
      rw [mappedSpecial_inter_mappedRoot E φ' e']
      exact hx'
    exact (Finset.mem_inter.mp hxInter).1
  have hgRoot : g ∈ I.1.1.powersetCard r := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hgcard⟩
    rw [← S.root_image I.1.1 I.1.2 I.2]
    intro x hx
    have hxInter : x ∈ mappedSpecial E φ e ∩
        mapEdge φ E.pattern.root := by
      rw [mappedSpecial_inter_mappedRoot E φ e]
      exact hx
    exact (Finset.mem_inter.mp hxInter).2
  have hgForbidden : g ∈ forbidden := by
    apply hrootForbidden
    apply Finset.mem_biUnion.mpr
    exact ⟨I.1.1, I.1.2, hgRoot⟩
  have hlabel := multiIndex_label_ne hII'
  have hcommon : ∀ h ∈
      (mappedSpecial E φ e ∩ mappedSpecial E φ' e').powersetCard r,
      h = g := by
    intro h hh
    have hhData := Finset.mem_powersetCard.mp hh
    have hhB : h ∈ (mappedSpecial E φ e).powersetCard r :=
      Finset.mem_powersetCard.mpr
        ⟨hhData.1.trans Finset.inter_subset_left, hhData.2⟩
    have hhB' : h ∈ (mappedSpecial E φ' e').powersetCard r :=
      Finset.mem_powersetCard.mpr
        ⟨hhData.1.trans Finset.inter_subset_right, hhData.2⟩
    rcases mappedSpecial_edge_eq_or_free E φ e hhB with heq | hfree <;>
      rcases mappedSpecial_edge_eq_or_free E φ' e' hhB' with
        heq' | hfree'
    · exact heq
    · exfalso
      exact Finset.disjoint_left.mp
        (S.free_disjoint_forbidden I'.1.1 I'.1.2 I'.2)
          hfree' (by simpa [heq] using hgForbidden)
    · exfalso
      exact Finset.disjoint_left.mp
        (S.free_disjoint_forbidden I.1.1 I.1.2 I.2)
          hfree (by simpa [heq'.trans hsame.symm] using hgForbidden)
    · exact False.elim (Finset.disjoint_left.mp
        (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2 hlabel)
          hfree hfree')
  have hgInter : g ⊆ mappedSpecial E φ e ∩ mappedSpecial E φ' e' :=
    fun x hx ↦ Finset.mem_inter.mpr ⟨hgB hx, hgB' hx⟩
  have hlower : r ≤
      (mappedSpecial E φ e ∩ mappedSpecial E φ' e').card := by
    calc
      r = g.card := hgcard.symm
      _ ≤ (mappedSpecial E φ e ∩ mappedSpecial E φ' e').card :=
        Finset.card_le_card hgInter
  have hupper :
      (mappedSpecial E φ e ∩ mappedSpecial E φ' e').card ≤ r := by
    by_contra hnot
    have hnotSub : ¬(mappedSpecial E φ e ∩ mappedSpecial E φ' e') ⊆ g := by
      intro hsub
      have hc := Finset.card_le_card hsub
      rw [hgcard] at hc
      omega
    obtain ⟨h, hh, hhnot⟩ := exists_powersetCard_not_subset hr hlower hnotSub
    exact hhnot (by rw [hcommon h hh])
  simpa [φ, φ'] using Nat.le_antisymm hupper hlower

theorem mappedNegative_multi_pairwise_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {I I' : ↥roots × Fin multiplicity} (hII' : I ≠ I') :
    Disjoint (mappedNegative E (S.embedding I.1.1 I.1.2 I.2))
      (mappedNegative E (S.embedding I'.1.1 I'.1.2 I'.2)) := by
  apply Finset.disjoint_left.mpr
  intro B hBI hBI'
  obtain ⟨g, hgB, hgfreeI⟩ :=
    exists_freeEdge_of_mem_mappedNegative E hr hrk _ hBI
  have hgcard : g.card = r := (Finset.mem_powersetCard.mp hgB).2
  have hgNotForbidden : g ∉ forbidden := fun hgf ↦
    Finset.disjoint_left.mp
      (S.free_disjoint_forbidden I.1.1 I.1.2 I.2) hgfreeI hgf
  have hgNotRoot : ¬g ⊆ I'.1.1 := by
    intro hgI'
    apply hgNotForbidden
    apply hrootForbidden
    apply Finset.mem_biUnion.mpr
    exact ⟨I'.1.1, I'.1.2,
      Finset.mem_powersetCard.mpr ⟨hgI', hgcard⟩⟩
  have hgHostI' : g ∈ mappedHost E
      (S.embedding I'.1.1 I'.1.2 I'.2) :=
    (mappedNegative_decomp E _).2.1 B hBI' hgB
  have hgFreeI' : g ∈ imageFreeEdges E.pattern
      (S.embedding I'.1.1 I'.1.2 I'.2) := by
    rw [← mappedHost_sdiff_root_eq_freeEdges E
      (S.embedding I'.1.1 I'.1.2 I'.2)]
    apply Finset.mem_sdiff.mpr
    refine ⟨hgHostI', ?_⟩
    intro hgRootImage
    apply hgNotRoot
    rw [← S.root_image I'.1.1 I'.1.2 I'.2]
    exact (Finset.mem_powersetCard.mp hgRootImage).1
  exact Finset.disjoint_left.mp
    (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
      (multiIndex_label_ne hII')) hgfreeI hgFreeI'

theorem mappedPositiveErase_multi_pairwise_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hrk : r ≤ k)
    {I I' : ↥roots × Fin multiplicity} (hII' : I ≠ I') :
    Disjoint
      ((mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)
      ((mappedPositive E
        (S.embedding I'.1.1 I'.1.2 I'.2)).erase I'.1.1) := by
  have hrootI := S.root_image I.1.1 I.1.2 I.2
  have hrootI' := S.root_image I'.1.1 I'.1.2 I'.2
  have hdecI : IsUniformDecomposition
      (imageFreeEdges E.pattern (S.embedding I.1.1 I.1.2 I.2))
      ((mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)
      k r := by
    simpa [hrootI] using mappedPositive_erase_decomp E
      (S.embedding I.1.1 I.1.2 I.2)
  have hdecI' : IsUniformDecomposition
      (imageFreeEdges E.pattern (S.embedding I'.1.1 I'.1.2 I'.2))
      ((mappedPositive E
        (S.embedding I'.1.1 I'.1.2 I'.2)).erase I'.1.1) k r := by
    simpa [hrootI'] using mappedPositive_erase_decomp E
      (S.embedding I'.1.1 I'.1.2 I'.2)
  exact hdecI.disjoint_blocks hdecI'
    (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
      (multiIndex_label_ne hII')) hrk

theorem mappedNegative_multi_disjoint_mappedPositiveErase
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    {I I' : ↥roots × Fin multiplicity} (hII' : I ≠ I') :
    Disjoint (mappedNegative E (S.embedding I.1.1 I.1.2 I.2))
      ((mappedPositive E
        (S.embedding I'.1.1 I'.1.2 I'.2)).erase I'.1.1) := by
  apply Finset.disjoint_left.mpr
  intro B hBI hBI'
  obtain ⟨g, hgB, hgfreeI⟩ :=
    exists_freeEdge_of_mem_mappedNegative E hr hrk _ hBI
  have hgcard : g.card = r := (Finset.mem_powersetCard.mp hgB).2
  have hgNotForbidden : g ∉ forbidden := fun hgf ↦
    Finset.disjoint_left.mp
      (S.free_disjoint_forbidden I.1.1 I.1.2 I.2) hgfreeI hgf
  have hgNotRoot : ¬g ⊆ I'.1.1 := by
    intro hgI'
    apply hgNotForbidden
    apply hrootForbidden
    apply Finset.mem_biUnion.mpr
    exact ⟨I'.1.1, I'.1.2,
      Finset.mem_powersetCard.mpr ⟨hgI', hgcard⟩⟩
  have hrootI' := S.root_image I'.1.1 I'.1.2 I'.2
  have hdecomp : IsUniformDecomposition
      (imageFreeEdges E.pattern (S.embedding I'.1.1 I'.1.2 I'.2))
      ((mappedPositive E
        (S.embedding I'.1.1 I'.1.2 I'.2)).erase I'.1.1) k r := by
    simpa [hrootI'] using mappedPositive_erase_decomp E
      (S.embedding I'.1.1 I'.1.2 I'.2)
  have hgFreeI' : g ∈ imageFreeEdges E.pattern
      (S.embedding I'.1.1 I'.1.2 I'.2) :=
    hdecomp.2.1 B hBI' hgB
  exact Finset.disjoint_left.mp
    (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2
      (multiIndex_label_ne hII')) hgfreeI hgFreeI'

/-- Summing any selected root/layer copies gives the sum of their root-clique
incidence vectors, including repeated copies at the same root. -/
theorem selectedMultiFullExchanges_signed_roots
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (chosen : Finset (↥roots × Fin multiplicity))
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount
        (chosen.biUnion fun I ↦
          mappedNegative E (S.embedding I.1.1 I.1.2 I.2)) g : ℤ) -
      (incidenceCount
        (chosen.biUnion fun I ↦
          (mappedPositive E
            (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) g : ℤ) =
      ∑ I ∈ chosen, if g ⊆ I.1.1 then (1 : ℤ) else 0 := by
  let neg : ↥roots × Fin multiplicity → Finset (Finset (Fin n)) := fun I ↦
    mappedNegative E (S.embedding I.1.1 I.1.2 I.2)
  let posErase : ↥roots × Fin multiplicity →
      Finset (Finset (Fin n)) := fun I ↦
    (mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1
  have hnegPair : (↑chosen : Set (↥roots × Fin multiplicity)).PairwiseDisjoint
      neg := by
    intro I hI I' hI' hne
    exact mappedNegative_multi_pairwise_disjoint S hr hrk hrootForbidden hne
  have hposPair : (↑chosen : Set (↥roots × Fin multiplicity)).PairwiseDisjoint
      posErase := by
    intro I hI I' hI' hne
    exact mappedPositiveErase_multi_pairwise_disjoint S hrk.le hne
  have hnegFilter :
      (↑chosen : Set (↥roots × Fin multiplicity)).PairwiseDisjoint fun I ↦
        (neg I).filter fun B ↦ g ⊆ B := by
    intro I hI I' hI' hne
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hnegPair hI hI' hne)
  have hposFilter :
      (↑chosen : Set (↥roots × Fin multiplicity)).PairwiseDisjoint fun I ↦
        (posErase I).filter fun B ↦ g ⊆ B := by
    intro I hI I' hI' hne
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (hposPair hI hI' hne)
  rw [incidenceCount, Finset.filter_biUnion, Finset.card_biUnion hnegFilter,
    incidenceCount, Finset.filter_biUnion, Finset.card_biUnion hposFilter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  have hsingle := mappedFullExchange_signed_root E
    (S.embedding I.1.1 I.1.2 I.2) hg
  simpa [neg, posErase, incidenceCount,
    S.root_image I.1.1 I.1.2 I.2] using hsingle

lemma intToNat_le_natAbs (z : ℤ) : z.toNat ≤ z.natAbs := by
  cases z <;> simp

lemma sum_fin_layers_lt_toNat {m : ℕ} (z : ℤ) (h : z.natAbs ≤ m) :
    ∑ t : Fin m,
      (if (t : ℕ) < z.toNat then (1 : ℤ) else (0 : ℤ)) = z.toNat := by
  have hz : z.toNat ≤ m := (intToNat_le_natAbs z).trans h
  have hcard : ((Finset.univ : Finset (Fin m)).filter fun t : Fin m ↦
      (t : ℕ) < z.toNat).card = z.toNat := by
    rw [Fin.card_filter_val_lt, min_eq_right hz]
  calc
    (∑ t : Fin m,
        (if (t : ℕ) < z.toNat then (1 : ℤ) else (0 : ℤ))) =
        (((Finset.univ : Finset (Fin m)).filter fun t : Fin m ↦
          (t : ℕ) < z.toNat).card : ℤ) := by simp
    _ = z.toNat := by exact_mod_cast hcard

/-- Layers assigned to the positive part of an integer coefficient. -/
def positiveLayerSelection {n m : ℕ}
    (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) : Finset (↥roots × Fin m) :=
  (roots.attach.product Finset.univ).filter fun I ↦
    (I.2 : ℕ) < (θ I.1.1).toNat

/-- Layers assigned to the negative part of an integer coefficient. -/
def negativeLayerSelection {n m : ℕ}
    (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) : Finset (↥roots × Fin m) :=
  (roots.attach.product Finset.univ).filter fun I ↦
    (I.2 : ℕ) < (-θ I.1.1).toNat

theorem positiveLayerSelection_disjoint_negativeLayerSelection
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) :
    Disjoint (positiveLayerSelection (m := m) roots θ)
      (negativeLayerSelection (m := m) roots θ) := by
  apply Finset.disjoint_left.mpr
  intro I hpos hneg
  have hposLt := (Finset.mem_filter.mp hpos).2
  have hnegLt := (Finset.mem_filter.mp hneg).2
  by_cases hnonneg : 0 ≤ θ I.1.1
  · have hzero : (-θ I.1.1).toNat = 0 :=
      Int.toNat_of_nonpos (neg_nonpos.mpr hnonneg)
    rw [hzero] at hnegLt
    omega
  · have hzero : (θ I.1.1).toNat = 0 :=
      Int.toNat_of_nonpos (le_of_not_ge hnonneg)
    rw [hzero] at hposLt
    omega

/-! ## Permanently signed layer banks -/

/-- The first half of a bank of `2 * m` exchange layers. -/
def positiveBankLayerEmbedding (m : ℕ) : Fin m ↪ Fin (2 * m) :=
  Fin.castLEEmb (by omega)

/-- The second half of a bank of `2 * m` exchange layers. -/
def negativeBankLayerEmbedding (m : ℕ) : Fin m ↪ Fin (2 * m) :=
  { toFun := fun t ↦ ⟨m + t.1, by omega⟩
    inj' := by
      intro t u h
      apply Fin.ext
      have hval := congrArg Fin.val h
      change m + t.1 = m + u.1 at hval
      omega }

def bankIndexEmbedding
    {roots : Finset (Finset (Fin n))} {m : ℕ}
    (f : Fin m ↪ Fin (2 * m)) :
    (↥roots × Fin m) ↪ (↥roots × Fin (2 * m)) :=
  (Function.Embedding.refl ↥roots).prodMap f

/-- Selected layers in the permanently positive-labelled half of the bank. -/
def positiveBankSelection {n m : ℕ}
    (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) : Finset (↥roots × Fin (2 * m)) :=
  (positiveLayerSelection (m := m) roots θ).map
    (bankIndexEmbedding (positiveBankLayerEmbedding m))

/-- Selected layers in the permanently negative-labelled half of the bank. -/
def negativeBankSelection {n m : ℕ}
    (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) : Finset (↥roots × Fin (2 * m)) :=
  (negativeLayerSelection (m := m) roots θ).map
    (bankIndexEmbedding (negativeBankLayerEmbedding m))

@[simp] theorem positiveBankLayerEmbedding_val (m : ℕ) (t : Fin m) :
    (positiveBankLayerEmbedding m t).1 = t.1 := rfl

@[simp] theorem negativeBankLayerEmbedding_val (m : ℕ) (t : Fin m) :
    (negativeBankLayerEmbedding m t).1 = m + t.1 := rfl

/-- The host assigned to one permanently signed splitting copy.  Positive
layers keep the whole free host; negative layers delete the near root
boundary, which is exactly the part later routed through elimination. -/
def permanentNegativeBankHost
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (I : ↥roots × Fin (2 * m)) : Finset (Finset (Fin n)) :=
  if (I.2 : ℕ) < m then
    imageFreeEdges E.pattern (S.embedding I.1.1 I.1.2 I.2)
  else
    mappedHost E (S.embedding I.1.1 I.1.2 I.2) \
      (mappedNearNegative E
        (S.embedding I.1.1 I.1.2 I.2)).biUnion
          (fun B ↦ B.powersetCard r)

/-- The negative splitting blocks permanently assigned to one bank copy. -/
def permanentNegativeBankBlocksAt
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (I : ↥roots × Fin (2 * m)) : Finset (Finset (Fin n)) :=
  if (I.2 : ℕ) < m then
    (mappedPositive E
      (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1
  else
    mappedFarNegative E (S.embedding I.1.1 I.1.2 I.2)

def permanentNegativeBankHostUnion
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    Finset (Finset (Fin n)) :=
  (roots.attach.product Finset.univ).biUnion
    (permanentNegativeBankHost S)

def permanentNegativeBankBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C) :
    Finset (Finset (Fin n)) :=
  (roots.attach.product Finset.univ).biUnion
    (permanentNegativeBankBlocksAt S)

/-- The permanently negative far splitting bank is already a genuine
edge-disjoint decomposition.  Only its omitted near blocks require the two
elimination rounds. -/
theorem permanentNegativeBankBlocks_decomp
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hrk : r ≤ k) :
    IsUniformDecomposition (permanentNegativeBankHostUnion S)
      (permanentNegativeBankBlocks S) k r := by
  classical
  let indices := roots.attach.product
    (Finset.univ : Finset (Fin (2 * m)))
  let host : (↥roots × Fin (2 * m)) → Finset (Finset (Fin n)) :=
    permanentNegativeBankHost S
  let blocks : (↥roots × Fin (2 * m)) →
      Finset (Finset (Fin n)) := permanentNegativeBankBlocksAt S
  have hdecomp : ∀ I ∈ indices,
      IsUniformDecomposition (host I) (blocks I) k r := by
    intro I hI
    by_cases hpos : (I.2 : ℕ) < m
    · have hroot := S.root_image I.1.1 I.1.2 I.2
      simpa [host, blocks, permanentNegativeBankHost,
        permanentNegativeBankBlocksAt, hpos, hroot] using
        mappedPositive_erase_decomp E
          (S.embedding I.1.1 I.1.2 I.2)
    · simpa [host, blocks, permanentNegativeBankHost,
        permanentNegativeBankBlocksAt, hpos] using
        mappedFarNegative_decomp E
          (S.embedding I.1.1 I.1.2 I.2)
  have hhostSub (I : ↥roots × Fin (2 * m)) :
      host I ⊆ imageFreeEdges E.pattern
        (S.embedding I.1.1 I.1.2 I.2) := by
    by_cases hpos : (I.2 : ℕ) < m
    · simpa [host, permanentNegativeBankHost, hpos]
    · simpa [host, permanentNegativeBankHost, hpos] using
        mappedFarHost_subset_freeEdges E
          (S.embedding I.1.1 I.1.2 I.2)
  have huniform : ∀ I ∈ indices, ∀ g ∈ host I, g.card = r := by
    intro I hI g hg
    exact imageFreeEdges_uniform E.pattern
      (S.embedding I.1.1 I.1.2 I.2) (hhostSub I hg)
  have hpair : ∀ I ∈ indices, ∀ I' ∈ indices, I ≠ I' →
      Disjoint (host I) (host I') := by
    intro I hI I' hI' hne
    have hlabel := multiIndex_label_ne hne
    exact Disjoint.mono (hhostSub I) (hhostSub I')
      (S.free_pairwise I.1.1 I.1.2 I.2 I'.1.1 I'.1.2 I'.2 hlabel)
  have h := IsUniformDecomposition.biUnion indices host blocks
    hdecomp huniform hpair hrk
  simpa [indices, host, blocks, permanentNegativeBankHostUnion,
    permanentNegativeBankBlocks] using h

theorem sum_positiveBankSelection
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) (g : Finset (Fin n)) :
    ∑ I ∈ positiveBankSelection (m := m) roots θ,
        (if g ⊆ I.1.1 then (1 : ℤ) else 0) =
      ∑ I ∈ positiveLayerSelection (m := m) roots θ,
        (if g ⊆ I.1.1 then (1 : ℤ) else 0) := by
  unfold positiveBankSelection
  rw [Finset.sum_map]
  rfl

theorem sum_negativeBankSelection
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) (g : Finset (Fin n)) :
    ∑ I ∈ negativeBankSelection (m := m) roots θ,
        (if g ⊆ I.1.1 then (1 : ℤ) else 0) =
      ∑ I ∈ negativeLayerSelection (m := m) roots θ,
        (if g ⊆ I.1.1 then (1 : ℤ) else 0) := by
  unfold negativeBankSelection
  rw [Finset.sum_map]
  rfl

theorem positiveBankSelection_disjoint_negativeBankSelection
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ) :
    Disjoint (positiveBankSelection (m := m) roots θ)
      (negativeBankSelection (m := m) roots θ) := by
  apply Finset.disjoint_left.mpr
  intro I hIpos hIneg
  obtain ⟨Ipos, _hIpos, hpos⟩ := Finset.mem_map.mp hIpos
  obtain ⟨Ineg, _hIneg, hneg⟩ := Finset.mem_map.mp hIneg
  have hsnd := congrArg (fun I : ↥roots × Fin (2 * m) ↦ I.2.1)
    (hpos.trans hneg.symm)
  change Ipos.2.1 = m + Ineg.2.1 at hsnd
  omega

/-- Positive blocks selected from a bank whose first and second halves have
permanent opposite signs. -/
def selectedBankPositiveBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  ((positiveBankSelection (m := m) roots θ).biUnion fun I ↦
      mappedNegative E (S.embedding I.1.1 I.1.2 I.2)) ∪
    ((negativeBankSelection (m := m) roots θ).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)

/-- Negative blocks selected from the same permanently signed bank. -/
def selectedBankNegativeBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  ((positiveBankSelection (m := m) roots θ).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) ∪
    ((negativeBankSelection (m := m) roots θ).biUnion fun I ↦
      mappedNegative E (S.embedding I.1.1 I.1.2 I.2))

/-- Near positive splitting blocks selected from the permanent positive
half. -/
def selectedBankPositiveNearBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  (positiveBankSelection (m := m) roots θ).biUnion fun I ↦
    mappedNearNegative E (S.embedding I.1.1 I.1.2 I.2)

/-- Near negative splitting blocks selected from the permanent negative
half. -/
def selectedBankNegativeNearBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  (negativeBankSelection (m := m) roots θ).biUnion fun I ↦
    mappedNearNegative E (S.embedding I.1.1 I.1.2 I.2)

/-- The selected negative splitting blocks after deleting the near part. -/
def selectedBankFarNegativeBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  ((positiveBankSelection (m := m) roots θ).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) ∪
    ((negativeBankSelection (m := m) roots θ).biUnion fun I ↦
      mappedFarNegative E (S.embedding I.1.1 I.1.2 I.2))

theorem mappedFarNegative_union_mappedNearNegative
    (E : RelabeledFullExchange k r) (φ : Fin E.v ↪ Fin n) :
    mappedFarNegative E φ ∪ mappedNearNegative E φ =
      mappedNegative E φ := by
  exact Finset.sdiff_union_of_subset
    (mappedNearNegative_subset_mappedNegative E φ)

theorem selectedBankNegativeBlocks_eq_far_union_near
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) :
    selectedBankNegativeBlocks S θ =
      selectedBankFarNegativeBlocks S θ ∪
        selectedBankNegativeNearBlocks S θ := by
  classical
  ext B
  simp only [selectedBankNegativeBlocks, selectedBankFarNegativeBlocks,
    selectedBankNegativeNearBlocks, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (hpos | ⟨I, hI, hB⟩)
    · exact Or.inl (Or.inl hpos)
    · rcases Finset.mem_union.mp
          (show B ∈ mappedFarNegative E
              (S.embedding I.1.1 I.1.2 I.2) ∪
            mappedNearNegative E
              (S.embedding I.1.1 I.1.2 I.2) by
            rw [mappedFarNegative_union_mappedNearNegative]
            exact hB) with hfar | hnear
      · exact Or.inl (Or.inr ⟨I, hI, hfar⟩)
      · exact Or.inr ⟨I, hI, hnear⟩
  · rintro ((hpos | ⟨I, hI, hfar⟩) | ⟨I, hI, hnear⟩)
    · exact Or.inl hpos
    · exact Or.inr ⟨I, hI, (Finset.mem_sdiff.mp hfar).1⟩
    · exact Or.inr ⟨I, hI,
        mappedNearNegative_subset_mappedNegative E _ hnear⟩

theorem selectedBankPositiveNearBlocks_subset
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) :
    selectedBankPositiveNearBlocks S θ ⊆
      selectedBankPositiveBlocks S θ := by
  intro B hB
  obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  exact ⟨I, hI, mappedNearNegative_subset_mappedNegative E _ hBI⟩

theorem selectedBankNegativeNearBlocks_subset
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (θ : Finset (Fin n) → ℤ) :
    selectedBankNegativeNearBlocks S θ ⊆
      selectedBankNegativeBlocks S θ := by
  intro B hB
  obtain ⟨I, hI, hBI⟩ := Finset.mem_biUnion.mp hB
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨I, hI, mappedNearNegative_subset_mappedNegative E _ hBI⟩

theorem selectedBankPositive_cross_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ) :
    Disjoint
      ((positiveBankSelection (m := m) roots θ).biUnion fun I ↦
        mappedNegative E (S.embedding I.1.1 I.1.2 I.2))
      ((negativeBankSelection (m := m) roots θ).biUnion fun I ↦
        (mappedPositive E
          (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) := by
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  obtain ⟨I, hIpos, hBI⟩ := Finset.mem_biUnion.mp hBpos
  obtain ⟨I', hIneg, hBI'⟩ := Finset.mem_biUnion.mp hBneg
  have hII' : I ≠ I' := by
    intro hEq
    subst I'
    exact Finset.disjoint_left.mp
      (positiveBankSelection_disjoint_negativeBankSelection roots θ)
      hIpos hIneg
  exact Finset.disjoint_left.mp
    (mappedNegative_multi_disjoint_mappedPositiveErase
      S hr hrk hrootForbidden hII') hBI hBI'

theorem selectedBankNegative_cross_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ) :
    Disjoint
      ((positiveBankSelection (m := m) roots θ).biUnion fun I ↦
        (mappedPositive E
          (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)
      ((negativeBankSelection (m := m) roots θ).biUnion fun I ↦
        mappedNegative E (S.embedding I.1.1 I.1.2 I.2)) := by
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  obtain ⟨I, hIpos, hBI⟩ := Finset.mem_biUnion.mp hBpos
  obtain ⟨I', hIneg, hBI'⟩ := Finset.mem_biUnion.mp hBneg
  have hII' : I' ≠ I := by
    intro hEq
    subst I'
    exact Finset.disjoint_left.mp
      (positiveBankSelection_disjoint_negativeBankSelection roots θ)
      hIpos hIneg
  exact Finset.disjoint_left.mp
    (mappedNegative_multi_disjoint_mappedPositiveErase
      S hr hrk hrootForbidden hII').symm hBI hBI'

def selectedSignedPositiveBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  ((positiveLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
      mappedNegative E (S.embedding I.1.1 I.1.2 I.2)) ∪
    ((negativeLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)

def selectedSignedNegativeBlocks
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (θ : Finset (Fin n) → ℤ) : Finset (Finset (Fin n)) :=
  ((positiveLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
      (mappedPositive E
        (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) ∪
    ((negativeLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
      mappedNegative E (S.embedding I.1.1 I.1.2 I.2))

lemma incidenceCount_union_of_disjoint
    {family₁ family₂ : Finset (Finset (Fin n))}
    (hdisjoint : Disjoint family₁ family₂) (g : Finset (Fin n)) :
    incidenceCount (family₁ ∪ family₂) g =
      incidenceCount family₁ g + incidenceCount family₂ g := by
  unfold incidenceCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    hdisjoint

theorem selectedSignedPositive_cross_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ) :
    Disjoint
      ((positiveLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
        mappedNegative E (S.embedding I.1.1 I.1.2 I.2))
      ((negativeLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
        (mappedPositive E
          (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) := by
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  obtain ⟨I, hIpos, hBI⟩ := Finset.mem_biUnion.mp hBpos
  obtain ⟨I', hIneg, hBI'⟩ := Finset.mem_biUnion.mp hBneg
  have hII' : I ≠ I' := by
    intro hEq
    subst I'
    exact Finset.disjoint_left.mp
      (positiveLayerSelection_disjoint_negativeLayerSelection roots θ)
      hIpos hIneg
  exact Finset.disjoint_left.mp
    (mappedNegative_multi_disjoint_mappedPositiveErase
      S hr hrk hrootForbidden hII') hBI hBI'

theorem selectedSignedNegative_cross_disjoint
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ) :
    Disjoint
      ((positiveLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
        (mappedPositive E
          (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1)
      ((negativeLayerSelection (m := multiplicity) roots θ).biUnion fun I ↦
        mappedNegative E (S.embedding I.1.1 I.1.2 I.2)) := by
  apply Finset.disjoint_left.mpr
  intro B hBpos hBneg
  obtain ⟨I, hIpos, hBI⟩ := Finset.mem_biUnion.mp hBpos
  obtain ⟨I', hIneg, hBI'⟩ := Finset.mem_biUnion.mp hBneg
  have hII' : I' ≠ I := by
    intro hEq
    subst I'
    exact Finset.disjoint_left.mp
      (positiveLayerSelection_disjoint_negativeLayerSelection roots θ)
      hIpos hIneg
  exact Finset.disjoint_left.mp
    (mappedNegative_multi_disjoint_mappedPositiveErase
      S hr hrk hrootForbidden hII').symm hBI hBI'

/-- Selecting the first `θ⁺` and `θ⁻` layers realizes the integer
coefficient exactly. -/
theorem signedLayerSelection_sum
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ)
    (hθ : ∀ Q ∈ roots, (θ Q).natAbs ≤ m)
    (g : Finset (Fin n)) :
    (∑ I ∈ positiveLayerSelection (m := m) roots θ,
      if g ⊆ I.1.1 then (1 : ℤ) else 0) -
      (∑ I ∈ negativeLayerSelection (m := m) roots θ,
        if g ⊆ I.1.1 then (1 : ℤ) else 0) =
      ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
  classical
  rw [positiveLayerSelection, negativeLayerSelection,
    Finset.sum_filter, Finset.sum_filter]
  have hposExpand :
      (∑ I ∈ roots.attach.product (Finset.univ : Finset (Fin m)),
        if (I.2 : ℕ) < (θ I.1.1).toNat then
          (if g ⊆ I.1.1 then (1 : ℤ) else 0) else 0) =
      ∑ Q ∈ roots.attach, ∑ t : Fin m,
        if (t : ℕ) < (θ Q.1).toNat then
          (if g ⊆ Q.1 then (1 : ℤ) else 0) else 0 := by
    exact Finset.sum_product _ _ _
  have hnegExpand :
      (∑ I ∈ roots.attach.product (Finset.univ : Finset (Fin m)),
        if (I.2 : ℕ) < (-θ I.1.1).toNat then
          (if g ⊆ I.1.1 then (1 : ℤ) else 0) else 0) =
      ∑ Q ∈ roots.attach, ∑ t : Fin m,
        if (t : ℕ) < (-θ Q.1).toNat then
          (if g ⊆ Q.1 then (1 : ℤ) else 0) else 0 := by
    exact Finset.sum_product _ _ _
  rw [hposExpand, hnegExpand, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hgQ : g ⊆ Q.1
  · simp only [hgQ, ↓reduceIte]
    rw [sum_fin_layers_lt_toNat (θ Q.1) (hθ Q.1 Q.2),
      sum_fin_layers_lt_toNat (-θ Q.1) (by simpa using hθ Q.1 Q.2)]
    exact Int.toNat_sub_toNat_neg (θ Q.1)
  · simp [hgQ]

theorem signedBankSelection_sum
    {n m : ℕ} (roots : Finset (Finset (Fin n)))
    (θ : Finset (Fin n) → ℤ)
    (hθ : ∀ Q ∈ roots, (θ Q).natAbs ≤ m)
    (g : Finset (Fin n)) :
    (∑ I ∈ positiveBankSelection (m := m) roots θ,
      if g ⊆ I.1.1 then (1 : ℤ) else 0) -
      (∑ I ∈ negativeBankSelection (m := m) roots θ,
        if g ⊆ I.1.1 then (1 : ℤ) else 0) =
      ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
  rw [sum_positiveBankSelection, sum_negativeBankSelection]
  exact signedLayerSelection_sum roots θ hθ g

/-- The permanently signed two-half bank realizes every coefficient vector
of absolute value at most `m` without changing the sign assigned to any
preallocated exchange copy. -/
theorem selectedBankBlocks_incidence_sub
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {m C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden (2 * m) C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (hθ : ∀ Q ∈ roots, (θ Q).natAbs ≤ m)
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount (selectedBankPositiveBlocks S θ) g : ℤ) -
        (incidenceCount (selectedBankNegativeBlocks S θ) g : ℤ) =
      ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
  let posIdx := positiveBankSelection (m := m) roots θ
  let negIdx := negativeBankSelection (m := m) roots θ
  let posNeg := posIdx.biUnion fun I ↦
    mappedNegative E (S.embedding I.1.1 I.1.2 I.2)
  let posErase := posIdx.biUnion fun I ↦
    (mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1
  let negNeg := negIdx.biUnion fun I ↦
    mappedNegative E (S.embedding I.1.1 I.1.2 I.2)
  let negErase := negIdx.biUnion fun I ↦
    (mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1
  have hposCross : Disjoint posNeg negErase := by
    simpa [posIdx, negIdx, posNeg, negErase] using
      selectedBankPositive_cross_disjoint S hr hrk hrootForbidden θ
  have hnegCross : Disjoint posErase negNeg := by
    simpa [posIdx, negIdx, posErase, negNeg] using
      selectedBankNegative_cross_disjoint S hr hrk hrootForbidden θ
  have hposIdentity := selectedMultiFullExchanges_signed_roots
    S hr hrk hrootForbidden posIdx hg
  have hnegIdentity := selectedMultiFullExchanges_signed_roots
    S hr hrk hrootForbidden negIdx hg
  rw [show selectedBankPositiveBlocks S θ = posNeg ∪ negErase by rfl,
    show selectedBankNegativeBlocks S θ = posErase ∪ negNeg by rfl,
    incidenceCount_union_of_disjoint hposCross,
    incidenceCount_union_of_disjoint hnegCross]
  push_cast
  calc
    ((incidenceCount posNeg g : ℤ) + incidenceCount negErase g) -
          ((incidenceCount posErase g : ℤ) + incidenceCount negNeg g) =
        ((incidenceCount posNeg g : ℤ) - incidenceCount posErase g) -
          ((incidenceCount negNeg g : ℤ) - incidenceCount negErase g) := by
      ring
    _ = (∑ I ∈ posIdx, if g ⊆ I.1.1 then (1 : ℤ) else 0) -
          ∑ I ∈ negIdx, if g ⊆ I.1.1 then (1 : ℤ) else 0 := by
      rw [hposIdentity, hnegIdentity]
    _ = ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
      simpa [posIdx, negIdx] using signedBankSelection_sum roots θ hθ g

/-- The two layer selections realize a bounded signed clique vector as a
difference of selected full-exchange trades. -/
theorem boundedCoefficients_fullExchange_identity
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (hθ : ∀ Q ∈ roots, (θ Q).natAbs ≤ multiplicity)
    {g : Finset (Fin n)} (hg : g.card = r) :
    ((incidenceCount
        ((positiveLayerSelection (m := multiplicity) roots θ).biUnion
          fun I ↦ mappedNegative E
            (S.embedding I.1.1 I.1.2 I.2)) g : ℤ) -
      (incidenceCount
        ((positiveLayerSelection (m := multiplicity) roots θ).biUnion
          fun I ↦ (mappedPositive E
            (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) g : ℤ)) -
      ((incidenceCount
        ((negativeLayerSelection (m := multiplicity) roots θ).biUnion
          fun I ↦ mappedNegative E
            (S.embedding I.1.1 I.1.2 I.2)) g : ℤ) -
      (incidenceCount
        ((negativeLayerSelection (m := multiplicity) roots θ).biUnion
          fun I ↦ (mappedPositive E
            (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1) g : ℤ)) =
      ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
  rw [selectedMultiFullExchanges_signed_roots S hr hrk hrootForbidden
      (positiveLayerSelection (m := multiplicity) roots θ) hg,
    selectedMultiFullExchanges_signed_roots S hr hrk hrootForbidden
      (negativeLayerSelection (m := multiplicity) roots θ) hg]
  exact signedLayerSelection_sum roots θ hθ g

/-- The coefficient identity as one genuine difference of two finite block
families; the two unions are cardinality-additive because opposite signs use
different layers. -/
theorem selectedSignedBlocks_incidence_sub
    {E : RelabeledFullExchange k r}
    {roots forbidden : Finset (Finset (Fin n))}
    {multiplicity C : ℕ}
    (S : BoundedMultiRootedFamilyEmbeddings
      E.pattern roots forbidden multiplicity C)
    (hr : 0 < r) (hrk : r < k)
    (hrootForbidden : rootBoundary roots r ⊆ forbidden)
    (θ : Finset (Fin n) → ℤ)
    (hθ : ∀ Q ∈ roots, (θ Q).natAbs ≤ multiplicity)
    {g : Finset (Fin n)} (hg : g.card = r) :
    (incidenceCount (selectedSignedPositiveBlocks S θ) g : ℤ) -
        (incidenceCount (selectedSignedNegativeBlocks S θ) g : ℤ) =
      ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
  let posIdx := positiveLayerSelection (m := multiplicity) roots θ
  let negIdx := negativeLayerSelection (m := multiplicity) roots θ
  let posNeg := posIdx.biUnion fun I ↦
    mappedNegative E (S.embedding I.1.1 I.1.2 I.2)
  let posErase := posIdx.biUnion fun I ↦
    (mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1
  let negNeg := negIdx.biUnion fun I ↦
    mappedNegative E (S.embedding I.1.1 I.1.2 I.2)
  let negErase := negIdx.biUnion fun I ↦
    (mappedPositive E (S.embedding I.1.1 I.1.2 I.2)).erase I.1.1
  have hposCross : Disjoint posNeg negErase := by
    simpa [posIdx, negIdx, posNeg, negErase] using
      selectedSignedPositive_cross_disjoint S hr hrk hrootForbidden θ
  have hnegCross : Disjoint posErase negNeg := by
    simpa [posIdx, negIdx, posErase, negNeg] using
      selectedSignedNegative_cross_disjoint S hr hrk hrootForbidden θ
  have hidentity := boundedCoefficients_fullExchange_identity
    S hr hrk hrootForbidden θ hθ hg
  rw [show selectedSignedPositiveBlocks S θ = posNeg ∪ negErase by rfl,
    show selectedSignedNegativeBlocks S θ = posErase ∪ negNeg by rfl,
    incidenceCount_union_of_disjoint hposCross,
    incidenceCount_union_of_disjoint hnegCross]
  push_cast
  calc
    ((incidenceCount posNeg g : ℤ) + incidenceCount negErase g) -
          ((incidenceCount posErase g : ℤ) + incidenceCount negNeg g) =
        ((incidenceCount posNeg g : ℤ) - incidenceCount posErase g) -
          ((incidenceCount negNeg g : ℤ) - incidenceCount negErase g) := by
      ring
    _ = ∑ Q ∈ roots.attach, if g ⊆ Q.1 then θ Q.1 else 0 := by
      simpa [posIdx, negIdx, posNeg, posErase, negNeg, negErase]
        using hidentity

end

end Erdos722.ExchangeEmbedding

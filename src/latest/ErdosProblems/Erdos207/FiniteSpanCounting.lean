/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberExtensionSplit
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Polynomial counting of bounded-span triple systems

The well-spread estimates ultimately reduce to a standard finite count: a
configuration extending a fixed root is determined by a bounded set of new
vertices and by one of boundedly many triple systems on that span.  This file
formalizes that reduction with explicit (coarse) constants.
-/

namespace Erdos207

open Finset

/-- Subsets of `s` having cardinality at most `d`. -/
def subsetsUpToCard {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : Finset (Finset α) :=
  (range (d + 1)).biUnion fun k ↦ s.powersetCard k

@[simp]
lemma mem_subsetsUpToCard_iff
    {α : Type*} [DecidableEq α] {s t : Finset α} {d : ℕ} :
    t ∈ subsetsUpToCard s d ↔ t ⊆ s ∧ t.card ≤ d := by
  constructor
  · intro ht
    obtain ⟨k, hk, htk⟩ := mem_biUnion.mp ht
    have hk' := mem_range.mp hk
    obtain ⟨hts, htcard⟩ := mem_powersetCard.mp htk
    exact ⟨hts, by omega⟩
  · rintro ⟨hts, htcard⟩
    apply mem_biUnion.mpr
    exact ⟨t.card, mem_range.mpr (by omega),
      mem_powersetCard.mpr ⟨hts, rfl⟩⟩

/-- Coarse polynomial bound for the number of subsets of bounded size.  The
base `|s|+1` handles the empty ambient set uniformly. -/
theorem card_subsetsUpToCard_le
    {α : Type*} [DecidableEq α] (s : Finset α) (d : ℕ) :
    (subsetsUpToCard s d).card ≤
      (d + 1) * (s.card + 1) ^ d := by
  calc
    (subsetsUpToCard s d).card ≤
        ∑ k ∈ range (d + 1), (s.powersetCard k).card :=
      card_biUnion_le
    _ = ∑ k ∈ range (d + 1), Nat.choose s.card k := by
      apply sum_congr rfl
      intro k _hk
      rw [card_powersetCard]
    _ ≤ ∑ _k ∈ range (d + 1), (s.card + 1) ^ d := by
      apply sum_le_sum
      intro k hk
      have hkd : k ≤ d := by
        have := mem_range.mp hk
        omega
      calc
        Nat.choose s.card k ≤ s.card ^ k := Nat.choose_le_pow _ _
        _ ≤ (s.card + 1) ^ k :=
          pow_le_pow_left₀ zero_le (by omega) k
        _ ≤ (s.card + 1) ^ d :=
          pow_le_pow_right₀ (by omega) hkd
    _ = (d + 1) * (s.card + 1) ^ d := by simp

/-- All triples whose vertices lie in `W`. -/
def triplesSupportedOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) : Finset (TripleOn V) :=
  (univ : Finset (TripleOn V)).filter fun T ↦ T.1 ⊆ W

@[simp]
lemma mem_triplesSupportedOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {W : Finset V} {T : TripleOn V} :
    T ∈ triplesSupportedOn W ↔ T.1 ⊆ W := by
  simp [triplesSupportedOn]

/-- Restrict a supported ambient triple to the subtype carried by `W`. -/
noncomputable def restrictSupportedTriple
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (T : triplesSupportedOn W) : TripleOn W := by
  classical
  refine ⟨T.1.1.subtype (fun x ↦ x ∈ W), ?_⟩
  rw [card_subtype, filter_eq_self.mpr]
  · exact T.1.2
  · intro x hx
    exact (mem_triplesSupportedOn_iff.mp T.2) hx

lemma restrictSupportedTriple_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) : Function.Injective (restrictSupportedTriple W) := by
  classical
  intro T U hTU
  apply Subtype.ext
  apply Subtype.ext
  have hTmap :
      (restrictSupportedTriple W T).1.map (Function.Embedding.subtype _) =
        T.1.1 := by
    apply subtype_map_of_mem
    intro x hx
    exact (mem_triplesSupportedOn_iff.mp T.2) hx
  have hUmap :
      (restrictSupportedTriple W U).1.map (Function.Embedding.subtype _) =
        U.1.1 := by
    apply subtype_map_of_mem
    intro x hx
    exact (mem_triplesSupportedOn_iff.mp U.2) hx
  rw [← hTmap, ← hUmap, hTU]

/-- At most `|W|^3` ambient triples are supported on `W`. -/
theorem card_triplesSupportedOn_le_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) :
    (triplesSupportedOn W).card ≤ W.card ^ 3 := by
  calc
    (triplesSupportedOn W).card =
        Fintype.card (triplesSupportedOn W) :=
      (Fintype.card_coe (triplesSupportedOn W)).symm
    _ ≤ Fintype.card (TripleOn W) :=
      Fintype.card_le_of_injective (restrictSupportedTriple W)
        (restrictSupportedTriple_injective W)
    _ = Nat.choose W.card 3 := by
      simpa only [Fintype.card_coe] using
        (Fintype.card_finset_len (α := W) 3)
    _ ≤ W.card ^ 3 := Nat.choose_le_pow _ _

/-- Triple systems supported on `W`. -/
def tripleSystemsSupportedOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) : Finset (TripleSystemOn V) :=
  (triplesSupportedOn W).powerset

@[simp]
lemma mem_tripleSystemsSupportedOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {W : Finset V} {C : TripleSystemOn V} :
    C ∈ tripleSystemsSupportedOn W ↔ verticesOn C ⊆ W := by
  rw [tripleSystemsSupportedOn, mem_powerset]
  constructor
  · intro hC x hx
    obtain ⟨T, hTC, hxT⟩ := mem_biUnion.mp hx
    exact (mem_triplesSupportedOn_iff.mp (hC hTC)) hxT
  · intro hspan T hTC
    apply mem_triplesSupportedOn_iff.mpr
    intro x hxT
    exact hspan (mem_biUnion.mpr ⟨T, hTC, hxT⟩)

/-- There are at most `2^(|W|^3)` triple systems on a prescribed span. -/
theorem card_tripleSystemsSupportedOn_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) :
    (tripleSystemsSupportedOn W).card ≤ 2 ^ (W.card ^ 3) := by
  rw [tripleSystemsSupportedOn, card_powerset]
  exact pow_le_pow_right₀ (by omega) (card_triplesSupportedOn_le_cube W)

/-- Triple systems extending `R` and spanning at most `q` vertices. -/
def tripleSystemsExtendingWithSpan
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : TripleSystemOn V) (q : ℕ) : Finset (TripleSystemOn V) :=
  (univ : Finset (TripleSystemOn V)).filter fun C ↦
    R ⊆ C ∧ (verticesOn C).card ≤ q

@[simp]
lemma mem_tripleSystemsExtendingWithSpan_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {R C : TripleSystemOn V} {q : ℕ} :
    C ∈ tripleSystemsExtendingWithSpan R q ↔
      R ⊆ C ∧ (verticesOn C).card ≤ q := by
  simp [tripleSystemsExtendingWithSpan]

/-- New vertices introduced beyond a fixed root system. -/
def extensionExtraVertices
    {V : Type*} [DecidableEq V]
    (R C : TripleSystemOn V) : Finset V :=
  verticesOn C \ verticesOn R

lemma extensionExtraVertices_mem_subsetsUpToCard
    {V : Type*} [Fintype V] [DecidableEq V]
    {R C : TripleSystemOn V} {q : ℕ}
    (hC : C ∈ tripleSystemsExtendingWithSpan R q) :
    extensionExtraVertices R C ∈
      subsetsUpToCard (univ \ verticesOn R)
        (q - (verticesOn R).card) := by
  obtain ⟨hRC, hspan⟩ :=
    mem_tripleSystemsExtendingWithSpan_iff.mp hC
  have hvertices : verticesOn R ⊆ verticesOn C := verticesOn_mono hRC
  apply mem_subsetsUpToCard_iff.mpr
  constructor
  · intro x hx
    obtain ⟨hxC, hxR⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨mem_univ x, hxR⟩
  · rw [extensionExtraVertices, card_sdiff_of_subset hvertices]
    omega

/-- Reattaching the fixed root vertices to the extra-vertex code recovers
the full vertex span. -/
lemma verticesOn_union_extensionExtraVertices
    {V : Type*} [DecidableEq V]
    {R C : TripleSystemOn V} (hRC : R ⊆ C) :
    verticesOn R ∪ extensionExtraVertices R C = verticesOn C := by
  exact union_sdiff_of_subset (verticesOn_mono hRC)

/-- Explicit polynomial bound for all bounded-span extensions of a fixed
root.  The factor `2^(q^3)` records the bounded number of hypergraphs on a
chosen span; the remaining factor chooses the new vertices. -/
theorem card_tripleSystemsExtendingWithSpan_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : TripleSystemOn V) (q : ℕ) :
    (tripleSystemsExtendingWithSpan R q).card ≤
      2 ^ (q ^ 3) *
        ((q - (verticesOn R).card + 1) *
          (((univ \ verticesOn R : Finset V).card + 1) ^
            (q - (verticesOn R).card))) := by
  classical
  let family := tripleSystemsExtendingWithSpan R q
  let code : TripleSystemOn V → Finset V := extensionExtraVertices R
  have hfiber : ∀ W ∈ family.image code,
      (family.filter fun C ↦ code C = W).card ≤ 2 ^ (q ^ 3) := by
    intro W hW
    obtain ⟨C, hCfamily, hCW⟩ := mem_image.mp hW
    have hC := mem_tripleSystemsExtendingWithSpan_iff.mp hCfamily
    have hspanUnion :
        (verticesOn R ∪ W).card ≤ q := by
      rw [← hCW, verticesOn_union_extensionExtraVertices hC.1]
      exact hC.2
    have hsub : (family.filter fun D ↦ code D = W) ⊆
        tripleSystemsSupportedOn (verticesOn R ∪ W) := by
      intro D hD
      obtain ⟨hDfamily, hDcode⟩ := mem_filter.mp hD
      have hD' := mem_tripleSystemsExtendingWithSpan_iff.mp hDfamily
      apply mem_tripleSystemsSupportedOn_iff.mpr
      rw [← verticesOn_union_extensionExtraVertices hD'.1]
      change verticesOn R ∪ extensionExtraVertices R D ⊆
        verticesOn R ∪ W
      dsimp only [code] at hDcode
      rw [hDcode]
    calc
      (family.filter fun D ↦ code D = W).card ≤
          (tripleSystemsSupportedOn (verticesOn R ∪ W)).card :=
        card_le_card hsub
      _ ≤ 2 ^ ((verticesOn R ∪ W).card ^ 3) :=
        card_tripleSystemsSupportedOn_le _
      _ ≤ 2 ^ (q ^ 3) := by
        apply pow_le_pow_right₀ (by omega)
        exact pow_le_pow_left₀ zero_le hspanUnion 3
  have himage : family.image code ⊆
      subsetsUpToCard (univ \ verticesOn R)
        (q - (verticesOn R).card) := by
    intro W hW
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hW
    exact extensionExtraVertices_mem_subsetsUpToCard hC
  calc
    family.card ≤ 2 ^ (q ^ 3) * (family.image code).card :=
      card_le_mul_card_image family (2 ^ (q ^ 3)) hfiber
    _ ≤ 2 ^ (q ^ 3) *
        (subsetsUpToCard (univ \ verticesOn R)
          (q - (verticesOn R).card)).card := by
      exact Nat.mul_le_mul_left _ (card_le_card himage)
    _ ≤ 2 ^ (q ^ 3) *
        ((q - (verticesOn R).card + 1) *
          (((univ \ verticesOn R : Finset V).card + 1) ^
            (q - (verticesOn R).card))) := by
      exact Nat.mul_le_mul_left _
        (card_subsetsUpToCard_le
          (univ \ verticesOn R : Finset V)
          (q - (verticesOn R).card))

/-- Minimal configurations of order between five and `q` which extend a
fixed root family. -/
noncomputable def erdosConfigExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (R : TripleSystemOn V) :
    Finset (ℕ × TripleSystemOn V) := by
  classical
  exact ((Icc 5 q).product (univ : Finset (TripleSystemOn V))).filter
    fun z ↦ IsErdosConfigOn z.1 z.2 ∧ R ⊆ z.2

@[simp]
lemma mem_erdosConfigExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {R E : TripleSystemOn V} {r : ℕ} :
    (r, E) ∈ erdosConfigExtensions q R ↔
      5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧ R ⊆ E := by
  classical
  simp [erdosConfigExtensions, and_assoc]

/-- On minimal configurations of order at least five, the triple system
determines the order parameter. -/
lemma erdosConfigExtensions_snd_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {R : TripleSystemOn V} :
    Set.InjOn (fun z : ℕ × TripleSystemOn V ↦ z.2)
      (erdosConfigExtensions q R : Set (ℕ × TripleSystemOn V)) := by
  intro z hz w hw hzw
  obtain ⟨hz5, _hzq, hzE, _hzR⟩ :=
    mem_erdosConfigExtensions_iff.mp hz
  obtain ⟨hw5, _hwq, hwE, _hwR⟩ :=
    mem_erdosConfigExtensions_iff.mp hw
  apply Prod.ext
  · have hcardz := hzE.1.1
    have hcardw := hwE.1.1
    change z.2 = w.2 at hzw
    rw [hzw] at hcardz
    omega
  · exact hzw

/-- Minimal rooted configurations inherit the bounded-span count. -/
theorem card_erdosConfigExtensions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (R : TripleSystemOn V) :
    (erdosConfigExtensions q R).card ≤
      2 ^ (q ^ 3) *
        ((q - (verticesOn R).card + 1) *
          (((univ \ verticesOn R : Finset V).card + 1) ^
            (q - (verticesOn R).card))) := by
  classical
  have himage : (erdosConfigExtensions q R).image
      (fun z : ℕ × TripleSystemOn V ↦ z.2) ⊆
      tripleSystemsExtendingWithSpan R q := by
    intro E hE
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hE
    obtain ⟨hr5, hrq, hzE, hRz⟩ :=
      mem_erdosConfigExtensions_iff.mp hz
    apply mem_tripleSystemsExtendingWithSpan_iff.mpr
    exact ⟨hRz, by rw [IsErdosConfig.vertices_card_eq hzE hr5]; exact hrq⟩
  calc
    (erdosConfigExtensions q R).card =
        ((erdosConfigExtensions q R).image
          (fun z : ℕ × TripleSystemOn V ↦ z.2)).card :=
      (card_image_of_injOn erdosConfigExtensions_snd_injective).symm
    _ ≤ (tripleSystemsExtendingWithSpan R q).card := card_le_card himage
    _ ≤ _ := card_tripleSystemsExtendingWithSpan_le R q

/-- Every indexed absorber-induced extension of `R` is the outside part of
one rooted minimal configuration. -/
theorem absorberInducedExtensions_subset_image_erdosConfigExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V) :
    absorberInducedExtensions q j B R ⊆
      (erdosConfigExtensions q R).image (fun z ↦ z.2 \ B) := by
  intro S hS
  obtain ⟨hSinduced, hRS⟩ :=
    mem_absorberInducedExtensions_iff.mp hS
  obtain ⟨_hScard, r, hr5, hrq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hSinduced
  have hRE : R ⊆ E := by
    intro T hTR
    have hTS : T ∈ S := hRS hTR
    have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
    exact (mem_sdiff.mp hTdiff).1
  apply mem_image.mpr
  exact ⟨(r, E), mem_erdosConfigExtensions_iff.mpr
    ⟨hr5, hrq, hE, hRE⟩, hEout⟩

/-- Coarse rooted count for absorber-induced outside parts.  A2 sharpens
this by controlling how many of the bounded-span configurations may use a
large absorber portion. -/
theorem card_absorberInducedExtensions_le_span
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V) :
    (absorberInducedExtensions q j B R).card ≤
      2 ^ (q ^ 3) *
        ((q - (verticesOn R).card + 1) *
          (((univ \ verticesOn R : Finset V).card + 1) ^
            (q - (verticesOn R).card))) := by
  calc
    (absorberInducedExtensions q j B R).card ≤
        ((erdosConfigExtensions q R).image (fun z ↦ z.2 \ B)).card :=
      card_le_card
        (absorberInducedExtensions_subset_image_erdosConfigExtensions
          q j B R)
    _ ≤ (erdosConfigExtensions q R).card := card_image_le
    _ ≤ _ := card_erdosConfigExtensions_le q R

end Erdos207

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
import ErdosProblems.Erdos722.ColoredTypicality
import ErdosProblems.Erdos722.RootedEmbedding
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Greedy embeddings into a simultaneously typical coloured host

This file packages the deterministic induction used after coloured
typicality.  A partial embedding is represented by a total vertex map which
is injective and realizes every constrained edge on an initial segment.
The next vertex imposes at most one coloured `(r-1)`-root for each pattern
edge, so the common-neighbour lemma extends the partial embedding.
-/

namespace Erdos722.ColoredEmbedding

open Finset
open Erdos722.Typicality
open Erdos722.ColoredTypicality

noncomputable section

/-- A finite `r`-uniform hypergraph whose edges have prescribed colours. -/
structure ColoredPattern (u v r : ℕ) where
  edges : Finset (Finset (Fin v))
  color : Finset (Fin v) → Fin u
  uniform : ∀ e ∈ edges, e.card = r

/-- Relabel a coloured pattern by a permutation of its vertex set.  A new
label `i` represents the old vertex `σ i`. -/
def ColoredPattern.relabel
    (P : ColoredPattern u v r) (σ : Fin v ≃ Fin v) :
    ColoredPattern u v r where
  edges := P.edges.image fun e ↦ e.map σ.symm.toEmbedding
  color := fun e ↦ P.color (e.map σ.toEmbedding)
  uniform := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.card_map]
    exact P.uniform e₀ he₀

lemma mem_relabel_edges
    {P : ColoredPattern u v r} {σ : Fin v ≃ Fin v}
    {e : Finset (Fin v)} :
    e ∈ (P.relabel σ).edges ↔
      ∃ e₀ ∈ P.edges, e = e₀.map σ.symm.toEmbedding := by
  constructor
  · intro he
    obtain ⟨e₀, he₀, heq⟩ :=
      Finset.mem_image.mp (show e ∈ P.edges.image
        (fun e ↦ e.map σ.symm.toEmbedding) from he)
    exact ⟨e₀, he₀, heq.symm⟩
  · rintro ⟨e₀, he₀, rfl⟩
    exact Finset.mem_image.mpr ⟨e₀, he₀, rfl⟩

@[simp] lemma relabel_color_map_symm
    (P : ColoredPattern u v r) (σ : Fin v ≃ Fin v)
    (e : Finset (Fin v)) :
    (P.relabel σ).color (e.map σ.symm.toEmbedding) = P.color e := by
  simp [ColoredPattern.relabel, Finset.map_map]

lemma image_trans_symm_eq
    (σ : Fin v ≃ Fin v) (ψ : Fin v ↪ Fin n)
    (e : Finset (Fin v)) :
    e.image (σ.symm.toEmbedding.trans ψ) =
      (e.map σ.symm.toEmbedding).image ψ := by
  classical
  have hmap : e.map σ.symm.toEmbedding = e.image σ.symm := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_map.mp hx
      obtain ⟨a, ha, hax⟩ := hx'
      apply Finset.mem_image.mpr
      exact ⟨a, ha, hax⟩
    · intro hx
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
      exact Finset.mem_map.mpr ⟨a, ha, hax⟩
  change e.image (fun a ↦ ψ (σ.symm a)) = _
  rw [hmap, Finset.image_image]
  rfl

/-- Turn the free edges of a rooted pattern into coloured constraints. -/
def coloredFreePattern
    (P : Erdos722.RootedEmbedding.RootedPattern v r)
    (color : Finset (Fin v) → Fin u) : ColoredPattern u v r where
  edges := P.freeEdges
  color := color
  uniform := by
    intro e he
    exact P.uniform e (Finset.mem_filter.mp he).1

/-- Vertices of the pattern already embedded before position `t`. -/
def initialVertices (v t : ℕ) : Finset (Fin v) :=
  (Finset.univ : Finset (Fin v)).filter fun x ↦ x.1 < t

lemma mem_initialVertices {x : Fin v} :
    x ∈ initialVertices v t ↔ x.1 < t := by
  simp [initialVertices]

lemma initialVertices_mono {s t : ℕ} (hst : s ≤ t) :
    initialVertices v s ⊆ initialVertices v t := by
  intro x hx
  exact mem_initialVertices.mpr ((mem_initialVertices.mp hx).trans_le hst)

lemma initialVertices_eq_map_castLE {s v : ℕ} (hsv : s ≤ v) :
    initialVertices v s =
      (Finset.univ : Finset (Fin s)).map (Fin.castLEEmb hsv) := by
  ext x
  constructor
  · intro hx
    have hxs : x.1 < s := mem_initialVertices.mp hx
    apply Finset.mem_map.mpr
    exact ⟨⟨x.1, hxs⟩, Finset.mem_univ _, by
      apply Fin.ext
      rfl⟩
  · intro hx
    obtain ⟨y, _hy, hxy⟩ := Finset.mem_map.mp hx
    have hval : x.1 = y.1 := congrArg Fin.val hxy.symm
    exact mem_initialVertices.mpr (by simpa [hval] using y.2)

lemma card_initialVertices {s v : ℕ} (hsv : s ≤ v) :
    (initialVertices v s).card = s := by
  rw [initialVertices_eq_map_castLE hsv, Finset.card_map]
  simp

/-- A permutation which puts any prescribed `s`-set into the first `s`
positions. -/
theorem exists_rootFirstPermutation
    {root : Finset (Fin v)} (hroot : root.card = s) (hsv : s ≤ v) :
    ∃ σ : Fin v ≃ Fin v,
      (initialVertices v s).map σ.toEmbedding = root := by
  exact Equiv.Perm.exists_map_finset_eq _ _
    ((card_initialVertices hsv).trans hroot.symm)

/-- A total map realizing the coloured pattern on the first `t` vertices. -/
def IsPartialEmbedding
    {u v r n : ℕ} (P : ColoredPattern u v r) (t : ℕ)
    (φ : Fin v → Fin n)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool) : Prop :=
  Set.InjOn φ (↑(initialVertices v t) : Set (Fin v)) ∧
    ∀ e ∈ P.edges, e ⊆ initialVertices v t →
      e.image φ ∈ sampledColorEdges u n r ω (P.color e)

/-- Pattern edges first completed when vertex `t` is embedded. -/
def newEdgesAt (P : ColoredPattern u v r) (t : Fin v) :
    Finset (Finset (Fin v)) :=
  P.edges.filter fun e ↦ t ∈ e ∧ e ⊆ initialVertices v (t.1 + 1)

/-- The coloured root faces imposed on the image of the next vertex. -/
def extensionRoots
    (P : ColoredPattern u v r) (t : Fin v) (φ : Fin v → Fin n) :
    Finset (ColoredRoot u n) :=
  (newEdgesAt P t).image fun e ↦
    (P.color e, (e.erase t).image φ)

lemma extensionRoots_card_le (P : ColoredPattern u v r)
    (t : Fin v) (φ : Fin v → Fin n) :
    (extensionRoots P t φ).card ≤ P.edges.card := by
  exact (Finset.card_image_le.trans
    (Finset.card_le_card (Finset.filter_subset _ _)))

lemma erase_subset_initial_of_mem_newEdgesAt
    {P : ColoredPattern u v r} {t : Fin v} {e : Finset (Fin v)}
    (he : e ∈ newEdgesAt P t) :
    e.erase t ⊆ initialVertices v t.1 := by
  intro x hx
  have heData := Finset.mem_filter.mp he
  have hxSucc := mem_initialVertices.mp (heData.2.2 (Finset.mem_of_mem_erase hx))
  have hne : x ≠ t := (Finset.mem_erase.mp hx).1
  exact mem_initialVertices.mpr (by omega)

lemma card_image_erase_of_partial
    {P : ColoredPattern u v r} {t : Fin v} {φ : Fin v → Fin n}
    (hpartial : IsPartialEmbedding P t.1 φ ω)
    {e : Finset (Fin v)} (he : e ∈ newEdgesAt P t) :
    ((e.erase t).image φ).card = r - 1 := by
  have heraseSub := erase_subset_initial_of_mem_newEdgesAt he
  have hinj : Set.InjOn φ (↑(e.erase t) : Set (Fin v)) := by
    intro x hx y hy hxy
    exact hpartial.1 (heraseSub hx) (heraseSub hy) hxy
  rw [Finset.card_image_iff.mpr (by
    intro x hx y hy hxy
    exact hinj (by simpa using hx) (by simpa using hy) hxy)]
  have heData := Finset.mem_filter.mp he
  rw [Finset.card_erase_of_mem heData.2.1, P.uniform e heData.1]

lemma extensionRoots_uniform
    {P : ColoredPattern u v r} {t : Fin v} {φ : Fin v → Fin n}
    (hpartial : IsPartialEmbedding P t.1 φ ω) :
    ∀ z ∈ extensionRoots P t φ, z.2.card = r - 1 := by
  intro z hz
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
  exact card_image_erase_of_partial hpartial he

lemma extensionRoots_mem_coloredRootFamilies
    {P : ColoredPattern u v r} {t : Fin v} {φ : Fin v → Fin n}
    (hpartial : IsPartialEmbedding P t.1 φ ω)
    {h : ℕ} (hedges : P.edges.card ≤ h) :
    extensionRoots P t φ ∈ coloredRootFamilies u n r h := by
  rw [mem_coloredRootFamilies]
  constructor
  · intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_univ _, mem_uniformEdges.mpr
      (card_image_erase_of_partial hpartial he)⟩
  · exact (extensionRoots_card_le P t φ).trans hedges

/-- Images of the already embedded initial segment. -/
def usedVertices (v t : ℕ) (φ : Fin v → Fin n) : Finset (Fin n) :=
  (initialVertices v t).image φ

lemma card_usedVertices_le (v t : ℕ) (φ : Fin v → Fin n) :
    (usedVertices v t φ).card ≤ v := by
  have himage : ((initialVertices v t).image φ).card ≤
      (initialVertices v t).card := Finset.card_image_le
  have hinit : (initialVertices v t).card ≤ v := by
    simpa using Finset.card_le_univ (initialVertices v t)
  exact himage.trans hinit

/-- Extend a total map at the next pattern vertex. -/
def extendMap (φ : Fin v → Fin n) (t : Fin v) (x : Fin n) : Fin v → Fin n :=
  Function.update φ t x

@[simp] lemma extendMap_apply_self (φ : Fin v → Fin n)
    (t : Fin v) (x : Fin n) : extendMap φ t x t = x := by
  simp [extendMap]

lemma extendMap_apply_of_ne (φ : Fin v → Fin n)
    (t y : Fin v) (x : Fin n) (hy : y ≠ t) :
    extendMap φ t x y = φ y := by
  simp [extendMap, hy]

lemma extendMap_injOn_next
    {P : ColoredPattern u v r} {t : Fin v} {φ : Fin v → Fin n}
    (hpartial : IsPartialEmbedding P t.1 φ ω)
    {x : Fin n} (hx : x ∉ usedVertices v t.1 φ) :
    Set.InjOn (extendMap φ t x)
      (↑(initialVertices v (t.1 + 1)) : Set (Fin v)) := by
  intro a ha b hb hab
  have haSucc : a.1 < t.1 + 1 := mem_initialVertices.mp ha
  have hbSucc : b.1 < t.1 + 1 := mem_initialVertices.mp hb
  by_cases hat : a = t
  · subst a
    by_cases hbt : b = t
    · exact hbt.symm
    · exfalso
      apply hx
      apply Finset.mem_image.mpr
      refine ⟨b, mem_initialVertices.mpr (by omega), ?_⟩
      simpa [extendMap_apply_of_ne φ t b x hbt] using hab.symm
  · by_cases hbt : b = t
    · subst b
      exfalso
      apply hx
      apply Finset.mem_image.mpr
      refine ⟨a, mem_initialVertices.mpr (by omega), ?_⟩
      simpa [extendMap_apply_of_ne φ t a x hat] using hab
    · apply hpartial.1
      · exact mem_initialVertices.mpr (by omega)
      · exact mem_initialVertices.mpr (by omega)
      · simpa [extendMap_apply_of_ne φ t a x hat,
          extendMap_apply_of_ne φ t b x hbt] using hab

lemma image_extendMap_eq_insert_image_erase
    (φ : Fin v → Fin n) (t : Fin v) (x : Fin n)
    {e : Finset (Fin v)} (ht : t ∈ e) :
    e.image (extendMap φ t x) = insert x ((e.erase t).image φ) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    by_cases hyt : y = t
    · subst y
      simpa using Finset.mem_insert_self x ((e.erase t).image φ)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨y, Finset.mem_erase.mpr ⟨hyt, hy⟩,
        extendMap_apply_of_ne φ t y x hyt |>.symm⟩
  · intro hz
    rcases Finset.mem_insert.mp hz with hzx | hz
    · subst z
      apply Finset.mem_image.mpr
      exact ⟨t, ht, extendMap_apply_self φ t x⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      have hyt : y ≠ t := (Finset.mem_erase.mp hy).1
      apply Finset.mem_image.mpr
      exact ⟨y, Finset.mem_of_mem_erase hy,
        extendMap_apply_of_ne φ t y x hyt⟩

lemma subset_initial_of_subset_next_not_mem
    {t : Fin v} {e : Finset (Fin v)}
    (hnext : e ⊆ initialVertices v (t.1 + 1)) (ht : t ∉ e) :
    e ⊆ initialVertices v t.1 := by
  intro y hy
  have hySucc := mem_initialVertices.mp (hnext hy)
  have hyt : y ≠ t := fun h ↦ ht (h ▸ hy)
  exact mem_initialVertices.mpr (by omega)

/-- One common-neighbour choice performs a valid one-vertex extension. -/
theorem isPartialEmbedding_extend
    {P : ColoredPattern u v r} {t : Fin v} {φ : Fin v → Fin n}
    (hpartial : IsPartialEmbedding P t.1 φ ω)
    {h : ℕ} (hedges : P.edges.card ≤ h)
    {x : cleanColoredVertices n (extensionRoots P t φ)}
    (hxCommon : x ∈ coloredCommonNeighbors u n r
      (extensionRoots P t φ) hr
      (extensionRoots_uniform hpartial) ω)
    (hxUnused : (x : Fin n) ∉ usedVertices v t.1 φ) :
    IsPartialEmbedding P (t.1 + 1) (extendMap φ t x) ω := by
  refine ⟨extendMap_injOn_next hpartial hxUnused, ?_⟩
  intro e heP heNext
  by_cases ht : t ∈ e
  · have heNew : e ∈ newEdgesAt P t :=
      Finset.mem_filter.mpr ⟨heP, ht, heNext⟩
    let roots := extensionRoots P t φ
    have hroots : roots ∈ coloredRootFamilies u n r h :=
      extensionRoots_mem_coloredRootFamilies hpartial hedges
    let z : {z // z ∈ roots} :=
      ⟨(P.color e, (e.erase t).image φ),
        Finset.mem_image.mpr ⟨e, heNew, rfl⟩⟩
    have hcoord := (mem_coloredCommonNeighbors hr
      (extensionRoots_uniform hpartial) ω).mp hxCommon z
    rw [image_extendMap_eq_insert_image_erase φ t x ht]
    apply mem_sampledColorEdges.mpr
    refine ⟨?_, ?_⟩
    · exact (coloredCommonEdgeCoord u n r roots hr
        (extensionRoots_uniform hpartial) ⟨x, z⟩).2.property
    · simpa [roots, z, coloredCommonEdgeCoord] using hcoord
  · have heOld := subset_initial_of_subset_next_not_mem heNext ht
    have hsample := hpartial.2 e heP heOld
    have himage : e.image (extendMap φ t x) = e.image φ := by
      apply Finset.image_congr
      intro y hy
      exact extendMap_apply_of_ne φ t y x (fun h ↦ ht (h ▸ hy))
    simpa [himage] using hsample

/-- Under lower typicality and the uniform mean bound, every partial
embedding extends by one vertex. -/
theorem exists_isPartialEmbedding_succ
    {P : ColoredPattern u v r} {t : ℕ} (ht : t < v)
    {φ : Fin v → Fin n} (hpartial : IsPartialEmbedding P t φ ω)
    {h : ℕ} (hedges : P.edges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      (v : ℝ) ≤ coloredCommonMean n roots p / 2) :
    ∃ φ' : Fin v → Fin n,
      IsPartialEmbedding P (t + 1) φ' ω ∧
      ∀ y ∈ initialVertices v t, φ' y = φ y := by
  let tv : Fin v := ⟨t, ht⟩
  let roots := extensionRoots P tv φ
  have hroots : roots ∈ coloredRootFamilies u n r h :=
    extensionRoots_mem_coloredRootFamilies hpartial hedges
  let avoid := usedVertices v t φ
  have havoidCard : (avoid.card : ℝ) ≤ v := by
    exact_mod_cast card_usedVertices_le v t φ
  have havoid : (avoid.card : ℝ) ≤ coloredCommonMean n roots p / 2 :=
    havoidCard.trans (hmean roots hroots)
  obtain ⟨x, hxCommon, hxAvoid⟩ :=
    exists_coloredCommonNeighbor_not_mem hr p ω htyp hroots avoid havoid
  refine ⟨extendMap φ tv x,
    isPartialEmbedding_extend hpartial hedges hxCommon hxAvoid, ?_⟩
  intro y hy
  apply extendMap_apply_of_ne
  intro hyt
  subst y
  have : tv.1 < t := mem_initialVertices.mp hy
  simp [tv] at this

/-- Iterating the one-vertex step extends a partial embedding through any
fixed number of further pattern vertices. -/
theorem exists_isPartialEmbedding_add
    {P : ColoredPattern u v r} {t d : ℕ} (htd : t + d ≤ v)
    {φ : Fin v → Fin n} (hpartial : IsPartialEmbedding P t φ ω)
    {h : ℕ} (hedges : P.edges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      (v : ℝ) ≤ coloredCommonMean n roots p / 2) :
    ∃ ψ : Fin v → Fin n,
      IsPartialEmbedding P (t + d) ψ ω ∧
      ∀ y ∈ initialVertices v t, ψ y = φ y := by
  induction d generalizing t φ with
  | zero =>
      exact ⟨φ, by simpa using hpartial, fun _ _ ↦ rfl⟩
  | succ d ih =>
      have ht : t < v := by omega
      obtain ⟨φ', hpartial', hagree⟩ :=
        exists_isPartialEmbedding_succ ht hpartial hedges hr p htyp hmean
      have hbound : (t + 1) + d ≤ v := by omega
      obtain ⟨ψ, hψ, hψagree⟩ :=
        ih hbound hpartial'
      refine ⟨ψ, by simpa [Nat.add_assoc, Nat.add_comm d 1] using hψ, ?_⟩
      intro y hy
      rw [hψagree y (initialVertices_mono (by omega) hy), hagree y hy]

/-- A partial embedding on an initial root segment extends to a full
embedding of every constrained coloured edge. -/
theorem exists_fullEmbedding_of_partial
    {P : ColoredPattern u v r} {s : ℕ} (hsv : s ≤ v)
    {φ : Fin v → Fin n} (hpartial : IsPartialEmbedding P s φ ω)
    {h : ℕ} (hedges : P.edges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      (v : ℝ) ≤ coloredCommonMean n roots p / 2) :
    ∃ ψ : Fin v ↪ Fin n,
      (∀ e ∈ P.edges,
        e.image ψ ∈ sampledColorEdges u n r ω (P.color e)) ∧
      ∀ y ∈ initialVertices v s, ψ y = φ y := by
  obtain ⟨ψ, hψ, hagree⟩ := exists_isPartialEmbedding_add
    (t := s) (d := v - s) (by omega) hpartial hedges hr p htyp hmean
  have hfull : s + (v - s) = v := Nat.add_sub_of_le hsv
  have hinj : Function.Injective ψ := by
    intro x y hxy
    apply hψ.1
    · simpa [hfull, initialVertices] using (Finset.mem_univ x)
    · simpa [hfull, initialVertices] using (Finset.mem_univ y)
    · exact hxy
  let ψ' : Fin v ↪ Fin n := ⟨ψ, hinj⟩
  refine ⟨ψ', ?_, ?_⟩
  · intro e he
    apply hψ.2 e he
    intro y hy
    exact mem_initialVertices.mpr (by omega)
  · exact hagree

/-- One extension step which also avoids a fixed finite set of ambient
vertices.  The forbidden set is charged only through its cardinality. -/
theorem exists_isPartialEmbedding_succ_avoiding
    {P : ColoredPattern u v r} {t : ℕ} (ht : t < v)
    {φ : Fin v → Fin n} (hpartial : IsPartialEmbedding P t φ ω)
    (forbiddenVertices : Finset (Fin n))
    {h : ℕ} (hedges : P.edges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      ((v + forbiddenVertices.card : ℕ) : ℝ) ≤
        coloredCommonMean n roots p / 2) :
    ∃ φ' : Fin v → Fin n,
      IsPartialEmbedding P (t + 1) φ' ω ∧
      (∀ y ∈ initialVertices v t, φ' y = φ y) ∧
      φ' ⟨t, ht⟩ ∉ forbiddenVertices := by
  let tv : Fin v := ⟨t, ht⟩
  let roots := extensionRoots P tv φ
  have hroots : roots ∈ coloredRootFamilies u n r h :=
    extensionRoots_mem_coloredRootFamilies hpartial hedges
  let avoid := usedVertices v t φ ∪ forbiddenVertices
  have havoidCardNat : avoid.card ≤ v + forbiddenVertices.card := by
    calc
      avoid.card ≤ (usedVertices v t φ).card + forbiddenVertices.card :=
        Finset.card_union_le _ _
      _ ≤ v + forbiddenVertices.card :=
        Nat.add_le_add_right (card_usedVertices_le v t φ) _
  have havoidCard : (avoid.card : ℝ) ≤
      ((v + forbiddenVertices.card : ℕ) : ℝ) := by
    exact_mod_cast havoidCardNat
  have havoid : (avoid.card : ℝ) ≤ coloredCommonMean n roots p / 2 :=
    havoidCard.trans (hmean roots hroots)
  obtain ⟨x, hxCommon, hxAvoid⟩ :=
    exists_coloredCommonNeighbor_not_mem hr p ω htyp hroots avoid havoid
  have hxUnused : (x : Fin n) ∉ usedVertices v t φ := by
    intro hx
    exact hxAvoid (Finset.mem_union_left _ hx)
  have hxForbidden : (x : Fin n) ∉ forbiddenVertices := by
    intro hx
    exact hxAvoid (Finset.mem_union_right _ hx)
  refine ⟨extendMap φ tv x,
    isPartialEmbedding_extend hpartial hedges hxCommon hxUnused, ?_, ?_⟩
  · intro y hy
    apply extendMap_apply_of_ne
    intro hyt
    subst y
    have : tv.1 < t := mem_initialVertices.mp hy
    simp [tv] at this
  · simpa [tv] using hxForbidden

/-- Iteration of the avoiding extension step.  Every newly embedded vertex
after the prescribed initial segment avoids the fixed forbidden set. -/
theorem exists_isPartialEmbedding_add_avoiding
    {P : ColoredPattern u v r} {t d : ℕ} (htd : t + d ≤ v)
    {φ : Fin v → Fin n} (hpartial : IsPartialEmbedding P t φ ω)
    (forbiddenVertices : Finset (Fin n))
    {h : ℕ} (hedges : P.edges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      ((v + forbiddenVertices.card : ℕ) : ℝ) ≤
        coloredCommonMean n roots p / 2) :
    ∃ ψ : Fin v → Fin n,
      IsPartialEmbedding P (t + d) ψ ω ∧
      (∀ y ∈ initialVertices v t, ψ y = φ y) ∧
      ∀ y : Fin v, t ≤ y.1 → y.1 < t + d →
        ψ y ∉ forbiddenVertices := by
  induction d generalizing t φ with
  | zero =>
      refine ⟨φ, by simpa using hpartial, fun _ _ ↦ rfl, ?_⟩
      intro y hyLower hyUpper
      omega
  | succ d ih =>
      have ht : t < v := by omega
      obtain ⟨φ', hpartial', hagree, hnewAvoid⟩ :=
        exists_isPartialEmbedding_succ_avoiding ht hpartial
          forbiddenVertices hedges hr p htyp hmean
      have hbound : (t + 1) + d ≤ v := by omega
      obtain ⟨ψ, hψ, hψagree, hψavoid⟩ :=
        ih hbound hpartial'
      refine ⟨ψ, by simpa [Nat.add_assoc, Nat.add_comm d 1] using hψ,
        ?_, ?_⟩
      · intro y hy
        rw [hψagree y (initialVertices_mono (by omega) hy), hagree y hy]
      · intro y hyLower hyUpper
        by_cases hyt : y.1 = t
        · have hyEq : y = (⟨t, ht⟩ : Fin v) := Fin.ext hyt
          rw [hψagree y (mem_initialVertices.mpr (by omega)), hyEq]
          exact hnewAvoid
        · apply hψavoid y
          · omega
          · omega

/-- Full avoiding extension of a partial embedding. -/
theorem exists_fullEmbedding_of_partial_avoiding
    {P : ColoredPattern u v r} {s : ℕ} (hsv : s ≤ v)
    {φ : Fin v → Fin n} (hpartial : IsPartialEmbedding P s φ ω)
    (forbiddenVertices : Finset (Fin n))
    {h : ℕ} (hedges : P.edges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      ((v + forbiddenVertices.card : ℕ) : ℝ) ≤
        coloredCommonMean n roots p / 2) :
    ∃ ψ : Fin v ↪ Fin n,
      (∀ e ∈ P.edges,
        e.image ψ ∈ sampledColorEdges u n r ω (P.color e)) ∧
      (∀ y ∈ initialVertices v s, ψ y = φ y) ∧
      ∀ y : Fin v, s ≤ y.1 → ψ y ∉ forbiddenVertices := by
  obtain ⟨ψ, hψ, hagree, havoid⟩ := exists_isPartialEmbedding_add_avoiding
    (t := s) (d := v - s) (by omega) hpartial forbiddenVertices
      hedges hr p htyp hmean
  have hfull : s + (v - s) = v := Nat.add_sub_of_le hsv
  have hinj : Function.Injective ψ := by
    intro x y hxy
    apply hψ.1
    · simpa [hfull, initialVertices] using (Finset.mem_univ x)
    · simpa [hfull, initialVertices] using (Finset.mem_univ y)
    · exact hxy
  let ψ' : Fin v ↪ Fin n := ⟨ψ, hinj⟩
  refine ⟨ψ', ?_, hagree, ?_⟩
  · intro e he
    apply hψ.2 e he
    intro y hy
    exact mem_initialVertices.mpr (by omega)
  · intro y hy
    exact havoid y hy (by omega)

/-- A free edge of a rooted pattern cannot become supported entirely on
the initial root segment after a root-first relabelling. -/
lemma relabeledFreeEdge_not_subset_initial
    {P : Erdos722.RootedEmbedding.RootedPattern v r}
    {color : Finset (Fin v) → Fin u} {σ : Fin v ≃ Fin v}
    {s : ℕ}
    (hroot : (initialVertices v s).map σ.toEmbedding = P.root)
    {e : Finset (Fin v)}
    (he : e ∈ ((coloredFreePattern P color).relabel σ).edges) :
    ¬e ⊆ initialVertices v s := by
  intro hesub
  obtain ⟨e₀, he₀, rfl⟩ := mem_relabel_edges.mp he
  have he₀free := Finset.mem_filter.mp he₀
  apply he₀free.2
  intro x hx
  have hy : σ.symm x ∈ e₀.map σ.symm.toEmbedding := by
    apply Finset.mem_map.mpr
    exact ⟨x, hx, by simp⟩
  have hyInit := hesub hy
  rw [← hroot]
  apply Finset.mem_map.mpr
  exact ⟨σ.symm x, hyInit, by simp⟩

/-- Simultaneous coloured typicality extends any injectively prescribed
root of a rooted uniform pattern. -/
theorem exists_rootedColoredEmbedding
    {P : Erdos722.RootedEmbedding.RootedPattern v r}
    (hsv : P.root.card ≤ v)
    (color : Finset (Fin v) → Fin u)
    (σ : Fin v ≃ Fin v)
    (hroot : (initialVertices v P.root.card).map σ.toEmbedding = P.root)
    (request : Erdos722.RootedEmbedding.RootRequest v n P.root)
    {h : ℕ} (hedges : P.freeEdges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      (v : ℝ) ≤ coloredCommonMean n roots p / 2) :
    ∃ ψ : Fin v ↪ Fin n,
      Erdos722.RootedEmbedding.ExtendsRequest P.root request ψ ∧
      ∀ e ∈ P.freeEdges,
        e.image ψ ∈ sampledColorEdges u n r ω (color e) := by
  let CP := (coloredFreePattern P color).relabel σ
  let φ : Fin v → Fin n := fun y ↦ request.map (σ y)
  have hpartial : IsPartialEmbedding CP P.root.card φ ω := by
    constructor
    · intro x hx y hy hxy
      apply σ.injective
      apply request.injOn
      · rw [← hroot]
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      · rw [← hroot]
        exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
      · exact hxy
    · intro e he hesub
      exact (relabeledFreeEdge_not_subset_initial hroot he hesub).elim
  have hCPedges : CP.edges.card ≤ h := by
    calc
      CP.edges.card ≤ (coloredFreePattern P color).edges.card :=
        Finset.card_image_le
      _ ≤ h := hedges
  obtain ⟨ψnew, hψedges, hψroot⟩ := exists_fullEmbedding_of_partial
    hsv hpartial hCPedges hr p htyp hmean
  let ψ : Fin v ↪ Fin n := σ.symm.toEmbedding.trans ψnew
  refine ⟨ψ, ?_, ?_⟩
  · intro x hx
    have hxMap : x ∈ (initialVertices v P.root.card).map σ.toEmbedding := by
      rw [hroot]
      exact hx
    obtain ⟨y, hyInit, hyx⟩ := Finset.mem_map.mp hxMap
    have hyEq : y = σ.symm x := by
      apply σ.injective
      simpa using hyx
    change ψnew (σ.symm x) = request.map x
    rw [← hyEq, hψroot y hyInit]
    exact congrArg request.map hyx
  · intro e he
    let enew := e.map σ.symm.toEmbedding
    have henew : enew ∈ CP.edges := by
      apply mem_relabel_edges.mpr
      exact ⟨e, he, rfl⟩
    have hsamp := hψedges enew henew
    simpa [ψ, CP, enew, coloredFreePattern, relabel_color_map_symm,
      image_trans_symm_eq] using hsamp

/-- Rooted coloured embedding with an additional finite avoidance set.  Only
vertices outside the prescribed root are required to avoid it. -/
theorem exists_rootedColoredEmbedding_avoiding
    {P : Erdos722.RootedEmbedding.RootedPattern v r}
    (hsv : P.root.card ≤ v)
    (color : Finset (Fin v) → Fin u)
    (σ : Fin v ≃ Fin v)
    (hroot : (initialVertices v P.root.card).map σ.toEmbedding = P.root)
    (request : Erdos722.RootedEmbedding.RootRequest v n P.root)
    (forbiddenVertices : Finset (Fin n))
    {h : ℕ} (hedges : P.freeEdges.card ≤ h)
    (hr : 0 < r) (p : Set.Icc (0 : ℝ) 1)
    (ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool)
    (htyp : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      coloredCommonMean n roots p / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ coloredCommonNeighborIndicator u n r roots hr
            (coloredRoot_card_of_mem hroots) x) ω <
        2 * coloredCommonMean n roots p)
    (hmean : ∀ roots, ∀ hroots : roots ∈ coloredRootFamilies u n r h,
      ((v + forbiddenVertices.card : ℕ) : ℝ) ≤
        coloredCommonMean n roots p / 2) :
    ∃ ψ : Fin v ↪ Fin n,
      Erdos722.RootedEmbedding.ExtendsRequest P.root request ψ ∧
      (∀ e ∈ P.freeEdges,
        e.image ψ ∈ sampledColorEdges u n r ω (color e)) ∧
      ∀ y : Fin v, y ∉ P.root → ψ y ∉ forbiddenVertices := by
  let CP := (coloredFreePattern P color).relabel σ
  let φ : Fin v → Fin n := fun y ↦ request.map (σ y)
  have hpartial : IsPartialEmbedding CP P.root.card φ ω := by
    constructor
    · intro x hx y hy hxy
      apply σ.injective
      apply request.injOn
      · rw [← hroot]
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      · rw [← hroot]
        exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
      · exact hxy
    · intro e he hesub
      exact (relabeledFreeEdge_not_subset_initial hroot he hesub).elim
  have hCPedges : CP.edges.card ≤ h := by
    calc
      CP.edges.card ≤ (coloredFreePattern P color).edges.card :=
        Finset.card_image_le
      _ ≤ h := hedges
  obtain ⟨ψnew, hψedges, hψroot, hψavoid⟩ :=
    exists_fullEmbedding_of_partial_avoiding hsv hpartial
      forbiddenVertices hCPedges hr p htyp hmean
  let ψ : Fin v ↪ Fin n := σ.symm.toEmbedding.trans ψnew
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x hx
    have hxMap : x ∈ (initialVertices v P.root.card).map σ.toEmbedding := by
      rw [hroot]
      exact hx
    obtain ⟨y, hyInit, hyx⟩ := Finset.mem_map.mp hxMap
    have hyEq : y = σ.symm x := by
      apply σ.injective
      simpa using hyx
    change ψnew (σ.symm x) = request.map x
    rw [← hyEq, hψroot y hyInit]
    exact congrArg request.map hyx
  · intro e he
    let enew := e.map σ.symm.toEmbedding
    have henew : enew ∈ CP.edges := by
      apply mem_relabel_edges.mpr
      exact ⟨e, he, rfl⟩
    have hsamp := hψedges enew henew
    simpa [ψ, CP, enew, coloredFreePattern, relabel_color_map_symm,
      image_trans_symm_eq] using hsamp
  · intro y hyRoot
    apply hψavoid (σ.symm y)
    by_contra hlt
    have hyInit : σ.symm y ∈ initialVertices v P.root.card :=
      mem_initialVertices.mpr (Nat.lt_of_not_ge hlt)
    apply hyRoot
    rw [← hroot]
    exact Finset.mem_map.mpr ⟨σ.symm y, hyInit, by simp⟩

/-- For every fixed coloured pattern, a sufficiently large ground set has
one sparse coloured host which extends every admissible prescribed initial
embedding of that pattern. -/
theorem eventually_exists_universalColoredHost
    (P : ColoredPattern u v r) (h D : ℕ)
    (hr : 0 < r) (hh : 0 < h) (hD : 0 < D) (hhD : h < D)
    (hedges : P.edges.card ≤ h) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ hn : 0 < n,
      ∃ ω : (Fin u × {e // e ∈ uniformEdges n r}) → Bool,
        (∀ i, sampledColorEdges u n r ω i ⊆ uniformEdges n r) ∧
        (∀ i I, I.card = r - 1 →
          ((sampledColorEdges u n r ω i).filter fun e ↦ I ⊆ e).card ^ D ≤
            2 ^ D * n ^ (D - 1)) ∧
        ∀ s, s ≤ v → ∀ φ : Fin v → Fin n,
          IsPartialEmbedding P s φ ω →
          ∃ ψ : Fin v ↪ Fin n,
            (∀ e ∈ P.edges,
              e.image ψ ∈ sampledColorEdges u n r ω (P.color e)) ∧
            ∀ y ∈ initialVertices v s, ψ y = φ y := by
  have hsample := eventually_exists_colored_typical_sample
    u r h D hr hh hD hhD
  have hmean := eventually_fixed_le_half_coloredCommonMean
    u r h D v hD hhD
  filter_upwards [hsample, hmean] with n hsample hmean
  obtain ⟨hn, ω, htyp, hsub, hdegree⟩ := hsample
  refine ⟨hn, ω, hsub, hdegree, ?_⟩
  intro s hsv φ hpartial
  exact exists_fullEmbedding_of_partial hsv hpartial hedges hr
    (Erdos722.Reserve.reserveProbabilityIcc n D hn) htyp
    (hmean hn)

end

end Erdos722.ColoredEmbedding

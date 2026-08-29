/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ExtensionClause
import Mathlib.SetTheory.Ordinal.FundamentalSequence

/-!
# Cofinal source layers for the singular extension step

This file constructs the concrete cofinal cardinal scale used by Assertion
9.17. The index type is the canonical type of the cofinality ordinal. We
discard an initial segment of a fundamental sequence so that every scale
cardinal dominates both `aleph_0` and the cardinality of the index type.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMatrix

universe u

/-- Canonical index type of size `cf kappa`. -/
abbrev Index (kappa : Cardinal.{u}) : Type u :=
  kappa.ord.cof.ord.ToType

/-- A chosen ordinal fundamental sequence cofinal in `kappa.ord`. -/
noncomputable def rawFundamental (kappa : Cardinal.{u}) :
    (i : Ordinal.{u}) → i < kappa.ord.cof.ord → Ordinal.{u} :=
  Classical.choose (Ordinal.exists_fundamental_sequence kappa.ord)

theorem rawFundamental_spec (kappa : Cardinal.{u}) :
    kappa.ord.IsFundamentalSequence kappa.ord.cof.ord
      (rawFundamental kappa) :=
  Classical.choose_spec (Ordinal.exists_fundamental_sequence kappa.ord)

/-- The ordinal rank of an index in the canonical cofinality order. -/
def indexRank (kappa : Cardinal.{u}) (i : Index kappa) : Ordinal.{u} :=
  Ordinal.typein (fun x y : Index kappa => x < y) i

theorem indexRank_lt (kappa : Cardinal.{u}) (i : Index kappa) :
    indexRank kappa i < kappa.ord.cof.ord := by
  simpa only [indexRank, Ordinal.type_toType] using
    Ordinal.typein_lt_type (fun x y : Index kappa => x < y) i

/-- Fundamental-sequence value at a canonical index. -/
def fundamentalAt (kappa : Cardinal.{u}) (i : Index kappa) : Ordinal.{u} :=
  rawFundamental kappa (indexRank kappa i) (indexRank_lt kappa i)

theorem fundamentalAt_lt (kappa : Cardinal.{u}) (i : Index kappa) :
    fundamentalAt kappa i < kappa.ord :=
  (rawFundamental_spec kappa).lt (indexRank_lt kappa i)

theorem fundamentalAt_strictMono (kappa : Cardinal.{u}) :
    StrictMono (fundamentalAt kappa) := by
  intro i j hij
  apply (rawFundamental_spec kappa).strict_mono
      (indexRank_lt kappa i) (indexRank_lt kappa j)
  exact (Ordinal.typein_lt_typein
    (fun x y : Index kappa => x < y)).2 hij

/-- Cardinal which every retained scale value must dominate. -/
def scaleFloor (kappa : Cardinal.{u}) : Cardinal.{u} :=
  max aleph0 kappa.ord.cof

theorem scaleFloor_lt (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    scaleFloor kappa < kappa :=
  max_lt huncountable hsingular.cof_ord_lt

/-- The ordinal index witnessing that the fundamental sequence has passed
the scale floor. -/
noncomputable def floorOrdinalIndex (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    Ordinal.{u} := by
  have hord : (scaleFloor kappa).ord < kappa.ord :=
    Cardinal.ord_lt_ord.2 (scaleFloor_lt kappa huncountable hsingular)
  have hbelow : (scaleFloor kappa).ord <
      Ordinal.blsub kappa.ord.cof.ord (rawFundamental kappa) := by
    simpa only [(rawFundamental_spec kappa).blsub_eq] using hord
  exact Classical.choose (Ordinal.lt_blsub_iff.1 hbelow)

theorem floorOrdinalIndex_lt (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    floorOrdinalIndex kappa huncountable hsingular <
      kappa.ord.cof.ord := by
  have hord : (scaleFloor kappa).ord < kappa.ord :=
    Cardinal.ord_lt_ord.2 (scaleFloor_lt kappa huncountable hsingular)
  have hbelow : (scaleFloor kappa).ord <
      Ordinal.blsub kappa.ord.cof.ord (rawFundamental kappa) := by
    simpa only [(rawFundamental_spec kappa).blsub_eq] using hord
  exact Classical.choose (Classical.choose_spec
    (Ordinal.lt_blsub_iff.1 hbelow))

theorem floorOrdinalIndex_bound (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    (scaleFloor kappa).ord ≤ rawFundamental kappa
      (floorOrdinalIndex kappa huncountable hsingular)
      (floorOrdinalIndex_lt kappa huncountable hsingular) := by
  have hord : (scaleFloor kappa).ord < kappa.ord :=
    Cardinal.ord_lt_ord.2 (scaleFloor_lt kappa huncountable hsingular)
  have hbelow : (scaleFloor kappa).ord <
      Ordinal.blsub kappa.ord.cof.ord (rawFundamental kappa) := by
    simpa only [(rawFundamental_spec kappa).blsub_eq] using hord
  exact Classical.choose_spec (Classical.choose_spec
    (Ordinal.lt_blsub_iff.1 hbelow))

/-- A canonical-type index corresponding to `floorOrdinalIndex`. -/
noncomputable def floorIndex (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    Index kappa :=
  Ordinal.enum (fun x y : Index kappa => x < y)
    ⟨floorOrdinalIndex kappa huncountable hsingular, by
      rw [Ordinal.type_toType]
      exact floorOrdinalIndex_lt kappa huncountable hsingular⟩

theorem floor_le_fundamentalAt_floorIndex (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    (scaleFloor kappa).ord ≤
      fundamentalAt kappa (floorIndex kappa huncountable hsingular) := by
  have hrank : indexRank kappa
      (floorIndex kappa huncountable hsingular) =
      floorOrdinalIndex kappa huncountable hsingular := by
    unfold indexRank floorIndex
    apply Ordinal.typein_enum
  simpa only [fundamentalAt, hrank] using
    floorOrdinalIndex_bound kappa huncountable hsingular

/-- Tail-shifted cofinal ordinal sequence. -/
def cutOrdinal (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) : Ordinal.{u} :=
  fundamentalAt kappa (max i (floorIndex kappa huncountable hsingular))

/-- The singular scale used in the matrix. -/
def scale (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) : Cardinal.{u} :=
  (cutOrdinal kappa huncountable hsingular i).card

theorem scale_mono (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    Monotone (scale kappa huncountable hsingular) := by
  intro i j hij
  apply Ordinal.card_le_card
  apply (fundamentalAt_strictMono kappa).monotone
  exact max_le_max hij le_rfl

theorem scale_infinite (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    aleph0 ≤ scale kappa huncountable hsingular i := by
  have hfloorOrd := floor_le_fundamentalAt_floorIndex kappa
    huncountable hsingular
  have htail : fundamentalAt kappa
      (floorIndex kappa huncountable hsingular) ≤
      cutOrdinal kappa huncountable hsingular i := by
    apply (fundamentalAt_strictMono kappa).monotone
    exact le_max_right _ _
  have hfloorCard : scaleFloor kappa ≤
      scale kappa huncountable hsingular i := by
    change scaleFloor kappa ≤
      (cutOrdinal kappa huncountable hsingular i).card
    simpa only [Cardinal.card_ord] using
      Ordinal.card_le_card (hfloorOrd.trans htail)
  exact (le_max_left aleph0 kappa.ord.cof).trans hfloorCard

theorem scale_index_le (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    #(Index kappa) ≤ scale kappa huncountable hsingular i := by
  rw [Cardinal.mk_toType, Cardinal.card_ord]
  have hfloorOrd := floor_le_fundamentalAt_floorIndex kappa
    huncountable hsingular
  have htail : fundamentalAt kappa
      (floorIndex kappa huncountable hsingular) ≤
      cutOrdinal kappa huncountable hsingular i := by
    apply (fundamentalAt_strictMono kappa).monotone
    exact le_max_right _ _
  have hfloorCard : scaleFloor kappa ≤
      scale kappa huncountable hsingular i := by
    change scaleFloor kappa ≤
      (cutOrdinal kappa huncountable hsingular i).card
    simpa only [Cardinal.card_ord] using
      Ordinal.card_le_card (hfloorOrd.trans htail)
  exact (le_max_right aleph0 kappa.ord.cof).trans hfloorCard

theorem scale_below (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    scale kappa huncountable hsingular i < kappa := by
  rw [scale]
  exact Cardinal.lt_ord.1 (fundamentalAt_lt kappa _)

theorem scale_cofinal (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {rho : Cardinal.{u}} (hrho : rho < kappa) :
    ∃ i : Index kappa, rho < scale kappa huncountable hsingular i := by
  have hsucc : succ rho < kappa := hsingular.isSuccLimit.succ_lt hrho
  have hord : (succ rho).ord < kappa.ord := Cardinal.ord_lt_ord.2 hsucc
  have hbelow : (succ rho).ord <
      Ordinal.blsub kappa.ord.cof.ord (rawFundamental kappa) := by
    simpa only [(rawFundamental_spec kappa).blsub_eq] using hord
  obtain ⟨j, hj, hle⟩ := Ordinal.lt_blsub_iff.1 hbelow
  let i0 : Index kappa := Ordinal.enum
    (fun x y : Index kappa => x < y)
    ⟨j, by rw [Ordinal.type_toType]; exact hj⟩
  let i := max i0 (floorIndex kappa huncountable hsingular)
  refine ⟨i, (lt_succ rho).trans_le ?_⟩
  rw [scale, cutOrdinal]
  have hjrank : indexRank kappa i0 = j := by
    unfold i0 indexRank
    apply Ordinal.typein_enum
  have hji : fundamentalAt kappa i0 ≤
      cutOrdinal kappa huncountable hsingular i := by
    unfold cutOrdinal
    apply (fundamentalAt_strictMono kappa).monotone
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hcard : succ rho ≤ (fundamentalAt kappa i0).card := by
    rw [← Cardinal.card_ord (succ rho)]
    exact Ordinal.card_le_card <| by
      simpa only [fundamentalAt, hjrank] using hle
  exact hcard.trans (Ordinal.card_le_card hji)

theorem scale_isCofinal (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    SingularCardinal.IsCofinalScale
      (scale kappa huncountable hsingular) kappa := by
  refine ⟨scale_mono kappa huncountable hsingular,
    scale_infinite kappa huncountable hsingular,
    scale_below kappa huncountable hsingular, ?_⟩
  intro rho hrho
  exact scale_cofinal kappa huncountable hsingular hrho

/-! ## Exact nested source layers -/

theorem cutOrdinal_lt (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    cutOrdinal kappa huncountable hsingular i < kappa.ord :=
  fundamentalAt_lt kappa _

theorem cutOrdinal_mono (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    Monotone (cutOrdinal kappa huncountable hsingular) := by
  intro i j hij
  apply (fundamentalAt_strictMono kappa).monotone
  exact max_le_max hij le_rfl

theorem cutOrdinal_cofinal (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {xi : Ordinal.{u}} (hxi : xi < kappa.ord) :
    ∃ i : Index kappa, xi < cutOrdinal kappa huncountable hsingular i := by
  have hxisucc : Order.succ xi < kappa.ord :=
    (Cardinal.isSuccLimit_ord huncountable.le).succ_lt hxi
  have hbelow : Order.succ xi <
      Ordinal.blsub kappa.ord.cof.ord (rawFundamental kappa) := by
    simpa only [(rawFundamental_spec kappa).blsub_eq] using hxisucc
  obtain ⟨j, hj, hle⟩ := Ordinal.lt_blsub_iff.1 hbelow
  let i0 : Index kappa := Ordinal.enum
    (fun x y : Index kappa => x < y)
    ⟨j, by rw [Ordinal.type_toType]; exact hj⟩
  let i := max i0 (floorIndex kappa huncountable hsingular)
  refine ⟨i, (Order.lt_succ xi).trans_le (hle.trans ?_)⟩
  unfold cutOrdinal
  have hjrank : indexRank kappa i0 = j := by
    unfold i0 indexRank
    apply Ordinal.typein_enum
  have hbase : rawFundamental kappa j hj = fundamentalAt kappa i0 := by
    simp only [fundamentalAt, hjrank]
  rw [hbase]
  apply (fundamentalAt_strictMono kappa).monotone
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- A chosen enumeration of a set of cardinality `kappa` by the canonical
well-order of cardinal `kappa`. -/
noncomputable def sourceEquiv {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa) :
    kappa.ord.ToType ≃ A₀ :=
  Classical.choice (Cardinal.eq.mp <| by
    rw [Cardinal.mk_toType, Cardinal.card_ord, hcard])

/-- Underlying vertex map of `sourceEquiv`. -/
noncomputable def sourceEnum {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa) :
    kappa.ord.ToType → V := fun x => (sourceEquiv A₀ kappa hcard x).1

theorem sourceEnum_injective {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa) :
    Function.Injective (sourceEnum A₀ kappa hcard) := by
  intro x y hxy
  apply (sourceEquiv A₀ kappa hcard).injective
  exact Subtype.ext hxy

theorem sourceEnum_mem {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa)
    (x : kappa.ord.ToType) :
    sourceEnum A₀ kappa hcard x ∈ A₀ :=
  (sourceEquiv A₀ kappa hcard x).2

/-- Endpoint of the initial segment which represents the `i`th scale
cardinal inside the canonical type of `kappa`. -/
noncomputable def sourceCutPoint (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) : kappa.ord.ToType :=
  Ordinal.enum (fun x y : kappa.ord.ToType => x < y)
    ⟨cutOrdinal kappa huncountable hsingular i, by
      rw [Ordinal.type_toType]
      exact cutOrdinal_lt kappa huncountable hsingular i⟩

theorem sourceCutPoint_typein (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    Ordinal.typein (fun x y : kappa.ord.ToType => x < y)
      (sourceCutPoint kappa huncountable hsingular i) =
      cutOrdinal kappa huncountable hsingular i := by
  unfold sourceCutPoint
  apply Ordinal.typein_enum

/-- The exact-cardinality nested exhaustion of `A₀` attached to the
cofinal scale. -/
noncomputable def sourceLayer {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) : Set V :=
  sourceEnum A₀ kappa hcard ''
    Set.Iio (sourceCutPoint kappa huncountable hsingular i)

theorem sourceLayer_subset {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    sourceLayer A₀ kappa hcard huncountable hsingular i ⊆ A₀ := by
  rintro _ ⟨x, _, rfl⟩
  exact sourceEnum_mem A₀ kappa hcard x

theorem sourceLayer_card {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (i : Index kappa) :
    #(sourceLayer A₀ kappa hcard huncountable hsingular i) =
      scale kappa huncountable hsingular i := by
  rw [sourceLayer, Cardinal.mk_image_eq
    (sourceEnum_injective A₀ kappa hcard)]
  calc
    #(Set.Iio (sourceCutPoint kappa huncountable hsingular i)) =
        (Ordinal.typein (fun x y : kappa.ord.ToType => x < y)
          (sourceCutPoint kappa huncountable hsingular i)).card :=
      (Ordinal.card_typein (r := fun x y : kappa.ord.ToType => x < y)
        (sourceCutPoint kappa huncountable hsingular i)).symm
    _ = scale kappa huncountable hsingular i := by
      rw [sourceCutPoint_typein, scale]

theorem sourceLayer_mono {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    Monotone (sourceLayer A₀ kappa hcard huncountable hsingular) := by
  intro i j hij
  apply Set.image_mono
  intro x hx
  have hxrank : Ordinal.typein
      (fun x y : kappa.ord.ToType => x < y) x <
      cutOrdinal kappa huncountable hsingular i := by
    rw [← sourceCutPoint_typein kappa huncountable hsingular i]
    rwa [Ordinal.typein_lt_typein]
  have hxrank' := hxrank.trans_le
    (cutOrdinal_mono kappa huncountable hsingular hij)
  change x < sourceCutPoint kappa huncountable hsingular j
  rw [← Ordinal.typein_lt_typein
    (fun x y : kappa.ord.ToType => x < y)]
  simpa only [sourceCutPoint_typein] using hxrank'

theorem sourceLayer_cover {V : Type u} (A₀ : Set V)
    (kappa : Cardinal.{u}) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular) :
    ⋃ i, sourceLayer A₀ kappa hcard huncountable hsingular i = A₀ := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i => sourceLayer_subset A₀ kappa hcard
      huncountable hsingular i
  · intro a ha
    let x : kappa.ord.ToType :=
      (sourceEquiv A₀ kappa hcard).symm ⟨a, ha⟩
    have hxrank : Ordinal.typein
        (fun x y : kappa.ord.ToType => x < y) x < kappa.ord := by
      simpa only [Ordinal.type_toType] using
        Ordinal.typein_lt_type (fun x y : kappa.ord.ToType => x < y) x
    obtain ⟨i, hi⟩ := cutOrdinal_cofinal kappa huncountable hsingular hxrank
    apply Set.mem_iUnion.2
    refine ⟨i, ?_⟩
    refine ⟨x, ?_, ?_⟩
    · change x < sourceCutPoint kappa huncountable hsingular i
      rw [← Ordinal.typein_lt_typein
        (fun x y : kappa.ord.ToType => x < y)]
      simpa only [sourceCutPoint_typein] using hi
    · change (sourceEquiv A₀ kappa hcard x).1 = a
      exact congrArg Subtype.val <|
        (sourceEquiv A₀ kappa hcard).apply_symm_apply ⟨a, ha⟩

/-! ## The recursive source rows -/

/-- Competitor closure never creates anything except an initial vertex of
the ambient path family. -/
theorem competitorClosure_subset_initialSet {V : Type u} (G : DWeb V)
    (W : Set G.DPath) (S : Set V) :
    G.competitorClosure W S ⊆ G.initialSet W := by
  rintro b ⟨a, ha, p, hp, hpa, q, hq, hqb, hpq⟩
  exact ⟨q, hq, hqb⟩

/-- The rows obtained by applying the source's competitor-closing operation
once after every path column.  The path family used in a closing step is
global in the scale index, exactly as in Assertion 9.17. -/
def matrixSources {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V) :
    I → ℕ → Set V
  | i, 0 => initial i
  | i, n + 1 => G.competitorStep (G.matrixStageFamily fixed paths n)
      (matrixSources G fixed paths initial i n)

@[simp] theorem matrixSources_zero {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V) (i : I) :
    matrixSources G fixed paths initial i 0 = initial i := rfl

@[simp] theorem matrixSources_succ {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (i : I) (n : ℕ) :
    matrixSources G fixed paths initial i (n + 1) =
      G.competitorStep (G.matrixStageFamily fixed paths n)
        (matrixSources G fixed paths initial i n) := rfl

theorem matrixSources_subset_succ {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (i : I) (n : ℕ) :
    matrixSources G fixed paths initial i n ⊆
      matrixSources G fixed paths initial i (n + 1) := by
  intro x hx
  exact Or.inl hx

theorem matrixSources_mono_stage {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V) (i : I) :
    Monotone (matrixSources G fixed paths initial i) := by
  apply monotone_nat_of_le_succ
  exact matrixSources_subset_succ G fixed paths initial i

theorem matrixSources_mono_index {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (hinitial : Monotone initial) (n : ℕ) :
    Monotone fun i => matrixSources G fixed paths initial i n := by
  intro i j hij
  induction n with
  | zero => exact hinitial hij
  | succ n ih =>
      exact G.competitorStep_mono (G.matrixStageFamily fixed paths n) ih

theorem matrixStageFamily_initialSet_subset_source
    {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath)
    (hfixed : G.initialSet fixed ⊆ G.source)
    (hpaths : ∀ i n, G.initialSet (paths i n) ⊆ G.source)
    (n : ℕ) :
    G.initialSet (G.matrixStageFamily fixed paths n) ⊆ G.source := by
  rintro x ⟨p, hp, rfl⟩
  rcases hp with hp | hp
  · exact hfixed ⟨p, hp, rfl⟩
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
    exact hpaths i n ⟨p, hpi, rfl⟩

theorem matrixSources_subset_source
    {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (hinitial : ∀ i, initial i ⊆ G.source)
    (hfixed : G.initialSet fixed ⊆ G.source)
    (hpaths : ∀ i n, G.initialSet (paths i n) ⊆ G.source) :
    ∀ i n, matrixSources G fixed paths initial i n ⊆ G.source := by
  intro i n
  induction n with
  | zero => exact hinitial i
  | succ n ih =>
      apply Set.union_subset ih
      exact (competitorClosure_subset_initialSet G
        (G.matrixStageFamily fixed paths n)
        (matrixSources G fixed paths initial i n)).trans
        (matrixStageFamily_initialSet_subset_source G fixed paths
          hfixed hpaths n)

theorem matrixSources_card
    {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (kappa : I → Cardinal.{u})
    (hfixed : G.IsWarp fixed)
    (hpaths : ∀ i n, G.IsWarp (paths i n))
    (hinfinite : ∀ i, aleph0 ≤ kappa i)
    (hindex : ∀ i, #I ≤ kappa i)
    (hcard : ∀ i, #(initial i) = kappa i) :
    ∀ i n, #(matrixSources G fixed paths initial i n) = kappa i := by
  intro i n
  induction n with
  | zero => exact hcard i
  | succ n ih =>
      apply le_antisymm
      · refine (Cardinal.mk_union_le _ _).trans ?_
        apply Cardinal.add_le_of_le (hinfinite i) ih.le
        apply G.mk_competitorClosure_fixed_iUnion_le fixed
          (fun j => paths j n) (matrixSources G fixed paths initial i n)
          hfixed (fun j => hpaths j n) (hinfinite i) (hindex i)
        exact ih.le
      · rw [← ih]
        exact Cardinal.mk_subtype_mono <|
          matrixSources_subset_succ G fixed paths initial i n

theorem matrixSources_close_succ
    {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (i : I) (n : ℕ) :
    G.competitorClosure (G.matrixStageFamily fixed paths n)
      (matrixSources G fixed paths initial i n) ⊆
      matrixSources G fixed paths initial i (n + 1) := by
  intro x hx
  exact Or.inr hx

/-- Constructor for the complete competitor matrix once the genuinely
graph-theoretic path rows have been selected.  All source/cardinal/closure
fields are discharged by the preceding bookkeeping lemmas. -/
noncomputable def competitorMatrixOfPaths
    {V : Type u} {I : Type u} [Preorder I]
    (G : DWeb V) (fixed : Set G.DPath)
    (paths : I → ℕ → Set G.DPath) (initial : I → Set V)
    (kappa : I → Cardinal.{u}) (A₀ : Set V)
    (Qualified : Set V → Cardinal.{u} → Set G.DPath → Prop)
    (hfixedWarp : G.IsWarp fixed)
    (hfixedFinite : G.HasFiniteCharacter fixed)
    (hfixedInitial : G.initialSet fixed = G.source \ A₀)
    (hfixedTarget : G.terminalFrontier fixed ⊆ G.target)
    (hinitialSource : ∀ i, initial i ⊆ G.source)
    (hinitialCard : ∀ i, #(initial i) = kappa i)
    (hinitialMono : Monotone initial)
    (hinitialCover : ⋃ i, initial i = A₀)
    (hkappaInfinite : ∀ i, aleph0 ≤ kappa i)
    (hindex : ∀ i, #I ≤ kappa i)
    (hpathsWarp : ∀ i n, G.IsWarp (paths i n))
    (hpathsFinite : ∀ i n, G.HasFiniteCharacter (paths i n))
    (hpathsInitial : ∀ i n, G.initialSet (paths i n) = G.source)
    (hqualified : ∀ i n, Qualified
      (matrixSources G fixed paths initial i n) (kappa i) (paths i n))
    (htarget : ∀ i n a,
      a ∈ matrixSources G fixed paths initial i n →
      Nonempty (G.TargetSegment (paths i n)
        (matrixSources G fixed paths initial i n) a))
    (hforward : ∀ i n,
      G.ForwardExtension (paths i n) (paths i (n + 1))) :
    SingularCardinal.CompetitorMatrix (I := I) G kappa A₀ Qualified where
  fixed := fixed
  fixed_isWarp := hfixedWarp
  fixed_finite := hfixedFinite
  fixed_initial := hfixedInitial
  fixed_target := hfixedTarget
  sources := matrixSources G fixed paths initial
  paths := paths
  sources_subset_source := matrixSources_subset_source G fixed paths initial
    hinitialSource (hfixedInitial.le.trans Set.diff_subset) (fun i n => by
      rw [hpathsInitial i n])
  sources_card := matrixSources_card G fixed paths initial kappa
    hfixedWarp hpathsWarp hkappaInfinite hindex hinitialCard
  sources_mono_stage := matrixSources_mono_stage G fixed paths initial
  sources_mono_index := matrixSources_mono_index G fixed paths initial
    hinitialMono
  paths_isWarp := hpathsWarp
  paths_finite := hpathsFinite
  paths_initial := hpathsInitial
  qualified := hqualified
  target_segment := htarget
  forward := hforward
  cover := hinitialCover
  close_succ := matrixSources_close_succ G fixed paths initial

end SingularMatrix
end CardinalInduction
end Erdos599

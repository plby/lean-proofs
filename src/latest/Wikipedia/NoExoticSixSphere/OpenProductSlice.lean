import Wikipedia.NoExoticSixSphere.OpenFiberCollapse

/-!
# Restricting an open product tube to an exact time slice

The time-level preimage is required to be exactly a base subset times the
whole fiber. The restricted tube is then an open embedding in the spatial
slice, and its collapse is exactly the corresponding restriction of the
original collapse, including at infinity.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.OpenProductSlice

variable {M K T Y : Type*} (τ : M × K → T × Y) (S : Set M)

def slice (p : S × K) : Y := (τ (p.1.val, p.2)).2

variable {τ S} {t : T}
  (ht : ∀ m k, (τ (m, k)).1 = t ↔ m ∈ S)

include ht

theorem pair_slice (p : S × K) : τ (p.1.val, p.2) = (t, slice τ S p) :=
  Prod.ext ((ht p.1.val p.2).mpr p.1.property) rfl

theorem injective_slice (hi : Injective τ) : Injective (slice τ S) := by
  intro p q he
  have hτ : τ (p.1.val, p.2) = τ (q.1.val, q.2) := by
    rw [pair_slice ht p, pair_slice ht q, he]
  have h := hi hτ
  have hb := congrArg (fun z : M × K ↦ z.1) h
  have hk := congrArg (fun z : M × K ↦ z.2) h
  exact Prod.ext (Subtype.ext hb) hk

section Topology

variable [TopologicalSpace M] [TopologicalSpace K] [TopologicalSpace T] [TopologicalSpace Y]

omit ht in
theorem continuous_slice (hc : Continuous τ) : Continuous (slice τ S) :=
  continuous_snd.comp (hc.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

theorem isOpenMap_slice (ho : IsOpenMap τ) : IsOpenMap (slice τ S) := by
  let i : S × K → M × K := fun p ↦ (p.1.val, p.2)
  have hi : IsInducing i :=
    (IsEmbedding.subtypeVal.prodMap (Homeomorph.refl K).isEmbedding).isInducing
  intro U hU
  obtain ⟨V, hV, hVU⟩ := hi.isOpen_iff.mp hU
  have he : slice τ S '' U = (fun y ↦ (t, y)) ⁻¹' (τ '' V) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(p.1.val, p.2), ?_, pair_slice ht p⟩
      have hpV : p ∈ i ⁻¹' V := hVU ▸ hp
      exact hpV
    · rintro ⟨⟨m, k⟩, hmkV, hmk⟩
      have htime : (τ (m, k)).1 = t := congrArg Prod.fst hmk
      let p : S × K := (⟨m, (ht m k).mp htime⟩, k)
      refine ⟨p, ?_, ?_⟩
      · rw [← hVU]
        exact hmkV
      · exact congrArg Prod.snd hmk
  rw [he]
  exact (ho V hV).preimage (continuous_const.prodMk continuous_id)

theorem isOpenEmbedding_slice (hτ : IsOpenEmbedding τ) : IsOpenEmbedding (slice τ S) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_slice hτ.continuous)
    (injective_slice ht hτ.injective) (isOpenMap_slice ht hτ.isOpenMap)

end Topology

theorem collapse_slice (hi : Injective τ) (y : Y) :
    OpenFiberCollapse.collapse τ (t, y) = OpenFiberCollapse.collapse (slice τ S) y := by
  by_cases hy : y ∈ range (slice τ S)
  · obtain ⟨p, rfl⟩ := hy
    rw [← pair_slice ht p, OpenFiberCollapse.collapse_apply τ hi,
      OpenFiberCollapse.collapse_apply _ (injective_slice ht hi)]
  · have hty : (t, y) ∉ range τ := by
      rintro ⟨⟨m, k⟩, hmk⟩
      have htime : (τ (m, k)).1 = t := congrArg Prod.fst hmk
      apply hy
      exact ⟨(⟨m, (ht m k).mp htime⟩, k), congrArg Prod.snd hmk⟩
    rw [OpenFiberCollapse.collapse_of_not_mem τ hty,
      OpenFiberCollapse.collapse_of_not_mem _ hy]

end NoExoticSixSphere.OpenProductSlice

namespace NoExoticSixSphere.OpenProductSlice.ProductBase

variable {T M K Y : Type*} (τ : (T × M) × K → T × Y)

def slice (t : T) (p : M × K) : Y := (τ ((t, p.1), p.2)).2

variable (ht : ∀ p, (τ p).1 = p.1.1)

include ht

theorem pair_slice (t : T) (p : M × K) : τ ((t, p.1), p.2) = (t, slice τ t p) :=
  Prod.ext (ht _) rfl

theorem injective_slice (hi : Injective τ) (t : T) : Injective (slice τ t) := by
  intro p q h
  have hpq := congrArg (fun y : Y ↦ (t, y)) h
  have he := hi ((pair_slice τ ht t p).trans
    (hpq.trans (pair_slice τ ht t q).symm))
  exact congrArg (fun z : (T × M) × K ↦ (z.1.2, z.2)) he

theorem collapse_slice (hi : Injective τ) (t : T) (y : Y) :
    OpenFiberCollapse.collapse τ (t, y) = OpenFiberCollapse.collapse (slice τ t) y := by
  by_cases hy : y ∈ range (slice τ t)
  · obtain ⟨p, rfl⟩ := hy
    rw [← pair_slice τ ht t p, OpenFiberCollapse.collapse_apply τ hi,
      OpenFiberCollapse.collapse_apply _ (injective_slice τ ht hi t)]
  · have hty : (t, y) ∉ range τ := by
      rintro ⟨⟨⟨s, m⟩, k⟩, h⟩
      have he : s = t := (ht ((s, m), k)).symm.trans (congrArg Prod.fst h)
      subst s
      exact hy ⟨(m, k), congrArg Prod.snd h⟩
    rw [OpenFiberCollapse.collapse_of_not_mem τ hty,
      OpenFiberCollapse.collapse_of_not_mem _ hy]

end NoExoticSixSphere.OpenProductSlice.ProductBase

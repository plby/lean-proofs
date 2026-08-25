import StackExchange.Puzzling139335.CentralRotation.DecreasingLift
import Wikipedia.SchoenfliesTheorem.Subarc

/-! # Closed and open subarcs in a circle parametrization -/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation

/-- Evaluate a circle parametrization at a real lift of the parameter. -/
def circleParam {X : Type*} (f : AddCircle (1 : ℝ) → X) (t : ℝ) : X :=
  f (t : AddCircle (1 : ℝ))

theorem continuous_circleParam {X : Type*} [TopologicalSpace X]
    {f : AddCircle (1 : ℝ) → X} (hf : Continuous f) : Continuous (circleParam f) :=
  hf.comp (AddCircle.continuous_mk' 1)

/-- A circle embedding is injective on every real interval shorter than one period. -/
theorem circleParam_injOn_Icc {X : Type*} {f : AddCircle (1 : ℝ) → X}
    (hf : Function.Injective f) {a b : ℝ} (hshort : b < a + 1) :
    InjOn (circleParam f) (Icc a b) := by
  intro s hs t ht heq
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show s ∈ Ico a (a + 1) from ⟨hs.1, hs.2.trans_lt hshort⟩)
    (show t ∈ Ico a (a + 1) from ⟨ht.1, ht.2.trans_lt hshort⟩)).mp (hf heq)

/-- Every nondegenerate interval shorter than one period parametrizes a simple arc. -/
theorem isArcBetween_circleParam {f : AddCircle (1 : ℝ) → Plane}
    (hfc : Continuous f) (hfi : Function.Injective f) {a b : ℝ}
    (hab : a < b) (hshort : b < a + 1) :
    IsArcBetween (circleParam f '' Icc a b) (circleParam f a) (circleParam f b) := by
  have himage : reparam a b '' I = Icc a b := by
    rw [image_reparam_I, uIcc_of_le hab.le]
  have hmaps : MapsTo (reparam a b) I (Icc a b) := mapsTo_iff_image_subset.mpr himage.subset
  refine ⟨circleParam f ∘ reparam a b,
    ((continuous_circleParam hfc).comp continuous_reparam).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy heq
    exact reparam_injective hab.ne
      (circleParam_injOn_Icc hfi hshort (hmaps hx) (hmaps hy) heq)
  · rw [image_comp, himage]
  · simp only [Function.comp_apply, reparam_zero]
  · simp only [Function.comp_apply, reparam_one]

/-- Deleting the endpoints agrees exactly with using the open parameter interval. -/
theorem circleParam_image_Ioo {X : Type*} {f : AddCircle (1 : ℝ) → X}
    (hf : Function.Injective f) {a b : ℝ} (hab : a < b) (hshort : b < a + 1) :
    circleParam f '' Ioo a b =
      circleParam f '' Icc a b \ {circleParam f a, circleParam f b} := by
  have hparam : Ioo a b = Icc a b \ {a, b} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro ht
      exact ⟨⟨ht.1.le, ht.2.le⟩, ht.1.ne', ht.2.ne⟩
    · rintro ⟨ht, hta, htb⟩
      exact ⟨lt_of_le_of_ne ht.1 (fun h => hta h.symm), lt_of_le_of_ne ht.2 htb⟩
  have hends : ({a, b} : Set ℝ) ⊆ Icc a b :=
    pair_subset (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  rw [hparam, (circleParam_injOn_Icc hf hshort).image_sdiff_subset hends, image_pair]

/-- The image of a continuous circle embedding is a Jordan curve. -/
theorem isJordanCurve_range_circle {f : AddCircle (1 : ℝ) → Plane}
    (hfc : Continuous f) (hfi : Function.Injective f) : IsJordanCurve (range f) := by
  refine ⟨circleParam f, ⟨(continuous_circleParam hfc).continuousOn, ?_, ?_⟩, ?_⟩
  · apply congrArg f
    exact (AddCircle.coe_period (1 : ℝ)).symm
  · intro s hs t ht heq
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa only [zero_add] using hs) (by simpa only [zero_add] using ht)).mp (hfi heq)
  · apply Subset.antisymm
    · rintro _ ⟨t, _, rfl⟩
      exact mem_range_self (t : AddCircle (1 : ℝ))
    · rintro _ ⟨z, rfl⟩
      let t : ℝ := AddCircle.equivIco (1 : ℝ) 0 z
      have ht : t ∈ Ico (0 : ℝ) 1 := by
        simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).property
      refine ⟨t, Ico_subset_Icc_self ht, ?_⟩
      dsimp only [circleParam, t]
      rw [AddCircle.coe_equivIco]

end Puzzling139335.CentralRotation

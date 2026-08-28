import Wikipedia.SmoothSixDPoincare.FlowCollarRescaling
import Mathlib.Topology.Separation.Hausdorff

/-!
# Homeomorphism by rescaling a compact flow collar

Surjectivity is proved by lengthening the same trajectory segment. Thus
the continuous injective rescaling is an actual homeomorphism onto the
intermediate absorbing region, not merely a homotopy equivalence.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {X : Type*} [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
  (d : FlowCollarData F A B)

/-- Every point of the intermediate region is the image of a rescaled trajectory. -/
theorem exists_rescale_eq (y : B) (hy : y.1 ∈ A) : ∃ x : B, d.rescale x = y := by
  by_cases hs : d.duration y = 0
  · exact ⟨y, d.rescale_eq_self_of_duration_eq_zero y hs⟩
  have hspos : 0 < d.duration y := lt_of_le_of_ne (d.duration_nonneg y) (Ne.symm hs)
  let r := d.duration y / d.factor y
  have hr₀ : 0 ≤ r := (div_pos hspos (d.factor_pos y)).le
  have hrT : r ≤ d.time := (div_le_iff₀ (d.factor_pos y)).mpr
    (d.duration_le_retained y hy)
  have hr : r * d.factor y = d.duration y :=
    div_mul_cancel₀ _ (d.factor_pos y).ne'
  have hsr : d.duration y ≤ r := by
    have hh := mul_le_mul_of_nonneg_left (d.factor_le_one y) hr₀
    rwa [mul_one, hr] at hh
  let x : B := ⟨F (d.time - r) (d.origin y).1,
    d.forward_outer _ (d.origin y).2 _ (sub_nonneg.mpr hrT)⟩
  have hxy : F (r - d.duration y) x.1 = y.1 := by
    change F (r - d.duration y) (F (d.time - r) (d.origin y).1) = y.1
    rw [← F.map_add]
    convert d.origin_reconstruct y using 2
    ring
  have hdx : d.duration x = r := by
    have hh := entryTime_eq_add_of_flow_pos F d.closed_core d.forward_core
      (d.hits_core x.2) (sub_nonneg.mpr hsr)
      (show 0 < entryTime F d.core (F (r - d.duration y) x.1) by
        rw [hxy]; exact hspos)
    rw [hxy] at hh
    change d.duration x = r - d.duration y + d.duration y at hh
    linarith
  have hox : d.origin x = d.origin y := by
    apply Subtype.ext
    change F (d.duration x - d.time) (F (d.time - r) (d.origin y).1) = _
    rw [hdx, ← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]
  have hfx : d.factor x = d.factor y := by
    unfold factor delay
    rw [hox]
  refine ⟨x, Subtype.ext ?_⟩
  rw [d.rescale_from_origin, hdx, hfx, hox, hr, d.origin_reconstruct]

/-- The rescaling with its actual intermediate-region codomain. -/
def innerMap : C(B, A) where
  toFun x := ⟨(d.rescale x).1, d.rescale_mem_inner x⟩
  continuous_toFun := (continuous_subtype_val.comp d.rescale.continuous).subtype_mk _

theorem innerMap_bijective : Function.Bijective d.innerMap := by
  constructor
  · intro x y h
    apply d.rescale_injective
    exact Subtype.ext (congrArg (fun z : A => (z : X)) h)
  · intro y
    obtain ⟨x, hx⟩ := d.exists_rescale_eq ⟨y.1, d.inner_subset y.2⟩ y.2
    exact ⟨x, Subtype.ext (congrArg (fun z : B => (z : X)) hx)⟩

/-- A compact flow collar shrinks homeomorphically onto its absorbing intermediate region. -/
def homeomorph [T2Space X] [CompactSpace B] : B ≃ₜ A :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective d.innerMap d.innerMap_bijective) d.innerMap.continuous

/-- The constructed homeomorphism fixes every point in the inner core. -/
theorem homeomorph_fixed_on_core [T2Space X] [CompactSpace B]
    (x : B) (hx : x.1 ∈ d.core) : (d.homeomorph x).1 = x.1 := by
  change (d.rescale x).1 = x.1
  have ht : d.duration x = 0 := entryTime_eq_zero F hx
  exact congrArg Subtype.val (d.rescale_eq_self_of_duration_eq_zero x ht)

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

import Wikipedia.NoExoticSixSphere.ReflectionQuotientCoordinate
import Mathlib.Tactic.Linarith

/-!
# A genuine half-line chart on the involution quotient

The quotient coordinate is the absolute value of the original real
coordinate. Its inverse sends a nonnegative coordinate to the orbit of the
original inverse-chart point. The image of the invariant source is open in
the actual quotient topology, yielding an open partial homeomorphism.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.InvolutionQuotient

variable {X : Type*} [TopologicalSpace X] {σ : X → X}

theorem ReflectionChart.inverse_coordinate_proj (c : ReflectionChart σ) (hσ : Involutive σ)
    {x : X} (hx : x ∈ c.coord.source) :
    proj σ hσ (c.coord.symm (c.coordinate hσ (proj σ hσ x)).val) = proj σ hσ x := by
  rw [c.coordinate_proj_val hσ hx]
  by_cases h : 0 ≤ c.coord x
  · rw [abs_of_nonneg h, c.coord.left_inv hx]
  · rw [abs_of_neg (lt_of_not_ge h), ← c.coordinate_swap x hx,
      c.coord.left_inv (c.source_invariant x hx), proj_swap]

def ReflectionChart.quotientChart (c : ReflectionChart σ) (hσ : Involutive σ)
    (hcont : Continuous σ) : OpenPartialHomeomorph (Orbit σ hσ) HalfLine where
  toFun := c.coordinate hσ
  invFun r := proj σ hσ (c.coord.symm r.val)
  source := proj σ hσ '' c.coord.source
  target := Subtype.val ⁻¹' c.coord.target
  map_source' r hr := by
    obtain ⟨x, hx, rfl⟩ := hr
    change (c.coordinate hσ (proj σ hσ x)).val ∈ c.coord.target
    rw [c.coordinate_proj_val hσ hx]
    exact c.abs_mem_target hx
  map_target' r hr := ⟨c.coord.symm r.val, c.coord.map_target hr, rfl⟩
  left_inv' r hr := by
    obtain ⟨x, hx, rfl⟩ := hr
    exact c.inverse_coordinate_proj hσ hx
  right_inv' r hr := by
    apply Subtype.ext
    rw [c.coordinate_proj_val hσ (c.coord.map_target hr),
      c.coord.right_inv hr, abs_of_nonneg r.property]
  open_source := (isOpenQuotientMap_proj σ hσ hcont).isOpenMap _ c.coord.open_source
  open_target := c.coord.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact (c.continuousAt_coordinate hσ hcont hx).continuousWithinAt
  continuousOn_invFun := (continuous_proj σ hσ).comp_continuousOn
    (c.coord.symm.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hr ↦ hr))

theorem ReflectionChart.quotientChart_source (c : ReflectionChart σ) (hσ : Involutive σ)
    (hcont : Continuous σ) :
    (c.quotientChart hσ hcont).source = proj σ hσ '' c.coord.source := rfl

theorem ReflectionChart.quotientChart_target (c : ReflectionChart σ) (hσ : Involutive σ)
    (hcont : Continuous σ) :
    (c.quotientChart hσ hcont).target = Subtype.val ⁻¹' c.coord.target := rfl

theorem ReflectionChart.quotientChart_apply (c : ReflectionChart σ) (hσ : Involutive σ)
    (hcont : Continuous σ) {x : X} (hx : x ∈ c.coord.source) :
    ((c.quotientChart hσ hcont) (proj σ hσ x)).val = |c.coord x| :=
  c.coordinate_proj_val hσ hx

theorem ReflectionChart.quotientChart_center (c : ReflectionChart σ) (hσ : Involutive σ)
    (hcont : Continuous σ) {x : X} (hx : x ∈ c.coord.source) (hz : c.coord x = 0) :
    proj σ hσ x ∈ (c.quotientChart hσ hcont).source ∧
      (c.quotientChart hσ hcont) (proj σ hσ x) = ⟨0, le_rfl⟩ := by
  refine ⟨⟨x, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [c.quotientChart_apply hσ hcont hx, hz, abs_zero]

theorem ReflectionChart.coord_zero_iff_fixed (c : ReflectionChart σ) {x : X}
    (hx : x ∈ c.coord.source) : c.coord x = 0 ↔ σ x = x := by
  constructor
  · intro hz
    apply c.coord.injOn (c.source_invariant x hx) hx
    rw [c.coordinate_swap x hx, hz, neg_zero]
  · intro hfix
    have he := c.coordinate_swap x hx
    rw [hfix] at he
    linarith

theorem ReflectionChart.quotientChart_zero_iff_fixed (c : ReflectionChart σ)
    (hσ : Involutive σ) (hcont : Continuous σ) {x : X} (hx : x ∈ c.coord.source) :
    ((c.quotientChart hσ hcont) (proj σ hσ x)).val = 0 ↔ σ x = x := by
  rw [c.quotientChart_apply hσ hcont hx, abs_eq_zero]
  exact c.coord_zero_iff_fixed hx

end NoExoticSixSphere.InvolutionQuotient

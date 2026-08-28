import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith

/-!
# The original outside-radius inclusion is a homotopy equivalence

On a product with a normed vector space, expand a nonzero normal vector
by adding the prescribed nonnegative radius to its norm. The original
radial interpolation stays nonzero, and stays outside the radius when
started there. Both homotopies retain the base point exactly.
-/

noncomputable section

open Function Set ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialExterior

variable (B E : Type) [TopologicalSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E]

def outside (r : ℝ) : Set (B × E) := {p | r < ‖p.2‖}

def expansion (r : ℝ) : C(unitInterval × outside B E 0, B × E) where
  toFun p := (p.2.val.1, (1 + p.1.val * r / ‖p.2.val.2‖) • p.2.val.2)
  continuous_toFun := by
    have hv : Continuous (fun p : unitInterval × outside B E 0 ↦ p.2.val.2) :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
    have ht : Continuous (fun p : unitInterval × outside B E 0 ↦ p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hn : ∀ p : unitInterval × outside B E 0, ‖p.2.val.2‖ ≠ 0 :=
      fun p ↦ ne_of_gt p.2.property
    exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      ((continuous_const.add ((ht.mul continuous_const).div hv.norm hn)).smul hv)

variable (r : ℝ) (hr : 0 ≤ r)

include hr in
theorem expansion_norm (s : unitInterval) (p : outside B E 0) :
    ‖(expansion B E r (s, p)).2‖ = ‖p.val.2‖ + s.val * r := by
  have hnonneg : 0 ≤ 1 + s.val * r / ‖p.val.2‖ :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg s.property.1 hr) (norm_nonneg _))
  change ‖(1 + s.val * r / ‖p.val.2‖) • p.val.2‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, add_mul, one_mul,
    div_mul_cancel₀ _ (ne_of_gt p.property)]

def inclusion : C(outside B E r, outside B E 0) :=
  ⟨fun p ↦ ⟨p.val, hr.trans_lt p.property⟩, continuous_subtype_val.subtype_mk _⟩

include hr in
theorem expansion_one_mem (p : outside B E 0) :
    expansion B E r (1, p) ∈ outside B E r := by
  change r < ‖(expansion B E r (1, p)).2‖
  rw [expansion_norm B E r hr]
  change r < ‖p.val.2‖ + 1 * r
  have hp : 0 < ‖p.val.2‖ := p.property
  linarith only [hp]

def outward : C(outside B E 0, outside B E r) where
  toFun p := ⟨expansion B E r (1, p), expansion_one_mem B E r hr p⟩
  continuous_toFun := ((expansion B E r).continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

theorem expansion_zero (p : outside B E 0) : expansion B E r (0, p) = p.val := by
  apply Prod.ext
  · rfl
  · change (1 + (0 : ℝ) * r / ‖p.val.2‖) • p.val.2 = p.val.2
    simp

include hr in
theorem expansion_zero_mem (s : unitInterval) (p : outside B E 0) :
    expansion B E r (s, p) ∈ outside B E 0 := by
  change 0 < ‖(expansion B E r (s, p)).2‖
  rw [expansion_norm B E r hr]
  exact p.property.trans_le (le_add_of_nonneg_right (mul_nonneg s.property.1 hr))

theorem expansion_outside_mem (s : unitInterval) (p : outside B E r) :
    expansion B E r (s, inclusion B E r hr p) ∈ outside B E r := by
  change r < ‖(expansion B E r (s, inclusion B E r hr p)).2‖
  rw [expansion_norm B E r hr]
  exact p.property.trans_le (le_add_of_nonneg_right (mul_nonneg s.property.1 hr))

def zeroSlide : (ContinuousMap.id (outside B E 0)).Homotopy
    ((inclusion B E r hr).comp (outward B E r hr)) where
  toFun p := ⟨expansion B E r p, expansion_zero_mem B E r hr p.1 p.2⟩
  continuous_toFun := (expansion B E r).continuous.subtype_mk _
  map_zero_left p := Subtype.ext (expansion_zero B E r p)
  map_one_left _ := rfl

def outsideSlide : (ContinuousMap.id (outside B E r)).Homotopy
    ((outward B E r hr).comp (inclusion B E r hr)) where
  toFun p := ⟨expansion B E r (p.1, inclusion B E r hr p.2),
    expansion_outside_mem B E r hr p.1 p.2⟩
  continuous_toFun := ((expansion B E r).continuous.comp
    (continuous_fst.prodMk ((inclusion B E r hr).continuous.comp continuous_snd))).subtype_mk _
  map_zero_left p := Subtype.ext (expansion_zero B E r (inclusion B E r hr p))
  map_one_left _ := rfl

def homotopyEquiv : outside B E r ≃ₕ outside B E 0 where
  toFun := inclusion B E r hr
  invFun := outward B E r hr
  left_inv := ⟨(outsideSlide B E r hr).symm⟩
  right_inv := ⟨(zeroSlide B E r hr).symm⟩

theorem inclusion_homology_bijective (n : ℕ) :
    Bijective (SingularMayerVietoris.singularHomologyMap (inclusion B E r hr) n) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (homotopyEquiv B E r hr) n).bijective

end Wikipedia.HopfProblem.DegreeCollapse.RadialExterior

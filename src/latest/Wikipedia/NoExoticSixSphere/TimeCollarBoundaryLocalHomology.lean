import Wikipedia.NoExoticSixSphere.TimeCollarCompactCores
import Wikipedia.NoExoticSixSphere.RelativeHomologyAcyclic
import Wikipedia.NoExoticSixSphere.RelativeCoefficientSequence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Vanishing of the actual half's local homology at its boundary

The existing collar push moves every point strictly inward at positive
homotopy times. It restricts to the complement of any boundary point and
makes the original puncture inclusion a homotopy equivalence. Actual pair
and coefficient sequences then give local homology vanishing in all degrees.
-/

noncomputable section

open Set Function ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem halfSlide_mem_interior_of_pos (p : NonnegativeHalf t)
    (u : unitInterval) (hu : 0 < (u : ℝ)) :
    C.halfInteriorSlideMap (u, p) ∈ interiorDomain C := by
  change 0 < t (C.halfInteriorClamp (u, p)).val
  rw [C.halfInteriorClamp_time]
  change 0 < (1 - (u : ℝ)) * t p.val + (u : ℝ) * max (t p.val) (C.width / 2)
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr u.property.2) p.property)
    (mul_pos hu ((half_pos C.width_pos).trans_le (le_max_right _ _)))

theorem exists_interior_mem_open (O : Set (NonnegativeHalf t)) (hO : IsOpen O)
    (p : NonnegativeHalf t) (hp : p ∈ O) :
    ∃ y : NonnegativeHalf t, y ∈ O ∧ y ∈ interiorDomain C := by
  let f : C(unitInterval, NonnegativeHalf t) := C.halfInteriorSlideMap.comp
    ⟨fun u ↦ (u, p), continuous_id.prodMk continuous_const⟩
  have hzero : (0 : unitInterval) ∈ f ⁻¹' O := by
    have he : C.halfInteriorSlideMap (0, p) = p := C.halfInteriorSlide.map_zero_left p
    change C.halfInteriorSlideMap (0, p) ∈ O
    rw [he]
    exact hp
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp ((hO.preimage f.continuous).mem_nhds hzero)
  let r : ℝ := min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hε) (by norm_num)
  let u : unitInterval := ⟨r, hr.le, (min_le_right _ _).trans (by norm_num)⟩
  have hu : u ∈ Metric.ball (0 : unitInterval) ε := by
    change |r - 0| < ε
    rw [sub_zero, abs_of_pos hr]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  exact ⟨f u, hball hu, halfSlide_mem_interior_of_pos C p u hr⟩

variable (w : boundary t)

theorem halfSlide_ne_boundary_of_pos (p : NonnegativeHalf t)
    (u : unitInterval) (hu : 0 < (u : ℝ)) : C.halfInteriorSlideMap (u, p) ≠ w.val := by
  intro he
  have hi : w.val ∈ interiorDomain C := he ▸ halfSlide_mem_interior_of_pos C p u hu
  exact (ne_of_gt hi) w.property

theorem halfSlide_preserves_boundary_puncture
    (p : ({w.val}ᶜ : Set (NonnegativeHalf t))) (u : unitInterval) :
    C.halfInteriorSlideMap (u, p.val) ∈ ({w.val}ᶜ : Set (NonnegativeHalf t)) := by
  change C.halfInteriorSlideMap (u, p.val) ≠ w.val
  by_cases hu : u = 0
  · subst u
    have he : C.halfInteriorSlideMap (0, p.val) = p.val :=
      C.halfInteriorSlide.map_zero_left p.val
    rw [he]
    exact p.property
  · have hu' : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
      intro he
      exact hu (Subtype.ext he.symm))
    exact halfSlide_ne_boundary_of_pos C w p.val u hu'

def puncturePush : C(NonnegativeHalf t, ({w.val}ᶜ : Set (NonnegativeHalf t))) where
  toFun p := ⟨C.halfInteriorSlideMap (1, p),
    halfSlide_ne_boundary_of_pos C w p 1 (by norm_num)⟩
  continuous_toFun := (C.halfInteriorSlideMap.continuous.comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

def punctureDeformation :
    (ContinuousMap.id ({w.val}ᶜ : Set (NonnegativeHalf t))).Homotopy
      ((puncturePush C w).comp (subtypeInclusion ({w.val}ᶜ : Set (NonnegativeHalf t)))) where
  toFun p := ⟨C.halfInteriorSlideMap (p.1, p.2.val),
    halfSlide_preserves_boundary_puncture C w p.2 p.1⟩
  continuous_toFun := (C.halfInteriorSlideMap.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := Subtype.ext (C.halfInteriorSlide.map_zero_left p.val)
  map_one_left _ := rfl

def boundaryPunctureHomotopyEquiv : ({w.val}ᶜ : Set (NonnegativeHalf t)) ≃ₕ NonnegativeHalf t where
  toFun := subtypeInclusion ({w.val}ᶜ : Set (NonnegativeHalf t))
  invFun := puncturePush C w
  left_inv := ⟨(punctureDeformation C w).symm⟩
  right_inv := ⟨C.halfInteriorSlide.symm⟩

theorem boundaryPunctureHomotopyEquiv_toFun :
    (boundaryPunctureHomotopyEquiv C w).toFun =
      subtypeInclusion ({w.val}ᶜ : Set (NonnegativeHalf t)) := rfl

include C in
theorem boundaryLocalIntegralHomology_subsingleton (n : ℕ) :
    Subsingleton (RelativeSingularHomology.Homology ({w.val}ᶜ : Set (NonnegativeHalf t)) n) :=
  RelativeSingularHomology.subsingleton_of_inclusion_bijective
    ({w.val}ᶜ : Set (NonnegativeHalf t))
    (fun q ↦ (homotopyEquivHomologyEquiv (boundaryPunctureHomotopyEquiv C w) q).bijective) n

include C in
theorem boundaryLocalModHomology_subsingleton (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    Subsingleton (RelativeCoefficients.ModHomology p ({w.val}ᶜ : Set (NonnegativeHalf t)) n) := by
  let := boundaryLocalIntegralHomology_subsingleton C w n
  cases n with
  | zero => exact (RelativeCoefficients.reductionMap_zero_surjective p hp
      ({w.val}ᶜ : Set (NonnegativeHalf t))).subsingleton
  | succ n =>
    let := boundaryLocalIntegralHomology_subsingleton C w n
    exact (RelativeCoefficients.reductionMap_surjective_of_subsingleton p hp
      ({w.val}ᶜ : Set (NonnegativeHalf t)) n).subsingleton

end NoExoticSixSphere.TimeCollarDuality

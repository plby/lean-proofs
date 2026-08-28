import Wikipedia.NoExoticSixSphere.SphereHeadReflection

/-!
# An actual three-piece open cover of the source sphere

The middle lies in the existing cylinder chart with time between minus four
and four. Its overlaps with the two cap regions have time beyond plus or
minus two, where the capped neck is exactly linear. The actual poles belong
to the cap regions and do not belong to the middle.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def neckRegion : Set (Sphere 3) :=
  {x | |x.val 0| < 4 * ‖SphereCylinder.tail 2 x.val‖}

def northRegion : Set (Sphere 3) :=
  {x | 2 * ‖SphereCylinder.tail 2 x.val‖ < x.val 0}

def southRegion : Set (Sphere 3) :=
  {x | 2 * ‖SphereCylinder.tail 2 x.val‖ < -x.val 0}

theorem continuous_sourceHead : Continuous (fun x : Sphere 3 ↦ x.val 0) :=
  (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val

theorem continuous_sourceTailNorm :
    Continuous (fun x : Sphere 3 ↦ ‖SphereCylinder.tail 2 x.val‖) :=
  ((SphereCylinder.tail 2).continuous.comp continuous_subtype_val).norm

theorem isOpen_neckRegion : IsOpen neckRegion :=
  isOpen_lt continuous_sourceHead.abs (continuous_const.mul continuous_sourceTailNorm)

theorem isOpen_northRegion : IsOpen northRegion :=
  isOpen_lt (continuous_const.mul continuous_sourceTailNorm) continuous_sourceHead

theorem isOpen_southRegion : IsOpen southRegion :=
  isOpen_lt (continuous_const.mul continuous_sourceTailNorm) continuous_sourceHead.neg

theorem neckRegion_mem_band {x : Sphere 3} (hx : x ∈ neckRegion) : x ∈ SphereCylinder.band 2 := by
  intro hz
  change |x.val 0| < 4 * ‖SphereCylinder.tail 2 x.val‖ at hx
  rw [hz, norm_zero, mul_zero] at hx
  exact (not_lt_of_ge (abs_nonneg _)) hx

theorem northRegion_head_pos {x : Sphere 3} (hx : x ∈ northRegion) : 0 < x.val 0 := by
  change 2 * ‖SphereCylinder.tail 2 x.val‖ < x.val 0 at hx
  linarith [norm_nonneg (SphereCylinder.tail 2 x.val)]

theorem southRegion_head_neg {x : Sphere 3} (hx : x ∈ southRegion) : x.val 0 < 0 := by
  change 2 * ‖SphereCylinder.tail 2 x.val‖ < -x.val 0 at hx
  linarith [norm_nonneg (SphereCylinder.tail 2 x.val)]

theorem neckRegion_time {x : Sphere 3} (hx : x ∈ neckRegion) :
    (SphereCylinder.inverse 2 x).1 ∈ Ioo (-4 : ℝ) 4 := by
  have hn := norm_pos_iff.mpr (neckRegion_mem_band hx)
  change |x.val 0| < 4 * ‖SphereCylinder.tail 2 x.val‖ at hx
  change -4 < x.val 0 / ‖SphereCylinder.tail 2 x.val‖ ∧
    x.val 0 / ‖SphereCylinder.tail 2 x.val‖ < 4
  rw [lt_div_iff₀ hn, div_lt_iff₀ hn]
  constructor <;> linarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]

theorem northRegion_time {x : Sphere 3} (hx : x ∈ northRegion)
    (hb : x ∈ SphereCylinder.band 2) : 2 < (SphereCylinder.inverse 2 x).1 := by
  change 2 < x.val 0 / ‖SphereCylinder.tail 2 x.val‖
  exact (lt_div_iff₀ (norm_pos_iff.mpr hb)).mpr hx

theorem southRegion_time {x : Sphere 3} (hx : x ∈ southRegion)
    (hb : x ∈ SphereCylinder.band 2) : (SphereCylinder.inverse 2 x).1 < -2 := by
  change x.val 0 / ‖SphereCylinder.tail 2 x.val‖ < -2
  apply (div_lt_iff₀ (norm_pos_iff.mpr hb)).mpr
  change 2 * ‖SphereCylinder.tail 2 x.val‖ < -x.val 0 at hx
  linarith

theorem sourceRegion_cover (x : Sphere 3) :
    x ∈ neckRegion ∨ x ∈ northRegion ∨ x ∈ southRegion := by
  by_cases hb : x ∈ neckRegion
  · exact Or.inl hb
  right
  have hlarge : 4 * ‖SphereCylinder.tail 2 x.val‖ ≤ |x.val 0| := le_of_not_gt hb
  have hnonzero : x.val 0 ≠ 0 ∨ SphereCylinder.tail 2 x.val ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz := join_head_tail x.val
    rw [hn.1, hn.2] at hz
    have he : SphereCylinder.join 2 (0, (0 : Vector 3)) = 0 :=
      (SphereCylinder.join 2).map_zero
    rw [he] at hz
    exact ne_zero_of_mem_unit_sphere x hz.symm
  by_cases hs : 0 ≤ x.val 0
  · left
    change 2 * ‖SphereCylinder.tail 2 x.val‖ < x.val 0
    rw [abs_of_nonneg hs] at hlarge
    rcases hnonzero with hh | ht
    · have hp := lt_of_le_of_ne hs (Ne.symm hh)
      linarith
    · linarith [norm_pos_iff.mpr ht]
  · right
    change 2 * ‖SphereCylinder.tail 2 x.val‖ < -x.val 0
    rw [abs_of_neg (lt_of_not_ge hs)] at hlarge
    linarith

end NoExoticSixSphere.SphereSumNeck

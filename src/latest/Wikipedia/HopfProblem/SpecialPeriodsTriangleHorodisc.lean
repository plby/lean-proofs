import Wikipedia.HopfProblem.SpecialPeriodsTriangleShimizu
import Wikipedia.HopfProblem.SpecialPeriodsTriangleFundamentalRegion
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspStabilizer

/-!
# High horodiscs for the actual triangle matrix group

The proved Shimizu bound forces every group element with nonzero lower
left entry to send a point above height `width` below that height.
Consequently an intersection of two sufficiently high horodiscs forces
the translating matrix to fix the cusp at infinity.  No cusp separation
or precisely-invariant-neighborhood hypothesis is used.
-/

noncomputable section

open Set UpperHalfPlane Matrix
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def horodisc (Y : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | Y < z.im}, isOpen_lt continuous_const continuous_im⟩

@[simp] theorem mem_horodisc (Y : ℝ) (z : ℍ) : z ∈ horodisc Y ↔ Y < z.im := Iff.rfl

theorem normSq_slDenom_lower_bound (A : SL(2, ℝ)) (z : ℍ) :
    (A 1 0) ^ 2 * z.im ^ 2 ≤ Complex.normSq (slDenom A z) := by
  have he : Complex.normSq (slDenom A z) =
      (A 1 0 * z.re + A 1 1) ^ 2 + (A 1 0 * z.im) ^ 2 := by
    simp [slDenom, Complex.normSq_apply, pow_two]
  rw [he]
  nlinarith [sq_nonneg (A 1 0 * z.re + A 1 1)]

/-- The actual height bound for every triangle matrix not fixing infinity. -/
theorem matrixGroup_nonparabolic_im_bound (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hc : A 1 0 ≠ 0) (z : ℍ) : (A • z).im ≤ width ^ 2 / z.im := by
  have hlow := matrixGroup_lower_left_bound A hA hc
  have hmul : 1 ≤ |A 1 0| * width := (div_le_iff₀ width_pos).mp hlow
  have hsq : 1 ≤ (A 1 0) ^ 2 * width ^ 2 := by
    have hs := sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (abs_nonneg (A 1 0)) width_pos.le) |>.mpr hmul
    simpa only [one_pow, mul_pow, sq_abs] using hs
  have hn := normSq_slDenom_lower_bound A z
  have hden := Complex.normSq_pos.mpr (slDenom_ne_zero A z)
  rw [sl_im]
  apply (div_le_iff₀ hden).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ z.im_pos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hn (sq_nonneg width)
  have h₂ := mul_le_mul_of_nonneg_right hsq (sq_nonneg z.im)
  nlinarith

theorem matrixGroup_nonparabolic_above_width (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hc : A 1 0 ≠ 0) (z : ℍ) (hz : width < z.im) : (A • z).im < width := by
  apply lt_of_le_of_lt (matrixGroup_nonparabolic_im_bound A hA hc z)
  apply (div_lt_iff₀ z.im_pos).mpr
  nlinarith [width_pos]

theorem matrixGroup_nonparabolic_disjoint_horodisc (Y : ℝ) (hY : width ≤ Y)
    (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) :
    Disjoint ((fun z : ℍ => A • z) '' (horodisc Y : Set ℍ)) (horodisc Y) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨z, hz, rfl⟩ hw
  have hlow := matrixGroup_nonparabolic_above_width A hA hc z (hY.trans_lt hz)
  exact (not_lt_of_ge (le_trans hlow.le hY)) hw

/-- A translated high horodisc can meet itself only for an actual
upper-triangular matrix, i.e. a transformation fixing the cusp. -/
theorem matrixGroup_horodisc_overlap_lower_left_zero (Y : ℝ) (hY : width ≤ Y)
    (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hinter : ((fun z : ℍ => A • z) '' (horodisc Y : Set ℍ) ∩ horodisc Y).Nonempty) :
    A 1 0 = 0 := by
  by_contra hc
  exact (Set.disjoint_iff_inter_eq_empty.mp
    (matrixGroup_nonparabolic_disjoint_horodisc Y hY A hA hc)) ▸ hinter |>.ne_empty rfl

theorem horodisc_nonempty (Y : ℝ) : (horodisc Y : Set ℍ).Nonempty := by
  let z : ℍ := ⟨((max Y 0 + 1 : ℝ) : ℂ) * Complex.I, by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    linarith [le_max_right Y 0]⟩
  refine ⟨z, ?_⟩
  change Y < (((max Y 0 + 1 : ℝ) : ℂ) * Complex.I).im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero]
  linarith [le_max_left Y 0]

theorem cusp_horodisc_invariant (Y : ℝ)
    (g : Subgroup.zpowers triangleCuspGenerator) :
    MapsTo (fun z : ℍ => triangleGeometricRepresentation (g : TriangleGroup) z)
      (horodisc Y) (horodisc Y) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  intro z hz
  change Y < (triangleGeometricRepresentation (g : TriangleGroup) z).im
  rw [← hn, triangleGeometricRepresentation_cusp_zpow_apply, vadd_im]
  exact hz

/-- The high horodisc is precisely invariant under the actual primitive
cusp subgroup of the full triangle action. -/
theorem triangle_horodisc_overlap_mem_cusp (Y : ℝ) (hY : width ≤ Y) (g : TriangleGroup)
    (hinter : ((triangleGeometricRepresentation g) '' (horodisc Y : Set ℍ) ∩
      horodisc Y).Nonempty) : g ∈ Subgroup.zpowers triangleCuspGenerator := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  apply (triangleGeometric_upperTriangular_lift_iff g A hA).mp
  apply matrixGroup_horodisc_overlap_lower_left_zero Y hY A A.property
  have he : (fun z : ℍ => (A : SL(2, ℝ)) • z) = triangleGeometricRepresentation g := by
    funext z
    change realSLPermutation A z = triangleGeometricRepresentation g z
    rw [hA]
  simpa only [he] using hinter

theorem triangle_horodisc_return_iff (Y : ℝ) (hY : width ≤ Y) (g : TriangleGroup) :
    ((triangleGeometricRepresentation g) '' (horodisc Y : Set ℍ) ∩ horodisc Y).Nonempty ↔
      g ∈ Subgroup.zpowers triangleCuspGenerator := by
  refine ⟨triangle_horodisc_overlap_mem_cusp Y hY g, ?_⟩
  intro hg
  obtain ⟨z, hz⟩ := horodisc_nonempty Y
  exact ⟨triangleGeometricRepresentation g z, ⟨z, hz, rfl⟩,
    cusp_horodisc_invariant Y ⟨g, hg⟩ hz⟩

/-- A finite continuous bound for the imaginary parts of an entire orbit. -/
def orbitHeightBound (z : ℍ) : ℝ := max z.im (width ^ 2 / z.im)

theorem orbitHeightBound_continuous : Continuous orbitHeightBound :=
  continuous_im.max (continuous_const.div continuous_im (fun z => z.im_ne_zero))

theorem matrixGroup_im_le_orbitHeightBound (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) (z : ℍ) :
    (A • z).im ≤ orbitHeightBound z := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_smul A hA hc
    rw [hn z, vadd_im]
    exact le_max_left _ _
  · exact (matrixGroup_nonparabolic_im_bound A hA hc z).trans (le_max_right _ _)

theorem triangle_im_le_orbitHeightBound (g : TriangleGroup) (z : ℍ) :
    (triangleGeometricRepresentation g z).im ≤ orbitHeightBound z := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  rw [← hA]
  exact matrixGroup_im_le_orbitHeightBound A A.property z

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

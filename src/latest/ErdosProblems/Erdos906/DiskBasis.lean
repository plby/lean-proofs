import Mathlib.Data.Countable.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Complex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Complex Function Metric Set

namespace CofiniteDerivatives

noncomputable section

/-- Rational center/radius data for disks whose radius is smaller than the center norm. -/
def RationalDiskData :=
  {q : (ℚ × ℚ) × ℚ //
    0 < q.2 ∧ (q.2 : ℝ) < ‖(q.1.1 : ℂ) + (q.1.2 : ℂ) * I‖}

instance : Countable RationalDiskData := by
  unfold RationalDiskData
  infer_instance

instance : Nonempty RationalDiskData := by
  refine ⟨⟨((1, 0), 1 / 2), ?_⟩⟩
  norm_num

/-- A fixed surjective enumeration of all admissible rational disk data. -/
noncomputable def rationalDiskEnumeration : ℕ → RationalDiskData :=
  (exists_surjective_nat RationalDiskData).choose

theorem rationalDiskEnumeration_surjective : Surjective rationalDiskEnumeration :=
  (exists_surjective_nat RationalDiskData).choose_spec

/-- The rational real coordinate of the `j`-th disk center. -/
def diskCenterRe (j : ℕ) : ℚ :=
  (rationalDiskEnumeration j).1.1.1

/-- The rational imaginary coordinate of the `j`-th disk center. -/
def diskCenterIm (j : ℕ) : ℚ :=
  (rationalDiskEnumeration j).1.1.2

/-- The positive rational radius of the `j`-th disk. -/
def diskRadiusRat (j : ℕ) : ℚ :=
  (rationalDiskEnumeration j).1.2

/-- The center of the `j`-th disk, explicitly in `ℚ + iℚ`. -/
def diskCenter (j : ℕ) : ℂ :=
  (diskCenterRe j : ℂ) + (diskCenterIm j : ℂ) * I

/-- The radius of the `j`-th disk, regarded as a real number. -/
def diskRadius (j : ℕ) : ℝ :=
  diskRadiusRat j

theorem diskCenter_eq_rational (j : ℕ) :
    diskCenter j = (diskCenterRe j : ℂ) + (diskCenterIm j : ℂ) * I :=
  rfl

theorem diskRadius_eq_rational (j : ℕ) : diskRadius j = (diskRadiusRat j : ℝ) :=
  rfl

/-- The enumerated family of admissible rational open disks. -/
def diskBasis (j : ℕ) : Set ℂ :=
  ball (diskCenter j) (diskRadius j)

theorem diskBasis_eq_ball (j : ℕ) :
    diskBasis j = ball (diskCenter j) (diskRadius j) :=
  rfl

theorem diskRadiusRat_pos (j : ℕ) : 0 < diskRadiusRat j :=
  (rationalDiskEnumeration j).2.1

theorem diskRadius_pos (j : ℕ) : 0 < diskRadius j := by
  change (0 : ℝ) < (diskRadiusRat j : ℝ)
  exact_mod_cast diskRadiusRat_pos j

theorem diskRadius_lt_norm_center (j : ℕ) : diskRadius j < ‖diskCenter j‖ :=
  (rationalDiskEnumeration j).2.2

theorem diskBasis_isOpen (j : ℕ) : IsOpen (diskBasis j) :=
  isOpen_ball

/-- Complex numbers with rational real and imaginary parts are dense in `ℂ`. -/
theorem denseRange_rationalComplex :
    DenseRange (fun q : ℚ × ℚ ↦ (q.1 : ℂ) + (q.2 : ℂ) * I) := by
  have hprod : DenseRange
      (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hcomplex := Complex.equivRealProdCLM.symm.surjective.denseRange.comp hprod
    Complex.equivRealProdCLM.symm.continuous
  simpa [Function.comp_def, Complex.equivRealProdCLM_symm_apply] using! hcomplex

private theorem exists_ne_zero_mem_ball (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ≠ 0, y ∈ ball z ε := by
  by_cases hz : z = 0
  · refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · simpa using! (ne_of_gt (half_pos hε))
    · rw [hz, mem_ball, dist_zero_right]
      simp only [ofReal_div, ofReal_ofNat, norm_div, norm_real, Real.norm_eq_abs, norm_ofNat,
        abs_of_pos hε]
      linarith
  · exact ⟨z, hz, mem_ball_self hε⟩

/-- Every nonempty complex open set contains one of the enumerated rational disks. -/
theorem exists_diskBasis_subset (U : Set ℂ) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ j, diskBasis j ⊆ U := by
  obtain ⟨z, hzU⟩ := hUne
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨y, hy_ne, hy_ball⟩ := exists_ne_zero_mem_ball z hε
  obtain ⟨η, hη, hη_ball⟩ := exists_ball_subset_ball hy_ball
  have hηnorm : 0 < min η ‖y‖ := lt_min hη (norm_pos_iff.mpr hy_ne)
  obtain ⟨q, hq⟩ := denseRange_rationalComplex.exists_dist_lt y hηnorm
  let c : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * I
  have hqη : dist y c < η :=
    lt_of_lt_of_le hq (min_le_left _ _)
  have hqnorm : dist y c < ‖y‖ :=
    lt_of_lt_of_le hq (min_le_right _ _)
  have hc_ne : c ≠ 0 := by
    intro hc
    rw [hc, dist_zero_right] at hqnorm
    exact (lt_irrefl _ hqnorm)
  have hcU : c ∈ U :=
    hεU (hη_ball (mem_ball'.mpr hqη))
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU c hcU
  have hρnorm : 0 < min ρ ‖c‖ := lt_min hρ (norm_pos_iff.mpr hc_ne)
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℚ, (0 : ℝ) < r ∧ (r : ℝ) < min ρ ‖c‖ :=
    exists_rat_btwn hρnorm
  let data : RationalDiskData := ⟨((q.1, q.2), r), by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hr0
    · exact lt_of_lt_of_le hr (min_le_right _ _)⟩
  obtain ⟨j, hj⟩ := rationalDiskEnumeration_surjective data
  refine ⟨j, ?_⟩
  have hcj : diskCenter j = c := by
    simp [diskCenter, diskCenterRe, diskCenterIm, c, hj, data]
  have hrj : diskRadius j = (r : ℝ) := by
    simp [diskRadius, diskRadiusRat, hj, data]
  rw [diskBasis_eq_ball, hcj, hrj]
  exact (ball_subset_ball (le_of_lt (lt_of_lt_of_le hr (min_le_left _ _)))).trans hρU

/-- A positive lower norm bound for the closed ball at half the enumerated radius. -/
def diskNormLower (j : ℕ) : ℝ :=
  ‖diskCenter j‖ - diskRadius j / 2

/-- An upper norm bound for the closed ball at half the enumerated radius. -/
def diskNormUpper (j : ℕ) : ℝ :=
  ‖diskCenter j‖ + diskRadius j / 2

theorem diskNormLower_pos (j : ℕ) : 0 < diskNormLower j := by
  have hr := diskRadius_lt_norm_center j
  have hr0 := diskRadius_pos j
  simp only [diskNormLower]
  linarith

theorem diskNormUpper_pos (j : ℕ) : 0 < diskNormUpper j := by
  have hδ := diskNormLower_pos j
  have hr0 := diskRadius_pos j
  simp only [diskNormLower, diskNormUpper] at hδ ⊢
  linarith

/-- Every point of the closed half-radius disk has norm in the explicit compact interval
`[diskNormLower j, diskNormUpper j]`. -/
theorem norm_mem_closedBall_half_bounds (j : ℕ) {z : ℂ}
    (hz : z ∈ closedBall (diskCenter j) (diskRadius j / 2)) :
    diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j := by
  have hdist : ‖z - diskCenter j‖ ≤ diskRadius j / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using! hz
  have hdist' : ‖diskCenter j - z‖ ≤ diskRadius j / 2 := by
    simpa only [norm_sub_rev] using! hdist
  constructor
  · have htriangle := norm_le_norm_add_norm_sub' (diskCenter j) z
    simp only [diskNormLower]
    linarith
  · have htriangle := norm_le_norm_add_norm_sub (diskCenter j) z
    simp only [diskNormUpper]
    linarith

/-- The closed half-radius disk is bounded away from zero by `diskNormLower j`. -/
theorem norm_mem_closedBall_half_lower (j : ℕ) {z : ℂ}
    (hz : z ∈ closedBall (diskCenter j) (diskRadius j / 2)) :
    diskNormLower j ≤ ‖z‖ :=
  (norm_mem_closedBall_half_bounds j hz).1

/-- In particular, the closed half-radius disk does not contain zero. -/
theorem zero_not_mem_closedBall_half (j : ℕ) :
    0 ∉ closedBall (diskCenter j) (diskRadius j / 2) := by
  intro hzero
  have hlower := norm_mem_closedBall_half_lower j hzero
  have hlower' : diskNormLower j ≤ 0 := by
    simpa only [norm_zero] using! hlower
  exact (not_le_of_gt (diskNormLower_pos j)) hlower'

theorem closedBall_half_isBounded (j : ℕ) :
    Bornology.IsBounded (closedBall (diskCenter j) (diskRadius j / 2)) :=
  Metric.isBounded_closedBall

/-- The boundary circle at half radius has norm between the explicit positive lower bound and
the explicit finite upper bound. -/
theorem norm_mem_sphere_half_bounds (j : ℕ) {z : ℂ}
    (hz : z ∈ sphere (diskCenter j) (diskRadius j / 2)) :
    diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j :=
  norm_mem_closedBall_half_bounds j (sphere_subset_closedBall hz)

/-- Bundled positive finite norm bounds on the boundary circle at half radius. -/
theorem exists_pos_norm_bounds_on_sphere_half (j : ℕ) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧
      ∀ z ∈ sphere (diskCenter j) (diskRadius j / 2), δ ≤ ‖z‖ ∧ ‖z‖ ≤ R :=
  ⟨diskNormLower j, diskNormUpper j, diskNormLower_pos j, diskNormUpper_pos j,
    fun _ hz ↦ norm_mem_sphere_half_bounds j hz⟩

/-- The same bounds hold on the topological boundary of the open half-radius disk. -/
theorem norm_mem_frontier_ball_half_bounds (j : ℕ) {z : ℂ}
    (hz : z ∈ frontier (ball (diskCenter j) (diskRadius j / 2))) :
    diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j :=
  norm_mem_sphere_half_bounds j (frontier_ball_subset_sphere hz)

end

end CofiniteDerivatives

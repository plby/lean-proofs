import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCoordinates

/-!
# A uniform radius bound for the actual cusp time

The squared Euclidean radius of the trivialized normal vector controls
the original toric time uniformly over both affine charts of the base
sphere. Thus a sufficiently small product neighborhood of the entire
zero section lies in the original cusp tube, not just in a chartwise
or point-dependent replacement domain.
-/

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan

/-- The actual squared Euclidean radius on the two complex normal coordinates. -/
def radiusSq (v : Fibre) : ℝ := Complex.normSq v.1 + Complex.normSq v.2

@[simp] theorem radiusSq_zero : radiusSq (0 : Fibre) = 0 := by simp [radiusSq]

theorem radiusSq_nonneg (v : Fibre) : 0 ≤ radiusSq v :=
  add_nonneg (Complex.normSq_nonneg v.1) (Complex.normSq_nonneg v.2)

theorem radiusSq_eq_zero_iff (v : Fibre) : radiusSq v = 0 ↔ v = 0 := by
  rw [radiusSq, add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg v.1)
    (Complex.normSq_nonneg v.2)]
  simp only [Complex.normSq_eq_zero]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem contDiff_radiusSq {n : ℕ∞ω} : ContDiff ℝ n radiusSq := by
  have hn : ContDiff ℝ n (fun a : ℂ => Complex.normSq a) := by
    have hr := Complex.reCLM.contDiff (n := n)
    have hi := Complex.imCLM.contDiff (n := n)
    exact (hr.mul hr).add (hi.mul hi)
  exact (hn.comp contDiff_fst).add (hn.comp contDiff_snd)

theorem radiusSq_smul (u : ℂ) (v : Fibre) :
    radiusSq (u • v) = Complex.normSq u * radiusSq v := by
  simp only [radiusSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.normSq_mul]
  ring

/-- The two explicit frames have exactly the same weighted radius formula. -/
theorem radiusSq_chartCoordinates (b : Bool) (z : CoordinateSpace 3) :
    radiusSq (chartCoordinates b z).2 =
      denominator (z 1) * (Complex.normSq (z 0) + Complex.normSq (z 2)) := by
  cases b
  · exact lowerMap_normSq (z 1) (z 0, z 2)
  · exact upperMap_normSq (z 1) (z 0, z 2)

/-- A sum-of-squares identity bounds the original cubic time in either native chart. -/
theorem four_norm_time_le_radiusSq (b : Bool) (z : CoordinateSpace 3) :
    4 * ‖Triangle.time z‖ ≤ radiusSq (chartCoordinates b z).2 := by
  rw [radiusSq_chartCoordinates]
  simp only [denominator, Complex.normSq_eq_norm_sq, Triangle.time, norm_mul]
  nlinarith only [sq_nonneg (‖z 1‖ * ‖z 0‖ - ‖z 2‖),
    sq_nonneg (‖z 0‖ - ‖z 1‖ * ‖z 2‖)]

/-- The bound is stated on the actual toric point produced by the inverse coordinates. -/
theorem chartParameters_time_bound (b : Bool) (q : Model) :
    4 * ‖ToricSpace.time
        (ToricSpace.inclusion (chartTriangle b) ((chartCoordinates b).symm q))‖ ≤
      radiusSq q.2 := by
  rw [ToricSpace.time_inclusion]
  simpa only [(chartCoordinates b).apply_symm_apply] using
    four_norm_time_le_radiusSq b ((chartCoordinates b).symm q)

/-- One fixed normal-radius condition puts every base point in the original time tube. -/
theorem chartParameters_time_lt (b : Bool) (q : Model) (ε : ℝ)
    (hq : radiusSq q.2 < 4 * ε) :
    ‖ToricSpace.time
      (ToricSpace.inclusion (chartTriangle b) ((chartCoordinates b).symm q))‖ < ε := by
  have h := chartParameters_time_bound b q
  linarith

/-- Every positive cusp radius contains a genuine uniform normal ball. -/
theorem exists_normal_ball_radius (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : Fibre, ‖v‖ < r → radiusSq v < 4 * ε := by
  have hN : {v : Fibre | radiusSq v < 4 * ε} ∈ 𝓝 (0 : Fibre) := by
    apply (isOpen_lt (contDiff_radiusSq (n := ∞)).continuous continuous_const).mem_nhds
    change radiusSq (0 : Fibre) < 4 * ε
    rw [radiusSq_zero]
    linarith
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨r, hr, fun v hv => hsub ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right] using hv

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization

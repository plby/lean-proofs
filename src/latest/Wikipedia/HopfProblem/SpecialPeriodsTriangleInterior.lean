import Wikipedia.HopfProblem.SpecialPeriodsTriangleFundamentalRegion
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The interior of the source hyperbolic triangle

The half-Ford triangle is an actual open subset of the complex plane.
Subtracting its continuous semicircular boundary height gives an explicit
homeomorphism to a convex open vertical strip.  Thus its contractibility
and simple connectivity do not require a uniformization assumption.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The actual open half-Ford triangle used for the source map. -/
def triangleInterior : Set ℂ := {z |
  stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

/-- The continuous upper semicircle height, extended by zero where the
radicand is nonpositive. -/
def boundaryHeight (x : ℝ) : ℝ := Real.sqrt (1 - (x + 1) ^ 2)

@[fun_prop] theorem continuous_boundaryHeight : Continuous boundaryHeight := by
  unfold boundaryHeight
  fun_prop

theorem boundaryHeight_nonneg (x : ℝ) : 0 ≤ boundaryHeight x :=
  Real.sqrt_nonneg _

theorem boundaryHeight_le_one (x : ℝ) : boundaryHeight x ≤ 1 := by
  have h : 1 - (x + 1) ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg (x + 1)]
  simpa only [boundaryHeight, Real.sqrt_one] using Real.sqrt_le_sqrt h

theorem stripLeft_lt_neg_one : stripLeft < -1 := by
  unfold stripLeft
  linarith [one_lt_width]

theorem neg_two_lt_stripLeft : -2 < stripLeft := by
  have h : width < 3 := by nlinarith [width_sq, width_pos]
  unfold stripLeft
  linarith

theorem boundaryHeight_pos {x : ℝ} (hl : stripLeft < x) (hr : x < -1 / 2) :
    0 < boundaryHeight x := by
  have hlo : 0 < x + 2 := by linarith [neg_two_lt_stripLeft]
  have hhi : 0 < -x := by linarith
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos hlo hhi]

/-- The upper-half-plane exterior of the circle is exactly the strict
epigraph of the clipped semicircle height. -/
theorem circle_epigraph_iff (z : ℂ) :
    (0 < z.im ∧ 1 < ‖z + 1‖) ↔ boundaryHeight z.re < z.im := by
  have hnorm : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  constructor
  · rintro ⟨hy, hn⟩
    apply (Real.sqrt_lt' hy).mpr
    have hs := (sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg (z + 1))).mpr hn
    nlinarith
  · intro h
    have hy : 0 < z.im := lt_of_le_of_lt (Real.sqrt_nonneg _) h
    refine ⟨hy, ?_⟩
    apply (sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mp
    have hs := (Real.sqrt_lt' hy).mp h
    nlinarith

theorem mem_triangleInterior_iff_epigraph (z : ℂ) :
    z ∈ triangleInterior ↔
      stripLeft < z.re ∧ z.re < -1 / 2 ∧ boundaryHeight z.re < z.im := by
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ (0 < z.im ∧ 1 < ‖z + 1‖)) ↔ _
  rw [circle_epigraph_iff]

/-- A concrete interior point for normalization of a Riemann map. -/
def triangleBasepoint : ℂ := -1 + 2 * Complex.I

theorem triangleBasepoint_mem : triangleBasepoint ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph]
  norm_num [triangleBasepoint, boundaryHeight, stripLeft_lt_neg_one]

theorem triangleInterior_nonempty : triangleInterior.Nonempty :=
  ⟨triangleBasepoint, triangleBasepoint_mem⟩

theorem triangleInterior_isOpen : IsOpen triangleInterior :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm))))

theorem zero_not_mem_triangleInterior : (0 : ℂ) ∉ triangleInterior := by
  simp [triangleInterior]

theorem triangleInterior_ne_univ : triangleInterior ≠ univ := by
  intro h
  exact zero_not_mem_triangleInterior (h.symm ▸ mem_univ (0 : ℂ))

theorem triangleInterior_im_pos {z : ℂ} (hz : z ∈ triangleInterior) : 0 < z.im :=
  hz.2.2.1

/-- The convex strip obtained after subtracting the lower boundary. -/
def triangleOpenStrip : Set ℂ := {z |
  stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im}

theorem triangleOpenStrip_convex : Convex ℝ triangleOpenStrip :=
  (convex_halfSpace_re_gt stripLeft).inter
    ((convex_halfSpace_re_lt (-1 / 2)).inter (convex_halfSpace_im_gt 0))

theorem triangleOpenStrip_nonempty : triangleOpenStrip.Nonempty := by
  refine ⟨(-1 : ℂ) + Complex.I, ?_⟩
  norm_num [triangleOpenStrip, stripLeft_lt_neg_one]

theorem triangleOpenStrip_isOpen : IsOpen triangleOpenStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

/-- A global vertical shear by the continuous boundary graph. -/
def triangleHeightShift : ℂ ≃ₜ ℂ where
  toFun z := ⟨z.re, z.im - boundaryHeight z.re⟩
  invFun z := ⟨z.re, z.im + boundaryHeight z.re⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun z : ℂ => (z.re, z.im - boundaryHeight z.re)) from by fun_prop)
  continuous_invFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun z : ℂ => (z.re, z.im + boundaryHeight z.re)) from by fun_prop)

@[simp] theorem triangleHeightShift_re (z : ℂ) : (triangleHeightShift z).re = z.re := rfl

@[simp] theorem triangleHeightShift_im (z : ℂ) :
    (triangleHeightShift z).im = z.im - boundaryHeight z.re := rfl

@[simp] theorem triangleHeightShift_symm_re (z : ℂ) :
    (triangleHeightShift.symm z).re = z.re := rfl

@[simp] theorem triangleHeightShift_symm_im (z : ℂ) :
    (triangleHeightShift.symm z).im = z.im + boundaryHeight z.re := rfl

theorem triangleInterior_eq_preimage_strip :
    triangleInterior = triangleHeightShift ⁻¹' triangleOpenStrip := by
  ext z
  rw [mem_triangleInterior_iff_epigraph]
  simp only [mem_preimage, triangleOpenStrip, mem_ofPred_eq,
    triangleHeightShift_re, triangleHeightShift_im, sub_pos]

/-- The actual source interior is homeomorphic to a nonempty convex strip. -/
def triangleInteriorHomeomorphStrip : triangleInterior ≃ₜ triangleOpenStrip :=
  triangleHeightShift.sets triangleInterior_eq_preimage_strip

instance triangleInterior_contractible : ContractibleSpace triangleInterior := by
  have : ContractibleSpace triangleOpenStrip :=
    triangleOpenStrip_convex.contractibleSpace triangleOpenStrip_nonempty
  exact triangleInteriorHomeomorphStrip.contractibleSpace

instance triangleInterior_simplyConnectedSpace : SimplyConnectedSpace triangleInterior :=
  inferInstance

/-- The exact set-valued simple-connectivity input for the Riemann
mapping theorem, proved for this concrete source triangle. -/
theorem triangleInterior_isSimplyConnected : IsSimplyConnected triangleInterior := by
  change SimplyConnectedSpace triangleInterior
  infer_instance

theorem triangleInterior_isPathConnected : IsPathConnected triangleInterior :=
  triangleInterior_isSimplyConnected.isPathConnected

theorem triangleInterior_isConnected : IsConnected triangleInterior :=
  triangleInterior_isPathConnected.isConnected

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyData
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspRegular

/-!
# The actual logarithmic base of a global cusp overlap

Restricting the supplied local family preserves its analytic correction
and small-drift estimate.  After restricting the radius to the actual
high cusp radius, multiplication by the positive cusp width identifies
the logarithmic base with an open subset of the upper half-plane.  This
subset lies in the proved regular locus.  The identification respects
the actual exponential coordinate and the clockwise cusp translations.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily

open CuspUniformization Triangle

namespace Data

/-- Restrict an actual cusp family to a smaller positive parameter radius. -/
def shrink (D : Data) (r : ℝ) (hr : 0 < r) (hrD : r ≤ D.radius) : Data where
  μ := D.μ
  b := D.b
  h := D.h
  radius := r
  radius_pos := hr
  radius_lt_one := hrD.trans_lt D.radius_lt_one
  holomorphic i j := (D.holomorphic i j).mono (Metric.ball_subset_ball hrD)
  smallDrift := D.smallDrift.mono hrD

@[simp] theorem shrink_radius (D : Data) (r : ℝ) (hr : 0 < r) (hrD : r ≤ D.radius) :
    (D.shrink r hr hrD).radius = r := rfl

@[simp] theorem shrink_μ (D : Data) (r : ℝ) (hr : 0 < r) (hrD : r ≤ D.radius) :
    (D.shrink r hr hrD).μ = D.μ := rfl

@[simp] theorem shrink_b (D : Data) (r : ℝ) (hr : 0 < r) (hrD : r ≤ D.radius) :
    (D.shrink r hr hrD).b = D.b := rfl

@[simp] theorem shrink_h (D : Data) (r : ℝ) (hr : 0 < r) (hrD : r ≤ D.radius) :
    (D.shrink r hr hrD).h = D.h := rfl

@[simp] theorem shrink_correction (D : Data) (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ D.radius) :
    (D.shrink r hr hrD).correction = D.correction := rfl

end Data

private theorem complex_width_ne_zero : (width : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr width_ne_zero

/-- The ordinary normalized exponential is exactly the global cusp
coordinate after multiplication by the actual cusp width. -/
theorem qParam_width_mul (s : ℂ) :
    Periodic.qParam width ((width : ℂ) * s) = exponential s := by
  unfold Periodic.qParam exponential
  congr 1
  rw [mul_left_comm, mul_div_cancel_left₀ _ complex_width_ne_zero]

theorem exponential_div_width (z : ℍ) :
    exponential ((z : ℂ) / width) = cuspQ z := by
  simp only [exponential, cuspQ, Periodic.qParam, mul_div_assoc]

private theorem logBase_scaled_height (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : width < ((width : ℂ) * (s : ℂ)).im := by
  apply (Periodic.norm_qParam_lt_iff width_pos width _).mp
  rw [qParam_width_mul]
  exact ((mem_logBase r s).mp s.property).trans_le hrcap

/-- The precise upper-half-plane open subset corresponding to the
restricted parameter radius. -/
def cuspOverlapUpperDomain (r : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | ‖cuspQ z‖ < r}, isOpen_lt cuspQ_continuous.norm continuous_const⟩

@[simp] theorem mem_cuspOverlapUpperDomain (r : ℝ) (z : ℍ) :
    z ∈ cuspOverlapUpperDomain r ↔ ‖cuspQ z‖ < r := Iff.rfl

theorem cuspOverlapUpperDomain_subset_horodisc (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    (cuspOverlapUpperDomain r : Set ℍ) ⊆ horodisc width := by
  intro z hz
  exact (cuspQ_norm_lt_exp_iff width z).mp (hz.trans_le hrcap)

theorem cuspOverlapUpperDomain_subset_regular (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    (cuspOverlapUpperDomain r : Set ℍ) ⊆ triangleRegularLocus :=
  (cuspOverlapUpperDomain_subset_horodisc r hrcap).trans
    (horodisc_subset_triangleRegularLocus width le_rfl)

/-- The actual unnormalized upper-half-plane point of a logarithmic
base point. Its imaginary part exceeds the proved high-cusp threshold. -/
def logBaseToUpperHalfPlane (r : ℝ) (_hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : ℍ := UpperHalfPlane.ofComplex ((width : ℂ) * (s : ℂ))

@[simp] theorem logBaseToUpperHalfPlane_coe (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) :
    (logBaseToUpperHalfPlane r hrcap s : ℂ) = (width : ℂ) * (s : ℂ) :=
  congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos
    (width_pos.trans (logBase_scaled_height r hrcap s)))

theorem logBaseToUpperHalfPlane_mem_horodisc (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : logBaseToUpperHalfPlane r hrcap s ∈ horodisc width := by
  change width < (logBaseToUpperHalfPlane r hrcap s).im
  rw [← UpperHalfPlane.coe_im, logBaseToUpperHalfPlane_coe]
  exact logBase_scaled_height r hrcap s

@[simp] theorem logBaseToUpperHalfPlane_cuspQ (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : cuspQ (logBaseToUpperHalfPlane r hrcap s) = exponential s := by
  rw [cuspQ, logBaseToUpperHalfPlane_coe, qParam_width_mul]

theorem logBaseToUpperHalfPlane_mem_domain (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : logBaseToUpperHalfPlane r hrcap s ∈ cuspOverlapUpperDomain r := by
  rw [mem_cuspOverlapUpperDomain, logBaseToUpperHalfPlane_cuspQ]
  exact (mem_logBase r s).mp s.property

theorem logBaseToUpperHalfPlane_holomorphic (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToUpperHalfPlane r hrcap) := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun s : LogBase r => (width : ℂ) * (s : ℂ)) :=
    contMDiff_const.mul contMDiff_subtype_val
  intro s
  exact (UpperHalfPlane.contMDiffAt_ofComplex
    (width_pos.trans (logBase_scaled_height r hrcap s))).comp s (h s)

/-- The explicit map into the precise overlap open subset. -/
def logBaseToOverlapUpperDomain (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : cuspOverlapUpperDomain r :=
  ⟨logBaseToUpperHalfPlane r hrcap s, logBaseToUpperHalfPlane_mem_domain r hrcap s⟩

@[simp] theorem logBaseToOverlapUpperDomain_val (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) :
    (logBaseToOverlapUpperDomain r hrcap s : ℍ) = logBaseToUpperHalfPlane r hrcap s := rfl

/-- The inverse is the ordinary division by the actual cusp width. -/
def overlapUpperToLogBase (r : ℝ) (z : cuspOverlapUpperDomain r) : LogBase r :=
  ⟨(z.val : ℂ) / width, by
    rw [mem_logBase, exponential_div_width]
    exact z.property⟩

@[simp] theorem overlapUpperToLogBase_coe (r : ℝ) (z : cuspOverlapUpperDomain r) :
    (overlapUpperToLogBase r z : ℂ) = (z.val : ℂ) / width := rfl

theorem logBaseToOverlapUpperDomain_holomorphic (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToOverlapUpperDomain r hrcap) := by
  intro s
  have hi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (Subtype.val ∘ logBaseToOverlapUpperDomain r hrcap) s ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToOverlapUpperDomain r hrcap) s :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (logBaseToUpperHalfPlane_holomorphic r hrcap s)

theorem overlapUpperToLogBase_holomorphic (r : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (overlapUpperToLogBase r) := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : cuspOverlapUpperDomain r => (z.val : ℂ) / width) :=
    (UpperHalfPlane.contMDiff_coe.comp contMDiff_subtype_val).div_const (width : ℂ)
  intro z
  have hi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ overlapUpperToLogBase r) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (overlapUpperToLogBase r) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (h z)

/-- An explicit biholomorphism for the inherited complex structures. -/
def logBaseBiholomorph (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (LogBase r) (cuspOverlapUpperDomain r) ω where
  toFun := logBaseToOverlapUpperDomain r hrcap
  invFun := overlapUpperToLogBase r
  left_inv s := by
    apply Subtype.ext
    change (logBaseToUpperHalfPlane r hrcap s : ℂ) / width = (s : ℂ)
    rw [logBaseToUpperHalfPlane_coe, mul_div_cancel_left₀ _ complex_width_ne_zero]
  right_inv z := by
    apply Subtype.ext
    apply UpperHalfPlane.ext
    change (logBaseToUpperHalfPlane r hrcap (overlapUpperToLogBase r z) : ℂ) = (z.val : ℂ)
    rw [logBaseToUpperHalfPlane_coe, overlapUpperToLogBase_coe,
      mul_div_cancel₀ _ complex_width_ne_zero]
  contMDiff_toFun := logBaseToOverlapUpperDomain_holomorphic r hrcap
  contMDiff_invFun := overlapUpperToLogBase_holomorphic r

@[simp] theorem logBaseBiholomorph_apply (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) :
    logBaseBiholomorph r hrcap s = logBaseToOverlapUpperDomain r hrcap s := rfl

@[simp] theorem logBaseBiholomorph_symm_apply (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (z : cuspOverlapUpperDomain r) :
    (logBaseBiholomorph r hrcap).symm z = overlapUpperToLogBase r z := rfl

theorem logBaseToUpperHalfPlane_injective (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    Injective (logBaseToUpperHalfPlane r hrcap) := by
  intro s t h
  exact (logBaseBiholomorph r hrcap).injective (Subtype.ext h)

theorem logBaseToUpperHalfPlane_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ cuspRadius width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToUpperHalfPlane r hrcap) := by
  intro s
  exact ((logBaseBiholomorph r hrcap).isLocalDiffeomorph s).comp
    (K := 𝓘(ℂ)) (P := ℍ)
    (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (cuspOverlapUpperDomain r)
      (logBaseBiholomorph r hrcap s))

theorem logBaseToUpperHalfPlane_isOpenEmbedding (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    IsOpenEmbedding (logBaseToUpperHalfPlane r hrcap) :=
  .of_continuous_injective_isOpenMap
    (logBaseToUpperHalfPlane_holomorphic r hrcap).continuous
    (logBaseToUpperHalfPlane_injective r hrcap)
    (logBaseToUpperHalfPlane_isLocalDiffeomorph r hrcap).isOpenMap

theorem logBaseToUpperHalfPlane_range (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    range (logBaseToUpperHalfPlane r hrcap) = (cuspOverlapUpperDomain r : Set ℍ) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact logBaseToUpperHalfPlane_mem_domain r hrcap s
  · intro hz
    obtain ⟨s, hs⟩ := (logBaseBiholomorph r hrcap).surjective ⟨z, hz⟩
    exact ⟨s, congrArg Subtype.val hs⟩

/-- The logarithmic base really lands in the free locus of the full
triangle action, by the proved high-horodisc regularity theorem. -/
def logBaseToRegular (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : TriangleRegularPoint :=
  ⟨logBaseToUpperHalfPlane r hrcap s,
    (cuspOverlapUpperDomain_subset_regular r hrcap)
      (logBaseToUpperHalfPlane_mem_domain r hrcap s)⟩

@[simp] theorem logBaseToRegular_val (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) :
    (logBaseToRegular r hrcap s : ℍ) = logBaseToUpperHalfPlane r hrcap s := rfl

@[simp] theorem logBaseToRegular_coe (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) :
    ((logBaseToRegular r hrcap s : ℍ) : ℂ) = (width : ℂ) * (s : ℂ) :=
  logBaseToUpperHalfPlane_coe r hrcap s

theorem logBaseToRegular_mem_horodisc (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : (logBaseToRegular r hrcap s : ℍ) ∈ horodisc width :=
  logBaseToUpperHalfPlane_mem_horodisc r hrcap s

@[simp] theorem logBaseToRegular_cuspQ (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) : cuspQ (logBaseToRegular r hrcap s : ℍ) = exponential s :=
  logBaseToUpperHalfPlane_cuspQ r hrcap s

theorem logBaseToRegular_injective (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    Injective (logBaseToRegular r hrcap) := by
  intro s t h
  exact logBaseToUpperHalfPlane_injective r hrcap (congrArg Subtype.val h)

theorem logBaseToRegular_isLocalDiffeomorph (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToRegular r hrcap) :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ)
    (logBaseToUpperHalfPlane_isLocalDiffeomorph r hrcap) triangleRegularDomain
    (fun s => (logBaseToRegular r hrcap s).property)

theorem logBaseToRegular_holomorphic (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToRegular r hrcap) :=
  (logBaseToRegular_isLocalDiffeomorph r hrcap).contMDiff

theorem logBaseToRegular_isOpenEmbedding (r : ℝ) (hrcap : r ≤ cuspRadius width) :
    IsOpenEmbedding (logBaseToRegular r hrcap) :=
  .of_continuous_injective_isOpenMap (logBaseToRegular_holomorphic r hrcap).continuous
    (logBaseToRegular_injective r hrcap) (logBaseToRegular_isLocalDiffeomorph r hrcap).isOpenMap

/-- The image in the original upper half-plane has the exact small-disc
description, not just an inclusion in an unspecified cusp neighborhood. -/
theorem logBaseToRegular_range_val_iff (r : ℝ) (hrcap : r ≤ cuspRadius width) (z : ℍ) :
    z ∈ range (fun s : LogBase r => (logBaseToRegular r hrcap s : ℍ)) ↔
      ‖cuspQ z‖ < r := by
  change z ∈ range (logBaseToUpperHalfPlane r hrcap) ↔ _
  rw [logBaseToUpperHalfPlane_range]
  rfl

theorem logBaseToRegular_range_iff (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (z : TriangleRegularPoint) :
    z ∈ range (logBaseToRegular r hrcap) ↔ ‖cuspQ (z : ℍ)‖ < r := by
  rw [← logBaseToRegular_range_val_iff r hrcap]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, Subtype.ext hs⟩

/-- Clockwise logarithmic translation is precisely the actual integer
power of the triangle cusp generator. -/
theorem logBaseToUpperHalfPlane_translate (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (k : ℤ) (s : LogBase r) :
    logBaseToUpperHalfPlane r hrcap (logBaseTranslate r k s) =
      triangleGeometricRepresentation (triangleCuspGenerator ^ k)
        (logBaseToUpperHalfPlane r hrcap s) := by
  apply UpperHalfPlane.ext
  rw [logBaseToUpperHalfPlane_coe, logBaseTranslate_coe,
    triangleGeometricRepresentation_cusp_zpow_coe, logBaseToUpperHalfPlane_coe]
  ring

theorem logBaseToRegular_translate (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (k : ℤ) (s : LogBase r) :
    logBaseToRegular r hrcap (logBaseTranslate r k s) =
      (triangleCuspGenerator ^ k) • logBaseToRegular r hrcap s :=
  Subtype.ext (logBaseToUpperHalfPlane_translate r hrcap k s)

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily

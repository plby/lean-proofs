import Wikipedia.SmoothSixDPoincare.MorseHandleModel

/-!
# An ambient homeomorphism extending the curved handle model

The curved product parametrization is the restriction of an explicit
triangular homeomorphism of the entire coordinate space. In particular,
the local handle contains an open neighborhood of its critical center.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def ambientMap (ρ : ℝ) (z : N × P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖z.2‖ ^ 2)) • z.1, ρ • z.2)

def ambientInverse (ρ : ℝ) (z : N × P) : N × P :=
  ((ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2))⁻¹ • z.1, ρ⁻¹ • z.2)

theorem ambientInverse_ambientMap {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ambientInverse ρ (ambientMap ρ z) = z := by
  have hscale : 0 < ρ * Real.sqrt (1 + ‖z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  apply Prod.ext
  · simp only [ambientInverse, ambientMap, smul_smul,
      inv_mul_cancel₀ hρ.ne', one_smul, inv_mul_cancel₀ hscale.ne']
  · simp only [ambientInverse, ambientMap, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

theorem ambientMap_ambientInverse {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    ambientMap ρ (ambientInverse ρ z) = z := by
  have hscale : 0 < ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  apply Prod.ext
  · simp only [ambientInverse, ambientMap, smul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
  · simp only [ambientInverse, ambientMap, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]

/-- The handle's triangular coordinate map extends to an ambient homeomorphism. -/
def ambientHomeomorph (ρ : ℝ) (hρ : 0 < ρ) : (N × P) ≃ₜ (N × P) := by
  have hscale (v : P) : 0 < ρ * Real.sqrt (1 + ‖v‖ ^ 2) :=
    mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  refine
    { toFun := ambientMap ρ
      invFun := ambientInverse ρ
      left_inv := ambientInverse_ambientMap hρ
      right_inv := ambientMap_ambientInverse hρ
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact ((continuous_const.mul
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_snd.norm.pow 2)))).smul
        continuous_fst).prodMk (continuous_const.smul continuous_snd)
  · have hv : Continuous (fun z : N × P => ρ⁻¹ • z.2) := continuous_const.smul continuous_snd
    have hc : Continuous (fun z : N × P => ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)) :=
      continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.add (hv.norm.pow 2)))
    exact ((hc.inv₀ (fun z => (hscale (ρ⁻¹ • z.2)).ne')).smul continuous_fst).prodMk hv

@[simp] theorem ambientHomeomorph_zero (ρ : ℝ) (hρ : 0 < ρ) :
    ambientHomeomorph (N := N) (P := P) ρ hρ 0 = 0 := by
  change ambientMap ρ (0 : N × P) = 0
  simp only [ambientMap, Prod.fst_zero, Prod.snd_zero, smul_zero, Prod.mk_zero_zero]

theorem ambientHomeomorph_apply_disk (ρ : ℝ) (hρ : 0 < ρ) (z : UnitDisk N × UnitDisk P) :
    ambientHomeomorph ρ hρ ((z.1 : N), (z.2 : P)) = modelMap ρ z := rfl

/-- The actual model handle contains a neighborhood of the origin, in every Morse index. -/
theorem range_modelMap_mem_nhds_zero {ρ : ℝ} (hρ : 0 < ρ) :
    range (modelMap (N := N) (P := P) ρ) ∈ 𝓝 (0 : N × P) := by
  let e := ambientHomeomorph (N := N) (P := P) ρ hρ
  let O := ball (0 : N) 1 ×ˢ ball (0 : P) 1
  have hO : IsOpen (e '' O) := e.isOpenMap O (isOpen_ball.prod isOpen_ball)
  have hzero : (0 : N × P) ∈ e '' O := by
    refine ⟨0, ?_, ambientHomeomorph_zero ρ hρ⟩
    exact ⟨by simp, by simp⟩
  have hsub : e '' O ⊆ range (modelMap (N := N) (P := P) ρ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨(⟨z.1, ball_subset_closedBall hz.1⟩, ⟨z.2, ball_subset_closedBall hz.2⟩), rfl⟩
  exact mem_of_superset (hO.mem_nhds hzero) hsub

/-- The square of the negative-coordinate scaling factor in the triangular inverse. -/
theorem inverse_scale_sq {ρ : ℝ} (hρ : 0 < ρ) (v : P) :
    (ρ * Real.sqrt (1 + ‖ρ⁻¹ • v‖ ^ 2)) ^ 2 = ρ ^ 2 + ‖v‖ ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hρ)]
  field_simp

/-- Exact membership in the model handle, expressed in the ambient coordinates. -/
theorem mem_range_modelMap_iff {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ range (modelMap ρ) ↔
      ‖z.2‖ ≤ ρ ∧ -(ρ ^ 2) ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  let A := ρ * Real.sqrt (1 + ‖ρ⁻¹ • z.2‖ ^ 2)
  have hA : 0 < A := mul_pos hρ (Real.sqrt_pos.mpr (by positivity))
  have hA₂ : A ^ 2 = ρ ^ 2 + ‖z.2‖ ^ 2 := inverse_scale_sq hρ z.2
  have hneg : ‖A⁻¹ • z.1‖ ≤ 1 ↔ -(ρ ^ 2) ≤ -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), inv_mul_le_one₀ hA,
      ← sq_le_sq₀ (norm_nonneg z.1) hA.le, hA₂]
    constructor <;> intro h <;> linarith
  have hpos : ‖ρ⁻¹ • z.2‖ ≤ 1 ↔ ‖z.2‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), inv_mul_le_one₀ hρ]
  constructor
  · rintro ⟨w, hw⟩
    have hi : ambientInverse ρ z = ((w.1 : N), (w.2 : P)) := by
      rw [← hw]
      exact ambientInverse_ambientMap hρ ((w.1 : N), (w.2 : P))
    have h₁ : A⁻¹ • z.1 = (w.1 : N) := congrArg Prod.fst hi
    have h₂ : ρ⁻¹ • z.2 = (w.2 : P) := congrArg Prod.snd hi
    exact ⟨hpos.mp (by rw [h₂]; exact mem_closedBall_zero_iff.mp w.2.2),
      hneg.mp (by rw [h₁]; exact mem_closedBall_zero_iff.mp w.1.2)⟩
  · intro hz
    refine ⟨(⟨A⁻¹ • z.1, mem_closedBall_zero_iff.mpr (hneg.mpr hz.2)⟩,
      ⟨ρ⁻¹ • z.2, mem_closedBall_zero_iff.mpr (hpos.mpr hz.1)⟩), ?_⟩
    exact ambientMap_ambientInverse hρ z

end Wikipedia.SmoothSixDPoincare.MorseHandle

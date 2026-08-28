import Wikipedia.NoExoticSixSphere.DoublePointRelativePerturbation

/-!
# Uniform bounds for endpoint-relative affine ambient perturbations

The independent constant term allows value and derivative to be prescribed
separately. On the unit ball, the perturbation is uniformly bounded by twice
the norm of its actual operator/constant parameter, at every time.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.RelativeDoublePointPerturbation

theorem cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t :=
  mul_nonneg (expNegInvGlue.nonneg t) (expNegInvGlue.nonneg (1 - t))

theorem cutoff_le_one (t : ℝ) : cutoff t ≤ 1 := by
  have h (s : ℝ) : expNegInvGlue s ≤ 1 := by
    by_cases hs : s ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hs]
      exact zero_le_one
    · rw [expNegInvGlue, if_neg hs]
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (inv_nonneg.mpr (le_of_lt (lt_of_not_ge hs))))
  exact mul_le_one₀ (h t) (expNegInvGlue.nonneg (1 - t)) (h (1 - t))

theorem norm_cutoff_le_one (t : ℝ) : ‖cutoff t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg t)]
  exact cutoff_le_one t

end NoExoticSixSphere.RelativeDoublePointPerturbation

namespace NoExoticSixSphere.AffinePerturbation

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev Parameters := (E →L[ℝ] F) × F

variable {E F}

def value (p : Parameters E F) (x : E) : F := p.1 x + p.2

theorem contDiff_value : ContDiff ℝ ∞ (uncurry (value (E := E) (F := F))) :=
  ((contDiff_fst.comp contDiff_fst).clm_apply contDiff_snd).add
    (contDiff_snd.comp contDiff_fst)

theorem fderiv_value (p : Parameters E F) (x : E) : fderiv ℝ (value p) x = p.1 :=
  (p.1.hasFDerivAt.add_const p.2).fderiv

theorem exists_value_derivative (x : E) (v : F) (L : E →L[ℝ] F) :
    ∃ p : Parameters E F, value p x = v ∧ fderiv ℝ (value p) x = L := by
  refine ⟨(L, v - L x), ?_, fderiv_value _ x⟩
  simp only [value]
  abel

theorem norm_value_le (p : Parameters E F) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖value p x‖ ≤ 2 * ‖p‖ := by
  calc
    ‖value p x‖ ≤ ‖p.1 x‖ + ‖p.2‖ := norm_add_le _ _
    _ ≤ ‖p.1‖ * ‖x‖ + ‖p.2‖ := add_le_add (p.1.le_opNorm x) le_rfl
    _ ≤ ‖p.1‖ + ‖p.2‖ := by
      gcongr
      exact mul_le_of_le_one_right (norm_nonneg _) hx
    _ ≤ 2 * ‖p‖ := by
      have h₁ := norm_fst_le p
      have h₂ := norm_snd_le p
      linarith

theorem norm_weighted_value_le (p : Parameters E F) (t : ℝ)
    {x : E} (hx : ‖x‖ ≤ 1) :
    ‖RelativeDoublePointPerturbation.cutoff t • value p x‖ ≤ 2 * ‖p‖ := by
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (RelativeDoublePointPerturbation.norm_cutoff_le_one t)).trans (norm_value_le p hx)

end NoExoticSixSphere.AffinePerturbation

import Wikipedia.NoExoticSixSphere.CutoffAffinePerturbation

/-!
# Actual value and two-point evaluation of affine parameters

Affine parameters independently prescribe a value and a derivative, and
independently prescribe values at any two distinct source points. These
linear maps are the parameter derivatives used in the manifold perturbation.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.AffinePerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def evaluation (x : E) : Parameters E F →L[ℝ] F :=
  (ContinuousLinearMap.apply ℝ F x).comp (ContinuousLinearMap.fst ℝ (E →L[ℝ] F) F) +
    ContinuousLinearMap.snd ℝ (E →L[ℝ] F) F

theorem evaluation_apply (x : E) (p : Parameters E F) : evaluation x p = value p x := rfl

theorem surjective_evaluation (x : E) : Surjective (evaluation (F := F) x) := by
  intro v
  refine ⟨(0, v), ?_⟩
  change (0 : E →L[ℝ] F) x + v = v
  simp

theorem fderiv_parameter_value (x : E) (p : Parameters E F) :
    fderiv ℝ (fun q ↦ value q x) p = evaluation x := by
  change fderiv ℝ (evaluation (F := F) x) p = evaluation x
  exact (evaluation (F := F) x).hasFDerivAt.fderiv

theorem hasFDerivAt_weighted_value (x : E) (p : Parameters E F) (a : ℝ) (b : F) :
    HasFDerivAt (fun q ↦ b + a • value q x) (a • evaluation x) p :=
  ((evaluation x).hasFDerivAt.const_smul a).const_add b

def pairEvaluation (x y : E) : Parameters E F →L[ℝ] F × F :=
  (evaluation x).prod (evaluation y)

theorem surjective_pairEvaluation (x y : E) (hxy : x ≠ y) :
    Surjective (pairEvaluation (F := F) x y) := by
  obtain ⟨ℓ, hℓ⟩ := ParametricRegular.operator_evaluation_surjective
    (F := ℝ) (x - y) (sub_ne_zero.mpr hxy) 1
  change ℓ (x - y) = 1 at hℓ
  rintro ⟨v, w⟩
  let A : E →L[ℝ] F := ℓ.smulRight (v - w)
  have hA : A x - A y = v - w := by
    rw [← map_sub]
    change ℓ (x - y) • (v - w) = v - w
    rw [hℓ, one_smul]
  refine ⟨(A, w - A y), Prod.ext ?_ ?_⟩
  · change A x + (w - A y) = v
    calc
      A x + (w - A y) = (A x - A y) + w := by abel
      _ = v := by rw [hA]; abel
  · change A y + (w - A y) = w
    abel

theorem surjective_smul_evaluation (x : E) {a : ℝ} (ha : a ≠ 0) :
    Surjective (a • evaluation (F := F) x) := by
  intro v
  obtain ⟨p, hp⟩ := surjective_evaluation (F := F) x (a⁻¹ • v)
  refine ⟨p, ?_⟩
  change a • evaluation x p = v
  rw [hp, smul_inv_smul₀ ha]

theorem surjective_smul_pairEvaluation (x y : E) (hxy : x ≠ y)
    {a : ℝ} (ha : a ≠ 0) : Surjective (a • pairEvaluation (F := F) x y) := by
  intro v
  obtain ⟨p, hp⟩ := surjective_pairEvaluation (F := F) x y hxy (a⁻¹ • v)
  refine ⟨p, ?_⟩
  change a • pairEvaluation x y p = v
  rw [hp, smul_inv_smul₀ ha]

end NoExoticSixSphere.AffinePerturbation

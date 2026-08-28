import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonRealization
import Wikipedia.HomotopyGroupsOfSpheres.UnitaryCompactLogarithm
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonTangent
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonRefinement

/-!
# Exact refinement of symmetric determinant-one polygons

Each fine increment is the exponential of a scalar in `[0,1]` times its
coarse generator. The common logarithm radius is preserved, so the refined
polygon is admissible and has exactly the same path and energy.
-/

noncomputable section

open Set
open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N] {m k : ℕ}

def resample (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (σ : Fin (k + 2) → ℝ) (v : VertexSpace.Space N m)
    (hv : v ∈ admissible a b m) : VertexSpace.Space N k :=
  fun j ↦ path a b τ hτ v hv (σ j.castSucc.succ)

theorem forget_resample (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (σ : Fin (k + 2) → ℝ) (v : VertexSpace.Space N m)
    (hv : v ∈ admissible a b m) :
    forget (resample a b τ hτ σ v hv) =
      NoExoticSixSphere.OrthogonalPolygon.resample
        (specialOrthogonal a) (specialOrthogonal b) τ σ (forget v) :=
  funext (fun j ↦ path_orthogonal a b τ hτ v hv (σ j.castSucc.succ))

theorem continuous_resample (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (σ : Fin (k + 2) → ℝ) :
    Continuous (fun v : admissible a b m ↦ resample a b τ hτ σ v.1 v.2) := by
  apply continuous_pi
  intro j
  let input : C(admissible a b m, admissible a b m × ℝ) :=
    ⟨fun v ↦ (v, σ j.castSucc.succ), continuous_id.prodMk continuous_const⟩
  exact ((family a b τ hτ).comp input).continuous

variable (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (σ : Fin (k + 2) → ℝ)
  (hτ : StrictMono τ) (hσ : StrictMono σ)
  (hzero : σ 0 = τ 0) (hone : σ (Fin.last (k + 1)) = τ (Fin.last (m + 1)))
  (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
  (parent : Fin (k + 1) → Fin (m + 1))
  (hparent : ∀ j, τ (parent j).castSucc ≤ σ j.castSucc ∧ σ j.succ ≤ τ (parent j).succ)

include hτ hσ hv hparent in
theorem refinement_generator_norm_lt (j : Fin (k + 1)) :
    ‖((σ j.succ - σ j.castSucc) /
      (τ (parent j).succ - τ (parent j).castSucc)) • generator a b v (parent j)‖ <
        ComplexSkewMatrices.CompatibleLog.radius N := by
  have hc : 0 < τ (parent j).succ - τ (parent j).castSucc :=
    sub_pos.mpr (hτ (show (parent j).castSucc < (parent j).succ by simp))
  have hf : 0 ≤ σ j.succ - σ j.castSucc :=
    (sub_pos.mpr (hσ (show j.castSucc < j.succ by simp))).le
  have hle : σ j.succ - σ j.castSucc ≤ τ (parent j).succ - τ (parent j).castSucc := by
    have h := hparent j
    linarith only [h.1, h.2]
  have hr0 := div_nonneg hf hc.le
  have hr1 : (σ j.succ - σ j.castSucc) /
      (τ (parent j).succ - τ (parent j).castSucc) ≤ 1 := (div_le_one hc).mpr hle
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact (mul_le_of_le_one_left (norm_nonneg (generator a b v (parent j))) hr1).trans_lt
    (hv (parent j)).2

include hτ hσ hv hparent in
theorem refinement_generator_mem_target (j : Fin (k + 1)) :
    ((σ j.succ - σ j.castSucc) /
      (τ (parent j).succ - τ (parent j).castSucc)) •
        NoExoticSixSphere.OrthogonalPolygon.generator
          (specialOrthogonal a) (specialOrthogonal b) (forget v) (parent j) ∈
          (NoExoticSixSphere.OrthogonalExponential.logarithmChart
            (2 * Fintype.card N)).target := by
  rw [generator_forget a b hv, ← map_smul]
  have hball : ((σ j.succ - σ j.castSucc) /
      (τ (parent j).succ - τ (parent j).castSucc)) • generator a b v (parent j) ∈
      Metric.closedBall (0 : ComplexSkewMatrices.Space N)
        (ComplexSkewMatrices.CompatibleLog.radius N) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (refinement_generator_norm_lt a b τ σ hτ hσ v hv parent hparent j).le
  exact (ComplexSkewMatrices.CompatibleLog.radius_closedBall hball).2.1

include hτ hσ hzero hone hv hparent in
theorem increment_resample (j : Fin (k + 1)) :
    ShortLog.relative (vertices a b (resample a b τ hτ σ v hv) j.castSucc)
      (vertices a b (resample a b τ hτ σ v hv) j.succ) =
      ComplexSkewMatrices.exponential (((σ j.succ - σ j.castSucc) /
        (τ (parent j).succ - τ (parent j).castSucc)) • generator a b v (parent j)) := by
  apply orthogonal_injective
  rw [ShortLog.orthogonal_relative, vertices_forget, vertices_forget, forget_resample]
  change NoExoticSixSphere.OrthogonalPolygon.increment (specialOrthogonal a)
    (specialOrthogonal b)
    (NoExoticSixSphere.OrthogonalPolygon.resample (specialOrthogonal a)
      (specialOrthogonal b) τ σ (forget v)) j = _
  rw [NoExoticSixSphere.OrthogonalPolygon.increment_resample
    (specialOrthogonal a) (specialOrthogonal b) τ σ hτ hσ hzero hone
    (forget v) (admissible_forget a b hv) parent hparent j,
    ComplexSkewMatrices.orthogonal_exponential, map_smul, generator_forget a b hv]

include hτ hσ hzero hone hv hparent in
theorem resample_admissible : resample a b τ hτ σ v hv ∈ admissible a b k := by
  intro j
  change ShortLog.relative (vertices a b (resample a b τ hτ σ v hv) j.castSucc)
    (vertices a b (resample a b τ hτ σ v hv) j.succ) ∈
      ComplexSkewMatrices.CompatibleLog.domain N
  rw [increment_resample a b τ σ hτ hσ hzero hone v hv parent hparent j]
  exact ComplexSkewMatrices.CompatibleLog.exponential_mem_domain _
    (refinement_generator_norm_lt a b τ σ hτ hσ v hv parent hparent j)

include hτ hσ hzero hone hv hparent in
theorem generator_resample (j : Fin (k + 1)) :
    generator a b (resample a b τ hτ σ v hv) j =
      ((σ j.succ - σ j.castSucc) / (τ (parent j).succ - τ (parent j).castSucc)) •
        generator a b v (parent j) := by
  apply ComplexSkewMatrices.toOrthogonalSkew_injective
  rw [← generator_forget a b
    (resample_admissible a b τ σ hτ hσ hzero hone v hv parent hparent) j, forget_resample]
  rw [NoExoticSixSphere.OrthogonalPolygon.generator_resample
    (specialOrthogonal a) (specialOrthogonal b) τ σ hτ hσ hzero hone
    (forget v) (admissible_forget a b hv) parent hparent
    (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent) j,
    generator_forget a b hv, map_smul]

include hτ hσ hzero hone hv hparent in
theorem path_resample (hw : resample a b τ hτ σ v hv ∈ admissible a b k)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b σ hσ (resample a b τ hτ σ v hv) hw t = path a b τ hτ v hv t := by
  apply Subtype.ext
  apply Subtype.ext
  apply orthogonal_injective
  change specialOrthogonal (path a b σ hσ (resample a b τ hτ σ v hv) hw t) =
    specialOrthogonal (path a b τ hτ v hv t)
  rw [path_orthogonal, path_orthogonal, forget_resample]
  exact NoExoticSixSphere.OrthogonalPolygon.path_resample
    (specialOrthogonal a) (specialOrthogonal b) τ σ hτ hσ hzero hone
    (forget v) (admissible_forget a b hv) parent hparent
    (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent) ht

include hτ hσ hzero hone hv hparent in
theorem energy_resample : energy a b σ (resample a b τ hτ σ v hv) = energy a b τ v := by
  change NoExoticSixSphere.OrthogonalPolygon.energy (specialOrthogonal a)
    (specialOrthogonal b) σ (forget (resample a b τ hτ σ v hv)) = _
  rw [forget_resample]
  exact NoExoticSixSphere.OrthogonalPolygon.energy_resample
    (specialOrthogonal a) (specialOrthogonal b) τ σ hτ hσ hzero hone
    (forget v) (admissible_forget a b hv) parent hparent
    (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonRealization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRefinement

/-!
# Exact refinement of complex-structure polygons

Sampling an admissible polygon on a finer partition preserves its actual path
and energy. Every fine generator is a scalar in `[0,1]` times a coarse one,
so the common short-logarithm radius is preserved without an extra hypothesis.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices Exponential

variable {n m k : ℕ}

private theorem real_norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℝ) (v : V) : ‖r • v‖ = |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]

private theorem mem_closedBall_zero_of_norm_le {V : Type*} [NormedAddCommGroup V]
    {v : V} {r : ℝ} (h : ‖v‖ ≤ r) : v ∈ Metric.closedBall (0 : V) r := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

def resample (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (σ : Fin (k + 2) → ℝ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) : ComplexStructureVertices.Space n k :=
  fun j ↦ path a b τ hτ v hv (σ j.castSucc.succ)

theorem forget_resample (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (σ : Fin (k + 2) → ℝ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) :
    forget (resample a b τ hτ σ v hv) =
      Polygon.resample (toSymplectic a) (toSymplectic b) τ σ (forget v) :=
  funext (fun j ↦ path_toSymplectic a b τ hτ v hv (σ j.castSucc.succ))

theorem continuous_resample (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (σ : Fin (k + 2) → ℝ) :
    Continuous (fun v : admissible a b m ↦ resample a b τ hτ σ v.1 v.2) := by
  apply continuous_pi
  intro j
  let input : C(admissible a b m, admissible a b m × ℝ) :=
    ⟨fun v ↦ (v, σ j.castSucc.succ), continuous_id.prodMk continuous_const⟩
  exact ((family a b τ hτ).comp input).continuous

variable (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) (σ : Fin (k + 2) → ℝ)
  (hτ : StrictMono τ) (hσ : StrictMono σ)
  (hzero : σ 0 = τ 0) (hone : σ (Fin.last (k + 1)) = τ (Fin.last (m + 1)))
  (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
  (parent : Fin (k + 1) → Fin (m + 1))
  (hparent : ∀ j, τ (parent j).castSucc ≤ σ j.castSucc ∧ σ j.succ ≤ τ (parent j).succ)

include hτ hσ hv hparent in
theorem refinement_generator_norm_lt (j : Fin (k + 1)) :
    ‖((σ j.succ - σ j.castSucc) /
      (τ (parent j).succ - τ (parent j).castSucc)) • generator a b v (parent j)‖ <
        ShortLog.radius n := by
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
  rw [real_norm_smul (V := SkewSpace n), abs_of_nonneg hr0]
  exact (mul_le_of_le_one_left (norm_nonneg (generator a b v (parent j))) hr1).trans_lt
    (generator_norm_lt a b hv (parent j))

include hτ hσ hv hparent in
theorem refinement_generator_mem_target (j : Fin (k + 1)) :
    ((σ j.succ - σ j.castSucc) /
      (τ (parent j).succ - τ (parent j).castSucc)) •
        Polygon.generator (toSymplectic a) (toSymplectic b) (forget v) (parent j) ∈
          compatibleTarget n := by
  rw [generator_forget]
  apply ShortLog.radius_closedBall n
  exact mem_closedBall_zero_of_norm_le (V := SkewSpace n)
    (refinement_generator_norm_lt a b τ σ hτ hσ v hv parent hparent j).le

include hτ hσ hzero hone hv hparent in
theorem generator_resample (j : Fin (k + 1)) :
    generator a b (resample a b τ hτ σ v hv) j =
      ((σ j.succ - σ j.castSucc) / (τ (parent j).succ - τ (parent j).castSucc)) •
        generator a b v (parent j) := by
  rw [← generator_forget, forget_resample]
  have he := Polygon.generator_resample (toSymplectic a) (toSymplectic b)
    τ σ hτ hσ hzero hone (forget v) (admissible_forget a b hv) parent hparent
    (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent) j
  rwa [generator_forget] at he

include hτ hσ hzero hone hv hparent in
theorem resample_admissible : resample a b τ hτ σ v hv ∈ admissible a b k := by
  apply admissible_of_forget a b
  · rw [forget_resample]
    exact Polygon.resample_admissible (toSymplectic a) (toSymplectic b)
      τ σ hτ hσ hzero hone (forget v) (admissible_forget a b hv) parent hparent
      (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent)
  · intro j
    rw [generator_resample a b τ σ hτ hσ hzero hone v hv parent hparent]
    exact refinement_generator_norm_lt a b τ σ hτ hσ v hv parent hparent j

include hτ hσ hzero hone hv hparent in
theorem path_resample (hw : resample a b τ hτ σ v hv ∈ admissible a b k)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b σ hσ (resample a b τ hτ σ v hv) hw t = path a b τ hτ v hv t := by
  apply toSymplectic_injective
  rw [path_toSymplectic, path_toSymplectic, forget_resample]
  exact Polygon.path_resample (toSymplectic a) (toSymplectic b)
    τ σ hτ hσ hzero hone (forget v) (admissible_forget a b hv) parent hparent
    (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent) ht

include hτ hσ hzero hone hv hparent in
theorem energy_resample : energy a b σ (resample a b τ hτ σ v hv) = energy a b τ v := by
  change Polygon.energy (toSymplectic a) (toSymplectic b) σ
    (forget (resample a b τ hτ σ v hv)) = _
  rw [forget_resample]
  exact Polygon.energy_resample (toSymplectic a) (toSymplectic b)
    τ σ hτ hσ hzero hone (forget v) (admissible_forget a b hv) parent hparent
    (refinement_generator_mem_target a b τ σ hτ hσ v hv parent hparent)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

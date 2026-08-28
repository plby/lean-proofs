import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonSegments

/-!
# Refining an actual polygon preserves its path and energy

Each fine cell must lie in its specified coarse cell. The corresponding
scaled coarse generator must belong to the logarithm target. Under these
conditions sampling the coarse path gives exactly the same realized path,
and hence the same integral and finite polygon energy.
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential

variable {n m k : ℕ}

noncomputable def resample (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (σ : Fin (k + 2) → ℝ) (v : Space n m) : Space n k :=
  fun j ↦ path a b τ v (σ j.castSucc.succ)

theorem continuous_resample (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (σ : Fin (k + 2) → ℝ) :
    Continuous (fun v : admissible a b m ↦ resample a b τ σ v.1) := by
  apply continuous_pi
  intro j
  change Continuous ((family a b τ) ∘ (fun v : admissible a b m ↦ (v, σ j.castSucc.succ)))
  exact (family a b τ).continuous.comp (continuous_id.prodMk continuous_const)

variable (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) (σ : Fin (k + 2) → ℝ)
  (hτ : StrictMono τ) (hσ : StrictMono σ)
  (hzero : σ 0 = τ 0) (hone : σ (Fin.last (k + 1)) = τ (Fin.last (m + 1)))
  (v : Space n m) (hv : v ∈ admissible a b m)

include hτ hzero hone hv in
theorem vertices_resample (j : Fin (k + 2)) :
    vertices a b (resample a b τ σ v) j = path a b τ v (σ j) := by
  induction j using Fin.cases with
  | zero => rw [vertices_zero, hzero, path_start a b τ hτ hv]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change vertices a b (resample a b τ σ v) (Fin.last (k + 1)) =
        path a b τ v (σ (Fin.last (k + 1)))
      rw [vertices_last, hone, path_end a b τ hτ hv]
    | cast j => rw [vertices_interior]; rfl

variable (parent : Fin (k + 1) → Fin (m + 1))
  (hparent : ∀ j, τ (parent j).castSucc ≤ σ j.castSucc ∧ σ j.succ ≤ τ (parent j).succ)

include hparent in
theorem refinement_cell_mem (j : Fin (k + 1)) {t : ℝ}
    (ht : t ∈ Icc (σ j.castSucc) (σ j.succ)) :
    t ∈ Icc (τ (parent j).castSucc) (τ (parent j).succ) :=
  ⟨(hparent j).1.trans ht.1, ht.2.trans (hparent j).2⟩

include hτ hσ hzero hone hv hparent in
theorem increment_resample (j : Fin (k + 1)) :
    increment a b (resample a b τ σ v) j =
      exp (((σ j.succ - σ j.castSucc) /
        (τ (parent j).succ - τ (parent j).castSucc)) • generator a b v (parent j)) := by
  have hstep := (hσ (show j.castSucc < j.succ by simp)).le
  have hl := refinement_cell_mem τ σ parent hparent j ⟨le_rfl, hstep⟩
  have hr := refinement_cell_mem τ σ parent hparent j ⟨hstep, le_rfl⟩
  rw [increment, vertices_resample a b τ σ hτ hzero hone v hv,
    vertices_resample a b τ σ hτ hzero hone v hv,
    path_eq_segment a b τ hτ hv (parent j) hl,
    path_eq_segment a b τ hτ hv (parent j) hr, rescaledSegment_increment]

variable (hsmall : ∀ j, ((σ j.succ - σ j.castSucc) /
  (τ (parent j).succ - τ (parent j).castSucc)) • generator a b v (parent j) ∈
    compatibleTarget n)

include hτ hσ hzero hone hv hparent hsmall in
theorem resample_admissible : resample a b τ σ v ∈ admissible a b k := by
  intro j
  rw [increment_resample a b τ σ hτ hσ hzero hone v hv parent hparent j]
  exact exp_mem_compatibleDomain _ (hsmall j)

include hτ hσ hzero hone hv hparent hsmall in
theorem generator_resample (j : Fin (k + 1)) :
    generator a b (resample a b τ σ v) j =
      ((σ j.succ - σ j.castSucc) / (τ (parent j).succ - τ (parent j).castSucc)) •
        generator a b v (parent j) := by
  rw [generator, increment_resample a b τ σ hτ hσ hzero hone v hv parent hparent j,
    logarithmChart_exp _ (hsmall j).1]

include hτ hσ hzero hone hv hparent hsmall in
theorem path_resample {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b σ (resample a b τ σ v) t = path a b τ v t := by
  have ht' : t ∈ Icc (σ 0) (σ (Fin.last (k + 1))) := by rwa [hzero, hone]
  obtain ⟨j, hj⟩ := NoExoticSixSphere.IntervalPartition.exists_mem_adjacent σ ht'
  have hstep := hσ (show j.castSucc < j.succ by simp)
  have hl := refinement_cell_mem τ σ parent hparent j ⟨le_rfl, hstep.le⟩
  have htcoarse := refinement_cell_mem τ σ parent hparent j hj
  have hadm := resample_admissible a b τ σ hτ hσ hzero hone v hv parent hparent hsmall
  rw [path_eq_segment a b σ hσ hadm j hj,
    vertices_resample a b τ σ hτ hzero hone v hv,
    generator_resample a b τ σ hτ hσ hzero hone v hv parent hparent hsmall,
    path_eq_segment a b τ hτ hv (parent j) hl,
    rescaledSegment_subsegment _ _ _ _ _ _ _ hstep.ne,
    path_eq_segment a b τ hτ hv (parent j) htcoarse]

include hτ hσ hzero hone hv hparent hsmall in
theorem energy_resample : energy a b σ (resample a b τ σ v) = energy a b τ v := by
  have hadm := resample_admissible a b τ σ hτ hσ hzero hone v hv parent hparent hsmall
  have hfine := path_energy_eq a b σ hσ hadm
  rw [hzero, hone] at hfine
  have htime : τ 0 ≤ τ (Fin.last (m + 1)) := hτ.monotone (Fin.zero_le _)
  have he := NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc htime (fun t ht ↦
    congrArg (fun q : symplecticSubgroup n ↦ q.val.val.val)
      (path_resample a b τ σ hτ hσ hzero hone v hv parent hparent hsmall ht))
  exact hfine.symm.trans (he.trans (path_energy_eq a b τ hτ hv))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

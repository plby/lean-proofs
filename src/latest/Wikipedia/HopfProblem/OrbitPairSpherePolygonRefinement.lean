import Wikipedia.HopfProblem.OrbitPairSphereRescaledSubsegment
import Wikipedia.HopfProblem.OrbitPairSphereRealizedEnergy

/-!
# Refinement preserves actual sphere paths and energy

Sample a coarse polygon realization at a finer partition whose cells lie in
specified coarse cells. Exact canonical subsegment identities supply fine
admissibility and equality of the realized paths. Their actual integral
energies, and therefore their finite polygon energies, agree exactly.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SphereCanonicalGeodesic

variable {n m k : ℕ}

def resample (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (σ : Fin (k + 2) → ℝ) (v : admissible (costDomain n) a b m) : Space n k :=
  fun j => path a b τ hτ v (σ j.castSucc.succ)

theorem continuous_resample (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (σ : Fin (k + 2) → ℝ) : Continuous (resample a b τ hτ σ) := by
  apply continuous_pi
  intro j
  change Continuous ((family a b τ hτ) ∘
    (fun v : admissible (costDomain n) a b m => (v, σ j.castSucc.succ)))
  exact (family a b τ hτ).continuous.comp (continuous_id.prodMk continuous_const)

variable (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (σ : Fin (k + 2) → ℝ)
    (hτ : StrictMono τ) (hσ : StrictMono σ)
    (hzero : σ 0 = τ 0) (hone : σ (Fin.last (k + 1)) = τ (Fin.last (m + 1)))
    (v : admissible (costDomain n) a b m)

include hzero hone in
theorem vertices_resample (j : Fin (k + 2)) :
    vertices a b (resample a b τ hτ σ v) j = path a b τ hτ v (σ j) := by
  induction j using Fin.cases with
  | zero => rw [vertices_zero, hzero, path_start]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change vertices a b (resample a b τ hτ σ v) (Fin.last (k + 1)) =
        path a b τ hτ v (σ (Fin.last (k + 1)))
      rw [vertices_last, hone, path_end]
    | cast j => rw [vertices_interior]; rfl

variable (parent : Fin (k + 1) → Fin (m + 1))
    (hparent : ∀ j, τ (parent j).castSucc ≤ σ j.castSucc ∧ σ j.succ ≤ τ (parent j).succ)

include hparent in
theorem refinement_cell_mem (j : Fin (k + 1)) {t : ℝ}
    (ht : t ∈ Icc (σ j.castSucc) (σ j.succ)) :
    t ∈ Icc (τ (parent j).castSucc) (τ (parent j).succ) :=
  ⟨(hparent j).1.trans ht.1, ht.2.trans (hparent j).2⟩

include hσ hzero hone hparent in
theorem resample_edge_spec (j : Fin (k + 1)) :
    edge a b (resample a b τ hτ σ v) j ∈ (costDomain n).set ∧
      ∀ t : ℝ, rescaledSegment (vertices a b (resample a b τ hτ σ v) j.castSucc)
          (vertices a b (resample a b τ hτ σ v) j.succ) (σ j.castSucc) (σ j.succ) t =
        rescaledSegment (vertices a b v.val (parent j).castSucc)
          (vertices a b v.val (parent j).succ) (τ (parent j).castSucc) (τ (parent j).succ) t := by
  have hstep := hσ (show j.castSucc < j.succ by simp)
  have hl := refinement_cell_mem τ σ parent hparent j ⟨le_rfl, hstep.le⟩
  have hr := refinement_cell_mem τ σ parent hparent j ⟨hstep.le, le_rfl⟩
  change (vertices a b (resample a b τ hτ σ v) j.castSucc,
    vertices a b (resample a b τ hτ σ v) j.succ) ∈ SpherePairedGeodesic.nonantipodal n ∧ _
  rw [vertices_resample a b τ σ hτ hzero hone v,
    vertices_resample a b τ σ hτ hzero hone v,
    path_eq_segment a b τ hτ v (parent j) hl, path_eq_segment a b τ hτ v (parent j) hr]
  exact rescaled_subsegment_spec _ _ (v.2 (parent j))
    (hτ (show (parent j).castSucc < (parent j).succ by simp)) hstep
    (hparent j).1 (hparent j).2

include hσ hzero hone hparent in
theorem resample_admissible : resample a b τ hτ σ v ∈ admissible (costDomain n) a b k :=
  fun j => (resample_edge_spec a b τ σ hτ hσ hzero hone v parent hparent j).1

include hσ hzero hone hparent in
theorem path_resample {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b σ hσ ⟨resample a b τ hτ σ v,
      resample_admissible a b τ σ hτ hσ hzero hone v parent hparent⟩ t = path a b τ hτ v t := by
  have ht' : t ∈ Icc (σ 0) (σ (Fin.last (k + 1))) := by rwa [hzero, hone]
  obtain ⟨j, hj⟩ := IntervalPartition.exists_mem_adjacent σ ht'
  have hcoarse := refinement_cell_mem τ σ parent hparent j hj
  rw [path_eq_segment a b σ hσ _ j hj,
    (resample_edge_spec a b τ σ hτ hσ hzero hone v parent hparent j).2,
    path_eq_segment a b τ hτ v (parent j) hcoarse]

include hσ hzero hone hparent in
theorem energy_resample : energy a b σ (resample a b τ hτ σ v) = energy a b τ v.val := by
  have hfine := path_energy_eq a b σ hσ ⟨resample a b τ hτ σ v,
    resample_admissible a b τ σ hτ hσ hzero hone v parent hparent⟩
  rw [hzero, hone] at hfine
  have htime : τ 0 ≤ τ (Fin.last (m + 1)) := hτ.monotone (Fin.zero_le _)
  have he := SpherePathEnergy.energy_congr_Icc htime (fun t ht => congrArg Subtype.val
    (path_resample a b τ σ hτ hσ hzero hone v parent hparent ht))
  exact hfine.symm.trans (he.trans (path_energy_eq a b τ hτ v))

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

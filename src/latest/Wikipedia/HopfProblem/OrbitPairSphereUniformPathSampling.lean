import Wikipedia.HopfProblem.OrbitPairSphereCanonicalBounds
import Wikipedia.HopfProblem.OrbitPairSpherePolygonFamilyPaths
import Wikipedia.HopfProblem.OrbitPairUniformMetricPartition

/-!
# Sampling continuous sphere paths and controlling their polygon realizations

Uniform control of the original path inside every subdivision cell makes the
sampled edges nonantipodal. The canonical segment distance estimate then keeps
the realized polygon uniformly close to the original path, including at the
subdivision points. The original paths need only be continuous.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SphereCanonicalGeodesic UniformTimePartition

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def sampleUniform (H : C(I × X, Sphere n)) (m : ℕ) : C(X, Space n m) where
  toFun x j := H (unitTime m j.castSucc.succ, x)
  continuous_toFun := continuous_pi (fun _ =>
    H.continuous.comp (continuous_const.prodMk continuous_id))

variable (H : C(I × X, Sphere n)) (a b : Sphere n) (m : ℕ)
    (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)

include ha hb in
theorem vertices_sampleUniform (x : X) (j : Fin (m + 2)) :
    vertices a b (sampleUniform H m x) j = H (unitTime m j, x) := by
  induction j using Fin.cases with
  | zero => rw [vertices_zero, unitTime_zero, ha]
  | succ j =>
    induction j using Fin.lastCases with
    | last => simpa only [Fin.succ_last, vertices_last, unitTime_last] using (hb x).symm
    | cast j => rw [vertices_interior]; rfl

variable (hsmall : ∀ i : Fin (m + 1),
    ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
      dist (H (u, x)).val (H (unitTime m i.castSucc, x)).val < (1 : ℝ) / 4)

include ha hb hsmall in
theorem sampleUniform_admissible (x : X) :
    sampleUniform H m x ∈ admissible (costDomain n) a b m := by
  intro i
  change (vertices a b (sampleUniform H m x) i.castSucc,
    vertices a b (sampleUniform H m x) i.succ) ∈ SpherePairedGeodesic.nonantipodal n
  rw [vertices_sampleUniform H a b m ha hb, vertices_sampleUniform H a b m ha hb]
  apply nonantipodal_of_dist_lt_one
  have h := hsmall i _ ⟨((strictMono_unitTime m)
    (show i.castSucc < i.succ by simp)).le, le_rfl⟩ x
  linarith

include ha hb hsmall in
theorem uniformReplacement_close (z : I × X) :
    dist (realizedFamily a b (time m) (strictMono_time m) (sampleUniform H m)
      (sampleUniform_admissible H a b m ha hb hsmall) z).val (H z).val < 1 := by
  rcases z with ⟨t, x⟩
  have ht : (t : ℝ) ∈ Icc (time m 0) (time m (Fin.last (m + 1))) := by
    simpa only [time_zero, time_last] using t.2
  obtain ⟨i, hi⟩ := IntervalPartition.exists_mem_adjacent (time m) ht
  have hi' : t ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ) := hi
  have htime := (strictMono_time m) (show i.castSucc < i.succ by simp)
  have hα : ((t : ℝ) - time m i.castSucc) / (time m i.succ - time m i.castSucc) ∈
      Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hi.1) (sub_nonneg.mpr htime.le), ?_⟩
    apply (div_le_iff₀ (sub_pos.mpr htime)).mpr
    simpa only [one_mul] using sub_le_sub_right hi.2 (time m i.castSucc)
  have hright := hsmall i _ ⟨htime.le, le_rfl⟩ x
  have hcurrent := hsmall i t hi' x
  have hab := nonantipodal_of_dist_lt_one (H (unitTime m i.castSucc, x))
    (H (unitTime m i.succ, x)) (by linarith)
  have hseg := dist_segment_start_le _ _ hab hα
  change dist (path a b (time m) (strictMono_time m)
    ⟨sampleUniform H m x, sampleUniform_admissible H a b m ha hb hsmall x⟩ (t : ℝ)).val
      (H (t, x)).val < 1
  rw [path_eq_segment a b (time m) (strictMono_time m) _ i hi,
    vertices_sampleUniform H a b m ha hb, vertices_sampleUniform H a b m ha hb]
  have htri := dist_triangle
    (rescaledSegment (H (unitTime m i.castSucc, x)) (H (unitTime m i.succ, x))
      (time m i.castSucc) (time m i.succ) (t : ℝ)).val
    (H (unitTime m i.castSucc, x)).val (H (t, x)).val
  rw [dist_comm (H (unitTime m i.castSucc, x)).val (H (t, x)).val] at htri
  change dist (rescaledSegment (H (unitTime m i.castSucc, x)) (H (unitTime m i.succ, x))
    (time m i.castSucc) (time m i.succ) (t : ℝ)).val (H (unitTime m i.castSucc, x)).val ≤ _ at hseg
  linarith

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

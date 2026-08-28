import Wikipedia.NoExoticSixSphere.ExponentialReplacementFixed
import Wikipedia.NoExoticSixSphere.ClampedUniformPartition
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonFamilyPaths
import Wikipedia.NoExoticSixSphere.IntervalPartition

/-!
# Uniform broken-path replacement is the sampled polygon realization

The finite sampled vertices and the existing natural-indexed replacement
define exactly the same path. Exponential parameters remain fixed whenever
their interval prefixes lie in the actual logarithm target.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  UniformTimePartition IntervalCoordinates OrthogonalPathEnergy

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def sampleUniform (H : C(I × X, OrthogonalOperators n)) (m : ℕ) :
    C(X, Space n m) where
  toFun x i := H (unitTime m i.castSucc.succ, x)
  continuous_toFun := continuous_pi (fun _i ↦
    H.continuous.comp (continuous_const.prodMk continuous_id))

variable (H : C(I × X, OrthogonalOperators n)) (a b : OrthogonalOperators n) (m : ℕ)
  (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)

include ha hb in
theorem vertices_sampleUniform (x : X) (i : Fin (m + 2)) :
    vertices a b (sampleUniform H m x) i = H (unitTime m i, x) := by
  induction i using Fin.cases with
  | zero => rw [vertices_zero, unitTime_zero, ha]
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [Fin.succ_last, vertices_last, unitTime_last] using (hb x).symm
    | cast i => rw [vertices_interior]; rfl

include ha hb in
theorem increment_sampleUniform (x : X) (i : Fin (m + 1)) :
    increment a b (sampleUniform H m x) i =
      (H (unitTime m i.castSucc, x))⁻¹ * H (unitTime m i.succ, x) := by
  rw [increment, vertices_sampleUniform H a b m ha hb, vertices_sampleUniform H a b m ha hb]

variable (hsmall : ∀ i : Fin (m + 1),
  ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
    (H (unitTime m i.castSucc, x))⁻¹ * H (u, x) ∈ (logarithmChart n).source)

include ha hb hsmall in
theorem sampleUniform_admissible (x : X) : sampleUniform H m x ∈ admissible a b m := by
  intro i
  rw [increment_sampleUniform H a b m ha hb]
  exact hsmall i _ ⟨((strictMono_unitTime m) (show i.castSucc < i.succ by simp)).le, le_rfl⟩ x

include hsmall in
theorem uniform_clamped_small :
    ∀ k, ∀ u ∈ Icc (clampedTime m k) (clampedTime m (k + 1)), ∀ x,
      (H (clampedTime m k, x))⁻¹ * H (u, x) ∈ (logarithmChart n).source :=
  clamped_increment_control H m (logarithmChart n).source
    (one_mem_logarithmChart_source n) hsmall

theorem ending_eq_uniform_realizedFamily :
    BrokenPaths.ending H (clampedTime m) (monotone_clampedTime m)
      (uniform_clamped_small H m hsmall) (m + 1) =
    realizedFamily a b (time m) (sampleUniform H m)
      (sampleUniform_admissible H a b m ha hb hsmall) := by
  apply ContinuousMap.ext
  intro q
  rcases q with ⟨u, x⟩
  have hu : (u : ℝ) ∈ Icc (time m 0) (time m (Fin.last (m + 1))) := by
    simpa only [time_zero, time_last] using u.property
  obtain ⟨i, hi⟩ := IntervalPartition.exists_mem_adjacent (time m) hu
  have hi' : u ∈ Icc (clampedTime m i.val) (clampedTime m (i.val + 1)) := by
    rw [clampedTime_left, clampedTime_right]
    exact hi
  rw [BrokenPaths.ending_on_interval H (clampedTime m) (monotone_clampedTime m)
    (uniform_clamped_small H m hsmall) (m + 1) i.val i.isLt u x hi',
    clampedTime_left, clampedTime_right]
  change _ = path a b (time m) (sampleUniform H m x) (u : ℝ)
  rw [path_eq_segment a b (time m) (strictMono_time m)
    (sampleUniform_admissible H a b m ha hb hsmall x) i hi,
    rescaledSegment, vertices_sampleUniform H a b m ha hb]
  rw [coe_normalize_of_mem ((strictMono_unitTime m) (show i.castSucc < i.succ by simp)) hi]
  rw [generator, increment_sampleUniform H a b m ha hb]
  rfl

noncomputable def uniformReplacementHomotopy (S : Set X)
    (hS : ∀ x ∈ S, ∃ K : SkewOperators n,
      (∀ u : I, H (u, x) = H (0, x) * exp ((u : ℝ) • K)) ∧
      ∀ i : Fin (m + 1), ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ),
        ((u : ℝ) - time m i.castSucc) • K ∈ (logarithmChart n).target) :
    H.HomotopyRel
      (realizedFamily a b (time m) (sampleUniform H m)
        (sampleUniform_admissible H a b m ha hb hsmall))
      {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} := by
  rw [← ending_eq_uniform_realizedFamily H a b m ha hb hsmall]
  apply BrokenPaths.homotopyRel_exponential
  intro x hx
  obtain ⟨K, hpath, hK⟩ := hS x hx
  refine ⟨K, hpath, ?_⟩
  intro k hk u hu
  let i : Fin (m + 1) := ⟨k, hk⟩
  have hl : clampedTime m k = unitTime m i.castSucc := clampedTime_left m i
  have hr : clampedTime m (k + 1) = unitTime m i.succ := clampedTime_right m i
  rw [hl, hr] at hu
  rw [hl]
  exact hK i u hu

end NoExoticSixSphere.OrthogonalPolygon

import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryBrokenReplacement
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonFamilyPaths
import Wikipedia.NoExoticSixSphere.OrthogonalUniformPathReplacement

/-!
# Uniform path replacement is the sampled symmetric determinant-one polygon

The actual broken-path homotopy ends at the sampled polygon realization.
It fixes the two endpoint slices and all specified exponential parameters
whose interval prefixes lie in the logarithm target.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open ComplexMatrixRealRepresentation VertexSpace NoExoticSixSphere.UniformTimePartition
  NoExoticSixSphere.CayleyTransform

variable {N : Type*} [Fintype N] [DecidableEq N] {X : Type*} [TopologicalSpace X]

def sampleUniform (H : C(I × X, SpecialSpace N)) (m : ℕ) :
    C(X, VertexSpace.Space N m) where
  toFun x i := H (unitTime m i.castSucc.succ, x)
  continuous_toFun := continuous_pi (fun _i ↦
    H.continuous.comp (continuous_const.prodMk continuous_id))

theorem forget_sampleUniform (H : C(I × X, SpecialSpace N)) (m : ℕ) (x : X) :
    forget (sampleUniform H m x) =
      NoExoticSixSphere.OrthogonalPolygon.sampleUniform (orthogonalFamily H) m x := rfl

variable (H : C(I × X, SpecialSpace N)) (a b : SpecialSpace N) (m : ℕ)
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

variable (hsmall : ∀ i : Fin (m + 1),
  ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
    (H (unitTime m i.castSucc, x), H (u, x)) ∈ ShortLog.domain N)

include ha hb hsmall in
theorem sampleUniform_admissible (x : X) : sampleUniform H m x ∈ admissible a b m := by
  intro i
  rw [vertices_sampleUniform H a b m ha hb, vertices_sampleUniform H a b m ha hb]
  exact hsmall i _ ⟨((strictMono_unitTime m) (show i.castSucc < i.succ by simp)).le, le_rfl⟩ x

include hsmall in
theorem ambientPrefixCondition (i : Fin (m + 1)) (u : I)
    (hu : u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ)) (x : X) :
    (orthogonalFamily H (unitTime m i.castSucc, x))⁻¹ * orthogonalFamily H (u, x) ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).source := by
  change (specialOrthogonal (H (unitTime m i.castSucc, x)))⁻¹ *
    specialOrthogonal (H (u, x)) ∈ _
  rw [← ShortLog.orthogonal_relative]
  exact ComplexSkewMatrices.CompatibleLog.orthogonal_mem_source _ (hsmall i u hu x)

theorem ending_eq_uniform_realizedFamily :
    BrokenReplacement.ending H m hsmall =
      realizedFamily a b (time m) (strictMono_time m) (sampleUniform H m)
        (sampleUniform_admissible H a b m ha hb hsmall) := by
  apply ContinuousMap.ext
  intro z
  apply specialOrthogonal_injective
  change specialOrthogonal (BrokenReplacement.deformation H m hsmall (1, z)) =
    specialOrthogonal (path a b (time m) (strictMono_time m) (sampleUniform H m z.2)
      (sampleUniform_admissible H a b m ha hb hsmall z.2) (z.1 : ℝ))
  rw [BrokenReplacement.deformation_toOrthogonal, path_orthogonal, forget_sampleUniform]
  exact congrArg (fun F : C(I × X,
    NoExoticSixSphere.GLOrthonormalization.OrthogonalOperators (2 * Fintype.card N)) ↦ F z)
    (NoExoticSixSphere.OrthogonalPolygon.ending_eq_uniform_realizedFamily
      (orthogonalFamily H) (specialOrthogonal a)
      (specialOrthogonal b) m (fun x ↦ congrArg specialOrthogonal (ha x))
      (fun x ↦ congrArg specialOrthogonal (hb x)) (ambientPrefixCondition H m hsmall))

def uniformReplacementHomotopy (S : Set X)
    (hS : ∀ x ∈ S, ∃ K : SkewOperators (2 * Fintype.card N),
      (∀ u : I, orthogonalFamily H (u, x) = orthogonalFamily H (0, x) *
        NoExoticSixSphere.OrthogonalExponential.exp ((u : ℝ) • K)) ∧
      ∀ i : Fin (m + 1), ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ),
        ((u : ℝ) - time m i.castSucc) • K ∈
          (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).target) :
    H.HomotopyRel
      (realizedFamily a b (time m) (strictMono_time m) (sampleUniform H m)
        (sampleUniform_admissible H a b m ha hb hsmall))
      {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} := by
  have hS' : ∀ x ∈ S, ∃ K : SkewOperators (2 * Fintype.card N),
      (∀ u : I, orthogonalFamily H (u, x) = orthogonalFamily H (0, x) *
        NoExoticSixSphere.OrthogonalExponential.exp ((u : ℝ) • K)) ∧
      ∀ i < m + 1, ∀ u ∈ Icc (clampedTime m i) (clampedTime m (i + 1)),
        ((u : ℝ) - (clampedTime m i : ℝ)) • K ∈
          (NoExoticSixSphere.OrthogonalExponential.logarithmChart
            (2 * Fintype.card N)).target := by
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
  exact (BrokenReplacement.homotopyRel_exponential H m hsmall S hS').cast rfl
    (ending_eq_uniform_realizedFamily H a b m ha hb hsmall)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

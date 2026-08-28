import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumFamilies
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonFamilyPaths
import Wikipedia.NoExoticSixSphere.UniformUnitIntervalPartition

/-!
# Actual minimum exponential path families
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential NoExoticSixSphere.GLOrthonormalization
  NoExoticSixSphere.UniformTimePartition

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def complexStructurePathFamily (a : symplecticSubgroup n)
    (J : C(X, ComplexStructures.Space n)) :
    C(unitInterval × X, symplecticSubgroup n) where
  toFun z := a * exp ((z.1 : ℝ) • (Real.pi • (J z.2).1))
  continuous_toFun := by
    have hK : Continuous (fun z : unitInterval × X ↦ Real.pi • (J z.2).1) :=
      ((continuous_subtype_val.comp J.continuous).comp continuous_snd).const_smul Real.pi
    have hA : Continuous (fun z : unitInterval × X ↦ (z.1 : ℝ) • (Real.pi • (J z.2).1)) :=
      (continuous_subtype_val.comp continuous_fst).smul hK
    exact continuous_const.mul (contMDiff_exp.continuous.comp hA)

def minimumPathParameters (F : C(unitInterval × X, symplecticSubgroup n))
    (a : symplecticSubgroup n) : Set X :=
  {x | ∃ J : ComplexStructures.Space n,
    ∀ u : unitInterval, F (u, x) = a * exp ((u : ℝ) • (Real.pi • J.1))}

theorem complexStructure_eq_of_paths (a : symplecticSubgroup n)
    (J K : ComplexStructures.Space n)
    (h : ∀ u : unitInterval,
      a * exp ((u : ℝ) • (Real.pi • J.1)) = a * exp ((u : ℝ) • (Real.pi • K.1))) :
    J = K := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have he := mul_left_cancel (h half)
  have hcoef : (half : ℝ) * Real.pi = Real.pi / 2 := by dsimp only [half]; ring
  rw [smul_smul, smul_smul, hcoef] at he
  rw [ComplexStructures.exp_half_pi, ComplexStructures.exp_half_pi] at he
  have hop := congrArg (fun q : symplecticSubgroup n ↦ q.val.val.val) he
  exact Subtype.ext (Subtype.ext hop)

theorem realizedFamily_complexStructure (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (hzero : τ 0 = 0)
    (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ J : ComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ compatibleTarget n)
    (J : C(X, ComplexStructures.Space n))
    (hp : ∀ x, complexStructureFamilyVertices a τ J x ∈ admissible a b m) :
    realizedFamily a b τ (complexStructureFamilyVertices a τ J) hp =
      complexStructurePathFamily a J := by
  apply ContinuousMap.ext
  intro z
  exact path_exponentialVertices a b τ hτ hzero hone (Real.pi • (J z.2).1)
    (complexStructure_endpoint a b hanti (J z.2)) (hsmall (J z.2)) z.1.property

theorem uniform_vertices_eq_exponential_of_path
    (a b : symplecticSubgroup n) (v : Space n m) (hv : v ∈ admissible a b m)
    (J : ComplexStructures.Space n)
    (hpath : ∀ u : unitInterval, path a b (time m) v (u : ℝ) =
      a * exp ((u : ℝ) • (Real.pi • J.1))) :
    v = exponentialVertices a (time m) (Real.pi • J.1) := by
  funext i
  have h := hpath (unitTime m i.castSucc.succ)
  change path a b (time m) v (time m i.castSucc.succ) =
    a * exp (time m i.castSucc.succ • (Real.pi • J.1)) at h
  rw [path_vertex a b (time m) (strictMono_time m) hv, vertices_interior] at h
  exact h

theorem uniform_mem_minimumSet_of_path
    (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ J : ComplexStructures.Space n, ∀ i : Fin (m + 1),
      (time m i.succ - time m i.castSucc) • (Real.pi • J.1) ∈ compatibleTarget n)
    (v : Space n m) (hv : v ∈ admissible a b m)
    (J : ComplexStructures.Space n)
    (hpath : ∀ u : unitInterval, path a b (time m) v (u : ℝ) =
      a * exp ((u : ℝ) • (Real.pi • J.1))) :
    v ∈ minimumSet a b (time m) := by
  rw [uniform_vertices_eq_exponential_of_path a b v hv J hpath]
  exact exponentialVertices_mem_minimumSet a b (time m) (strictMono_time m)
    (time_zero m) (time_last m) hanti hsmall J

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

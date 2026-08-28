import Wikipedia.HopfProblem.OrbitPairSpherePolygonEnergy
import Wikipedia.HopfProblem.OrbitPairSphereAngleFirstVariation

/-!
# Smooth variations in the original sphere vertex manifold

Coordinatewise smooth maps into spheres give smooth maps into the native
finite vertex product. Exponentiating each actual tangent vector therefore
realizes every tangent vertex field by a globally smooth curve. Both fixed
endpoints are left unchanged and their ambient derivatives are zero.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere GLOrthonormalization SphereTangentExponential

variable {n m : ℕ}

section IntoVertices

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_of_coordinate {f : M → Space n m} {x : M}
    (hf : ∀ i : Fin m, ContMDiffAt I (𝓡 n) ∞ (fun y => f y i) x) :
    ContMDiffAt I 𝓘(ℝ, Model n m) ∞ f x := by
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuousAt_pi.mpr (fun i => (hf i).continuousAt), ?_⟩
  rw [extChartAt_coe, chartAt_eq, modelWithCornersSelf_coe]
  simp only [Function.id_comp]
  apply contMDiffAt_pi_space.mpr
  intro i
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (sphereChart (f x i)) (f x i) :=
    (sphereChart (f x i)).contMDiffOn_toFun.contMDiffAt
      ((sphereChart (f x i)).open_source.mem_nhds (mem_sphereChart_source (f x i)))
  simpa only [Function.comp_apply, atVertices_apply] using!
    ContMDiffAt.comp (g := sphereChart (f x i)) (f := fun y => f y i) x hc (hf i)

theorem contMDiff_of_coordinate {f : M → Space n m}
    (hf : ∀ i : Fin m, ContMDiff I (𝓡 n) ∞ (fun y => f y i)) :
    ContMDiff I 𝓘(ℝ, Model n m) ∞ f :=
  fun x => contMDiffAt_of_coordinate (fun i => (hf i).contMDiffAt)

end IntoVertices

abbrev Field (v : Space n m) := ∀ j : Fin m, Tangent (v j).val

def variation (v : Space n m) (W : Field v) (r : ℝ) : Space n m := fun j =>
  ⟨curve (v j).val (W j) r, by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      norm_curve (ClosedHemisphere.unit_norm (v j)) (W j) r⟩

theorem variation_zero (v : Space n m) (W : Field v) : variation v W 0 = v := by
  funext j
  apply Subtype.ext
  exact curve_zero (v j).val (W j)

theorem contMDiff_variation_eval (v : Space n m) (W : Field v) (j : Fin m) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun r => variation v W r j) := by
  letI : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact (contDiff_curve (v j).val (W j)).contMDiff.codRestrict_sphere
    (fun r => (variation v W r j).property)

theorem contMDiff_variation (v : Space n m) (W : Field v) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ (variation v W) :=
  contMDiff_of_coordinate (contMDiff_variation_eval v W)

theorem hasDerivAt_variation_eval_zero (v : Space n m) (W : Field v) (j : Fin m) :
    HasDerivAt (fun r => (variation v W r j).val) (W j : Vector (n + 1)) 0 := by
  have hd := hasDerivAt_curve (ClosedHemisphere.unit_norm (v j)) (W j) 0
  simpa only [zero_smul, OrthogonalExponential.exp_zero] using! hd

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace

variable {n m : ℕ}

def vertexField (v : Space n m) (W : Field v) : Fin (m + 2) → Vector (n + 1) :=
  Fin.cons 0 (Fin.snoc (fun j => (W j : Vector (n + 1))) 0)

theorem vertexField_zero (v : Space n m) (W : Field v) : vertexField v W 0 = 0 := rfl

theorem vertexField_last (v : Space n m) (W : Field v) :
    vertexField v W (Fin.last (m + 1)) = 0 := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => Vector (n + 1))
    (fun j => (W j : Vector (n + 1))) 0 (Fin.last m) = 0
  simp only [Fin.snoc_last]

theorem vertexField_interior (v : Space n m) (W : Field v) (j : Fin m) :
    vertexField v W j.castSucc.succ = (W j : Vector (n + 1)) := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => Vector (n + 1))
    (fun j => (W j : Vector (n + 1))) 0 j.castSucc = (W j : Vector (n + 1))
  simp only [Fin.snoc_castSucc]

theorem contMDiff_vertices_variation (a b : Sphere n) (v : Space n m)
    (W : Field v) (i : Fin (m + 2)) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun r => vertices a b (variation v W r) i) :=
  (contMDiff_vertices a b i).comp (contMDiff_variation v W)

theorem hasDerivAt_vertices_variation (a b : Sphere n) (v : Space n m)
    (W : Field v) (i : Fin (m + 2)) :
    HasDerivAt (fun r => (vertices a b (variation v W r) i).val) (vertexField v W i) 0 := by
  induction i using Fin.cases with
  | zero => simpa only [vertices_zero, vertexField_zero] using hasDerivAt_const (0 : ℝ) a.val
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [Fin.succ_last, vertices_last, vertexField_last] using
        hasDerivAt_const (0 : ℝ) b.val
    | cast j => simpa only [vertices_interior, vertexField_interior] using
        hasDerivAt_variation_eval_zero v W j

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

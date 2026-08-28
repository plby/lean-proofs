import Wikipedia.NoExoticSixSphere.OrthogonalVertexSpace

/-!
# Smooth families of actual orthogonal vertices

For the product Cayley atlas, smoothness is exactly coordinatewise
smoothness in the original orthogonal manifolds. This allows actual
vertex variations to be used in the finite-dimensional energy calculus.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalVertexSpace

open GLOrthonormalization CayleyTransform

variable {n m : ℕ}
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f : M → Space n m} {x : M}

theorem contMDiffAt_iff_coordinatewise :
    ContMDiffAt I 𝓘(ℝ, Model n m) ∞ f x ↔
      ∀ i : Fin m, ContMDiffAt I 𝓘(ℝ, SkewOperators n) ∞ (fun y ↦ f y i) x := by
  constructor
  · intro hf i
    exact (contMDiff_eval (n := n) i).contMDiffAt.comp x hf
  · intro hf
    apply (contMDiffAt_iff_target_of_mem_source
      (I := I) (I' := 𝓘(ℝ, Model n m)) (f := f)
      (mem_atVertices_source (n := n) (m := m) (f x))).mpr
    refine ⟨continuousAt_pi.mpr (fun i ↦ (hf i).continuousAt), ?_⟩
    change ContMDiffAt I 𝓘(ℝ, Model n m) ∞ (fun y ↦ atVertices (f x) (f y)) x
    apply contMDiffAt_pi_space.mpr
    intro i
    have hchart : ContMDiffAt 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n) ∞
        (CayleyAtlas.atOperator (f x i)) (f x i) :=
      (CayleyAtlas.partialChart (f x i)).contMDiffOn_toFun.contMDiffAt
        ((CayleyAtlas.atOperator (f x i)).open_source.mem_nhds
          (CayleyAtlas.mem_atOperator_source (f x i)))
    exact hchart.comp x (hf i)

theorem contMDiff_iff_coordinatewise :
    ContMDiff I 𝓘(ℝ, Model n m) ∞ f ↔
      ∀ i : Fin m, ContMDiff I 𝓘(ℝ, SkewOperators n) ∞ (fun y ↦ f y i) := by
  constructor
  · intro hf i x
    exact contMDiffAt_iff_coordinatewise.mp (hf x) i
  · intro hf x
    exact contMDiffAt_iff_coordinatewise.mpr (fun i ↦ hf i x)

theorem contMDiff_iff_operator_family :
    ContMDiff I 𝓘(ℝ, Model n m) ∞ f ↔
      ∀ i : Fin m, ContMDiff I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun y ↦ (f y i).1.1) := by
  rw [contMDiff_iff_coordinatewise]
  exact forall_congr' (fun _ ↦ OrthogonalSmoothness.contMDiff_iff_operator)

end NoExoticSixSphere.OrthogonalVertexSpace

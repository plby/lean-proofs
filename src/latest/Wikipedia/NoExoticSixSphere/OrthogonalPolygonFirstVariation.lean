import Wikipedia.NoExoticSixSphere.OrthogonalPolygon
import Wikipedia.NoExoticSixSphere.OrthogonalVertexFamilies
import Wikipedia.NoExoticSixSphere.OrthogonalSegmentFirstVariation

/-!
# First variation of the finite polygon energy

These are derivatives of the smooth energy on the actual finite vertex
manifold. The segment formula applies to the genuine local logarithm; its
extension outside the chart is not assumed smooth.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  HilbertSchmidt OrthogonalFirstVariation

variable {n m : ℕ} {v : ℝ → Space n m} {s : ℝ}

theorem hasDerivAt_generator_squareNorm (a b : OrthogonalOperators n)
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ v)
    (hs : v s ∈ admissible a b m) (i : Fin (m + 1)) :
    HasDerivAt (fun r ↦ squareNorm (generator a b (v r) i : Vector n →L[ℝ] Vector n))
      (2 * (innerForm (generator a b (v s) i)
          (endpointBody (fun r ↦ vertices a b (v r) i.succ) s) -
        innerForm (generator a b (v s) i)
          (endpointBody (fun r ↦ vertices a b (v r) i.castSucc) s))) s := by
  let U : Set ℝ := v ⁻¹' admissible a b m
  have hU : IsOpen U := (isOpen_admissible a b m).preimage hv.continuous
  have hα : ContDiff ℝ ∞ (fun r ↦ (vertices a b (v r) i.castSucc).1.1) :=
    (OrthogonalSmoothness.contMDiff_iff_operator.mp
      ((contMDiff_vertices a b i.castSucc).comp hv)).contDiff
  have hK : ContDiffOn ℝ ∞ (fun r ↦ generator a b (v r) i) U :=
    ((contMDiffOn_generator a b i).comp hv.contMDiffOn (fun _ hr ↦ hr)).contDiffOn
  apply hasDerivAt_squareNorm_of_local_endpoints hα hU hs hK
  filter_upwards [hU.mem_nhds hs] with r hr
  exact generator_endpoint a b hr i

theorem hasDerivAt_energy (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ v)
    (hs : v s ∈ admissible a b m) :
    HasDerivAt (fun r ↦ energy a b τ (v r))
      (∑ i : Fin (m + 1),
        2 * (innerForm (generator a b (v s) i)
            (endpointBody (fun r ↦ vertices a b (v r) i.succ) s) -
          innerForm (generator a b (v s) i)
            (endpointBody (fun r ↦ vertices a b (v r) i.castSucc) s)) /
          (τ i.succ - τ i.castSucc)) s := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    (hasDerivAt_generator_squareNorm a b hv hs i).div_const (τ i.succ - τ i.castSucc))

end NoExoticSixSphere.OrthogonalPolygon

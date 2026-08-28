import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# A smooth global extension with exact values on a closed protected set

A genuine smooth function on an open part of a compact native manifold
can be extended after multiplying by a smooth cutoff equal to one near
the protected closed subset. No smoothness outside the given open part
is inferred for the original total function.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

theorem exists_contMDiff_eqOn_closed {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : M → F) {K U : Set M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ContMDiffOn (𝓡 n) 𝓘(ℝ, F) ∞ g U) :
    ∃ G : M → F, ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ G ∧ EqOn G g K := by
  have hdis : Disjoint Uᶜ K := disjoint_left.mpr (fun x hxU hxK ↦ hxU (hKU hxK))
  obtain ⟨ψ, hψ0, hψ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡 n)
    hU.isClosed_compl hK hdis (n := (⊤ : ℕ∞))
  let G : M → F := fun x ↦ ψ x • g x
  refine ⟨G, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact ψ.contMDiff.contMDiffAt.smul (hg.contMDiffAt (hU.mem_nhds hx))
    · have he : G =ᶠ[𝓝 x] (fun _ ↦ 0) := by
        filter_upwards [hψ0.filter_mono (nhds_le_nhdsSet hx)] with y hy
        simp only [G, hy, zero_smul]
      exact he.contMDiffAt_iff.mpr contMDiffAt_const
  · intro x hx
    change ψ x • g x = g x
    rw [hψ1.self_of_nhdsSet x hx, one_smul]

end NoExoticSixSphere

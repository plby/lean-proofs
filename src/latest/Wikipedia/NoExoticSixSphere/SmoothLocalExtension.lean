import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A global smooth extension agreeing on a closed protected set

A smooth cutoff is one near the protected set and zero near the complement
of the given smooth domain. Multiplication therefore gives a globally smooth
map with exact protected values, even if the original total function is
arbitrary outside its smooth domain.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

theorem exists_contDiff_eqOn_closed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) {K U : Set E} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) : ∃ G : E → F, ContDiff ℝ ∞ G ∧ EqOn G g K := by
  have hdis : Disjoint Uᶜ K := disjoint_left.mpr (fun x hxU hxK ↦ hxU (hKU hxK))
  obtain ⟨ψ, hψ0, hψ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
    hU.isClosed_compl hK hdis (n := (⊤ : ℕ∞))
  have hψ : ContDiff ℝ ∞ ψ := ψ.contMDiff.contDiff
  let G : E → F := fun x ↦ ψ x • g x
  refine ⟨G, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hψ.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx))
    · have he : G =ᶠ[𝓝 x] (fun _ ↦ 0) := by
        filter_upwards [hψ0.filter_mono (nhds_le_nhdsSet hx)] with y hy
        simp only [G, hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro x hx
    change ψ x • g x = g x
    rw [hψ1.self_of_nhdsSet x hx, one_smul]

end NoExoticSixSphere

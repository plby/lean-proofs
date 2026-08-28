import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Support

/-! # A compact smooth cutoff around a prescribed compact subset of an open vector domain -/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, η x = 1) ∧ ∀ x, η x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKL (n := ⊤)
  have hsupp : tsupport (η : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx (hηzero x hxL)
  exact ⟨η, η.contMDiff.contDiff, HasCompactSupport.intro hL hηzero,
    hsupp.trans hLU, hηone, hηrange⟩

end Wikipedia.SmoothSixDPoincare

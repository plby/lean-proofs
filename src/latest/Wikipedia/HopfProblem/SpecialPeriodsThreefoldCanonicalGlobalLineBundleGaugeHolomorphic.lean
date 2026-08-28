import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Holomorphic bundle maps from local coefficients

A fibre-preserving map between two cocycle line bundles on the same open
cover is holomorphic if its expression in each pair of original bundle
charts is multiplication by a holomorphic scalar. The preferred chart
indices of the two bundles need not agree.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

variable {M ι : Type*} [TopologicalSpace M]
    (A B : HolomorphicCharacterBundle.TransitionData M ι)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [A.IsHolomorphic I] [B.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Holomorphic local scalar coefficients give a holomorphic map on the
original bundle total spaces, without any separate continuity assumption. -/
theorem bundleMap_holomorphic_of_local_coefficients
    (hbase : A.baseSet = B.baseSet)
    (F : A.core.TotalSpace → B.core.TotalSpace)
    (hproj : ∀ p, (F p).proj = p.proj)
    (u : ι → M → ℂ)
    (hu : ∀ i, ContMDiffOn I I₁ ω (u i) (A.baseSet i))
    (hcoef : ∀ i p, p.proj ∈ A.baseSet i →
      (B.core.localTriv i (F p)).2 = u i p.proj * (A.core.localTriv i p).2) :
    ContMDiff (I.prod I₁) (I.prod I₁) ω F := by
  intro p
  let i := A.indexAt p.proj
  have hp : p.proj ∈ A.baseSet i := A.mem_baseSet_at p.proj
  have hsource : F p ∈ (B.core.localTriv i).source := by
    change (F p).proj ∈ B.baseSet i
    rw [hproj, ← hbase]
    exact hp
  apply ((B.core.localTriv i).contMDiffAt_iff hsource).mpr
  have hπ : ContMDiffAt (I.prod I₁) I ω
      (fun q : A.core.TotalSpace => q.proj) p :=
    Bundle.contMDiffAt_proj A.core.Fiber
  refine ⟨?_, ?_⟩
  · simpa only [hproj] using hπ
  · have huAt := (hu i).contMDiffAt ((A.isOpen_baseSet i).mem_nhds hp)
    have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω (A.core.localTriv i) p :=
      (A.core.localTriv i).contMDiffOn.contMDiffAt
        ((A.core.localTriv i).open_source.mem_nhds hp)
    apply ((huAt.comp p hπ).mul he.snd).congr_of_eventuallyEq
    filter_upwards [hπ.continuousAt ((A.isOpen_baseSet i).mem_nhds hp)] with q hq
    exact hcoef i q hq

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle

import Wikipedia.NoExoticSixSphere.DiskThickening
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# A thin affine thickening of a compact core avoids a closed set

Continuity on the compact parameter space gives a single positive transverse
radius. Only pointwise smoothness along that parameter space is used; no
uniform open infinitely smooth neighborhood is assumed.
-/

noncomputable section

open Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization

theorem exists_avoiding_closed_product {N q : ℕ} {K : Set (Vector 4)} (hK : IsCompact K)
    (D : Vector 4 → Vector N) (C : Vector 4 → Vector q →L[ℝ] Vector N)
    (hD : ∀ x ∈ K, ContDiffAt ℝ ∞ D x) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    {L : Set (Vector N)} (hL : IsClosed L) (havoid : ∀ x ∈ K, D x ∉ L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ v ∈ closedBall (0 : Vector q) ε,
      map D C (x, v) ∉ L := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let j : K × Vector q → Vector 4 × Vector q := fun p ↦ (p.1.val, p.2)
  have hj : Continuous j :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hc : Continuous (fun p : K × Vector q ↦ map D C (p.1.val, p.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := j)
      (contDiffAt_map D C p.1.val p.2 (hD p.1.val p.1.property)
        (hC p.1.val p.1.property)).continuousAt hj.continuousAt
  let U := (fun p : K × Vector q ↦ map D C (p.1.val, p.2)) ⁻¹' Lᶜ
  have hU : IsOpen U := hL.isOpen_compl.preimage hc
  have hzero (x : K) : (x, (0 : Vector q)) ∈ U := by
    change map D C (x.val, 0) ∉ L
    rw [map_core]
    exact havoid x.val x.property
  obtain ⟨ε, hε, hεU⟩ := exists_uniform_closedProductTube hU hzero
  refine ⟨ε, hε, ?_⟩
  intro x hx v hv
  exact hεU ⟨x, hx⟩ v (by simpa only [mem_closedBall, dist_zero_right] using hv)

end NoExoticSixSphere.DiskThickening

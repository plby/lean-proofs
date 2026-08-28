import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Separation.Hausdorff

/-!
# One smooth coordinate neighborhood around a compact embedded locus

Injectivity on a compact set and smooth local inverses along that set give a
single injective open neighborhood. The inverse on its image agrees locally
with the already constructed smooth local inverses, and is therefore smooth.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X] [Nonempty X]
  [TopologicalSpace Y] [ChartedSpace H' Y]

/-- A one-to-one smooth local diffeomorphism on an open set gives
a smooth partial diffeomorphism. -/
def partialDiffeomorphOfInjectiveLocal {f : X → Y} {U : Set X}
    (hU : IsOpen U) (hinj : InjOn f U) (hloc : IsLocalDiffeomorphOn I J ∞ f U) :
    PartialDiffeomorph I J X Y ∞ := by
  let p := hinj.toPartialEquiv f U
  have htarget : IsOpen p.target := by
    change IsOpen (f '' U)
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hx]
    exact image_mem_map (hU.mem_nhds hx)
  have hinverse : ContMDiffOn J I ∞ p.symm p.target := by
    intro y hy
    have hx : p.symm y ∈ U := p.map_target hy
    obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
    have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
    have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
    have hφyx : φ.symm y = p.symm y := by
      calc
        φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
        _ = p.symm y := φ.left_inv' hφx
    have hg : ContMDiffAt J I ∞ φ.symm y :=
      φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
    have hNU : U ∈ 𝓝 (φ.symm y) := by
      rw [hφyx]
      exact hU.mem_nhds hx
    have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
      filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
      have hfz : f (φ.symm z) = z := (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
      exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
    exact (hfg.contMDiffAt_iff.mpr hg).contMDiffWithinAt
  exact { p with
    open_source := hU
    open_target := htarget
    contMDiffOn_toFun := hloc.contMDiffOn
    contMDiffOn_invFun := hinverse }

/-- The compact locus has a single smooth coordinate neighborhood inside any prescribed open set. -/
theorem exists_partialDiffeomorph_near_compact [T2Space Y] {f : X → Y} {K U : Set X}
    (hK : IsCompact K) (hinj : InjOn f K)
    (hloc : ∀ x ∈ K, IsLocalDiffeomorphAt I J ∞ f x)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Φ : PartialDiffeomorph I J X Y ∞,
      K ⊆ Φ.source ∧ Φ.source ⊆ U ∧ (Φ : X → Y) = f := by
  let R : Set X := {x | IsLocalDiffeomorphAt I J ∞ f x}
  have hR : IsOpen R := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨φ, hx, heq⟩
    exact mem_of_superset (φ.open_source.mem_nhds hx) (fun y hy => ⟨φ, hy, heq⟩)
  have hlocalinj : ∀ x ∈ K, ∃ V ∈ 𝓝 x, InjOn f V := by
    intro x hx
    obtain ⟨φ, hφ, heq⟩ := hloc x hx
    exact ⟨φ.source, φ.open_source.mem_nhds hφ, heq.injOn_iff.mpr φ.toPartialEquiv.injOn⟩
  obtain ⟨V, hV, hKV, hVi⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => (hloc x hx).contMDiffAt.continuousAt) hlocalinj
  let W := (V ∩ R) ∩ U
  have hW : IsOpen W := (hV.inter hR).inter hU
  have hKW : K ⊆ W := fun x hx => ⟨⟨hKV hx, hloc x hx⟩, hKU hx⟩
  have hWi : InjOn f W := hVi.mono (inter_subset_left.trans inter_subset_left)
  have hWloc : IsLocalDiffeomorphOn I J ∞ f W := fun x => x.property.1.2
  exact ⟨partialDiffeomorphOfInjectiveLocal hW hWi hWloc, hKW, inter_subset_right, rfl⟩

end Wikipedia.SmoothSixDPoincare

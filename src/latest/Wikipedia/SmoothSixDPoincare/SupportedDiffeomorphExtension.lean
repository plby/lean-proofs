import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending supported coordinate diffeomorphisms to the native manifold

A genuine diffeomorphism supported on a compact subset of a partial smooth
chart extends to an actual global diffeomorphism, equal to the identity off
the chart. Smoothness across the chart boundary follows from the compact
support image, not from an assumed global chart or a piecewise-smooth shortcut.
-/

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

/-- A bijection fixed outside a set preserves that set. -/
theorem mapsTo_of_fixed_outside {X : Type*} (d : X ≃ X) {S : Set X}
    (hfix : ∀ x ∉ S, d x = x) : MapsTo d S S := by
  intro x hx
  by_contra hdx
  have heq : d x = x := d.injective (hfix (d x) hdx)
  exact hdx (heq.symm ▸ hx)

/-- Its inverse is fixed on exactly the same prescribed exterior. -/
theorem inverse_fixed_outside {X : Type*} (d : X ≃ X) {S : Set X}
    (hfix : ∀ x ∉ S, d x = x) : ∀ x ∉ S, d.symm x = x := by
  intro x hx
  apply d.injective
  rw [d.apply_symm_apply, hfix x hx]

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  (Φ : PartialDiffeomorph I J X Y ∞)

/-- Coordinate conjugation on the chart, identity on its complement. -/
def extendMap (f : X → X) (y : Y) : Y := by
  classical
  exact if y ∈ Φ.target then Φ (f (Φ.symm y)) else y

theorem extendMap_of_mem (f : X → X) {y : Y} (hy : y ∈ Φ.target) :
    extendMap Φ f y = Φ (f (Φ.symm y)) := by
  simp only [extendMap, hy, if_pos]

theorem extendMap_of_notMem (f : X → X) {y : Y} (hy : y ∉ Φ.target) :
    extendMap Φ f y = y := by
  simp only [extendMap, hy, if_false]

theorem extendMap_id (y : Y) : extendMap Φ id y = y := by
  by_cases hy : y ∈ Φ.target
  · rw [extendMap_of_mem Φ id hy]
    exact Φ.right_inv' hy
  · exact extendMap_of_notMem Φ id hy

/-- On a valid source coordinate, extension is exactly conjugation. -/
theorem extendMap_chart (f : X → X) {x : X} (hx : x ∈ Φ.source) :
    extendMap Φ f (Φ x) = Φ (f x) := by
  rw [extendMap_of_mem Φ f (Φ.map_source' hx)]
  exact congrArg (fun z => Φ (f z)) (Φ.left_inv' hx)

theorem extendMap_mem_target {f : X → X} (hf : MapsTo f Φ.source Φ.source)
    {y : Y} (hy : y ∈ Φ.target) : extendMap Φ f y ∈ Φ.target := by
  rw [extendMap_of_mem Φ f hy]
  exact Φ.map_source' (hf (Φ.map_target' hy))

/-- Inverse coordinate maps give inverse global extensions. -/
theorem extendMap_leftInverse (d : X ≃ X)
    (hd : MapsTo d Φ.source Φ.source) :
    LeftInverse (extendMap Φ d.symm) (extendMap Φ d) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · rw [extendMap_of_mem Φ d.symm (extendMap_mem_target Φ hd hy), extendMap_of_mem Φ d hy]
    change Φ (d.symm (Φ.invFun (Φ (d (Φ.invFun y))))) = y
    rw [Φ.left_inv' (hd (Φ.map_target' hy)), d.symm_apply_apply]
    exact Φ.right_inv' hy
  · rw [extendMap_of_notMem Φ d hy, extendMap_of_notMem Φ d.symm hy]

/-- The global extension is fixed outside the actual compact support image. -/
theorem extendMap_eq_of_notMem_image {f : X → X} {K : Set X}
    (hfix : ∀ x ∉ K, f x = x) {y : Y} (hy : y ∉ Φ '' K) : extendMap Φ f y = y := by
  by_cases hyt : y ∈ Φ.target
  · have hback : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [extendMap_of_mem Φ f hyt, hfix _ hback]
    exact Φ.right_inv' hyt
  · exact extendMap_of_notMem Φ f hyt

/-- Being fixed outside the compact support also preserves the whole source chart. -/
theorem mapsTo_source (d : X ≃ X) {K : Set X} (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∉ K, d x = x) : MapsTo d Φ.source Φ.source :=
  mapsTo_of_fixed_outside d (fun x hx => hfix x (fun hk => hx (hKΦ hk)))

variable [T2Space Y]

/-- The piecewise extension is genuinely smooth, including at the chart boundary. -/
theorem contMDiff_extendMap {f : X → X} (hf : ContMDiff I I ∞ f)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∉ K, f x = x) (hsource : MapsTo f Φ.source Φ.source) :
    ContMDiff J J ∞ (extendMap Φ f) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hback := Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy)
    have hforward := Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hsource (Φ.map_target' hy)))
    have hs := hforward.comp y (hf.contMDiffAt.comp y hback)
    apply hs.congr_of_eventuallyEq
    filter_upwards [Φ.open_target.mem_nhds hy] with z hz
    exact extendMap_of_mem Φ f hz
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    apply (contMDiffAt_id : ContMDiffAt J J ∞ id y).congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds hnot] with z hz
    exact extendMap_eq_of_notMem_image Φ hfix hz

/-- A compactly supported coordinate diffeomorphism extends to a global native diffeomorphism. -/
def extension (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) :
    Diffeomorph J J Y Y ∞ := by
  have hdi : ∀ x ∉ K, d.symm x = x := inverse_fixed_outside d.toEquiv hfix
  have hdS : MapsTo d Φ.source Φ.source := mapsTo_source Φ d.toEquiv hKΦ hfix
  have hdiS : MapsTo d.symm Φ.source Φ.source := mapsTo_source Φ d.symm.toEquiv hKΦ hdi
  exact {
    toFun := extendMap Φ d
    invFun := extendMap Φ d.symm
    left_inv := extendMap_leftInverse Φ d.toEquiv hdS
    right_inv := extendMap_leftInverse Φ d.symm.toEquiv hdiS
    contMDiff_toFun := contMDiff_extendMap Φ d.contMDiff hK hKΦ hfix hdS
    contMDiff_invFun := contMDiff_extendMap Φ d.symm.contMDiff hK hKΦ hdi hdiS }

theorem extension_chart (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x)
    {x : X} (hx : x ∈ Φ.source) : extension Φ d hK hKΦ hfix (Φ x) = Φ (d x) :=
  extendMap_chart Φ d hx

theorem extension_eq_of_notMem_image (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x)
    {y : Y} (hy : y ∉ Φ '' K) : extension Φ d hK hKΦ hfix y = y :=
  extendMap_eq_of_notMem_image Φ hfix hy

/-- In particular every point outside the chart, including any disjoint obstacle, stays fixed. -/
theorem extension_eq_of_notMem_target (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x)
    {y : Y} (hy : y ∉ Φ.target) : extension Φ d hK hKΦ hfix y = y :=
  extendMap_of_notMem Φ d hy

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

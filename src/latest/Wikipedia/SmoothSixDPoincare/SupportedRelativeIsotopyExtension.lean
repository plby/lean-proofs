import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopy
import Wikipedia.SmoothSixDPoincare.SupportedDiffeomorphFamily

/-! # Extending a supported relative isotopy with its exact support and fixed set -/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]

namespace SupportedRelativeIsotopy

variable {e : Diffeomorph I I X X ∞} {K S : Set X}
  (A : SupportedRelativeIsotopy e K S)

include A in
/-- Every slice preserves each set containing the common support. -/
theorem mapsTo_superset {U : Set X} (hKU : K ⊆ U) (t : ℝ) :
    MapsTo (fun x => A.family (t, x)) U U := by
  obtain ⟨d, hd⟩ := A.slices t
  have hfix : ∀ x ∉ U, d x = x := by
    intro x hx
    exact (hd x).trans (A.fixedOutside t x (fun h => hx (hKU h)))
  intro x hx
  change A.family (t, x) ∈ U
  rw [← hd]
  exact mapsTo_of_fixed_outside d.toEquiv hfix hx

/-- The extended family has exactly the transported support and retains the prescribed fixed set. -/
def extension (Φ : PartialDiffeomorph I J X Y ∞)
    (hK : IsCompact K) (hKsource : K ⊆ Φ.source) {T : Set Y}
    (hfixed : ∀ x ∈ Φ.source, Φ x ∈ T → x ∈ S) :
    SupportedRelativeIsotopy
      (SupportedDiffeomorph.extension Φ e hK hKsource A.endpoint_fixed_outside)
      (Φ '' K) T where
  family := fun p => extendMap Φ (fun x => A.family (p.1, x)) p.2
  smooth := contMDiff_extendFamily Φ A.smooth hK hKsource A.fixedOutside
    (A.mapsTo_superset hKsource)
  zero := by
    intro y
    have heq : (fun x => A.family (0, x)) = id := funext A.zero
    rw [heq]
    exact extendMap_id Φ y
  one := by
    intro y
    exact congrArg (fun f : X → X => extendMap Φ f y) (funext A.one)
  slices := by
    intro t
    obtain ⟨d, hd⟩ := A.slices t
    have hfix : ∀ x ∉ K, d x = x := fun x hx => (hd x).trans (A.fixedOutside t x hx)
    exact ⟨SupportedDiffeomorph.extension Φ d hK hKsource hfix,
      fun y => congrArg (fun f : X → X => extendMap Φ f y) (funext hd)⟩
  fixedOutside := fun t y hy => extendMap_eq_of_notMem_image Φ (A.fixedOutside t) hy
  fixedOn := by
    intro t y hy
    by_cases hyt : y ∈ Φ.target
    · rw [extendMap_of_mem Φ _ hyt]
      have hsource : Φ.symm y ∈ Φ.source := Φ.map_target' hyt
      have hi : Φ (Φ.symm y) = y := Φ.right_inv' hyt
      have hs : Φ.symm y ∈ S := hfixed (Φ.symm y) hsource (hi.symm ▸ hy)
      rw [A.fixedOn t (Φ.symm y) hs]
      exact hi
    · exact extendMap_of_notMem Φ _ hyt

theorem extension_family_chart (Φ : PartialDiffeomorph I J X Y ∞)
    (hK : IsCompact K) (hKsource : K ⊆ Φ.source) {T : Set Y}
    (hfixed : ∀ x ∈ Φ.source, Φ x ∈ T → x ∈ S)
    (t : ℝ) {x : X} (hx : x ∈ Φ.source) :
    (A.extension Φ hK hKsource hfixed).family (t, Φ x) = Φ (A.family (t, x)) :=
  extendMap_chart Φ (fun z => A.family (t, z)) hx

end SupportedRelativeIsotopy

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

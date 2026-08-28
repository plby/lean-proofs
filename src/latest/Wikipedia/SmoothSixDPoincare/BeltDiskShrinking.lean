import Wikipedia.SmoothSixDPoincare.MorseSurgeryBeltCoordinates
import Wikipedia.SmoothSixDPoincare.SmoothBeltNeighborhood
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphPartial
import Wikipedia.SmoothSixDPoincare.SupportedDiskShrinking
import Wikipedia.SmoothSixDPoincare.SupportedIsotopyExtension

/-!
# Supported shrinking of the actual closed belt disk

The explicit radial isotopy extends through the entire native belt chart.
It fixes every belt point throughout and scales the whole unit normal disk
by any prescribed factor in `(0, 1]` at its endpoint.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def normalDiskScale {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates) :
    PuncturedHandle.UnitBall d.chart.NegativeCoordinates :=
  ⟨a • u.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le u.property).trans ha₁⟩

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- The original upper level admits a supported isotopy shrinking the entire
new-piece normal disk and fixing the original belt sphere at all times. -/
theorem exists_belt_disk_shrinking (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v₀ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)
    {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∃ K : Set d.UpperLevel, IsCompact K ∧ K ⊆ d.chart.beltTarget d.radius ∧
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        d.UpperLevel d.UpperLevel ∞,
        Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy e K
          (range d.surgery.beltSphere)) ∧
        ∀ u v, e (d.beltClosedDiskMap (u, v)) =
          d.beltClosedDiskMap (d.normalDiskScale ha ha₁ u, v) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let J := (𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates)
  let X := PuncturedHandle.UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates
  let e₀ := d.chart.beltNeighborhoodDiffeomorph hf n d.radius d.radius_pos d.upper_regular
  let x₀ := d.chart.beltZeroPoint d.radius d.radius_pos d.block v₀
  let Φ := OpenDiffeomorph.partialDiffeomorph e₀ x₀
  let C : Set X := univ ×ˢ closedBall (0 : d.chart.NegativeCoordinates) (3 / 2 : ℝ)
  have hC : IsCompact C := isCompact_univ.prod (isCompact_closedBall _ _)
  have hsource : C ⊆ Φ.source :=
    d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
  let A : ℝ × X → X := fun q => (q.2.1, SmoothRadial.shrinkingFamily a (q.1, q.2.2))
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A :=
    (contMDiff_fst.comp contMDiff_snd).prodMk
      ((SmoothRadial.contMDiff_shrinkingFamily a).comp
        (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))
  have hA₀ : ∀ x, A (0, x) = x := by
    intro x
    exact Prod.ext rfl (SmoothRadial.shrinkingFamily_zero a x.2)
  have hAt : ∀ t, ∃ D : Diffeomorph J J X X ∞, ∀ x, D x = A (t, x) := by
    intro t
    obtain ⟨D, hD⟩ := SmoothRadial.shrinkingFamily_slices
      (N := d.chart.NegativeCoordinates) ha ha₁ t
    refine ⟨(Diffeomorph.refl (𝓡 n)
      (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ∞).prodCongr D, ?_⟩
    intro x
    exact Prod.ext rfl (hD x.2)
  have hfix : ∀ t x, x ∉ C → A (t, x) = x := by
    intro t x hx
    have hn : (3 / 2 : ℝ) ≤ ‖x.2‖ := le_of_not_ge
      (fun h => hx ⟨mem_univ _, mem_closedBall_zero_iff.mpr h⟩)
    exact Prod.ext rfl (SmoothRadial.shrinkingFamily_outer ha ha₁ t hn)
  obtain ⟨B, K, hK, hKtarget, hB, hB₀, hBt, hBfix, _, hchart⟩ :=
    SupportedDiffeomorph.exists_supported_isotopy_extension Φ hA hA₀ hAt hC hsource hfix
  have hpoint (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
      (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
      Φ (v, u.val) = d.beltClosedDiskMap (u, v) :=
    OpenDiffeomorph.partialDiffeomorph_apply e₀ x₀ (d.beltClosedDiskPoint (u, v))
  have hbelt (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
      Φ (v, 0) = d.surgery.beltSphere v := by
    rw [d.belt_eq]
    exact (OpenDiffeomorph.partialDiffeomorph_apply e₀ x₀
      (d.chart.beltZeroPoint d.radius d.radius_pos d.block v)).trans
        (d.chart.beltNeighborhoodDiffeomorph_zero hf n d.radius d.radius_pos d.block
          d.upper_regular v)
  have hBbelt : ∀ t v, B (t, d.surgery.beltSphere v) = d.surgery.beltSphere v := by
    intro t v
    have hx : (v, (0 : d.chart.NegativeCoordinates)) ∈ Φ.source :=
      (d.chart.beltZeroPoint d.radius d.radius_pos d.block v).property
    have hAcenter : A (t, (v, 0)) = (v, 0) :=
      Prod.ext rfl (SmoothRadial.shrinkingFamily_origin a t)
    have hh := hchart t (v, 0) hx
    rwa [hAcenter, hbelt] at hh
  obtain ⟨e, he⟩ := hBt 1
  refine ⟨K, hK, hKtarget, e, ⟨{
    family := B
    smooth := hB
    zero := hB₀
    one := fun x => (he x).symm
    slices := hBt
    fixedOutside := hBfix
    fixedOn := by
      rintro t _ ⟨v, rfl⟩
      exact hBbelt t v }⟩, ?_⟩
  intro u v
  have hx : (v, u.val) ∈ Φ.source := (d.beltClosedDiskPoint (u, v)).property
  have hAend : A (1, (v, u.val)) = (v, (d.normalDiskScale ha ha₁ u).val) := by
    exact Prod.ext rfl ((SmoothRadial.shrinkingFamily_one ha ha₁ u.val).trans
      (SmoothRadial.shrinkingDiffeomorph_inner ha ha₁ u.property))
  rw [he, ← hpoint u v, hchart 1 (v, u.val) hx, hAend, hpoint]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

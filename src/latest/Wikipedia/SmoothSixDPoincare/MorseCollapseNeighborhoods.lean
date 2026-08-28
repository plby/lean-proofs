import Wikipedia.SmoothSixDPoincare.SeparatedDegreeMaps
import Wikipedia.SmoothSixDPoincare.MorseCollapseLocalRegularity

/-!
# A separated local-degree neighborhood family for the actual Morse collapse

Construct the full finite family from the smooth embedded attaching sphere
and its native transverse belt crossings. Every neighborhood stays inside
the original new surgery interior and retains its actual coordinate
derivative and strictly inner local boundary.
-/

noncomputable section

open Set Metric Topology Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)

open Classical in
abbrev CollapseNeighborhoods (m : ℕ) (g : Hemisphere.Sphere m → d.UpperLevel) :=
  LocalDegree.SeparatedNeighborhoods (EuclideanSpace ℝ (Fin m))
    (d.beltIntersectionPoints m g) (d.collapseNormal ∘ g) (g ⁻¹' d.surgery.NewInterior)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem nonempty_collapseNeighborhoods [T2Space M] [CompactSpace M] (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_hinj : Injective g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y), Nonempty (d.CollapseNeighborhoods m g) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  have hfin := d.finite_beltIntersectionPoints hf n m hdim g hg hinj ht
  apply LocalDegree.nonempty_separatedNeighborhoods (EuclideanSpace ℝ (Fin m)) hfin
  · exact fun x hx => d.contMDiffAt_collapseNormal_comp hf m g hg x hx
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    change d.collapseNormal (g x) = 0
    rw [← hv, d.collapseNormal_belt]
  · exact fun x hx =>
      d.isInvertible_collapseNormal_comp_of_transverse hf n m hdim g hg ht x hx
  · intro x hx
    apply hg.continuous.continuousAt
    apply d.surgery.isOpen_newInterior.mem_nhds
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    exact d.surgery.beltSphere_mem_newInterior v

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

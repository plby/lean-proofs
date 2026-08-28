import Wikipedia.HopfProblem.DegreeCollapseNativePrescribedPassage
import Wikipedia.HopfProblem.DegreeCollapseFiniteSurfaceImage

/-!
# A prescribed-sign native passage relative to the whole finite family

Represent every other original sphere by its exact finite disjoint-sum
image. The selected native passage has compact support disjoint from that
whole image and realizes either requested integral unit.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology MorseRearrangement

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {ι E M : Type} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}

theorem exists_native_prescribed_finite_family_passage
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (a : ι → C(S₂, d.UpperLevel))
    (hpair : Pairwise (fun j k => Disjoint (range (a j)) (range (a k))))
    (i : ι) (hfe : IsEmbedding (a i))
    (hdisj : Disjoint (range (a i)) (range d.surgery.beltSphere))
    (x : S₂) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (hv : d.surgery.beltSphere v ∉ otherSheetImages (fun j => a j) i)
    (γ : Path (a i x) (d.surgery.beltSphere v)) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (a j)) →
    (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (a i) z)) →
    ∃ A : CenteredSheetPassage (RegularLevel.Model E) (a i) d.surgery.beltSphere
        x v (otherSheetImages (fun j => a j) i),
      ∃ L : P₃ ≃L[ℝ] d.chart.NegativeCoordinates,
        HasFDerivAt (fun z : P₃ => d.beltNormal (A.family
          ((radialParameterChart (1 / 2) x z).1, a i (radialParameterChart (1 / 2) x z).2)))
          L.toContinuousLinearMap 0 ∧
        singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
          k • singularHomologyMap ((SphereCoordinates.standardParametrization
            d.chart.NegativeCoordinates 2).toHomeomorph :
              C(S₂, sphere (0 : d.chart.NegativeCoordinates) 1)) 2 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro ha hfi
  obtain ⟨n, b, hb, hbrange⟩ := exists_sheetSumMap_for_finite_family
    (fun j : {j : ι // j ≠ i} => a j.val) (fun j => ha j.val)
  have hrange : range b = otherSheetImages (fun j => a j) i := hbrange
  have hbc : IsClosed (range b) := (isCompact_range hb.continuous).isClosed
  have hx : a i x ∉ range b := by
    rw [hrange]
    intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hpair (Ne.symm j.property)) (mem_range_self x) hj
  have hvb : d.surgery.beltSphere v ∉ range b := by rwa [hrange]
  obtain ⟨A, L, hL, hunit⟩ := exists_native_prescribed_centered_passage d hf hdim
    (a i) hfe hdisj b hbc x v hx hvb γ k hk (ha i) hfi hb
  let A' : CenteredSheetPassage (RegularLevel.Model E) (a i) d.surgery.beltSphere
      x v (otherSheetImages (fun j => a j) i) := {
    A with avoids := by rw [← hrange]; exact A.avoids }
  exact ⟨A', L, hL, hunit⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

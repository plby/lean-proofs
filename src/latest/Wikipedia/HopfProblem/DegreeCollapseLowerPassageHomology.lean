import Wikipedia.HopfProblem.DegreeCollapseTransportedMeridianHomotopy

/-!
# The actual lower-level homology relation of a single belt passage

Construct the common-flow complement map and apply it to the actual
punctured passage trace. The resulting endpoint-plus-link identity holds
in the original lower level. The same complement map sends every native
normalized belt meridian to the original attaching sphere up to homotopy.
Identifying the trace's small link with a unit native meridian is separate.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_lower_passage_homology_relation
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    (u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (H : C(ℝ × Hemisphere.Sphere 2, (S.data p).UpperLevel))
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (x₀ : Hemisphere.Sphere 2)
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Hemisphere.Sphere 2,
      H (t, x) ∈ range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀) :
    ∃ D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
      (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
      (∀ (w : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
        (s : unitInterval) (hs : 0 < (s : ℝ)),
        (D.comp (nativeUpperMeridianInComplement S p w s hs)).Homotopic
          (S.data p).surgery.attachingSphere) ∧
      let G := D.comp (puncturedPassageTrace H (range (S.data p).surgery.beltSphere) hτ x₀ hcross)
      (∀ z : ({(τ, x₀)}ᶜ : Set (ℝ × Hemisphere.Sphere 2)), z.val.1 ∈ Icc (0 : ℝ) 1 →
        ∃ t : ℝ, S.flow t (H z.val).val = (G z).val) ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
        singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
          singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
            singularHomologyMap (G.comp (cylinderLink τ x₀ ε hε hεx)) 2 := by
  obtain ⟨D, horbit, hunique, hmeridian⟩ := S.exists_lower_transport_with_meridians hf p u v
  refine ⟨D, horbit, hunique, hmeridian, ?_, ?_⟩
  · intro z hz
    have hh := horbit (puncturedPassageTrace H (range (S.data p).surgery.beltSphere) hτ x₀ hcross z)
    rw [puncturedPassageTrace_on_interval H (range (S.data p).surgery.beltSphere) hτ x₀ hcross z hz]
      at hh
    exact hh
  · intro ε hε hεx
    exact punctured_cylinder_trace_relation hτ x₀ hε hεx
      (D.comp (puncturedPassageTrace H (range (S.data p).surgery.beltSphere) hτ x₀ hcross))
      2 (by decide)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

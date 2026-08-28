import Wikipedia.HopfProblem.DegreeCollapseGeneralSurgeryCancellation
import Wikipedia.HopfProblem.DegreeCollapseRegularBandReplacement
import Wikipedia.HopfProblem.DegreeCollapseRegularSublevelBody

/-!
# Unique adjacent Morse-pair cancellation preserves the native smooth boundary

Use the constructed cancellation of the original Morse function, rather
than the whole-handle quotient homeomorphism. Compactness and native
Fermat retain the original band endpoints after cancellation. Smooth
regular-band transport then gives an ambient diffeomorphism carrying
the original lower sublevel to the original upper sublevel, together
with its actual restriction between their independently native atlases.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_adjacent_pair_native_boundary_transport
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (k l : ℕ) (hpk : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = k)
    (hqk : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = k + 1)
    (hpl : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = l + 1) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    letI := RegularLevel.chartedSpace hf (S.data p).lower_regular
    letI := RegularLevel.chartedSpace hf (S.data q).upper_regular
    letI : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = k + 1) := ⟨hqk⟩
    letI : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = l + 1) := ⟨hpl⟩
    ∀ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data p).UpperLevel (S.data q).LowerLevel ∞,
      (∀ x : (S.data p).UpperLevel, ∃ t, S.flow t x = (b x : M)) →
      ∀ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).UpperLevel (S.data p).UpperLevel ∞,
        IsotopicToIdentity e →
        (∀ x y, NativeTransversality.At (𝓡 k) (𝓡 l) 𝓘(ℝ, RegularLevel.Model E)
          (e ∘ (S.data p).transportedAttachingSphere (S.data q) k b.toHomeomorph)
          (S.data p).surgery.beltSphere x y) →
        (range (e ∘ (S.data p).transportedAttachingSphere (S.data q) k b.toHomeomorph) ∩
          range (S.data p).surgery.beltSphere).ncard = 1 →
        ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
          D '' {x : M | f x = S.toSurgeryWindows.lower p} =
            {x : M | f x = S.toSurgeryWindows.upper q} ∧
          D '' {x : M | f x ≤ S.toSurgeryWindows.lower p} =
            {x : M | f x ≤ S.toSurgeryWindows.upper q} ∧
          ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
              (S.data p).LowerLevel (S.data q).UpperLevel ∞,
            (∀ x, (d x : M) = D x) ∧
            ∃ r : SmoothBoundaryBody.Equiv ((S.data p).lowerSmoothBody hf)
                ((S.data q).upperSmoothBody hf),
              ∀ x, (r.body x).val = D x.val := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = k + 1) := ⟨hqk⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = l + 1) := ⟨hpl⟩
  intro b horbit e he ht hsingle
  obtain ⟨g, hg, _hmg, _hcount, hcrit, hkeep⟩ :=
    S.cancel_adjacent_transverse_spheres hf hm p q hpq hconsecutive
      k l hpk hqk hpl b horbit e he ht hsingle
  have hreg (x : M)
      (hx : f x ∈ Icc (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q)) :
      x ∉ criticalPoints E g := by
    intro h
    obtain ⟨hxf, hxp, hxq⟩ := (hcrit x).mp h
    exact (surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive x hxf hx).elim
      hxp hxq
  obtain ⟨D, hlevel, hsublevel, d, hd⟩ :=
    RegularBandReplacement.exists_native_level_transport hf hg
      (fun x hx => (hkeep x hx).self_of_nhds) hreg
      ((S.toSurgeryWindows.lower_lt_value p).le.trans
        (hpq.le.trans (S.toSurgeryWindows.value_lt_upper q).le))
      (S.data p).lower_regular (S.data q).upper_regular
  obtain ⟨r, hr⟩ := RegularMorseSublevel.exists_bodyEquiv_of_ambient hf
    (S.data p).lower_regular (S.data q).upper_regular D hlevel hsublevel
  exact ⟨D, hlevel, hsublevel, d, hd, r, hr⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

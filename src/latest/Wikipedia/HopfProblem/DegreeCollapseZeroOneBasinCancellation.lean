import Wikipedia.HopfProblem.DegreeCollapseGeneralSurgeryCancellation
import Wikipedia.HopfProblem.DegreeCollapseIndexZeroBeltRegularity
import Wikipedia.HopfProblem.DegreeCollapseSurvivingMorseGerms
import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation

/-!
# Exact zero/one cancellation from a single original basin crossing

The common-flow band bridge is constructed. Index-zero belt transversality
is automatic, and the entire native basin identities give the one actual
attaching intersection. The global Morse replacement removes exactly the
zero/one pair, retains the surviving germs, recovers excellence and a new
compatible surgery system, and decreases precisely the two indexed counts.
Selecting such a crossing from connectedness remains a separate obligation.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.cancel_zero_one_single_basin
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hzero : nativeMorseIndex E f p = 0) (hone : nativeMorseIndex E f q = 1)
    (hsingle : {x : (S.data p).UpperLevel |
      Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)}.ncard = 1) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val) ∧
      (∀ z, f z ∉ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
        g =ᶠ[𝓝 z] f) ∧
      (∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) ∧
      InjOn g (criticalPoints E g) ∧ Nonempty (AdaptedSurgeryWindows E g) ∧
      nativeMorseCount E g 0 + 1 = nativeMorseCount E f 0 ∧
      nativeMorseCount E g 1 + 1 = nativeMorseCount E f 1 ∧
      ∀ k, k ≠ 0 → k ≠ 1 → nativeMorseCount E g k = nativeMorseCount E f k := by
  have hp0 : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 0 := by
    rwa [nativeMorseIndex_eq_chart (S.data p).chart] at hzero
  have hq1 : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0 + 1 := by
    rwa [nativeMorseIndex_eq_chart (S.data q).chart] at hone
  let n := Module.finrank ℝ E - 1
  have hpn : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = n + 1 := by
    have hpdim := (S.data p).chart.finrank_negative_add_positive
    have hqdim := (S.data q).chart.finrank_negative_add_positive
    dsimp [n]
    omega
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0 + 1) := ⟨hq1⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = n + 1) := ⟨hpn⟩
  obtain ⟨D, b, -, hb, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  have horbit' (x : (S.data p).UpperLevel) : ∃ t, S.flow t x = (b x : M) := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, ht.trans (hb x).symm⟩
  let α := (S.data p).transportedAttachingSphere (S.data q) 0 b.toHomeomorph
  have hgeom : (range α ∩ range (S.data p).surgery.beltSphere).ncard = 1 := by
    have heq : {x : (S.data p).UpperLevel |
        Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} =
        range α ∩ range (S.data p).surgery.beltSphere := by
      ext x
      exact and_congr (S.transported_attaching_basin_iff hf p q 0 b.toHomeomorph horbit' x)
        (S.belt_basin_iff hf p x)
    rwa [heq] at hsingle
  let e := Diffeomorph.refl 𝓘(ℝ, RegularLevel.Model E) (S.data p).UpperLevel ∞
  have ht : ∀ x y, NativeTransversality.At (𝓡 0) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
      (e ∘ α) (S.data p).surgery.beltSphere x y :=
    nativeAt_index_zero_belt (𝓡 0) (S.data p) hf hp0 n (e ∘ α)
  obtain ⟨g, hg, hmg, hcard, hcrit, hexterior⟩ :=
    S.cancel_adjacent_transverse_spheres hf hm p q hpq hconsecutive 0 n hp0 hq1 hpn b horbit'
      e SupportedDiffeomorph.isotopicToIdentity_refl ht hgeom
  obtain ⟨hkeep, hinj, hnew⟩ := adapted_surgeries_after_pair_removal S.toSurgeryWindows p q
    hconsecutive hg hmg hcrit hexterior
  have hne : p.val ≠ q.val := fun heq => (ne_of_lt hpq) (congrArg f heq)
  obtain ⟨hc0, hc1, hcother⟩ := nativeMorseCount_adjacent_pair S.finite p.property q.property hne
    hcrit hkeep hzero hone
  exact ⟨g, hg, hmg, hcard, hcrit, hexterior, hkeep, hinj, hnew, hc0, hc1, hcother⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

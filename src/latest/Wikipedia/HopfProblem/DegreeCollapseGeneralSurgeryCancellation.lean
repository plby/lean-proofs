import Wikipedia.HopfProblem.DegreeCollapseGeometricSurgeryCancellation

/-!
# Actual Morse cancellation for every adjacent index

The attaching and belt basin argument is independent of the middle-index
values two and three. With the actual sphere dimensions explicit, one
transverse intersection after a native level isotopy constructs exact
Morse-function cancellation of any consecutive adjacent-index pair.
This includes the outer pairs needed for index-zero and index-one removal.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.cancel_adjacent_transverse_spheres
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (k l : ℕ) (hpk : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = k)
    (hqk : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = k + 1)
    (hpl : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = l + 1) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
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
        ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
          (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
          (∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val) ∧
          ∀ z, f z ∉ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
            g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = k + 1) := ⟨hqk⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = l + 1) := ⟨hpl⟩
  intro b horbit e he ht hsingle
  let α := (S.data p).transportedAttachingSphere (S.data q) k b.toHomeomorph
  let β := e.symm ∘ (S.data p).surgery.beltSphere
  let g : C(Hemisphere.Sphere k, (S.data p).UpperLevel) := ⟨e ∘ α, e.continuous.comp α.continuous⟩
  have hα : ContMDiff (𝓡 k) 𝓘(ℝ, RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf k b
  have hg : ContMDiff (𝓡 k) 𝓘(ℝ, RegularLevel.Model E) ∞ g := e.contMDiff.comp hα
  have hB := (S.data p).belt_smooth hf l
  have hβ : ContMDiff (𝓡 l) 𝓘(ℝ, RegularLevel.Model E) ∞ β := e.symm.contMDiff.comp hB
  have hαeq : e.symm ∘ g = α := by
    funext x
    exact e.symm_apply_apply (α x)
  have hrange (w : (S.data p).UpperLevel) : w ∈ range α ↔ e w ∈ range g := by
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, e.injective hv⟩
  change (range g ∩ range (S.data p).surgery.beltSphere).ncard = 1 at hsingle
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hsingle
  have hzmem : z ∈ range g ∩ range (S.data p).surgery.beltSphere := by
    rw [hz]
    exact mem_singleton z
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hzmem
  have hcross : (S.data p).surgery.beltSphere y = g x := hy.trans hx.symm
  have hcross' : β y = α x := by
    rw [← hαeq]
    exact congrArg e.symm hcross
  have htrans : NativeTransversality.At (𝓡 k) (𝓡 l) 𝓘(ℝ, RegularLevel.Model E) α β x y := by
    have hh := (TransverseGerms.native_transversality_partial_diffeomorph_iff
      e.symm.toPartialDiffeomorph (hg.mdifferentiableAt (by simp))
        (hB.mdifferentiableAt (by simp)) hcross (mem_univ _)).mp (ht x y)
    change NativeTransversality.At (𝓡 k) (𝓡 l) 𝓘(ℝ, RegularLevel.Model E)
      (e.symm ∘ g) β x y at hh
    rwa [hαeq] at hh
  have hcount : {w : (S.data p).UpperLevel |
      Tendsto (fun t => S.flow t w) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t (e w)) atTop (𝓝 p.val)}.ncard = 1 := by
    have hk : {w : (S.data p).UpperLevel |
        Tendsto (fun t => S.flow t w) atBot (𝓝 q.val) ∧
        Tendsto (fun t => S.flow t (e w)) atTop (𝓝 p.val)} = {e.symm z} := by
      ext w
      change (_ ∧ _) ↔ w = e.symm z
      rw [S.transported_attaching_basin_iff hf p q k b.toHomeomorph horbit w,
        S.belt_basin_iff hf p (e w), hrange w]
      change e w ∈ range g ∩ range (S.data p).surgery.beltSphere ↔ w = e.symm z
      rw [hz, mem_singleton_iff]
      exact ⟨fun h => (e.symm_apply_apply w).symm.trans (congrArg e.symm h),
        fun h => (congrArg e h).trans (e.apply_symm_apply z)⟩
    rw [hk, Set.ncard_singleton]
  have hαbasin : ∀ᶠ w in 𝓝 x, Tendsto (fun t => S.flow t (α w)) atBot (𝓝 q.val) :=
    Eventually.of_forall fun w =>
      (S.transported_attaching_basin_iff hf p q k b.toHomeomorph horbit (α w)).mpr ⟨w, rfl⟩
  have hβbasin : ∀ᶠ w in 𝓝 y, Tendsto (fun t => S.flow t (e (β w))) atTop (𝓝 p.val) := by
    apply Eventually.of_forall
    intro w
    change Tendsto (fun t => S.flow t (e (e.symm ((S.data p).surgery.beltSphere w))))
      atTop (𝓝 p.val)
    rw [e.apply_symm_apply]
    exact (S.belt_basin_iff hf p _).mpr ⟨w, rfl⟩
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  have hdim : Module.finrank ℝ E = (k + l) + 1 := by
    have hh := (S.data p).chart.finrank_negative_add_positive
    omega
  have hweightp : Fintype.card {i // (S.data p).chart.weights i = -1} = k := by
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hpk
  have hweightq : Fintype.card {i // (S.data q).chart.weights i = -1} = k + 1 := by
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hqk
  exact cancel_of_transverse_level_isotopy (m := k + l) (S.data p).chart (S.data q).chart
    hf hm hdim (by omega) S.field S.smooth S.zero S.descent S.flow S.integral S.distinct
    p.property q.property (S.toSurgeryWindows.lower_lt_value p)
    (S.toSurgeryWindows.value_lt_upper q)
    (surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive)
    hac hcb hpc hqc (surgery_pair_inner_band_regular S.toSurgeryWindows p q hconsecutive hpa hbq)
    (S.data p).upper_regular (S.critical_model_germ p) (S.critical_model_germ q)
    e he hcount α β x y (hα.mdifferentiableAt (by simp)) (hβ.mdifferentiableAt (by simp))
    hcross' htrans hαbasin hβbasin

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

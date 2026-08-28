import Wikipedia.HopfProblem.DegreeCollapseConjugateLevelIsotopy

/-!
# Cancel after a unit coordinate is realized on a preserved native belt cut

The old native surgery supplies the collapse coordinate and Whitney
contractions. The current flow supplies the full attaching basin and has
the same forward basin on the literal cut. Conjugate the actual old-level
isotopy into the current native atlas and apply basin-section cancellation.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f g : M → ℝ}

theorem cancel_from_preserved_unit_belt_cut
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : IsMorse E g)
    (hdim : Module.finrank ℝ E = 6) (p : criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull : ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hpcg : p.val ∈ criticalPoints E g) (hpg : nativeMorseIndex E g p = 2)
    (q : criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hconsecutive : ∀ z : criticalPoints E g, ¬(g p < g z ∧ g z < g q))
    (hpc : g p < (f p + (S.data p).radius ^ 2)) (hcq : (f p + (S.data p).radius ^ 2) < g q)
    (hsub : ∀ y, g y ≤ (f p + (S.data p).radius ^ 2) ↔ f y ≤ (f p + (S.data p).radius ^ 2))
    (hlevel : ∀ y, g y = (f p + (S.data p).radius ^ 2) ↔ f y = (f p + (S.data p).radius ^ 2))
    (hga : ∀ y, g y = (f p + (S.data p).radius ^ 2) → y ∉ criticalPoints E g)
    (hforward : ∀ y : (S.data p).UpperLevel,
      Tendsto (fun t => T.flow t y.val) atTop (𝓝 p.val) ↔
        Tendsto (fun t => S.flow t y.val) atTop (𝓝 p.val))
    (γ : C(S₂, {y : M // g y = (f p + (S.data p).radius ^ 2)})) :
    letI := RegularLevel.chartedSpace hg hga
    ∀ (hγ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ)
      (hinj : Injective γ)
      (himm : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ x)),
      (∀ y, y ∈ range γ ↔ Tendsto (fun t => T.flow t y.val) atBot (𝓝 q.val)) →
      ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex
        ((equalCutHomologyEquiv hsub).symm (middleSectionClass γ))).natAbs = 1 →
      ∃ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧ IsMorse E v ∧
        (criticalPoints E v).ncard + 2 = (criticalPoints E g).ncard ∧
        (∀ z, z ∈ criticalPoints E v ↔
          z ∈ criticalPoints E g ∧ z ≠ p.val ∧ z ≠ q.val) ∧
        ∀ z, g z ∉ Ioo (T.toSurgeryWindows.lower ⟨p.val, hpcg⟩) (T.toSurgeryWindows.upper q) →
          v =ᶠ[𝓝 z] g := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hg hga
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := (S.data p).chart.finrank_negative_add_positive; omega⟩
  intro hγ hinj himm hback hunit
  let e := equalLevelDiffeomorph hf hg (S.data p).upper_regular hga hlevel
  let α : C(S₂, (S.data p).UpperLevel) := equalCutSection (fun y => (hlevel y).symm) γ
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (e.symm ∘ γ)
    exact e.symm.contMDiff.comp hγ
  have hαinj : Injective α := e.symm.injective.comp hinj
  have hαimm (x : S₂) : Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) α x) := by
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e.symm ∘ γ) x)
    rw [mfderiv_comp x (e.symm.contMDiff.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))]
    exact (e.symm.mfderivToContinuousLinearEquiv (by simp) (γ x)).injective.comp (himm x)
  have hsection : equalCutSection hlevel α = γ := rfl
  have hclass := equalCutSection_class hsub hlevel α
  rw [hsection] at hclass
  have hpull : (equalCutHomologyEquiv hsub).symm (middleSectionClass γ) = middleSectionClass α := by
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hαunit : ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex
      (middleSectionClass α)).natAbs = 1 := by
    rwa [hpull] at hunit
  obtain ⟨D, δ, hD, hδ, hgood, hsingle⟩ := exists_single_intersection_of_unit_coordinate
    (S.data p) hf hdim hindex hnull α hα hαinj hαimm hαunit
  let β₀ := (S.data p).surgery.beltSphere
  let β := e ∘ β₀
  have hβ₀ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β₀ := (S.data p).belt_smooth hf 3
  have hβ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β := e.contMDiff.comp hβ₀
  let D' := e.symm.trans (D.trans e)
  have hD' : IsotopicToIdentity D' := conjugate_level_isotopy e D hD
  have hDγ : D' ∘ γ = e ∘ δ := by
    funext x
    change e (D (α x)) = e (δ x)
    exact congrArg e (hδ x).symm
  have hβfull (y : {z : M // g z = (f p + (S.data p).radius ^ 2)}) :
      y ∈ range β ↔ Tendsto (fun t => T.flow t y.val) atTop (𝓝 p.val) := by
    have hmem : y ∈ range β ↔ e.symm y ∈ range β₀ := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, e.injective (hx.trans (e.apply_symm_apply y).symm)⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem]
    exact (S.belt_basin_iff hf p (e.symm y)).symm.trans (hforward (e.symm y)).symm
  have ht : ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
      (D' ∘ γ) β x y := by
    rw [hDγ]
    intro x y hxy
    have hold : β₀ y = δ x := e.injective hxy
    have hh := (TransverseGerms.native_transversality_partial_diffeomorph_iff
      e.toPartialDiffeomorph (hgood.1.mdifferentiableAt (by simp))
        (hβ₀.mdifferentiableAt (by simp)) hold (mem_univ _)).mp (hgood.2.2.2 x y)
    exact hh hxy
  have hcount : (range (D' ∘ γ) ∩ range β).ncard = 1 := by
    rw [hDγ]
    exact (intersection_count_under_injective_map e e.injective δ β₀).trans hsingle
  exact T.cancel_single_basin_section_isotopy hg hmg hdim ⟨p.val, hpcg⟩ q
    hconsecutive hpg hq hpc hcq hga γ β hγ hβ hback hβfull D' hD' ht hcount

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

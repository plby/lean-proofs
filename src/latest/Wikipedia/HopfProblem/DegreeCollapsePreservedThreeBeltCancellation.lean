import Wikipedia.HopfProblem.DegreeCollapseFourCommonCutFamily
import Wikipedia.HopfProblem.DegreeCollapseUnitThreeFourPairCancellation
import Wikipedia.HopfProblem.DegreeCollapseConjugateLevelIsotopy

/-!
# Native three/four cancellation using the preserved original belt cut

Pull the actual current sphere through the literal native level identity.
The original three-handle collapse coordinate and lower loop contractions
construct the Whitney isotopy. Conjugate that actual isotopy to the current
level atlas; the retained forward basin identifies its unique crossing.
Native transverse realization then cancels the current consecutive pair,
preserving the original outer cut and all surviving critical indices.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f g : M → ℝ}

theorem cancel_from_preserved_three_belt_unit
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : IsMorse E g)
    (hdim : Module.finrank ℝ E = 7) (p : criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 3)
    (hnull : ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hpcg : p.val ∈ criticalPoints E g) (hpg : nativeMorseIndex E g p = 3)
    (q : criticalPoints E g) (hq : nativeMorseIndex E g q = 4)
    (hconsecutive : ∀ z : criticalPoints E g, ¬(g p < g z ∧ g z < g q))
    {b : ℝ} (hqb : g q < b)
    (hpc : g p < (f p + (S.data p).radius ^ 2))
    (hcq : (f p + (S.data p).radius ^ 2) < g q)
    (hsub : ∀ y, g y ≤ (f p + (S.data p).radius ^ 2) ↔
      f y ≤ (f p + (S.data p).radius ^ 2))
    (hlevel : ∀ y, g y = (f p + (S.data p).radius ^ 2) ↔
      f y = (f p + (S.data p).radius ^ 2))
    (hga : ∀ y, g y = (f p + (S.data p).radius ^ 2) → y ∉ criticalPoints E g)
    (hforward : ∀ y : (S.data p).UpperLevel,
      Tendsto (fun t => T.flow t y.val) atTop (𝓝 p.val) ↔
        Tendsto (fun t => S.flow t y.val) atTop (𝓝 p.val))
    (γ : C(S₃, {y : M // g y = (f p + (S.data p).radius ^ 2)})) :
    letI := RegularLevel.chartedSpace hg hga
    ∀ (_hγ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ γ)
      (_hinj : Injective γ)
      (_himm : ∀ x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) γ x)),
      (∀ y, y ∈ range γ ↔ Tendsto (fun t => T.flow t y.val) atBot (𝓝 q.val)) →
      (MiddleBasis.collapseCoordinate (S.data p) 1 hf.continuous hindex
        ((equalFourCutHomologyEquiv hsub).symm (threeSectionClass γ))).natAbs = 1 →
      ∃ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧ IsMorse E v ∧
        InjOn v (criticalPoints E v) ∧
        (criticalPoints E v).ncard + 2 = (criticalPoints E g).ncard ∧
        (∀ z, z ∈ criticalPoints E v ↔
          z ∈ criticalPoints E g ∧ z ≠ p.val ∧ z ≠ q.val) ∧
        (∀ z ∈ criticalPoints E v, nativeMorseIndex E v z = nativeMorseIndex E g z) ∧
        (∀ z, b ≤ g z → v =ᶠ[𝓝 z] g) ∧ ∀ z, v z < b ↔ g z < b := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hg hga
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := (S.data p).chart.finrank_negative_add_positive; omega⟩
  intro hγ hinj himm hback hunit
  let e := equalLevelDiffeomorph hf hg (S.data p).upper_regular hga hlevel
  let α : C(S₃, (S.data p).UpperLevel) :=
    equalFourCutSection (fun y => (hlevel y).symm) γ
  have hα : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ α := by
    change ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ (e.symm ∘ γ)
    exact e.symm.contMDiff.comp hγ
  have hαinj : Injective α := e.symm.injective.comp hinj
  have hαimm (x : S₃) : Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) α x) := by
    change Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (e.symm ∘ γ) x)
    rw [mfderiv_comp x (e.symm.contMDiff.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))]
    exact (e.symm.mfderivToContinuousLinearEquiv (by simp) (γ x)).injective.comp (himm x)
  have hsection : equalFourCutSection hlevel α = γ := rfl
  have hclass := equalFourCutSection_class hsub hlevel α
  rw [hsection] at hclass
  have hpull : (equalFourCutHomologyEquiv hsub).symm (threeSectionClass γ) =
      threeSectionClass α := by
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hαunit : (MiddleBasis.collapseCoordinate (S.data p) 1 hf.continuous hindex
      (threeSectionClass α)).natAbs = 1 := by
    rwa [hpull] at hunit
  obtain ⟨D, δ, x, hD, hplace, hgood, hpoints, _⟩ :=
    exists_single_three_belt_intersection_of_unit_coordinate (S.data p) hf hdim
      hindex hnull α hαunit hα hαinj hαimm
  let δ' : C(S₃, {y : M // g y = (f p + (S.data p).radius ^ 2)}) :=
    equalFourCutSection hlevel δ
  let D' := e.symm.trans (D.trans e)
  have hD' : IsotopicToIdentity D' := conjugate_level_isotopy e D hD
  have hplace' (z : S₃) : δ' z = D' (γ z) := by
    change e (δ z) = e (D (α z))
    exact congrArg e (hplace z)
  have hplacement (y : {z : M // g z = (f p + (S.data p).radius ^ 2)}) :
      Tendsto (fun t => T.flow t y.val) atBot (𝓝 q.val) ↔ D' y ∈ range δ' := by
    rw [← hback]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hplace' z⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, D'.injective ((hplace' z).symm.trans hz)⟩
  have hsingle (z : S₃) :
      Tendsto (fun t => T.flow t (δ' z).val) atTop (𝓝 p.val) ↔ z = x := by
    change Tendsto (fun t => T.flow t (δ z).val) atTop (𝓝 p.val) ↔ z = x
    rw [hforward (δ z), S.belt_basin_iff hf p]
    change z ∈ (S.data p).beltIntersectionPoints 3 δ ↔ z = x
    rw [hpoints]
    rfl
  have hcount := unit_level_count_of_circle_placement T.flow D'.toEquiv δ' x hplacement hsingle
  have hx : x ∈ (S.data p).beltIntersectionPoints 3 δ := by
    rw [hpoints]
    exact mem_singleton x
  obtain ⟨v, hv⟩ := hx
  let β₀ := (S.data p).surgery.beltSphere
  let β' := e ∘ β₀
  have hβ₀ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β₀ :=
    (S.data p).belt_smooth hf 3
  have hβ' : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β' :=
    e.contMDiff.comp hβ₀
  have hcross' : β' v = δ' x := congrArg e hv
  have htrans' : NativeTransversality.At (𝓡 3) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
      δ' β' x v :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff
      e.toPartialDiffeomorph (hgood.1.mdifferentiableAt (by simp))
        (hβ₀.mdifferentiableAt (by simp)) hv (mem_univ _)).mp (hgood.2.2.2 x v)
  obtain ⟨β, hβ, hcross, htrans, hDβ⟩ := exists_transverse_sheet_of_circle_placement D'
    (hγ.mdifferentiableAt (by simp)) (hβ'.mdifferentiableAt (by simp))
    (fun z => (hplace' z).symm) hcross' htrans'
  have hγbasin : ∀ᶠ z in 𝓝 x,
      Tendsto (fun t => T.flow t (γ z).val) atBot (𝓝 q.val) :=
    Filter.Eventually.of_forall (fun z => (hback (γ z)).mp (mem_range_self z))
  have hβbasin : ∀ᶠ z in 𝓝 v,
      Tendsto (fun t => T.flow t (D' (β z)).val) atTop (𝓝 p.val) := by
    apply Filter.Eventually.of_forall
    intro z
    rw [hDβ z]
    change Tendsto (fun t => T.flow t (β₀ z).val) atTop (𝓝 p.val)
    rw [hforward (β₀ z)]
    exact (S.belt_basin_iff hf p (β₀ z)).mpr (mem_range_self z)
  have hidx : nativeMorseIndex E g q =
      nativeMorseIndex E g (⟨p.val, hpcg⟩ : criticalPoints E g) + 1 := by
    rw [hq, hpg]
  exact T.cancel_unit_consecutive_level_isotopy_below_cut hg hmg (m := 6) hdim
    ⟨p.val, hpcg⟩ q hpc hcq hqb hconsecutive hidx hga
      D' hD' hcount γ β x v (hγ.mdifferentiableAt (by simp)) hβ hcross htrans hγbasin hβbasin

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

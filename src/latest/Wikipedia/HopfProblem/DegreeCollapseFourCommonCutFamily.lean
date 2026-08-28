import Wikipedia.HopfProblem.DegreeCollapseCommonCutFamily
import Wikipedia.HopfProblem.DegreeCollapseIndexFourBasinFamily
import Wikipedia.HopfProblem.DegreeCollapseFourSectionSpanning

/-!
# Identity on the original common cut retains the four-handle family and matrix

The identity on ambient points identifies equal sublevels and regular levels.
It transports the exact parametrized sphere maps, their homology classes and
their basis coordinates. With the same complete flow, every labelled full
backward-basin image and all native embedding and immersion data persist.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f g : M → ℝ} {a : ℝ}

def equalFourCutSection (hlevel : ∀ y, g y = a ↔ f y = a)
    (γ : C(S₃, {y : M // f y = a})) : C(S₃, {y : M // g y = a}) :=
  ⟨fun x => ⟨(γ x).val, (hlevel _).mpr (γ x).property⟩,
    (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩

def equalFourCutHomologyEquiv (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) :
    SingularHomology {y : M // f y ≤ a} 3 ≃ₗ[ℤ]
      SingularHomology {y : M // g y ≤ a} 3 :=
  homotopyEquivHomologyEquiv (equalCutSublevelHomeomorph hsub).toHomotopyEquiv 3

omit [T2Space M] [CompactSpace M] in
theorem equalFourCutSection_class (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C(S₃, {y : M // f y = a})) :
    equalFourCutHomologyEquiv hsub (threeSectionClass γ) =
      threeSectionClass (equalFourCutSection hlevel γ) := by
  have hmaps : (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun.comp
      ((levelSublevelMap f le_rfl).comp γ) =
      (levelSublevelMap g le_rfl).comp (equalFourCutSection hlevel γ) := by
    apply ContinuousMap.ext
    intro x
    rfl
  change singularHomologyMap (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun 3
    (threeSectionClass γ) = _
  rw [threeSectionClass, ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]
  rfl

omit [T2Space M] [CompactSpace M] in
theorem canonicalFourMatrix_equalCut
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) (hlevel : ∀ y, g y = a ↔ f y = a)
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (γ : Fin n → C(S₃, {y : M // f y = a})) :
    canonicalFourMatrix (B.trans (equalFourCutHomologyEquiv hsub))
      (fun j => equalFourCutSection hlevel (γ j)) = canonicalFourMatrix B γ := by
  funext i j
  change B.symm ((equalFourCutHomologyEquiv hsub).symm
    (threeSectionClass (equalFourCutSection hlevel (γ j)))) i = B.symm (threeSectionClass (γ j)) i
  rw [← equalFourCutSection_class hsub hlevel, LinearEquiv.symm_apply_apply]

omit [CompactSpace M] in
theorem nativeFourBasinFamily_equalCut
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hga : ∀ y, g y = a → y ∉ criticalPoints E g)
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hlevel : ∀ y, g y = a ↔ f y = a) (hflow : T.flow = S.flow)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (γ : Fin n → C(S₃, {y : M // f y = a}))
    (hγ : IsNativeFourBasinFamily S hf ha p (fun j => γ j)) :
    IsNativeFourBasinFamily T hg hga
      (fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩)
      (fun j => equalFourCutSection hlevel (γ j)) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hg hga
  let e := equalLevelDiffeomorph hf hg ha hga hlevel
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hγ
  have hβs (j : Fin n) : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞
      (equalFourCutSection hlevel (γ j)) := by
    change ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ (e ∘ γ j)
    exact e.contMDiff.comp (hs j)
  refine ⟨hβs, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (hβs j).continuous.isClosedEmbedding
    change Injective (e ∘ γ j)
    exact e.injective.comp (he j).injective
  · intro j x
    change Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (e ∘ γ j) x)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp))
      ((hs j).mdifferentiableAt (by simp))]
    exact (e.mfderivToContinuousLinearEquiv (by simp) (γ j x)).injective.comp (hi j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hiy hjy
    obtain ⟨x, hx⟩ := hiy
    obtain ⟨z, hz⟩ := hjy
    have hsame : γ i x = γ j z := e.injective (hx.trans hz.symm)
    exact Set.disjoint_left.mp (hpair hij) (mem_range_self x) ⟨z, hsame.symm⟩
  · intro j y
    have hmem : y ∈ range (equalFourCutSection hlevel (γ j)) ↔
        e.symm y ∈ range (γ j) := by
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply e.injective
        exact hx.trans (e.apply_symm_apply y).symm
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem, hfull j]
    rw [hflow]
    rfl
variable {h : M → ℝ}

omit [T2Space M] [CompactSpace M] in
theorem equalFourCutSection_refl (γ : C(S₃, {y : M // f y = a})) :
    equalFourCutSection (fun _ => Iff.rfl) γ = γ := rfl

omit [T2Space M] [CompactSpace M] in
theorem equalFourCutSection_trans
    (hfg : ∀ y, g y = a ↔ f y = a) (hgh : ∀ y, h y = a ↔ g y = a)
    (γ : C(S₃, {y : M // f y = a})) :
    equalFourCutSection hgh (equalFourCutSection hfg γ) =
      equalFourCutSection (fun y => (hgh y).trans (hfg y)) γ := rfl

omit [T2Space M] [CompactSpace M] in
theorem equalFourCutHomologyEquiv_refl :
    equalFourCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl) =
      LinearEquiv.refl ℤ (SingularHomology {y : M // f y ≤ a} 3) := by
  apply LinearEquiv.ext
  intro x
  change singularHomologyMap
    (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun 3 x = x
  have hmap : (equalCutSublevelHomeomorph (f := f) (a := a)
      (fun _ => Iff.rfl)).toHomotopyEquiv.toFun = ContinuousMap.id {y : M // f y ≤ a} := rfl
  rw [hmap, singularHomologyMap_id]
  rfl

omit [T2Space M] [CompactSpace M] in
theorem equalFourCutHomologyEquiv_trans
    (hfg : ∀ y, g y ≤ a ↔ f y ≤ a) (hgh : ∀ y, h y ≤ a ↔ g y ≤ a) :
    (equalFourCutHomologyEquiv hfg).trans (equalFourCutHomologyEquiv hgh) =
      equalFourCutHomologyEquiv (fun y => (hgh y).trans (hfg y)) := by
  apply LinearEquiv.ext
  intro x
  change singularHomologyMap (equalCutSublevelHomeomorph hgh).toHomotopyEquiv.toFun 3
    (singularHomologyMap (equalCutSublevelHomeomorph hfg).toHomotopyEquiv.toFun 3 x) =
      singularHomologyMap (equalCutSublevelHomeomorph
        (fun y => (hgh y).trans (hfg y))).toHomotopyEquiv.toFun 3 x
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

import Wikipedia.HopfProblem.DegreeCollapseCommonCutValueExchange

/-!
# Retain the actual sphere family and matrix when a common cut is unchanged

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

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f g : M → ℝ} {a : ℝ}

def equalCutSection (hlevel : ∀ y, g y = a ↔ f y = a)
    (γ : C(S₂, {y : M // f y = a})) : C(S₂, {y : M // g y = a}) :=
  ⟨fun x => ⟨(γ x).val, (hlevel _).mpr (γ x).property⟩,
    (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩

def equalCutSublevelHomeomorph (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) :
    {y : M // f y ≤ a} ≃ₜ {y : M // g y ≤ a} where
  toFun y := ⟨y.val, (hsub y).mpr y.property⟩
  invFun y := ⟨y.val, (hsub y).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def equalCutHomologyEquiv (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) :
    SingularHomology {y : M // f y ≤ a} 2 ≃ₗ[ℤ]
      SingularHomology {y : M // g y ≤ a} 2 :=
  homotopyEquivHomologyEquiv (equalCutSublevelHomeomorph hsub).toHomotopyEquiv 2

theorem equalCutSection_class (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C(S₂, {y : M // f y = a})) :
    equalCutHomologyEquiv hsub (middleSectionClass γ) =
      middleSectionClass (equalCutSection hlevel γ) := by
  have hmaps : (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun.comp
      ((levelSublevelMap f le_rfl).comp γ) =
      (levelSublevelMap g le_rfl).comp (equalCutSection hlevel γ) := by
    apply ContinuousMap.ext
    intro x
    rfl
  change singularHomologyMap (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun 2
    (middleSectionClass γ) = _
  rw [middleSectionClass, ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]
  rfl

theorem canonicalMiddleMatrix_equalCut [Nonempty M]
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) (hlevel : ∀ y, g y = a ↔ f y = a)
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (γ : Fin n → C(S₂, {y : M // f y = a})) :
    canonicalMiddleMatrix (B.trans (equalCutHomologyEquiv hsub))
      (fun j => equalCutSection hlevel (γ j)) = canonicalMiddleMatrix B γ := by
  funext i j
  change B.symm ((equalCutHomologyEquiv hsub).symm
    (middleSectionClass (equalCutSection hlevel (γ j)))) i = B.symm (middleSectionClass (γ j)) i
  rw [← equalCutSection_class hsub hlevel, LinearEquiv.symm_apply_apply]

theorem nativeMiddleBasinFamily_equalCut
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hga : ∀ y, g y = a → y ∉ criticalPoints E g)
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hlevel : ∀ y, g y = a ↔ f y = a) (hflow : T.flow = S.flow)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (γ : Fin n → C(S₂, {y : M // f y = a}))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) :
    IsNativeMiddleBasinFamily T hg hga
      (fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩)
      (fun j => equalCutSection hlevel (γ j)) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hg hga
  let e := equalLevelDiffeomorph hf hg ha hga hlevel
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hγ
  have hβs (j : Fin n) : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞
      (equalCutSection hlevel (γ j)) := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (e ∘ γ j)
    exact e.contMDiff.comp (hs j)
  refine ⟨hβs, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (hβs j).continuous.isClosedEmbedding
    change Injective (e ∘ γ j)
    exact e.injective.comp (he j).injective
  · intro j x
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e ∘ γ j) x)
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
    have hmem : y ∈ range (equalCutSection hlevel (γ j)) ↔
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

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

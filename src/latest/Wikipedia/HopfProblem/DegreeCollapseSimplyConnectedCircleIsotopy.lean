import Wikipedia.HopfProblem.DegreeCollapseSimplyConnectedLevelDisks
import Wikipedia.HopfProblem.DegreeCollapseNewAttachingCirclePlacement

/-!
# Native circle placement from simple connectivity

Construct both disks in the actual middle level using simple connectivity
of the ambient manifold, then use native disk isotopy and the actual equal
level diffeomorphism. This places a newborn two-handle's entire backward
basin section on a prescribed embedded circle. All parametrizations and
whole-level basin equivalences are retained. The proofs adapt the existing
middle-level and equal-level constructions to the weaker filling theorem.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f : M → ℝ}

theorem exists_native_middle_level_circle_disk
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Hemisphere.Sphere 1, {y : M // f y = a})) :
    let _ := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ∃ g : C(Hemisphere.Ambient 2, {y : M // f y = a}),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      (∀ z : Hemisphere.Ball 2,
        Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, RegularLevel.Model E) g z.val)) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) → _
  intro hγ hγi hγd
  let γM : C(Hemisphere.Sphere 1, M) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γM :=
    (RegularLevel.contMDiff_inclusion hf hreg).comp hγ
  have hγMi : Injective γM := Subtype.val_injective.comp hγi
  have hγMd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γM z) := by
    intro z
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (Subtype.val ∘ γ) z)
    rw [mfderiv_comp z ((RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))]
    exact (RegularLevel.injective_mfderiv_inclusion hf hreg (γ z)).comp (hγd z)
  obtain ⟨g, hg, hb, hemb, hgd⟩ := exists_embedded_regular_level_disk_of_index_cut S hf hdim
    hreg hhigh hlow γM hγM hγMi hγMd (fun z => (γ z).property)
  exact ⟨g, hg, fun z => Subtype.ext (hb z), hemb, hgd⟩

theorem exists_native_middle_level_circle_isotopy
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 1, {y : M // f y = a})) :
    let _ := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
    ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = a} {y : M // f y = a} ∞,
      IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let _ : CompactSpace {y : M // f y = a} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  obtain ⟨g, hg, hgb, hge, hgd⟩ :=
    exists_native_middle_level_circle_disk S hf hdim hreg hhigh hlow γ hγ hγi hγd
  obtain ⟨h, hh, hhb, hhe, hhd⟩ :=
    exists_native_middle_level_circle_disk S hf hdim hreg hhigh hlow δ hδ hδi hδd
  let _ := S.pathConnectedSpace_middle_level hf hdim hreg hhigh hlow (g 0)
  have hgi : InjOn g (closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hge.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hhi : InjOn h (closedBall (0 : Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hhe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcodim : Module.finrank ℝ (Hemisphere.Ambient 2) + 3 =
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [Hemisphere.Ambient, RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
  have hmodel : 2 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    omega
  obtain ⟨P, hP, hformula⟩ := DiskShrinking.exists_embedded_disk_isotopy hg hh hgi hhi
    (fun x hx => hgd ⟨x, hx⟩) (fun x hx => hhd ⟨x, hx⟩) 3 (by omega) hcodim hmodel
  refine ⟨P, hP, ?_⟩
  intro z
  rw [← hgb z, hformula z.val (sphere_subset_closedBall z.property), hhb z]

end

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f g : M → ℝ}

theorem exists_equal_level_circle_isotopy
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Hemisphere.Sphere 1, {y : M // g y = a})) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
    ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // g y = a} {y : M // g y = a} ∞,
      IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := RegularLevel.chartedSpace hf hfr
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.isManifold hf hfr
  let _ := RegularLevel.isManifold hg hgr
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalLevelDiffeomorph hf hg hfr hgr heq
  let γ' : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Hemisphere.Sphere 1, {y : M // g y = a}))
      (hk : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ κ)
      (hkd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) κ z)) (z) :
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨Q, hQ, hformula⟩ := exists_native_middle_level_circle_isotopy S hf hdim
    hfr hhigh hlow γ' δ' hγ' (L.symm.injective.comp hγi) (hderiv γ hγ hγd)
      hδ' (L.symm.injective.comp hδi) (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans Q).trans L, isotopicToIdentity_conj L hQ, ?_⟩
  intro z
  change L (Q (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

end

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem exists_new_attaching_circle_placement
    (S : AdaptedSurgeryWindows E f) (T : AdaptedSurgeryWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ q : criticalPoints E f, a ≤ f q → 3 ≤ nativeMorseIndex E f q)
    (hlow : ∀ q : criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ 3)
    (p : criticalPoints E g)
    [Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 1 + 1)]
    (hap : a < g p) (hgap : ∀ q : criticalPoints E g, g q < g p → g q < a)
    (δ : C(Hemisphere.Sphere 1, {y : M // g y = a})) :
    let _ := RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) →
    ∃ Γ : C(Hemisphere.Sphere 1, {y : M // g y = a}),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧ Injective Γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
      (∀ x, x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 p.val)) ∧
      ∃ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          {y : M // g y = a} {y : M // g y = a} ∞,
        IsotopicToIdentity P ∧ (∀ z, P (Γ z) = δ z) ∧
        ∀ x, Tendsto (fun t => T.flow t x.val) atBot (𝓝 p.val) ↔ P x ∈ range δ := by
  let _ := RegularLevel.chartedSpace hg hgr
  let _ := RegularLevel.chartedSpace hg (T.data p).lower_regular
  let _ := RegularLevel.isManifold hg hgr
  let _ := RegularLevel.isManifold hg (T.data p).lower_regular
  change ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ → Injective δ →
    (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    T.exists_attaching_circle_lower_transport hg p hgr hap hgap
  have hrange (x : {y : M // g y = a}) :
      x ∈ range Γ ↔ Tendsto (fun t => T.flow t x.val) atBot (𝓝 p.val) :=
    T.transported_attaching_range_iff hg p hgr σ σ.surjective Γ hflow x
  obtain ⟨P, hP, hformula⟩ := exists_equal_level_circle_isotopy S hf hg hdim
    hfr hgr heq hhigh hlow Γ δ hΓ hΓi hΓd hδ hδi hδd
  refine ⟨Γ, hΓ, hΓi, hΓd, hrange, P, hP, hformula, ?_⟩
  intro x
  rw [← hrange]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, P.injective ((hformula z).trans hz)⟩

end

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

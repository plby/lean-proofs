import Wikipedia.HopfProblem.DegreeCollapseActualPassageEndpointClasses

/-!
# A constructed signed middle-family slide in the actual descending dynamics

Lift the original higher spheres, cross the selected native belt once,
realize that relative isotopy by a new complete flow, and return to the
original lower cut. Every other parameter map is fixed. The changed map
adds exactly one signed copy of the original native attaching map in
integral second homology. All lower backward basins are preserved.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris MorseRearrangement

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_signed_family_slide
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C(S₂, {y : M // f y = a}))
    (hα : IsNativeMiddleBasinFamily S hf ha p (fun j => α j))
    (ε : criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < ε z) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      ∃ β δ : Fin n → C(S₂, (S.data q).LowerLevel),
        IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p (fun j => β j) ∧
        IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p (fun j => δ j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
        (∀ j, j ≠ i → δ j = β j) ∧
        (∀ j, j ≠ i → ∀ x, ∃ t : ℝ, T.flow t (δ j x).val = (α j x).val) ∧
        (∃ k : ℤ, (k = 1 ∨ k = -1) ∧
          singularHomologyMap (δ i) 2 = singularHomologyMap (β i) 2 +
            k • singularHomologyMap (nativeIndexThreeAttachingSphere S q hq) 2) ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          ∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
  obtain ⟨γ, hγ, hαγ, havoid, x₀, v, τ, hτ, F, K,
      hK, hKU, hF, hF0, hFd, hFfix, hfixed, hcount, htrans⟩ :=
    S.exists_higher_family_passage hf hdim horder q hq ha haq p i hp hhigh α hα
  obtain ⟨D, hD⟩ := hFd 1
  have I : SupportedRelativeIsotopy D K (otherSheetImages (fun j => γ j) i) := {
    family := F
    smooth := hF
    zero := hF0
    one := fun x => (hD x).symm
    slices := hFd
    fixedOutside := hFfix
    fixedOn := fun t x hx => hFfix t x (fun h => hKU h hx) }
  have hDavoid (j : Fin n) :
      Disjoint (range (D ∘ γ j)) (range (S.data q).surgery.beltSphere) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ ⟨w, hw⟩
    by_cases hji : j = i
    · subst j
      have heq : F (1, γ i x) = (S.data q).surgery.beltSphere w :=
        (hD _).symm.trans hw.symm
      exact hτ.2.ne' ((hcount 1 ⟨zero_le_one, le_rfl⟩ x w).mp heq).1
    · have heq : D (γ j x) = γ j x :=
        I.endpoint_fixed_on (γ j x) (mem_otherSheetImages (fun j => γ j) i j hji x)
      exact Set.disjoint_left.mp (havoid j) (mem_range_self x) ⟨w, hw.trans heq⟩
  obtain ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hβflow, hδflow, hδold,
      hother, hprotected, hkeep⟩ :=
    S.exists_relative_family_lower_transport hf hm q hq p i hhigh γ hγ havoid ε hε D K hK I hDavoid
  let H : C(ℝ × S₂, (S.data q).UpperLevel) :=
    ⟨fun z => F (z.1, γ i z.2), hF.continuous.comp
      (continuous_fst.prodMk ((γ i).continuous.comp continuous_snd))⟩
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H :=
    hF.comp (contMDiff_fst.prodMk ((hγ.1 i).comp contMDiff_snd))
  have hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀) :=
    ((hcount τ ⟨hτ.1.le, hτ.2.le⟩ x₀ v).mpr ⟨rfl, rfl, rfl⟩).symm
  have hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S₂,
      H (t, x) ∈ range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀ := by
    intro t ht x
    constructor
    · rintro ⟨w, hw⟩
      have hh := (hcount t ht x w).mp hw.symm
      exact ⟨hh.1, hh.2.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨v, hpoint⟩
  have hstart (x : S₂) : ∃ t : ℝ, S.flow t (H (0, x)).val = (β i x).val := by
    change ∃ t : ℝ, S.flow t (F (0, γ i x)).val = (β i x).val
    rw [hF0]
    exact hβflow i x
  have hend (x : S₂) : ∃ t : ℝ, S.flow t (H (1, x)).val = (δ i x).val := by
    change ∃ t : ℝ, S.flow t (F (1, γ i x)).val = (δ i x).val
    rw [← hD]
    exact hδold i x
  obtain ⟨k, hk, hclasses⟩ := S.single_passage_actual_endpoint_classes hf q hq H hτ x₀ v
    hpoint hcross (β i) (δ i) hstart hend hH.contMDiffAt htrans
  refine ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, ?_, hother, ?_, ⟨k, hk, hclasses⟩, fun z hz => ⟨(hkeep z hz).1, (hkeep z hz).2.1⟩⟩
  · intro j x
    obtain ⟨s, hs⟩ := hαγ j x
    obtain ⟨t, ht⟩ := hβflow j x
    exact ⟨t + s, by rw [S.flow.map_add, hs, ht]⟩
  · intro j hji x
    obtain ⟨s, hs⟩ := hαγ j x
    have hm : (α j x).val ∈ range (fun t => S.flow t (γ j x).val) := by
      refine ⟨-s, ?_⟩
      change S.flow (-s) (γ j x).val = (α j x).val
      rw [← hs, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    rw [← hprotected j hji x] at hm
    obtain ⟨t, ht⟩ := hm
    change T.flow t (γ j x).val = (α j x).val at ht
    obtain ⟨u, hu⟩ := hδflow j x
    exact ⟨t - u, by rw [← hu, ← T.flow.map_add, sub_add_cancel, ht]⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

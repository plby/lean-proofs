import Wikipedia.HopfProblem.DegreeCollapseGeometricSurgeryCancellation
import Wikipedia.HopfProblem.DegreeCollapseIntrinsicMorseIndex

/-!
# Native Morse cancellation from full basin sections at any regular cut

The source sheets need not be the current surgery parametrizations. Their
full backward and forward basin images suffice. A level isotopy with one
transverse intersection supplies the exact analytic cancellation criterion.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]

theorem AdaptedSurgeryWindows.cancel_single_basin_section_isotopy
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p q : criticalPoints E f)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hp : nativeMorseIndex E f p = 2) (hq : nativeMorseIndex E f q = 3)
    {c : ℝ} (hpc : f p < c) (hcq : c < f q)
    (hc : ∀ z, f z = c → z ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf hc
    ∀ (α : Hemisphere.Sphere 2 → {z : M // f z = c})
      (β : Y → {z : M // f z = c}),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
      ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β →
      (∀ z, z ∈ range α ↔ Tendsto (fun t => S.flow t z.val) atBot (𝓝 q.val)) →
      (∀ z, z ∈ range β ↔ Tendsto (fun t => S.flow t z.val) atTop (𝓝 p.val)) →
      ∀ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          {z : M // f z = c} {z : M // f z = c} ∞,
        IsotopicToIdentity D →
        (∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
          (D ∘ α) β x y) →
        (range (D ∘ α) ∩ range β).ncard = 1 →
        ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
          (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
          (∀ z, z ∈ criticalPoints E g ↔
            z ∈ criticalPoints E f ∧ z ≠ p.val ∧ z ≠ q.val) ∧
          ∀ z, f z ∉ Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
            g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf hc
  intro α β hα hβ hback hforward D hD htrans hsingle
  let δ := D.symm ∘ β
  have hδ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ δ := D.symm.contMDiff.comp hβ
  have hDα : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ α) := D.contMDiff.comp hα
  have hαeq : D.symm ∘ (D ∘ α) = α := by
    funext x
    exact D.symm_apply_apply (α x)
  have hrange (z : {w : M // f w = c}) : z ∈ range α ↔ D z ∈ range (D ∘ α) := by
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_range_self x
    · rintro ⟨x, hx⟩
      exact ⟨x, D.injective hx⟩
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hsingle
  have hzmem : z ∈ range (D ∘ α) ∩ range β := by
    rw [hz]
    exact mem_singleton z
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hzmem
  have hcross : β y = (D ∘ α) x := hy.trans hx.symm
  have hcross' : δ y = α x := by
    exact (congrArg D.symm hcross).trans (D.symm_apply_apply (α x))
  have ht : NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) α δ x y := by
    have hh := (TransverseGerms.native_transversality_partial_diffeomorph_iff
      D.symm.toPartialDiffeomorph (hDα.mdifferentiableAt (by simp))
        (hβ.mdifferentiableAt (by simp)) hcross (mem_univ _)).mp (htrans x y)
    change NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
      (D.symm ∘ (D ∘ α)) δ x y at hh
    rwa [hαeq] at hh
  have hcount : {w : {z : M // f z = c} |
      Tendsto (fun t => S.flow t w.val) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t (D w).val) atTop (𝓝 p.val)}.ncard = 1 := by
    have heq : {w : {z : M // f z = c} |
        Tendsto (fun t => S.flow t w.val) atBot (𝓝 q.val) ∧
        Tendsto (fun t => S.flow t (D w).val) atTop (𝓝 p.val)} = {D.symm z} := by
      ext w
      change (_ ∧ _) ↔ w = D.symm z
      rw [← hback w, ← hforward (D w), hrange w]
      change D w ∈ range (D ∘ α) ∩ range β ↔ w = D.symm z
      rw [hz, mem_singleton_iff]
      exact ⟨fun h => (D.symm_apply_apply w).symm.trans (congrArg D.symm h),
        fun h => (congrArg D h).trans (D.apply_symm_apply z)⟩
    rw [heq, Set.ncard_singleton]
  have hαbasin : ∀ᶠ w in 𝓝 x, Tendsto (fun t => S.flow t (α w).val) atBot (𝓝 q.val) :=
    Eventually.of_forall (fun w => (hback (α w)).mp (mem_range_self w))
  have hδbasin : ∀ᶠ w in 𝓝 y, Tendsto (fun t => S.flow t (D (δ w)).val) atTop (𝓝 p.val) := by
    apply Eventually.of_forall
    intro w
    change Tendsto (fun t => S.flow t (D (D.symm (β w))).val) atTop (𝓝 p.val)
    rw [D.apply_symm_apply]
    exact (hforward (β w)).mp (mem_range_self w)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b, hcb, hbq⟩ := exists_between hcq
  have hweightp : Fintype.card {i // (S.data p).chart.weights i = -1} = 2 := by
    have hh := (nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hh
  have hweightq : Fintype.card {i // (S.data q).chart.weights i = -1} = 3 := by
    have hh := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using hh
  exact cancel_of_transverse_level_isotopy (m := 5) (S.data p).chart (S.data q).chart
    hf hm hdim (by omega) S.field S.smooth S.zero S.descent S.flow S.integral S.distinct
    p.property q.property (S.toSurgeryWindows.lower_lt_value p)
    (S.toSurgeryWindows.value_lt_upper q)
    (surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive)
    hac hcb hpc hcq (surgery_pair_inner_band_regular S.toSurgeryWindows p q hconsecutive hpa hbq)
    hc (S.critical_model_germ p) (S.critical_model_germ q)
    D hD hcount α δ x y (hα.mdifferentiableAt (by simp)) (hδ.mdifferentiableAt (by simp))
    hcross' ht hαbasin hδbasin

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

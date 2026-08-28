import Wikipedia.SmoothSixDPoincare.CurveAffineImmersion
import Wikipedia.SmoothSixDPoincare.ChartCoordinateApproximation
import Wikipedia.SmoothSixDPoincare.ChartMapHomotopy
import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.ChartPerturbationTargetControl

/-!
# A relative native curve-immersion patch

Use the compact scalar weight `β(t) t` in the actual target-chart perturbation.
On the open unit plateau it is exactly the affine curve perturbation, while
every zero of `β` is fixed throughout the homotopy. The parameter may also
satisfy any property holding on a neighborhood of zero.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {G F H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)

/-- A small localized affine parameter repairs the derivative on the open plateau,
fixing the cutoff's zero set and retaining any prescribed small-parameter property. -/
theorem exists_curve_immersion_patch_with_property_within_target (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) {β χ : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) (hχone : ∀ t ∈ tsupport β, χ t = 1)
    (hdim : 3 ≤ Module.finrank ℝ F) (Q : (ℝ → N) → Prop)
    (hQ : ∀ᶠ a : F in 𝓝 0, Q (ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a))
    {D : Set ℝ} {O : Set N} (hsource : c.source ⊆ O) (hmaps : MapsTo f D O) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ Q g ∧
      HomotopicRelWithin f g {t | β t = 0} D O ∧
      ∀ t ∈ interior {t | β t = 1}, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro t ht
    exact hχsupport (subset_tsupport χ (by change χ t ≠ 0; rw [hχone t ht]; norm_num))
  have hw := CurveImmersion.contDiff_weight hβ
  have hwsupport : tsupport (CurveImmersion.weight β) ⊆ f ⁻¹' c.source :=
    (CurveImmersion.tsupport_weight_subset β).trans hsupport
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) ∞ k := fun t =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ := ChartMapPerturbation.exists_radius_valid c hf hw.contMDiff
    (CurveImmersion.hasCompactSupport_weight hcompact) hwsupport
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hQ
  obtain ⟨a, ha, -, hderiv⟩ := CurveImmersion.exists_small_affine_immersion hk hdim (lt_min hε hδ)
  have haε : ‖a‖ < ε := ha.trans_le (min_le_left _ _)
  have hv := hvalid a haε
  have hsmooth := ChartMapPerturbation.contMDiff_perturb c hf hw.contMDiff hwsupport hv
  let g : C(ℝ, N) :=
    ⟨ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a, hsmooth.continuous⟩
  have hcoord (t : ℝ) (ht : β t = 1) : c (g t) = CurveImmersion.perturb k a t := by
    have hts : t ∈ tsupport β := subset_tsupport β (by change β t ≠ 0; rw [ht]; norm_num)
    change c (ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a t) = _
    rw [ChartMapPerturbation.chart_perturb c f (CurveImmersion.weight β) hv (hsupport hts)]
    simp only [ChartMapPerturbation.coordinateFamily, CurveImmersion.perturb,
      WeightedPerturbation.perturb, k, ChartMapPerturbation.cutoffCoordinates,
      CurveImmersion.weight, ht, hχone t hts, one_mul, one_smul, id_eq]
  have hQg : Q g := hδkeep (show a ∈ Metric.ball 0 δ by
    simpa only [Metric.mem_ball, dist_zero_right] using ha.trans_le (min_le_right ε δ))
  refine ⟨g, hsmooth, hQg, ?_, ?_⟩
  · have hrel := ChartMapPerturbation.homotopicRelWithin_of_source_subset
      c hf hw.contMDiff hwsupport hvalid haε hsource hmaps
    exact hrel.mono (fun _ hx => CurveImmersion.weight_eq_zero hx)
      (Subset.refl D) (Subset.refl O)
  · intro t ht
    have hβt : β t = 1 := interior_subset (s := {t | β t = 1}) ht
    have hfs : f t ∈ c.source :=
      hsupport (subset_tsupport β (by change β t ≠ 0; rw [hβt]; norm_num))
    have hgs : g t ∈ c.source :=
      ChartMapPerturbation.perturb_mem_source c f (CurveImmersion.weight β) hv hfs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 t] CurveImmersion.perturb k a := by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact hcoord s (interior_subset (s := {t | β t = 1}) hs)
    change Function.Injective (fderiv ℝ (c ∘ g) t)
    rw [heq.fderiv_eq]
    exact hderiv t

/-- The original local immersion theorem follows by forgetting the controlled target. -/
theorem exists_curve_immersion_patch_with_property (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) {β χ : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) (hχone : ∀ t ∈ tsupport β, χ t = 1)
    (hdim : 3 ≤ Module.finrank ℝ F) (Q : (ℝ → N) → Prop)
    (hQ : ∀ᶠ a : F in 𝓝 0, Q (ChartMapPerturbation.perturb c f (CurveImmersion.weight β) a)) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ Q g ∧
      Nonempty (f.HomotopyRel g {t | β t = 0}) ∧
      ∀ t ∈ interior {t | β t = 1}, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hQg, hrel, hi⟩ :=
    exists_curve_immersion_patch_with_property_within_target c f hf hβ hχ hcompact
      hχsupport hχone hdim Q hQ (subset_univ _) (mapsTo_univ f univ)
  exact ⟨g, hg, hQg, hrel.homotopicRel, hi⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion

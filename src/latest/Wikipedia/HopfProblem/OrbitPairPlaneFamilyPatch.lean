import Wikipedia.HopfProblem.OrbitPairPlaneFamilyDisplacement
import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.ChartCoordinateApproximation
import Wikipedia.SmoothSixDPoincare.VariableChartPerturbation

/-!
# Relative spatial immersion repair in an actual target chart

This localized perturbation of a smooth family into a native manifold
repairs every spatial slice on the cutoff plateau, preserves the map at
every zero of the cutoff, and retains any property true for all sufficiently
small parameters. Smoothness is joint in the original time and space.

No injectivity of the slices or ambient isotopy is asserted.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.PlaneFamily

open Wikipedia.SmoothSixDPoincare
open PlaneImmersion (Plane)

variable {G F H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)

def affinePatch (f : ℝ × Plane → N) (β : ℝ × Plane → ℝ) (A : F × F) : ℝ × Plane → N :=
  ChartMapPerturbation.variablePerturb c f β (displacement β A)

theorem chart_affinePatch_on_plateau {f : ℝ × Plane → N} {β χ : ℝ × Plane → ℝ}
    {A : F × F} (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hχ : ∀ p ∈ tsupport β, χ p = 1)
    (hvalid : ∀ p, ChartMapPerturbation.Valid c f β (displacement β A p))
    {p : ℝ × Plane} (hp : β p = 1) :
    c (affinePatch c f β A p) =
      perturb (ChartMapPerturbation.cutoffCoordinates c f χ) A p := by
  have hps : p ∈ tsupport β := subset_tsupport β (by change β p ≠ 0; rw [hp]; norm_num)
  change c (ChartMapPerturbation.perturb c f β (displacement β A p) p) = _
  rw [ChartMapPerturbation.chart_perturb c f β (hvalid p) (hsupport hps)]
  simp only [ChartMapPerturbation.coordinateFamily, perturb,
    ChartMapPerturbation.cutoffCoordinates, displacement, hp, hχ p hps, one_smul]

theorem contMDiff_affinePatch {f : ℝ × Plane → N} {β : ℝ × Plane → ℝ} {A : F × F}
    (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hvalid : ∀ p, ChartMapPerturbation.Valid c f β (displacement β A p)) :
    ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ (affinePatch c f β A) := by
  have hd := (contDiff_displacement_family (F := F) hβ).comp
    (contDiff_const (c := A) |>.prodMk contDiff_id)
  intro p
  exact ChartMapPerturbation.contMDiffAt_variablePerturb c hsupport hf.contMDiffAt
    hβ.contMDiff.contMDiffAt hd.contMDiff.contMDiffAt (hvalid p)

theorem affinePatch_zero (f : ℝ × Plane → N) (β : ℝ × Plane → ℝ) :
    affinePatch c f β (0 : F × F) = f := by
  funext p
  change ChartMapPerturbation.perturb c f β (displacement β 0 p) p = f p
  rw [displacement_zero, ChartMapPerturbation.perturb_zero]

variable [FiniteDimensional ℝ F]

theorem exists_affine_family_patch_with_property (f : C(ℝ × Plane, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f) {β χ : ℝ × Plane → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport β)
    (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) (hχone : ∀ p ∈ tsupport β, χ p = 1)
    (hdim : 5 ≤ Module.finrank ℝ F) (Q : (ℝ × Plane → N) → Prop)
    (hQ : ∀ᶠ A : F × F in 𝓝 0, Q (affinePatch c f β A)) :
    ∃ g : C(ℝ × Plane, N), ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g ∧ Q g ∧
      Nonempty (f.HomotopyRel g {p | β p = 0}) ∧
      ∀ p ∈ interior {p | β p = 1},
        Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => g (p.1, x)) p.2) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro p hp
    exact hχsupport (subset_tsupport χ (by change χ p ≠ 0; rw [hχone p hp]; norm_num))
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, ℝ × Plane) 𝓘(ℝ, F) ∞ k := fun p =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ := ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff
    hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ := exists_radius_displacement_lt (F := F) hβ hcompact hε
  have hQmem : {A : F × F | Q (affinePatch c f β A)} ∈ 𝓝 0 := hQ
  obtain ⟨η, hη, hηkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨A, hA, -, hderiv⟩ := exists_small_affine_family_immersion hk hdim (lt_min hδ hη)
  have hbound : ∀ p, ‖displacement β A p‖ < ε :=
    hδbound A (lt_of_lt_of_le hA (min_le_left _ _))
  have hv : ∀ p, ChartMapPerturbation.Valid c f β (displacement β A p) :=
    fun p => hvalid _ (hbound p)
  have hsmooth := contMDiff_affinePatch c hf hβ hsupport hv
  let g : C(ℝ × Plane, N) := ⟨affinePatch c f β A, hsmooth.continuous⟩
  have hcoord (p : ℝ × Plane) (hp : β p = 1) : c (g p) = perturb k A p :=
    chart_affinePatch_on_plateau c hsupport hχone hv hp
  have hQg : Q g := hηkeep (show A ∈ Metric.ball 0 η by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (lt_of_lt_of_le hA (min_le_right δ η)))
  refine ⟨g, hsmooth, hQg, ?_, ?_⟩
  · have hd := (contDiff_displacement_family (F := F) hβ).comp
      (contDiff_const (c := A) |>.prodMk contDiff_id)
    exact ⟨ChartMapPerturbation.variableHomotopyRel c f.continuous hβ.continuous hsupport
      hd.continuous hvalid hbound (fun _ hp => Or.inl hp)⟩
  · intro p hp
    have hβp : β p = 1 := interior_subset (s := {q | β q = 1}) hp
    have hps : f p ∈ c.source :=
      hsupport (subset_tsupport β (by change β p ≠ 0; rw [hβp]; norm_num))
    have hgs : g p ∈ c.source :=
      ChartMapPerturbation.perturb_mem_source c f β (hv p) hps
    have hslice : ContMDiff 𝓘(ℝ, Plane) J ∞ (fun x => g (p.1, x)) :=
      hsmooth.comp ((contDiff_const.prodMk contDiff_id).contMDiff)
    apply (ManifoldImmersion.injective_fderiv_chart_iff c
      (hslice.mdifferentiableAt (by simp)) hgs).mp
    have heq : (fun x => c (g (p.1, x))) =ᶠ[𝓝 p.2]
        (fun x => perturb k A (p.1, x)) := by
      have hn : {x : Plane | (p.1, x) ∈ interior {q | β q = 1}} ∈ 𝓝 p.2 :=
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
          (isOpen_interior.mem_nhds hp)
      filter_upwards [hn] with x hx
      exact hcoord (p.1, x) (interior_subset (s := {q | β q = 1}) hx)
    change Function.Injective (fderiv ℝ (fun x => c (g (p.1, x))) p.2)
    rw [heq.fderiv_eq]
    exact hderiv p.1 p.2

end Wikipedia.HopfProblem.OrbitPair.PlaneFamily

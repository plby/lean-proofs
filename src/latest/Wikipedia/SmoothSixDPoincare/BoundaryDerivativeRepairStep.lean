import Wikipedia.SmoothSixDPoincare.WeightedManifoldPatch
import Wikipedia.SmoothSixDPoincare.ChartPerturbationKernel
import Wikipedia.SmoothSixDPoincare.ChartPerturbationImmersionStability
import Wikipedia.SmoothSixDPoincare.MapSmoothingPatch

/-!
# One boundary-derivative repair step

Multiplying the source cutoff by a defining function fixes its entire zero
set. On the unit plateau the weight has the same derivative as the defining
function. A good small parameter repairs the native derivative there, while
preserving the common tangent-kernel condition, old compact immersive regions,
and all future target charts.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open ManifoldSmoothing (MapSmoothingPatch)

variable {B E G H H' X N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Repair one compact part of the boundary locus with a zero-set-fixed homotopy, retaining
the common-kernel condition needed for every subsequent patch. -/
theorem exists_boundary_derivative_repair_step {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N)) (i : ι)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G)
    {K L : Set E} (hK : IsCompact K)
    (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hLsub : L ⊆ (p i).plateau) (hLrange : L ⊆ range b)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 →
      fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ (∀ j, (p j).Compatible g) ∧
      f.HomotopicRel g {y | ρ y = 0} ∧
      (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 →
        fderiv ℝ ρ y v = 0 → v = 0) ∧
      ∀ y ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  let β : E → ℝ := fun y => (p i).cutoff y * ρ y
  have hβ : ContDiff ℝ ∞ β := (p i).smooth.contDiff.mul hρ
  have hcompact : HasCompactSupport β := (p i).compact.mul_right
  have hsupport : tsupport β ⊆ f ⁻¹' (p i).chart.source :=
    tsupport_mul_subset_left.trans ((p i).inner_compatible (hcompatible i))
  have hkeep : ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f β a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf
      hβ.contMDiff hsupport (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold := ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf
    hβ.contMDiff hcompact hsupport hK hinj
  let Common (g : E → N) : Prop := ∀ y, ρ y = 0 → ∀ v,
    mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0
  have hretain : ∀ᶠ a in 𝓝 (0 : G), Common (ChartMapPerturbation.perturb (p i).chart f β a) := by
    filter_upwards [ChartMapPerturbation.eventually_valid (p i).chart hf hβ.contMDiff
      hcompact hsupport] with a ha
    exact ChartMapPerturbation.common_kernel_preserved_on_zero_set (p i).chart hf
      (p i).smooth.contDiff hρ hsupport ha hcommon
  let Q : (E → N) → Prop := fun g => (∀ j, (p j).Compatible g) ∧
    (∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g y)) ∧ Common g
  have hQ : ∀ᶠ a in 𝓝 (0 : G), Q (ChartMapPerturbation.perturb (p i).chart f β a) :=
    hkeep.and (hold.and hretain)
  have houter : (p i).plateau ⊆ interior {y | (p i).outer y = 1} := by
    apply isOpen_interior.subset_interior_iff.mpr
    intro y hy
    apply (p i).nested y
    apply subset_tsupport (p i).cutoff
    change (p i).cutoff y ≠ 0
    rw [interior_subset (s := {y | (p i).cutoff y = 1}) hy]
    exact one_ne_zero
  have hplateau : ∀ x ∈ b ⁻¹' L, b x ∈ interior {y | (p i).outer y = 1} :=
    fun _ hx => houter (hLsub hx)
  have hcommonβ : ∀ x ∈ b ⁻¹' L, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 →
      fderiv ℝ β (b x) v = 0 → v = 0 := by
    intro x hx v hfv hβv
    have heq : β =ᶠ[𝓝 (b x)] ρ := by
      filter_upwards [(p i).plateau_eventually_one (hLsub hx)] with y hy
      simp only [β, hy, one_mul]
    apply hcommon (b x) (hzero x) v hfv
    rw [← heq.fderiv_eq]
    exact hβv
  obtain ⟨g, hg, ⟨hc, hinjg, hcommong⟩, ⟨Hrel⟩, hnew⟩ :=
    exists_weighted_immersive_patch_with_property (p i).chart f hf hb hβ
      (p i).outer_smooth.contDiff hcompact hsupport (hcompatible i) hplateau hcommonβ hdim Q hQ
  refine ⟨g, hg, hc, ?_, hcommong, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := ?_ }⟩
    intro t y hy
    apply Hrel.eq_fst t
    change (p i).cutoff y * ρ y = 0
    rw [hy, mul_zero]
  · intro y hy
    rcases hy with hy | hy
    · exact hinjg y hy
    · obtain ⟨x, rfl⟩ := hLrange hy
      exact hnew x hy

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion

import Wikipedia.HopfProblem.OrbitPairPlaneFamilyPatch
import Wikipedia.SmoothSixDPoincare.ManifoldImmersionStability

/-!
# Compact stability of spatial immersion in a perturbed family

The parameter-dependent chart patch is jointly smooth. Treating the affine
parameter and original time together as parameters, native derivative
stability proves that every previously immersive compact portion of the
cylinder stays immersive for all sufficiently small affine parameters.
-/

noncomputable section

open Set Filter
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

theorem contMDiffAt_affinePatch_family {f : ℝ × Plane → N} {β : ℝ × Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : (F × F) × (ℝ × Plane))
    (hvalid : ChartMapPerturbation.Valid c f β (displacement β q.1 q.2)) :
    ContMDiffAt 𝓘(ℝ, (F × F) × (ℝ × Plane)) J ∞
      (fun r : (F × F) × (ℝ × Plane) => affinePatch c f β r.1 r.2) q := by
  have hd := (contDiff_displacement_family (F := F) hβ).contMDiff.contMDiffAt (x := q)
  exact (ChartMapPerturbation.contMDiffAt_perturb c hf hβ.contMDiff hsupport
    (displacement β q.1 q.2, q.2) hvalid).comp q
      (f := fun r : (F × F) × (ℝ × Plane) => (displacement β r.1 r.2, r.2))
      (hd.prodMk contDiffAt_snd.contMDiffAt)

theorem eventually_affinePatch_maps_compact_into_open {f : ℝ × Plane → N}
    {β : ℝ × Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set (ℝ × Plane)} (hK : IsCompact K) {U : Set N}
    (hU : IsOpen U) (hmap : MapsTo f K U) :
    ∀ᶠ A : F × F in 𝓝 0, MapsTo (affinePatch c f β A) K U := by
  apply hK.eventually_forall_of_forall_eventually
  intro p hp
  have hvalid : ChartMapPerturbation.Valid c f β (displacement β (0 : F × F) p) := by
    rw [displacement_zero]
    exact ChartMapPerturbation.valid_zero c f β hsupport
  have hc := (contMDiffAt_affinePatch_family c hf hβ hsupport (0, p) hvalid).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  rw [affinePatch_zero]
  exact hmap hp

variable [J.Boundaryless] [IsManifold J ∞ N]

theorem eventually_affinePatch_injective_spatialDerivative {f : ℝ × Plane → N}
    {β : ℝ × Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {K : Set (ℝ × Plane)} (hK : IsCompact K)
    (hinj : ∀ p ∈ K,
      Function.Injective (mfderiv 𝓘(ℝ, Plane) J (fun x => f (p.1, x)) p.2)) :
    ∀ᶠ A : F × F in 𝓝 0, ∀ p ∈ K,
      Function.Injective (mfderiv 𝓘(ℝ, Plane) J
        (fun x => affinePatch c f β A (p.1, x)) p.2) := by
  obtain ⟨ε, hε, hvalid⟩ := ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff
    hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ := exists_radius_displacement_lt (F := F) hβ hcompact hε
  let W : Set (((F × F) × ℝ) × Plane) := {q | ‖q.1.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.fst.norm continuous_const
  let k : ((F × F) × ℝ) → Plane → N := fun a x => affinePatch c f β a.1 (a.2, x)
  have hassoc : ContDiff ℝ ∞
      (fun q : ((F × F) × ℝ) × Plane => (q.1.1, (q.1.2, q.2))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  have hfamily : ContMDiffOn (𝓘(ℝ, (F × F) × ℝ).prod 𝓘(ℝ, Plane)) J ∞
      (Function.uncurry k) W := by
    intro q hq
    have hid : ContMDiffAt (𝓘(ℝ, (F × F) × ℝ).prod 𝓘(ℝ, Plane))
        𝓘(ℝ, ((F × F) × ℝ) × Plane) ∞ (fun r : ((F × F) × ℝ) × Plane => r) q :=
      (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst, contMDiffAt_snd⟩
    have ha := hassoc.contMDiff.contMDiffAt.comp q hid
    exact ((contMDiffAt_affinePatch_family c hf hβ hsupport (q.1.1, (q.1.2, q.2))
      (hvalid _ (hδbound q.1.1 hq (q.1.2, q.2)))).comp q
        ha).contMDiffWithinAt
  have hopen := ManifoldImmersion.isOpen_injective_nativeDerivative hW hfamily
  have hreassoc : Continuous
      (fun q : (F × F) × (ℝ × Plane) => ((q.1, q.2.1), q.2.2)) :=
    (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  have hgood : IsOpen {q : (F × F) × (ℝ × Plane) | ‖q.1‖ < δ ∧
      Function.Injective (mfderiv 𝓘(ℝ, Plane) J
        (fun x => affinePatch c f β q.1 (q.2.1, x)) q.2.2)} :=
    hopen.preimage hreassoc
  have hn := (MorsePerturbation.isOpen_forall_mem_compact hK hgood).mem_nhds
    (x := (0 : F × F)) (by
      intro p hp
      constructor
      · simpa only [norm_zero] using hδ
      · rw [affinePatch_zero]
        exact hinj p hp)
  filter_upwards [hn] with A hA p hp
  exact (hA p hp).2

end Wikipedia.HopfProblem.OrbitPair.PlaneFamily

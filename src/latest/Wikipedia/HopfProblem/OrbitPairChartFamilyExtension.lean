import Wikipedia.HopfProblem.OrbitPairOpenMapExtension
import Wikipedia.HopfProblem.OrbitPairCompactPlaneFamilyImmersion
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Extending a supported family modification from a full affine source chart

A native parametrization with source the entire plane pulls a sphere family
back to an ordinary plane family. A modification supported in a compact
cylinder subset extends smoothly by the original family across the chart
boundary. Spatial immersion transfers through the actual chart derivative.
The maps, topologies, and source manifold structures are not replaced.
-/

noncomputable section

open Set Filter Topology TopologicalSpace ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.ChartFamily

open Wikipedia.SmoothSixDPoincare
open PlaneImmersion (Plane)
open OpenHomotopyExtension

variable {E H M G K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K]
  [TopologicalSpace N] [ChartedSpace K N] {J : ModelWithCorners ℝ G K}
  (c : PartialDiffeomorph 𝓘(ℝ, Plane) I Plane M ∞) (hsource : c.source = univ)

def cylinderMap (q : ℝ × Plane) : ℝ × M := (q.1, c q.2)

include hsource in
theorem parametrization_smooth : ContMDiff 𝓘(ℝ, Plane) I ∞ c := by
  apply contMDiffOn_univ.mp
  simpa only [hsource] using c.contMDiffOn_toFun

include hsource in
theorem cylinderMap_smooth :
    ContMDiff 𝓘(ℝ, ℝ × Plane) (𝓘(ℝ, ℝ).prod I) ∞ (cylinderMap c) :=
  contDiff_fst.contMDiff.prodMk ((parametrization_smooth c hsource).comp contDiff_snd.contMDiff)

def region : Opens (ℝ × M) := ⟨Prod.snd ⁻¹' c.target, c.open_target.preimage continuous_snd⟩

def coordinates (q : region c) : ℝ × Plane := (q.val.1, c.invFun q.val.2)

theorem coordinates_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × Plane) ∞ (coordinates c) := by
  intro q
  have ht : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun r : region c => r.val.1) q :=
    contMDiffAt_fst.comp q (contMDiff_subtype_val q)
  have hx : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun r : region c => r.val.2) q :=
    contMDiffAt_snd.comp q (contMDiff_subtype_val q)
  have hc := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds q.property)).comp q hx
  exact ht.prodMk_space hc

include hsource in
theorem cylinderMap_mem_region (q : ℝ × Plane) : cylinderMap c q ∈ region c :=
  c.map_source (hsource.symm ▸ mem_univ q.2)

theorem coordinates_cylinderMap (q : ℝ × Plane) :
    coordinates c ⟨cylinderMap c q, cylinderMap_mem_region c hsource q⟩ = q := by
  apply Prod.ext
  · rfl
  · exact c.left_inv (hsource.symm ▸ mem_univ q.2)

theorem cylinderMap_coordinates (q : region c) : cylinderMap c (coordinates c q) = q.val := by
  apply Prod.ext
  · rfl
  · exact c.right_inv q.property

def extend (f : ℝ × M → N) (g : ℝ × Plane → N) : ℝ × M → N :=
  extendFunction (region c) f (g ∘ coordinates c)

theorem extend_on (f : ℝ × M → N) (g : ℝ × Plane → N) (q : region c) :
    extend c f g q.val = g (coordinates c q) :=
  extendFunction_of_mem (region c) f (g ∘ coordinates c) q

include hsource in
theorem extend_cylinderMap (f : ℝ × M → N) (g : ℝ × Plane → N) (q : ℝ × Plane) :
    extend c f g (cylinderMap c q) = g q := by
  rw [extend_on c f g ⟨cylinderMap c q, cylinderMap_mem_region c hsource q⟩,
    coordinates_cylinderMap c hsource]

theorem extend_eq_off_image (f : ℝ × M → N) (g : ℝ × Plane → N)
    {T : Set (ℝ × Plane)} (hfixed : ∀ q, q ∉ T → g q = f (cylinderMap c q))
    {q : ℝ × M} (hq : q ∉ cylinderMap c '' T) : extend c f g q = f q := by
  apply OpenMapExtension.eq_off (region c) f (g ∘ coordinates c) (S := cylinderMap c '' T) _ hq
  intro p hp
  have hpt : coordinates c p ∉ T := fun h =>
    hp ⟨coordinates c p, h, cylinderMap_coordinates c p⟩
  exact (hfixed _ hpt).trans (congrArg f (cylinderMap_coordinates c p))

variable [T2Space M]

include hsource in
theorem extend_smooth (f : ℝ × M → N) (g : ℝ × Plane → N)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ f)
    (hg : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g)
    {T : Set (ℝ × Plane)} (hT : IsCompact T)
    (hfixed : ∀ q, q ∉ T → g q = f (cylinderMap c q)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (extend c f g) := by
  apply OpenMapExtension.smooth (𝓘(ℝ, ℝ).prod I) J (region c) f (g ∘ coordinates c)
    hf (hg.comp (coordinates_smooth c))
    (hT.image (cylinderMap_smooth c hsource).continuous).isClosed
  · rintro _ ⟨q, _, rfl⟩
    exact cylinderMap_mem_region c hsource q
  · intro q hq
    have ht : coordinates c q ∉ T := fun h =>
      hq ⟨coordinates c q, h, cylinderMap_coordinates c q⟩
    exact (hfixed _ ht).trans (congrArg f (cylinderMap_coordinates c q))

omit [T2Space M] hsource in
theorem extend_injective_spatialDerivative_on (f : ℝ × M → N) (g : ℝ × Plane → N)
    (hg : ContMDiff 𝓘(ℝ, ℝ × Plane) J ∞ g) {q : ℝ × M} (hq : q.2 ∈ c.target)
    (hinj : Function.Injective
      (mfderiv 𝓘(ℝ, Plane) J (fun y => g (q.1, y)) (c.invFun q.2))) :
    Function.Injective (mfderiv I J (fun x => extend c f g (q.1, x)) q.2) := by
  have heq : (fun x => extend c f g (q.1, x)) =ᶠ[𝓝 q.2]
      (fun x => g (q.1, c.invFun x)) := by
    filter_upwards [c.open_target.mem_nhds hq] with x hx
    exact extend_on c f g ⟨(q.1, x), hx⟩
  rw [heq.mfderiv_eq]
  have hgs : ContMDiff 𝓘(ℝ, Plane) J ∞ (fun y => g (q.1, y)) :=
    hg.comp (contDiff_const.prodMk contDiff_id).contMDiff
  have hcs := c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hq)
  change Function.Injective (mfderiv I J ((fun y => g (q.1, y)) ∘ c.invFun) q.2)
  rw [mfderiv_comp q.2 (hgs.mdifferentiableAt (by simp)) (hcs.mdifferentiableAt (by simp))]
  exact hinj.comp (PartialChart.bijective_mfderiv c.symm (x := q.2) hq).1

end Wikipedia.HopfProblem.OrbitPair.ChartFamily

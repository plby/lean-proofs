import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.MorseOpenDomain
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Compact stability of injective native derivatives

A fixed target chart near each parameter-point pair reduces the condition
to the open set of injective continuous linear maps. Spatial differentiation
is continuous on that open coordinate domain. Compact quantification then
gives a uniform parameter neighborhood preserving a previously immersive set.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {P E G H N : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- The native injective-derivative locus is open in any open jointly smooth family domain. -/
theorem isOpen_injective_nativeDerivative {f : P → E → N} {W : Set (P × E)}
    (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W) :
    IsOpen {q : P × E | q ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqinj⟩
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f q.1 q.2)
  let U := W ∩ (Function.uncurry f) ⁻¹' c.source
  have hU : IsOpen U := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hqU : q ∈ U := ⟨hq, mem_extChartAt_source (f q.1 q.2)⟩
  have hc : ContDiffOn ℝ ∞ (fun r : P × E => c (f r.1 r.2)) U := by
    intro r hr
    have hmap : ContMDiffAt 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod 𝓘(ℝ, E)) ∞
        (fun s : P × E => (s.1, s.2)) r :=
      contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
    have hfr := (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r hmap
    exact ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r hfr)
      |>.contDiffAt.contDiffWithinAt
  have hd := MorsePerturbation.contDiffOn_spatialDerivative
    (f := fun a x => c (f a x)) hU hc
  have hgood : IsOpen (U ∩ (fun r : P × E => fderiv ℝ (c ∘ f r.1) r.2) ⁻¹'
      {L : E →L[ℝ] G | Function.Injective L}) :=
    hd.continuousOn.isOpen_inter_preimage hU ContinuousLinearMap.isOpen_injective
  have hiff (r : P × E) (hr : r ∈ U) :
      Function.Injective (fderiv ℝ (c ∘ f r.1) r.2) ↔
        Function.Injective (mfderiv 𝓘(ℝ, E) J (f r.1) r.2) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) J ∞ (f r.1) r.2 :=
      (hf.contMDiffAt (hW.mem_nhds hr.1)).comp r.2 (f := fun x : E => (r.1, x))
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact injective_fderiv_chart_iff c (hs.mdifferentiableAt (by simp)) hr.2
  have hn := hgood.mem_nhds ⟨hqU, (hiff q hqU).mpr hqinj⟩
  apply mem_of_superset hn
  intro r hr
  exact ⟨hr.1.1, (hiff r hr.1).mp hr.2⟩

/-- The injective native-derivative locus of a single smooth map is open. -/
theorem isOpen_injective_derivative_on {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) :
    IsOpen {x : E | x ∈ W ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞
      (fun q : ℝ × E => f q.2) (Prod.snd ⁻¹' W) :=
    hf.comp contMDiff_snd.contMDiffOn (fun _ hp => hp)
  have hopen := (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f)
    (hW.preimage continuous_snd) hfamily).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  exact hopen

/-- The injective native-derivative locus of a single globally smooth map is open. -/
theorem isOpen_injective_derivative {f : E → N} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) :
    IsOpen {x : E | Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} := by
  have hfamily : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) J ∞ (fun q : ℝ × E => f q.2) :=
    hf.comp contMDiff_snd
  have hopen := (isOpen_injective_nativeDerivative (f := fun (_ : ℝ) => f)
    isOpen_univ hfamily.contMDiffOn).preimage
      ((continuous_const (y := (0 : ℝ))).prodMk (continuous_id : Continuous (id : E → E)))
  change IsOpen {x : E | True ∧ Function.Injective (mfderiv 𝓘(ℝ, E) J f x)} at hopen
  simpa only [true_and] using hopen

/-- A compact set of injective native derivatives remains so throughout a parameter neighborhood. -/
theorem eventually_injective_nativeDerivative {f : P → E → N} {W : Set (P × E)}
    (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞ (Function.uncurry f) W)
    {K : Set E} (hK : IsCompact K) {a₀ : P}
    (hmem : ∀ x ∈ K, (a₀, x) ∈ W)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a₀) x)) :
    ∀ᶠ a in 𝓝 a₀, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (f a) x) := by
  have hopen := MorsePerturbation.isOpen_forall_mem_compact hK
    (isOpen_injective_nativeDerivative hW hf)
  have hn := hopen.mem_nhds (fun x hx => ⟨hmem x hx, hinj x hx⟩)
  filter_upwards [hn] with a ha x hx
  exact (ha x hx).2

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion

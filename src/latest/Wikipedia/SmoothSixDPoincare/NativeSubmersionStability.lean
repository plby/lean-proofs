import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.SmoothSixDPoincare.MorseOpenDomain
import Wikipedia.SmoothSixDPoincare.MorseCompactStability

/-!
# Compact stability of surjective native derivatives in equal dimensions

An actual source chart identifies the native derivative with an ordinary
spatial derivative up to an invertible right factor. Spatial derivatives
vary continuously in a smooth family. In equal finite dimensions the
surjective locus is open, and compact quantification gives uniform parameter
neighborhoods.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.NativeSubmersion

variable {E F H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]

/-- A source chart preserves surjectivity of the original native derivative. -/
theorem surjective_fderiv_sourceChart_iff
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → F} {z : E}
    (hz : z ∈ c.target) (hf : MDifferentiableAt I 𝓘(ℝ, F) f (c.symm z)) :
    Surjective (fderiv ℝ (f ∘ c.symm) z) ↔ Surjective (mfderiv I 𝓘(ℝ, F) f (c.symm z)) := by
  let A : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f (c.symm z)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  have hd : fderiv ℝ (f ∘ c.symm) z = A.comp B := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp z hf (c.symm.mdifferentiableAt (by simp) hz)
  have hB : Surjective B := (PartialChart.bijective_mfderiv c.symm hz).surjective
  rw [hd]
  change Surjective (A.comp B) ↔ Surjective A
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨B v, hv⟩
  · intro h
    exact h.comp hB

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [IsManifold I ∞ X]

/-- The native surjective-derivative locus is open in the joint parameter-source domain. -/
theorem isOpen_surjective_nativeDerivative {f : P → X → F} {W : Set (P × X)}
    (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ (uncurry f) W)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsOpen {q : P × X | q ∈ W ∧ Surjective (mfderiv I 𝓘(ℝ, F) (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqsurj⟩
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) q.2
  have hqc : q.2 ∈ c.source := mem_extChartAt_source q.2
  let Q : Set (P × E) := univ ×ˢ c.target
  let C : P × E → P × X := fun r => (r.1, c.symm r.2)
  have hQ : IsOpen Q := isOpen_univ.prod c.open_target
  have hC : ContMDiffOn 𝓘(ℝ, P × E) (𝓘(ℝ, P).prod I) ∞ C Q :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (c.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hr => hr.2))
  let U : Set (P × E) := Q ∩ C ⁻¹' W
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hQ hW
  have hcoord : ContDiffOn ℝ ∞ (fun r : P × E => f r.1 (c.symm r.2)) U :=
    (hf.comp (hC.mono inter_subset_left) (fun _ hr => hr.2)).contDiffOn
  have hspatial := MorsePerturbation.contDiffOn_spatialDerivative
    (f := fun a z => f a (c.symm z)) hU hcoord
  have hopen : IsOpen {A : E →L[ℝ] F | Surjective A} := by
    have heq : {A : E →L[ℝ] F | Surjective A} = {A : E →L[ℝ] F | Injective A} := by
      ext A
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).symm
    rw [heq]
    exact ContinuousLinearMap.isOpen_injective
  let V : Set (P × E) := U ∩ (fun r => fderiv ℝ (fun z => f r.1 (c.symm z)) r.2) ⁻¹'
    {A : E →L[ℝ] F | Surjective A}
  have hV : IsOpen V := hspatial.continuousOn.isOpen_inter_preimage hU hopen
  have hiff (r : P × E) (hr : r ∈ U) :
      Surjective (fderiv ℝ (fun z => f r.1 (c.symm z)) r.2) ↔
        Surjective (mfderiv I 𝓘(ℝ, F) (f r.1) (c.symm r.2)) := by
    have hfr : ContMDiffAt I 𝓘(ℝ, F) ∞ (f r.1) (c.symm r.2) :=
      (hf.contMDiffAt (hW.mem_nhds hr.2)).comp (c.symm r.2)
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact surjective_fderiv_sourceChart_iff c hr.1.2 (hfr.mdifferentiableAt (by simp))
  have hleft : c.symm (c q.2) = q.2 := c.left_inv' hqc
  have hqU : (q.1, c q.2) ∈ U := by
    refine ⟨⟨mem_univ _, c.map_source' hqc⟩, ?_⟩
    change (q.1, c.symm (c q.2)) ∈ W
    rw [hleft]
    exact hq
  have hqV : (q.1, c q.2) ∈ V := by
    refine ⟨hqU, (hiff _ hqU).mpr ?_⟩
    exact hleft.symm ▸ hqsurj
  have hforward : ContinuousAt (fun r : P × X => (r.1, c r.2)) q :=
    continuousAt_fst.prodMk
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hqc)).continuousAt.comp
        continuousAt_snd)
  have hn := hforward.preimage_mem_nhds (hV.mem_nhds hqV)
  have hnc : ∀ᶠ r : P × X in 𝓝 q, r.2 ∈ c.source :=
    continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hqc)
  apply mem_of_superset (inter_mem hn hnc)
  intro r hr
  have hleft' : c.symm (c r.2) = r.2 := c.left_inv' hr.2
  have hmem : (r.1, c.symm (c r.2)) ∈ W := hr.1.1.2
  have hsurj := (hiff (r.1, c r.2) hr.1.1).mp hr.1.2
  refine ⟨?_, hleft' ▸ hsurj⟩
  rwa [hleft'] at hmem

/-- Surjectivity on a compact source set persists throughout a parameter neighborhood. -/
theorem eventually_surjective_nativeDerivative {f : P → X → F} {W : Set (P × X)}
    (hW : IsOpen W)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) ∞ (uncurry f) W)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {K : Set X} (hK : IsCompact K) {a : P}
    (hmem : ∀ x ∈ K, (a, x) ∈ W)
    (hregular : ∀ x ∈ K, Surjective (mfderiv I 𝓘(ℝ, F) (f a) x)) :
    ∀ᶠ b in 𝓝 a, ∀ x ∈ K, Surjective (mfderiv I 𝓘(ℝ, F) (f b) x) := by
  have hopen := MorsePerturbation.isOpen_forall_mem_compact hK
    (isOpen_surjective_nativeDerivative hW hf hdim)
  have hn := hopen.mem_nhds (fun x hx => ⟨hmem x hx, hregular x hx⟩)
  filter_upwards [hn] with b hb x hx
  exact (hb x hx).2

end Wikipedia.SmoothSixDPoincare.NativeSubmersion

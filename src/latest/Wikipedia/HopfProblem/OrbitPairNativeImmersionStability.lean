import Wikipedia.SmoothSixDPoincare.ManifoldImmersionStability
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Compact immersion stability with a native manifold source

Source charts reduce to the already proved normed-source family theorem.
The actual chart differential is invertible, so the native injectivity
condition is unchanged. This allows small target-chart translations to
retain immersion of all spheres in a compact time interval.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

open Wikipedia.SmoothSixDPoincare

variable {P E G H K X N : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem injective_sourceChart_iff
    (c : PartialDiffeomorph I 𝓘(ℝ, E) X E ∞) {f : X → N} {z : E}
    (hz : z ∈ c.target) (hf : MDifferentiableAt I J f (c.symm z)) :
    Injective (mfderiv 𝓘(ℝ, E) J (f ∘ c.symm) z) ↔
      Injective (mfderiv I J f (c.symm z)) := by
  let A : E →L[ℝ] G := mfderiv I J f (c.symm z)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  let L : E →L[ℝ] G := mfderiv 𝓘(ℝ, E) J (f ∘ c.symm) z
  have hL : L = A.comp B := mfderiv_comp z hf (c.symm.mdifferentiableAt (by simp) hz)
  have hB : Bijective B := PartialChart.bijective_mfderiv c.symm hz
  change Injective L ↔ Injective A
  rw [hL]
  constructor
  · intro hi u v huv
    obtain ⟨u', rfl⟩ := hB.surjective u
    obtain ⟨v', rfl⟩ := hB.surjective v
    exact congrArg B (hi huv)
  · intro hi
    exact hi.comp hB.injective

theorem isOpen_injective_derivative {f : P → X → N} {W : Set (P × X)}
    (hW : IsOpen W) (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (uncurry f) W) :
    IsOpen {q : P × X | q ∈ W ∧ Injective (mfderiv I J (f q.1) q.2)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqinj⟩
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) q.2
  have hqc : q.2 ∈ c.source := mem_extChartAt_source q.2
  let Q : Set (P × E) := univ ×ˢ c.target
  let C : P × E → P × X := fun r => (r.1, c.symm r.2)
  have hQ : IsOpen Q := isOpen_univ.prod c.open_target
  have hC : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) (𝓘(ℝ, P).prod I) ∞ C Q :=
    contMDiff_fst.contMDiffOn.prodMk
      (c.contMDiffOn_invFun.comp contMDiff_snd.contMDiffOn (fun _ hr => hr.2))
  let U : Set (P × E) := Q ∩ C ⁻¹' W
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hQ hW
  have hcoord : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) J ∞
      (fun r : P × E => f r.1 (c.symm r.2)) U :=
    hf.comp (hC.mono inter_subset_left) (fun _ hr => hr.2)
  have hopen := ManifoldImmersion.isOpen_injective_nativeDerivative
    (f := fun p z => f p (c.symm z)) (J := J) hU hcoord
  have hiff (r : P × E) (hr : r ∈ U) :
      Injective (mfderiv 𝓘(ℝ, E) J (fun z => f r.1 (c.symm z)) r.2) ↔
        Injective (mfderiv I J (f r.1) (c.symm r.2)) := by
    have hfr : ContMDiffAt I J ∞ (f r.1) (c.symm r.2) :=
      (hf.contMDiffAt (hW.mem_nhds hr.2)).comp (c.symm r.2)
        (f := fun x : X => (r.1, x)) (contMDiffAt_const.prodMk contMDiffAt_id)
    exact injective_sourceChart_iff c hr.1.2 (hfr.mdifferentiableAt (by simp))
  have hleft : c.symm (c q.2) = q.2 := c.left_inv' hqc
  have hqU : (q.1, c q.2) ∈ U := by
    refine ⟨⟨mem_univ _, c.map_source' hqc⟩, ?_⟩
    change (q.1, c.symm (c q.2)) ∈ W
    rw [hleft]
    exact hq
  have hreg : Injective (mfderiv 𝓘(ℝ, E) J (fun z => f q.1 (c.symm z)) (c q.2)) :=
    (hiff _ hqU).mpr (hleft.symm ▸ hqinj)
  have hforward : ContinuousAt (fun r : P × X => (r.1, c r.2)) q :=
    continuousAt_fst.prodMk
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hqc)).continuousAt.comp
        continuousAt_snd)
  have hn := hforward.preimage_mem_nhds (hopen.mem_nhds ⟨hqU, hreg⟩)
  have hnc : ∀ᶠ r : P × X in 𝓝 q, r.2 ∈ c.source :=
    continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hqc)
  apply mem_of_superset (inter_mem hn hnc)
  intro r hr
  have hleft' : c.symm (c r.2) = r.2 := c.left_inv' hr.2
  have hmem : (r.1, c.symm (c r.2)) ∈ W := hr.1.1.2
  have hi := (hiff (r.1, c r.2) hr.1.1).mp hr.1.2
  refine ⟨?_, hleft' ▸ hi⟩
  rwa [hleft'] at hmem

theorem eventually_injective_derivative {f : P → X → N} {W : Set (P × X)}
    (hW : IsOpen W) (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (uncurry f) W)
    {S : Set X} (hS : IsCompact S) {p : P} (hmem : ∀ x ∈ S, (p, x) ∈ W)
    (hinj : ∀ x ∈ S, Injective (mfderiv I J (f p) x)) :
    ∀ᶠ a in 𝓝 p, ∀ x ∈ S, Injective (mfderiv I J (f a) x) := by
  have hopen := MorsePerturbation.isOpen_forall_mem_compact hS
    (isOpen_injective_derivative hW hf)
  have hn := hopen.mem_nhds (fun x hx => ⟨hmem x hx, hinj x hx⟩)
  filter_upwards [hn] with a ha x hx
  exact (ha x hx).2

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion

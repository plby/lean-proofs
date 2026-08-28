import Wikipedia.SmoothSixDPoincare.ManifoldMorse
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCutoff

/-!
# Extending a Morse region by a compact chart patch

The perturbation is an actual smooth function on the original manifold.
The Euclidean Sard argument supplies a parameter that makes a new compact
patch Morse; manifold compact stability preserves the previously treated set.
-/

noncomputable section

open Set Metric MeasureTheory MeasureTheory.Measure Topology Filter
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- A smooth bump has an open unit plateau containing a compact neighborhood of its center. -/
theorem exists_compact_plateau (p : M) :
    ∃ (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (U L : Set M),
      IsOpen U ∧ U ⊆ (chartAt E p).source ∧ EqOn φ (fun _ => 1) U ∧
      IsCompact L ∧ L ∈ 𝓝 p ∧ L ⊆ U := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let φ : SmoothBumpFunction 𝓘(ℝ, E) p := Classical.choice inferInstance
  have hN : {x : M | φ x = 1} ∩ (chartAt E p).source ∈ 𝓝 p :=
    inter_mem φ.eventuallyEq_one ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))
  obtain ⟨U, hUN, hU, hpU⟩ := mem_nhds_iff.mp hN
  obtain ⟨L, hpL, hLU, hL⟩ := local_compact_nhds (hU.mem_nhds hpU)
  exact ⟨φ, U, L, hU, fun x hx => (hUN hx).2, fun x hx => (hUN hx).1,
    hL, hpL, hLU⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- On a unit plateau, the coordinate expression agrees locally with a linear perturbation. -/
theorem perturb_inChart_eventuallyEq {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p)
    {f : M → ℝ} {G : E → ℝ} {U : Set M} {V : Set E}
    (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source) (hφ : EqOn φ (fun _ => 1) U)
    (hV : IsOpen V) (hG : EqOn G (f ∘ (chartAt E p).symm) V)
    (a : E) {x : M} (hx : x ∈ U) (hxV : chartAt E p x ∈ V) :
    ManifoldPerturbation.perturb φ f a ∘ (chartAt E p).symm =ᶠ[𝓝 (chartAt E p x)]
      MorsePerturbation.linearPerturbation G a := by
  let e := chartAt E p
  have hxt : e x ∈ e.target := e.map_source (hUs hx)
  have hi : ContinuousAt e.symm (e x) := e.symm.continuousAt hxt
  have hpre : e.symm ⁻¹' U ∈ 𝓝 (e x) := by
    apply hi.preimage_mem_nhds
    simpa only [e.left_inv (hUs hx)] using hU.mem_nhds hx
  filter_upwards [hpre, e.open_target.mem_nhds hxt, hV.mem_nhds hxV] with y hyU hyt hyV
  have hφy := hφ hyU
  have hGy := hG hyV
  change G y = f (e.symm y) at hGy
  change f (e.symm y) - MorsePerturbation.dualEquiv a
    (φ (e.symm y) • extChartAt 𝓘(ℝ, E) p (e.symm y)) =
      G y - MorsePerturbation.dualEquiv a y
  rw [hφy, one_smul, ← hGy]
  congr 2
  simpa only [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq]
    using e.right_inv hyt

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

include μ in
/-- A small genuine manifold perturbation adds one compact patch to the Morse region. -/
theorem exists_morse_extension {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p)
    {U L K : Set M} (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source)
    (hφ : EqOn φ (fun _ => 1) U) (hL : IsCompact L) (hLU : L ⊆ U)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hK : IsCompact K) (hfK : IsMorseOn E f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (ManifoldPerturbation.perturb φ f a) ∧
      IsMorseOn E (ManifoldPerturbation.perturb φ f a) (L ∪ K) := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hLc : IsCompact (e '' L) :=
    hL.image_of_continuousOn (e.continuousOn.mono (hLU.trans hUs))
  have hLt : e '' L ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs (hLU hx))
  obtain ⟨G, hG, V, hV, hLV, -, hGV⟩ :=
    exists_smooth_extension_near_closed hLc.isClosed e.open_target hLt
      (contDiffOn_chartExpression hf he)
  have hfamily := ManifoldPerturbation.contMDiff_perturb φ hf
  let A : Set E := {a | IsMorseOn E (ManifoldPerturbation.perturb φ f a) K}
  have hA : IsOpen A := isOpen_isMorseOn
    (f := ManifoldPerturbation.perturb φ f) hfamily hK
  have hA₀ : (0 : E) ∈ A := by simpa [A] using hfK
  have hd := RegularValues.dense_regularValues μ
    ((MorsePerturbation.contDiff_coordinateGradient hG).differentiable (by simp))
  obtain ⟨a, ha, haA, haε⟩ := hd.exists_mem_open (hA.inter isOpen_ball)
    ⟨0, hA₀, mem_ball_self hε⟩
  refine ⟨a, mem_ball_zero_iff.mp haε, ?_, ?_⟩
  · exact hfamily.comp (contMDiff_const.prodMk contMDiff_id)
  · refine IsMorseOn.union ?_ haA
    intro x hx
    apply isMorseAt_of_chart_eventuallyEq he (hUs (hLU hx))
      (MorsePerturbation.isMorse_of_regularValue hG ha)
    exact perturb_inChart_eventuallyEq φ hU hUs hφ hV hGV a (hLU hx)
      (hLV (mem_image_of_mem e hx))

end Wikipedia.SmoothSixDPoincare.ManifoldMorse

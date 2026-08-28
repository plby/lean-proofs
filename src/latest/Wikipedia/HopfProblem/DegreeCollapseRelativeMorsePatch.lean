import Wikipedia.SmoothSixDPoincare.ManifoldMorseExtension

/-!
# Small Morse patches supported in a prescribed open set

Actual smooth chart bumps can be chosen with their closed support in
the allowed region. Compactness makes the perturbation uniformly small
for all sufficiently small parameters. Combining this with the proved
Sard/compact-stability step gives a genuine local Morse improvement with
both a uniform value bound and exact equality off the bump support.
-/

noncomputable section

open Set Function Filter Metric MeasureTheory MeasureTheory.Measure Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare
open ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_compact_plateau_supported (O : Set M) (hO : IsOpen O) (p : M) (hp : p ∈ O) :
    ∃ (φ : SmoothBumpFunction 𝓘(ℝ, E) p) (U L : Set M),
      tsupport φ ⊆ O ∧ IsOpen U ∧ U ⊆ (chartAt E p).source ∧ EqOn φ (fun _ ↦ 1) U ∧
      IsCompact L ∧ L ∈ 𝓝 p ∧ L ⊆ U := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨φ, _, hφO⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p
    ).mem_iff.mp (hO.mem_nhds hp)
  have hN : {x : M | φ x = 1} ∩ (chartAt E p).source ∈ 𝓝 p :=
    inter_mem φ.eventuallyEq_one ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))
  obtain ⟨U, hUN, hU, hpU⟩ := mem_nhds_iff.mp hN
  obtain ⟨L, hpL, hLU, hL⟩ := local_compact_nhds (hU.mem_nhds hpU)
  exact ⟨φ, U, L, hφO, hU, fun x hx ↦ (hUN hx).2, fun x hx ↦ (hUN hx).1,
    hL, hpL, hLU⟩

theorem exists_uniform_perturbation_bound [CompactSpace M] {p : M}
    (φ : SmoothBumpFunction 𝓘(ℝ, E) p) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : E, ‖a‖ < δ →
      ∀ x : M, |ManifoldPerturbation.perturb φ f a x - f x| < ε := by
  let A : Set E := {a | ∀ x ∈ (univ : Set M),
    |ManifoldPerturbation.perturb φ f a x - f x| < ε}
  have hfamily : Continuous (fun q : E × M ↦
      |ManifoldPerturbation.perturb φ f q.1 q.2 - f q.2|) :=
    ((ManifoldPerturbation.contMDiff_perturb φ hf).continuous.sub
      (hf.continuous.comp continuous_snd)).abs
  have hA : IsOpen A := MorsePerturbation.isOpen_forall_mem_compact isCompact_univ
    (isOpen_lt hfamily continuous_const)
  have hA0 : (0 : E) ∈ A := by
    intro x _
    simpa [ManifoldPerturbation.perturb] using hε
  obtain ⟨δ, hδ, hδA⟩ := Metric.isOpen_iff.mp hA 0 hA0
  exact ⟨δ, hδ, fun a ha x ↦ hδA (mem_ball_zero_iff.mpr ha) x (mem_univ x)⟩

variable [CompactSpace M] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

include μ in
theorem exists_morse_extension_close {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p)
    {U L K : Set M} (hU : IsOpen U) (hUs : U ⊆ (chartAt E p).source)
    (hφ : EqOn φ (fun _ ↦ 1) U) (hL : IsCompact L) (hLU : L ⊆ U)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hK : IsCompact K) (hfK : IsMorseOn E f K) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorseOn E g (L ∪ K) ∧
      (∀ x : M, |g x - f x| < ε) ∧ ∀ x : M, φ x = 0 → g x = f x := by
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_perturbation_bound φ hf ε hε
  obtain ⟨a, ha, hg, hm⟩ := exists_morse_extension μ φ hU hUs hφ hL hLU hf hK hfK hδ
  exact ⟨ManifoldPerturbation.perturb φ f a, hg, hm, hbound a ha,
    fun x hx ↦ ManifoldPerturbation.perturb_eq_of_zero φ f a hx⟩

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

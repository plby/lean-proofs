import Mathlib.Dynamics.OmegaLimit
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Convergence to a critical endpoint from strict height descent

The limiting height is constant on every actual limit set. Flow invariance
and strict height decrease force that set into the stationary exceptional
locus. If height is injective there, compactness gives a single endpoint
and convergence of the original trajectory, not just a subsequence.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

theorem height_eq_of_mem_omegaLimit (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    {κ : Filter ℝ} {x : X} {l : ℝ}
    (hlim : Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l))
    {y : X} (hy : y ∈ omegaLimit κ F {x}) : f y = l := by
  have hc : MapClusterPt y κ (fun t => F t x) :=
    (mem_omegaLimit_singleton_iff_mapClusterPt κ F x y).mp hy
  have hh := hc.continuousAt_comp hf.continuousAt
  have hl : Filter.map (f ∘ (fun t => F t x)) κ ≤ 𝓝 l := hlim
  exact eq_of_nhds_neBot (hh.clusterPt.mono hl)

/-- Strict decrease outside `S` forces every actual limit point into `S`. -/
theorem omegaLimit_subset_of_strict_height (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {κ : Filter ℝ}
    (hshift : ∀ t : ℝ, Tendsto (t + ·) κ κ)
    {S : Set X} (hstrict : ∀ y ∉ S, f (F 1 y) < f y)
    {x : X} {l : ℝ} (hlim : Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) :
    omegaLimit κ F {x} ⊆ S := by
  intro y hy
  by_contra hnot
  have hy' : F 1 y ∈ omegaLimit κ F {x} :=
    (F.isInvariant_omegaLimit κ {x} hshift) 1 hy
  have h0 := height_eq_of_mem_omegaLimit F hf hlim hy
  have h1 := height_eq_of_mem_omegaLimit F hf hlim hy'
  have hs := hstrict y hnot
  rw [h0, h1] at hs
  exact lt_irrefl _ hs

variable [CompactSpace X]

/-- Injectivity of height on the exceptional set gives an actual limiting endpoint. -/
theorem exists_flow_limit_of_injective_exceptional_height (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {κ : Filter ℝ} [NeBot κ]
    (hshift : ∀ t : ℝ, Tendsto (t + ·) κ κ)
    {S : Set X} (hstrict : ∀ y ∉ S, f (F 1 y) < f y) (hinj : InjOn f S)
    {x : X} {l : ℝ} (hlim : Tendsto (fun t : ℝ => f (F t x)) κ (𝓝 l)) :
    ∃ p ∈ S, f p = l ∧ Tendsto (fun t : ℝ => F t x) κ (𝓝 p) := by
  have hsub := omegaLimit_subset_of_strict_height F hf hshift hstrict hlim
  obtain ⟨p, hp⟩ := nonempty_omegaLimit κ F {x} (singleton_nonempty x)
  have hpl := height_eq_of_mem_omegaLimit F hf hlim hp
  have hsingle : omegaLimit κ F {x} ⊆ {p} := by
    intro y hy
    exact hinj (hsub hy) (hsub hp)
      ((height_eq_of_mem_omegaLimit F hf hlim hy).trans hpl.symm)
  refine ⟨p, hsub hp, hpl, ?_⟩
  rw [tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  have hωV : omegaLimit κ F {x} ⊆ V :=
    hsingle.trans (singleton_subset_iff.mpr hpV)
  have hEv := eventually_mapsTo_of_isOpen_of_omegaLimit_subset κ F {x} hV hωV
  filter_upwards [hEv] with t ht
  exact hVU (ht (mem_singleton x))

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

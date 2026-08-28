import Wikipedia.HopfProblem.DegreeCollapseActualEndpointBasins
import Wikipedia.HopfProblem.DegreeCollapseAdjacentMorseSigns

/-!
# Matched endpoint charts with exact stable and unstable basins

An actual adjacent-index connection constructs a common transverse
signature and two genuine native cubic charts. Each chart describes
the whole relevant endpoint basin on its source, and contains the far
tail of the original connecting orbit on its regular axis.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p q : M}

open ManifoldMorse

open Classical in
theorem exists_matched_connection_basin_endpoints
    (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hf : Continuous f) {m : ℕ} (hdim : Module.finrank ℝ E = m + 1)
    (hindex : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {x : M} (hxp : x ≠ p) (hxq : x ≠ q)
    (hp : Tendsto (fun t => F t x) atTop (𝓝 p))
    (hq : Tendsto (fun t => F t x) atBot (𝓝 q))
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y)
    (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y) :
    ∃ (σ : Fin m → ℝ)
      (Φp Φq : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φp.source ∧ Φp (1 / 2, 0) = p ∧
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φq.source ∧ Φq (-(1 / 2 : ℝ), 0) = q ∧
      (∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(1 / 2 : ℝ) ^ 2) y) ∧
      (∀ z ∈ Φp.source, Tendsto (fun t => F t (Φp z)) atTop (𝓝 p) ↔
        ∀ i, σ i = -1 → z.2 i = 0) ∧
      (∀ z ∈ Φq.source, Tendsto (fun t => F t (Φq z)) atBot (𝓝 q) ↔
        ∀ i, σ i = 1 → z.2 i = 0) ∧
      (∀ᶠ t in atTop, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (s, (0 : Fin m → ℝ)) ∈ Φp.source ∧ Φp (s, 0) = F t x) ∧
      ∀ᶠ t in atBot, ∃ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (s, (0 : Fin m → ℝ)) ∈ Φq.source ∧ Φq (s, 0) = F t x := by
  obtain ⟨ρp, ρq, hρp, hρq, hmatch⟩ :=
    SignedCoordinates.exists_adjacent_sign_enumerations_of_dimension hdim
      cp.weights cq.weights cp.signs cq.signs hindex
  let σ := fun i : Fin m => cp.weights (ρp (some i))
  obtain ⟨Φp, hpc, hpv, _, hpfield, hpbasin, hptail⟩ :=
    exists_actual_incoming_cubic_basin cp hf ρp hρp hV F hF hmono hxp hp heqp
  obtain ⟨Φq, hqc, hqv, _, hqfield, hqbasin, hqtail⟩ :=
    exists_actual_outgoing_cubic_basin cq hf ρq hρq hV F hF hmono hxq hq heqq
  have hsigma : (fun i : Fin m => cq.weights (ρq (some i))) = σ :=
    funext (fun i => (hmatch i).symm)
  rw [hsigma] at hqfield hqbasin
  exact ⟨σ, Φp, Φq, fun i => cp.signs _, hpc, hpv, hqc, hqv,
    hpfield, hqfield, hpbasin, hqbasin, hptail, hqtail⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

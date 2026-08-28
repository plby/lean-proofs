import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart
import Wikipedia.HopfProblem.DegreeCollapseMorseCoordinateSplit
import Wikipedia.SmoothSixDPoincare.MorseDescentField

/-!
# Cubic field endpoints in every actual signed Morse chart

The genuine Morse descent field has rates plus one on the negative block
and minus one on the positive block. A selected signed coordinate becomes
the longitudinal cubic coordinate at parameter `a = 1/2`. All remaining
signs are the original transverse signs. The native field itself is retained.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- Separating any selected coordinate respects the exact signed linear field. -/
theorem splitEquiv_endpoint_field {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) (p : Model m) :
    splitEquiv ρ (endpointLinearField (fun i => w (ρ (some i))) (1 / 2) (w (ρ none)) p) =
      fun j => -w j * splitEquiv ρ p j := by
  funext j
  obtain ⟨k, rfl⟩ := ρ.surjective j
  cases k with
  | none =>
    rw [splitEquiv_apply_none, splitEquiv_apply_none]
    change (-2 * w (ρ none) * (1 / 2)) * p.1 = -w (ρ none) * p.1
    ring
  | some i =>
    rw [splitEquiv_apply_some, splitEquiv_apply_some]
    rfl

open Classical in
/-- The original Euclidean signed splitting intertwines the two descriptions of descent. -/
theorem splitCoordinates_signed_descent {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    MorseHandle.splitCoordinates w (fun i => -w i * z i) =
      MorseHandle.descent (MorseHandle.splitCoordinates w z) := by
  apply Prod.ext
  · ext i
    change -w i.1 * z i.1 = z i.1
    rw [i.2]
    ring
  · ext i
    change -w i.1 * z i.1 = -z i.1
    rw [(hw i.1).resolve_left i.2]
    ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

open ManifoldMorse

open Classical in
/-- A constructed continuous linear map puts the selected Morse coordinate first. -/
def selectedMorseFieldEquiv (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates) :=
  (splitEquiv ρ).trans (MorseHandle.splitCoordinates c.weights)

open Classical in
theorem selectedMorseFieldEquiv_descent (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (p : Model m) :
    selectedMorseFieldEquiv c ρ
        (endpointLinearField (fun i => c.weights (ρ (some i))) (1 / 2) (c.weights (ρ none)) p) =
      MorseHandle.descent (selectedMorseFieldEquiv c ρ p) := by
  change MorseHandle.splitCoordinates c.weights (splitEquiv ρ _) =
    MorseHandle.descent (MorseHandle.splitCoordinates c.weights (splitEquiv ρ p))
  rw [splitEquiv_endpoint_field]
  exact splitCoordinates_signed_descent c.weights c.signs (splitEquiv ρ p)

open Classical in
/-- The exact native cubic field endpoint chart is constructed from the
original signed Morse chart and one selected coordinate, without any
cubic normal-form hypothesis or critical-value compatibility assumption. -/
theorem exists_cubic_field_endpoint_of_morseChart (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    let e := c.weights (ρ none)
    let σ := fun i : Fin m => c.weights (ρ (some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) = x ∧
      Φ.target ⊆ c.splitChart.source ∧
      ∀ y ∈ Φ.target, c.descentField y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y := by
  let e := c.weights (ρ none)
  let σ := fun i : Fin m => c.weights (ρ (some i))
  let L := selectedMorseFieldEquiv c ρ
  let P := L.toDiffeomorph.toPartialDiffeomorph
  let Q := P.trans c.splitChart.symm
  have he : e ^ 2 = 1 := by
    rcases c.signs (ρ none) with h | h <;> change c.weights (ρ none) ^ 2 = 1 <;>
      rw [h] <;> norm_num
  have h0 : (0 : Model m) ∈ Q.source := by
    change (0 : Model m) ∈ univ ∧ L 0 ∈ c.splitChart.target
    rw [map_zero, ← c.splitChart_center]
    exact ⟨mem_univ _, c.splitChart.map_source' c.splitChart_mem_source⟩
  have hQzero : Q 0 = x := by
    change c.splitChart.symm (L 0) = x
    rw [map_zero, ← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hmodel : ∀ y ∈ Q.target, c.descentField y =
      FlowConstruction.partialChartField Q.symm (endpointLinearField σ (1 / 2) e) y := by
    intro y hy
    have hpush (p : Model m) (_ : p ∈ P.source) :
        fderiv ℝ P p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (P p) := by
      change fderiv ℝ L p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)
      rw [L.fderiv]
      exact selectedMorseFieldEquiv_descent c ρ p
    exact (partialChartField_of_model_conjugacy P c.splitChart.symm
      (endpointLinearField σ (1 / 2) e) MorseHandle.descent hpush hy).symm
  obtain ⟨Φ, hp, hc, hsub, hf, _⟩ :=
    exists_native_cubic_field_endpoint σ (by norm_num : 0 < (1 / 2 : ℝ)) he Q h0
      c.descentField hmodel
  refine ⟨Φ, ?_, ?_, fun y hy => (hsub hy).1, hf⟩
  · simpa only [mul_one_div] using hp
  · simpa only [mul_one_div, hQzero] using hc

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

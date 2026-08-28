import Wikipedia.HopfProblem.DegreeCollapseScaledCubicMorseChart
import Wikipedia.HopfProblem.DegreeCollapseIntrinsicMorseIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The exact intrinsic indices of the native cubic birth

The explicit endpoint signed charts have the chosen transverse signs and
one scalar sign, positive at the lower endpoint and negative at the upper.
Counting the enumerated negative coordinates gives adjacent intrinsic Morse
indices. In particular two transverse negative signs give indices two/three.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Classical in
theorem negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ) :
    Fintype.card {j // w j = -1} =
      (if w (ρ none) = -1 then 1 else 0) + Fintype.card {i // w (ρ (some i)) = -1} := by
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← ρ.sum_comp, Fintype.sum_option]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}

open Classical in
theorem native_index_of_scaled_cubic_germ
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a δ b : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (e * a, 0)) =
      (if e = -1 then 1 else 0) + Fintype.card {i // σ i = -1} := by
  let ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨c, hce, hcσ⟩ := exists_signed_chart_of_scaled_cubic_germ Φ ρ σ hσ ha hδ e he hp hgerm
  rw [nativeMorseIndex_eq_chart c]
  simp only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace, finrank_euclideanSpace]
  rw [negative_card_split ρ c.weights, hce]
  simp only [hcσ]

open Classical in
theorem native_indices_of_cubic_birth_germs
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a δ b : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source) (hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgp : f ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z)
    (hgq : f ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (a, 0)) = Fintype.card {i // σ i = -1} ∧
      nativeMorseIndex E f (Φ (-a, 0)) = Fintype.card {i // σ i = -1} + 1 := by
  constructor
  · have h := native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ 1 (Or.inr rfl)
      (by simpa only [one_mul] using hp) (by simpa only [one_mul] using hgp)
    simpa only [one_mul, if_neg (by norm_num : (1 : ℝ) ≠ -1), zero_add] using h
  · have h := native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ (-1) (Or.inl rfl)
      (by simpa only [neg_one_mul] using hq) (by simpa only [neg_one_mul] using hgq)
    simpa [Nat.add_comm] using h

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

import Wikipedia.HopfProblem.DegreeCollapseControlledMorseEndpointCharts

/-!
# Stable planes determined by the endpoint field conjugacy

An arbitrary invertible linear conjugacy with the signed Morse field
identifies its stable and unstable planes. No chosen orthogonal alignment
or coordinate formula for that conjugacy is required.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

open ManifoldMorse

open Classical in
/-- The incoming endpoint's stable plane is exactly the vanishing of the
negative transverse coordinates, for any actual linear field conjugacy. -/
theorem incoming_linear_stable_plane (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) 1 p) = MorseHandle.descent (L p))
    (p : Model m) : (L p).1 = 0 ↔ ∀ i, σ i = -1 → p.2 i = 0 := by
  have heig : (L p).1 = 0 ↔ endpointLinearField σ (1 / 2) 1 p = -p := by
    constructor
    · intro hz
      apply L.injective
      rw [hL, map_neg]
      apply Prod.ext
      · change (L p).1 = -(L p).1
        rw [hz, neg_zero]
      · rfl
    · intro h
      have hh := congrArg Prod.fst (hL p)
      rw [h, map_neg] at hh
      have hs : (2 : ℝ) • (L p).1 = 0 := by
        rw [two_smul]
        exact (congrArg (fun z => z + (L p).1) hh.symm).trans (neg_add_cancel _)
      exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  rw [heig]
  constructor
  · intro h i hi
    have hh := congrArg (fun q : Model m => q.2 i) h
    change -σ i * p.2 i = -p.2 i at hh
    rw [hi] at hh
    linarith
  · intro h
    apply Prod.ext
    · simp [endpointLinearField]
    · funext i
      rcases hσ i with hi | hi
      · simp [endpointLinearField, hi, h i hi]
      · simp [endpointLinearField, hi]

open Classical in
/-- The outgoing endpoint's unstable plane is exactly the vanishing of
the positive transverse coordinates. -/
theorem outgoing_linear_unstable_plane (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) (-1) p) = MorseHandle.descent (L p))
    (p : Model m) : (L p).2 = 0 ↔ ∀ i, σ i = 1 → p.2 i = 0 := by
  have heig : (L p).2 = 0 ↔ endpointLinearField σ (1 / 2) (-1) p = p := by
    constructor
    · intro hz
      apply L.injective
      rw [hL]
      apply Prod.ext
      · rfl
      · change -(L p).2 = (L p).2
        rw [hz, neg_zero]
    · intro h
      have hh := congrArg Prod.snd (hL p)
      rw [h] at hh
      have hs : (2 : ℝ) • (L p).2 = 0 := by
        rw [two_smul]
        exact (congrArg (fun z => z + (L p).2) hh).trans (neg_add_cancel _)
      exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  rw [heig]
  constructor
  · intro h i hi
    have hh := congrArg (fun q : Model m => q.2 i) h
    simp only [endpointLinearField, hi] at hh
    linarith
  · intro h
    apply Prod.ext
    · simp [endpointLinearField]
    · funext i
      rcases hσ i with hi | hi
      · simp [endpointLinearField, hi]
      · simp [endpointLinearField, hi, h i hi]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

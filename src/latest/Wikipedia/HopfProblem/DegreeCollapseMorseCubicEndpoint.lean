import Wikipedia.HopfProblem.DegreeCollapseMorseCoordinateSplit

/-!
# Cubic endpoint germs constructed from the actual native Morse normal forms

Every selected signed coordinate of a native Morse chart gives a constructed
cubic endpoint chart. The physical center, all transverse signs, and the
critical value are retained explicitly. No new local normal-form premise is
introduced: the input is the already proved signed Morse chart of the function.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- Enumerate the remaining coordinates while putting any selected coordinate first. -/
theorem exists_coordinate_enum {m n : ℕ} (hn : n = m + 1) (j : Fin n) :
    ∃ ρ : Option (Fin m) ≃ Fin n, ρ none = j := by
  let ρ₀ : Option (Fin m) ≃ Fin n := Fintype.equivOfCardEq (by simp [hn])
  exact ⟨ρ₀.trans (Equiv.swap (ρ₀ none) j), by simp⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

open Wikipedia.SmoothSixDPoincare.ManifoldMorse

/-- Separate the selected signed square and convert it to an actual cubic endpoint chart. -/
theorem exists_cubic_endpoint_of_morseChart (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E))
    {a : ℝ} (ha : 0 < a) :
    let e := c.weights (ρ none)
    let σ := fun i : Fin m => c.weights (ρ (some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e * a, 0) = x ∧
      Φ.target ⊆ c.chart.source ∧
      (∀ p ∈ Φ.source, f (Φ p) =
        f x - cubic σ (-(a ^ 2)) (e * a, 0) + cubic σ (-(a ^ 2)) p) := by
  let e := c.weights (ρ none)
  let σ := fun i : Fin m => c.weights (ρ (some i))
  let b := f x - cubic σ (-(a ^ 2)) (e * a, 0)
  let Q := splitNativeChart c ρ
  have he : e ^ 2 = 1 := by
    rcases c.signs (ρ none) with h | h <;> change c.weights (ρ none) ^ 2 = 1 <;>
      rw [h] <;> norm_num
  have hquad : ∀ p ∈ Q.source, f (Q p) = b + cubic σ (-(a ^ 2)) (e * a, 0) +
      e * p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 := by
    intro p hp
    have hh := splitNativeChart_equation c ρ hp
    change f (Q p) = f x + e * p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 at hh
    rw [hh]
    dsimp only [b]
    ring
  obtain ⟨Φ, hp, hcenter, htarget, hformula⟩ :=
    exists_native_cubic_endpoint σ ha e he Q (splitNativeChart_zero_mem c ρ) b hquad
  exact ⟨Φ, hp, hcenter.trans (splitNativeChart_center c ρ),
    fun _ hy => (htarget hy).1, hformula⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

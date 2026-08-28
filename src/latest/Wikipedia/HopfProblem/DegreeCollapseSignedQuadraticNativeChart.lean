import Wikipedia.HopfProblem.DegreeCollapseMorseCoordinateSplit

/-!
# A split signed quadratic formula gives an actual native Morse chart

Enumerating the scalar and transverse coordinates constructs a signed chart
in the original atlas. Both full chart identities are proved, and the sign
of every enumerated coordinate is retained explicitly.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} {m : ℕ}

theorem exists_signed_chart_of_split_quadratic
    (P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Model m) M (Model m) ∞)
    (hp : p ∈ P.source) (hcenter : P p = 0)
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E))
    (e : ℝ) (σ : Fin m → ℝ) (he : e = -1 ∨ e = 1)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hformula : ∀ y ∈ P.source,
      f y = f p + e * (P y).1 ^ 2 + ∑ i, σ i * (P y).2 i ^ 2) :
    ∃ c : SignedMorseChart (E := E) f p,
      c.weights (ρ none) = e ∧ ∀ i, c.weights (ρ (some i)) = σ i := by
  let w : Fin (Module.finrank ℝ E) → ℝ := fun j => (ρ.symm j).elim e σ
  have hwn : w (ρ none) = e := by simp [w]
  have hws (i : Fin m) : w (ρ (some i)) = σ i := by simp [w]
  have hw (j : Fin (Module.finrank ℝ E)) : w j = -1 ∨ w j = 1 := by
    change (ρ.symm j).elim e σ = -1 ∨ (ρ.symm j).elim e σ = 1
    cases h : ρ.symm j with
    | none => exact he
    | some i => exact hσ i
  have hsum (z : Model m) : (∑ j, w j * splitEquiv ρ z j ^ 2) =
      e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2 := by
    rw [split_signed_sum, hwn]
    simp only [hws]
  let C := P.trans (splitEquiv ρ).toDiffeomorph.toPartialDiffeomorph
  have hpC : p ∈ C.source := ⟨hp, mem_univ _⟩
  have hC0 : C p = 0 := by
    change splitEquiv ρ (P p) = 0
    rw [hcenter, map_zero]
  have hCformula (y : M) (hy : y ∈ C.source) :
      f y = f p + ∑ i, w i * (C y i) ^ 2 := by
    change f y = f p + ∑ i, w i * splitEquiv ρ (P y) i ^ 2
    rw [hsum, hformula y hy.1]
    ring
  let c : SignedMorseChart (E := E) f p := {
    weights := w
    signs := hw
    chart := C
    mem_source := hpC
    center := hC0
    equation := hCformula
    inverse_equation := by
      intro z hz
      have h := hCformula (C.symm z) (C.map_target' hz)
      have hr : C (C.symm z) = z := C.right_inv' hz
      rw [hr] at h
      exact h }
  exact ⟨c, hwn, hws⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

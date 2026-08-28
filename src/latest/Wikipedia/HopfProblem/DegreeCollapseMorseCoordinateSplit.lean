import Wikipedia.SmoothSixDPoincare.ManifoldMorseNormalForm
import Wikipedia.HopfProblem.DegreeCollapseNativeCubicEndpoint
import Mathlib.LinearAlgebra.Pi

/-!
# Separating a scalar direction in an actual signed Morse chart

An explicit finite-coordinate linear equivalence separates one selected
square from all remaining squares. Composing it with the native inverse
Morse chart gives the exact scalar-plus-transverse formula, with the same
physical critical point and the original manifold atlas.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

def splitLinear {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun p j := (ρ.symm j).elim p.1 p.2
  invFun f := (f (ρ none), fun i => f (ρ (some i)))
  left_inv p := by
    apply Prod.ext
    · simp
    · funext i
      simp
  right_inv f := by
    funext j
    have hj := ρ.apply_symm_apply j
    cases h : ρ.symm j with
    | none => simpa only [h, Option.elim_none] using congrArg f hj
    | some i => simpa only [h, Option.elim_some] using congrArg f hj
  map_add' p q := by
    funext j
    cases h : ρ.symm j <;> simp [h]
  map_smul' t p := by
    funext j
    cases h : ρ.symm j <;> simp [h]

def splitEquiv {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃L[ℝ] (Fin n → ℝ) :=
  (splitLinear ρ).toContinuousLinearEquiv

theorem splitEquiv_apply_none {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m) :
    splitEquiv ρ p (ρ none) = p.1 := by
  change (ρ.symm (ρ none)).elim p.1 p.2 = p.1
  simp

theorem splitEquiv_apply_some {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m)
    (i : Fin m) : splitEquiv ρ p (ρ (some i)) = p.2 i := by
  change (ρ.symm (ρ (some i))).elim p.1 p.2 = p.2 i
  simp

theorem split_signed_sum {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) (p : Model m) :
    (∑ j, w j * splitEquiv ρ p j ^ 2) =
      w (ρ none) * p.1 ^ 2 + ∑ i, w (ρ (some i)) * p.2 i ^ 2 := by
  rw [← ρ.sum_comp]
  simp only [Fintype.sum_option, splitEquiv_apply_none, splitEquiv_apply_some]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

open Wikipedia.SmoothSixDPoincare.ManifoldMorse

/-- The chosen scalar square is separated by a proved linear coordinate change. -/
def splitNativeChart (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞ :=
  (splitEquiv ρ).toDiffeomorph.toPartialDiffeomorph.trans c.chart.symm

theorem splitNativeChart_zero_mem (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    (0 : Model m) ∈ (splitNativeChart c ρ).source := by
  change (0 : Model m) ∈ univ ∧ splitEquiv ρ 0 ∈ c.chart.target
  rw [map_zero, ← c.center]
  exact ⟨mem_univ _, c.chart.map_source' c.mem_source⟩

theorem splitNativeChart_center (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    splitNativeChart c ρ 0 = x := by
  change c.chart.symm (splitEquiv ρ 0) = x
  rw [map_zero, ← c.center]
  exact c.chart.left_inv' c.mem_source

theorem splitNativeChart_equation (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E))
    {p : Model m} (hp : p ∈ (splitNativeChart c ρ).source) :
    f (splitNativeChart c ρ p) = f x + c.weights (ρ none) * p.1 ^ 2 +
      ∑ i, c.weights (ρ (some i)) * p.2 i ^ 2 := by
  change f (c.chart.symm (splitEquiv ρ p)) = _
  rw [c.inverse_equation (splitEquiv ρ p) hp.2, split_signed_sum]
  ring

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

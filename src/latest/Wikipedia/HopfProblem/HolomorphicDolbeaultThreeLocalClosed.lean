import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalCoordinates

/-!
# The actual coordinate closedness equations

Closedness means equality of the mixed antiholomorphic derivatives of
the coefficients.  It is not defined by the existence of primitives.
-/

noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- The genuine all-pairs antiholomorphic closedness equations. -/
def IsClosedOn (f : Fin 3 → Coordinates → ℂ) (U : Set Coordinates) : Prop :=
  ∀ q ∈ U, ∀ i j, coordinateDbar i (f j) q = coordinateDbar j (f i) q

@[simp] theorem coordinateDbar_const (i : Fin 3) (c : ℂ) (q : Coordinates) :
    coordinateDbar i (fun _ => c) q = 0 := by
  simp only [coordinateDbar, dbar_const, zero_apply]

theorem coordinateDbar_add (i : Fin 3) {f g : Coordinates → ℂ} {q : Coordinates}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    coordinateDbar i (fun x => f x + g x) q =
      coordinateDbar i f q + coordinateDbar i g q := by
  change dbar (f + g) q (basisVector i) = _
  rw [dbar_add hf hg]
  rfl

theorem coordinateDbar_sub (i : Fin 3) {f g : Coordinates → ℂ} {q : Coordinates}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    coordinateDbar i (fun x => f x - g x) q =
      coordinateDbar i f q - coordinateDbar i g q := by
  change dbar (f - g) q (basisVector i) = _
  rw [dbar_sub hf hg]
  rfl

theorem coordinateDbar_mul (i : Fin 3) {f g : Coordinates → ℂ} {q : Coordinates}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    coordinateDbar i (fun x => f x * g x) q =
      f q * coordinateDbar i g q + g q * coordinateDbar i f q := by
  change dbar (fun x => f x * g x) q (basisVector i) = _
  rw [dbar_mul hf hg]
  rfl

theorem coordinateDbar_eventuallyEq (i : Fin 3) {f g : Coordinates → ℂ}
    {q : Coordinates} (h : f =ᶠ[𝓝 q] g) :
    coordinateDbar i f =ᶠ[𝓝 q] coordinateDbar i g :=
  h.eventuallyEq_nhds.mono fun _ he => coordinateDbar_congr i he

/-- A coefficient which vanishes on an open neighborhood has zero actual
antiholomorphic derivative there. -/
theorem coordinateDbar_zero_of_eqOn (i : Fin 3) {f : Coordinates → ℂ}
    {U : Set Coordinates} (hU : IsOpen U) (hf : ∀ q ∈ U, f q = 0)
    {q : Coordinates} (hq : q ∈ U) : coordinateDbar i f q = 0 := by
  have he : f =ᶠ[𝓝 q] fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hq] with x hx
    exact hf x hx
  rw [coordinateDbar_congr i he, coordinateDbar_const]

/-- Subtracting an actual differential from the coefficient family. -/
def subtractDbar (f : Fin 3 → Coordinates → ℂ) (u : Coordinates → ℂ)
    (i : Fin 3) (q : Coordinates) : ℂ := f i q - coordinateDbar i u q

theorem contDiff_subtractDbar {f : Fin 3 → Coordinates → ℂ} {u : Coordinates → ℂ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (subtractDbar f u i) :=
  (hf i).sub (contDiff_coordinateDbar i hu)

/-- The residual remains genuinely closed on exactly the original domain,
by the actual symmetry of second real Fréchet derivatives. -/
theorem isClosedOn_subtractDbar {f : Fin 3 → Coordinates → ℂ}
    {u : Coordinates → ℂ} {U : Set Coordinates}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hu : ContDiff ℝ ∞ u)
    (hclosed : IsClosedOn f U) : IsClosedOn (subtractDbar f u) U := by
  intro q hq i j
  change coordinateDbar i (fun x => f j x - coordinateDbar j u x) q =
    coordinateDbar j (fun x => f i x - coordinateDbar i u x) q
  rw [coordinateDbar_sub i ((hf j).differentiable (by simp) q)
      ((contDiff_coordinateDbar j hu).differentiable (by simp) q),
    coordinateDbar_sub j ((hf i).differentiable (by simp) q)
      ((contDiff_coordinateDbar i hu).differentiable (by simp) q),
    hclosed q hq i j, coordinateDbar_coordinateDbar hu i j q]

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

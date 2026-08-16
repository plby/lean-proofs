import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-- The removable completion of `z * ζ(1 + z)` at `z = 0`. -/
noncomputable def zetaResidueFactor (z : ℂ) : ℂ :=
  riemannZeta₁ (1 + z)

@[simp]
theorem zetaResidueFactor_zero :
    zetaResidueFactor 0 = 1 := by
  simp [zetaResidueFactor]

/-- Away from zero, the completed factor is the usual residue-normalized
zeta function. -/
theorem zetaResidueFactor_eq_mul_riemannZeta
    {z : ℂ} (hz : z ≠ 0) :
    zetaResidueFactor z = z * riemannZeta (1 + z) := by
  have hs : (1 : ℂ) + z ≠ 1 := by
    intro h
    apply hz
    exact add_left_cancel (by simpa only [add_zero] using h)
  rw [riemannZeta_eq_inv_sub_mul hs]
  simp [zetaResidueFactor, hz]

theorem differentiable_zetaResidueFactor :
    Differentiable ℂ zetaResidueFactor := by
  unfold zetaResidueFactor
  fun_prop

theorem continuous_zetaResidueFactor :
    Continuous zetaResidueFactor :=
  differentiable_zetaResidueFactor.continuous

theorem tendsto_zetaResidueFactor_zero :
    Tendsto zetaResidueFactor (𝓝 0) (𝓝 1) := by
  have h :=
    continuous_zetaResidueFactor.continuousAt
      (x := (0 : ℂ))
  simpa only [zetaResidueFactor_zero] using h.tendsto

/-- Epsilon--delta form of the residue asymptotic, uniform over every
complex direction. -/
theorem exists_norm_zetaResidueFactor_sub_one_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, ‖z‖ < δ →
        ‖zetaResidueFactor z - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      continuous_zetaResidueFactor.continuousAt ε hε
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hdist :
      dist z 0 < δ := by
    simpa [dist_eq_norm] using hz
  have := hclose hdist
  simpa [dist_eq_norm] using this

/-- The completed residue factor is nonzero throughout some explicit
neighborhood furnished by continuity. -/
theorem exists_zetaResidueFactor_ne_zero_ball :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, ‖z‖ < δ →
        zetaResidueFactor z ≠ 0 := by
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_norm_zetaResidueFactor_sub_one_lt
      (ε := 1) (by norm_num)
  refine ⟨δ, hδ, fun z hz hzero => ?_⟩
  have h := hclose z hz
  rw [hzero] at h
  norm_num at h

/-- Consequently `ζ(1+z)` itself has no zero in a sufficiently small
punctured ball. -/
theorem exists_riemannZeta_one_add_ne_zero_ball :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ≠ 0 → ‖z‖ < δ →
        riemannZeta (1 + z) ≠ 0 := by
  obtain ⟨δ, hδ, hfactor⟩ :=
    exists_zetaResidueFactor_ne_zero_ball
  refine ⟨δ, hδ, fun z hz hnorm hzero => ?_⟩
  apply hfactor z hnorm
  rw [zetaResidueFactor_eq_mul_riemannZeta hz,
    hzero, mul_zero]

/-- The completed two-variable zeta quotient which tends to one when both
parameters tend to zero. -/
noncomputable def normalizedZetaPairFactor
    (u v : ℂ) : ℂ :=
  zetaResidueFactor (u + v) /
    (zetaResidueFactor u * zetaResidueFactor v)

@[simp]
theorem normalizedZetaPairFactor_zero_zero :
    normalizedZetaPairFactor 0 0 = 1 := by
  simp [normalizedZetaPairFactor]

theorem continuousAt_normalizedZetaPairFactor_zero :
    ContinuousAt
      (fun z : ℂ × ℂ =>
        normalizedZetaPairFactor z.1 z.2)
      (0, 0) := by
  have hnum :
      ContinuousAt
        (fun z : ℂ × ℂ =>
          zetaResidueFactor (z.1 + z.2))
        (0, 0) := by
    exact continuous_zetaResidueFactor.continuousAt.comp
      (by fun_prop)
  have hden :
      ContinuousAt
        (fun z : ℂ × ℂ =>
          zetaResidueFactor z.1 *
            zetaResidueFactor z.2)
        (0, 0) := by
    exact
      (continuous_zetaResidueFactor.continuousAt.comp
          (by fun_prop)).mul
        (continuous_zetaResidueFactor.continuousAt.comp
          (by fun_prop))
  exact hnum.div hden (by simp)

theorem tendsto_normalizedZetaPairFactor_zero :
    Tendsto
      (fun z : ℂ × ℂ =>
        normalizedZetaPairFactor z.1 z.2)
      (𝓝 (0, 0)) (𝓝 1) := by
  simpa only [normalizedZetaPairFactor_zero_zero] using
    continuousAt_normalizedZetaPairFactor_zero.tendsto

/-- Uniform two-variable zeta comparison on a small complex polydisc. -/
theorem exists_norm_normalizedZetaPairFactor_sub_one_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℂ,
        ‖u‖ < δ →
        ‖v‖ < δ →
        ‖normalizedZetaPairFactor u v - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      continuousAt_normalizedZetaPairFactor_zero ε hε
  refine ⟨δ, hδ, fun u v hu hv => ?_⟩
  have hdist :
      dist (u, v) (0, 0) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor <;>
      simpa [dist_eq_norm] using ‹_›
  have := hclose hdist
  simpa [dist_eq_norm] using this

/-- Raw zeta form of one completed pair factor.  The hypotheses are exactly
the nonvanishing conditions needed to divide by the uncompleted factors. -/
theorem normalizedZetaPairFactor_eq
    {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0)
    (hζu : riemannZeta (1 + u) ≠ 0)
    (hζv : riemannZeta (1 + v) ≠ 0) :
    normalizedZetaPairFactor u v =
      ((u + v) / (u * v)) *
        (riemannZeta (1 + u + v) /
          (riemannZeta (1 + u) *
            riemannZeta (1 + v))) := by
  rw [normalizedZetaPairFactor,
    zetaResidueFactor_eq_mul_riemannZeta huv,
    zetaResidueFactor_eq_mul_riemannZeta hu,
    zetaResidueFactor_eq_mul_riemannZeta hv]
  field_simp
  ring_nf

/-! ## Finite systems of paired zeta factors -/

/-- Product of the completed pair factors for a finite family of divisor
pairs. -/
noncomputable def normalizedZetaSystemFactor
    {κ : Type*} [Fintype κ]
    (u v : κ → ℂ) : ℂ :=
  ∏ i, normalizedZetaPairFactor (u i) (v i)

@[simp]
theorem normalizedZetaSystemFactor_zero_zero
    {κ : Type*} [Fintype κ] :
    normalizedZetaSystemFactor
      (0 : κ → ℂ) (0 : κ → ℂ) = 1 := by
  simp [normalizedZetaSystemFactor]

/-- A finite product of the completed pair factors still tends to one
uniformly as all parameters tend to zero. -/
theorem tendsto_normalizedZetaSystemFactor_zero
    {κ : Type*} [Fintype κ] :
    Tendsto
      (fun z : (κ → ℂ) × (κ → ℂ) =>
        normalizedZetaSystemFactor z.1 z.2)
      (𝓝 (0, 0)) (𝓝 1) := by
  classical
  have hfactor :
      ∀ i ∈ (Finset.univ : Finset κ),
        Tendsto
          (fun z : (κ → ℂ) × (κ → ℂ) =>
            normalizedZetaPairFactor
              (z.1 i) (z.2 i))
          (𝓝 (0, 0)) (𝓝 1) := by
    intro i _
    have hcoord :
        ContinuousAt
          (fun z : (κ → ℂ) × (κ → ℂ) =>
            (z.1 i, z.2 i))
          (0, 0) := by
      fun_prop
    change
      Tendsto
        ((fun z : ℂ × ℂ =>
            normalizedZetaPairFactor z.1 z.2) ∘
          (fun z : (κ → ℂ) × (κ → ℂ) =>
            (z.1 i, z.2 i)))
        (𝓝 (0, 0)) (𝓝 1)
    exact
      tendsto_normalizedZetaPairFactor_zero.comp
        hcoord.tendsto
  simpa [normalizedZetaSystemFactor] using
    (tendsto_finsetProd
      (s := (Finset.univ : Finset κ)) hfactor)

theorem continuousAt_normalizedZetaSystemFactor_zero
    {κ : Type*} [Fintype κ] :
    ContinuousAt
      (fun z : (κ → ℂ) × (κ → ℂ) =>
        normalizedZetaSystemFactor z.1 z.2)
      (0, 0) := by
  simpa only [ContinuousAt,
    normalizedZetaSystemFactor_zero_zero] using
    (tendsto_normalizedZetaSystemFactor_zero
      (κ := κ))

/-- Epsilon--delta form of the finite-system zeta comparison.  The sup norms
give simultaneous control of every Fourier parameter. -/
theorem exists_norm_normalizedZetaSystemFactor_sub_one_lt
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : κ → ℂ,
        ‖u‖ < δ →
        ‖v‖ < δ →
        ‖normalizedZetaSystemFactor u v - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      (continuousAt_normalizedZetaSystemFactor_zero
        (κ := κ)) ε hε
  refine ⟨δ, hδ, fun u v hu hv => ?_⟩
  have hdist :
      dist (u, v) (0, 0) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor <;>
      simpa [dist_eq_norm] using ‹_›
  have := hclose hdist
  simpa [dist_eq_norm] using this

/-- Exact raw-zeta expression for a finite system of paired parameters. -/
theorem normalizedZetaSystemFactor_eq_prod
    {κ : Type*} [Fintype κ]
    {u v : κ → ℂ}
    (hu : ∀ i, u i ≠ 0)
    (hv : ∀ i, v i ≠ 0)
    (huv : ∀ i, u i + v i ≠ 0)
    (hζu : ∀ i, riemannZeta (1 + u i) ≠ 0)
    (hζv : ∀ i, riemannZeta (1 + v i) ≠ 0) :
    normalizedZetaSystemFactor u v =
      ∏ i,
        (((u i + v i) / (u i * v i)) *
          (riemannZeta (1 + u i + v i) /
            (riemannZeta (1 + u i) *
              riemannZeta (1 + v i)))) := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedZetaPairFactor_eq
    (hu i) (hv i) (huv i) (hζu i) (hζv i)

end Wikipedia.SzemeredisTheorem

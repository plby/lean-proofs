import Wikipedia.GreenTao.Sieve.CyclicLinearFormsLimitAssembly
import Wikipedia.GreenTao.Primes.ReducedResidues

/-!
# Reduced-residue cyclic linear-forms assembly

The analytic sieve estimates one fixed reduced residue and one fixed
Boolean-selected subproduct at a time.  Both indexing types are finite once
the `W`-trick modulus and the number of forms have been fixed.  This file
records the exact finite-intersection step needed by the final sieve:
eventual non-strict error bounds are retained unchanged, without passing
through a `Tendsto` statement and without requiring estimates for residues
that are not coprime to `W`.

The second theorem packages the triangle step used when the cyclic
subproduct mean is first compared with a complex Euler main term, and that
main term is then compared with one.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-- Pointwise eventual error bounds for every reduced residue and every
Boolean exponent have a common eventual range on which the linear-forms
condition holds for all reduced residues.

This is only a finite-intersection argument.  In particular, the input
bound `≤ η` is passed to `HasLinearFormsCondition` without weakening it to a
strict bound or deriving it from convergence. -/
theorem
    eventually_reducedResidues_hasLinearFormsCondition_of_eventually_subproduct_error_le
    {k W : ℕ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    {η : ℝ}
    (herror :
      ∀ b, b ∈ reducedResidues W →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            |mean
                  (linearFormsProduct k (M + 1)
                    (ν M b) e) -
                1| ≤ η) :
    ∀ᶠ M : ℕ in atTop,
      ∀ b, b ∈ reducedResidues W →
        HasLinearFormsCondition
          k (M + 1) (ν M b) η := by
  have hresidue :
      ∀ b : ↥(reducedResidues W),
        ∀ᶠ M : ℕ in atTop,
          HasLinearFormsCondition
            k (M + 1) (ν M b) η := by
    intro b
    exact
      Filter.eventually_all.mpr
        (herror b b.property)
  have hall :
      ∀ᶠ M : ℕ in atTop,
        ∀ b : ↥(reducedResidues W),
          HasLinearFormsCondition
            k (M + 1) (ν M b) η :=
    Filter.eventually_all.mpr hresidue
  filter_upwards [hall] with M hM
  intro b hb
  exact hM ⟨b, hb⟩

/-- Two pointwise eventual comparisons through a complex intermediate main
term assemble into a reduced-residue-uniform linear-forms condition.

The first budget controls the cyclic selected-subproduct mean against the
intermediate main term; the second controls that main term against one.
Their sum is the exact loss from the triangle inequality. -/
theorem
    eventually_reducedResidues_hasLinearFormsCondition_of_eventually_complex_triangle_error_le
    {k W : ℕ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    (mainTerm : ℕ → ℕ → LinearFormsExponent k → ℂ)
    {cyclicError mainTermError : ℝ}
    (hcyclic :
      ∀ b, b ∈ reducedResidues W →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            ‖(mean
                  (linearFormsProduct k (M + 1)
                    (ν M b) e) : ℂ) -
                mainTerm M b e‖ ≤ cyclicError)
    (hmainTerm :
      ∀ b, b ∈ reducedResidues W →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            ‖mainTerm M b e - 1‖ ≤ mainTermError) :
    ∀ᶠ M : ℕ in atTop,
      ∀ b, b ∈ reducedResidues W →
        HasLinearFormsCondition
          k (M + 1) (ν M b)
            (cyclicError + mainTermError) := by
  apply
    eventually_reducedResidues_hasLinearFormsCondition_of_eventually_subproduct_error_le
      ν
  intro b hb e
  filter_upwards [hcyclic b hb e, hmainTerm b hb e] with
    M hcyclicM hmainTermM
  let productMean :=
    mean
      (linearFormsProduct k (M + 1)
        (ν M b) e)
  have habs :
      |productMean - 1| =
        ‖(productMean : ℂ) - 1‖ := by
    have hcoe :
        (productMean : ℂ) - 1 =
          ((productMean - 1 : ℝ) : ℂ) := by
      norm_num
    rw [hcoe, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  calc
    ‖(productMean : ℂ) - 1‖ =
        ‖((productMean : ℂ) - mainTerm M b e) +
          (mainTerm M b e - 1)‖ := by
      congr 1
      ring
    _ ≤
        ‖(productMean : ℂ) - mainTerm M b e‖ +
          ‖mainTerm M b e - 1‖ :=
      norm_add_le _ _
    _ ≤ cyclicError + mainTermError :=
      add_le_add hcyclicM hmainTermM

end Wikipedia.SzemeredisTheorem

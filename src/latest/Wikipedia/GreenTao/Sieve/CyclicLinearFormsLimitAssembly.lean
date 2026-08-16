import Wikipedia.GreenTao.Sieve.CyclicMajorant
import Wikipedia.GreenTao.LinearForms.Condition
import Mathlib.Order.Filter.Finite

/-!
# From selected subproduct limits to the cyclic linear-forms condition

The sieve calculation fixes one Boolean exponent at a time.  The
Conlon--Fox--Zhao linear-forms condition quantifies over all such exponents,
and final Green--Tao assembly must also be uniform over the finitely many
residue representatives below a fixed `W`.

Both quantifiers are finite.  This file records the exact compactness step:
pointwise convergence of every selected subproduct mean to one implies an
eventual common linear-forms error, first for one majorant family and then
uniformly over every `b<W`.  No analytic estimate is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-- Pointwise convergence for every Boolean CFZ exponent yields one
eventual linear-forms error bound valid for all exponents simultaneously.
The modulus is written as `M+1` so its `NeZero` instance is automatic. -/
theorem eventually_hasLinearFormsCondition_of_tendsto_subproduct_means
    {k : ℕ}
    (ν : (M : ℕ) → ZMod (M + 1) → ℝ)
    (hlimit :
      ∀ e : LinearFormsExponent k,
        Tendsto
          (fun M =>
            mean
              (linearFormsProduct k (M + 1) (ν M) e))
          atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      HasLinearFormsCondition k (M + 1) (ν M) η := by
  have heventual :
      ∀ e : LinearFormsExponent k,
        ∀ᶠ M : ℕ in atTop,
          |mean
              (linearFormsProduct k (M + 1) (ν M) e) -
            1| ≤ η := by
    intro e
    have hclose :=
      (Metric.tendsto_nhds.mp (hlimit e)) η hη
    filter_upwards [hclose] with M hM
    exact (by
      simpa only [Real.dist_eq] using hM.le)
  have hall :
      ∀ᶠ M : ℕ in atTop,
        ∀ e : LinearFormsExponent k,
          |mean
              (linearFormsProduct k (M + 1) (ν M) e) -
            1| ≤ η :=
    Filter.eventually_all.mpr heventual
  exact hall

/-- Threshold form of the preceding finite-exponent compactness theorem. -/
theorem exists_threshold_hasLinearFormsCondition_of_tendsto_subproduct_means
    {k : ℕ}
    (ν : (M : ℕ) → ZMod (M + 1) → ℝ)
    (hlimit :
      ∀ e : LinearFormsExponent k,
        Tendsto
          (fun M =>
            mean
              (linearFormsProduct k (M + 1) (ν M) e))
          atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      HasLinearFormsCondition k (M + 1) (ν M) η :=
  eventually_atTop.1
    (eventually_hasLinearFormsCondition_of_tendsto_subproduct_means
      ν hlimit hη)

/-- If every fixed residue representative and every Boolean exponent has
mean tending to one, then one eventual threshold works for all `b<W` and
all exponents. -/
theorem
    eventually_all_residues_hasLinearFormsCondition_of_tendsto_subproduct_means
    {k W : ℕ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    (hlimit :
      ∀ b, b < W →
        ∀ e : LinearFormsExponent k,
          Tendsto
            (fun M =>
              mean
                (linearFormsProduct k (M + 1)
                  (ν M b) e))
            atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      ∀ b, b < W →
        HasLinearFormsCondition
          k (M + 1) (ν M b) η := by
  have hb :
      ∀ b : Fin W,
        ∀ᶠ M : ℕ in atTop,
          HasLinearFormsCondition
            k (M + 1) (ν M b) η := by
    intro b
    exact
      eventually_hasLinearFormsCondition_of_tendsto_subproduct_means
        (fun M => ν M b)
        (hlimit b b.isLt) hη
  have hall :
      ∀ᶠ M : ℕ in atTop,
        ∀ b : Fin W,
          HasLinearFormsCondition
            k (M + 1) (ν M b) η :=
    Filter.eventually_all.mpr hb
  filter_upwards [hall] with M hM
  intro b hbW
  exact hM ⟨b, hbW⟩

/-- Threshold form uniform over the finitely many standard residue
representatives. -/
theorem
    exists_threshold_all_residues_hasLinearFormsCondition_of_tendsto_subproduct_means
    {k W : ℕ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    (hlimit :
      ∀ b, b < W →
        ∀ e : LinearFormsExponent k,
          Tendsto
            (fun M =>
              mean
                (linearFormsProduct k (M + 1)
                  (ν M b) e))
            atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      ∀ b, b < W →
        HasLinearFormsCondition
          k (M + 1) (ν M b) η :=
  eventually_atTop.1
    (eventually_all_residues_hasLinearFormsCondition_of_tendsto_subproduct_means
      ν hlimit hη)

/-- Specialization to the global cyclic smooth Selberg majorant.  This is
the finite-quantifier endpoint consumed by transference once the sieve layer
proves the selected-family limit for each fixed residue and exponent. -/
theorem
    eventually_all_residues_hasLinearFormsCondition_cyclicMajorant
    {k W : ℕ}
    (χ : SmoothSieveCutoff)
    (R : ℕ → ℕ)
    (hlimit :
      ∀ b, b < W →
        ∀ e : LinearFormsExponent k,
          Tendsto
            (fun M =>
              mean
                (linearFormsProduct k (M + 1)
                  (χ.cyclicMajorant
                    (R (M + 1)) W b) e))
            atTop (𝓝 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      ∀ b, b < W →
        HasLinearFormsCondition k (M + 1)
          (χ.cyclicMajorant (R (M + 1)) W b) η := by
  exact
    eventually_all_residues_hasLinearFormsCondition_of_tendsto_subproduct_means
      (fun M b =>
        χ.cyclicMajorant (R (M + 1)) W b)
      hlimit hη

end Wikipedia.SzemeredisTheorem

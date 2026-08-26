import ErdosProblems.Erdos520.CaichAuxiliaryAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# Moment, finite-union, and summability assembly for Caich auxiliaries

This is the common probability wrapper for `W/x`, `L12`, and `L2`.  It keeps
the moment exponent arbitrary, applies Markov at each actual test point,
takes the honest finite union, and leaves only a deterministic summable
budget.  In particular, no extra factor involving `T(ell)` is inserted in
the `W` event; this is the corrected reading of Caich v2 lines 683--684.
-/

/-- Markov's inequality for an arbitrary positive natural moment. -/
theorem measureReal_lt_le_natMoment
    {Y : Omega → ℝ} {q : ℕ} {t M : ℝ}
    (hq : 0 < q) (hY : ∀ omega, 0 ≤ Y omega) (ht : 0 < t)
    (hYpow : Integrable (fun omega ↦ Y omega ^ q) μ)
    (hmoment : (∫ omega, Y omega ^ q ∂μ) ≤ M) :
    μ.real {omega | t < Y omega} ≤ M / t ^ q := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ)
    (ae_of_all μ fun omega ↦ pow_nonneg (hY omega) q)
    hYpow (t ^ q)
  have hsubset :
      {omega | t < Y omega} ⊆ {omega | t ^ q ≤ Y omega ^ q} := by
    intro omega homega
    change t < Y omega at homega
    exact le_of_lt
      (pow_lt_pow_left₀ homega ht.le (Nat.ne_of_gt hq))
  have htpow : 0 < t ^ q := pow_pos ht q
  have hmul : t ^ q * μ.real {omega | t < Y omega} ≤ M :=
    calc
      t ^ q * μ.real {omega | t < Y omega} ≤
          t ^ q * μ.real {omega | t ^ q ≤ Y omega ^ q} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) htpow.le
      _ ≤ ∫ omega, Y omega ^ q ∂μ := hmarkov
      _ ≤ M := hmoment
  exact (le_div_iff₀ htpow).2 (by simpa [mul_comm] using! hmul)

/-- Deterministic finite-union budget for one auxiliary value at every test
point of a scale. -/
noncomputable def caichAuxiliaryFiniteUnionMomentBudget
    (tests : ℕ → Finset ℕ) (moment : ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (q : ℕ) (ell : ℕ) : ℝ :=
  ∑ r ∈ tests ell, moment ell r / threshold ell ^ q

/-- Markov plus the exact finite union over the selected test points. -/
theorem measureReal_caichAuxiliaryComponentFailure_le_natMomentBudget
    (tests : ℕ → Finset ℕ)
    (value : ℕ → ℕ → Omega → ℝ)
    (moment : ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (q : ℕ)
    (hq : 0 < q)
    (hvalue : ∀ ell r omega, 0 ≤ value ell r omega)
    (hthreshold : ∀ ell, 0 < threshold ell)
    (hintegrable : ∀ ell r,
      Integrable (fun omega ↦ value ell r omega ^ q) μ)
    (hmoment : ∀ ell r,
      (∫ omega, value ell r omega ^ q ∂μ) ≤ moment ell r)
    (ell : ℕ) :
    μ.real (caichAuxiliaryComponentFailure tests value threshold ell) ≤
      caichAuxiliaryFiniteUnionMomentBudget
        tests moment threshold q ell := by
  let point : ℕ → Set Omega := fun r ↦
    {omega | threshold ell < value ell r omega}
  have hfailure :
      caichAuxiliaryComponentFailure tests value threshold ell =
        ⋃ r ∈ tests ell, point r := by
    ext omega
    simp only [caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale, Set.mem_setOf_eq, not_forall,
      not_le, Set.mem_iUnion, exists_prop, point]
  rw [hfailure]
  calc
    μ.real (⋃ r ∈ tests ell, point r) ≤
        ∑ r ∈ tests ell, μ.real (point r) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ tests ell,
        moment ell r / threshold ell ^ q := by
      gcongr with r hr
      exact measureReal_lt_le_natMoment hq (hvalue ell r)
        (hthreshold ell) (hintegrable ell r) (hmoment ell r)
    _ = caichAuxiliaryFiniteUnionMomentBudget
        tests moment threshold q ell := rfl

/-- A summable displayed moment/union budget proves summability of the
corresponding auxiliary failures. -/
theorem summable_measureReal_caichAuxiliaryComponentFailure_of_natMoment
    (tests : ℕ → Finset ℕ)
    (value : ℕ → ℕ → Omega → ℝ)
    (moment : ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (q : ℕ)
    (hq : 0 < q)
    (hvalue : ∀ ell r omega, 0 ≤ value ell r omega)
    (hthreshold : ∀ ell, 0 < threshold ell)
    (hintegrable : ∀ ell r,
      Integrable (fun omega ↦ value ell r omega ^ q) μ)
    (hmoment : ∀ ell r,
      (∫ omega, value ell r omega ^ q ∂μ) ≤ moment ell r)
    (hbudget : Summable
      (caichAuxiliaryFiniteUnionMomentBudget
        tests moment threshold q)) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests value threshold ell) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) _ hbudget
  intro ell
  exact measureReal_caichAuxiliaryComponentFailure_le_natMomentBudget
    tests value moment threshold q hq hvalue hthreshold
      hintegrable hmoment ell

/-- Exponential pointwise decay beats the exact test entropy. -/
theorem summable_caichAuxiliaryFiniteUnionMomentBudget_of_exp
    (tests : ℕ → Finset ℕ) (moment : ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (q : ℕ) (U : ℕ → ℝ)
    (hterm : ∀ ell r, r ∈ tests ell →
      moment ell r / threshold ell ^ q ≤ Real.exp (-U ell))
    (hterm_nonneg : ∀ ell r,
      0 ≤ moment ell r / threshold ell ^ q)
    (hentropy : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (U ell / 2))
    (hlinear : ∀ ell : ℕ, 2 * (ell : ℝ) ≤ U ell) :
    Summable (caichAuxiliaryFiniteUnionMomentBudget
      tests moment threshold q) := by
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold caichAuxiliaryFiniteUnionMomentBudget
    exact Finset.sum_nonneg fun r hr ↦ hterm_nonneg ell r
  · intro ell
    unfold caichAuxiliaryFiniteUnionMomentBudget
    calc
      (∑ r ∈ tests ell, moment ell r / threshold ell ^ q) ≤
          ∑ _r ∈ tests ell, Real.exp (-U ell) := by
        gcongr with r hr
        exact hterm ell r hr
      _ = ((tests ell).card : ℝ) * Real.exp (-U ell) := by simp
      _ ≤ Real.exp (U ell / 2) * Real.exp (-U ell) :=
        mul_le_mul_of_nonneg_right (hentropy ell) (Real.exp_pos _).le
      _ = Real.exp (-U ell / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(ell : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith [hlinear ell]
  · exact Real.summable_exp_neg_nat

end Problem520
end Erdos

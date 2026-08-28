import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.Finite

/-!
# Locally uniform bounds on the roots of monic polynomial families

Continuity of finitely many coefficients gives a common Cauchy bound on a
neighbourhood. The degree may drop, and the parameter space need not be a
normed space. No continuity of a chosen root is required.
-/

open Filter Topology
open scoped NNReal

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

/-- Roots of a monic polynomial family of bounded degree are uniformly
bounded near a point where all the lower coefficients are continuous. -/
theorem exists_pos_eventually_root_norm_le {X : Type*} [TopologicalSpace X]
    {a : X} (P : X → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ z, (P z).Monic) (hdegree : ∀ z, (P z).natDegree ≤ n)
    (hc : ∀ i < n, ContinuousAt (fun z => (P z).coeff i) a) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z in 𝓝 a, ∀ w, (P z).IsRoot w → ‖w‖ ≤ M := by
  let B : ℝ≥0 := (Finset.range n).sup (fun i => ‖(P a).coeff i‖₊) + 1
  have hcoeff : ∀ᶠ z in 𝓝 a, ∀ i ∈ Finset.range n, ‖(P z).coeff i‖₊ ≤ B := by
    rw [Filter.eventually_all_finset]
    intro i hi
    apply (hc i (Finset.mem_range.mp hi)).nnnorm.eventually_le_const
    exact lt_of_le_of_lt
      (Finset.le_sup (f := fun j => ‖(P a).coeff j‖₊) hi) (lt_add_one _)
  refine ⟨(B : ℝ) + 1, add_pos_of_nonneg_of_pos B.2 zero_lt_one, ?_⟩
  filter_upwards [hcoeff] with z hz w hw
  have hsup : (Finset.range (P z).natDegree).sup (fun i => ‖(P z).coeff i‖₊) ≤ B := by
    apply Finset.sup_le
    intro i hi
    exact hz i (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le (hdegree z)))
  have hbound : (P z).cauchyBound ≤ B + 1 := by
    simpa [Polynomial.cauchyBound, (hmonic z).leadingCoeff]
      using add_le_add_right hsup (1 : ℝ≥0)
  have hw' : ‖w‖₊ ≤ B + 1 :=
    (Polynomial.IsRoot.norm_lt_cauchyBound (hmonic z).ne_zero hw).le.trans hbound
  exact_mod_cast hw'

end Wikipedia.HopfProblem.CuspNormalization.Germs

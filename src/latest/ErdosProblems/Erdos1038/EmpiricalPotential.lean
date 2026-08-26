import ErdosProblems.Erdos1038.PolynomialBridge


/-!
# Empirical logarithmic potentials

Mathlib defines `Real.log 0 = 0`, whereas the paper informally uses
`log 0 = -∞`.  This module makes the trust boundary explicit: the normalized
finite logarithmic sum agrees with `natDegree⁻¹ * log |f|` away from the
finite root set, and its negative set therefore has exactly the same
Lebesgue measure as the polynomial sublevel set.  No assertion is made at
the roots themselves.
-/

open scoped ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- Normalized logarithmic potential of the empirical root multiset. -/
def empiricalPotential (f : Polynomial ℝ) (x : ℝ) : ℝ :=
  (f.natDegree : ℝ)⁻¹ *
    (f.roots.map fun r => Real.log |x - r|).sum

/-- Negative set of the real-valued empirical potential. -/
def potentialNegativeSet (f : Polynomial ℝ) : Set ℝ :=
  {x | empiricalPotential f x < 0}

/-- The finite set underlying the root multiset. -/
def rootSet (f : Polynomial ℝ) : Set ℝ := ↑f.roots.toFinset

theorem mem_rootSet_iff {f : Polynomial ℝ} {x : ℝ} :
    x ∈ rootSet f ↔ x ∈ f.roots := by
  simp [rootSet]

theorem rootSet_finite (f : Polynomial ℝ) : (rootSet f).Finite :=
  f.roots.toFinset.finite_toSet

theorem volume_rootSet (f : Polynomial ℝ) : volume (rootSet f) = 0 :=
  (rootSet_finite f).measure_zero volume

/-- The exact logarithmic product formula away from the roots. -/
theorem log_abs_eval_eq_sum_log_abs_roots {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∉ rootSet f) :
    Real.log |f.eval x| =
      (f.roots.map fun r => Real.log |x - r|).sum := by
  have hnonzero :
      ∀ y ∈ f.roots.map (fun r => |x - r|), y ≠ 0 := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    rw [abs_ne_zero]
    intro hxr
    apply hx
    rw [mem_rootSet_iff]
    have heq : x = r := sub_eq_zero.mp hxr
    simpa [heq] using! hr
  have hlog := Real.log_multiset_prod hnonzero
  rw [← hf.abs_eval_eq_prod_abs_roots] at hlog
  simpa only [Multiset.map_map, Function.comp_apply] using! hlog

/-- Away from roots, negativity of the normalized logarithmic potential is
equivalent to strict polynomial sublevel membership. -/
theorem empiricalPotential_neg_iff_sublevel {f : Polynomial ℝ}
    (hf : IsAdmissible f) {x : ℝ} (hx : x ∉ rootSet f) :
    empiricalPotential f x < 0 ↔ x ∈ sublevelSet f := by
  have hdegree : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hf.monic.natDegree_pos.mpr hf.ne_one
  have heval : f.eval x ≠ 0 := by
    rw [hf.eval_eq_prod_roots]
    apply Multiset.prod_ne_zero
    intro hmem
    obtain ⟨r, hr, hzero⟩ := Multiset.mem_map.mp hmem
    apply hx
    rw [mem_rootSet_iff]
    have : x = r := sub_eq_zero.mp hzero
    simpa [this] using! hr
  rw [empiricalPotential, ← log_abs_eval_eq_sum_log_abs_roots hf hx]
  have habspos : 0 < |f.eval x| := abs_pos.mpr heval
  have hinvpos : 0 < (f.natDegree : ℝ)⁻¹ := inv_pos.mpr hdegree
  rw [mul_neg_iff]
  simp only [hinvpos, true_and, not_lt_of_ge hinvpos.le, false_and,
    or_false]
  rw [Real.log_neg_iff habspos]
  rfl

/-- The paper's empirical-potential sublevel set and the original polynomial
sublevel set agree in Lebesgue measure. -/
theorem sublevelVolume_eq_volume_potentialNegativeSet {f : Polynomial ℝ}
    (hf : IsAdmissible f) :
    sublevelVolume f = volume (potentialNegativeSet f) := by
  rw [sublevelVolume]
  apply MeasureTheory.measure_congr
  have hae : ∀ᵐ x : ℝ ∂volume, x ∉ rootSet f := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not] using! volume_rootSet f
  filter_upwards [hae] with x hx
  change (x ∈ sublevelSet f) = (empiricalPotential f x < 0)
  exact propext (empiricalPotential_neg_iff_sublevel hf hx).symm

end

end Erdos1038

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Chapter VII, Section 6: indices of power subgroups

Proposition 6.8 computes the index of the subgroup of `n`th powers in a
characteristic-zero local field.  Its finite-group algebraic core is the
first-isomorphism identity saying that the index of the power image is the
cardinality of the `n`-torsion kernel.  For multiplicative groups this kernel
is the group of `n`th roots of unity.

The archimedean cases are completely available: algebraic closedness handles
`ℂ`, while the ordered-field power calculation gives the odd/even alternatives
over `ℝ`.  The nonarchimedean formula additionally requires the finite-index
exponential-map comparison used in the source; it is not presently packaged.
-/

namespace Towers.CField.KNIndex

noncomputable section

/-- The algebraic kernel/image identity underlying Milne's `h_n(M)` for a
finite commutative group. -/
theorem subgroup_index_card
    (M : Type*) [CommGroup M] [Finite M] (n : ℕ) :
    (powMonoidHom n : M →* M).range.index =
      Nat.card (powMonoidHom n : M →* M).ker :=
  Subgroup.index_range

/-- For a finite multiplicative group, the power-subgroup index is the
number of `n`th roots of unity. -/
theorem roots_unity_card
    (M : Type*) [CommGroup M] [Finite M] (n : ℕ) :
    (powMonoidHom n : Mˣ →* Mˣ).range.index =
      Nat.card (rootsOfUnity n M) := by
  rw [Subgroup.index_range, rootsOfUnity_eq_ker]

/-- The `n`th-power map on `ℂˣ` is surjective for positive `n`. -/
theorem complex_monoid_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (powMonoidHom n : ℂˣ →* ℂˣ) := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℂ) hn
  have hz0 : z ≠ 0 := by
    intro h
    have hzero : (0 : ℂ) = (u : ℂ) := by
      simpa [h, hn.ne'] using hz
    exact u.ne_zero hzero.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  ext
  exact hz

/-- **Proposition VII.6.8, complex index formula.** Every nonzero complex
number is an `n`th power, so the power subgroup has index one. -/
theorem complex_power_index (n : ℕ) (hn : 0 < n) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range.index = 1 := by
  rw [MonoidHom.range_eq_top.mpr (complex_monoid_surjective n hn)]
  exact Subgroup.index_top

/-- The root-of-unity factor in the complex case of Proposition 6.8 has
cardinality `n`. -/
theorem complex_roots_unity (n : ℕ) [NeZero n] :
    Nat.card (rootsOfUnity n ℂ) = n := by
  exact Complex.card_rootsOfUnity n

private theorem real_unit_pos
    (u : ℝˣ) (hu : 0 < (u : ℝ)) {n : ℕ} (hn : n ≠ 0) :
    ∃ z : ℝˣ, z ^ n = u := by
  let r : ℝ := (u : ℝ) ^ ((n : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hu _
  let z : ℝˣ := Units.mk0 r hr.ne'
  refine ⟨z, ?_⟩
  ext
  exact Real.rpow_inv_natCast_pow hu.le hn

/-- For positive even `n`, the `n`th powers in `ℝˣ` are exactly the positive
units. -/
theorem real_even_pos
    {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = Units.posSubgroup ℝ := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact hn.pow_pos x.ne_zero
  · intro y hy
    obtain ⟨z, hz⟩ := real_unit_pos y hy hn0
    exact ⟨z, hz⟩

/-- **Proposition VII.6.8, real even case.** The subgroup of even powers in
`ℝˣ` has index two. -/
theorem real_even_index
    {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [real_even_pos hn hn0]
  exact Units.index_posSubgroup ℝ

/-- For odd `n`, every nonzero real number is an `n`th power. -/
theorem real_odd_monoid
    {n : ℕ} (hn : Odd n) :
    Function.Surjective (powMonoidHom n : ℝˣ →* ℝˣ) := by
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, hk⟩
    omega
  intro u
  by_cases hu : 0 < (u : ℝ)
  · exact real_unit_pos u hu hn0
  · have hu_neg : (u : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hu) u.ne_zero
    have hneg_pos : 0 < ((-u : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hu_neg
    obtain ⟨z, hz⟩ := real_unit_pos (-u) hneg_pos hn0
    refine ⟨-z, ?_⟩
    apply Units.ext
    change (-(z : ℝ)) ^ n = (u : ℝ)
    rw [hn.neg_pow]
    have hz' : (z : ℝ) ^ n = -(u : ℝ) := congrArg Units.val hz
    linarith

/-- **Proposition VII.6.8, real odd case.** The subgroup of odd powers in
`ℝˣ` has index one. -/
theorem real_odd_index
    {n : ℕ} (hn : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 1 := by
  rw [MonoidHom.range_eq_top.mpr (real_odd_monoid hn)]
  exact Subgroup.index_top

end

end Towers.CField.KNIndex

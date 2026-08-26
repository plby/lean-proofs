import ErdosProblems.Erdos1038.ResidualWidthInverseBranch

/-!
# Invariance of inverse-width series under coordinate refinement

A common quantile refinement replaces every coordinate by finitely many
copies, divides its Lagrange weight equally among those copies, and repeats
the target value.  This operation does not change the Lagrange kernel, any
scaled coefficient, the odd inverse-width series, or its material
directional derivative.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set

namespace Erdos1038

noncomputable section

/-- Repeat every coordinate `m` times. -/
def refinedCoordinates {iota : Type*} (m : ℕ) (d : iota → ℝ) :
    iota × Fin m → ℝ :=
  fun p ↦ d p.1

/-- Divide a coordinate weight equally among its `m` copies. -/
def refinedLagrangeWeight {iota : Type*} (m : ℕ) (a : iota → ℝ) :
    iota × Fin m → ℝ :=
  fun p ↦ a p.1 / (m : ℝ)

lemma refinedCoordinates_mem_positiveCoordinates
    {iota : Type*} [Fintype iota] {m : ℕ} {d : iota → ℝ}
    (hd : d ∈ positiveCoordinates iota) :
    refinedCoordinates m d ∈ positiveCoordinates (iota × Fin m) := by
  intro p
  exact hd p.1

lemma refinedLagrangeWeight_pos
    {iota : Type*} {m : ℕ} (hm : 0 < m) {a : iota → ℝ}
    (ha : ∀ i, 0 < a i) (p : iota × Fin m) :
    0 < refinedLagrangeWeight m a p := by
  exact div_pos (ha p.1) (Nat.cast_pos.mpr hm)

lemma refinedCoordinates_lineMap
    {iota : Type*} [Fintype iota] (m : ℕ)
    (reference target : iota → ℝ) (t : ℝ) :
    AffineMap.lineMap (k := ℝ)
        (refinedCoordinates m reference) (refinedCoordinates m target) t =
      refinedCoordinates m
        (AffineMap.lineMap (k := ℝ) reference target t) := by
  funext p
  simp only [AffineMap.lineMap_apply_module, refinedCoordinates,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private lemma inverseMonomial_refined
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (gamma d : iota → ℝ) :
    inverseMonomial (refinedLagrangeWeight m gamma)
        (refinedCoordinates m d) =
      inverseMonomial gamma d := by
  classical
  unfold inverseMonomial refinedLagrangeWeight refinedCoordinates
  congr 1
  rw [Fintype.sum_prod_type]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']

private lemma lagrangePhi_refined
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a d : iota → ℝ) :
    PowerSeries.lagrangePhi (refinedLagrangeWeight m a)
        (refinedCoordinates m d) =
      PowerSeries.lagrangePhi a d := by
  classical
  unfold PowerSeries.lagrangePhi refinedLagrangeWeight refinedCoordinates
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _hi
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [PowerSeries.lagrangeFactorSeries_pow]
  congr 2
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']

/-- Every scaled Lagrange coefficient is invariant under equal splitting of
coordinates. -/
theorem scaledLagrangeCoefficient_refined
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota)
    (n : ℕ) :
    scaledLagrangeCoefficient (refinedLagrangeWeight m a) n
        (refinedCoordinates m d) =
      scaledLagrangeCoefficient a n d := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [scaledLagrangeCoefficient, scaledLagrangeTerm,
      scaledLagrangePrefactor]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [scaledLagrangeCoefficient_eq_mul_coeff_phi_pow
      (refinedLagrangeWeight m a) (refinedCoordinates m d)
      (refinedCoordinates_mem_positiveCoordinates hd) hn]
    rw [scaledLagrangeCoefficient_eq_mul_coeff_phi_pow a d hd hn]
    have hweight :
        (fun p : iota × Fin m ↦
            (n : ℝ) * refinedLagrangeWeight m a p) =
          refinedLagrangeWeight m (fun i ↦ (n : ℝ) * a i) := by
      funext p
      unfold refinedLagrangeWeight
      ring
    rw [hweight, inverseMonomial_refined hm,
      lagrangePhi_refined hm]

/-- Coefficient summability is likewise unchanged by refinement. -/
theorem summable_scaledLagrangeCoefficient_refined_iff
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota) :
    Summable (fun n ↦
      scaledLagrangeCoefficient (refinedLagrangeWeight m a) n
        (refinedCoordinates m d)) ↔
      Summable (fun n ↦ scaledLagrangeCoefficient a n d) := by
  apply summable_congr
  intro n
  exact scaledLagrangeCoefficient_refined hm a d hd n

/-- The exact odd inverse-width series is invariant under refinement. -/
theorem inverseWidthSeries_refined
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a d : iota → ℝ) (hd : d ∈ positiveCoordinates iota) :
    inverseWidthSeries (refinedLagrangeWeight m a)
        (refinedCoordinates m d) =
      inverseWidthSeries a d := by
  unfold inverseWidthSeries
  congr 1
  apply tsum_congr
  intro j
  exact scaledLagrangeCoefficient_refined hm a d hd (2 * j + 1)

/-- The derivative of every scaled coefficient along a simultaneously
refined material line agrees with the unrefined derivative. -/
theorem scaledLagrangeCoefficientDirectional_refined
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a reference target : iota → ℝ)
    (href : reference ∈ positiveCoordinates iota)
    (htarget : target ∈ positiveCoordinates iota) (n : ℕ) :
    scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight m a) n
        (refinedCoordinates m reference) (refinedCoordinates m target) =
      scaledLagrangeCoefficientDirectional a n reference target := by
  let refinedLine : ℝ → ℝ :=
    scaledLagrangeCoefficient (refinedLagrangeWeight m a) n ∘
      AffineMap.lineMap (k := ℝ)
        (refinedCoordinates m reference) (refinedCoordinates m target)
  let originalLine : ℝ → ℝ :=
    scaledLagrangeCoefficient a n ∘
      AffineMap.lineMap (k := ℝ) reference target
  have hlines : ∀ t ∈ Icc (0 : ℝ) 1, refinedLine t = originalLine t := by
    intro t ht
    change scaledLagrangeCoefficient (refinedLagrangeWeight m a) n
        (AffineMap.lineMap (k := ℝ)
          (refinedCoordinates m reference) (refinedCoordinates m target) t) =
      scaledLagrangeCoefficient a n
        (AffineMap.lineMap (k := ℝ) reference target t)
    rw [refinedCoordinates_lineMap]
    apply scaledLagrangeCoefficient_refined hm
    intro i
    simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases ht0 : t = 0
    · subst t
      simpa using! href i
    · have htPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      by_cases ht1 : t = 1
      · subst t
        simpa using! htarget i
      · have htLt : t < 1 := lt_of_le_of_ne ht.2 ht1
        exact add_pos (mul_pos (sub_pos.mpr htLt) (href i))
          (mul_pos htPos (htarget i))
  have hrefined := hasDerivAt_scaledLagrangeCoefficient_line
    (refinedLagrangeWeight m a) n
    (target := refinedCoordinates m target)
    (refinedCoordinates_mem_positiveCoordinates href)
  have horiginal := hasDerivAt_scaledLagrangeCoefficient_line
    a n (target := target) href
  change HasDerivAt refinedLine _ 0 at hrefined
  change HasDerivAt originalLine _ 0 at horiginal
  have hrefinedWithin : HasDerivWithinAt originalLine
      (scaledLagrangeCoefficientDirectional
        (refinedLagrangeWeight m a) n
        (refinedCoordinates m reference) (refinedCoordinates m target))
      (Icc (0 : ℝ) 1) 0 :=
    hrefined.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ (hlines t ht).symm) (by simp)
  have hunique := uniqueDiffOn_Icc_zero_one 0
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
  exact (hrefinedWithin.derivWithin hunique).symm.trans
    (horiginal.hasDerivWithinAt.derivWithin hunique)

/-- The exact odd directional series is invariant under simultaneous
refinement of reference and target coordinates. -/
theorem inverseWidthSeriesDirectional_refined
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a reference target : iota → ℝ)
    (href : reference ∈ positiveCoordinates iota)
    (htarget : target ∈ positiveCoordinates iota) :
    inverseWidthSeriesDirectional (refinedLagrangeWeight m a)
        (refinedCoordinates m reference) (refinedCoordinates m target) =
      inverseWidthSeriesDirectional a reference target := by
  unfold inverseWidthSeriesDirectional
  congr 1
  apply tsum_congr
  intro j
  exact scaledLagrangeCoefficientDirectional_refined
    hm a reference target href htarget (2 * j + 1)

/-- Directional odd-series summability is invariant under simultaneous
refinement. -/
theorem summable_scaledLagrangeCoefficientDirectional_refined_iff
    {iota : Type*} [Fintype iota] {m : ℕ} (hm : 0 < m)
    (a reference target : iota → ℝ)
    (href : reference ∈ positiveCoordinates iota)
    (htarget : target ∈ positiveCoordinates iota) :
    Summable (fun j ↦ scaledLagrangeCoefficientDirectional
      (refinedLagrangeWeight m a) (2 * j + 1)
      (refinedCoordinates m reference) (refinedCoordinates m target)) ↔
      Summable (fun j ↦ scaledLagrangeCoefficientDirectional
        a (2 * j + 1) reference target) := by
  apply summable_congr
  intro j
  exact scaledLagrangeCoefficientDirectional_refined
    hm a reference target href htarget (2 * j + 1)

end

end Erdos1038

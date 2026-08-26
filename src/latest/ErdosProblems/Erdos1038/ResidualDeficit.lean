import ErdosProblems.Erdos1038.ResidualRadius
import ErdosProblems.Erdos1038.LowKEntropy

/-!
# Mean-deficit and radius estimates for residual configurations

This file formalizes the elementary `1 ≤ k ≤ 29 / 20` argument.  It
controls pairwise logarithmic energy by the mean endpoint deficit, combines
that estimate with the exact residual-radius identity and weighted Jensen,
and proves that any separated residual configuration has radius sum greater
than `1 / 3`.
-/

open scoped BigOperators Real
open Finset Set

namespace Erdos1038

noncomputable section

def residualMeanDeficit {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ℝ :=
  ∑ i, C.weight i * (2 - C.location i)

def residualQuadraticMass {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ℝ :=
  ∑ i, (C.weight i) ^ 2

def residualOffDiagonalMass {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ℝ :=
  1 - residualQuadraticMass C

def offDiagonalPairs (ι : Type*) [Fintype ι] : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter fun p ↦ p.1 ≠ p.2

def residualPairSum {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (φ : ι → ι → ℝ) : ℝ :=
  ∑ p ∈ offDiagonalPairs ι,
    C.weight p.1 * C.weight p.2 * φ p.1 p.2

def residualPairDistance {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ℝ :=
  residualPairSum C (fun i j ↦ |C.location i - C.location j|)

def residualRadiusSum {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) : ℝ :=
  ∑ i, residualRadius C k i

def IsResidualSeparationPoint {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k b : ℝ) : Prop :=
  0 < b ∧ (∀ i, b < C.location i) ∧ 0 ≤ residualPotential C k b

lemma residual_index_univ_nonempty {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : (Finset.univ : Finset ι).Nonempty := by
  classical
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hzero : (∑ i, C.weight i) = 0 := by rw [hempty]; simp
  linarith [C.sum_weight]

lemma weight_le_one {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (i : ι) : C.weight i ≤ 1 := by
  rw [← C.sum_weight]
  exact Finset.single_le_sum (fun j _ ↦ (C.weight_pos j).le) (Finset.mem_univ i)

lemma residualMeanDeficit_nonneg {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : 0 ≤ residualMeanDeficit C := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (C.weight_pos i).le (by linarith [(C.location_mem i).2])

lemma residualQuadraticMass_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : 0 < residualQuadraticMass C := by
  classical
  apply Finset.sum_pos
  · intro i hi
    exact pow_pos (C.weight_pos i) 2
  · exact residual_index_univ_nonempty C

lemma residualOffDiagonalMass_lt_one {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : residualOffDiagonalMass C < 1 := by
  rw [residualOffDiagonalMass]
  linarith [residualQuadraticMass_pos C]

lemma sum_weight_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ResidualConfiguration ι) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, C.weight j = 1 - C.weight i := by
  classical
  have h : (∑ j ∈ Finset.univ.erase i, C.weight j) + C.weight i = 1 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), C.sum_weight]
  linarith

lemma sum_offDiagonalPairs_weight {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    ∑ p ∈ offDiagonalPairs ι, C.weight p.1 * C.weight p.2 =
      residualOffDiagonalMass C := by
  classical
  rw [offDiagonalPairs]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  -- rewrite the filtered product sum as nested erased sums
  have hrewrite (i : ι) :
      ∑ j, (if i ≠ j then C.weight i * C.weight j else 0) =
        C.weight i * (1 - C.weight i) := by
    have hfilter :
        Finset.univ.filter (fun j : ι ↦ i ≠ j) = Finset.univ.erase i := by
      ext j
      simp [ne_comm]
    calc
      ∑ j, (if i ≠ j then C.weight i * C.weight j else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : ι ↦ i ≠ j),
            C.weight i * C.weight j := by
        exact (Finset.sum_filter (s := Finset.univ)
          (fun j : ι ↦ i ≠ j) (fun j ↦ C.weight i * C.weight j)).symm
      _ = ∑ j ∈ Finset.univ.erase i, C.weight i * C.weight j := by rw [hfilter]
      _ = C.weight i * (1 - C.weight i) := by
        rw [← Finset.mul_sum, sum_weight_erase]
  simp_rw [hrewrite]
  rw [residualOffDiagonalMass, residualQuadraticMass]
  have hexpand (i : ι) :
      C.weight i * (1 - C.weight i) = C.weight i - (C.weight i) ^ 2 := by
    ring
  simp_rw [hexpand]
  rw [Finset.sum_sub_distrib]
  rw [C.sum_weight]

lemma residualOffDiagonalMass_nonneg {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : 0 ≤ residualOffDiagonalMass C := by
  rw [← sum_offDiagonalPairs_weight]
  exact Finset.sum_nonneg fun p hp ↦
    mul_nonneg (C.weight_pos p.1).le (C.weight_pos p.2).le

lemma residualPairSum_one {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    residualPairSum C (fun _ _ ↦ 1) = residualOffDiagonalMass C := by
  simpa [residualPairSum] using! sum_offDiagonalPairs_weight C

lemma residualPairEnergy_eq_pairSum {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) :
    residualPairEnergy C =
      residualPairSum C (fun i j ↦
        Real.log |C.location i - C.location j|) := by
  classical
  rw [residualPairEnergy, residualPairSum, offDiagonalPairs]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  have hrewrite (i : ι) :
      ∑ j, (if i ≠ j then
          C.weight i * C.weight j *
            Real.log |C.location i - C.location j| else 0) =
        C.weight i *
          (∑ j ∈ Finset.univ.erase i,
            C.weight j * Real.log |C.location i - C.location j|) := by
    have hfilter :
        Finset.univ.filter (fun j : ι ↦ i ≠ j) = Finset.univ.erase i := by
      ext j
      simp [ne_comm]
    calc
      ∑ j, (if i ≠ j then
          C.weight i * C.weight j *
            Real.log |C.location i - C.location j| else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : ι ↦ i ≠ j),
            C.weight i * C.weight j *
              Real.log |C.location i - C.location j| := by
        exact (Finset.sum_filter (s := Finset.univ)
          (fun j : ι ↦ i ≠ j)
          (fun j ↦ C.weight i * C.weight j *
            Real.log |C.location i - C.location j|)).symm
      _ = ∑ j ∈ Finset.univ.erase i,
          C.weight i * (C.weight j *
            Real.log |C.location i - C.location j|) := by
        rw [hfilter]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.mul_sum]
  simp_rw [hrewrite]

lemma abs_location_sub_le_deficits {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (i j : ι) :
    |C.location i - C.location j| ≤
      (2 - C.location i) + (2 - C.location j) := by
  have hi : 0 ≤ 2 - C.location i := by linarith [(C.location_mem i).2]
  have hj : 0 ≤ 2 - C.location j := by linarith [(C.location_mem j).2]
  calc
    |C.location i - C.location j| =
        |(2 - C.location j) - (2 - C.location i)| := by
          congr 1
          ring
    _ ≤ |2 - C.location j| + |2 - C.location i| := abs_sub _ _
    _ = (2 - C.location i) + (2 - C.location j) := by
      rw [abs_of_nonneg hi, abs_of_nonneg hj]
      ring

lemma residualPairDistance_le_twice_meanDeficit
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    residualPairDistance C ≤ 2 * residualMeanDeficit C := by
  classical
  let g : ι × ι → ℝ := fun p ↦
    C.weight p.1 * C.weight p.2 *
      ((2 - C.location p.1) + (2 - C.location p.2))
  calc
    residualPairDistance C ≤ ∑ p ∈ offDiagonalPairs ι, g p := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (abs_location_sub_le_deficits C p.1 p.2)
        (mul_nonneg (C.weight_pos p.1).le (C.weight_pos p.2).le)
    _ ≤ ∑ p, g p := by
      rw [offDiagonalPairs]
      simp only [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · exact le_rfl
      · dsimp [g]
        exact mul_nonneg
          (mul_nonneg (C.weight_pos p.1).le (C.weight_pos p.2).le)
          (add_nonneg (by linarith [(C.location_mem p.1).2])
            (by linarith [(C.location_mem p.2).2]))
    _ = 2 * residualMeanDeficit C := by
      rw [Fintype.sum_prod_type]
      dsimp only [g]
      simp_rw [mul_add]
      simp_rw [Finset.sum_add_distrib]
      have hleft :
          ∑ i, ∑ j,
              C.weight i * C.weight j * (2 - C.location i) =
            residualMeanDeficit C := by
        calc
          ∑ i, ∑ j,
              C.weight i * C.weight j * (2 - C.location i) =
              ∑ i, (C.weight i * (2 - C.location i)) *
                (∑ j, C.weight j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = residualMeanDeficit C := by
            simp_rw [C.sum_weight, mul_one]
            rfl
      have hright :
          ∑ i, ∑ j,
              C.weight i * C.weight j * (2 - C.location j) =
            residualMeanDeficit C := by
        calc
          ∑ i, ∑ j,
              C.weight i * C.weight j * (2 - C.location j) =
              ∑ i, C.weight i * residualMeanDeficit C := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [residualMeanDeficit, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = residualMeanDeficit C := by
            rw [← Finset.sum_mul, C.sum_weight, one_mul]
      rw [hleft, hright]
      ring

lemma normalized_offDiagonal_weight_sum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (ht : residualOffDiagonalMass C ≠ 0) :
    ∑ p ∈ offDiagonalPairs ι,
        (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) = 1 := by
  rw [← Finset.sum_div, sum_offDiagonalPairs_weight]
  exact div_self ht

lemma normalized_pairDistance_sum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    ∑ p ∈ offDiagonalPairs ι,
        (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
          |C.location p.1 - C.location p.2| =
      residualPairDistance C / residualOffDiagonalMass C := by
  rw [residualPairDistance, residualPairSum]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

lemma normalized_pairEnergy_sum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    ∑ p ∈ offDiagonalPairs ι,
        (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
          Real.log |C.location p.1 - C.location p.2| =
      residualPairEnergy C / residualOffDiagonalMass C := by
  rw [residualPairEnergy_eq_pairSum, residualPairSum]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem residualPairEnergy_le_entropy
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (hlocation : Function.Injective C.location)
    (ht : 0 < residualOffDiagonalMass C)
    (hε : 0 < residualMeanDeficit C) :
    residualPairEnergy C ≤
      residualOffDiagonalMass C *
        Real.log (2 * residualMeanDeficit C /
          residualOffDiagonalMass C) := by
  classical
  have hpair_ne {p : ι × ι} (hp : p ∈ offDiagonalPairs ι) : p.1 ≠ p.2 := by
    simpa [offDiagonalPairs] using! hp
  have hdistance_pos {p : ι × ι} (hp : p ∈ offDiagonalPairs ι) :
      0 < |C.location p.1 - C.location p.2| := by
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (hlocation.ne (hpair_ne hp))
  have hweight_nonneg {p : ι × ι} (hp : p ∈ offDiagonalPairs ι) :
      0 ≤ C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C := by
    exact div_nonneg
      (mul_nonneg (C.weight_pos p.1).le (C.weight_pos p.2).le) ht.le
  have hweight_sum :
      ∑ p ∈ offDiagonalPairs ι,
          C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C = 1 :=
    normalized_offDiagonal_weight_sum C ht.ne'
  have hjensen :
      (∑ p ∈ offDiagonalPairs ι,
          (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
            Real.log |C.location p.1 - C.location p.2|) ≤
        Real.log
          (∑ p ∈ offDiagonalPairs ι,
            (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
              |C.location p.1 - C.location p.2|) := by
    simpa only [smul_eq_mul, Function.comp_apply] using!
      (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
        (t := offDiagonalPairs ι)
        (w := fun p : ι × ι ↦
          C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C)
        (p := fun p : ι × ι ↦ |C.location p.1 - C.location p.2|)
        (fun p hp ↦ hweight_nonneg hp) hweight_sum
        (fun p hp ↦ hdistance_pos hp)
  have hnormalized_pos :
      0 < ∑ p ∈ offDiagonalPairs ι,
          (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
            |C.location p.1 - C.location p.2| := by
    have hnonempty : (offDiagonalPairs ι).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      rw [hempty] at hweight_sum
      simp at hweight_sum
    exact Finset.sum_pos
      (fun p hp ↦ mul_pos
        (div_pos (mul_pos (C.weight_pos p.1) (C.weight_pos p.2)) ht)
        (hdistance_pos hp)) hnonempty
  have hnormalized_le :
      (∑ p ∈ offDiagonalPairs ι,
          (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
            |C.location p.1 - C.location p.2|) ≤
        2 * residualMeanDeficit C / residualOffDiagonalMass C := by
    rw [normalized_pairDistance_sum]
    exact (div_le_div_iff_of_pos_right ht).2
      (residualPairDistance_le_twice_meanDeficit C)
  have hupper_pos :
      0 < 2 * residualMeanDeficit C / residualOffDiagonalMass C := by
    positivity
  have hlog_le :
      Real.log
          (∑ p ∈ offDiagonalPairs ι,
            (C.weight p.1 * C.weight p.2 / residualOffDiagonalMass C) *
              |C.location p.1 - C.location p.2|) ≤
        Real.log (2 * residualMeanDeficit C /
          residualOffDiagonalMass C) :=
    Real.strictMonoOn_log.monotoneOn hnormalized_pos hupper_pos hnormalized_le
  rw [normalized_pairEnergy_sum, normalized_pairDistance_sum] at hjensen
  rw [normalized_pairDistance_sum] at hlog_le
  have hquotient :
      residualPairEnergy C / residualOffDiagonalMass C ≤
        Real.log (2 * residualMeanDeficit C /
          residualOffDiagonalMass C) := by
    exact hjensen.trans hlog_le
  have := (div_le_iff₀ ht).1 hquotient
  simpa [mul_comm] using! this

lemma offDiagonalPairs_eq_empty_of_mass_eq_zero
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (ht : residualOffDiagonalMass C = 0) :
    offDiagonalPairs ι = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hsum :
      ∑ p ∈ offDiagonalPairs ι, C.weight p.1 * C.weight p.2 = 0 := by
    rw [sum_offDiagonalPairs_weight, ht]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun p hp ↦ mul_nonneg (C.weight_pos p.1).le
      (C.weight_pos p.2).le)).1 hsum
  have hpzero := hall p hp
  have hppos := mul_pos (C.weight_pos p.1) (C.weight_pos p.2)
  linarith

lemma residualPairEnergy_eq_zero_of_offDiagonalMass_eq_zero
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (ht : residualOffDiagonalMass C = 0) :
    residualPairEnergy C = 0 := by
  rw [residualPairEnergy_eq_pairSum, residualPairSum,
    offDiagonalPairs_eq_empty_of_mass_eq_zero C ht]
  simp

theorem residualPairEnergy_le_entropy_continuous
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (hlocation : Function.Injective C.location)
    (hε : 0 < residualMeanDeficit C) :
    residualPairEnergy C ≤
      residualOffDiagonalMass C *
        Real.log (2 * residualMeanDeficit C /
          residualOffDiagonalMass C) := by
  rcases (residualOffDiagonalMass_nonneg C).eq_or_lt with ht | ht
  · rw [← ht, residualPairEnergy_eq_zero_of_offDiagonalMass_eq_zero C ht.symm]
    simp
  · exact residualPairEnergy_le_entropy C hlocation ht hε

lemma residual_weighted_log_location_le_log_two
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    ∑ i, C.weight i * Real.log (C.location i) ≤ Real.log 2 := by
  calc
    ∑ i, C.weight i * Real.log (C.location i) ≤
        ∑ i, C.weight i * Real.log 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (C.weight_pos i).le
      exact Real.strictMonoOn_log.monotoneOn
        (by linarith [(C.location_mem i).1] : 0 < C.location i)
        (by norm_num) (C.location_mem i).2
    _ = Real.log 2 := by rw [← Finset.sum_mul, C.sum_weight, one_mul]

theorem residual_weighted_log_radius_lower
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 0 ≤ k) (hlocation : Function.Injective C.location)
    (hε : 0 < residualMeanDeficit C) :
    -k * Real.log 2 -
        residualOffDiagonalMass C *
          Real.log (2 * residualMeanDeficit C /
            residualOffDiagonalMass C) ≤
      ∑ i, (C.weight i) ^ 2 * Real.log (residualRadius C k i) := by
  rw [residualRadius_energy_identity]
  have hlocationLog := residual_weighted_log_location_le_log_two C
  have hmul :
      k * (∑ i, C.weight i * Real.log (C.location i)) ≤
        k * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlocationLog hk
  have henergy := residualPairEnergy_le_entropy_continuous
    C hlocation hε
  linarith

lemma normalized_quadratic_weight_sum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    ∑ i, (C.weight i) ^ 2 / residualQuadraticMass C = 1 := by
  rw [← Finset.sum_div, residualQuadraticMass]
  exact div_self (residualQuadraticMass_pos C).ne'

lemma normalized_weighted_radius_le_radiusSum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) (k : ℝ) :
    (∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
        residualRadius C k i) ≤ residualRadiusSum C k := by
  apply Finset.sum_le_sum
  intro i hi
  have hwile : (C.weight i) ^ 2 / residualQuadraticMass C ≤ 1 := by
    rw [← normalized_quadratic_weight_sum C]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun j ↦ (C.weight j) ^ 2 / residualQuadraticMass C)
      (fun j hj ↦ div_nonneg (sq_nonneg _)
        (residualQuadraticMass_pos C).le) (Finset.mem_univ i)
  have hr := residualRadius_pos C k i
  nlinarith [mul_nonneg (sub_nonneg.mpr hwile) hr.le]

lemma normalized_weighted_radius_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) (k : ℝ) :
    0 < ∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
        residualRadius C k i := by
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (div_pos (sq_pos_of_pos (C.weight_pos i))
      (residualQuadraticMass_pos C)) (residualRadius_pos C k i)
  · exact residual_index_univ_nonempty C

lemma residualRadiusSum_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) (k : ℝ) :
    0 < residualRadiusSum C k := by
  apply Finset.sum_pos
  · intro i hi
    exact residualRadius_pos C k i
  · exact residual_index_univ_nonempty C

theorem normalized_weighted_log_radius_le_log_sum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) (k : ℝ) :
    (∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
        Real.log (residualRadius C k i)) ≤
      Real.log (residualRadiusSum C k) := by
  have hjensen :
      (∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
          Real.log (residualRadius C k i)) ≤
        Real.log
          (∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
            residualRadius C k i) := by
    simpa only [smul_eq_mul, Function.comp_apply] using!
      (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
        (t := (Finset.univ : Finset ι))
        (w := fun i ↦ (C.weight i) ^ 2 / residualQuadraticMass C)
        (p := fun i ↦ residualRadius C k i)
        (fun i hi ↦ div_nonneg (sq_nonneg _)
          (residualQuadraticMass_pos C).le)
        (normalized_quadratic_weight_sum C)
        (fun i hi ↦ residualRadius_pos C k i)
  have hlogmono :
      Real.log
          (∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
            residualRadius C k i) ≤
        Real.log (residualRadiusSum C k) :=
    Real.strictMonoOn_log.monotoneOn
      (normalized_weighted_radius_pos C k)
      (residualRadiusSum_pos C k)
      (normalized_weighted_radius_le_radiusSum C k)
  exact hjensen.trans hlogmono

lemma normalized_weighted_log_radius_eq_div
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) (k : ℝ) :
    (∑ i, ((C.weight i) ^ 2 / residualQuadraticMass C) *
        Real.log (residualRadius C k i)) =
      (∑ i, (C.weight i) ^ 2 * Real.log (residualRadius C k i)) /
        residualQuadraticMass C := by
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

lemma residualQuadraticMass_eq_one_sub_offDiagonalMass
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    residualQuadraticMass C = 1 - residualOffDiagonalMass C := by
  rw [residualOffDiagonalMass]
  ring

theorem residual_radius_log_calibration_base
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 0 ≤ k) (hlocation : Function.Injective C.location)
    (hε : 0 < residualMeanDeficit C) :
    -k * Real.log 2 -
        residualOffDiagonalMass C *
          Real.log (2 * residualMeanDeficit C /
            residualOffDiagonalMass C) ≤
      (1 - residualOffDiagonalMass C) *
        Real.log (residualRadiusSum C k) := by
  have hlower := residual_weighted_log_radius_lower C hk hlocation hε
  have hupper := normalized_weighted_log_radius_le_log_sum C k
  rw [normalized_weighted_log_radius_eq_div] at hupper
  have hQ := residualQuadraticMass_pos C
  have hscaled := (div_le_iff₀ hQ).1 hupper
  rw [residualQuadraticMass_eq_one_sub_offDiagonalMass] at hscaled
  exact hlower.trans (by simpa [mul_comm] using! hscaled)

theorem residual_radius_log_calibration
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 0 ≤ k) (hlocation : Function.Injective C.location)
    (hε : 0 < residualMeanDeficit C) :
    Real.log 3 - k * Real.log 2 -
        residualOffDiagonalMass C *
          Real.log (6 * residualMeanDeficit C /
            residualOffDiagonalMass C) ≤
      (1 - residualOffDiagonalMass C) *
        Real.log (3 * residualRadiusSum C k) := by
  have hbase := residual_radius_log_calibration_base C hk hlocation hε
  have hS := residualRadiusSum_pos C k
  have hlogS : Real.log (3 * residualRadiusSum C k) =
      Real.log 3 + Real.log (residualRadiusSum C k) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hS.ne']
  rcases (residualOffDiagonalMass_nonneg C).eq_or_lt with ht | ht
  · have ht' : residualOffDiagonalMass C = 0 := ht.symm
    rw [ht'] at hbase ⊢
    simp only [zero_mul, div_zero, Real.log_zero, sub_zero, one_mul]
    rw [hlogS]
    linarith
  · have hratio : 0 < 2 * residualMeanDeficit C /
        residualOffDiagonalMass C := by positivity
    have hsix :
        Real.log (6 * residualMeanDeficit C /
            residualOffDiagonalMass C) =
          Real.log 3 +
            Real.log (2 * residualMeanDeficit C /
              residualOffDiagonalMass C) := by
      have heq : 6 * residualMeanDeficit C /
            residualOffDiagonalMass C =
          3 * (2 * residualMeanDeficit C /
            residualOffDiagonalMass C) := by ring
      rw [heq, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hratio.ne']
    rw [hsix, hlogS]
    nlinarith

theorem residualRadiusSum_gt_one_third
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 29 / 20)
    (hlocation : Function.Injective C.location)
    (hε : 0 < residualMeanDeficit C)
    (hεmax : residualMeanDeficit C < 1 / 25) :
    1 / 3 < residualRadiusSum C k := by
  apply radius_sum_gt_one_third_of_calibration
    (k := k) (ε := residualMeanDeficit C)
    (t := residualOffDiagonalMass C)
  · rw [← residualQuadraticMass_eq_one_sub_offDiagonalMass]
    exact residualQuadraticMass_pos C
  · exact residualRadiusSum_pos C k
  · exact hk
  · exact hε
  · exact hεmax
  · exact residualOffDiagonalMass_nonneg C
  · exact residual_radius_log_calibration C hk0 hlocation hε

theorem two_lt_sqrt_two_add_twice_residualRadiusSum
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 29 / 20)
    (hlocation : Function.Injective C.location)
    (hε : 0 < residualMeanDeficit C)
    (hεmax : residualMeanDeficit C < 1 / 25) :
    2 < Real.sqrt 2 + 2 * residualRadiusSum C k :=
  sqrt_two_add_twice_gt_two
    (residualRadiusSum_gt_one_third C hk0 hk hlocation hε hεmax)

lemma weighted_residual_distance_eq
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) (b : ℝ) :
    ∑ i, C.weight i * (C.location i - b) =
      2 - residualMeanDeficit C - b := by
  rw [residualMeanDeficit]
  have hexpand (i : ι) :
      C.weight i * (C.location i - b) =
        2 * C.weight i - C.weight i * (2 - C.location i) -
          b * C.weight i := by ring
  simp_rw [hexpand]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, C.sum_weight]
  ring

lemma residual_log_jensen_at_separation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {b : ℝ} (hb : ∀ i, b < C.location i) :
    (∑ i, C.weight i * Real.log (C.location i - b)) ≤
      Real.log (2 - residualMeanDeficit C - b) := by
  have hjensen :
      (∑ i, C.weight i * Real.log (C.location i - b)) ≤
        Real.log (∑ i, C.weight i * (C.location i - b)) := by
    simpa only [smul_eq_mul, Function.comp_apply] using!
      (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
        (t := (Finset.univ : Finset ι))
        (w := C.weight)
        (p := fun i ↦ C.location i - b)
        (fun i hi ↦ (C.weight_pos i).le)
        C.sum_weight
        (fun i hi ↦ sub_pos.mpr (hb i))
  rw [weighted_residual_distance_eq] at hjensen
  exact hjensen

lemma residualPotential_at_separation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hb0 : 0 < b) (hb : ∀ i, b < C.location i) :
    residualPotential C k b =
      k * Real.log b +
        ∑ i, C.weight i * Real.log (C.location i - b) := by
  rw [residualPotential, abs_of_pos hb0]
  apply congrArg (fun z ↦ k * Real.log b + z)
  apply Finset.sum_congr rfl
  intro i hi
  rw [abs_of_neg (by linarith [hb i])]
  congr 2
  ring

lemma separationPoint_log_bound
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hsep : IsResidualSeparationPoint C k b) :
    0 ≤ k * Real.log b +
      Real.log (2 - residualMeanDeficit C - b) := by
  rcases hsep with ⟨hb0, hb, hpotential⟩
  rw [residualPotential_at_separation C hb0 hb] at hpotential
  have hjensen := residual_log_jensen_at_separation C hb
  linarith

lemma weighted_residual_distance_pos
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {b : ℝ} (hb : ∀ i, b < C.location i) :
    0 < 2 - residualMeanDeficit C - b := by
  rw [← weighted_residual_distance_eq]
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (C.weight_pos i) (sub_pos.mpr (hb i))
  · exact residual_index_univ_nonempty C

theorem one_le_separationPoint
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hk : 1 ≤ k)
    (hsep : IsResidualSeparationPoint C k b) : 1 ≤ b := by
  rcases hsep with ⟨hb0, hb, hpotential⟩
  have hlogbound := separationPoint_log_bound C ⟨hb0, hb, hpotential⟩
  have hε0 := residualMeanDeficit_nonneg C
  have havgpos := weighted_residual_distance_pos C hb
  have htwob : 0 < 2 - b := by linarith
  apply le_of_not_gt
  intro hb1
  have hlogb : Real.log b < 0 := Real.log_neg hb0 hb1
  have hklog : k * Real.log b ≤ Real.log b := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hk) hlogb.le]
  have hlogmono :
      Real.log (2 - residualMeanDeficit C - b) ≤ Real.log (2 - b) :=
    Real.strictMonoOn_log.monotoneOn havgpos htwob (by linarith)
  have hprodpos : 0 < b * (2 - b) := mul_pos hb0 htwob
  have hprodlt : b * (2 - b) < 1 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hb1)]
  have hlogprod : Real.log (b * (2 - b)) < 0 :=
    Real.log_neg hprodpos hprodlt
  have hadd : Real.log b + Real.log (2 - b) =
      Real.log (b * (2 - b)) := by
    rw [Real.log_mul hb0.ne' htwob.ne']
  linarith

theorem meanDeficit_le_endpoint_expression
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hsep : IsResidualSeparationPoint C k b) :
    residualMeanDeficit C ≤ 2 - b - b ^ (-k) := by
  rcases hsep with ⟨hb0, hb, hpotential⟩
  have hlogbound := separationPoint_log_bound C ⟨hb0, hb, hpotential⟩
  have havgpos := weighted_residual_distance_pos C hb
  have hexp :
      Real.exp (-k * Real.log b) ≤
        Real.exp (Real.log (2 - residualMeanDeficit C - b)) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [Real.exp_log havgpos] at hexp
  have hrpow : Real.exp (-k * Real.log b) = b ^ (-k) := by
    rw [Real.rpow_def_of_pos hb0]
    congr 1
    ring
  rw [hrpow] at hexp
  linarith

theorem endpoint_rpow_minimum {K b : ℝ} (hK : 0 < K) (hb : 0 < b) :
    (K + 1) * K ^ (-K / (K + 1)) ≤ b + b ^ (-K) := by
  have hK1 : 0 < K + 1 := by linarith
  let w₁ : ℝ := K / (K + 1)
  let w₂ : ℝ := 1 / (K + 1)
  let p₁ : ℝ := (K + 1) / K * b
  let p₂ : ℝ := (K + 1) * b ^ (-K)
  have hw₁ : 0 ≤ w₁ := by dsimp [w₁]; positivity
  have hw₂ : 0 ≤ w₂ := by dsimp [w₂]; positivity
  have hp₁ : 0 < p₁ := by dsimp [p₁]; positivity
  have hp₂ : 0 < p₂ := by dsimp [p₂]; positivity
  have hw : w₁ + w₂ = 1 := by
    dsimp [w₁, w₂]
    field_simp [hK1.ne']
  have hamgm : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
    Real.geom_mean_le_arith_mean2_weighted
      hw₁ hw₂ hp₁.le hp₂.le hw
  have harith : w₁ * p₁ + w₂ * p₂ = b + b ^ (-K) := by
    dsimp [w₁, w₂, p₁, p₂]
    field_simp [hK.ne', hK1.ne']
  have hgeom :
      p₁ ^ w₁ * p₂ ^ w₂ =
        (K + 1) * K ^ (-K / (K + 1)) := by
    apply Real.log_injOn_pos
    · exact mul_pos (Real.rpow_pos_of_pos hp₁ _) (Real.rpow_pos_of_pos hp₂ _)
    · exact mul_pos hK1 (Real.rpow_pos_of_pos hK _)
    rw [Real.log_mul (Real.rpow_pos_of_pos hp₁ _).ne'
        (Real.rpow_pos_of_pos hp₂ _).ne',
      Real.log_rpow hp₁, Real.log_rpow hp₂,
      Real.log_mul hK1.ne' (Real.rpow_pos_of_pos hK _).ne',
      Real.log_rpow hK]
    have hp₁log : Real.log p₁ =
        Real.log (K + 1) - Real.log K + Real.log b := by
      dsimp [p₁]
      rw [Real.log_mul (div_pos hK1 hK).ne' hb.ne',
        Real.log_div hK1.ne' hK.ne']
    have hp₂log : Real.log p₂ =
        Real.log (K + 1) + (-K) * Real.log b := by
      dsimp [p₂]
      rw [Real.log_mul hK1.ne' (Real.rpow_pos_of_pos hb _).ne',
        Real.log_rpow hb]
    rw [hp₁log, hp₂log]
    dsimp [w₁, w₂]
    field_simp [hK1.ne']
    ring
  rw [hgeom, harith] at hamgm
  exact hamgm

theorem meanDeficit_lt_one_div_twenty_five_of_separation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hk1 : 1 ≤ k) (hkK : k ≤ 29 / 20)
    (hsep : IsResidualSeparationPoint C k b) :
    residualMeanDeficit C < 1 / 25 := by
  have hb0 := hsep.1
  have hb1 := one_le_separationPoint C hk1 hsep
  have hdeficit := meanDeficit_le_endpoint_expression C hsep
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hpow : b ^ (-(29 / 20 : ℝ)) ≤ b ^ (-k) := by
    rw [Real.rpow_def_of_pos hb0, Real.rpow_def_of_pos hb0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hminimum := endpoint_rpow_minimum
    (K := (29 / 20 : ℝ)) (b := b) (by norm_num) hb0
  norm_num at hminimum
  have hcertificate := lowK_endpoint_deficit_lt_one_div_25
  nlinarith

lemma location_eq_two_of_meanDeficit_eq_zero
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (hε : residualMeanDeficit C = 0) (i : ι) :
    C.location i = 2 := by
  have hsum :
      ∑ i, C.weight i * (2 - C.location i) = 0 := by
    simpa [residualMeanDeficit] using! hε
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj ↦ mul_nonneg (C.weight_pos j).le
      (by linarith [(C.location_mem j).2]))).1 hsum
  have hi := hall i (Finset.mem_univ i)
  have hw := C.weight_pos i
  nlinarith

theorem residualRadiusSum_gt_one_third_of_meanDeficit_eq_zero
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : k ≤ 29 / 20)
    (hlocation : Function.Injective C.location)
    (hε : residualMeanDeficit C = 0) :
    1 / 3 < residualRadiusSum C k := by
  classical
  let i : ι := Classical.choose (residual_index_univ_nonempty C)
  letI : Unique ι :=
    { default := i
      uniq := fun j ↦ hlocation (by
        rw [location_eq_two_of_meanDeficit_eq_zero C hε j,
          location_eq_two_of_meanDeficit_eq_zero C hε i]) }
  have hweight : C.weight (default : ι) = 1 := by
    have hsum := C.sum_weight
    simpa only [Fintype.sum_unique] using! hsum
  have hlocationTwo : C.location (default : ι) = 2 :=
    location_eq_two_of_meanDeficit_eq_zero C hε default
  have hradius : residualRadiusSum C k = Real.exp (-k * Real.log 2) := by
    rw [residualRadiusSum, Fintype.sum_unique, residualRadius,
      residualBackgroundAt]
    simp [hweight, hlocationTwo, Subsingleton.elim]
  have hmargin := lowK_log_margin hk
  have hexp : Real.exp (-Real.log 3) < Real.exp (-k * Real.log 2) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have hthree : Real.exp (-Real.log 3) = (1 / 3 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  rw [hthree] at hexp
  simpa [hradius] using! hexp

theorem residualRadiusSum_gt_one_third_of_separation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hk1 : 1 ≤ k) (hkK : k ≤ 29 / 20)
    (hlocation : Function.Injective C.location)
    (hsep : IsResidualSeparationPoint C k b) :
    1 / 3 < residualRadiusSum C k := by
  rcases (residualMeanDeficit_nonneg C).eq_or_lt with hε | hε
  · exact residualRadiusSum_gt_one_third_of_meanDeficit_eq_zero
      C hkK hlocation hε.symm
  · exact residualRadiusSum_gt_one_third C (by linarith) hkK
      hlocation hε
      (meanDeficit_lt_one_div_twenty_five_of_separation C hk1 hkK hsep)

theorem two_lt_sqrt_two_add_twice_residualRadiusSum_of_separation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k b : ℝ} (hk1 : 1 ≤ k) (hkK : k ≤ 29 / 20)
    (hlocation : Function.Injective C.location)
    (hsep : IsResidualSeparationPoint C k b) :
    2 < Real.sqrt 2 + 2 * residualRadiusSum C k :=
  sqrt_two_add_twice_gt_two
    (residualRadiusSum_gt_one_third_of_separation
      C hk1 hkK hlocation hsep)

end

end Erdos1038

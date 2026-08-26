import ErdosProblems.Erdos421.ReciprocalDifferences

/-! # Increment spacing for logarithmic differences of arbitrary order -/

namespace Erdos421

theorem hasDerivAt_iteratedLogDifference (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDifference hs Real.log) (reciprocalDifference 0 hs x) x := by
  have h := hasDerivAt_iteratedDifference Real.log (fun y ↦ 1 / y)
    (fun y hy ↦ by simpa only [one_div] using Real.hasDerivAt_log hy.ne') hs hhs hx
  simpa only [reciprocalDifference, Nat.zero_add, pow_one] using h

theorem iteratedLogDifference_bounds (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x a : ℝ} (hx : 0 < x) (ha : 0 ≤ a) :
    a * differenceCoefficient 0 hs / (x + a + hs.sum) ^ (hs.length + 1) ≤
        iteratedDifference hs Real.log (x + a) - iteratedDifference hs Real.log x ∧
      iteratedDifference hs Real.log (x + a) - iteratedDifference hs Real.log x ≤
        a * differenceCoefficient 0 hs / x ^ (hs.length + 1) := by
  by_cases ha0 : a = 0
  · subst a
    simp
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hderiv := fun y hy ↦ hasDerivAt_iteratedLogDifference hs hhs (x := y) hy
  have hcont : ContinuousOn (iteratedDifference hs Real.log) (Set.Icc x (x + a)) := by
    intro y hy
    exact (hderiv y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hval⟩ := exists_hasDerivAt_eq_slope (iteratedDifference hs Real.log)
    (reciprocalDifference 0 hs) (show x < x + a by linarith) hcont
    (fun y hy ↦ hderiv y (hx.trans hy.1))
  have hcp : 0 < c := hx.trans hc.1
  have hb := reciprocalDifference_bounds 0 hs hhs hcp
  simp only [Nat.zero_add, Nat.add_comm 1 hs.length] at hb
  rw [add_sub_cancel_left] at hval
  have heq := (eq_div_iff hap.ne').mp hval
  have hvalue : iteratedDifference hs Real.log (x + a) - iteratedDifference hs Real.log x =
      a * reciprocalDifference 0 hs c := by nlinarith
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hcoef := differenceCoefficient_nonneg 0 hs hhs
  rw [hvalue]
  constructor
  · calc
      _ = a * (differenceCoefficient 0 hs / (x + a + hs.sum) ^ (hs.length + 1)) := by ring
      _ ≤ a * (differenceCoefficient 0 hs / (c + hs.sum) ^ (hs.length + 1)) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact div_le_div_of_nonneg_left hcoef (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith [hc.2]) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb.1 ha
  · calc
      _ ≤ a * (differenceCoefficient 0 hs / c ^ (hs.length + 1)) :=
        mul_le_mul_of_nonneg_left hb.2 ha
      _ ≤ a * (differenceCoefficient 0 hs / x ^ (hs.length + 1)) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact div_le_div_of_nonneg_left hcoef (by positivity)
          (pow_le_pow_left₀ hx.le hc.1.le _)
      _ = _ := by ring

noncomputable def iteratedLogIncrement (hs : List ℝ) (x : ℝ) : ℝ :=
  iteratedDifference hs Real.log (x + 1) - iteratedDifference hs Real.log x

theorem iteratedLogIncrement_bounds (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x : ℝ} (hx : 0 < x) :
    differenceCoefficient 0 hs / (x + 1 + hs.sum) ^ (hs.length + 1) ≤
        iteratedLogIncrement hs x ∧
      iteratedLogIncrement hs x ≤ differenceCoefficient 0 hs / x ^ (hs.length + 1) := by
  simpa only [one_mul, iteratedLogIncrement] using
    iteratedLogDifference_bounds hs hhs hx (by norm_num : (0 : ℝ) ≤ 1)

theorem iteratedLogIncrement_nonneg (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x : ℝ} (hx : 0 < x) : 0 ≤ iteratedLogIncrement hs x := by
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hcoef := differenceCoefficient_nonneg 0 hs hhs
  exact (by positivity : 0 ≤ differenceCoefficient 0 hs / (x + 1 + hs.sum) ^ (hs.length + 1)).trans
    (iteratedLogIncrement_bounds hs hhs hx).1

theorem iteratedLogIncrement_drop_lower (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) * differenceCoefficient 0 (1 :: hs) / (y + 1 + hs.sum) ^ (hs.length + 2) ≤
      iteratedLogIncrement hs x - iteratedLogIncrement hs y := by
  have hlist : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · norm_num
    · exact hhs h hh
  have hb := iteratedLogDifference_bounds (1 :: hs) hlist hx (sub_nonneg.mpr hxy)
  have hxs : x + (y - x) = y := by ring
  rw [hxs] at hb
  have heq : iteratedDifference (1 :: hs) Real.log y - iteratedDifference (1 :: hs) Real.log x =
      iteratedLogIncrement hs x - iteratedLogIncrement hs y := by
    simp only [iteratedDifference, iteratedLogIncrement]
    ring
  rw [heq] at hb
  simpa only [List.sum_cons, List.length_cons, add_assoc] using hb.1

theorem iteratedLogIncrement_antitone (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    iteratedLogIncrement hs y ≤ iteratedLogIncrement hs x := by
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hcoef : 0 ≤ differenceCoefficient 0 (1 :: hs) := by
    rw [differenceCoefficient_cons]
    have hc := differenceCoefficient_nonneg 1 hs hhs
    positivity
  have hy := hx.trans_le hxy
  have hnum := sub_nonneg.mpr hxy
  have hlo := iteratedLogIncrement_drop_lower hs hhs hx hxy
  have hnonneg : 0 ≤ (y - x) * differenceCoefficient 0 (1 :: hs) /
      (y + 1 + hs.sum) ^ (hs.length + 2) := by positivity
  linarith

theorem iteratedLogIncrement_drop_lower_bounded (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x y B : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyB : y + 1 + hs.sum ≤ B) :
    (y - x) * differenceCoefficient 0 (1 :: hs) / B ^ (hs.length + 2) ≤
      iteratedLogIncrement hs x - iteratedLogIncrement hs y := by
  have hy := hx.trans_le hxy
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hcoef : 0 ≤ differenceCoefficient 0 (1 :: hs) := by
    rw [differenceCoefficient_cons]
    have hc := differenceCoefficient_nonneg 1 hs hhs
    positivity
  have hnum : 0 ≤ (y - x) * differenceCoefficient 0 (1 :: hs) := by positivity
  exact (div_le_div_of_nonneg_left hnum (by positivity)
    (pow_le_pow_left₀ (by positivity) hyB _)).trans
      (iteratedLogIncrement_drop_lower hs hhs hx hxy)

end Erdos421

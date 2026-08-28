import Wikipedia.HopfProblem.QuaternionCoordinatePowerHomotopy

/-!
# The two coordinate powers compose to quaternion power

Swapping the two complex coordinates is multiplication on the left by
`i` and on the right by `-k`, so it is homotopic to the identity through
nonzero quaternions. Conjugating the first-coordinate homotopy therefore
handles the second coordinate. Composition multiplies the exponents.
-/

noncomputable section

open scoped Topology Quaternion unitInterval

namespace Wikipedia.HopfProblem.QuaternionCoordinatePowers

open UnitQuaternionSphere

theorem unit_ne_zero (q : UnitQuaternions) : (q : ℍ) ≠ 0 := by
  intro h
  have hn := (mem_unitary_iff_norm_eq_one q.val).mp q.property
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

def imaginaryI : UnitQuaternions := ⟨pair Complex.I 0, by
  have h : Quaternion.normSq (pair Complex.I 0) = 1 := by
    rw [Quaternion.normSq_def']
    norm_num [pair]
  exact ⟨by rw [Quaternion.star_mul_self, h, Quaternion.coe_one],
    by rw [Quaternion.self_mul_star, h, Quaternion.coe_one]⟩⟩

def negativeK : UnitQuaternions := ⟨pair 0 (-Complex.I), by
  have h : Quaternion.normSq (pair 0 (-Complex.I)) = 1 := by
    rw [Quaternion.normSq_def']
    norm_num [pair]
  exact ⟨by rw [Quaternion.star_mul_self, h, Quaternion.coe_one],
    by rw [Quaternion.self_mul_star, h, Quaternion.coe_one]⟩⟩

theorem swap_formula (q : ℍ) :
    pair (second q) (first q) = (imaginaryI : ℍ) * q * (negativeK : ℍ) := by
  symm
  apply QuaternionAlgebra.ext
  all_goals
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
    norm_num [imaginaryI, negativeK, pair, first, second]

theorem swap_ne_zero (q : Punctured) : pair (second q.val) (first q.val) ≠ 0 := by
  rw [swap_formula]
  exact mul_ne_zero (mul_ne_zero (unit_ne_zero imaginaryI) q.property) (unit_ne_zero negativeK)

def swap : C(Punctured, Punctured) where
  toFun q := ⟨pair (second q.val) (first q.val), swap_ne_zero q⟩
  continuous_toFun := (pair_continuous.comp
    ((second_continuous.comp continuous_subtype_val).prodMk
      (first_continuous.comp continuous_subtype_val))).subtype_mk swap_ne_zero

theorem swap_swap (q : Punctured) : swap (swap q) = q := by
  apply Subtype.ext
  rfl

def swapHomotopy : swap.Homotopy (ContinuousMap.id Punctured) := by
  let p : Path imaginaryI (1 : UnitQuaternions) :=
    (PathConnectedSpace.joined imaginaryI 1).somePath
  let r : Path negativeK (1 : UnitQuaternions) :=
    (PathConnectedSpace.joined negativeK 1).somePath
  exact {
    toFun := fun tq => ⟨(p tq.1 : ℍ) * tq.2.val * (r tq.1 : ℍ),
      mul_ne_zero (mul_ne_zero (unit_ne_zero _) tq.2.property) (unit_ne_zero _)⟩
    continuous_toFun := (((continuous_subtype_val.comp p.continuous).comp continuous_fst |>.mul
      (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_subtype_val.comp r.continuous).comp continuous_fst)).subtype_mk _
    map_zero_left := fun q => Subtype.ext (by
      change (p 0 : ℍ) * q.val * (r 0 : ℍ) = pair (second q.val) (first q.val)
      rw [p.source, r.source]
      exact (swap_formula q.val).symm)
    map_one_left := fun q => Subtype.ext (by simp)
  }

theorem swap_homotopic : swap.Homotopic (ContinuousMap.id Punctured) := ⟨swapHomotopy⟩

def secondPower (n : ℕ) : C(Punctured, Punctured) := swap.comp ((firstPower n).comp swap)

theorem secondPower_val (n : ℕ) (q : Punctured) :
    (secondPower n q).val = pair (first q.val) (second q.val ^ n) := rfl

theorem secondPower_homotopic (n : ℕ) : (secondPower n).Homotopic (quaternionPower n) := by
  unfold secondPower
  have h := swap_homotopic.comp ((firstPower_homotopic n).comp swap_homotopic)
  simpa only [ContinuousMap.id_comp, ContinuousMap.comp_id] using h

def coordinatePower (m n : ℕ) : C(Punctured, Punctured) := (firstPower m).comp (secondPower n)

theorem coordinatePower_val (m n : ℕ) (q : Punctured) :
    (coordinatePower m n q).val = pair (first q.val ^ m) (second q.val ^ n) := rfl

theorem quaternionPower_comp (m n : ℕ) :
    (quaternionPower m).comp (quaternionPower n) = quaternionPower (n * m) := by
  apply ContinuousMap.ext
  intro q
  exact Subtype.ext (pow_mul q.val n m).symm

/-- The full comparison uses actual homotopies and no degree input. -/
theorem coordinatePower_homotopic (m n : ℕ) :
    (coordinatePower m n).Homotopic (quaternionPower (n * m)) := by
  have h := (firstPower_homotopic m).comp (secondPower_homotopic n)
  rw [quaternionPower_comp] at h
  exact h

end Wikipedia.HopfProblem.QuaternionCoordinatePowers

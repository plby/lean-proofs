import Wikipedia.HopfProblem.QuaternionCoordinatePowers

/-!
# An explicit homotopy from one complex coordinate power to quaternion power

Write `q = z + w j` and `q^n = Z + B w j`, where `B` is real.
Interpolate the first coordinate linearly and use transverse multiplier
`(1-t) + t B + i t(1-t)`. For interior times its imaginary part is
nonzero. On `w = 0`, both endpoints have first coordinate `z^n`.
Thus this homotopy never meets zero; no degree theorem is assumed.
-/

noncomputable section

open scoped Topology Quaternion unitInterval

namespace Wikipedia.HopfProblem.QuaternionCoordinatePowers

def multiplier (n : ℕ) (t : ℝ) (q : ℍ) : ℂ :=
  ((1 - t + t * powerCoefficient n q : ℝ) : ℂ) +
    ((t * (1 - t) : ℝ) : ℂ) * Complex.I

theorem multiplier_im (n : ℕ) (t : ℝ) (q : ℍ) :
    (multiplier n t q).im = t * (1 - t) := by simp [multiplier]

def homotopyPoint (n : ℕ) (t : ℝ) (q : ℍ) : ℍ :=
  pair ((1 - (t : ℂ)) * first q ^ n + (t : ℂ) * first (q ^ n))
    (multiplier n t q * second q)

theorem homotopyPoint_zero (n : ℕ) (q : ℍ) :
    homotopyPoint n 0 q = pair (first q ^ n) (second q) := by
  simp [homotopyPoint, multiplier]

theorem homotopyPoint_one (n : ℕ) (q : ℍ) : homotopyPoint n 1 q = q ^ n := by
  simp only [homotopyPoint, multiplier, Complex.ofReal_one, sub_self, zero_mul, mul_zero,
    add_zero, zero_add, one_mul, Complex.ofReal_zero]
  rw [← second_pow, pair_coordinates]

theorem homotopyPoint_ne_zero (n : ℕ) (t : ℝ) (q : ℍ) (hq : q ≠ 0) :
    homotopyPoint n t q ≠ 0 := by
  by_cases ht0 : t = 0
  · subst t
    rw [homotopyPoint_zero]
    exact (firstPower n ⟨q, hq⟩).property
  by_cases ht1 : t = 1
  · subst t
    rw [homotopyPoint_one]
    exact pow_ne_zero n hq
  intro hz
  obtain ⟨hfirst, hsecond⟩ := (pair_eq_zero_iff _ _).mp hz
  have hm : multiplier n t q ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    rw [multiplier_im, Complex.zero_im] at hi
    exact (mul_ne_zero ht0 (sub_ne_zero.mpr (fun h => ht1 h.symm))) hi
  have hs : second q = 0 := (mul_eq_zero.mp hsecond).resolve_left hm
  rw [first_pow_of_second_zero n q hs] at hfirst
  have hf : first q ^ n = 0 := by
    calc
      first q ^ n = (1 - (t : ℂ)) * first q ^ n + (t : ℂ) * first q ^ n := by ring
      _ = 0 := hfirst
  rcases coordinates_ne_zero ⟨q, hq⟩ with hn | hn
  · exact (pow_ne_zero n hn) hf
  · exact hn hs

theorem multiplier_continuous (n : ℕ) : Continuous (fun p : ℝ × ℍ => multiplier n p.1 p.2) := by
  exact (Complex.continuous_ofReal.comp
    ((continuous_const.sub continuous_fst).add
      (continuous_fst.mul ((powerCoefficient_continuous n).comp continuous_snd)))).add
    ((Complex.continuous_ofReal.comp
      (continuous_fst.mul (continuous_const.sub continuous_fst))).mul_const Complex.I)

theorem homotopyPoint_continuous (n : ℕ) :
    Continuous (fun p : ℝ × ℍ => homotopyPoint n p.1 p.2) := by
  have ht : Continuous (fun p : ℝ × ℍ => (p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_fst
  exact pair_continuous.comp
    ((((continuous_const.sub ht).mul ((first_continuous.comp continuous_snd).pow n)).add
      (ht.mul (first_continuous.comp (continuous_snd.pow n)))).prodMk
      ((multiplier_continuous n).mul (second_continuous.comp continuous_snd)))

/-- A genuine homotopy in the punctured quaternion space. -/
def firstPowerHomotopy (n : ℕ) : (firstPower n).Homotopy (quaternionPower n) where
  toFun p := ⟨homotopyPoint n (p.1 : ℝ) p.2.val,
    homotopyPoint_ne_zero n _ _ p.2.property⟩
  continuous_toFun := ((homotopyPoint_continuous n).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left q := Subtype.ext (homotopyPoint_zero n q.val)
  map_one_left q := Subtype.ext (homotopyPoint_one n q.val)

theorem firstPower_homotopic (n : ℕ) : (firstPower n).Homotopic (quaternionPower n) :=
  ⟨firstPowerHomotopy n⟩

end Wikipedia.HopfProblem.QuaternionCoordinatePowers

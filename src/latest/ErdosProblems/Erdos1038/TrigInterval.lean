import ErdosProblems.Erdos1038.RationalInterval

/-!
# Kernel-checked trigonometric interval enclosures

The high-ratio scalar certificate needs thousands of evaluations of `sin`
and `cos`.  Floating-point balls are useful for discovering the boxes, but
they are not proof objects.  This file provides a small exact checker over
`RatInterval`.

The input is first divided by `2^n`.  On the resulting interval inside
`[-1,1]`, mathlib's proved cubic/quadratic bounds for sine and cosine give
rational seed enclosures.  The exact double-angle identities then recover
the original argument.  Consequently every successful finite certificate
can be reduced by the kernel to rational arithmetic.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

open RatInterval

namespace RatInterval

/-- A rational upper bound for the absolute value of every point of `I`. -/
def maxAbs (I : RatInterval) : Rat := max |I.lo| |I.hi|

/-- Symmetrically enlarge an interval by a rational error radius. -/
def inflate (I : RatInterval) (e : Rat) : RatInterval :=
  ⟨I.lo - e, I.hi + e⟩

theorem abs_le_maxAbs {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.maxAbs : ℝ) := by
  rw [abs_le]
  constructor
  · have hlo : -((|I.lo| : Rat) : ℝ) ≤ (I.lo : ℝ) := by
      norm_num only [Rat.cast_abs]
      exact neg_abs_le (I.lo : ℝ)
    have hmax : ((|I.lo| : Rat) : ℝ) ≤ (I.maxAbs : ℝ) := by
      exact_mod_cast le_max_left |I.lo| |I.hi|
    linarith [hx.1]
  · have hhi : (I.hi : ℝ) ≤ ((|I.hi| : Rat) : ℝ) := by
      norm_num only [Rat.cast_abs]
      exact le_abs_self (I.hi : ℝ)
    have hmax : ((|I.hi| : Rat) : ℝ) ≤ (I.maxAbs : ℝ) := by
      exact_mod_cast le_max_right |I.lo| |I.hi|
    linarith [hx.2]

theorem maxAbs_nonneg (I : RatInterval) : 0 ≤ I.maxAbs := by
  exact (abs_nonneg I.lo).trans (le_max_left |I.lo| |I.hi|)

theorem inflate_ordered {I : RatInterval} {e : Rat}
    (hI : I.Ordered) (he : 0 ≤ e) : (I.inflate e).Ordered := by
  change I.lo - e ≤ I.hi + e
  change I.lo ≤ I.hi at hI
  linarith

theorem inflate_contains_of_abs_sub_le {I : RatInterval} {e : Rat}
    {x y : ℝ} (hy : I.Contains y) (he : |x - y| ≤ (e : ℝ)) :
    (I.inflate e).Contains x := by
  have hbounds := (abs_le.mp he)
  unfold inflate Contains
  norm_num only [Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [hy.1, hy.2, hbounds.1, hbounds.2]

/-- The rational error in mathlib's seed estimates for sine and cosine. -/
def trigSeedError (I : RatInterval) : Rat :=
  I.maxAbs ^ 4 * (5 / 96)

def sinSeedPolynomial (I : RatInterval) : RatInterval :=
  I.sub ((I.mul I).mul I |>.mul (point (1 / 6)))

def cosSeedPolynomial (I : RatInterval) : RatInterval :=
  (point 1).sub ((I.mul I).mul (point (1 / 2)))

/-- Seed enclosure, valid whenever `maxAbs I ≤ 1`. -/
def sinSeed (I : RatInterval) : RatInterval :=
  (sinSeedPolynomial I).inflate (trigSeedError I)

/-- Seed enclosure, valid whenever `maxAbs I ≤ 1`. -/
def cosSeed (I : RatInterval) : RatInterval :=
  (cosSeedPolynomial I).inflate (trigSeedError I)

theorem trigSeedError_nonneg (I : RatInterval) : 0 ≤ trigSeedError I := by
  unfold trigSeedError
  positivity

theorem sinSeedPolynomial_ordered {I : RatInterval} (hI : I.Ordered) :
    (sinSeedPolynomial I).Ordered := by
  unfold sinSeedPolynomial
  exact sub_ordered hI
    (mul_ordered (mul_ordered (mul_ordered hI hI) hI)
      (point_ordered (1 / 6)))

theorem cosSeedPolynomial_ordered {I : RatInterval} (hI : I.Ordered) :
    (cosSeedPolynomial I).Ordered := by
  unfold cosSeedPolynomial
  exact sub_ordered (point_ordered 1)
    (mul_ordered (mul_ordered hI hI) (point_ordered (1 / 2)))

theorem sinSeed_ordered {I : RatInterval} (hI : I.Ordered) :
    (sinSeed I).Ordered :=
  inflate_ordered (sinSeedPolynomial_ordered hI) (trigSeedError_nonneg I)

theorem cosSeed_ordered {I : RatInterval} (hI : I.Ordered) :
    (cosSeed I).Ordered :=
  inflate_ordered (cosSeedPolynomial_ordered hI) (trigSeedError_nonneg I)

theorem sinSeedPolynomial_contains {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) :
    (sinSeedPolynomial I).Contains (x - x ^ 3 / 6) := by
  have hx2 : (I.mul I).Contains (x * x) := mul_contains hx hx
  have hx3 : ((I.mul I).mul I).Contains ((x * x) * x) := mul_contains hx2 hx
  have hscale := mul_contains hx3 (point_contains (1 / 6 : Rat))
  have hsub := sub_contains hx hscale
  convert! hsub using 1
  norm_num
  ring

theorem cosSeedPolynomial_contains {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) :
    (cosSeedPolynomial I).Contains (1 - x ^ 2 / 2) := by
  have hx2 : (I.mul I).Contains (x * x) := mul_contains hx hx
  have hscale := mul_contains hx2 (point_contains (1 / 2 : Rat))
  have hsub := sub_contains (point_contains (1 : Rat)) hscale
  convert! hsub using 1
  norm_num
  ring

theorem sinSeed_contains {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (hunit : I.maxAbs ≤ 1) :
    (sinSeed I).Contains (Real.sin x) := by
  have habs : |x| ≤ 1 := by
    exact (abs_le_maxAbs hx).trans (by exact_mod_cast hunit)
  have hbound := Real.sin_bound habs
  have hmax0 : (0 : ℝ) ≤ (I.maxAbs : ℝ) := by
    exact_mod_cast maxAbs_nonneg I
  have habs0 : 0 ≤ |x| := abs_nonneg x
  have hpow : |x| ^ 4 ≤ (I.maxAbs : ℝ) ^ 4 :=
    pow_le_pow_left₀ habs0 (abs_le_maxAbs hx) 4
  have herr :
      |Real.sin x - (x - x ^ 3 / 6)| ≤ (trigSeedError I : ℝ) := by
    unfold trigSeedError
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
      Rat.cast_ofNat]
    have hpow5 : |x| ^ 5 ≤ |x| ^ 4 := by
      calc
        |x| ^ 5 = |x| ^ 4 * |x| := by ring
        _ ≤ |x| ^ 4 * 1 := mul_le_mul_of_nonneg_left habs (by positivity)
        _ = |x| ^ 4 := mul_one _
    nlinarith [pow_nonneg habs0 4]
  exact inflate_contains_of_abs_sub_le (sinSeedPolynomial_contains hx) herr

theorem cosSeed_contains {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (hunit : I.maxAbs ≤ 1) :
    (cosSeed I).Contains (Real.cos x) := by
  have habs : |x| ≤ 1 := by
    exact (abs_le_maxAbs hx).trans (by exact_mod_cast hunit)
  have hbound := Real.cos_bound habs
  have habs0 : 0 ≤ |x| := abs_nonneg x
  have hpow : |x| ^ 4 ≤ (I.maxAbs : ℝ) ^ 4 :=
    pow_le_pow_left₀ habs0 (abs_le_maxAbs hx) 4
  have herr :
      |Real.cos x - (1 - x ^ 2 / 2)| ≤ (trigSeedError I : ℝ) := by
    unfold trigSeedError
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
      Rat.cast_ofNat]
    exact hbound.trans (mul_le_mul_of_nonneg_right hpow (by norm_num))
  exact inflate_contains_of_abs_sub_le (cosSeedPolynomial_contains hx) herr

/-- A simultaneous enclosure is substantially sharper under repeated
double-angle reconstruction than evaluating sine and cosine independently. -/
structure SinCosBox where
  sin : RatInterval
  cos : RatInterval
deriving DecidableEq, Repr

def SinCosBox.Ordered (B : SinCosBox) : Prop :=
  B.sin.Ordered ∧ B.cos.Ordered

def SinCosBox.Contains (B : SinCosBox) (x : ℝ) : Prop :=
  B.sin.Contains (Real.sin x) ∧ B.cos.Contains (Real.cos x)

def trigSeed (I : RatInterval) : SinCosBox :=
  ⟨sinSeed I, cosSeed I⟩

def doubleAngle (B : SinCosBox) : SinCosBox :=
  ⟨(point 2 |>.mul (B.sin.mul B.cos)),
    (point 2 |>.mul (B.cos.mul B.cos)).sub (point 1)⟩

def iterateDouble : Nat → SinCosBox → SinCosBox
  | 0, B => B
  | n + 1, B => doubleAngle (iterateDouble n B)

theorem trigSeed_ordered {I : RatInterval} (hI : I.Ordered) :
    (trigSeed I).Ordered := ⟨sinSeed_ordered hI, cosSeed_ordered hI⟩

theorem trigSeed_contains {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (hunit : I.maxAbs ≤ 1) :
    (trigSeed I).Contains x :=
  ⟨sinSeed_contains hx hunit, cosSeed_contains hx hunit⟩

theorem doubleAngle_ordered {B : SinCosBox} (hB : B.Ordered) :
    (doubleAngle B).Ordered := by
  constructor
  · exact mul_ordered (point_ordered 2) (mul_ordered hB.1 hB.2)
  · exact sub_ordered
      (mul_ordered (point_ordered 2) (mul_ordered hB.2 hB.2))
      (point_ordered 1)

theorem doubleAngle_contains {B : SinCosBox} {x : ℝ}
    (hB : B.Contains x) : (doubleAngle B).Contains (2 * x) := by
  constructor
  · have hmul := mul_contains hB.1 hB.2
    have htwo := mul_contains (point_contains (2 : Rat)) hmul
    change ((point 2).mul (B.sin.mul B.cos)).Contains (Real.sin (2 * x))
    rw [Real.sin_two_mul]
    convert! htwo using 1
    ring
  · have hsq := mul_contains hB.2 hB.2
    have htwo := mul_contains (point_contains (2 : Rat)) hsq
    have hsub := sub_contains htwo (point_contains (1 : Rat))
    change (((point 2).mul (B.cos.mul B.cos)).sub (point 1)).Contains
      (Real.cos (2 * x))
    rw [Real.cos_two_mul, pow_two]
    convert! hsub using 1
    norm_num

theorem iterateDouble_ordered (n : Nat) {B : SinCosBox} (hB : B.Ordered) :
    (iterateDouble n B).Ordered := by
  induction n with
  | zero => exact hB
  | succ n ih => exact doubleAngle_ordered ih

theorem iterateDouble_contains (n : Nat) {B : SinCosBox} {x : ℝ}
    (hB : B.Contains x) :
    (iterateDouble n B).Contains ((2 : ℝ) ^ n * x) := by
  induction n with
  | zero => simpa using! hB
  | succ n ih =>
      have hdouble := doubleAngle_contains ih
      convert! hdouble using 1
      rw [pow_succ]
      ring

/-- Divide an interval by the exact positive integer `2^n`. -/
def scaleDownPowTwo (n : Nat) (I : RatInterval) : RatInterval :=
  (point (1 / (2 : Rat) ^ n)).mul I

/-- Final simultaneous sine/cosine enclosure.  For the high-`k`
certificate we use `n = 12`, making the seed error microscopic while all
subsequent work remains exact rational interval arithmetic. -/
def sinCosBox (n : Nat) (I : RatInterval) : SinCosBox :=
  iterateDouble n (trigSeed (scaleDownPowTwo n I))

theorem scaleDownPowTwo_ordered (n : Nat) {I : RatInterval}
    (hI : I.Ordered) : (scaleDownPowTwo n I).Ordered :=
  mul_ordered (point_ordered _) hI

theorem scaleDownPowTwo_contains (n : Nat) {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) :
    (scaleDownPowTwo n I).Contains (x / (2 : ℝ) ^ n) := by
  have hmul := mul_contains (point_contains (1 / (2 : Rat) ^ n)) hx
  convert! hmul using 1
  norm_num
  field_simp

theorem sinCosBox_ordered (n : Nat) {I : RatInterval} (hI : I.Ordered) :
    (sinCosBox n I).Ordered :=
  iterateDouble_ordered n (trigSeed_ordered (scaleDownPowTwo_ordered n hI))

theorem sinCosBox_contains (n : Nat) {I : RatInterval} {x : ℝ}
    (hx : I.Contains x)
    (hunit : (scaleDownPowTwo n I).maxAbs ≤ 1) :
    (sinCosBox n I).Contains x := by
  have hscaled := scaleDownPowTwo_contains n hx
  have hseed := trigSeed_contains hscaled hunit
  have hresult := iterateDouble_contains n hseed
  convert! hresult using 1
  field_simp [show (2 : ℝ) ^ n ≠ 0 by positivity]

end RatInterval

end

end Erdos1038

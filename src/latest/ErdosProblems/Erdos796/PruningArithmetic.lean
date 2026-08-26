import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary arithmetic for the pruning step

The structural pruning argument repeatedly crosses a size threshold by
multiplying prime factors.  Here the same idea is expressed through the
least divisor above the threshold.  A prime factor of that least divisor
shows that it overshoots by at most one smoothness bound.
-/

namespace Erdos796

namespace PruningArithmetic

/-- `t` is `Y`-smooth when every prime divisor of `t` is at most `Y`.
This convention includes `1`. -/
def YSmooth (Y t : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ t → p ≤ Y

/-- The same predicate with the parameter named `Z`, for the two scales in
the pruning argument. -/
def ZSmooth (Z t : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ t → p ≤ Z

theorem zSmooth_iff_ySmooth {Z t : ℕ} :
    ZSmooth Z t ↔ YSmooth Z t := Iff.rfl

/-- Smoothness passes to divisors. -/
theorem YSmooth.of_dvd {Y a b : ℕ} (hb : YSmooth Y b) (hab : a ∣ b) :
    YSmooth Y a := by
  intro p hp hpa
  exact hb p hp (hpa.trans hab)

/-- `Z`-smoothness passes to divisors. -/
theorem ZSmooth.of_dvd {Z a b : ℕ} (hb : ZSmooth Z b) (hab : a ∣ b) :
    ZSmooth Z a := by
  intro p hp hpa
  exact hb p hp (hpa.trans hab)

/-- Least-divisor form of the minimal-subproduct argument.  If a
`Z`-smooth integer exceeds `Y`, it has a divisor which first crosses `Y`,
and that divisor is at most `Y Z`. -/
theorem exists_divisor_gt_le_mul_of_smooth
    {Y Z t : ℕ} (hY : 1 ≤ Y) (ht : Y < t) (hsmooth : ZSmooth Z t) :
    ∃ d : ℕ, d ∣ t ∧ Y < d ∧ d ≤ Y * Z := by
  let P : ℕ → Prop := fun d => d ∣ t ∧ Y < d
  have hex : ∃ d : ℕ, P d := ⟨t, dvd_rfl, ht⟩
  let d := Nat.find hex
  have hdP : P d := Nat.find_spec hex
  have hddiv : d ∣ t := hdP.1
  have hYd : Y < d := hdP.2
  have hdpos : 0 < d := lt_of_lt_of_le (by omega : 0 < Y) hYd.le
  have hdneone : d ≠ 1 := by omega
  obtain ⟨p, hpprime, hpd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hdneone
  have hpt : p ∣ t := hpd.trans hddiv
  have hpZ : p ≤ Z := hsmooth p hpprime hpt
  have hquotDvdD : d / p ∣ d := by
    exact ⟨p, (Nat.div_mul_cancel hpd).symm⟩
  have hquotDvdT : d / p ∣ t := hquotDvdD.trans hddiv
  have hquotLt : d / p < d := Nat.div_lt_self hdpos hpprime.one_lt
  have hminimal : ¬P (d / p) := Nat.find_min hex hquotLt
  have hquotLe : d / p ≤ Y := by
    by_contra h
    exact hminimal ⟨hquotDvdT, Nat.lt_of_not_ge h⟩
  refine ⟨d, hddiv, hYd, ?_⟩
  calc
    d = (d / p) * p := (Nat.div_mul_cancel hpd).symm
    _ ≤ Y * Z := Nat.mul_le_mul hquotLe hpZ

/-- The threshold form used for a `Z`-smooth cofactor in the manuscript. -/
theorem exists_divisor_between_Y_and_YZ
    {Y Z t : ℕ} (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hsmooth : ZSmooth Z t) (ht : Y ^ 4 ≤ t) :
    ∃ d : ℕ, d ∣ t ∧ Y < d ∧ d ≤ Y * Z := by
  have hY : 2 ≤ Y := hZ.trans hZY
  have hYltPow : Y < Y ^ 4 := by
    simpa only [pow_one] using!
      (Nat.pow_lt_pow_right (by omega : 1 < Y) (by norm_num : 1 < 4))
  exact exists_divisor_gt_le_mul_of_smooth (by omega)
    (hYltPow.trans_le ht) hsmooth

/-- A factorization into three factors, each strictly above `Y`. -/
def HasThreeLargeFactors (Y t : ℕ) : Prop :=
  ∃ a b c : ℕ, Y < a ∧ Y < b ∧ Y < c ∧ t = a * b * c

/-- If `q > Y` and a `Z`-smooth `t` reaches `Y⁴`, the controlled divisor
gives the three large factors `q`, `d`, and `t/d`. -/
theorem three_large_factors_of_large_prime_and_zSmooth
    {Y Z q t : ℕ} (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hq : Y < q) (hsmooth : ZSmooth Z t) (ht : Y ^ 4 ≤ t) :
    HasThreeLargeFactors Y (q * t) := by
  obtain ⟨d, hdt, hYd, hdYZ⟩ :=
    exists_divisor_between_Y_and_YZ hZ hZY hsmooth ht
  have hY : 2 ≤ Y := hZ.trans hZY
  have hdY2 : d ≤ Y ^ 2 := by
    calc
      d ≤ Y * Z := hdYZ
      _ ≤ Y * Y := Nat.mul_le_mul_left Y hZY
      _ = Y ^ 2 := by ring
  have htEq : t = d * (t / d) := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hdt]
  have hquot : Y < t / d := by
    by_contra h
    have hquotLe : t / d ≤ Y := Nat.le_of_not_gt h
    have htLe : t ≤ Y ^ 3 := by
      rw [htEq]
      calc
        d * (t / d) ≤ Y ^ 2 * Y := Nat.mul_le_mul hdY2 hquotLe
        _ = Y ^ 3 := by ring
    have hpow : Y ^ 3 < Y ^ 4 :=
      Nat.pow_lt_pow_right (by omega : 1 < Y) (by norm_num)
    exact (Nat.not_lt_of_ge (ht.trans htLe)) hpow
  exact ⟨q, d, t / d, hq, hYd, hquot, by
    exact (congrArg (fun x => q * x) htEq).trans (by ring)⟩

/-- A `Y`-smooth integer larger than `Y⁶` has three factors larger than
`Y`.  This is the greedy two-extraction argument from the manuscript. -/
theorem three_large_factors_of_ySmooth_gt_pow_six
    {Y t : ℕ} (hY : 2 ≤ Y) (hsmooth : YSmooth Y t)
    (ht : Y ^ 6 < t) : HasThreeLargeFactors Y t := by
  have hsmoothZ : ZSmooth Y t := hsmooth
  have hYt : Y < t := by
    have hpow : Y < Y ^ 6 := by
      simpa only [pow_one] using!
        (Nat.pow_lt_pow_right (by omega : 1 < Y) (by norm_num : 1 < 6))
    exact hpow.trans ht
  obtain ⟨d₁, hd₁t, hYd₁, hd₁Y⟩ :=
    exists_divisor_gt_le_mul_of_smooth (by omega) hYt hsmoothZ
  have hd₁Y2 : d₁ ≤ Y ^ 2 := by simpa [pow_two] using! hd₁Y
  let t₁ := t / d₁
  have htEq : t = d₁ * t₁ := by
    dsimp [t₁]
    rw [Nat.mul_comm, Nat.div_mul_cancel hd₁t]
  have ht₁gt : Y ^ 4 < t₁ := by
    by_contra h
    have ht₁le : t₁ ≤ Y ^ 4 := Nat.le_of_not_gt h
    have htle : t ≤ Y ^ 6 := by
      rw [htEq]
      calc
        d₁ * t₁ ≤ Y ^ 2 * Y ^ 4 := Nat.mul_le_mul hd₁Y2 ht₁le
        _ = Y ^ 6 := by ring
    exact (Nat.not_lt_of_ge htle) ht
  have ht₁dvd : t₁ ∣ t := by
    exact ⟨d₁, by simpa [Nat.mul_comm] using! htEq⟩
  have ht₁smooth : ZSmooth Y t₁ := hsmoothZ.of_dvd ht₁dvd
  obtain ⟨d₂, hd₂t₁, hYd₂, hd₂Y⟩ :=
    exists_divisor_gt_le_mul_of_smooth (by omega)
      ((show Y < Y ^ 4 by
        simpa only [pow_one] using!
          (Nat.pow_lt_pow_right (by omega : 1 < Y) (by norm_num : 1 < 4))).trans
        ht₁gt) ht₁smooth
  have hd₂Y2 : d₂ ≤ Y ^ 2 := by simpa [pow_two] using! hd₂Y
  let d₃ := t₁ / d₂
  have ht₁Eq : t₁ = d₂ * d₃ := by
    dsimp [d₃]
    rw [Nat.mul_comm, Nat.div_mul_cancel hd₂t₁]
  have hYd₃ : Y < d₃ := by
    by_contra h
    have hd₃le : d₃ ≤ Y := Nat.le_of_not_gt h
    have ht₁le : t₁ ≤ Y ^ 3 := by
      rw [ht₁Eq]
      calc
        d₂ * d₃ ≤ Y ^ 2 * Y := Nat.mul_le_mul hd₂Y2 hd₃le
        _ = Y ^ 3 := by ring
    have hpow : Y ^ 3 < Y ^ 4 :=
      Nat.pow_lt_pow_right (by omega : 1 < Y) (by norm_num)
    exact (Nat.not_lt_of_ge hpow.le) (ht₁gt.trans_le ht₁le)
  exact ⟨d₁, d₂, d₃, hYd₁, hYd₂, hYd₃, by
    rw [htEq, ht₁Eq]
    ring⟩

/-- Contrapositive form used in pruning: a `Y`-smooth integer with no
factorization into three factors above `Y` is at most `Y⁶`. -/
theorem ySmooth_le_pow_six_of_no_three_large_factors
    {Y t : ℕ} (hY : 2 ≤ Y) (hsmooth : YSmooth Y t)
    (hno : ¬HasThreeLargeFactors Y t) :
    t ≤ Y ^ 6 := by
  by_contra h
  exact hno (three_large_factors_of_ySmooth_gt_pow_six hY hsmooth
    (Nat.lt_of_not_ge h))

end PruningArithmetic

end Erdos796

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.KloostermanMultiplicativity
import ErdosProblems.Erdos387.RationalStepanovExtensionSum

/-!
# A prime-modulus Kloosterman bound from the rational Weil theorem

The Möbius substitution x = t / (t+1) changes a*x + b/x into the
constant a+b plus the two-simple-pole phase b/t - a/(t+1).  This brings
the prime Kloosterman sum under the already checked rational Weil estimate.
-/

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

noncomputable def mobiusForward
    {p : ℕ} [NeZero p] (t : ZMod p) : ZMod p :=
  t * (t + 1)⁻¹

noncomputable def mobiusInverse
    {p : ℕ} [NeZero p] (x : ZMod p) : ZMod p :=
  x * (1 - x)⁻¹

theorem mobiusForward_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] {t : ZMod p}
    (ht0 : t ≠ 0) (ht1 : t ≠ -1) :
    mobiusForward t ≠ 0 := by
  unfold mobiusForward
  exact mul_ne_zero ht0 (inv_ne_zero (by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)))

theorem mobiusForward_ne_one
    {p : ℕ} [NeZero p] [Fact p.Prime] {t : ZMod p}
    (ht1 : t ≠ -1) :
    mobiusForward t ≠ 1 := by
  have hden : t + 1 ≠ 0 := by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)
  unfold mobiusForward
  intro h
  field_simp [hden] at h
  have hone : (1 : ZMod p) = 0 := by
    simpa using congrArg (fun z : ZMod p => z - t) h.symm
  exact one_ne_zero hone

theorem mobiusInverse_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] {x : ZMod p}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    mobiusInverse x ≠ 0 := by
  unfold mobiusInverse
  exact mul_ne_zero hx0 (inv_ne_zero (sub_ne_zero.mpr hx1.symm))

theorem mobiusInverse_ne_neg_one
    {p : ℕ} [NeZero p] [Fact p.Prime] {x : ZMod p}
    (hx1 : x ≠ 1) :
    mobiusInverse x ≠ -1 := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  unfold mobiusInverse
  intro h
  field_simp [hden] at h
  have hneg : -x = 1 - x := by
    simpa using congrArg Neg.neg h
  have hone : (1 : ZMod p) = 0 := by
    calc
      1 = (1 - x) + x := by ring
      _ = -x + x := by rw [← hneg]
      _ = 0 := neg_add_cancel x
  exact one_ne_zero hone

theorem mobiusInverse_forward
    {p : ℕ} [NeZero p] [Fact p.Prime] {t : ZMod p}
    (ht1 : t ≠ -1) :
    mobiusInverse (mobiusForward t) = t := by
  have hden : t + 1 ≠ 0 := by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)
  unfold mobiusInverse mobiusForward
  field_simp [hden]
  ring

theorem mobiusForward_inverse
    {p : ℕ} [NeZero p] [Fact p.Prime] {x : ZMod p}
    (hx1 : x ≠ 1) :
    mobiusForward (mobiusInverse x) = x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  unfold mobiusInverse mobiusForward
  field_simp [hden]
  ring

/-- Coefficients of b/t - a/(t+1). -/
def twoPoleCoefficient
    {p : ℕ} [NeZero p] (a b r : ZMod p) : ZMod p :=
  if r = 0 then b else if r = -1 then -a else 0

theorem poleSupport_twoPoleCoefficient
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    InverseRational.poleSupport (twoPoleCoefficient a b) = {0, -1} := by
  classical
  ext r
  simp only [InverseRational.mem_poleSupport, Finset.mem_insert,
    Finset.mem_singleton]
  unfold twoPoleCoefficient
  by_cases hr0 : r = 0
  · simp [hr0, hb]
  · by_cases hr1 : r = -1
    · simp [hr1, ha]
    · simp [hr0, hr1]

theorem simplePolePhase_twoPoleCoefficient
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (t : ZMod p) :
    InverseRational.simplePolePhase (twoPoleCoefficient a b) t =
      b * t⁻¹ - a * (t + 1)⁻¹ := by
  rw [InverseRational.simplePolePhase_eq_sum_poleSupport,
    poleSupport_twoPoleCoefficient ha hb]
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  simp [twoPoleCoefficient, hneg]
  ring

theorem kloostermanPhase_mobiusForward
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b t : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ -1) :
    a * mobiusForward t + b * (mobiusForward t)⁻¹ =
      a + b + InverseRational.simplePolePhase
        (twoPoleCoefficient a b) t := by
  have hden : t + 1 ≠ 0 := by
    intro h
    exact ht1 (add_eq_zero_iff_eq_neg.mp h)
  rw [simplePolePhase_twoPoleCoefficient ha hb]
  unfold mobiusForward
  field_simp [ht0, hden]
  ring

noncomputable def mobiusDomain
    (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun t => t ≠ 0 ∧ t ≠ -1

noncomputable def mobiusCodomain
    (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun x => x ≠ 0 ∧ x ≠ 1

theorem sum_mobiusForward
    {p : ℕ} [NeZero p] [Fact p.Prime] (f : ZMod p → ℂ) :
    (∑ t ∈ mobiusDomain p, f (mobiusForward t)) =
      ∑ x ∈ mobiusCodomain p, f x := by
  classical
  apply Finset.sum_bij (fun t _ht => mobiusForward t)
  · intro t ht
    rw [mobiusDomain, Finset.mem_filter] at ht
    rw [mobiusCodomain, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, mobiusForward_ne_zero ht.2.1 ht.2.2,
      mobiusForward_ne_one ht.2.2⟩
  · intro t ht u hu htu
    rw [mobiusDomain, Finset.mem_filter] at ht hu
    have h := congrArg mobiusInverse htu
    simpa [mobiusInverse_forward ht.2.2,
      mobiusInverse_forward hu.2.2] using h
  · intro x hx
    rw [mobiusCodomain, Finset.mem_filter] at hx
    refine ⟨mobiusInverse x, ?_, ?_⟩
    · rw [mobiusDomain, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, mobiusInverse_ne_zero hx.2.1 hx.2.2,
        mobiusInverse_ne_neg_one hx.2.2⟩
    · exact mobiusForward_inverse hx.2.2
  · intro t ht
    rfl

/-- The zero-extended two-pole sum is the same sum over the Möbius domain. -/
theorem zeroExtendedTwoPoleSum_eq_domain
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport (twoPoleCoefficient a b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase (twoPoleCoefficient a b) t)) =
      ∑ t ∈ mobiusDomain p,
        ZMod.stdAddChar
          (InverseRational.simplePolePhase (twoPoleCoefficient a b) t) := by
  classical
  rw [poleSupport_twoPoleCoefficient ha hb]
  rw [mobiusDomain, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases ht0 : t = 0 <;> by_cases ht1 : t = -1 <;>
    simp [ht0, ht1]

/-- Remove the distinguished unit one from the complete zero-extended
Kloosterman sum. -/
theorem sum_eq_one_add_codomain
    {p : ℕ} [NeZero p] [Fact p.Prime] (a b : ZMod p) :
    sum p a b =
      ZMod.stdAddChar (a + b) +
        ∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹) := by
  classical
  rw [sum_eq_inverse_phase]
  let U := (Finset.univ : Finset (ZMod p)).filter IsUnit
  have hUone : (1 : ZMod p) ∈ U := by simp [U]
  calc
    (∑ x : ZMod p,
        if IsUnit x then ZMod.stdAddChar (a * x + b * x⁻¹) else 0) =
      ∑ x ∈ U, ZMod.stdAddChar (a * x + b * x⁻¹) := by
        rw [Finset.sum_filter]
    _ = ZMod.stdAddChar (a + b) +
        ∑ x ∈ U.erase 1, ZMod.stdAddChar (a * x + b * x⁻¹) := by
      rw [← Finset.add_sum_erase U
        (fun x => ZMod.stdAddChar (a * x + b * x⁻¹)) hUone]
      simp
    _ = ZMod.stdAddChar (a + b) +
        ∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹) := by
      congr 1
      apply Finset.sum_congr
      · ext x
        simp [U, mobiusCodomain, isUnit_iff_ne_zero, and_comm]
      · intro x hx
        rfl

/-- Exact Möbius-transform identity relating a prime Kloosterman sum to one
zero-extended two-pole rational sum. -/
theorem sum_eq_const_mul_one_add_twoPole
    {p : ℕ} [NeZero p] [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    sum p a b =
      ZMod.stdAddChar (a + b) *
        (1 + ∑ t : ZMod p,
          if t ∈ InverseRational.poleSupport
              (twoPoleCoefficient a b) then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase
              (twoPoleCoefficient a b) t)) := by
  rw [sum_eq_one_add_codomain]
  let R := ∑ t : ZMod p,
    if t ∈ InverseRational.poleSupport (twoPoleCoefficient a b) then 0
    else ZMod.stdAddChar
      (InverseRational.simplePolePhase (twoPoleCoefficient a b) t)
  have hcodomain :
      (∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹)) =
        ZMod.stdAddChar (a + b) * R := by
    calc
      (∑ x ∈ mobiusCodomain p,
          ZMod.stdAddChar (a * x + b * x⁻¹)) =
        ∑ t ∈ mobiusDomain p,
          ZMod.stdAddChar
            (a * mobiusForward t + b * (mobiusForward t)⁻¹) :=
          (sum_mobiusForward
            (fun x => ZMod.stdAddChar (a * x + b * x⁻¹))).symm
      _ = ∑ t ∈ mobiusDomain p,
          ZMod.stdAddChar
            (a + b + InverseRational.simplePolePhase
              (twoPoleCoefficient a b) t) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [mobiusDomain, Finset.mem_filter] at ht
        rw [kloostermanPhase_mobiusForward ha hb ht.2.1 ht.2.2]
      _ = ∑ t ∈ mobiusDomain p,
          ZMod.stdAddChar (a + b) *
            ZMod.stdAddChar
              (InverseRational.simplePolePhase
                (twoPoleCoefficient a b) t) := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [AddChar.map_add_eq_mul]
      _ = ZMod.stdAddChar (a + b) *
          ∑ t ∈ mobiusDomain p,
            ZMod.stdAddChar
              (InverseRational.simplePolePhase
                (twoPoleCoefficient a b) t) := by
        rw [Finset.mul_sum]
      _ = ZMod.stdAddChar (a + b) * R := by
        rw [← zeroExtendedTwoPoleSum_eq_domain ha hb]
  rw [hcodomain]
  ring

/-- Prime-field square-root bound obtained from the two-pole rational Weil
estimate.  The constant three is the conductor bound for two finite simple
poles; the final one is the point x=1 omitted by the Möbius chart. -/
theorem norm_sum_le_three_sqrt_add_one
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 2 < p)
    {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖sum p a b‖ ≤ 3 * Real.sqrt (p : ℝ) + 1 := by
  let coeff := twoPoleCoefficient a b
  let support := InverseRational.poleSupport coeff
  have hsupport : support = {0, -1} := by
    simpa only [support, coeff] using poleSupport_twoPoleCoefficient ha hb
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hnonempty : support.Nonempty := by
    rw [hsupport]
    simp
  have hcard : support.card < p := by
    rw [hsupport]
    simp
    omega
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hweil :
      ‖∑ t : ZMod p,
          if t ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff t)‖ ≤
        ((2 * support.card - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
    simpa only [support] using
      RationalStepanov.norm_zeroExtendedSimplePolePhase_sum_le
        hp1 coeff hnonempty hcard
  have hsupportCard : support.card = 2 := by
    rw [hsupport]
    simp
  have hweil' :
      ‖∑ t : ZMod p,
          if t ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff t)‖ ≤
        3 * Real.sqrt (p : ℝ) := by
    rw [hsupportCard] at hweil
    norm_num at hweil
    exact hweil
  rw [sum_eq_const_mul_one_add_twoPole ha hb, norm_mul,
    AddChar.norm_apply, one_mul]
  calc
    ‖1 + ∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport
            (twoPoleCoefficient a b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase
            (twoPoleCoefficient a b) t)‖ ≤
      1 + ‖∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport
            (twoPoleCoefficient a b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase
            (twoPoleCoefficient a b) t)‖ := by
        simpa using norm_add_le (1 : ℂ)
          (∑ t : ZMod p,
            if t ∈ InverseRational.poleSupport
                (twoPoleCoefficient a b) then 0
            else ZMod.stdAddChar
              (InverseRational.simplePolePhase
                (twoPoleCoefficient a b) t))
    _ ≤ 1 + 3 * Real.sqrt (p : ℝ) := by
      have hweil'' :
          ‖∑ t : ZMod p,
              if t ∈ InverseRational.poleSupport
                  (twoPoleCoefficient a b) then 0
              else ZMod.stdAddChar
                (InverseRational.simplePolePhase
                  (twoPoleCoefficient a b) t)‖ ≤
            3 * Real.sqrt (p : ℝ) := by
        simpa only [support, coeff] using hweil'
      exact add_le_add_right hweil'' 1
    _ = 3 * Real.sqrt (p : ℝ) + 1 := by ring

/-- Coefficients of the single-pole phase `b/t`. -/
def onePoleCoefficient
    {p : ℕ} [NeZero p] (b r : ZMod p) : ZMod p :=
  if r = 0 then b else 0

theorem poleSupport_onePoleCoefficient
    {p : ℕ} [NeZero p] [Fact p.Prime] {b : ZMod p} (hb : b ≠ 0) :
    InverseRational.poleSupport (onePoleCoefficient b) = {0} := by
  classical
  ext r
  simp only [InverseRational.mem_poleSupport, Finset.mem_singleton]
  unfold onePoleCoefficient
  by_cases hr : r = 0 <;> simp [hr, hb]

theorem simplePolePhase_onePoleCoefficient
    {p : ℕ} [NeZero p] [Fact p.Prime] {b : ZMod p}
    (hb : b ≠ 0) (t : ZMod p) :
    InverseRational.simplePolePhase (onePoleCoefficient b) t = b * t⁻¹ := by
  rw [InverseRational.simplePolePhase_eq_sum_poleSupport,
    poleSupport_onePoleCoefficient hb]
  simp [onePoleCoefficient]

theorem sum_zero_left_eq_onePole
    {p : ℕ} [NeZero p] [Fact p.Prime] {b : ZMod p} (hb : b ≠ 0) :
    sum p 0 b =
      ∑ t : ZMod p,
        if t ∈ InverseRational.poleSupport (onePoleCoefficient b) then 0
        else ZMod.stdAddChar
          (InverseRational.simplePolePhase (onePoleCoefficient b) t) := by
  classical
  rw [sum_eq_inverse_phase, poleSupport_onePoleCoefficient hb]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [simplePolePhase_onePoleCoefficient hb]
  by_cases ht0 : t = 0 <;> simp [ht0]

/-- The zero-linear-frequency prime Kloosterman sum is already a one-pole
rational sum, and hence has square-root cancellation. -/
theorem norm_sum_zero_left_le_sqrt
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 2 < p)
    {b : ZMod p} (hb : b ≠ 0) :
    ‖sum p 0 b‖ ≤ Real.sqrt (p : ℝ) := by
  let coeff := onePoleCoefficient b
  let support := InverseRational.poleSupport coeff
  have hsupport : support = {0} := by
    simpa only [support, coeff] using poleSupport_onePoleCoefficient hb
  have hnonempty : support.Nonempty := by rw [hsupport]; simp
  have hcard : support.card < p := by rw [hsupport]; simp; omega
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hweil :
      ‖∑ t : ZMod p,
          if t ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff t)‖ ≤
        ((2 * support.card - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
    simpa only [support] using
      RationalStepanov.norm_zeroExtendedSimplePolePhase_sum_le
        hp1 coeff hnonempty hcard
  rw [sum_zero_left_eq_onePole hb]
  have hsupportCard : support.card = 1 := by rw [hsupport]; simp
  have hweil' :
      ‖∑ t : ZMod p,
          if t ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff t)‖ ≤
        Real.sqrt (p : ℝ) := by
    rw [hsupportCard] at hweil
    norm_num at hweil
    exact hweil
  simpa only [support, coeff] using hweil'

/-- Trivial complete-sum bound by the number of residues. -/
theorem norm_sum_le_modulus
    (q : ℕ) [NeZero q] (a b : ZMod q) :
    ‖sum q a b‖ ≤ q := by
  rw [sum_eq_inverse_phase]
  calc
    ‖∑ v : ZMod q,
        if IsUnit v then ZMod.stdAddChar (a * v + b * v⁻¹) else 0‖ ≤
        ∑ v : ZMod q,
          ‖if IsUnit v then ZMod.stdAddChar (a * v + b * v⁻¹) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v : ZMod q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _hv
      by_cases hv : IsUnit v <;> simp [hv, AddChar.norm_apply]
    _ = q := by simp

/-- A uniform local factor suitable for CRT multiplication.  When the
inverse coefficient vanishes, the extra square root records the allowable
local gcd loss. -/
theorem norm_sum_le_four_sqrt_mul_ite
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 2 < p)
    (a b : ZMod p) :
    ‖sum p a b‖ ≤
      4 * Real.sqrt (p : ℝ) * (if b = 0 then Real.sqrt (p : ℝ) else 1) := by
  by_cases hb : b = 0
  · rw [if_pos hb]
    have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p := by
      rw [Real.mul_self_sqrt]
      positivity
    calc
      ‖sum p a b‖ ≤ p := norm_sum_le_modulus p a b
      _ ≤ 4 * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by
        rw [mul_assoc, hsqrt]
        have hpnonneg : (0 : ℝ) ≤ p := by positivity
        linarith
  · rw [if_neg hb]
    by_cases ha : a = 0
    · rw [ha, mul_one]
      exact (norm_sum_zero_left_le_sqrt hp hb).trans (by
        have hsqrt : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
        linarith)
    · rw [mul_one]
      have hprime := norm_sum_le_three_sqrt_add_one hp ha hb
      have hsqrtOne : 1 ≤ Real.sqrt (p : ℝ) := by
        exact (Real.one_le_sqrt).2 (by
          exact_mod_cast (show 1 ≤ p by omega))
      linarith

end Kloosterman

end Erdos387

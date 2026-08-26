import ErdosProblems.Erdos1002.GaussPrefixCylinderPartition
import ErdosProblems.Erdos1002.OscillatoryIntervalSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting finite continued-fraction cylinders by their terminal denominator

The oscillatory cylinder estimate in the marked-Poisson argument needs an
actual count of the possible deepest continued-fraction cylinders.  This
file supplies that count without assuming a cardinality estimate.

For a positive word `w = [a₁, ..., aₙ]`, `cfTerminalPair w = (p, q)` is the
reduced pair for the terminal endpoint `[0; a₁, ..., aₙ]`.  The recursion is
the inverse-branch recursion `(p, q) ↦ (q, a*q + p)`.  A reduced pair has at
most one positive expansion of each length parity; this records explicitly
the familiar two finite expansions of a rational.  Consequently the words
with terminal denominator at most `R` inject into
`Fin (R+1) × Fin (R+1) × Fin 2`, giving the deliberately coarse but uniform
bound `2 * (R+1)^2` used in the cylinder sum.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-! ## Terminal continuants -/

/-- Every digit of a finite regular continued-fraction word is positive. -/
def IsPositiveCFWord (w : List ℕ) : Prop :=
  ∀ q ∈ w, 0 < q

/-- Reduced numerator/denominator pair of the terminal endpoint
`[0; a₁, ..., aₙ]`. -/
def cfTerminalPair : List ℕ → ℕ × ℕ
  | [] => (0, 1)
  | a :: w =>
      let z := cfTerminalPair w
      (z.2, a * z.2 + z.1)

/-- Numerator of `cfTerminalPair`. -/
def cfTerminalNumerator (w : List ℕ) : ℕ :=
  (cfTerminalPair w).1

/-- Denominator of `cfTerminalPair`. -/
def cfTerminalDenominator (w : List ℕ) : ℕ :=
  (cfTerminalPair w).2

@[simp] theorem cfTerminalNumerator_nil :
    cfTerminalNumerator [] = 0 := rfl

@[simp] theorem cfTerminalDenominator_nil :
    cfTerminalDenominator [] = 1 := rfl

@[simp] theorem cfTerminalNumerator_cons (a : ℕ) (w : List ℕ) :
    cfTerminalNumerator (a :: w) = cfTerminalDenominator w := by
  simp [cfTerminalNumerator, cfTerminalDenominator, cfTerminalPair]

@[simp] theorem cfTerminalDenominator_cons (a : ℕ) (w : List ℕ) :
    cfTerminalDenominator (a :: w) =
      a * cfTerminalDenominator w + cfTerminalNumerator w := by
  simp [cfTerminalNumerator, cfTerminalDenominator, cfTerminalPair]

theorem cfTerminalDenominator_pos
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    0 < cfTerminalDenominator w := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha : 0 < a := hpos a (by simp)
      have htail : IsPositiveCFWord w := by
        intro q hq
        exact hpos q (by simp [hq])
      simp only [cfTerminalDenominator_cons]
      exact Nat.add_pos_left (Nat.mul_pos ha (ih htail)) _

theorem cfTerminalNumerator_le_denominator
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    cfTerminalNumerator w ≤ cfTerminalDenominator w := by
  cases w with
  | nil => simp
  | cons a w =>
      have ha : 1 ≤ a := hpos a (by simp)
      have hd : cfTerminalDenominator w ≤
          a * cfTerminalDenominator w := by
        simpa only [one_mul] using!
          Nat.mul_le_mul_right (cfTerminalDenominator w) ha
      simp only [cfTerminalNumerator_cons, cfTerminalDenominator_cons]
      exact hd.trans (Nat.le_add_right _ _)

theorem cfTerminalPair_coprime (w : List ℕ) :
    (cfTerminalNumerator w).Coprime (cfTerminalDenominator w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have h := (Nat.coprime_add_mul_left_left
        (cfTerminalNumerator w) (cfTerminalDenominator w) a).2 ih
      simpa only [cfTerminalNumerator_cons, cfTerminalDenominator_cons,
        Nat.add_comm, Nat.mul_comm] using! h.symm

theorem cfTerminalNumerator_eq_zero_iff
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    cfTerminalNumerator w = 0 ↔ w = [] := by
  cases w with
  | nil => simp
  | cons a w =>
      have htail : IsPositiveCFWord w := by
        intro q hq
        exact hpos q (by simp [hq])
      simp only [cfTerminalNumerator_cons]
      exact ⟨fun h ↦ (Nat.ne_of_gt
        (cfTerminalDenominator_pos htail)) h |>.elim, by simp⟩

theorem cfTerminalNumerator_eq_denominator_iff
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    cfTerminalNumerator w = cfTerminalDenominator w ↔ w = [1] := by
  cases w with
  | nil => simp
  | cons a w =>
      have ha : 1 ≤ a := hpos a (by simp)
      have htail : IsPositiveCFWord w := by
        intro q hq
        exact hpos q (by simp [hq])
      have hdpos : 0 < cfTerminalDenominator w :=
        cfTerminalDenominator_pos htail
      constructor
      · intro h
        simp only [cfTerminalNumerator_cons,
          cfTerminalDenominator_cons] at h
        have hdle : cfTerminalDenominator w ≤
            a * cfTerminalDenominator w := by
          simpa only [one_mul] using!
            Nat.mul_le_mul_right (cfTerminalDenominator w) ha
        have hmul : a * cfTerminalDenominator w =
            cfTerminalDenominator w := by omega
        have hnum : cfTerminalNumerator w = 0 := by omega
        have haone : a = 1 := by
          apply Nat.mul_right_cancel hdpos
          simpa only [one_mul] using! hmul
        have hw : w = [] :=
          (cfTerminalNumerator_eq_zero_iff htail).1 hnum
        simp [haone, hw]
      · intro h
        rcases List.cons.inj h with ⟨rfl, rfl⟩
        simp

/-! ## The reduced rational endpoint and its two possible expansions -/

/-- The inverse-branch endpoint is exactly the terminal continuant ratio. -/
theorem gaussInverseWord_zero_eq_cfTerminalRatio
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    gaussInverseWord w 0 =
      (cfTerminalNumerator w : ℝ) / cfTerminalDenominator w := by
  induction w with
  | nil => simp [gaussInverseWord]
  | cons a w ih =>
      have htail : IsPositiveCFWord w := by
        intro q hq
        exact hpos q (by simp [hq])
      have hdpos : 0 < cfTerminalDenominator w :=
        cfTerminalDenominator_pos htail
      have hnewpos : 0 < cfTerminalDenominator (a :: w) :=
        cfTerminalDenominator_pos hpos
      simp only [gaussInverseWord, gaussInverseBranch, ih htail,
        cfTerminalNumerator_cons, cfTerminalDenominator_cons]
      field_simp [Nat.ne_of_gt hdpos, Nat.ne_of_gt hnewpos]
      push_cast
      rfl

/-- The endpoint is represented by a positive denominator, a numerator no
larger than it, and a coprime pair. -/
theorem gaussInverseWord_zero_reduced_endpoint
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    gaussInverseWord w 0 =
        (cfTerminalNumerator w : ℝ) / cfTerminalDenominator w ∧
      0 < cfTerminalDenominator w ∧
      cfTerminalNumerator w ≤ cfTerminalDenominator w ∧
      (cfTerminalNumerator w).Coprime (cfTerminalDenominator w) :=
  ⟨gaussInverseWord_zero_eq_cfTerminalRatio hpos,
    cfTerminalDenominator_pos hpos,
    cfTerminalNumerator_le_denominator hpos,
    cfTerminalPair_coprime w⟩

/-- Equality of two positive-word endpoints is equality of their reduced
terminal pairs. -/
theorem cfTerminalPair_eq_of_gaussInverseWord_zero_eq
    {w v : List ℕ} (hw : IsPositiveCFWord w) (hv : IsPositiveCFWord v)
    (hend : gaussInverseWord w 0 = gaussInverseWord v 0) :
    cfTerminalPair w = cfTerminalPair v := by
  let p := cfTerminalNumerator w
  let q := cfTerminalDenominator w
  let r := cfTerminalNumerator v
  let s := cfTerminalDenominator v
  have hqpos : 0 < q := cfTerminalDenominator_pos hw
  have hspos : 0 < s := cfTerminalDenominator_pos hv
  have hratio : (p : ℝ) / q = (r : ℝ) / s := by
    rw [← gaussInverseWord_zero_eq_cfTerminalRatio hw,
      ← gaussInverseWord_zero_eq_cfTerminalRatio hv]
    exact hend
  have hcrossR : (p : ℝ) * s = (r : ℝ) * q :=
    (div_eq_div_iff (by exact_mod_cast hqpos.ne')
      (by exact_mod_cast hspos.ne')).1 hratio
  have hcross : p * s = r * q := by exact_mod_cast hcrossR
  have hpq : p.Coprime q := cfTerminalPair_coprime w
  have hrs : r.Coprime s := cfTerminalPair_coprime v
  have hq_dvd_s : q ∣ s := by
    apply (hpq.symm.dvd_mul_left).1
    rw [hcross]
    exact ⟨r, by simp [Nat.mul_comm]⟩
  have hs_dvd_q : s ∣ q := by
    apply (hrs.symm.dvd_mul_left).1
    rw [← hcross]
    exact ⟨p, by simp [Nat.mul_comm]⟩
  have hqs : q = s := Nat.dvd_antisymm hq_dvd_s hs_dvd_q
  have hpr : p = r := by
    apply Nat.mul_right_cancel hqpos
    simpa [hqs] using! hcross
  apply Prod.ext <;> simpa [p, q, r, s,
    cfTerminalNumerator, cfTerminalDenominator]

/-- A reduced terminal pair has at most one positive expansion of each
length parity.  The parity tag is precisely what separates the two standard
finite expansions of a rational endpoint. -/
theorem eq_of_cfTerminalPair_eq_of_length_mod_two_eq
    {w v : List ℕ} (hw : IsPositiveCFWord w) (hv : IsPositiveCFWord v)
    (hpair : cfTerminalPair w = cfTerminalPair v)
    (hparity : w.length % 2 = v.length % 2) :
    w = v := by
  induction w generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons b v =>
          have htail : IsPositiveCFWord v := by
            intro q hq
            exact hv q (by simp [hq])
          have hdpos := cfTerminalDenominator_pos htail
          have hfirst : 0 = cfTerminalDenominator v := by
            have := congrArg Prod.fst hpair
            simpa [cfTerminalPair, cfTerminalNumerator,
              cfTerminalDenominator] using! this
          omega
  | cons a w ih =>
      cases v with
      | nil =>
          have htail : IsPositiveCFWord w := by
            intro q hq
            exact hw q (by simp [hq])
          have hdpos := cfTerminalDenominator_pos htail
          have hfirst : cfTerminalDenominator w = 0 := by
            have := congrArg Prod.fst hpair
            simpa [cfTerminalPair, cfTerminalNumerator,
              cfTerminalDenominator] using! this
          omega
      | cons b v =>
          have ha : 0 < a := hw a (by simp)
          have hb : 0 < b := hv b (by simp)
          have hwtail : IsPositiveCFWord w := by
            intro q hq
            exact hw q (by simp [hq])
          have hvtail : IsPositiveCFWord v := by
            intro q hq
            exact hv q (by simp [hq])
          have hdwpos := cfTerminalDenominator_pos hwtail
          have hdvpos := cfTerminalDenominator_pos hvtail
          have hden : cfTerminalDenominator w =
              cfTerminalDenominator v := by
            have := congrArg Prod.fst hpair
            simpa [cfTerminalPair, cfTerminalNumerator,
              cfTerminalDenominator] using! this
          have hsecond :
              a * cfTerminalDenominator w + cfTerminalNumerator w =
                b * cfTerminalDenominator v + cfTerminalNumerator v := by
            have := congrArg Prod.snd hpair
            simpa [cfTerminalPair, cfTerminalNumerator,
              cfTerminalDenominator] using! this
          rcases lt_trichotomy a b with hab | hab | hab
          · have hmul : a * cfTerminalDenominator w +
                cfTerminalDenominator w ≤
                b * cfTerminalDenominator v := by
              rw [hden]
              simpa [Nat.add_mul] using!
                Nat.mul_le_mul_right (cfTerminalDenominator v)
                  (Nat.succ_le_of_lt hab)
            have hnumwle := cfTerminalNumerator_le_denominator hwtail
            have hnumw : cfTerminalNumerator w =
                cfTerminalDenominator w := by omega
            have hnumv : cfTerminalNumerator v = 0 := by omega
            have hwone :=
              (cfTerminalNumerator_eq_denominator_iff hwtail).1 hnumw
            have hvnil :=
              (cfTerminalNumerator_eq_zero_iff hvtail).1 hnumv
            subst w
            subst v
            simp at hparity
          · subst b
            have hnum : cfTerminalNumerator w =
                cfTerminalNumerator v := by
              rw [hden] at hsecond
              exact Nat.add_left_cancel hsecond
            have htailpair : cfTerminalPair w = cfTerminalPair v := by
              apply Prod.ext
              · simpa [cfTerminalNumerator] using! hnum
              · simpa [cfTerminalDenominator] using! hden
            have htailparity : w.length % 2 = v.length % 2 := by
              simp only [List.length_cons] at hparity
              omega
            have := ih hwtail hvtail htailpair htailparity
            simp [this]
          · have hmul : b * cfTerminalDenominator v +
                cfTerminalDenominator v ≤
                a * cfTerminalDenominator w := by
              rw [← hden]
              simpa [Nat.add_mul] using!
                Nat.mul_le_mul_right (cfTerminalDenominator w)
                  (Nat.succ_le_of_lt hab)
            have hnumvle := cfTerminalNumerator_le_denominator hvtail
            have hnumv : cfTerminalNumerator v =
                cfTerminalDenominator v := by omega
            have hnumw : cfTerminalNumerator w = 0 := by omega
            have hvone :=
              (cfTerminalNumerator_eq_denominator_iff hvtail).1 hnumv
            have hwnil :=
              (cfTerminalNumerator_eq_zero_iff hwtail).1 hnumw
            subst w
            subst v
            simp at hparity

/-- Endpoint version of the preceding theorem. -/
theorem eq_of_gaussInverseWord_zero_eq_of_length_mod_two_eq
    {w v : List ℕ} (hw : IsPositiveCFWord w) (hv : IsPositiveCFWord v)
    (hend : gaussInverseWord w 0 = gaussInverseWord v 0)
    (hparity : w.length % 2 = v.length % 2) :
    w = v :=
  eq_of_cfTerminalPair_eq_of_length_mod_two_eq hw hv
    (cfTerminalPair_eq_of_gaussInverseWord_zero_eq hw hv hend) hparity

/-! ## A finite type of denominator-bounded cylinders -/

/-- Nonempty positive words whose terminal denominator is at most `R`. -/
def BoundedPositiveTerminalWord (R : ℕ) :=
  {w : List ℕ // w ≠ [] ∧ IsPositiveCFWord w ∧
    cfTerminalDenominator w ≤ R}

/-- Explicit finite code: reduced numerator, denominator, and expansion
parity. -/
def boundedPositiveTerminalWordCode (R : ℕ) :
    BoundedPositiveTerminalWord R →
      Fin (R + 1) × Fin (R + 1) × Fin 2 := fun w ↦
  (⟨cfTerminalNumerator w.1,
      lt_of_le_of_lt
        (cfTerminalNumerator_le_denominator w.2.2.1)
        (Nat.lt_succ_of_le w.2.2.2)⟩,
    ⟨cfTerminalDenominator w.1, Nat.lt_succ_of_le w.2.2.2⟩,
    ⟨w.1.length % 2, Nat.mod_lt _ (by omega)⟩)

theorem boundedPositiveTerminalWordCode_injective (R : ℕ) :
    Function.Injective (boundedPositiveTerminalWordCode R) := by
  intro w v hcode
  apply Subtype.ext
  apply eq_of_cfTerminalPair_eq_of_length_mod_two_eq
      w.2.2.1 v.2.2.1
  · apply Prod.ext
    · have := congrArg (fun z => z.1.1) hcode
      simpa [boundedPositiveTerminalWordCode, cfTerminalNumerator] using! this
    · have := congrArg (fun z => z.2.1) hcode
      simpa [boundedPositiveTerminalWordCode, cfTerminalDenominator] using! this
  · have := congrArg (fun z => z.2.2.1) hcode
    simpa [boundedPositiveTerminalWordCode] using! this

noncomputable instance boundedPositiveTerminalWordFintype (R : ℕ) :
    Fintype (BoundedPositiveTerminalWord R) :=
  Fintype.ofInjective (boundedPositiveTerminalWordCode R)
    (boundedPositiveTerminalWordCode_injective R)

/-- Explicit quadratic count of all finite positive-word cylinders whose
terminal denominator is at most `R`. -/
theorem card_boundedPositiveTerminalWord_le (R : ℕ) :
    Fintype.card (BoundedPositiveTerminalWord R) ≤ 2 * (R + 1) ^ 2 := by
  calc
    Fintype.card (BoundedPositiveTerminalWord R) ≤
        Fintype.card (Fin (R + 1) × Fin (R + 1) × Fin 2) :=
      Fintype.card_le_of_injective (boundedPositiveTerminalWordCode R)
        (boundedPositiveTerminalWordCode_injective R)
    _ = 2 * (R + 1) ^ 2 := by
      simp [pow_two, Nat.mul_assoc, Nat.mul_comm]

theorem card_univ_boundedPositiveTerminalWord_le (R : ℕ) :
    (Finset.univ : Finset (BoundedPositiveTerminalWord R)).card ≤
      2 * (R + 1) ^ 2 := by
  simpa using! card_boundedPositiveTerminalWord_le R

/-! ## Direct composition with the oscillatory cylinder estimate -/

/-- Any retained family of denominator-`R` cylinders has total oscillatory
integral bounded by the explicit quadratic cylinder count. -/
theorem sum_norm_intervalIntegral_cfCylinders_le
    {R : ℕ} (s : Finset (BoundedPositiveTerminalWord R))
    (left right frequency : BoundedPositiveTerminalWord R → ℝ)
    {κ : ℝ} (hκ : 0 < κ)
    (hfrequency : ∀ w ∈ s, κ ≤ |frequency w|) :
    (∑ w ∈ s,
      ‖∫ x : ℝ in left w..right w,
        oscillatoryPhase (frequency w) x‖) ≤
      (2 * (R + 1) ^ 2 : ℕ) / (Real.pi * κ) := by
  apply sum_norm_intervalIntegral_oscillatoryPhase_le_of_card
      s left right frequency hκ (2 * (R + 1) ^ 2)
  · exact (Finset.card_le_univ s).trans
      (card_univ_boundedPositiveTerminalWord_le R)
  · exact hfrequency

/-- The same estimate for the complete family of all denominator-`R`
cylinders. -/
theorem sum_norm_intervalIntegral_all_cfCylinders_le
    {R : ℕ} (left right frequency : BoundedPositiveTerminalWord R → ℝ)
    {κ : ℝ} (hκ : 0 < κ)
    (hfrequency : ∀ w, κ ≤ |frequency w|) :
    (∑ w : BoundedPositiveTerminalWord R,
      ‖∫ x : ℝ in left w..right w,
        oscillatoryPhase (frequency w) x‖) ≤
      (2 * (R + 1) ^ 2 : ℕ) / (Real.pi * κ) := by
  simpa only [Finset.sum_subtype, Finset.mem_univ, and_true] using!
    sum_norm_intervalIntegral_cfCylinders_le
      (Finset.univ : Finset (BoundedPositiveTerminalWord R))
      left right frequency hκ (by simpa using! hfrequency)

end

end Erdos1002

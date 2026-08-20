import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite adaptive sampling bounds for Erdős 746

This file isolates the probability calculation used in the sprinkling
argument.  Everything is finite.  A history-dependent transition weight is
unfolded as a finite tree, and an induction gives the usual conditional-MGF
domination.  We then specialize the tree to uniform sampling without
replacement and prove that a fixed lower bound on the available booster
proportion exponentially suppresses the probability of avoiding every
booster.
-/

open scoped BigOperators

namespace Erdos746

section AdaptiveMoment

variable {A : Type*}

/-- The (unnormalized) multiplicative moment of the next `steps` levels of a
finite adaptive experiment.  At history `h`, choosing `a` contributes the
factor `factor h a`; the next history is `h ++ [a]`.

When `factor h a = q h a * exp (θ * X h a)`, this is exactly the exponential
moment obtained by expanding the finite probability tree with transition
weights `q`. -/
def adaptiveMoment (alphabet : Finset A) (factor : List A → A → ℝ) :
    List A → ℕ → ℝ
  | _, 0 => 1
  | h, steps + 1 =>
      ∑ a ∈ alphabet,
        factor h a * adaptiveMoment alphabet factor (h ++ [a]) steps

@[simp]
theorem adaptiveMoment_zero (alphabet : Finset A) (factor : List A → A → ℝ)
    (h : List A) :
    adaptiveMoment alphabet factor h 0 = 1 := rfl

@[simp]
theorem adaptiveMoment_succ (alphabet : Finset A) (factor : List A → A → ℝ)
    (h : List A) (steps : ℕ) :
    adaptiveMoment alphabet factor h (steps + 1) =
      ∑ a ∈ alphabet,
        factor h a * adaptiveMoment alphabet factor (h ++ [a]) steps := rfl

/-- Nonnegativity of a finite adaptive multiplicative moment. -/
theorem adaptiveMoment_nonneg (alphabet : Finset A) (factor : List A → A → ℝ)
    (hfactor : ∀ h a, 0 ≤ factor h a) :
    ∀ (h : List A) (steps : ℕ), 0 ≤ adaptiveMoment alphabet factor h steps := by
  intro h steps
  induction steps generalizing h with
  | zero => simp
  | succ steps ih =>
      rw [adaptiveMoment_succ]
      exact Finset.sum_nonneg fun a _ ↦
        mul_nonneg (hfactor h a) (ih (h ++ [a]))

/-- **Finite adaptive multiplicative-moment domination.**

Suppose every good history has one-step total factor at most `c`, and every
choice of nonzero factor leads to another good history.  Then the total
weight of the depth-`steps` tree is at most `c ^ steps`.  This is the finite
tower-property induction underlying adaptive Chernoff/MGF arguments; no
independence between different steps is assumed. -/
theorem adaptiveMoment_le_pow
    (alphabet : Finset A) (factor : List A → A → ℝ)
    (Good : List A → Prop) (c : ℝ)
    (hc : 0 ≤ c)
    (hfactor : ∀ h a, 0 ≤ factor h a)
    (hone : ∀ h, Good h → ∑ a ∈ alphabet, factor h a ≤ c)
    (hsupport : ∀ h, Good h → ∀ a ∈ alphabet,
      factor h a ≠ 0 → Good (h ++ [a])) :
    ∀ (h : List A), Good h → ∀ steps,
      adaptiveMoment alphabet factor h steps ≤ c ^ steps := by
  intro h hh steps
  induction steps generalizing h with
  | zero => simp
  | succ steps ih =>
      rw [adaptiveMoment_succ, pow_succ]
      calc
        (∑ a ∈ alphabet,
            factor h a * adaptiveMoment alphabet factor (h ++ [a]) steps) ≤
            ∑ a ∈ alphabet, factor h a * c ^ steps := by
              apply Finset.sum_le_sum
              intro a ha
              by_cases hzero : factor h a = 0
              · simp [hzero]
              · exact mul_le_mul_of_nonneg_left
                  (ih (h ++ [a]) (hsupport h hh a ha hzero)) (hfactor h a)
        _ = (∑ a ∈ alphabet, factor h a) * c ^ steps := by
              rw [Finset.sum_mul]
        _ ≤ c * c ^ steps :=
              mul_le_mul_of_nonneg_right (hone h hh) (pow_nonneg hc steps)
        _ = c ^ steps * c := mul_comm _ _

/-- The exact finite-tree moment-generating function for an adaptive process.
The transition weights and increments may both depend on the full past. -/
noncomputable def adaptiveMGF (alphabet : Finset A)
    (transition increment : List A → A → ℝ) (θ : ℝ) :
    List A → ℕ → ℝ :=
  adaptiveMoment alphabet fun h a ↦
    transition h a * Real.exp (θ * increment h a)

@[simp]
theorem adaptiveMGF_zero (alphabet : Finset A)
    (transition increment : List A → A → ℝ) (θ : ℝ) (h : List A) :
    adaptiveMGF alphabet transition increment θ h 0 = 1 := rfl

@[simp]
theorem adaptiveMGF_succ (alphabet : Finset A)
    (transition increment : List A → A → ℝ) (θ : ℝ)
    (h : List A) (steps : ℕ) :
    adaptiveMGF alphabet transition increment θ h (steps + 1) =
      ∑ a ∈ alphabet,
        transition h a * Real.exp (θ * increment h a) *
          adaptiveMGF alphabet transition increment θ (h ++ [a]) steps := rfl

/-- **Adaptive MGF domination.**  A uniform conditional bound on each
one-step MGF multiplies along the finite history tree, even though transition
laws and increments are history-dependent. -/
theorem adaptiveMGF_le_pow
    (alphabet : Finset A) (transition increment : List A → A → ℝ)
    (θ c : ℝ) (Good : List A → Prop)
    (hc : 0 ≤ c)
    (htransition : ∀ h a, 0 ≤ transition h a)
    (hone : ∀ h, Good h →
      ∑ a ∈ alphabet,
        transition h a * Real.exp (θ * increment h a) ≤ c)
    (hsupport : ∀ h, Good h → ∀ a ∈ alphabet,
      transition h a ≠ 0 → Good (h ++ [a])) :
    ∀ (h : List A), Good h → ∀ steps,
      adaptiveMGF alphabet transition increment θ h steps ≤ c ^ steps := by
  apply adaptiveMoment_le_pow alphabet
    (fun h a ↦ transition h a * Real.exp (θ * increment h a)) Good c hc
  · intro h a
    exact mul_nonneg (htransition h a) (Real.exp_nonneg _)
  · exact hone
  · intro h hh a ha hne
    apply hsupport h hh a ha
    intro hzero
    simp [hzero] at hne

/-! ## A finite adaptive lower-tail event -/

/-- Exact mass of paths of length `steps` having at most `budget` successes.
The Boolean `success h a` may depend on the complete history. -/
def adaptiveLowerTailMass (alphabet : Finset A)
    (transition : List A → A → ℝ) (success : List A → A → Bool) :
    List A → ℕ → ℕ → ℝ
  | _, 0, _ => 1
  | h, steps + 1, 0 =>
      ∑ a ∈ alphabet, transition h a *
        if success h a then 0
        else adaptiveLowerTailMass alphabet transition success (h ++ [a]) steps 0
  | h, steps + 1, budget + 1 =>
      ∑ a ∈ alphabet, transition h a *
        if success h a then
          adaptiveLowerTailMass alphabet transition success (h ++ [a]) steps budget
        else
          adaptiveLowerTailMass alphabet transition success (h ++ [a]) steps (budget + 1)

@[simp]
theorem adaptiveLowerTailMass_zero (alphabet : Finset A)
    (transition : List A → A → ℝ) (success : List A → A → Bool)
    (h : List A) (budget : ℕ) :
    adaptiveLowerTailMass alphabet transition success h 0 budget = 1 := rfl

@[simp]
theorem adaptiveLowerTailMass_succ_zero (alphabet : Finset A)
    (transition : List A → A → ℝ) (success : List A → A → Bool)
    (h : List A) (steps : ℕ) :
    adaptiveLowerTailMass alphabet transition success h (steps + 1) 0 =
      ∑ a ∈ alphabet, transition h a *
        if success h a then 0
        else adaptiveLowerTailMass alphabet transition success (h ++ [a]) steps 0 := rfl

@[simp]
theorem adaptiveLowerTailMass_succ_succ (alphabet : Finset A)
    (transition : List A → A → ℝ) (success : List A → A → Bool)
    (h : List A) (steps budget : ℕ) :
    adaptiveLowerTailMass alphabet transition success h (steps + 1) (budget + 1) =
      ∑ a ∈ alphabet, transition h a *
        if success h a then
          adaptiveLowerTailMass alphabet transition success (h ++ [a]) steps budget
        else
          adaptiveLowerTailMass alphabet transition success (h ++ [a]) steps (budget + 1) := rfl

/-- **Finite adaptive lower-tail domination from a one-step exponential
tilt.**  `Good h steps` records precisely which history/horizon pairs are
valid.  Thus terminal histories need not satisfy a further transition-law
hypothesis. -/
theorem adaptiveLowerTailMass_le_exp_mul_pow
    (alphabet : Finset A) (transition : List A → A → ℝ)
    (success : List A → A → Bool) (Good : List A → ℕ → Prop)
    {θ c : ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c)
    (htransition : ∀ h a, 0 ≤ transition h a)
    (htilt : ∀ h steps, Good h (steps + 1) →
      ∑ a ∈ alphabet, transition h a *
        (if success h a then Real.exp (-θ) else 1) ≤ c)
    (hsupport : ∀ h steps, Good h (steps + 1) → ∀ a ∈ alphabet,
      transition h a ≠ 0 → Good (h ++ [a]) steps) :
    ∀ h steps, Good h steps → ∀ budget,
      adaptiveLowerTailMass alphabet transition success h steps budget ≤
        Real.exp (θ * budget) * c ^ steps := by
  intro h steps hh budget
  induction steps generalizing h budget with
  | zero =>
      rw [adaptiveLowerTailMass_zero, pow_zero, mul_one]
      exact Real.one_le_exp (mul_nonneg hθ (Nat.cast_nonneg budget))
  | succ steps ih =>
      cases budget with
      | zero =>
          rw [adaptiveLowerTailMass_succ_zero, pow_succ]
          simp only [Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
          calc
            (∑ a ∈ alphabet, transition h a *
                if success h a then 0
                else adaptiveLowerTailMass alphabet transition success
                  (h ++ [a]) steps 0) ≤
                ∑ a ∈ alphabet,
                  (transition h a * (if success h a then Real.exp (-θ) else 1)) *
                    c ^ steps := by
              apply Finset.sum_le_sum
              intro a ha
              by_cases hzero : transition h a = 0
              · simp [hzero]
              · by_cases hs : success h a = true
                · simp [hs]
                  exact mul_nonneg
                    (mul_nonneg (htransition h a) (Real.exp_nonneg _))
                    (pow_nonneg hc steps)
                · have hi := ih (h ++ [a])
                      (hsupport h steps hh a ha hzero) 0
                  simpa [hs, mul_assoc] using
                    (mul_le_mul_of_nonneg_left hi (htransition h a))
            _ = (∑ a ∈ alphabet,
                  transition h a * (if success h a then Real.exp (-θ) else 1)) *
                    c ^ steps := by
              rw [Finset.sum_mul]
            _ ≤ c * c ^ steps :=
              mul_le_mul_of_nonneg_right (htilt h steps hh) (pow_nonneg hc steps)
            _ = c ^ steps * c := mul_comm _ _
      | succ budget =>
          rw [adaptiveLowerTailMass_succ_succ, pow_succ]
          have hexp :
              Real.exp (θ * (budget : ℝ)) =
                Real.exp (-θ) * Real.exp (θ * ((budget + 1 : ℕ) : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            norm_num [Nat.cast_add, Nat.cast_one]
            ring
          calc
            (∑ a ∈ alphabet, transition h a *
                if success h a then
                  adaptiveLowerTailMass alphabet transition success
                    (h ++ [a]) steps budget
                else
                  adaptiveLowerTailMass alphabet transition success
                    (h ++ [a]) steps (budget + 1)) ≤
                ∑ a ∈ alphabet,
                  (transition h a * (if success h a then Real.exp (-θ) else 1)) *
                    (Real.exp (θ * ((budget + 1 : ℕ) : ℝ)) * c ^ steps) := by
              apply Finset.sum_le_sum
              intro a ha
              by_cases hzero : transition h a = 0
              · simp [hzero]
              · by_cases hs : success h a = true
                · have hi := ih (h ++ [a])
                      (hsupport h steps hh a ha hzero) budget
                  rw [hexp] at hi
                  simpa [hs, mul_assoc] using
                    (mul_le_mul_of_nonneg_left hi (htransition h a))
                · have hi := ih (h ++ [a])
                      (hsupport h steps hh a ha hzero) (budget + 1)
                  simpa [hs, mul_assoc] using
                    (mul_le_mul_of_nonneg_left hi (htransition h a))
            _ = (∑ a ∈ alphabet,
                  transition h a * (if success h a then Real.exp (-θ) else 1)) *
                    (Real.exp (θ * ((budget + 1 : ℕ) : ℝ)) * c ^ steps) := by
              rw [Finset.sum_mul]
            _ ≤ c * (Real.exp (θ * ((budget + 1 : ℕ) : ℝ)) * c ^ steps) :=
              mul_le_mul_of_nonneg_right (htilt h steps hh)
                (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hc steps))
            _ = Real.exp (θ * ((budget + 1 : ℕ) : ℝ)) * (c ^ steps * c) := by
              ring

/-- **Adaptive 0/1 lower-tail Chernoff bound.**

The transitions at each valid nonterminal history have total mass one and
conditional success mass at least `q`.  There is no independence hypothesis:
both the transition law and the Boolean success test can depend on the whole
history. -/
theorem adaptiveLowerTailMass_le_exp
    (alphabet : Finset A) (transition : List A → A → ℝ)
    (success : List A → A → Bool) (Good : List A → ℕ → Prop)
    {θ q : ℝ} (hθ : 0 ≤ θ)
    (htransition : ∀ h a, 0 ≤ transition h a)
    (htotal : ∀ h steps, Good h (steps + 1) →
      ∑ a ∈ alphabet, transition h a = 1)
    (hsuccess : ∀ h steps, Good h (steps + 1) →
      q ≤ ∑ a ∈ alphabet, if success h a then transition h a else 0)
    (hsupport : ∀ h steps, Good h (steps + 1) → ∀ a ∈ alphabet,
      transition h a ≠ 0 → Good (h ++ [a]) steps) :
    ∀ h steps, Good h steps → ∀ budget,
      adaptiveLowerTailMass alphabet transition success h steps budget ≤
        Real.exp
          (θ * budget - q * steps * (1 - Real.exp (-θ))) := by
  intro h steps hh budget
  let δ : ℝ := 1 - Real.exp (-θ)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hθ))
  have hc : 0 ≤ Real.exp (-q * δ) := Real.exp_nonneg _
  have htilt : ∀ h steps, Good h (steps + 1) →
      ∑ a ∈ alphabet,
        transition h a * (if success h a then Real.exp (-θ) else 1) ≤
          Real.exp (-q * δ) := by
    intro h' steps' hh'
    have hid :
        (∑ a ∈ alphabet,
            transition h' a * (if success h' a then Real.exp (-θ) else 1)) =
          (∑ a ∈ alphabet, transition h' a) -
            (∑ a ∈ alphabet, if success h' a then transition h' a else 0) * δ := by
      calc
        (∑ a ∈ alphabet,
            transition h' a * (if success h' a then Real.exp (-θ) else 1)) =
            ∑ a ∈ alphabet,
              (transition h' a -
                (if success h' a then transition h' a else 0) * δ) := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hs : success h' a = true
          · simp [hs, δ]
            ring
          · simp [hs]
        _ = (∑ a ∈ alphabet, transition h' a) -
              ∑ a ∈ alphabet,
                (if success h' a then transition h' a else 0) * δ := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ a ∈ alphabet, transition h' a) -
              (∑ a ∈ alphabet, if success h' a then transition h' a else 0) * δ := by
          rw [Finset.sum_mul]
    rw [hid, htotal h' steps' hh']
    calc
      1 - (∑ a ∈ alphabet, if success h' a then transition h' a else 0) * δ ≤
          1 - q * δ := by
        exact sub_le_sub_left
          (mul_le_mul_of_nonneg_right (hsuccess h' steps' hh') hδ) 1
      _ ≤ Real.exp (-(q * δ)) := Real.one_sub_le_exp_neg _
      _ = Real.exp (-q * δ) := by
        congr 1
        ring
  have hbound := adaptiveLowerTailMass_le_exp_mul_pow alphabet transition success Good
    hθ hc htransition htilt hsupport h steps hh budget
  calc
    adaptiveLowerTailMass alphabet transition success h steps budget ≤
        Real.exp (θ * budget) * Real.exp (-q * δ) ^ steps := hbound
    _ = Real.exp (θ * budget - q * steps * (1 - Real.exp (-θ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      dsimp [δ]
      congr 1
      ring

end AdaptiveMoment

section WithoutReplacement

variable {A : Type*} [DecidableEq A]

/-- Elements of `ambient` which have not occurred in the history. -/
def remaining (ambient : Finset A) (h : List A) : Finset A :=
  ambient.filter fun a ↦ a ∉ h

/-- The currently available boosters. -/
def availableBoosters (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) : Finset A :=
  remaining ambient h ∩ boosters h

/-- The currently available choices which are not boosters. -/
def safeChoices (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) : Finset A :=
  remaining ambient h \ boosters h

/-- Histories which really can arise by sampling `ambient` without
replacement. -/
def AdmissibleHistory (ambient : Finset A) (h : List A) : Prop :=
  h.Nodup ∧ ∀ a ∈ h, a ∈ ambient

/-- A valid remaining sampling horizon. -/
def SamplingHorizon (ambient : Finset A) (h : List A) (steps : ℕ) : Prop :=
  AdmissibleHistory ambient h ∧ h.length + steps ≤ ambient.card

/-- Uniform transition weight on all elements not previously drawn. -/
noncomputable def uniformRemainingFactor
    (ambient : Finset A) (h : List A) (a : A) : ℝ :=
  if a ∈ remaining ambient h then
    ((remaining ambient h).card : ℝ)⁻¹
  else 0

/-- Boolean test for hitting the current adaptive booster set. -/
def boosterHit (boosters : List A → Finset A) (h : List A) (a : A) : Bool :=
  decide (a ∈ boosters h)

/-- Exact mass of uniform-without-replacement paths with at most `budget`
adaptive booster hits. -/
noncomputable def uniformBoosterLowerTailMass
    (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) (steps budget : ℕ) : ℝ :=
  adaptiveLowerTailMass ambient (uniformRemainingFactor ambient)
    (boosterHit boosters) h steps budget

/-- One transition factor for the event that a uniform draw from the
remaining elements avoids the adaptive booster set. -/
noncomputable def uniformAvoidanceFactor
    (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) (a : A) : ℝ :=
  if a ∈ safeChoices ambient boosters h then
    ((remaining ambient h).card : ℝ)⁻¹
  else 0

/-- Exact probability mass of avoiding every adaptive booster during the
next `steps` uniform draws without replacement, expanded as a finite tree.
It is intentionally defined from the transition tree, so it also remains
meaningful (and equals zero) if more draws are requested than remain. -/
noncomputable def sprinklingFailureMass
    (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) (steps : ℕ) : ℝ :=
  adaptiveMoment ambient (uniformAvoidanceFactor ambient boosters) h steps

theorem mem_remaining_iff {ambient : Finset A} {h : List A} {a : A} :
    a ∈ remaining ambient h ↔ a ∈ ambient ∧ a ∉ h := by
  simp [remaining]

theorem mem_availableBoosters_iff {ambient : Finset A}
    {boosters : List A → Finset A} {h : List A} {a : A} :
    a ∈ availableBoosters ambient boosters h ↔
      a ∈ remaining ambient h ∧ a ∈ boosters h := by
  simp [availableBoosters]

theorem mem_safeChoices_iff {ambient : Finset A}
    {boosters : List A → Finset A} {h : List A} {a : A} :
    a ∈ safeChoices ambient boosters h ↔
      a ∈ remaining ambient h ∧ a ∉ boosters h := by
  simp [safeChoices]

theorem remaining_eq_sdiff (ambient : Finset A) (h : List A) :
    remaining ambient h = ambient \ h.toFinset := by
  ext a
  simp [remaining]

/-- Cardinality of the remaining set along an admissible history. -/
theorem card_remaining_of_admissible (ambient : Finset A) {h : List A}
    (hh : AdmissibleHistory ambient h) :
    (remaining ambient h).card = ambient.card - h.length := by
  rw [remaining_eq_sdiff, Finset.card_sdiff_of_subset]
  · rw [List.toFinset_card_of_nodup hh.1]
  · intro a ha
    exact hh.2 a (List.mem_toFinset.mp ha)

/-- Available boosters and safe choices partition the remaining set. -/
theorem card_availableBoosters_add_card_safeChoices
    (ambient : Finset A) (boosters : List A → Finset A) (h : List A) :
    (availableBoosters ambient boosters h).card +
        (safeChoices ambient boosters h).card =
      (remaining ambient h).card := by
  rw [availableBoosters, safeChoices]
  exact Finset.card_inter_add_card_sdiff _ _

/-- The exact one-step failure mass is the fraction of remaining choices
which are not boosters. -/
theorem sum_uniformAvoidanceFactor
    (ambient : Finset A) (boosters : List A → Finset A) (h : List A) :
    (∑ a ∈ ambient, uniformAvoidanceFactor ambient boosters h a) =
      ((safeChoices ambient boosters h).card : ℝ) /
        ((remaining ambient h).card : ℝ) := by
  classical
  have hs : safeChoices ambient boosters h ⊆ ambient := by
    intro a ha
    exact (mem_remaining_iff.mp (mem_safeChoices_iff.mp ha).1).1
  have hcard :
      ((safeChoices ambient boosters h).card : ℝ) =
        ∑ a ∈ ambient, if a ∈ safeChoices ambient boosters h then (1 : ℝ) else 0 := by
    exact_mod_cast Finset.card_eq_sum_ite hs
  calc
    (∑ a ∈ ambient, uniformAvoidanceFactor ambient boosters h a) =
        (∑ a ∈ ambient, if a ∈ safeChoices ambient boosters h then (1 : ℝ) else 0) *
          ((remaining ambient h).card : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [uniformAvoidanceFactor]
      split_ifs <;> ring
    _ = ((safeChoices ambient boosters h).card : ℝ) *
          ((remaining ambient h).card : ℝ)⁻¹ := by
      rw [← hcard]
    _ = ((safeChoices ambient boosters h).card : ℝ) /
          ((remaining ambient h).card : ℝ) := by
      rw [div_eq_mul_inv]

/-- Uniform weights on the remaining elements sum to one whenever another
draw is available. -/
theorem sum_uniformRemainingFactor
    (ambient : Finset A) (h : List A)
    (hne : (remaining ambient h).card ≠ 0) :
    (∑ a ∈ ambient, uniformRemainingFactor ambient h a) = 1 := by
  classical
  have hs : remaining ambient h ⊆ ambient := by
    intro a ha
    exact (mem_remaining_iff.mp ha).1
  have hcard :
      ((remaining ambient h).card : ℝ) =
        ∑ a ∈ ambient, if a ∈ remaining ambient h then (1 : ℝ) else 0 := by
    exact_mod_cast Finset.card_eq_sum_ite hs
  calc
    (∑ a ∈ ambient, uniformRemainingFactor ambient h a) =
        (∑ a ∈ ambient, if a ∈ remaining ambient h then (1 : ℝ) else 0) *
          ((remaining ambient h).card : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [uniformRemainingFactor]
      split_ifs <;> ring
    _ = ((remaining ambient h).card : ℝ) *
          ((remaining ambient h).card : ℝ)⁻¹ := by rw [← hcard]
    _ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hne)

/-- The one-step mass of booster hits is exactly their proportion among the
remaining elements. -/
theorem sum_uniformRemainingFactor_boosterHit
    (ambient : Finset A) (boosters : List A → Finset A) (h : List A) :
    (∑ a ∈ ambient,
        if boosterHit boosters h a then uniformRemainingFactor ambient h a else 0) =
      ((availableBoosters ambient boosters h).card : ℝ) /
        ((remaining ambient h).card : ℝ) := by
  classical
  have hs : availableBoosters ambient boosters h ⊆ ambient := by
    intro a ha
    exact (mem_remaining_iff.mp (mem_availableBoosters_iff.mp ha).1).1
  have hcard :
      ((availableBoosters ambient boosters h).card : ℝ) =
        ∑ a ∈ ambient,
          if a ∈ availableBoosters ambient boosters h then (1 : ℝ) else 0 := by
    exact_mod_cast Finset.card_eq_sum_ite hs
  calc
    (∑ a ∈ ambient,
        if boosterHit boosters h a then uniformRemainingFactor ambient h a else 0) =
        (∑ a ∈ ambient,
          if a ∈ availableBoosters ambient boosters h then (1 : ℝ) else 0) *
            ((remaining ambient h).card : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hr : a ∈ remaining ambient h
      · by_cases hb : a ∈ boosters h <;>
          simp [boosterHit, uniformRemainingFactor, availableBoosters, hr, hb]
      · simp [boosterHit, uniformRemainingFactor, availableBoosters, hr]
    _ = ((availableBoosters ambient boosters h).card : ℝ) *
          ((remaining ambient h).card : ℝ)⁻¹ := by rw [← hcard]
    _ = ((availableBoosters ambient boosters h).card : ℝ) /
          ((remaining ambient h).card : ℝ) := by rw [div_eq_mul_inv]

theorem remaining_card_ne_zero_of_samplingHorizon_succ
    (ambient : Finset A) {h : List A} {steps : ℕ}
    (hh : SamplingHorizon ambient h (steps + 1)) :
    (remaining ambient h).card ≠ 0 := by
  rcases hh with ⟨hadm, hlength⟩
  rw [card_remaining_of_admissible ambient hadm]
  omega

/-- A nonzero uniform transition chooses a fresh element and preserves the
remaining-horizon invariant. -/
theorem samplingHorizon_append_of_uniformRemainingFactor_ne_zero
    (ambient : Finset A) {h : List A} {steps : ℕ}
    (hh : SamplingHorizon ambient h (steps + 1)) {a : A}
    (hne : uniformRemainingFactor ambient h a ≠ 0) :
    SamplingHorizon ambient (h ++ [a]) steps := by
  classical
  rcases hh with ⟨hadm, hlength⟩
  have haRemaining : a ∈ remaining ambient h := by
    by_contra ha
    simp [uniformRemainingFactor, ha] at hne
  have haAmbient : a ∈ ambient := (mem_remaining_iff.mp haRemaining).1
  have haFresh : a ∉ h := (mem_remaining_iff.mp haRemaining).2
  constructor
  · constructor
    · exact hadm.1.append (List.nodup_singleton a)
        (List.disjoint_singleton.mpr haFresh)
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hadm.2 x hx
      · exact haAmbient
  · simp only [List.length_append, List.length_singleton]
    omega

/-- A cardinal booster-proportion hypothesis gives the corresponding
conditional success-mass lower bound. -/
theorem le_sum_uniformRemainingFactor_boosterHit
    (ambient : Finset A) (boosters : List A → Finset A) (h : List A)
    {q : ℝ} (hne : (remaining ambient h).card ≠ 0)
    (hproportion :
      q * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ)) :
    q ≤ ∑ a ∈ ambient,
      if boosterHit boosters h a then uniformRemainingFactor ambient h a else 0 := by
  rw [sum_uniformRemainingFactor_boosterHit]
  apply (le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hne)).2
  exact hproportion

/-- **Adaptive booster-count lower tail for uniform sampling without
replacement.**  If at every nonterminal admissible history the available
boosters occupy at least a `q` proportion of the remaining ambient set, then
the mass of `steps`-draw paths with at most `budget` booster hits satisfies
the stated Chernoff bound. -/
theorem uniformBoosterLowerTailMass_le_exp
    (ambient : Finset A) (boosters : List A → Finset A)
    {θ q : ℝ} (hθ : 0 ≤ θ)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      h.length < ambient.card →
      q * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ))
    {h : List A} {steps : ℕ} (hh : SamplingHorizon ambient h steps)
    (budget : ℕ) :
    uniformBoosterLowerTailMass ambient boosters h steps budget ≤
      Real.exp
        (θ * budget - q * steps * (1 - Real.exp (-θ))) := by
  apply adaptiveLowerTailMass_le_exp ambient
    (uniformRemainingFactor ambient) (boosterHit boosters)
    (SamplingHorizon ambient) hθ
  · intro h' a
    simp only [uniformRemainingFactor]
    split_ifs
    · positivity
    · exact le_rfl
  · intro h' steps' hh'
    exact sum_uniformRemainingFactor ambient h'
      (remaining_card_ne_zero_of_samplingHorizon_succ ambient hh')
  · intro h' steps' hh'
    have hne := remaining_card_ne_zero_of_samplingHorizon_succ ambient hh'
    apply le_sum_uniformRemainingFactor_boosterHit ambient boosters h' hne
    apply hproportion h' hh'.1
    rcases hh' with ⟨hadm, hlength⟩
    omega
  · intro h' steps' hh' a ha hne
    exact samplingHorizon_append_of_uniformRemainingFactor_ne_zero ambient hh' hne
  · exact hh

/-- The specialization used in the Hamiltonicity sprinkling argument: the
conditional booster proportion is `1/16`, and failure means making at most
`n - 1` successful extensions. -/
theorem uniformBoosterLowerTailMass_le_exp_one_sixteenth
    (ambient : Finset A) (boosters : List A → Finset A)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      h.length < ambient.card →
      (1 / 16 : ℝ) * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ))
    {h : List A} {steps n : ℕ} (hh : SamplingHorizon ambient h steps) :
    uniformBoosterLowerTailMass ambient boosters h steps (n - 1) ≤
      Real.exp
        (θ * (n - 1 : ℕ) - (1 / 16 : ℝ) * steps *
          (1 - Real.exp (-θ))) := by
  exact uniformBoosterLowerTailMass_le_exp ambient boosters hθ
    hproportion hh (n - 1)

/-- A nonzero avoidance transition appends a fresh element of the ambient,
so admissibility is preserved. -/
theorem admissibleHistory_append_of_uniformAvoidanceFactor_ne_zero
    (ambient : Finset A) (boosters : List A → Finset A)
    {h : List A} (hh : AdmissibleHistory ambient h) {a : A}
    (hne : uniformAvoidanceFactor ambient boosters h a ≠ 0) :
    AdmissibleHistory ambient (h ++ [a]) := by
  classical
  have haSafe : a ∈ safeChoices ambient boosters h := by
    by_contra ha
    simp [uniformAvoidanceFactor, ha] at hne
  have haRemaining : a ∈ remaining ambient h :=
    (mem_safeChoices_iff.mp haSafe).1
  have haU : a ∈ ambient := (mem_remaining_iff.mp haRemaining).1
  have haFresh : a ∉ h := (mem_remaining_iff.mp haRemaining).2
  constructor
  · exact hh.1.append (List.nodup_singleton a)
      (List.disjoint_singleton.mpr haFresh)
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hh.2 x hx
    · exact haU

/-- A booster proportion lower bound gives the corresponding one-step
failure bound.  The empty-remaining-set case is included. -/
theorem sum_uniformAvoidanceFactor_le_one_sub
    (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) {β : ℝ} (hβle : β ≤ 1)
    (hproportion :
      β * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ)) :
    (∑ a ∈ ambient, uniformAvoidanceFactor ambient boosters h a) ≤
      1 - β := by
  rw [sum_uniformAvoidanceFactor]
  by_cases hempty : (remaining ambient h).card = 0
  · simp [hempty, hβle]
  · have hpos : (0 : ℝ) < ((remaining ambient h).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hempty
    apply (div_le_iff₀ hpos).2
    have hpartition := card_availableBoosters_add_card_safeChoices ambient boosters h
    have hpartitionR :
        ((availableBoosters ambient boosters h).card : ℝ) +
            ((safeChoices ambient boosters h).card : ℝ) =
          ((remaining ambient h).card : ℝ) := by
      exact_mod_cast hpartition
    nlinarith

/-- **Finite sprinkling bound for adaptive boosters.**

At every admissible history, suppose at least a `β` proportion of the
remaining elements are boosters.  Uniform sampling without replacement then
avoids every booster for `steps` further draws with probability mass at most
`(1 - β) ^ steps`.  The booster set may depend arbitrarily on the complete
history. -/
theorem sprinklingFailureMass_le_pow_one_sub
    (ambient : Finset A) (boosters : List A → Finset A)
    {β : ℝ} (hβnonneg : 0 ≤ β) (hβle : β ≤ 1)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      β * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ)) :
    ∀ h, AdmissibleHistory ambient h → ∀ steps,
      sprinklingFailureMass ambient boosters h steps ≤ (1 - β) ^ steps := by
  intro h hh steps
  apply adaptiveMoment_le_pow ambient
    (uniformAvoidanceFactor ambient boosters)
    (AdmissibleHistory ambient) (1 - β)
  · by_cases hβnonpos : β ≤ 0
    · have hβzero : β = 0 := le_antisymm hβnonpos hβnonneg
      simp [hβzero]
    · exact sub_nonneg.mpr hβle
  · intro h' a
    simp only [uniformAvoidanceFactor]
    split_ifs
    · positivity
    · exact le_rfl
  · intro h' hh'
    exact sum_uniformAvoidanceFactor_le_one_sub ambient boosters h' hβle
      (hproportion h' hh')
  · intro h' hh' a _ hne
    exact admissibleHistory_append_of_uniformAvoidanceFactor_ne_zero
      ambient boosters hh' hne
  · exact hh

/-- The standard exponential form of the finite sprinkling bound. -/
theorem sprinklingFailureMass_le_exp
    (ambient : Finset A) (boosters : List A → Finset A)
    {β : ℝ} (hβnonneg : 0 ≤ β) (hβle : β ≤ 1)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      β * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ))
    {h : List A} (hh : AdmissibleHistory ambient h) (steps : ℕ) :
    sprinklingFailureMass ambient boosters h steps ≤
      Real.exp (-β * steps) := by
  calc
    sprinklingFailureMass ambient boosters h steps ≤ (1 - β) ^ steps :=
      sprinklingFailureMass_le_pow_one_sub ambient boosters hβnonneg hβle
        hproportion h hh steps
    _ ≤ (Real.exp (-β)) ^ steps := by
      exact pow_le_pow_left₀ (sub_nonneg.mpr hβle) (Real.one_sub_le_exp_neg β) steps
    _ = Real.exp (-β * steps) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Initial-history version of the adaptive sprinkling bound. -/
theorem sprinklingFailureMass_nil_le_exp
    (ambient : Finset A) (boosters : List A → Finset A)
    {β : ℝ} (hβnonneg : 0 ≤ β) (hβle : β ≤ 1)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      β * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ))
    (steps : ℕ) :
    sprinklingFailureMass ambient boosters [] steps ≤
      Real.exp (-β * steps) := by
  apply sprinklingFailureMass_le_exp ambient boosters hβnonneg hβle
    hproportion
  simp [AdmissibleHistory]

/-- The complementary mass of paths on which at least one adaptive booster
is hit during the sprinkling round. -/
noncomputable def sprinklingSuccessMass
    (ambient : Finset A) (boosters : List A → Finset A)
    (h : List A) (steps : ℕ) : ℝ :=
  1 - sprinklingFailureMass ambient boosters h steps

/-- Success-probability form of the adaptive sprinkling estimate. -/
theorem one_sub_exp_le_sprinklingSuccessMass
    (ambient : Finset A) (boosters : List A → Finset A)
    {β : ℝ} (hβnonneg : 0 ≤ β) (hβle : β ≤ 1)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      β * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ))
    {h : List A} (hh : AdmissibleHistory ambient h) (steps : ℕ) :
    1 - Real.exp (-β * steps) ≤
      sprinklingSuccessMass ambient boosters h steps := by
  rw [sprinklingSuccessMass]
  exact sub_le_sub_left
    (sprinklingFailureMass_le_exp ambient boosters hβnonneg hβle
      hproportion hh steps) 1

/-- Initial-history success-probability form. -/
theorem one_sub_exp_le_sprinklingSuccessMass_nil
    (ambient : Finset A) (boosters : List A → Finset A)
    {β : ℝ} (hβnonneg : 0 ≤ β) (hβle : β ≤ 1)
    (hproportion : ∀ h, AdmissibleHistory ambient h →
      β * ((remaining ambient h).card : ℝ) ≤
        ((availableBoosters ambient boosters h).card : ℝ))
    (steps : ℕ) :
    1 - Real.exp (-β * steps) ≤
      sprinklingSuccessMass ambient boosters [] steps := by
  apply one_sub_exp_le_sprinklingSuccessMass ambient boosters hβnonneg hβle
    hproportion
  simp [AdmissibleHistory]

end WithoutReplacement

end Erdos746

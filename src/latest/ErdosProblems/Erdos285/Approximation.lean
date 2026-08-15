/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import UnitFractions.Definitions

/-!
# Erdős 285: Martin's approximate-representation interface

This file isolates the finite bookkeeping in Proposition 6 of Greg Martin's
*Denser Egyptian fractions*.  The analytic and modular-number-theory inputs are
represented by hypotheses of the theorems which use them; no global assumption
is introduced here.

There are three layers.

* `ApproximationState` and `ApproximationStep` implement Martin's recursion.  A
  state remembers both the currently selected denominators and every denominator
  that has ever been used.  A valid step may remove selected terms and may add
  only terms which have never been used.
* `ApproximationCertificate` is a finite, quantitative version of Proposition 6.
  The condition `q ^ 5 ≤ x` is the integral form of `q ≤ x^(1/5)` and avoids
  rounding ambiguity.
* `HasMartinApproximation` is the epsilon form of the cardinality asymptotic.

The actual construction of the blocks used in a valid step is the deep part of
Martin's argument (modular subset sums and smooth-number estimates).  Once those
blocks are supplied, all cardinality, reciprocal-sum, interval, and non-reuse
claims are proved below.
-/

namespace Erdos285

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The exact finite certificate -/

/-- The reciprocal sum of a finite set, regarded as a real number. -/
def realRecSum (A : Finset ℕ) : ℝ := ∑ n ∈ A, (1 : ℝ) / n

lemma realRecSum_eq_ratCast (A : Finset ℕ) :
    realRecSum A = (UnitFractions.rec_sum A : ℝ) := by
  simp only [realRecSum, UnitFractions.rec_sum, Rat.cast_sum, Rat.cast_div,
    Rat.cast_one, Rat.cast_natCast]

lemma realRecSum_disjoint {A B : Finset ℕ} (hAB : Disjoint A B) :
    realRecSum (A ∪ B) = realRecSum A + realRecSum B := by
  simpa [realRecSum] using Finset.sum_union hAB (f := fun n : ℕ ↦ (1 : ℝ) / n)

/-- The integer fifth-root scale passed from Proposition 6 to the exact
small-denominator correction in Proposition 7. -/
def approximationCorrectionScale (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊

/--
A finite certificate for Martin's Proposition 6 at scale `x` and target
cardinality `R`.

The interval starts at `exp (-r) * x / 2`, because the smooth reservoir used for
cardinality adjustment lies immediately below the main interval.  The main
interval itself begins at `exp (-r) * x` up to the quantified error.
-/
structure ApproximationCertificate (r : ℚ) (x R : ℕ) where
  denominators : Finset ℕ
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator_pos : 0 < numerator
  reduced : Nat.Coprime numerator denominator
  card_eq : denominators.card = R
  zero_not_mem : 0 ∉ denominators
  interval : ∀ n ∈ denominators,
    Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ x
  sum_add_residual :
    UnitFractions.rec_sum denominators + (numerator : ℚ) / denominator = r
  residual_lower :
    (Real.log (x : ℝ))⁻¹ < (numerator : ℝ) / denominator
  residual_upper : (numerator : ℝ) / denominator < 1
  denominator_primePower_bound :
    ∀ q : ℕ, IsPrimePow q → q ∣ denominator → q ^ 5 ≤ x

/-- The residual rational represented by an approximation certificate. -/
def ApproximationCertificate.residual {r : ℚ} {x R : ℕ}
    (C : ApproximationCertificate r x R) : ℚ :=
  (C.numerator : ℚ) / C.denominator

/-- The displayed numerator and denominator in a certificate are already
reduced, so the rational residual has exactly the displayed denominator. -/
lemma ApproximationCertificate.residual_den_eq
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    C.residual.den = C.denominator := by
  have hb : (0 : ℤ) < C.denominator := by exact_mod_cast C.denominator_pos
  have hcop : Nat.Coprime
      (C.numerator : ℤ).natAbs (C.denominator : ℤ).natAbs := by
    simpa using C.reduced
  have hden :
      ((((C.numerator : ℤ) : ℚ) / ((C.denominator : ℤ) : ℚ)).den : ℤ) =
        (C.denominator : ℤ) :=
    Rat.den_div_eq_of_coprime hb hcop
  change ((C.numerator : ℚ) / (C.denominator : ℚ)).den = C.denominator
  have hden' :
      ((((C.numerator : ℚ) / (C.denominator : ℚ)).den : ℕ) : ℤ) =
        (C.denominator : ℤ) := by
    simpa only [Int.cast_natCast] using hden
  exact Int.ofNat.inj hden'

lemma ApproximationCertificate.reciprocal_sum_eq_sub_residual
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    UnitFractions.rec_sum C.denominators = r - C.residual := by
  rw [eq_sub_iff_add_eq, ApproximationCertificate.residual]
  exact C.sum_add_residual

lemma ApproximationCertificate.residual_pos
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    0 < C.residual := by
  dsimp [ApproximationCertificate.residual]
  exact div_pos (by exact_mod_cast C.numerator_pos) (by exact_mod_cast C.denominator_pos)

lemma ApproximationCertificate.denominators_nonempty
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) (hR : 0 < R) :
    C.denominators.Nonempty := by
  apply Finset.card_pos.mp
  rw [C.card_eq]
  exact hR

/-! ## Removal/addition recursion with a no-reuse invariant -/

/--
A state in the prime-power elimination recursion.  `selected` is the current
Egyptian-fraction set; `used` additionally retains terms removed at earlier
stages, so they cannot be selected again.
-/
structure ApproximationState where
  selected : Finset ℕ
  used : Finset ℕ

/-- A stage removes some current terms and inserts a fresh correction block. -/
structure ApproximationStep where
  remove : Finset ℕ
  add : Finset ℕ

/-- Execute one removal/addition stage. -/
def ApproximationState.applyStep (s : ApproximationState) (d : ApproximationStep) :
    ApproximationState where
  selected := (s.selected \ d.remove) ∪ d.add
  used := s.used ∪ d.add

/--
Validity of one stage.  The old selected set must already lie in `used`; removed
terms must actually be selected; and new terms must be disjoint from all terms
ever used.
-/
def ApproximationStep.Valid (s : ApproximationState) (d : ApproximationStep) : Prop :=
  s.selected ⊆ s.used ∧ d.remove ⊆ s.selected ∧ Disjoint d.add s.used

lemma ApproximationStep.Valid.add_disjoint_selected
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    Disjoint d.add s.selected :=
  h.2.2.mono_right h.1

lemma ApproximationStep.Valid.add_disjoint_remaining
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    Disjoint (s.selected \ d.remove) d.add := by
  exact h.add_disjoint_selected.symm.mono_left (Finset.sdiff_subset)

lemma ApproximationStep.Valid.selected_subset_used_after
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    (s.applyStep d).selected ⊆ (s.applyStep d).used := by
  intro n hn
  rw [ApproximationState.applyStep, Finset.mem_union] at hn ⊢
  rcases hn with hn | hn
  · exact Or.inl (h.1 (Finset.sdiff_subset hn))
  · exact Or.inr hn

lemma ApproximationStep.Valid.used_card_after
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    (s.applyStep d).used.card = s.used.card + d.add.card := by
  rw [ApproximationState.applyStep, Finset.card_union_of_disjoint]
  exact h.2.2.symm

/-- Exact cardinality balance for one recursion stage. -/
lemma ApproximationStep.Valid.selected_card_balance
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    (s.applyStep d).selected.card + d.remove.card =
      s.selected.card + d.add.card := by
  rw [ApproximationState.applyStep,
    Finset.card_union_of_disjoint h.add_disjoint_remaining,
    Finset.card_sdiff_of_subset h.2.1]
  have hcardle := Finset.card_le_card h.2.1
  omega

/-- Exact reciprocal-sum balance for one recursion stage. -/
lemma ApproximationStep.Valid.rec_sum_balance
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    UnitFractions.rec_sum (s.applyStep d).selected + UnitFractions.rec_sum d.remove =
      UnitFractions.rec_sum s.selected + UnitFractions.rec_sum d.add := by
  have hnew := UnitFractions.rec_sum_disjoint h.add_disjoint_remaining
  have hold := UnitFractions.rec_sum_disjoint
    (Finset.sdiff_disjoint : Disjoint (s.selected \ d.remove) d.remove)
  rw [Finset.sdiff_union_of_subset h.2.1] at hold
  rw [ApproximationState.applyStep, hnew, hold]
  ring

lemma ApproximationStep.Valid.rec_sum_after
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    UnitFractions.rec_sum (s.applyStep d).selected =
      UnitFractions.rec_sum s.selected +
        (UnitFractions.rec_sum d.add - UnitFractions.rec_sum d.remove) := by
  have := h.rec_sum_balance
  linarith

lemma ApproximationStep.Valid.selected_card_after_int
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    ((s.applyStep d).selected.card : ℤ) =
      (s.selected.card : ℤ) + ((d.add.card : ℤ) - d.remove.card) := by
  have hbal := h.selected_card_balance
  have hbal' :
      ((s.applyStep d).selected.card : ℤ) + (d.remove.card : ℤ) =
        (s.selected.card : ℤ) + (d.add.card : ℤ) := by
    exact_mod_cast hbal
  omega

/-- A recursively valid list of elimination stages. -/
def ValidApproximationRun : ApproximationState → List ApproximationStep → Prop
  | s, [] => s.selected ⊆ s.used
  | s, d :: ds => d.Valid s ∧ ValidApproximationRun (s.applyStep d) ds

/-- Execute a list of elimination stages. -/
def runApproximation : ApproximationState → List ApproximationStep → ApproximationState
  | s, [] => s
  | s, d :: ds => runApproximation (s.applyStep d) ds

/-- Rational reciprocal-sum change contributed by a stage. -/
def ApproximationStep.sumDelta (d : ApproximationStep) : ℚ :=
  UnitFractions.rec_sum d.add - UnitFractions.rec_sum d.remove

/-- Integral cardinality change contributed by a stage. -/
def ApproximationStep.cardDelta (d : ApproximationStep) : ℤ :=
  (d.add.card : ℤ) - d.remove.card

lemma ValidApproximationRun.selected_subset_used
    {s : ApproximationState} {ds : List ApproximationStep}
    (h : ValidApproximationRun s ds) :
    (runApproximation s ds).selected ⊆ (runApproximation s ds).used := by
  induction ds generalizing s with
  | nil => exact h
  | cons d ds ih =>
      exact ih h.2

/-- The exact telescoping reciprocal-sum identity over the whole recursion. -/
lemma ValidApproximationRun.rec_sum_run
    {s : ApproximationState} {ds : List ApproximationStep}
    (h : ValidApproximationRun s ds) :
    UnitFractions.rec_sum (runApproximation s ds).selected =
      UnitFractions.rec_sum s.selected + (ds.map ApproximationStep.sumDelta).sum := by
  induction ds generalizing s with
  | nil => simp [runApproximation]
  | cons d ds ih =>
      rw [runApproximation, ih h.2, List.map_cons, List.sum_cons,
        h.1.rec_sum_after, ApproximationStep.sumDelta]
      ring

/-- The exact telescoping cardinality identity over the whole recursion. -/
lemma ValidApproximationRun.card_run
    {s : ApproximationState} {ds : List ApproximationStep}
    (h : ValidApproximationRun s ds) :
    ((runApproximation s ds).selected.card : ℤ) =
      (s.selected.card : ℤ) + (ds.map ApproximationStep.cardDelta).sum := by
  induction ds generalizing s with
  | nil => simp [runApproximation]
  | cons d ds ih =>
      rw [runApproximation, ih h.2, List.map_cons, List.sum_cons,
        h.1.selected_card_after_int, ApproximationStep.cardDelta]
      ring

/-- The number of ever-used terms grows by the sum of the fresh block sizes. -/
lemma ValidApproximationRun.used_card_run
    {s : ApproximationState} {ds : List ApproximationStep}
    (h : ValidApproximationRun s ds) :
    (runApproximation s ds).used.card =
      s.used.card + (ds.map fun d ↦ d.add.card).sum := by
  induction ds generalizing s with
  | nil => simp [runApproximation]
  | cons d ds ih =>
      rw [runApproximation, ih h.2, List.map_cons, List.sum_cons, h.1.used_card_after]
      omega

/-- A predicate is preserved when every newly added correction block satisfies it. -/
lemma ValidApproximationRun.forall_selected
    {s : ApproximationState} {ds : List ApproximationStep} {P : ℕ → Prop}
    (h : ValidApproximationRun s ds)
    (hs : ∀ n ∈ s.selected, P n)
    (hadd : ∀ d ∈ ds, ∀ n ∈ d.add, P n) :
    ∀ n ∈ (runApproximation s ds).selected, P n := by
  induction ds generalizing s with
  | nil => simpa [runApproximation] using hs
  | cons d ds ih =>
      apply ih h.2
      · intro n hn
        rw [ApproximationState.applyStep, Finset.mem_union] at hn
        rcases hn with hn | hn
        · exact hs n (Finset.sdiff_subset hn)
        · exact hadd d (by simp) n hn
      · intro e he n hn
        exact hadd e (by simp [he]) n hn

/-! ## Exact-cardinality selection from the smooth reservoir -/

/--
Select exactly enough unused reservoir terms to bring a finite construction to
cardinality `R`.  Besides existence, the result records the exact reciprocal-sum
and disjointness identities needed when the analytic argument updates the
residual.
-/
theorem exists_exact_card_extension
    {A reservoir : Finset ℕ} {R : ℕ}
    (hAR : A.card ≤ R)
    (hcapacity : R - A.card ≤ reservoir.card)
    (hdisjoint : Disjoint A reservoir) :
    ∃ padding : Finset ℕ,
      padding ⊆ reservoir ∧
      Disjoint A padding ∧
      (A ∪ padding).card = R ∧
      UnitFractions.rec_sum (A ∪ padding) =
        UnitFractions.rec_sum A + UnitFractions.rec_sum padding := by
  obtain ⟨padding, hpadding, hcard⟩ :=
    Finset.exists_subset_card_eq (s := reservoir) hcapacity
  refine ⟨padding, hpadding, hdisjoint.mono_right hpadding, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (hdisjoint.mono_right hpadding), hcard]
    omega
  · exact UnitFractions.rec_sum_disjoint (hdisjoint.mono_right hpadding)

lemma exists_exact_card_extension_forall
    {A reservoir : Finset ℕ} {R : ℕ} {P : ℕ → Prop}
    (hAR : A.card ≤ R)
    (hcapacity : R - A.card ≤ reservoir.card)
    (hdisjoint : Disjoint A reservoir)
    (hA : ∀ n ∈ A, P n)
    (hreservoir : ∀ n ∈ reservoir, P n) :
    ∃ padding : Finset ℕ,
      padding ⊆ reservoir ∧
      Disjoint A padding ∧
      (A ∪ padding).card = R ∧
      (∀ n ∈ A ∪ padding, P n) ∧
      UnitFractions.rec_sum (A ∪ padding) =
        UnitFractions.rec_sum A + UnitFractions.rec_sum padding := by
  obtain ⟨padding, hpadding, hdis, hcard, hsum⟩ :=
    exists_exact_card_extension hAR hcapacity hdisjoint
  refine ⟨padding, hpadding, hdis, hcard, ?_, hsum⟩
  intro n hn
  rw [Finset.mem_union] at hn
  exact hn.elim (hA n) (fun hn' ↦ hreservoir n (hpadding hn'))

/--
Run all prime-power elimination stages and then fill from a fresh smooth
reservoir.  This is the finite assembly step in Martin's Proposition 6.
-/
theorem exists_exact_card_extension_after_run
    {s : ApproximationState} {ds : List ApproximationStep}
    {reservoir : Finset ℕ} {R : ℕ} {P : ℕ → Prop}
    (hrun : ValidApproximationRun s ds)
    (hcard : (runApproximation s ds).selected.card ≤ R)
    (hcapacity : R - (runApproximation s ds).selected.card ≤ reservoir.card)
    (hfresh : Disjoint (runApproximation s ds).used reservoir)
    (hstart : ∀ n ∈ s.selected, P n)
    (hadds : ∀ d ∈ ds, ∀ n ∈ d.add, P n)
    (hreservoir : ∀ n ∈ reservoir, P n) :
    ∃ padding : Finset ℕ,
      padding ⊆ reservoir ∧
      Disjoint (runApproximation s ds).used padding ∧
      ((runApproximation s ds).selected ∪ padding).card = R ∧
      (∀ n ∈ (runApproximation s ds).selected ∪ padding, P n) ∧
      UnitFractions.rec_sum ((runApproximation s ds).selected ∪ padding) =
        UnitFractions.rec_sum s.selected +
          (ds.map ApproximationStep.sumDelta).sum + UnitFractions.rec_sum padding := by
  have hselectedUsed := hrun.selected_subset_used
  have hselectedFresh :
      Disjoint (runApproximation s ds).selected reservoir :=
    hfresh.mono_left hselectedUsed
  have hselectedP := hrun.forall_selected hstart hadds
  obtain ⟨padding, hpadding, hdis, hcardR, hP, hsum⟩ :=
    exists_exact_card_extension_forall hcard hcapacity hselectedFresh hselectedP hreservoir
  refine ⟨padding, hpadding, hfresh.mono_right hpadding, hcardR, hP, ?_⟩
  rw [hsum, hrun.rec_sum_run]

/-- Membership in the full interval used by the approximate representation. -/
def InApproximationInterval (r : ℚ) (x n : ℕ) : Prop :=
  Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ x

/--
Package a completed valid recursion as a Proposition 6 certificate.  The
hypotheses concerning the residual and its prime-power factors are precisely the
number-theoretic conclusions of Martin's elimination argument; the term-count,
positivity of denominators, and interval assertions are derived here.
-/
def approximationCertificate_of_valid_run
    {r : ℚ} {x R : ℕ} {s : ApproximationState} {ds : List ApproximationStep}
    {a b : ℕ}
    (hrun : ValidApproximationRun s ds)
    (hcard : (runApproximation s ds).selected.card = R)
    (hstartZero : ∀ n ∈ s.selected, n ≠ 0)
    (haddsZero : ∀ d ∈ ds, ∀ n ∈ d.add, n ≠ 0)
    (hstartInterval : ∀ n ∈ s.selected, InApproximationInterval r x n)
    (haddsInterval :
      ∀ d ∈ ds, ∀ n ∈ d.add, InApproximationInterval r x n)
    (hb : 0 < b) (ha : 0 < a) (hab : Nat.Coprime a b)
    (hsum : UnitFractions.rec_sum (runApproximation s ds).selected + (a : ℚ) / b = r)
    (hlower : (Real.log (x : ℝ))⁻¹ < (a : ℝ) / b)
    (hupper : (a : ℝ) / b < 1)
    (hsmooth : ∀ q : ℕ, IsPrimePow q → q ∣ b → q ^ 5 ≤ x) :
    ApproximationCertificate r x R := by
  have hzero := hrun.forall_selected hstartZero haddsZero
  have hinterval := hrun.forall_selected hstartInterval haddsInterval
  refine
    { denominators := (runApproximation s ds).selected
      numerator := a
      denominator := b
      denominator_pos := hb
      numerator_pos := ha
      reduced := hab
      card_eq := hcard
      zero_not_mem := ?_
      interval := ?_
      sum_add_residual := hsum
      residual_lower := hlower
      residual_upper := hupper
      denominator_primePower_bound := hsmooth }
  · intro hz
    exact hzero 0 hz rfl
  · intro n hn
    exact hinterval n hn

/-! ## Finite epsilon/asymptotic interface -/

/-- The expected density of denominators in Martin's theorem. -/
def martinDensity (r : ℚ) : ℝ := 1 - Real.exp (-(r : ℝ))

/-- Proposition 6 at one finite scale, with an epsilon cardinality error. -/
def MartinApproximationAt (r : ℚ) (x : ℕ) (eps : ℝ) : Prop :=
  ∃ R : ℕ, Nonempty (ApproximationCertificate r x R) ∧
    |(R : ℝ) / x - martinDensity r| < eps

/-- The epsilon form of Martin's approximate-representation proposition. -/
def HasMartinApproximation (r : ℚ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    MartinApproximationAt r x eps

/-- A nonnegative normalized error rate tending to zero supplies the epsilon interface. -/
theorem hasMartinApproximation_of_rate
    {r : ℚ} {rate : ℕ → ℝ}
    (hrate : ∀ eps : ℝ, 0 < eps → ∃ X : ℕ, ∀ x : ℕ, X ≤ x → rate x < eps)
    (hcert : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∃ R : ℕ, Nonempty (ApproximationCertificate r x R) ∧
        |(R : ℝ) / x - martinDensity r| ≤ rate x) :
    HasMartinApproximation r := by
  intro eps heps
  obtain ⟨X₁, hX₁⟩ := hrate eps heps
  obtain ⟨X₀, hX₀⟩ := hcert
  refine ⟨max X₀ X₁, fun x hx ↦ ?_⟩
  obtain ⟨R, C, hR⟩ := hX₀ x ((le_max_left _ _).trans hx)
  exact ⟨R, C, hR.trans_lt (hX₁ x ((le_max_right _ _).trans hx))⟩

/-- The filter form of the epsilon interface, convenient for later asymptotic wrappers. -/
lemma hasMartinApproximation_iff_eventually (r : ℚ) :
    HasMartinApproximation r ↔
      ∀ eps : ℝ, 0 < eps → ∀ᶠ x : ℕ in atTop, MartinApproximationAt r x eps := by
  constructor
  · intro h eps heps
    obtain ⟨X, hX⟩ := h eps heps
    filter_upwards [eventually_ge_atTop X] with x hx
    exact hX x hx
  · intro h eps heps
    have he := h eps heps
    rw [eventually_atTop] at he
    exact he

end

end Erdos285

#print axioms Erdos285.ValidApproximationRun.rec_sum_run
#print axioms Erdos285.ValidApproximationRun.card_run
#print axioms Erdos285.exists_exact_card_extension
#print axioms Erdos285.exists_exact_card_extension_after_run
#print axioms Erdos285.approximationCertificate_of_valid_run
#print axioms Erdos285.hasMartinApproximation_of_rate

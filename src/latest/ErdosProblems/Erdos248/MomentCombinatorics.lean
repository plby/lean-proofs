import Mathlib

/-!
# Erdős Problem 248: finite weighted moment combinatorics

This file is the purely algebraic part of the moment argument.  It deliberately
uses finite weighted sums rather than normalized expectations.  Consequently
the Markov inequalities are division-free and remain useful before positivity
of the total sieve mass has been established.

The final section gives a fourth-moment transfer principle.  Expanding four
centered indicators produces sixteen joint-event terms.  Every such event
involves at most four *distinct* indices; repetitions in the ordered
quadruple are removed by `selectedIndices`.  Thus a joint-event estimate for
sets of at most four indices is exactly the hypothesis needed by the API.
-/

noncomputable section

open scoped BigOperators

namespace Erdos248

local instance momentCombinatoricsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Weighted sums, masses, and moments -/

/-- The real-valued indicator of a proposition. -/
def realIndicator (P : Prop) : ℝ := if P then 1 else 0

@[simp] theorem realIndicator_of_true {P : Prop} (hP : P) :
    realIndicator P = 1 := by
  simp [realIndicator, hP]

@[simp] theorem realIndicator_of_false {P : Prop} (hP : ¬P) :
    realIndicator P = 0 := by
  simp [realIndicator, hP]

theorem realIndicator_nonneg (P : Prop) : 0 ≤ realIndicator P := by
  by_cases hP : P <;> simp [hP]

theorem realIndicator_mul (P Q : Prop) :
    realIndicator P * realIndicator Q = realIndicator (P ∧ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem realIndicator_pow {P : Prop} {m : ℕ} (hm : 0 < m) :
    realIndicator P ^ m = realIndicator P := by
  by_cases hP : P <;> simp [hP, hm.ne']

/-- An unnormalized weighted sum over a finite sample. -/
def weightedSum {Ω : Type*} (s : Finset Ω) (w F : Ω → ℝ) : ℝ :=
  ∑ x ∈ s, w x * F x

/-- The unnormalized weighted mass of an event. -/
def weightedMass {Ω : Type*} (s : Finset Ω) (w : Ω → ℝ)
    (P : Ω → Prop) : ℝ :=
  weightedSum s w (fun x ↦ realIndicator (P x))

/-- An unnormalized weighted raw moment. -/
def weightedMoment {Ω : Type*} (s : Finset Ω) (w Z : Ω → ℝ)
    (m : ℕ) : ℝ :=
  weightedSum s w (fun x ↦ Z x ^ m)

abbrev weightedSecondMoment {Ω : Type*} (s : Finset Ω)
    (w Z : Ω → ℝ) : ℝ :=
  weightedMoment s w Z 2

abbrev weightedFourthMoment {Ω : Type*} (s : Finset Ω)
    (w Z : Ω → ℝ) : ℝ :=
  weightedMoment s w Z 4

theorem weightedSum_nonneg {Ω : Type*} {s : Finset Ω} {w F : Ω → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hF : ∀ x ∈ s, 0 ≤ F x) :
    0 ≤ weightedSum s w F := by
  exact Finset.sum_nonneg fun x hx ↦ mul_nonneg (hw x hx) (hF x hx)

theorem weightedMass_nonneg {Ω : Type*} {s : Finset Ω} {w : Ω → ℝ}
    (P : Ω → Prop) (hw : ∀ x ∈ s, 0 ≤ w x) :
    0 ≤ weightedMass s w P :=
  weightedSum_nonneg hw fun x _ ↦ realIndicator_nonneg (P x)

theorem weightedSum_sum {Ω ι : Type*} (s : Finset Ω) (I : Finset ι)
    (w : Ω → ℝ) (F : ι → Ω → ℝ) :
    weightedSum s w (fun x ↦ ∑ i ∈ I, F i x) =
      ∑ i ∈ I, weightedSum s w (F i) := by
  classical
  unfold weightedSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem weightedSum_const_mul {Ω : Type*} (s : Finset Ω) (w F : Ω → ℝ)
    (c : ℝ) :
    weightedSum s w (fun x ↦ c * F x) = c * weightedSum s w F := by
  unfold weightedSum
  calc
    (∑ x ∈ s, w x * (c * F x)) = ∑ x ∈ s, c * (w x * F x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = c * ∑ x ∈ s, w x * F x := by rw [Finset.mul_sum]

/-! ## Division-free weighted Markov inequalities -/

/-- Square-moment Markov, without division by the threshold or total mass. -/
theorem sq_mul_weightedMass_threshold_abs_le_secondMoment
    {Ω : Type*} {s : Finset Ω} {w Z : Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hw : ∀ x ∈ s, 0 ≤ w x) :
    t ^ 2 * weightedMass s w (fun x ↦ t ≤ |Z x|) ≤
      weightedSecondMoment s w Z := by
  change t ^ 2 * weightedMass s w (fun x ↦ t ≤ |Z x|) ≤
    weightedMoment s w Z 2
  unfold weightedMass weightedMoment weightedSum
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hbad : t ≤ |Z x|
  · rw [realIndicator_of_true hbad]
    have hsq : t ^ 2 ≤ Z x ^ 2 := by
      calc
        t ^ 2 ≤ |Z x| ^ 2 := pow_le_pow_left₀ ht hbad 2
        _ = Z x ^ 2 := sq_abs (Z x)
    nlinarith [mul_le_mul_of_nonneg_left hsq (hw x hx)]
  · rw [realIndicator_of_false hbad]
    simpa using mul_nonneg (hw x hx) (sq_nonneg (Z x))

/-- Fourth-moment Markov, without division by the threshold or total mass. -/
theorem fourth_mul_weightedMass_threshold_abs_le_fourthMoment
    {Ω : Type*} {s : Finset Ω} {w Z : Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hw : ∀ x ∈ s, 0 ≤ w x) :
    t ^ 4 * weightedMass s w (fun x ↦ t ≤ |Z x|) ≤
      weightedFourthMoment s w Z := by
  change t ^ 4 * weightedMass s w (fun x ↦ t ≤ |Z x|) ≤
    weightedMoment s w Z 4
  unfold weightedMass weightedMoment weightedSum
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hbad : t ≤ |Z x|
  · rw [realIndicator_of_true hbad]
    have hpow : t ^ 4 ≤ Z x ^ 4 := by
      calc
        t ^ 4 ≤ |Z x| ^ 4 := pow_le_pow_left₀ ht hbad 4
        _ = Z x ^ 4 := Even.pow_abs (by norm_num) (Z x)
    nlinarith [mul_le_mul_of_nonneg_left hpow (hw x hx)]
  · rw [realIndicator_of_false hbad]
    have hnonneg : 0 ≤ Z x ^ 4 := by positivity
    simpa using mul_nonneg (hw x hx) hnonneg

/-! ## Exact indicator-moment expansions -/

/-- Ordered `m`-tuples drawn from `I`. -/
def indexTuples {ι : Type*} (m : ℕ) (I : Finset ι) : Finset (Fin m → ι) :=
  Fintype.piFinset fun _ : Fin m ↦ I

/-- The conjunction of the events selected by an ordered tuple. -/
def tupleEvent {ι Ω : Type*} {m : ℕ} (P : ι → Ω → Prop)
    (q : Fin m → ι) (x : Ω) : Prop :=
  ∀ r, P (q r) x

theorem prod_realIndicator_eq_tupleEvent
    {ι Ω : Type*} {m : ℕ} (P : ι → Ω → Prop)
    (q : Fin m → ι) (x : Ω) :
    (∏ r, realIndicator (P (q r) x)) = realIndicator (tupleEvent P q x) := by
  classical
  by_cases h : ∀ r, P (q r) x
  · simp [tupleEvent, h]
  · have htuple : ¬tupleEvent P q x := by simpa [tupleEvent] using h
    obtain ⟨r, hr⟩ := not_forall.mp h
    have hz : realIndicator (P (q r) x) = 0 := realIndicator_of_false hr
    rw [realIndicator_of_false htuple]
    exact Finset.prod_eq_zero (Finset.mem_univ r) hz

/-- Exact expansion of a weighted moment of a finite indicator sum. -/
theorem weightedMoment_indicatorSum_eq_tupleMass
    {Ω ι : Type*} (s : Finset Ω) (I : Finset ι) (w : Ω → ℝ)
    (a : ι → ℝ) (P : ι → Ω → Prop) (m : ℕ) :
    weightedMoment s w
        (fun x ↦ ∑ i ∈ I, a i * realIndicator (P i x)) m =
      ∑ q ∈ indexTuples m I,
        (∏ r, a (q r)) * weightedMass s w (tupleEvent P q) := by
  classical
  unfold weightedMoment
  calc
    weightedSum s w
        (fun x ↦ (∑ i ∈ I, a i * realIndicator (P i x)) ^ m) =
        weightedSum s w (fun x ↦
          ∑ q ∈ indexTuples m I,
            (∏ r, a (q r)) * realIndicator (tupleEvent P q x)) := by
      apply congrArg (weightedSum s w)
      funext x
      rw [Finset.sum_pow']
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.prod_mul_distrib, prod_realIndicator_eq_tupleEvent]
    _ = ∑ q ∈ indexTuples m I,
        weightedSum s w (fun x ↦
          (∏ r, a (q r)) * realIndicator (tupleEvent P q x)) :=
      weightedSum_sum s (indexTuples m I) w _
    _ = ∑ q ∈ indexTuples m I,
        (∏ r, a (q r)) * weightedMass s w (tupleEvent P q) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [weightedSum_const_mul]
      rfl

/-- The exact weighted square expansion, stated separately for convenient use. -/
theorem weightedSecondMoment_indicatorSum_eq_pairMass
    {Ω ι : Type*} (s : Finset Ω) (I : Finset ι) (w : Ω → ℝ)
    (a : ι → ℝ) (P : ι → Ω → Prop) :
    weightedSecondMoment s w
        (fun x ↦ ∑ i ∈ I, a i * realIndicator (P i x)) =
      ∑ q ∈ indexTuples 2 I,
        (∏ r, a (q r)) * weightedMass s w (tupleEvent P q) :=
  weightedMoment_indicatorSum_eq_tupleMass s I w a P 2

/-- An upper square expansion obtained by bounding each pair-event mass. -/
theorem weightedSecondMoment_indicatorSum_le_pairBound
    {Ω ι : Type*} (s : Finset Ω) (I : Finset ι) (w : Ω → ℝ)
    (a : ι → ℝ) (P : ι → Ω → Prop)
    (B : (Fin 2 → ι) → ℝ) (ha : ∀ i ∈ I, 0 ≤ a i)
    (hB : ∀ q ∈ indexTuples 2 I, weightedMass s w (tupleEvent P q) ≤ B q) :
    weightedSecondMoment s w
        (fun x ↦ ∑ i ∈ I, a i * realIndicator (P i x)) ≤
      ∑ q ∈ indexTuples 2 I, (∏ r, a (q r)) * B q := by
  rw [weightedSecondMoment_indicatorSum_eq_pairMass]
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left (hB q hq)
  apply Finset.prod_nonneg
  intro r hr
  apply ha
  exact (Fintype.mem_piFinset.mp hq) r

/-! ## Centered fourth moments from joint-event estimates -/

/-- The centered indicator `1_P - p`. -/
def centeredIndicator (p : ℝ) (P : Prop) : ℝ := realIndicator P - p

/-- A finite linear combination of centered indicators. -/
def centeredIndicatorSum {ι Ω : Type*} (I : Finset ι) (a p : ι → ℝ)
    (P : ι → Ω → Prop) (x : Ω) : ℝ :=
  ∑ i ∈ I, a i * centeredIndicator (p i) (P i x)

/-- The distinct indices selected by the positions in `T`. -/
def selectedIndices {ι : Type*} (q : Fin 4 → ι) (T : Finset (Fin 4)) :
    Finset ι := T.image q

/-- The coefficient of a joint event in the expansion of four centered
indicators.  Positions in `T` supply their indicator term; the complementary
positions supply `-p`. -/
def centeredExpansionCoefficient {ι : Type*} (p : ι → ℝ)
    (q : Fin 4 → ι) (T : Finset (Fin 4)) : ℝ :=
  ∏ r ∈ Tᶜ, -p (q r)

/-- The conjunction attached to a chosen set of positions. -/
def selectedEvent {ι Ω : Type*} (P : ι → Ω → Prop)
    (q : Fin 4 → ι) (T : Finset (Fin 4)) (x : Ω) : Prop :=
  ∀ i ∈ selectedIndices q T, P i x

theorem prod_realIndicator_selected_eq_selectedEvent
    {ι Ω : Type*} (P : ι → Ω → Prop) (q : Fin 4 → ι)
    (T : Finset (Fin 4)) (x : Ω) :
    (∏ r ∈ T, realIndicator (P (q r) x)) =
      realIndicator (selectedEvent P q T x) := by
  classical
  by_cases h : ∀ r ∈ T, P (q r) x
  · have hs : selectedEvent P q T x := by
      intro i hi
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
      exact h r hr
    rw [realIndicator_of_true hs]
    apply Finset.prod_eq_one
    intro r hrT
    exact realIndicator_of_true (h r hrT)
  · simp only [not_forall] at h
    obtain ⟨r, hrT, hr⟩ := h
    have hs : ¬selectedEvent P q T x := by
      intro hs
      exact hr (hs (q r) (Finset.mem_image.mpr ⟨r, hrT, rfl⟩))
    rw [realIndicator_of_false hs]
    exact Finset.prod_eq_zero hrT (realIndicator_of_false hr)

/-- Inclusion--exclusion expansion of a product of four centered indicators. -/
theorem prod_centeredIndicator_eq_selectedEventExpansion
    {ι Ω : Type*} (p : ι → ℝ) (P : ι → Ω → Prop)
    (q : Fin 4 → ι) (x : Ω) :
    (∏ r, centeredIndicator (p (q r)) (P (q r) x)) =
      ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
        realIndicator (selectedEvent P q T x) := by
  classical
  unfold centeredIndicator centeredExpansionCoefficient
  rw [show (∏ r, (realIndicator (P (q r) x) - p (q r))) =
      ∏ r, (realIndicator (P (q r) x) + -p (q r)) by
        apply Finset.prod_congr rfl
        intro r hr
        ring]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  rw [prod_realIndicator_selected_eq_selectedEvent]
  ring

/-- The exact joint-event expansion of the weighted centered fourth moment. -/
theorem weightedFourthMoment_centeredIndicatorSum_eq_jointExpansion
    {Ω ι : Type*} (s : Finset Ω) (I : Finset ι) (w : Ω → ℝ)
    (a p : ι → ℝ) (P : ι → Ω → Prop) :
    weightedFourthMoment s w (centeredIndicatorSum I a p P) =
      ∑ q ∈ indexTuples 4 I, (∏ r, a (q r)) *
        ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
          weightedMass s w (selectedEvent P q T) := by
  classical
  change weightedMoment s w (centeredIndicatorSum I a p P) 4 = _
  unfold weightedMoment centeredIndicatorSum
  calc
    weightedSum s w (fun x ↦
        (∑ i ∈ I, a i * centeredIndicator (p i) (P i x)) ^ 4) =
        weightedSum s w (fun x ↦
          ∑ q ∈ indexTuples 4 I, (∏ r, a (q r)) *
            ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
              realIndicator (selectedEvent P q T x)) := by
      apply congrArg (weightedSum s w)
      funext x
      rw [Finset.sum_pow']
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.prod_mul_distrib,
        prod_centeredIndicator_eq_selectedEventExpansion]
    _ = ∑ q ∈ indexTuples 4 I,
        weightedSum s w (fun x ↦ (∏ r, a (q r)) *
          ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
            realIndicator (selectedEvent P q T x)) :=
      weightedSum_sum s (indexTuples 4 I) w _
    _ = ∑ q ∈ indexTuples 4 I, (∏ r, a (q r)) *
        ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
          weightedMass s w (selectedEvent P q T) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [weightedSum_const_mul, weightedSum_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro T hT
      rw [weightedSum_const_mul]
      rfl

/-- The model fourth moment obtained by replacing each joint-event mass with
`M * ∏ i in J, p i`. -/
def jointModelCenteredFourth {ι : Type*} (I : Finset ι) (a p : ι → ℝ)
    (M : ℝ) : ℝ :=
  ∑ q ∈ indexTuples 4 I, (∏ r, a (q r)) *
    ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
      (M * ∏ i ∈ selectedIndices q T, p i)

/-- The explicit accumulated error in the centered fourth-moment transfer. -/
def jointCenteredFourthError {ι : Type*} (I : Finset ι) (a p : ι → ℝ)
    (err : Finset ι → ℝ) : ℝ :=
  ∑ q ∈ indexTuples 4 I, |∏ r, a (q r)| *
    ∑ T : Finset (Fin 4), |centeredExpansionCoefficient p q T| *
      err (selectedIndices q T)

theorem selectedIndices_subset_of_mem_indexTuples
    {ι : Type*} {I : Finset ι} {q : Fin 4 → ι}
    (hq : q ∈ indexTuples 4 I) (T : Finset (Fin 4)) :
    selectedIndices q T ⊆ I := by
  intro i hi
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
  exact (Fintype.mem_piFinset.mp hq) r

theorem selectedIndices_card_le_four {ι : Type*}
    (q : Fin 4 → ι) (T : Finset (Fin 4)) :
    (selectedIndices q T).card ≤ 4 := by
  calc
    (selectedIndices q T).card ≤ T.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_le_card (Finset.subset_univ T)
    _ = 4 := Fintype.card_fin 4

/-- Transfer of a centered fourth moment from joint-event estimates for at
most four distinct indices.  No sign assumption is imposed on the
coefficients or on the centering parameters. -/
theorem abs_weightedFourthMoment_sub_jointModel_le
    {Ω ι : Type*} (s : Finset Ω) (I : Finset ι) (w : Ω → ℝ)
    (a p : ι → ℝ) (P : ι → Ω → Prop) (M : ℝ)
    (err : Finset ι → ℝ)
    (hjoint : ∀ J : Finset ι, J ⊆ I → J.card ≤ 4 →
      |weightedMass s w (fun x ↦ ∀ i ∈ J, P i x) -
        M * ∏ i ∈ J, p i| ≤ err J) :
    |weightedFourthMoment s w (centeredIndicatorSum I a p P) -
        jointModelCenteredFourth I a p M| ≤
      jointCenteredFourthError I a p err := by
  classical
  rw [weightedFourthMoment_centeredIndicatorSum_eq_jointExpansion]
  unfold jointModelCenteredFourth jointCenteredFourthError
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ q ∈ indexTuples 4 I,
        ((∏ r, a (q r)) *
            ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
              weightedMass s w (selectedEvent P q T) -
          (∏ r, a (q r)) *
            ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
              (M * ∏ i ∈ selectedIndices q T, p i))| ≤
        ∑ q ∈ indexTuples 4 I,
          |(∏ r, a (q r)) *
              ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
                (weightedMass s w (selectedEvent P q T) -
                  M * ∏ i ∈ selectedIndices q T, p i)| := by
      have hrearrange :
          (∑ q ∈ indexTuples 4 I,
            ((∏ r, a (q r)) *
                ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
                  weightedMass s w (selectedEvent P q T) -
              (∏ r, a (q r)) *
                ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
                  (M * ∏ i ∈ selectedIndices q T, p i))) =
          ∑ q ∈ indexTuples 4 I,
            (∏ r, a (q r)) *
              ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
                (weightedMass s w (selectedEvent P q T) -
                  M * ∏ i ∈ selectedIndices q T, p i) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← mul_sub]
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      rw [hrearrange]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ indexTuples 4 I, |∏ r, a (q r)| *
          ∑ T : Finset (Fin 4), |centeredExpansionCoefficient p q T| *
            err (selectedIndices q T) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
            (weightedMass s w (selectedEvent P q T) -
              M * ∏ i ∈ selectedIndices q T, p i)| ≤
            ∑ T : Finset (Fin 4),
              |centeredExpansionCoefficient p q T *
                (weightedMass s w (selectedEvent P q T) -
                  M * ∏ i ∈ selectedIndices q T, p i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ T : Finset (Fin 4), |centeredExpansionCoefficient p q T| *
              err (selectedIndices q T) := by
          apply Finset.sum_le_sum
          intro T hT
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have happ := hjoint (selectedIndices q T)
            (selectedIndices_subset_of_mem_indexTuples hq T)
            (selectedIndices_card_le_four q T)
          change |weightedMass s w (fun x ↦ ∀ i ∈ selectedIndices q T, P i x) -
            M * ∏ i ∈ selectedIndices q T, p i| ≤ err (selectedIndices q T)
          exact happ

/-! ## The independent Bernoulli realization of the model -/

/-- Product Bernoulli weight on the powerset of `I`.  The definition is
algebraic and makes sense without assumptions on `p`. -/
def bernoulliWeight {ι : Type*} (I : Finset ι) (p : ι → ℝ)
    (B : Finset ι) : ℝ :=
  (∏ i ∈ B, p i) * ∏ i ∈ I \ B, (1 - p i)

/-- Expectation under the explicit product Bernoulli weights. -/
def bernoulliExpectation {ι : Type*} (I : Finset ι) (p : ι → ℝ)
    (F : Finset ι → ℝ) : ℝ :=
  ∑ B ∈ I.powerset, bernoulliWeight I p B * F B

/-- The coefficient-weighted centered sum on a Bernoulli subset. -/
def bernoulliCenteredSum {ι : Type*} (I : Finset ι) (a p : ι → ℝ)
    (B : Finset ι) : ℝ :=
  ∑ i ∈ I, a i * (realIndicator (i ∈ B) - p i)

theorem sum_bernoulliWeight {ι : Type*} (I : Finset ι) (p : ι → ℝ) :
    ∑ B ∈ I.powerset, bernoulliWeight I p B = 1 := by
  classical
  unfold bernoulliWeight
  rw [← Finset.prod_add (fun i ↦ p i) (fun i ↦ 1 - p i) I]
  simp

/-- Every joint event has exactly its product-model mass. -/
theorem weightedMass_bernoulliWeight_jointEvent
    {ι : Type*} {I J : Finset ι} (p : ι → ℝ) (hJI : J ⊆ I) :
    weightedMass I.powerset (bernoulliWeight I p) (fun B ↦ J ⊆ B) =
      ∏ i ∈ J, p i := by
  classical
  unfold weightedMass weightedSum
  calc
    (∑ B ∈ I.powerset,
        bernoulliWeight I p B * realIndicator (J ⊆ B)) =
        ∑ B ∈ I.powerset,
          (∏ i ∈ B, p i) *
            ∏ i ∈ I \ B, (if i ∈ J then 0 else 1 - p i) := by
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hJB : J ⊆ B
      · rw [realIndicator_of_true hJB]
        unfold bernoulliWeight
        rw [mul_one]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg]
        intro hiJ
        exact (Finset.mem_sdiff.mp hi).2 (hJB hiJ)
      · rw [realIndicator_of_false hJB, mul_zero]
        obtain ⟨i, hiJ, hiB⟩ := SetLike.not_le_iff_exists.mp hJB
        have hiI : i ∈ I := hJI hiJ
        have hiDiff : i ∈ I \ B := Finset.mem_sdiff.mpr ⟨hiI, hiB⟩
        rw [Finset.prod_eq_zero hiDiff]
        · rw [mul_zero]
        · exact if_pos hiJ
    _ = ∏ i ∈ I, (p i + if i ∈ J then 0 else 1 - p i) := by
      exact (Finset.prod_add (fun i ↦ p i)
        (fun i ↦ if i ∈ J then 0 else 1 - p i) I).symm
    _ = ∏ i ∈ J, p i := by
      calc
        (∏ i ∈ I, (p i + if i ∈ J then 0 else 1 - p i)) =
            ∏ i ∈ I, if i ∈ J then p i else 1 := by
          apply Finset.prod_congr rfl
          intro i hi
          by_cases hiJ : i ∈ J <;> simp [hiJ]
        _ = ∏ i ∈ J, p i := by
          rw [Finset.prod_ite]
          simp only [Finset.prod_const_one, mul_one]
          congr 1
          ext i
          simp only [Finset.mem_filter]
          constructor
          · exact fun hi ↦ hi.2
          · exact fun hi ↦ ⟨hJI hi, hi⟩

theorem centeredIndicator_mem_eq {ι : Type*} (p : ι → ℝ)
    (i : ι) (B : Finset ι) :
    centeredIndicator (p i) (i ∈ B) = realIndicator (i ∈ B) - p i := rfl

/-- The algebraic joint-event model is exactly the fourth moment of the
independent product Bernoulli law, scaled by `M`. -/
theorem jointModelCenteredFourth_eq_bernoulliExpectation
    {ι : Type*} (I : Finset ι) (a p : ι → ℝ) (M : ℝ) :
    jointModelCenteredFourth I a p M =
      M * bernoulliExpectation I p
        (fun B ↦ bernoulliCenteredSum I a p B ^ 4) := by
  classical
  have hexpand := weightedFourthMoment_centeredIndicatorSum_eq_jointExpansion
    I.powerset I (bernoulliWeight I p) a p (fun i B ↦ i ∈ B)
  have hleft :
      weightedFourthMoment I.powerset (bernoulliWeight I p)
          (centeredIndicatorSum I a p (fun i B ↦ i ∈ B)) =
        bernoulliExpectation I p (fun B ↦ bernoulliCenteredSum I a p B ^ 4) := by
    rfl
  rw [hleft] at hexpand
  unfold jointModelCenteredFourth
  calc
    (∑ q ∈ indexTuples 4 I, (∏ r, a (q r)) *
        ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
          (M * ∏ i ∈ selectedIndices q T, p i)) =
        M * (∑ q ∈ indexTuples 4 I, (∏ r, a (q r)) *
          ∑ T : Finset (Fin 4), centeredExpansionCoefficient p q T *
            (∏ i ∈ selectedIndices q T, p i)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = M * bernoulliExpectation I p
        (fun B ↦ bernoulliCenteredSum I a p B ^ 4) := by
      congr 1
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      apply Finset.sum_congr rfl
      intro T hT
      change centeredExpansionCoefficient p q T *
          (∏ i ∈ selectedIndices q T, p i) =
        centeredExpansionCoefficient p q T *
          weightedMass I.powerset (bernoulliWeight I p)
            (fun B ↦ selectedIndices q T ⊆ B)
      rw [weightedMass_bernoulliWeight_jointEvent p
        (selectedIndices_subset_of_mem_indexTuples hq T)]

/-! ## The independent fourth-moment bound -/

theorem bernoulliWeight_insert_notMem {ι : Type*} {I B : Finset ι}
    {e : ι} (p : ι → ℝ) (heI : e ∉ I) (hBI : B ⊆ I) :
    bernoulliWeight (insert e I) p B =
      (1 - p e) * bernoulliWeight I p B := by
  classical
  have heB : e ∉ B := fun heB ↦ heI (hBI heB)
  have hdiff : insert e I \ B = insert e (I \ B) := by
    ext i
    by_cases hie : i = e
    · subst i
      simp [heI, heB]
    · simp [hie]
  unfold bernoulliWeight
  rw [hdiff, Finset.prod_insert]
  · ring
  · simp [heI]

theorem bernoulliWeight_insert_mem {ι : Type*} {I B : Finset ι}
    {e : ι} (p : ι → ℝ) (heI : e ∉ I) (hBI : B ⊆ I) :
    bernoulliWeight (insert e I) p (insert e B) =
      p e * bernoulliWeight I p B := by
  classical
  have heB : e ∉ B := fun heB ↦ heI (hBI heB)
  have hdiff : insert e I \ insert e B = I \ B := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hi, hnot⟩
      exact ⟨hi.resolve_left (fun hie ↦ hnot (Or.inl hie)),
        fun hiB ↦ hnot (Or.inr hiB)⟩
    · rintro ⟨hiI, hiB⟩
      have hie : i ≠ e := fun hie ↦ heI (hie ▸ hiI)
      exact ⟨Or.inr hiI, fun hi ↦ hi.elim hie hiB⟩
  unfold bernoulliWeight
  rw [Finset.prod_insert heB, hdiff]
  ring

/-- Split a Bernoulli expectation according to one newly inserted
coordinate. -/
theorem bernoulliExpectation_insert {ι : Type*} {I : Finset ι}
    {e : ι} (p : ι → ℝ) (F : Finset ι → ℝ) (heI : e ∉ I) :
    bernoulliExpectation (insert e I) p F =
      (1 - p e) * bernoulliExpectation I p F +
        p e * bernoulliExpectation I p (fun B ↦ F (insert e B)) := by
  classical
  unfold bernoulliExpectation
  rw [Finset.sum_powerset_insert heI]
  calc
    (∑ B ∈ I.powerset, bernoulliWeight (insert e I) p B * F B) +
        ∑ B ∈ I.powerset,
          bernoulliWeight (insert e I) p (insert e B) * F (insert e B) =
      (∑ B ∈ I.powerset,
          (1 - p e) * (bernoulliWeight I p B * F B)) +
        ∑ B ∈ I.powerset,
          p e * (bernoulliWeight I p B * F (insert e B)) := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro B hB
        rw [bernoulliWeight_insert_notMem p heI
          (Finset.mem_powerset.mp hB)]
        ring
      · apply Finset.sum_congr rfl
        intro B hB
        rw [bernoulliWeight_insert_mem p heI
          (Finset.mem_powerset.mp hB)]
        ring
    _ = (1 - p e) *
          (∑ B ∈ I.powerset, bernoulliWeight I p B * F B) +
        p e * (∑ B ∈ I.powerset,
          bernoulliWeight I p B * F (insert e B)) := by
      rw [Finset.mul_sum, Finset.mul_sum]

theorem bernoulliExpectation_congr {ι : Type*} {I : Finset ι}
    (p : ι → ℝ) {F G : Finset ι → ℝ}
    (h : ∀ B ⊆ I, F B = G B) :
    bernoulliExpectation I p F = bernoulliExpectation I p G := by
  classical
  unfold bernoulliExpectation
  apply Finset.sum_congr rfl
  intro B hB
  rw [h B (Finset.mem_powerset.mp hB)]

theorem bernoulliExpectation_linear_combination {ι : Type*}
    (I : Finset ι) (p : ι → ℝ) (F G : Finset ι → ℝ) (c d : ℝ) :
    c * bernoulliExpectation I p F + d * bernoulliExpectation I p G =
      bernoulliExpectation I p (fun B ↦ c * F B + d * G B) := by
  classical
  unfold bernoulliExpectation
  simp_rw [Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) <;>
    apply Finset.sum_congr rfl <;>
    intro B hB <;> ring

theorem bernoulliCenteredSum_insert_notMem {ι : Type*} {I B : Finset ι}
    {e : ι} (a p : ι → ℝ) (heI : e ∉ I) (hBI : B ⊆ I) :
    bernoulliCenteredSum (insert e I) a p B =
      bernoulliCenteredSum I a p B - a e * p e := by
  classical
  have heB : e ∉ B := fun heB ↦ heI (hBI heB)
  unfold bernoulliCenteredSum
  rw [Finset.sum_insert heI, realIndicator_of_false heB]
  ring

theorem bernoulliCenteredSum_insert_mem {ι : Type*} {I B : Finset ι}
    {e : ι} (a p : ι → ℝ) (heI : e ∉ I) (hBI : B ⊆ I) :
    bernoulliCenteredSum (insert e I) a p (insert e B) =
      bernoulliCenteredSum I a p B + a e * (1 - p e) := by
  classical
  have heB : e ∉ B := fun heB ↦ heI (hBI heB)
  unfold bernoulliCenteredSum
  rw [Finset.sum_insert heI, realIndicator_of_true (Finset.mem_insert_self e B)]
  have hsum :
      (∑ i ∈ I, a i * (realIndicator (i ∈ insert e B) - p i)) =
        ∑ i ∈ I, a i * (realIndicator (i ∈ B) - p i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hie : i ≠ e := fun hie ↦ heI (hie ▸ hi)
    simp [hie]
  rw [hsum]
  ring

/-- Raw centered moment in the independent Bernoulli model. -/
def bernoulliCenteredMoment {ι : Type*} (I : Finset ι) (a p : ι → ℝ)
    (m : ℕ) : ℝ :=
  bernoulliExpectation I p (fun B ↦ bernoulliCenteredSum I a p B ^ m)

theorem bernoulliCenteredMoment_insert {ι : Type*} {I : Finset ι}
    {e : ι} (a p : ι → ℝ) (m : ℕ) (heI : e ∉ I) :
    bernoulliCenteredMoment (insert e I) a p m =
      (1 - p e) * bernoulliExpectation I p
        (fun B ↦ (bernoulliCenteredSum I a p B - a e * p e) ^ m) +
      p e * bernoulliExpectation I p
        (fun B ↦ (bernoulliCenteredSum I a p B + a e * (1 - p e)) ^ m) := by
  classical
  unfold bernoulliCenteredMoment
  rw [bernoulliExpectation_insert p _ heI]
  apply congrArg₂ (· + ·)
  · congr 1
    apply bernoulliExpectation_congr
    intro B hBI
    rw [bernoulliCenteredSum_insert_notMem a p heI hBI]
  · congr 1
    apply bernoulliExpectation_congr
    intro B hBI
    rw [bernoulliCenteredSum_insert_mem a p heI hBI]

theorem bernoulliCenteredMoment_one_eq_zero {ι : Type*}
    (I : Finset ι) (a p : ι → ℝ) :
    bernoulliCenteredMoment I a p 1 = 0 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bernoulliCenteredMoment, bernoulliExpectation,
      bernoulliCenteredSum, bernoulliWeight]
  | @insert e I heI ih =>
      rw [bernoulliCenteredMoment_insert a p 1 heI,
        bernoulliExpectation_linear_combination]
      calc
        bernoulliExpectation I p (fun B ↦
            (1 - p e) * (bernoulliCenteredSum I a p B - a e * p e) ^ 1 +
              p e * (bernoulliCenteredSum I a p B +
                a e * (1 - p e)) ^ 1) =
            bernoulliCenteredMoment I a p 1 := by
          unfold bernoulliCenteredMoment
          apply bernoulliExpectation_congr
          intro B hBI
          ring
        _ = 0 := ih

/-- Exact variance of the centered coefficient-weighted Bernoulli sum. -/
theorem bernoulliCenteredMoment_two_eq {ι : Type*}
    (I : Finset ι) (a p : ι → ℝ) :
    bernoulliCenteredMoment I a p 2 =
      ∑ i ∈ I, a i ^ 2 * p i * (1 - p i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bernoulliCenteredMoment, bernoulliExpectation,
      bernoulliCenteredSum, bernoulliWeight]
  | @insert e I heI ih =>
      rw [bernoulliCenteredMoment_insert a p 2 heI,
        bernoulliExpectation_linear_combination]
      have hcombine :
          bernoulliExpectation I p (fun B ↦
              (1 - p e) * (bernoulliCenteredSum I a p B - a e * p e) ^ 2 +
                p e * (bernoulliCenteredSum I a p B +
                  a e * (1 - p e)) ^ 2) =
            bernoulliCenteredMoment I a p 2 +
              a e ^ 2 * p e * (1 - p e) := by
        unfold bernoulliCenteredMoment bernoulliExpectation
        calc
          (∑ B ∈ I.powerset, bernoulliWeight I p B *
              ((1 - p e) * (bernoulliCenteredSum I a p B - a e * p e) ^ 2 +
                p e * (bernoulliCenteredSum I a p B +
                  a e * (1 - p e)) ^ 2)) =
              (∑ B ∈ I.powerset, bernoulliWeight I p B *
                bernoulliCenteredSum I a p B ^ 2) +
              a e ^ 2 * p e * (1 - p e) *
                (∑ B ∈ I.powerset, bernoulliWeight I p B) := by
            calc
              (∑ B ∈ I.powerset, bernoulliWeight I p B *
                  ((1 - p e) *
                      (bernoulliCenteredSum I a p B - a e * p e) ^ 2 +
                    p e * (bernoulliCenteredSum I a p B +
                      a e * (1 - p e)) ^ 2)) =
                  ∑ B ∈ I.powerset,
                    (bernoulliWeight I p B *
                        bernoulliCenteredSum I a p B ^ 2 +
                      bernoulliWeight I p B *
                        (a e ^ 2 * p e * (1 - p e))) := by
                apply Finset.sum_congr rfl
                intro B hB
                ring
              _ = (∑ B ∈ I.powerset, bernoulliWeight I p B *
                    bernoulliCenteredSum I a p B ^ 2) +
                  (∑ B ∈ I.powerset, bernoulliWeight I p B) *
                    (a e ^ 2 * p e * (1 - p e)) := by
                rw [Finset.sum_add_distrib, Finset.sum_mul]
              _ = (∑ B ∈ I.powerset, bernoulliWeight I p B *
                    bernoulliCenteredSum I a p B ^ 2) +
                  a e ^ 2 * p e * (1 - p e) *
                    (∑ B ∈ I.powerset, bernoulliWeight I p B) := by ring
          _ = (∑ B ∈ I.powerset, bernoulliWeight I p B *
                bernoulliCenteredSum I a p B ^ 2) +
              a e ^ 2 * p e * (1 - p e) := by
            rw [sum_bernoulliWeight, mul_one]
      rw [hcombine, ih, Finset.sum_insert heI]
      ring

/-- Exact one-coordinate fourth centered Bernoulli moment. -/
def bernoulliFourthAtom (p : ℝ) : ℝ :=
  (1 - p) * p ^ 4 + p * (1 - p) ^ 4

theorem bernoulliFourthAtom_le {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliFourthAtom p ≤ p := by
  unfold bernoulliFourthAtom
  have hnonpos : p ^ 2 * (p - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p) (sub_nonpos.mpr hp1)
  nlinarith

/-- Exact fourth-moment recursion.  It exhibits the repeated-index
contribution `bernoulliFourthAtom` and the paired-index contribution through
the previous second moment. -/
theorem bernoulliCenteredMoment_four_insert {ι : Type*} {I : Finset ι}
    {e : ι} (a p : ι → ℝ) (heI : e ∉ I) :
    bernoulliCenteredMoment (insert e I) a p 4 =
      bernoulliCenteredMoment I a p 4 +
        6 * a e ^ 2 * p e * (1 - p e) *
          bernoulliCenteredMoment I a p 2 +
        a e ^ 4 * bernoulliFourthAtom (p e) := by
  classical
  rw [bernoulliCenteredMoment_insert a p 4 heI,
    bernoulliExpectation_linear_combination]
  unfold bernoulliCenteredMoment bernoulliExpectation
  calc
    (∑ B ∈ I.powerset, bernoulliWeight I p B *
        ((1 - p e) * (bernoulliCenteredSum I a p B - a e * p e) ^ 4 +
          p e * (bernoulliCenteredSum I a p B +
            a e * (1 - p e)) ^ 4)) =
        (∑ B ∈ I.powerset, bernoulliWeight I p B *
          bernoulliCenteredSum I a p B ^ 4) +
        6 * a e ^ 2 * p e * (1 - p e) *
          (∑ B ∈ I.powerset, bernoulliWeight I p B *
            bernoulliCenteredSum I a p B ^ 2) +
        4 * a e ^ 3 * p e * (1 - p e) * (1 - 2 * p e) *
          (∑ B ∈ I.powerset, bernoulliWeight I p B *
            bernoulliCenteredSum I a p B) +
        a e ^ 4 * bernoulliFourthAtom (p e) *
          (∑ B ∈ I.powerset, bernoulliWeight I p B) := by
      calc
        (∑ B ∈ I.powerset, bernoulliWeight I p B *
            ((1 - p e) *
                (bernoulliCenteredSum I a p B - a e * p e) ^ 4 +
              p e * (bernoulliCenteredSum I a p B +
                a e * (1 - p e)) ^ 4)) =
            ∑ B ∈ I.powerset,
              (bernoulliWeight I p B *
                  bernoulliCenteredSum I a p B ^ 4 +
                (bernoulliWeight I p B *
                  bernoulliCenteredSum I a p B ^ 2) *
                    (6 * a e ^ 2 * p e * (1 - p e)) +
                (bernoulliWeight I p B *
                  bernoulliCenteredSum I a p B) *
                    (4 * a e ^ 3 * p e * (1 - p e) * (1 - 2 * p e)) +
                bernoulliWeight I p B *
                  (a e ^ 4 * bernoulliFourthAtom (p e))) := by
          apply Finset.sum_congr rfl
          intro B hB
          unfold bernoulliFourthAtom
          ring
        _ = (∑ B ∈ I.powerset, bernoulliWeight I p B *
              bernoulliCenteredSum I a p B ^ 4) +
            (∑ B ∈ I.powerset, bernoulliWeight I p B *
              bernoulliCenteredSum I a p B ^ 2) *
                (6 * a e ^ 2 * p e * (1 - p e)) +
            (∑ B ∈ I.powerset, bernoulliWeight I p B *
              bernoulliCenteredSum I a p B) *
                (4 * a e ^ 3 * p e * (1 - p e) * (1 - 2 * p e)) +
            (∑ B ∈ I.powerset, bernoulliWeight I p B) *
                (a e ^ 4 * bernoulliFourthAtom (p e)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul]
        _ = (∑ B ∈ I.powerset, bernoulliWeight I p B *
              bernoulliCenteredSum I a p B ^ 4) +
            6 * a e ^ 2 * p e * (1 - p e) *
              (∑ B ∈ I.powerset, bernoulliWeight I p B *
                bernoulliCenteredSum I a p B ^ 2) +
            4 * a e ^ 3 * p e * (1 - p e) * (1 - 2 * p e) *
              (∑ B ∈ I.powerset, bernoulliWeight I p B *
                bernoulliCenteredSum I a p B) +
            a e ^ 4 * bernoulliFourthAtom (p e) *
              (∑ B ∈ I.powerset, bernoulliWeight I p B) := by ring
    _ = (∑ B ∈ I.powerset, bernoulliWeight I p B *
          bernoulliCenteredSum I a p B ^ 4) +
        6 * a e ^ 2 * p e * (1 - p e) *
          (∑ B ∈ I.powerset, bernoulliWeight I p B *
            bernoulliCenteredSum I a p B ^ 2) +
        a e ^ 4 * bernoulliFourthAtom (p e) := by
      rw [show (∑ B ∈ I.powerset, bernoulliWeight I p B *
            bernoulliCenteredSum I a p B) = 0 by
          have hm := bernoulliCenteredMoment_one_eq_zero I a p
          unfold bernoulliCenteredMoment bernoulliExpectation at hm
          simpa [pow_one] using hm,
        sum_bernoulliWeight]
      ring

/-- Fourth moment of an independent centered Bernoulli sum.  The variance
proxy intentionally drops the factor `1-p`, giving the form used in the
sieve application. -/
theorem bernoulliCenteredMoment_four_le
    {ι : Type*} (I : Finset ι) (a p : ι → ℝ)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    bernoulliCenteredMoment I a p 4 ≤
      3 * (∑ i ∈ I, a i ^ 2 * p i) ^ 2 +
        ∑ i ∈ I, a i ^ 4 * p i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bernoulliCenteredMoment, bernoulliExpectation,
      bernoulliCenteredSum, bernoulliWeight]
  | @insert e I heI ih =>
      have hp0e : 0 ≤ p e := hp0 e (Finset.mem_insert_self e I)
      have hp1e : p e ≤ 1 := hp1 e (Finset.mem_insert_self e I)
      have hp0I : ∀ i ∈ I, 0 ≤ p i :=
        fun i hi ↦ hp0 i (Finset.mem_insert_of_mem hi)
      have hp1I : ∀ i ∈ I, p i ≤ 1 :=
        fun i hi ↦ hp1 i (Finset.mem_insert_of_mem hi)
      have hind := ih hp0I hp1I
      have hsecond := bernoulliCenteredMoment_two_eq I a p
      have hvarle : bernoulliCenteredMoment I a p 2 ≤
          ∑ i ∈ I, a i ^ 2 * p i := by
        rw [hsecond]
        apply Finset.sum_le_sum
        intro i hi
        have hpi0 := hp0I i hi
        have hpi1 := hp1I i hi
        have ha2 : 0 ≤ a i ^ 2 := sq_nonneg (a i)
        nlinarith [mul_nonneg ha2 hpi0, mul_nonneg hpi0 (sub_nonneg.mpr hpi1)]
      have hcross0 : 0 ≤ 6 * a e ^ 2 * p e * (1 - p e) := by positivity
      have hcross := mul_le_mul_of_nonneg_left hvarle hcross0
      have hatom := bernoulliFourthAtom_le hp0e hp1e
      have ha4 : 0 ≤ a e ^ 4 := by positivity
      have hatom' := mul_le_mul_of_nonneg_left hatom ha4
      rw [bernoulliCenteredMoment_four_insert a p heI,
        Finset.sum_insert heI, Finset.sum_insert heI]
      calc
        bernoulliCenteredMoment I a p 4 +
              6 * a e ^ 2 * p e * (1 - p e) *
                bernoulliCenteredMoment I a p 2 +
            a e ^ 4 * bernoulliFourthAtom (p e) ≤
            (3 * (∑ i ∈ I, a i ^ 2 * p i) ^ 2 +
                ∑ i ∈ I, a i ^ 4 * p i) +
              6 * a e ^ 2 * p e * (1 - p e) *
                (∑ i ∈ I, a i ^ 2 * p i) +
              a e ^ 4 * p e := by linarith
        _ ≤ 3 * (a e ^ 2 * p e + ∑ i ∈ I, a i ^ 2 * p i) ^ 2 +
              (a e ^ 4 * p e + ∑ i ∈ I, a i ^ 4 * p i) := by
          have hS : 0 ≤ ∑ i ∈ I, a i ^ 2 * p i := by
            apply Finset.sum_nonneg
            intro i hi
            exact mul_nonneg (sq_nonneg _) (hp0I i hi)
          have hb : 0 ≤ a e ^ 2 * p e := mul_nonneg (sq_nonneg _) hp0e
          have hone : 1 - p e ≤ 1 := by linarith
          have hsix : 0 ≤ 6 * (a e ^ 2 * p e) *
              (∑ i ∈ I, a i ^ 2 * p i) := by positivity
          have hcrossProxy :
              6 * a e ^ 2 * p e * (1 - p e) *
                  (∑ i ∈ I, a i ^ 2 * p i) ≤
                6 * (a e ^ 2 * p e) *
                  (∑ i ∈ I, a i ^ 2 * p i) := by
            calc
              6 * a e ^ 2 * p e * (1 - p e) *
                    (∑ i ∈ I, a i ^ 2 * p i) =
                  (6 * (a e ^ 2 * p e) *
                    (∑ i ∈ I, a i ^ 2 * p i)) * (1 - p e) := by ring
              _ ≤ (6 * (a e ^ 2 * p e) *
                    (∑ i ∈ I, a i ^ 2 * p i)) * 1 :=
                mul_le_mul_of_nonneg_left hone hsix
              _ = 6 * (a e ^ 2 * p e) *
                    (∑ i ∈ I, a i ^ 2 * p i) := by ring
          nlinarith [sq_nonneg (a e ^ 2 * p e)]

/-- The requested model estimate.  `M ≥ 0` is the natural case for a total
weight or main-term mass. -/
theorem jointModelCenteredFourth_le
    {ι : Type*} (I : Finset ι) (a p : ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hp0 : ∀ i ∈ I, 0 ≤ p i)
    (hp1 : ∀ i ∈ I, p i ≤ 1) :
    jointModelCenteredFourth I a p M ≤
      M * (3 * (∑ i ∈ I, a i ^ 2 * p i) ^ 2 +
        ∑ i ∈ I, a i ^ 4 * p i) := by
  rw [jointModelCenteredFourth_eq_bernoulliExpectation]
  exact mul_le_mul_of_nonneg_left
    (bernoulliCenteredMoment_four_le I a p hp0 hp1) hM

/-! ## A coarse, easy-to-sum accumulated-error bound -/

theorem abs_tupleCoefficient_le_one
    {ι : Type*} {I : Finset ι} {a : ι → ℝ} {q : Fin 4 → ι}
    (hq : q ∈ indexTuples 4 I) (ha : ∀ i ∈ I, |a i| ≤ 1) :
    |∏ r, a (q r)| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro r hr
    exact abs_nonneg _
  · intro r hr
    exact ha (q r) ((Fintype.mem_piFinset.mp hq) r)

theorem abs_centeredExpansionCoefficient_le_one
    {ι : Type*} {I : Finset ι} {p : ι → ℝ} {q : Fin 4 → ι}
    (hq : q ∈ indexTuples 4 I) (T : Finset (Fin 4))
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    |centeredExpansionCoefficient p q T| ≤ 1 := by
  unfold centeredExpansionCoefficient
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro r hr
    exact abs_nonneg _
  · intro r hr
    rw [abs_neg, abs_of_nonneg (hp0 (q r) ((Fintype.mem_piFinset.mp hq) r))]
    exact hp1 (q r) ((Fintype.mem_piFinset.mp hq) r)

theorem selectedProbabilityProduct_nonneg_le_one
    {ι : Type*} {I : Finset ι} {p : ι → ℝ} {q : Fin 4 → ι}
    (hq : q ∈ indexTuples 4 I) (T : Finset (Fin 4))
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1) :
    0 ≤ ∏ i ∈ selectedIndices q T, p i ∧
      (∏ i ∈ selectedIndices q T, p i) ≤ 1 := by
  have hsub := selectedIndices_subset_of_mem_indexTuples hq T
  constructor
  · exact Finset.prod_nonneg fun i hi ↦ hp0 i (hsub hi)
  · apply Finset.prod_le_one
    · exact fun i hi ↦ hp0 i (hsub hi)
    · exact fun i hi ↦ hp1 i (hsub hi)

/-- If each joint-event error is bounded by a relative product error plus a
uniform floor, then the full sixteen-term/four-index inclusion--exclusion
error is at most `16 * |I|^4 * (ε + E₀)`. -/
theorem jointCenteredFourthError_le_card_pow
    {ι : Type*} (I : Finset ι) (a p : ι → ℝ)
    (err : Finset ι → ℝ) (ε E₀ : ℝ)
    (hε : 0 ≤ ε) (hE₀ : 0 ≤ E₀)
    (ha : ∀ i ∈ I, |a i| ≤ 1)
    (hp0 : ∀ i ∈ I, 0 ≤ p i) (hp1 : ∀ i ∈ I, p i ≤ 1)
    (herr0 : ∀ J ⊆ I, J.card ≤ 4 → 0 ≤ err J)
    (herr : ∀ J ⊆ I, J.card ≤ 4 →
      err J ≤ ε * (∏ i ∈ J, p i) + E₀) :
    jointCenteredFourthError I a p err ≤
      16 * (I.card : ℝ) ^ 4 * (ε + E₀) := by
  classical
  have hsum0 : 0 ≤ ε + E₀ := add_nonneg hε hE₀
  unfold jointCenteredFourthError
  calc
    (∑ q ∈ indexTuples 4 I, |∏ r, a (q r)| *
        ∑ T : Finset (Fin 4), |centeredExpansionCoefficient p q T| *
          err (selectedIndices q T)) ≤
        ∑ q ∈ indexTuples 4 I, 16 * (ε + E₀) := by
      apply Finset.sum_le_sum
      intro q hq
      have houter := abs_tupleCoefficient_le_one hq ha
      have hinner0 : 0 ≤ ∑ T : Finset (Fin 4),
          |centeredExpansionCoefficient p q T| *
            err (selectedIndices q T) := by
        apply Finset.sum_nonneg
        intro T hT
        apply mul_nonneg (abs_nonneg _)
        exact herr0 _ (selectedIndices_subset_of_mem_indexTuples hq T)
          (selectedIndices_card_le_four q T)
      have hinner : (∑ T : Finset (Fin 4),
          |centeredExpansionCoefficient p q T| *
            err (selectedIndices q T)) ≤ 16 * (ε + E₀) := by
        calc
          (∑ T : Finset (Fin 4),
              |centeredExpansionCoefficient p q T| *
                err (selectedIndices q T)) ≤
              ∑ _T : Finset (Fin 4), (ε + E₀) := by
            apply Finset.sum_le_sum
            intro T hT
            have hsub := selectedIndices_subset_of_mem_indexTuples hq T
            have hcard := selectedIndices_card_le_four q T
            have hcoeff := abs_centeredExpansionCoefficient_le_one
              hq T hp0 hp1
            have hprod := selectedProbabilityProduct_nonneg_le_one
              hq T hp0 hp1
            have herrT := herr (selectedIndices q T) hsub hcard
            have herrT0 := herr0 (selectedIndices q T) hsub hcard
            have hrel : ε * (∏ i ∈ selectedIndices q T, p i) + E₀ ≤
                ε + E₀ := by
              linarith [mul_le_of_le_one_right hε hprod.2]
            calc
              |centeredExpansionCoefficient p q T| *
                    err (selectedIndices q T) ≤
                  1 * err (selectedIndices q T) :=
                mul_le_mul_of_nonneg_right hcoeff herrT0
              _ ≤ ε * (∏ i ∈ selectedIndices q T, p i) + E₀ := by
                simpa using herrT
              _ ≤ ε + E₀ := hrel
          _ = 16 * (ε + E₀) := by
            norm_num
            ring
      calc
        |∏ r, a (q r)| *
              (∑ T : Finset (Fin 4), |centeredExpansionCoefficient p q T| *
                err (selectedIndices q T)) ≤
            1 * (∑ T : Finset (Fin 4),
              |centeredExpansionCoefficient p q T| *
                err (selectedIndices q T)) :=
          mul_le_mul_of_nonneg_right houter hinner0
        _ ≤ 1 * (16 * (ε + E₀)) :=
          mul_le_mul_of_nonneg_left hinner zero_le_one
        _ = 16 * (ε + E₀) := by ring
    _ = 16 * (I.card : ℝ) ^ 4 * (ε + E₀) := by
      simp [indexTuples]
      ring

/-! ## Separating relative tuple errors from the absolute error floor -/

/-- Product of the probabilities at the distinct values occurring in an
ordered quadruple.  In the sieve application this is the reciprocal of the
squarefree product/LCM attached to the quadruple. -/
def distinctTupleProductN {ι : Type*} {n : ℕ} (u : ι → ℝ)
    (q : Fin n → ι) : ℝ :=
  ∏ i ∈ (Finset.univ.image q), u i

def distinctTupleProductSumN {ι : Type*} (n : ℕ) (I : Finset ι)
    (u : ι → ℝ) : ℝ :=
  ∑ q ∈ indexTuples n I, distinctTupleProductN u q

def distinctTupleProduct {ι : Type*} (u : ι → ℝ) (q : Fin 4 → ι) : ℝ :=
  distinctTupleProductN u q

def distinctTupleProductSum {ι : Type*} (I : Finset ι) (u : ι → ℝ) : ℝ :=
  distinctTupleProductSumN 4 I u

theorem distinctTupleProductN_cons {ι : Type*} {n : ℕ}
    (u : ι → ℝ) (x : ι) (q : Fin n → ι) :
    distinctTupleProductN u (Fin.cons x q) =
      if x ∈ Finset.univ.image q then distinctTupleProductN u q
      else u x * distinctTupleProductN u q := by
  classical
  have himage : (Finset.univ.image (Fin.cons x q)) =
      insert x (Finset.univ.image q) := by
    ext y
    simp [Fin.exists_fin_succ, eq_comm]
  unfold distinctTupleProductN
  rw [himage]
  by_cases hx : x ∈ Finset.univ.image q
  · rw [if_pos hx, Finset.insert_eq_of_mem hx]
  · rw [if_neg hx, Finset.prod_insert hx]

theorem distinctTupleProductSumN_succ_le
    {ι : Type*} (n : ℕ) (I : Finset ι) (u : ι → ℝ)
    (hu0 : ∀ i ∈ I, 0 ≤ u i) :
    distinctTupleProductSumN (n + 1) I u ≤
      ((n : ℝ) + ∑ i ∈ I, u i) * distinctTupleProductSumN n I u := by
  classical
  let S : Fin (n + 1) → Finset ι := fun _ ↦ I
  let e := (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι)).symm
  have hdecomp :
      distinctTupleProductSumN (n + 1) I u =
        ∑ z ∈ I ×ˢ indexTuples n I,
          distinctTupleProductN u (Fin.cons z.1 z.2) := by
    unfold distinctTupleProductSumN indexTuples
    apply Finset.sum_equiv e
    · intro q
      simp only [e, Fin.consEquiv_symm_apply, Finset.mem_product,
        Fin.mem_piFinset_iff_zero_tail]
      rfl
    · intro q hq
      simp only [e, Fin.consEquiv_symm_apply]
      rw [Fin.cons_self_tail]
  rw [hdecomp, Finset.sum_product, Finset.sum_comm]
  unfold distinctTupleProductSumN
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  let R : Finset ι := Finset.univ.image q
  have hRsub : R ⊆ I := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact (Fintype.mem_piFinset.mp hq) r
  have hRcard : R.card ≤ n := by
    calc
      R.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := Fintype.card_fin n
  have hprod0 : 0 ≤ distinctTupleProductN u q := by
    unfold distinctTupleProductN
    exact Finset.prod_nonneg fun i hi ↦ hu0 i (hRsub hi)
  calc
    (∑ x ∈ I, distinctTupleProductN u (Fin.cons x q)) =
        ∑ x ∈ I, (if x ∈ R then distinctTupleProductN u q
          else u x * distinctTupleProductN u q) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [distinctTupleProductN_cons]
    _ = ((I.filter (· ∈ R)).card : ℝ) * distinctTupleProductN u q +
          (∑ x ∈ I.filter (· ∉ R), u x) * distinctTupleProductN u q := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_mul]
    _ ≤ ((n : ℝ) + ∑ x ∈ I, u x) * distinctTupleProductN u q := by
      have hcard : ((I.filter (· ∈ R)).card : ℝ) ≤ n := by
        exact_mod_cast (Finset.card_le_card
          (fun x hx ↦ (Finset.mem_filter.mp hx).2) |>.trans hRcard)
      have hsum : (∑ x ∈ I.filter (· ∉ R), u x) ≤ ∑ x ∈ I, u x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro x hxI hxNot
        exact hu0 x hxI
      calc
        ((I.filter (· ∈ R)).card : ℝ) * distinctTupleProductN u q +
              (∑ x ∈ I.filter (· ∉ R), u x) * distinctTupleProductN u q =
            (((I.filter (· ∈ R)).card : ℝ) +
              ∑ x ∈ I.filter (· ∉ R), u x) * distinctTupleProductN u q := by
          ring
        _ ≤ ((n : ℝ) + ∑ x ∈ I, u x) * distinctTupleProductN u q :=
          mul_le_mul_of_nonneg_right (add_le_add hcard hsum) hprod0

theorem distinctTupleProductSum_le_fifteen
    {ι : Type*} (I : Finset ι) (u : ι → ℝ)
    (hu0 : ∀ i ∈ I, 0 ≤ u i) :
    distinctTupleProductSum I u ≤
      15 * (1 + ∑ i ∈ I, u i) ^ 4 := by
  let U : ℝ := ∑ i ∈ I, u i
  have hU : 0 ≤ U := Finset.sum_nonneg fun i hi ↦ hu0 i hi
  have h0 : distinctTupleProductSumN 0 I u = 1 := by
    simp [distinctTupleProductSumN, indexTuples, distinctTupleProductN]
  have h1 := distinctTupleProductSumN_succ_le 0 I u hu0
  have h2 := distinctTupleProductSumN_succ_le 1 I u hu0
  have h3 := distinctTupleProductSumN_succ_le 2 I u hu0
  have h4 := distinctTupleProductSumN_succ_le 3 I u hu0
  change distinctTupleProductSumN 4 I u ≤ _
  calc
    distinctTupleProductSumN 4 I u ≤ (3 + U) *
        distinctTupleProductSumN 3 I u := by simpa [U] using h4
    _ ≤ (3 + U) * ((2 + U) * distinctTupleProductSumN 2 I u) :=
      mul_le_mul_of_nonneg_left (by simpa [U] using h3) (by positivity)
    _ ≤ (3 + U) * ((2 + U) * ((1 + U) *
        distinctTupleProductSumN 1 I u)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [U] using h2
    _ ≤ (3 + U) * ((2 + U) * ((1 + U) * (U *
        distinctTupleProductSumN 0 I u))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [U] using h1
    _ = (3 + U) * (2 + U) * (1 + U) * U := by rw [h0]; ring
    _ ≤ 15 * (1 + U) ^ 4 := by
      have hU1 : U ≤ 1 + U := by linarith
      have hU2 : 2 + U ≤ 2 * (1 + U) := by linarith
      have hU3 : 3 + U ≤ 3 * (1 + U) := by linarith
      have h1U : 0 ≤ 1 + U := by linarith
      calc
        (3 + U) * (2 + U) * (1 + U) * U ≤
            (3 * (1 + U)) * (2 * (1 + U)) * (1 + U) * (1 + U) := by
          gcongr
        _ ≤ 15 * (1 + U) ^ 4 := by
          nlinarith [sq_nonneg ((1 + U) ^ 2)]

theorem prod_comp_image_mul_prod_image_le_distinctTupleProduct
    {ι : Type*} {I : Finset ι} {u : ι → ℝ} {q : Fin 4 → ι}
    (hq : q ∈ indexTuples 4 I) (T : Finset (Fin 4))
    (hu0 : ∀ i ∈ I, 0 ≤ u i) (hu1 : ∀ i ∈ I, u i ≤ 1) :
    (∏ r ∈ Tᶜ, u (q r)) * (∏ i ∈ selectedIndices q T, u i) ≤
      distinctTupleProduct u q := by
  classical
  let A : Finset ι := Tᶜ.image q
  let B : Finset ι := T.image q
  have hqI : ∀ r, q r ∈ I := Fintype.mem_piFinset.mp hq
  have hpos (S : Finset ι) (hS : S ⊆ Finset.univ.image q) :
      0 ≤ ∏ i ∈ S, u i :=
    Finset.prod_nonneg fun i hi ↦ by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (hS hi)
      exact hu0 (q r) (hqI r)
  have hinter_le : (∏ i ∈ A ∩ B, u i) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i hi
      have hiA : i ∈ A := (Finset.mem_inter.mp hi).1
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hiA
      exact hu0 (q r) (hqI r)
    · intro i hi
      have hiA : i ∈ A := (Finset.mem_inter.mp hi).1
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hiA
      exact hu1 (q r) (hqI r)
  have hunion : A ∪ B = Finset.univ.image q := by
    ext i
    simp only [A, B, Finset.mem_union, Finset.mem_image,
      Finset.mem_compl, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) <;>
        exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      by_cases hr : r ∈ T
      · exact Or.inr ⟨r, hr, rfl⟩
      · exact Or.inl ⟨r, hr, rfl⟩
  have hpositions_general (S : Finset (Fin 4)) :
      (∏ r ∈ S, u (q r)) ≤ ∏ i ∈ S.image q, u i := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert r S hrS ih =>
        have hSI : ∀ x ∈ S, q x ∈ I := fun x hx ↦ hqI x
        by_cases hmem : q r ∈ S.image q
        · rw [Finset.prod_insert hrS]
          have himage : (insert r S).image q = S.image q := by
            rw [Finset.image_insert, Finset.insert_eq_of_mem hmem]
          rw [himage]
          calc
            u (q r) * ∏ x ∈ S, u (q x) ≤
                1 * ∏ x ∈ S, u (q x) :=
              mul_le_mul_of_nonneg_right (hu1 (q r) (hqI r))
                (Finset.prod_nonneg fun x hx ↦ hu0 (q x) (hSI x hx))
            _ ≤ ∏ i ∈ S.image q, u i := by simpa using ih
        · rw [Finset.prod_insert hrS]
          rw [Finset.image_insert, Finset.prod_insert hmem]
          exact mul_le_mul_of_nonneg_left ih (hu0 (q r) (hqI r))
  have hpositions : (∏ r ∈ Tᶜ, u (q r)) ≤ ∏ i ∈ A, u i := by
    exact hpositions_general Tᶜ
  have hBsub : B ⊆ Finset.univ.image q := by
    intro i hi
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  calc
    (∏ r ∈ Tᶜ, u (q r)) * (∏ i ∈ selectedIndices q T, u i) ≤
        (∏ i ∈ A, u i) * (∏ i ∈ B, u i) :=
      mul_le_mul_of_nonneg_right hpositions
        (hpos B hBsub)
    _ = (∏ i ∈ A ∪ B, u i) * (∏ i ∈ A ∩ B, u i) :=
      (Finset.prod_union_inter (s₁ := A) (s₂ := B) (f := u)).symm
    _ ≤ (∏ i ∈ A ∪ B, u i) * 1 :=
      mul_le_mul_of_nonneg_left hinter_le
        (hpos (A ∪ B) (by rw [hunion]))
    _ = distinctTupleProduct u q := by
      rw [hunion]
      simp [distinctTupleProduct, distinctTupleProductN]

theorem abs_centeredCoefficient_mul_selectedProduct_le_distinct
    {ι : Type*} {I : Finset ι} {u : ι → ℝ} {q : Fin 4 → ι}
    (hq : q ∈ indexTuples 4 I) (T : Finset (Fin 4))
    (hu0 : ∀ i ∈ I, 0 ≤ u i) (hu1 : ∀ i ∈ I, u i ≤ 1) :
    |centeredExpansionCoefficient u q T| *
        (∏ i ∈ selectedIndices q T, u i) ≤ distinctTupleProduct u q := by
  unfold centeredExpansionCoefficient
  have hcoeff : |∏ r ∈ Tᶜ, -u (q r)| = ∏ r ∈ Tᶜ, u (q r) := by
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro r hr
    rw [abs_neg, abs_of_nonneg]
    exact hu0 (q r) ((Fintype.mem_piFinset.mp hq) r)
  rw [hcoeff]
  exact prod_comp_image_mul_prod_image_le_distinctTupleProduct hq T hu0 hu1

/-- Relative joint errors pay only the weighted distinct-tuple sum; only the
uniform absolute floor pays the full `|I|^4` count. -/
theorem jointCenteredFourthError_one_le_distinct_add_floor
    {ι : Type*} (I : Finset ι) (u : ι → ℝ) (err : Finset ι → ℝ)
    (ε E₀ : ℝ) (hε : 0 ≤ ε) (hE₀ : 0 ≤ E₀)
    (hu0 : ∀ i ∈ I, 0 ≤ u i) (hu1 : ∀ i ∈ I, u i ≤ 1)
    (_herr0 : ∀ J ⊆ I, J.card ≤ 4 → 0 ≤ err J)
    (herr : ∀ J ⊆ I, J.card ≤ 4 →
      err J ≤ ε * (∏ i ∈ J, u i) + E₀) :
    jointCenteredFourthError I (fun _ ↦ 1) u err ≤
      16 * ε * distinctTupleProductSum I u +
        16 * (I.card : ℝ) ^ 4 * E₀ := by
  classical
  unfold jointCenteredFourthError distinctTupleProductSum
  calc
    (∑ q ∈ indexTuples 4 I, |∏ r, (1 : ℝ)| *
        ∑ T : Finset (Fin 4), |centeredExpansionCoefficient u q T| *
          err (selectedIndices q T)) ≤
        ∑ q ∈ indexTuples 4 I,
          (16 * ε * distinctTupleProduct u q + 16 * E₀) := by
      apply Finset.sum_le_sum
      intro q hq
      simp only [Finset.prod_const_one, abs_one, one_mul]
      calc
        (∑ T : Finset (Fin 4), |centeredExpansionCoefficient u q T| *
            err (selectedIndices q T)) ≤
            ∑ _T : Finset (Fin 4),
              (ε * distinctTupleProduct u q + E₀) := by
          apply Finset.sum_le_sum
          intro T hT
          have hsub := selectedIndices_subset_of_mem_indexTuples hq T
          have hcard := selectedIndices_card_le_four q T
          have hc0 : 0 ≤ |centeredExpansionCoefficient u q T| := abs_nonneg _
          have hc1 := abs_centeredExpansionCoefficient_le_one hq T hu0 hu1
          have herrT := herr (selectedIndices q T) hsub hcard
          have hmul := mul_le_mul_of_nonneg_left herrT hc0
          have hrelative :=
            abs_centeredCoefficient_mul_selectedProduct_le_distinct
              hq T hu0 hu1
          calc
            |centeredExpansionCoefficient u q T| *
                  err (selectedIndices q T) ≤
                |centeredExpansionCoefficient u q T| *
                  (ε * (∏ i ∈ selectedIndices q T, u i) + E₀) := hmul
            _ = ε * (|centeredExpansionCoefficient u q T| *
                    (∏ i ∈ selectedIndices q T, u i)) +
                  E₀ * |centeredExpansionCoefficient u q T| := by ring
            _ ≤ ε * distinctTupleProduct u q + E₀ * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left hrelative hε)
                (mul_le_mul_of_nonneg_left hc1 hE₀)
            _ = ε * distinctTupleProduct u q + E₀ := by ring
        _ = 16 * ε * distinctTupleProduct u q + 16 * E₀ := by
          norm_num
          ring
    _ = 16 * ε * (∑ q ∈ indexTuples 4 I, distinctTupleProduct u q) +
          16 * (I.card : ℝ) ^ 4 * E₀ := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      simp [indexTuples]
      ring

/-- Consumer form: insert any independently proved collision-pattern bound
for the distinct-tuple sum.  The standard fifteen equality patterns give the
hypothesis with `C = 15 * (1 + ∑ i ∈ I, u i)^4`. -/
theorem jointCenteredFourthError_one_le_of_distinctTupleProductSum_le
    {ι : Type*} (I : Finset ι) (u : ι → ℝ) (err : Finset ι → ℝ)
    (ε E₀ C : ℝ) (hε : 0 ≤ ε) (hE₀ : 0 ≤ E₀)
    (hu0 : ∀ i ∈ I, 0 ≤ u i) (hu1 : ∀ i ∈ I, u i ≤ 1)
    (herr0 : ∀ J ⊆ I, J.card ≤ 4 → 0 ≤ err J)
    (herr : ∀ J ⊆ I, J.card ≤ 4 →
      err J ≤ ε * (∏ i ∈ J, u i) + E₀)
    (hcollision : distinctTupleProductSum I u ≤ C) :
    jointCenteredFourthError I (fun _ ↦ 1) u err ≤
      16 * ε * C + 16 * (I.card : ℝ) ^ 4 * E₀ := by
  calc
    jointCenteredFourthError I (fun _ ↦ 1) u err ≤
        16 * ε * distinctTupleProductSum I u +
          16 * (I.card : ℝ) ^ 4 * E₀ :=
      jointCenteredFourthError_one_le_distinct_add_floor
        I u err ε E₀ hε hE₀ hu0 hu1 herr0 herr
    _ ≤ 16 * ε * C + 16 * (I.card : ℝ) ^ 4 * E₀ := by
      gcongr

/-- Fully explicit weighted-error bound, with the collision sum discharged by
`distinctTupleProductSum_le_fifteen`. -/
theorem jointCenteredFourthError_one_le_relative_add_floor
    {ι : Type*} (I : Finset ι) (u : ι → ℝ) (err : Finset ι → ℝ)
    (ε E₀ : ℝ) (hε : 0 ≤ ε) (hE₀ : 0 ≤ E₀)
    (hu0 : ∀ i ∈ I, 0 ≤ u i) (hu1 : ∀ i ∈ I, u i ≤ 1)
    (herr0 : ∀ J ⊆ I, J.card ≤ 4 → 0 ≤ err J)
    (herr : ∀ J ⊆ I, J.card ≤ 4 →
      err J ≤ ε * (∏ i ∈ J, u i) + E₀) :
    jointCenteredFourthError I (fun _ ↦ 1) u err ≤
      16 * ε * (15 * (1 + ∑ i ∈ I, u i) ^ 4) +
        16 * (I.card : ℝ) ^ 4 * E₀ := by
  exact jointCenteredFourthError_one_le_of_distinctTupleProductSum_le
    I u err ε E₀ (15 * (1 + ∑ i ∈ I, u i) ^ 4)
    hε hE₀ hu0 hu1 herr0 herr (distinctTupleProductSum_le_fifteen I u hu0)

end Erdos248

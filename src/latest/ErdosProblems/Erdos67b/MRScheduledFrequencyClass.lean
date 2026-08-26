import ErdosProblems.Erdos67b.MRScheduledSmallBlockClass
import ErdosProblems.Erdos67b.MRFrequencyClasses
import ErdosProblems.Erdos67b.MRFirstBlockEnergy

/-!
# Actual scheduled first-small frequency classes

The class is defined from the prime polynomials themselves. Measurability,
small current subblocks and a large preceding subblock are proved, so the
scheduled energy theorem has no assumed frequency-cover condition.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

def mrScheduledSmallFrequencySet (eta p₁ q₁ : ℝ)
    (P : ℕ → ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℂ) : ℕ → Set ℝ :=
  mrSmallPrimeBlockSet (mrScheduledSubblocks eta p₁ q₁)
    (fun j r ↦ logarithmicDirichletPolynomial (P j r) (a j r))
    (fun j r ↦ Real.exp (-mrThresholdExponent eta (j : ℝ) * mrScheduledParameter eta p₁ q₁ j r))

theorem measurableSet_mrScheduledSmallFrequencySet
    (eta p₁ q₁ : ℝ) (P : ℕ → ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℂ) (j : ℕ) :
    MeasurableSet (mrScheduledSmallFrequencySet eta p₁ q₁ P a j) :=
  measurableSet_mrSmallPrimeBlockSet _ _ _
    (fun i r _ ↦ continuous_logarithmicDirichletPolynomial (P i r) (a i r)) j

/-- The actual first-small class on the source-shaped schedule has the
summable energy bound. Only arithmetic support/coefficient inputs remain. -/
theorem mrScheduled_firstSmallClass_energy_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    (P : ℕ → ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℂ)
    (S : ℕ → Finset ℕ) (b : ℕ → ℕ → ℂ)
    (hP : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r, p.Prime)
    (ha : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      ‖a (j - 1) r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hPlo : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤ p)
    (hPhi : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      (p : ℝ) ≤ 2 * Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (X : ℝ) / Real.exp (mrScheduledParameter eta p₁ q₁ j s) ≤ m)
    (hShi : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (m : ℝ) ≤ 2 * X / Real.exp (mrScheduledParameter eta p₁ q₁ j s))
    {T : ℝ} (hT : 0 ≤ T) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
      (∑ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T,
        (disjointed (mrScheduledSmallFrequencySet eta p₁ q₁ P a) j).indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial (P j s) (a j s) t *
            logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      128 * Real.exp 12 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
  apply scheduled_firstSmallBlock_frequencyClass_energy_le heta0 heta1 hp hqexp hpq hbudget hj
    (P (j - 1)) S (a (j - 1)) b
    (fun s ↦ logarithmicDirichletPolynomial (P j s) (a j s)) hP ha hb hPlo hPhi hX hSlo hShi
    (fun s _ ↦ continuous_logarithmicDirichletPolynomial (P j s) (a j s))
    (MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet eta p₁ q₁ P a) j) hT
  · intro s hs t ht _
    exact mrFirstSmall_current_small (mrScheduledSubblocks eta p₁ q₁)
      (fun i r ↦ logarithmicDirichletPolynomial (P i r) (a i r))
      (fun i r ↦ Real.exp (-mrThresholdExponent eta (i : ℝ) * mrScheduledParameter eta p₁ q₁ i r))
      (by omega) ht s hs
  · intro t ht _
    obtain ⟨r, hr, hlarge⟩ := mrFirstSmall_preceding_large (mrScheduledSubblocks eta p₁ q₁)
      (fun i r ↦ logarithmicDirichletPolynomial (P i r) (a i r))
      (fun i r ↦ Real.exp (-mrThresholdExponent eta (i : ℝ) * mrScheduledParameter eta p₁ q₁ i r)) hj ht
    exact ⟨r, hr, hlarge.le⟩

/-- The actual first-small frequency class also has summable energy
for the enlarged cofactor support required by finite Ramaré. -/
theorem mrScheduled_firstSmallClass_enlarged_energy_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    (P : ℕ → ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℂ)
    (S : ℕ → Finset ℕ) (b : ℕ → ℕ → ℂ)
    (hP : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r, p.Prime)
    (ha : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      ‖a (j - 1) r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hPlo : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤ p)
    (hPhi : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      (p : ℝ) ≤ 2 * Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (X : ℝ) / Real.exp (mrScheduledParameter eta p₁ q₁ j s + 1) ≤ m)
    (hShi : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (m : ℝ) ≤ 8 * X / Real.exp (mrScheduledParameter eta p₁ q₁ j s + 1))
    {T : ℝ} (hT : 0 ≤ T) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
      (∑ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T,
        (disjointed (mrScheduledSmallFrequencySet eta p₁ q₁ P a) j).indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial (P j s) (a j s) t *
            logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      512 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
  apply scheduled_firstSmallBlock_enlarged_frequencyClass_energy_le heta0 heta1 hp hqexp hpq hbudget hj
    (P (j - 1)) S (a (j - 1)) b
    (fun s ↦ logarithmicDirichletPolynomial (P j s) (a j s)) hP ha hb hPlo hPhi hX hSlo hShi
    (fun s _ ↦ continuous_logarithmicDirichletPolynomial (P j s) (a j s))
    (MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet eta p₁ q₁ P a) j) hT
  · intro s hs t ht _
    exact mrFirstSmall_current_small (mrScheduledSubblocks eta p₁ q₁)
      (fun i r ↦ logarithmicDirichletPolynomial (P i r) (a i r))
      (fun i r ↦ Real.exp (-mrThresholdExponent eta (i : ℝ) * mrScheduledParameter eta p₁ q₁ i r))
      (by omega) ht s hs
  · intro t ht _
    obtain ⟨r, hr, hlarge⟩ := mrFirstSmall_preceding_large (mrScheduledSubblocks eta p₁ q₁)
      (fun i r ↦ logarithmicDirichletPolynomial (P i r) (a i r))
      (fun i r ↦ Real.exp (-mrThresholdExponent eta (i : ℝ) * mrScheduledParameter eta p₁ q₁ i r)) hj ht
    exact ⟨r, hr, hlarge.le⟩

/-- Arithmetic rectangle specialization. Any subset is allowed, including
a cofactor support restricted by the other prime blocks. -/
theorem mrScheduled_firstSmallClass_rectangle_energy_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    (P : ℕ → ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℂ)
    (S : ℕ → Finset ℕ) (b : ℕ → ℕ → ℂ)
    (hP : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r, p.Prime)
    (ha : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      ‖a (j - 1) r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hPlo : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤ p)
    (hPhi : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P (j - 1) r,
      (p : ℝ) ≤ 2 * Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r))
    {X : ℕ} (hX : 0 < X)
    (I : ℕ → ℕ × ℕ)
    (hIpos : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, 0 < (I s).2)
    (hIlo : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j,
      Real.exp (mrScheduledParameter eta p₁ q₁ j s) ≤ (I s).1)
    (hIhi : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j,
      ((I s).2 : ℝ) ≤ Real.exp (mrScheduledParameter eta p₁ q₁ j s + 1))
    (hS : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j,
      S s ⊆ mrDyadicCofactorRectangle (I s) X)
    {T : ℝ} (hT : 0 ≤ T) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
      (∑ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T,
        (disjointed (mrScheduledSmallFrequencySet eta p₁ q₁ P a) j).indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial (P j s) (a j s) t *
            logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      512 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
  apply mrScheduled_firstSmallClass_enlarged_energy_le heta0 heta1 hp hqexp hpq hbudget hj
    P a S b hP ha hb hPlo hPhi hX ?_ ?_ hT
  · intro s hs m hm
    exact (mrDyadicCofactorRectangle_shifted_bounds (hIlo s hs) (hIhi s hs)
      (hIpos s hs) (hS s hs hm)).1
  · intro s hs m hm
    exact (mrDyadicCofactorRectangle_shifted_bounds (hIlo s hs) (hIhi s hs)
      (hIpos s hs) (hS s hs hm)).2

/-- The first-small frequency class at index one has the source decay
bound, using the finite cofactor mean square instead of amplification. -/
theorem mrScheduled_firstClass_rectangle_energy_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (P : ℕ → ℕ → Finset ℕ) (a : ℕ → ℕ → ℕ → ℂ)
    (I : ℕ → ℕ × ℕ) (S : ℕ → Finset ℕ) (b : ℕ → ℕ → ℂ)
    {X : ℕ} (hX : 0 < X)
    (hIlo : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, 0 < (I r).1)
    (hIhi : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, 0 < (I r).2)
    (hIX : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, (I r).1 ≤ X)
    (hIwidth : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, (I r).2 ≤ 2 * (I r).1)
    (hIq : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, ((I r).2 : ℝ) ≤ Real.exp (q₁ + 1))
    (hS : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, S r ⊆ mrDyadicCofactorRectangle (I r) X)
    (hb : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, ∀ m ∈ S r, ‖b r m‖ ≤ (m : ℝ)⁻¹)
    {T : ℝ} (hT : 0 ≤ T) :
    mrLogBlockResolution eta p₁ q₁ 1 * q₁ *
      (∑ r ∈ mrScheduledSubblocks eta p₁ q₁ 1, ∫ t in -T..T,
        (disjointed (mrScheduledSmallFrequencySet eta p₁ q₁ P a) 1).indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial (P 1 r) (a 1 r) t *
            logarithmicDirichletPolynomial (S r) (b r) t‖ ^ 2) t) ≤
      256 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
        Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁) := by
  have hq0 : 0 < q₁ := (Real.exp_pos _).trans_le hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hH := mrLogSchedule_resolution_one_le heta1 (by linarith) hlogq hbudget
    (by norm_num : 1 ≤ (1 : ℕ))
  simp only [Nat.cast_one] at hH
  have hbeta0 : 0 < mrThresholdExponent eta 1 := by
    unfold mrThresholdExponent
    norm_num
    linarith
  have hbeta1 : mrThresholdExponent eta 1 ≤ 1 / 4 :=
    (mrThresholdExponent_bounds heta0.le (by linarith) (by norm_num : (1 : ℝ) ≤ 1)).2
  have hindices : mrScheduledSubblocks eta p₁ q₁ 1 =
      mrLogBlockIndices (mrLogBlockResolution eta p₁ q₁ 1) p₁ q₁ := by
    unfold mrScheduledSubblocks mrLogScheduleLower mrLogScheduleWeight mrLogScheduleUpper
    norm_num
  rw [hindices] at hIlo hIhi hIX hIwidth hIq hS hb ⊢
  have hraw := firstBlock_frequencyClass_energy_le hH (by linarith : 0 ≤ p₁) hq0.le hbeta0 hbeta1
    I S b (fun r ↦ logarithmicDirichletPolynomial (P 1 r) (a 1 r))
    hX hIlo hIhi hIX hIwidth hIq hS hb
    (fun r _ ↦ continuous_logarithmicDirichletPolynomial (P 1 r) (a 1 r))
    (MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet eta p₁ q₁ P a) 1) hT
    (by
      intro r hr t ht _
      have hr' : r ∈ mrScheduledSubblocks eta p₁ q₁ 1 := by rwa [hindices]
      have hh := mrFirstSmall_current_small (mrScheduledSubblocks eta p₁ q₁)
        (fun i s ↦ logarithmicDirichletPolynomial (P i s) (a i s))
        (fun i s ↦ Real.exp (-mrThresholdExponent eta (i : ℝ) * mrScheduledParameter eta p₁ q₁ i s))
        (by norm_num : 1 ≤ (1 : ℕ)) ht r hr'
      simpa only [mrScheduledParameter, Nat.cast_one] using hh)
  exact hraw.trans (firstBlock_resolution_energy_prefactor_le (tau := T / X) heta1 hq0 (by positivity))

end

end Erdos67b

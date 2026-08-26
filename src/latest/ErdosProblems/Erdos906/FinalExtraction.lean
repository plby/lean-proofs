import ErdosProblems.Erdos906.Derivatives
import ErdosProblems.Erdos906.DiskBasis
import ErdosProblems.Erdos906.Extraction
import ErdosProblems.Erdos906.RandomFock

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ENNReal Polynomial

namespace CofiniteDerivatives

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]

/-- Intersect an almost-everywhere property with countably many Borel--Cantelli conclusions and
extract one deterministic sample. -/
theorem exists_ae_property_forall_eventually_not_failure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : ι → ℕ → Set Ω) (Q : Ω → Prop)
    (hQ : ∀ᵐ ω ∂μ, Q ω)
    (hsum : ∀ j, (∑' n, μ (failure j n)) < ∞) :
    ∃ ω, Q ω ∧ ∀ j, ∀ᶠ n in atTop, ω ∉ failure j n := by
  have hfailure : ∀ᵐ ω ∂μ, ∀ j, ∀ᶠ n in atTop, ω ∉ failure j n := by
    rw [ae_all_iff]
    intro j
    exact ae_eventually_notMem (ne_of_lt (hsum j))
  have hboth : ∀ᵐ ω ∂μ, Q ω ∧ ∀ j, ∀ᶠ n in atTop, ω ∉ failure j n := by
    filter_upwards [hQ, hfailure] with ω hQω hfailureω
    exact ⟨hQω, hfailureω⟩
  exact hboth.exists

/-- The zero set of the `n`-th derivative of a random Fock sample. -/
def randomFockZeroSet (ω : ℕ → ℂ) (n : ℕ) : Set ℂ :=
  {z | randomFockDeriv n ω z = 0}

/-- The event that the `n`-th random Fock derivative has no zero in the `j`-th basis disk. -/
def randomFockDiskHole (j n : ℕ) : Set (ℕ → ℂ) :=
  holeEvent randomFockZeroSet diskBasis j n

/-- The final deterministic random-Fock extraction, conditional only on summability of the
disk-hole probabilities. -/
theorem exists_randomFock_final_of_summable_holes
    (hsum : ∀ j, (∑' n, P (randomFockDiskHole j n)) < ∞) :
    ∃ ω,
      AnalyticOnNhd ℂ (randomFock ω) Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = randomFock ω z) ∧
      DerivativesCofinitelyHit (randomFock ω) ∧
      EveryDerivativeSubsequenceDense (randomFock ω) := by
  classical
  obtain ⟨ω, hnonpolynomial, hholes⟩ :=
    exists_ae_property_forall_eventually_not_failure
      (μ := P) (failure := randomFockDiskHole)
      (Q := fun ω ↦ ¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = randomFock ω z)
      P_ae_randomFock_nonpolynomial hsum
  have hcofinite : CofinitelyHits (randomFockZeroSet ω) := by
    intro U hU hUne
    obtain ⟨j, hjU⟩ := exists_diskBasis_subset U hU hUne
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hholes j)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hhit : (randomFockZeroSet ω n ∩ diskBasis j).Nonempty := by
      have hnotHole := hN n hn
      simpa only [randomFockDiskHole, holeEvent, mem_ofPred_eq, not_not] using! hnotHole
    rcases hhit with ⟨z, hzZero, hzDisk⟩
    exact ⟨z, hzZero, hjU hzDisk⟩
  have hderivatives : DerivativesCofinitelyHit (randomFock ω) := by
    exact hcofinite
  have hsubsequences : EveryDerivativeSubsequenceDense (randomFock ω) :=
    (derivativesCofinitelyHit_iff_everyDerivativeSubsequenceDense (randomFock ω)).mp
      hderivatives
  exact ⟨ω, analyticOnNhd_randomFock ω, hnonpolynomial, hderivatives, hsubsequences⟩

end CofiniteDerivatives

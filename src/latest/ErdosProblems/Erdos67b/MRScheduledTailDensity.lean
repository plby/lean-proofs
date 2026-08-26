import ErdosProblems.Erdos67b.MRScheduledTailBlocks
import ErdosProblems.Erdos67b.MRScheduledFiniteDensity
import ErdosProblems.Erdos67b.MRScheduledDensityRemainder

/-! # Finite tail-family density, with the initial index chosen before the scale -/

open Filter
open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrExists_scheduled_tail_finite_atypical_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ {eta p q L : ℝ}, eta ≤ 1 / 12 → 2 ≤ p → 1 ≤ q → 2 * p ≤ q →
        1 ≤ Real.log q → 4096 * Real.log q ≤ eta * p → 1 ≤ L →
      ∀ {K J : ℕ}, 0 < K → 1 ≤ J → mrLogScheduleUpper q J ≤ Real.sqrt L →
      ∀ Z : ℕ,
        ((atypicalFactorizationSet (mrScheduledTailBlocks p q K J) Z).card : ℝ) ≤
          (C * (p / q) / K) * Z + L * Real.exp (2 * (S : ℝ) * Real.sqrt L) := by
  obtain ⟨A, S, hA, hS, _, hfinite⟩ :=
    exists_uniform_card_atypicalFactorizationSet_mertens_beta_bound
  let D := (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
    Real.exp (2 * PrimeEstimates.mertensBound)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨2 * D, by positivity, S, hS, ?_⟩
  intro eta p q L heta hp hq hpq hlogq hbudget hL K J hK hJ hupper Z
  have hvalid : ∀ I ∈ mrScheduledTailBlocks p q K J, 3 ≤ I.1 ∧ I.1 ≤ I.2 := by
    intro I hI
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI
    exact mrScheduledPrimeInterval_valid hp hq hpq
      (by have := (Finset.mem_Ioc.mp hj).1; omega)
  have hbase := hfinite (mrScheduledTailBlocks p q K J) Z hvalid
  have hratio := mrScheduledTailBlocks_sum_logRatio_le heta hp hq hpq hlogq hbudget hK J
  have hsum : (∑ I ∈ mrScheduledTailBlocks p q K J,
      (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        (Real.exp (2 * PrimeEstimates.mertensBound) *
          (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) ≤
        D * ((2 * p / q) / K) := by
    calc
      _ = D * ∑ I ∈ mrScheduledTailBlocks p q K J,
          Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I hI
        dsimp only [D]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio hD.le
  have hrem : (∑ I ∈ mrScheduledTailBlocks p q K J, (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
      L * Real.exp (2 * (S : ℝ) * Real.sqrt L) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (mrScheduledTailBlocks_subset p q K J)
      (fun I _ _ ↦ sq_nonneg _)).trans ?_
    exact mrScheduled_sieveRemainder_le heta hp hq (by linarith) hlogq hbudget
      hL hJ hupper S
  calc
    _ ≤ (Z : ℝ) * _ + _ := hbase
    _ ≤ (Z : ℝ) * (D * ((2 * p / q) / K)) +
        L * Real.exp (2 * (S : ℝ) * Real.sqrt L) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg Z)) hrem
    _ = _ := by ring

/-- One fixed initial index pays the missing tail uniformly in every later final index. -/
theorem mrExists_scheduled_tail_density_small
    {eta p q delta : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : 2 * p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (hdelta : 0 < delta) :
    ∃ K₀ X₀ : ℕ, 0 < K₀ ∧ 2 ≤ X₀ ∧
      ∀ {K X : ℕ}, K₀ ≤ K → X₀ ≤ X →
      ∀ {J : ℕ}, 1 ≤ J → mrLogScheduleUpper q J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ Z : ℕ, Z ≤ 3 * X →
        ((atypicalFactorizationSet (mrScheduledTailBlocks p q K J) Z).card : ℝ) ≤ delta * X := by
  obtain ⟨C, hC, S, _, hfinite⟩ := mrExists_scheduled_tail_finite_atypical_bound
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    (mrEventually_scheduled_sieveRemainder_small S (half_pos hdelta))
  let K₀ : ℕ := max 1 ⌈6 * C * (p / q) / delta⌉₊
  refine ⟨K₀, max X₁ 2, by dsimp only [K₀]; omega, le_max_right _ _, ?_⟩
  intro K X hK₀ hX J hJ hupper Z hZ
  have hK : 0 < K := by dsimp only [K₀] at hK₀; omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hceil : ⌈6 * C * (p / q) / delta⌉₊ ≤ K := by dsimp only [K₀] at hK₀; omega
  have hpaid := (div_le_iff₀ hdelta).1 (Nat.le_of_ceil_le hceil)
  have hcoef : C * (p / q) / K ≤ delta / 6 := by
    apply (div_le_iff₀ hKR).2
    nlinarith
  obtain ⟨_, hlogX, hrem⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hbase := hfinite heta hp hq hpq hlogq hbudget hlogX hK hJ hupper Z
  have hZreal : (Z : ℝ) ≤ 3 * X := by exact_mod_cast hZ
  calc
    _ ≤ (C * (p / q) / K) * Z + Real.log (X : ℝ) *
        Real.exp (2 * (S : ℝ) * Real.sqrt (Real.log (X : ℝ))) := hbase
    _ ≤ (delta / 6) * (3 * X) + (delta / 2) * X := by gcongr
    _ = _ := by ring

end

end Erdos67b

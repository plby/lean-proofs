/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.Global

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Upper-density helper lemmas for Erdős Problem 330

The construction naturally produces dense finite blocks at arbitrarily large
endpoints.  This file bridges those witnesses to the `Set.upperDensity` API.
-/

namespace Erdos330

open Filter

theorem partialDensity_univ_nat (S : Set ℕ) (b : ℕ) :
    S.partialDensity Set.univ b = ((S ∩ Set.Iio b).ncard : ℝ) / b := by
  simp [Set.partialDensity, Set.ncard_Iio_nat]

theorem le_partialDensity_univ_nat_of_count {S : Set ℕ} {b : ℕ} {c : ℝ}
    (hb : 0 < b)
    (hcount : c * (b : ℝ) ≤ ((S ∩ Set.Iio b).ncard : ℝ)) :
    c ≤ S.partialDensity Set.univ b := by
  rw [partialDensity_univ_nat]
  rwa [le_div_iff₀ (Nat.cast_pos.mpr hb)]

theorem le_partialDensity_univ_nat_of_finset {S : Set ℕ} {B : Finset ℕ} {b : ℕ} {c : ℝ}
    (hb : 0 < b)
    (hB : ∀ n ∈ B, n ∈ S ∧ n < b)
    (hcount : c * (b : ℝ) ≤ (B.card : ℝ)) :
    c ≤ S.partialDensity Set.univ b := by
  have hBsub : (B : Set ℕ) ⊆ S ∩ Set.Iio b := by
    intro n hn
    exact hB n hn
  have hcard_nat : B.card ≤ (S ∩ Set.Iio b).ncard := by
    simpa using Set.ncard_le_ncard hBsub
  have hcard_real : (B.card : ℝ) ≤ ((S ∩ Set.Iio b).ncard : ℝ) := by
    exact_mod_cast hcard_nat
  exact le_partialDensity_univ_nat_of_count hb (hcount.trans hcard_real)

/--
Arbitrarily late positive lower bounds on partial density imply positive upper
density.  This is the main limsup bridge used by the global construction.
-/
theorem upperDensity_pos_of_frequently_partialDensity_ge {S : Set ℕ} {c : ℝ}
    (hc : 0 < c)
    (hfreq : ∀ N : ℕ, ∃ b : ℕ, N ≤ b ∧ c ≤ S.partialDensity Set.univ b) :
    0 < S.upperDensity := by
  have hbounded :
      Filter.atTop.IsBoundedUnder (· ≤ ·) (fun b : ℕ => S.partialDensity Set.univ b) := by
    refine isBoundedUnder_of_eventually_le (a := (1 : ℝ)) ?_
    exact Eventually.of_forall fun b => Set.partialDensity_le_one S Set.univ b
  have hle : c ≤ S.upperDensity := by
    rw [Set.upperDensity]
    refine le_limsup_of_le hbounded ?_
    intro B hB
    rcases eventually_atTop.mp hB with ⟨N, hN⟩
    rcases hfreq N with ⟨b, hbN, hcb⟩
    exact hcb.trans (hN b hbN)
  exact hc.trans_le hle

lemma ratio_mul_le_of_nat_mul_le {numerator denominator endpoint card : ℕ}
    (hdenominator : 0 < denominator)
    (hineq : numerator * endpoint ≤ denominator * card) :
    ((numerator : ℝ) / (denominator : ℝ)) * (endpoint : ℝ) ≤ (card : ℝ) := by
  have hdenposR : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  have hineqR : (numerator : ℝ) * (endpoint : ℝ) ≤
      (denominator : ℝ) * (card : ℝ) := by
    exact_mod_cast hineq
  field_simp [ne_of_gt hdenposR]
  nlinarith

theorem upperDensity_pos_of_frequent_finset_blocks {S : Set ℕ} {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hfreq : ∀ N : ℕ, ∃ endpoint : ℕ, ∃ B : Finset ℕ,
      N ≤ endpoint ∧ (∀ n ∈ B, n ∈ S ∧ n < endpoint) ∧
        numerator * endpoint ≤ denominator * B.card) :
    HasPositiveUpperDensity S := by
  unfold HasPositiveUpperDensity
  let c : ℝ := (numerator : ℝ) / (denominator : ℝ)
  have hc : 0 < c := by
    have hnR : (0 : ℝ) < numerator := by exact_mod_cast hnumerator
    have hdR : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
    exact div_pos hnR hdR
  refine upperDensity_pos_of_frequently_partialDensity_ge (S := S) (c := c) hc ?_
  intro N
  obtain ⟨endpoint, B, hN_endpoint, hB, hcount⟩ := hfreq (max N 1)
  have hendpoint_pos : 0 < endpoint := by omega
  refine ⟨endpoint, by omega, ?_⟩
  refine le_partialDensity_univ_nat_of_finset (S := S) (B := B) hendpoint_pos hB ?_
  exact ratio_mul_le_of_nat_mul_le hdenominator hcount

theorem finalSet_upperDensity_pos_of_frequent_stage_blocks {st : ℕ → StageState}
    {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hfreq : ∀ N : ℕ, ∃ k endpoint : ℕ, ∃ B : Finset ℕ,
      N ≤ endpoint ∧ (∀ n ∈ B, n ∈ (st k).S ∧ n < endpoint) ∧
        numerator * endpoint ≤ denominator * B.card) :
    HasPositiveUpperDensity (finalSet st) := by
  refine upperDensity_pos_of_frequent_finset_blocks hnumerator hdenominator ?_
  intro N
  obtain ⟨k, endpoint, B, hN_endpoint, hB, hcount⟩ := hfreq N
  refine ⟨endpoint, B, hN_endpoint, ?_, hcount⟩
  intro n hn
  exact ⟨mem_finalSet_of_mem_stage (hB n hn).1, (hB n hn).2⟩

theorem protectedBlock_partialDensity_lower {st : ℕ → StageState} (chain : StageChain st)
    {k a endpoint : ℕ} (hendpoint : endpoint ≤ (st k).X) (hendpoint_pos : 0 < endpoint)
    (cert : ProtectedBlockCertificate (st k).S a endpoint) :
    ((cert.densityNumerator : ℝ) / (cert.densityDenominator : ℝ)) ≤
      (privateSet (finalSet st) a).partialDensity Set.univ endpoint := by
  refine le_partialDensity_univ_nat_of_finset (S := privateSet (finalSet st) a)
    (B := cert.block) hendpoint_pos ?_ ?_
  · intro n hn
    exact ⟨privateSet_final_of_private_stage chain hendpoint cert hn,
      cert.block_lt_endpoint n hn⟩
  · exact ratio_mul_le_of_nat_mul_le cert.densityDenominator_pos cert.block_density_lower

theorem private_upperDensity_pos_of_frequent_protectedBlocks {st : ℕ → StageState}
    (chain : StageChain st) {a numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hfreq : ∀ N : ℕ,
      ∃ k endpoint : ℕ, ∃ cert : ProtectedBlockCertificate (st k).S a endpoint,
        N ≤ endpoint ∧ endpoint ≤ (st k).X ∧
          cert.densityNumerator = numerator ∧ cert.densityDenominator = denominator) :
    HasPositiveUpperDensity (privateSet (finalSet st) a) := by
  unfold HasPositiveUpperDensity
  let c : ℝ := (numerator : ℝ) / (denominator : ℝ)
  have hc : 0 < c := by
    have hnR : (0 : ℝ) < numerator := by exact_mod_cast hnumerator
    have hdR : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
    exact div_pos hnR hdR
  refine upperDensity_pos_of_frequently_partialDensity_ge (S := privateSet (finalSet st) a)
    (c := c) hc ?_
  intro N
  obtain ⟨k, endpoint, cert, hN_endpoint, hendpoint_X, hnum, hden⟩ := hfreq (max N 1)
  have hendpoint_pos : 0 < endpoint := by omega
  refine ⟨endpoint, by omega, ?_⟩
  have hpartial := protectedBlock_partialDensity_lower chain hendpoint_X hendpoint_pos cert
  simpa [c, hnum, hden] using hpartial

theorem private_upperDensity_pos_of_frequent_services {st : ℕ → StageState}
    (chain : StageChain st) {a numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hfreq : ∀ N : ℕ, ∃ k : ℕ, ∃ svc : ServiceExtension (st k) (st (k + 1)) a,
      N ≤ svc.protectedEndpoint ∧
        svc.protectedBlock.densityNumerator = numerator ∧
        svc.protectedBlock.densityDenominator = denominator) :
    HasPositiveUpperDensity (privateSet (finalSet st) a) := by
  refine private_upperDensity_pos_of_frequent_protectedBlocks chain hnumerator hdenominator ?_
  intro N
  obtain ⟨k, svc, hN, hnum, hden⟩ := hfreq N
  exact ⟨k + 1, svc.protectedEndpoint, svc.protectedBlock, hN,
    svc.protectedEndpoint_le_X, hnum, hden⟩

theorem mainTarget_of_frequent_services {st : ℕ → StageState} (chain : StageChain st)
    (hR_unbounded : ∀ n : ℕ, ∃ k : ℕ, n ≤ (st k).R)
    (hA_density : HasPositiveUpperDensity (finalSet st))
    (hservices :
      ∀ a ∈ finalSet st, ∃ numerator denominator : ℕ,
        0 < numerator ∧ 0 < denominator ∧
          ∀ N : ℕ, ∃ k : ℕ, ∃ svc : ServiceExtension (st k) (st (k + 1)) a,
            N ≤ svc.protectedEndpoint ∧
              svc.protectedBlock.densityNumerator = numerator ∧
              svc.protectedBlock.densityDenominator = denominator) :
    MainTarget := by
  refine mainTarget_of_finalSet_certificates chain hR_unbounded hA_density ?_
  intro a ha
  obtain ⟨numerator, denominator, hnumerator, hdenominator, hfreq⟩ := hservices a ha
  exact private_upperDensity_pos_of_frequent_services chain hnumerator hdenominator hfreq

theorem mainTarget_of_frequent_stage_blocks_and_services {st : ℕ → StageState}
    (chain : StageChain st)
    (hR_unbounded : ∀ n : ℕ, ∃ k : ℕ, n ≤ (st k).R)
    {setNumerator setDenominator : ℕ}
    (hsetNumerator : 0 < setNumerator) (hsetDenominator : 0 < setDenominator)
    (hsetBlocks : ∀ N : ℕ, ∃ k endpoint : ℕ, ∃ B : Finset ℕ,
      N ≤ endpoint ∧ (∀ n ∈ B, n ∈ (st k).S ∧ n < endpoint) ∧
        setNumerator * endpoint ≤ setDenominator * B.card)
    (hservices :
      ∀ a ∈ finalSet st, ∃ numerator denominator : ℕ,
        0 < numerator ∧ 0 < denominator ∧
          ∀ N : ℕ, ∃ k : ℕ, ∃ svc : ServiceExtension (st k) (st (k + 1)) a,
            N ≤ svc.protectedEndpoint ∧
              svc.protectedBlock.densityNumerator = numerator ∧
              svc.protectedBlock.densityDenominator = denominator) :
    MainTarget :=
  mainTarget_of_frequent_services chain hR_unbounded
    (finalSet_upperDensity_pos_of_frequent_stage_blocks hsetNumerator hsetDenominator
      hsetBlocks)
    hservices

end Erdos330

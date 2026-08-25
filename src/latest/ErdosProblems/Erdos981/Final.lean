import ErdosProblems.Erdos981.FixedPatterns
import ErdosProblems.Erdos981.LargeRange
import ErdosProblems.Erdos981.PrimeMoment
import ErdosProblems.Erdos746.Asymptotics

open scoped BigOperators NumberTheorySymbols Asymptotics
open Filter Finset

namespace Erdos981

def test_isBadTime (ε : ℝ) (p N : ℕ) : Prop :=
  ε * (N : ℝ) ≤ (legendrePartialSum p N : ℝ)

lemma test_eventualThreshold_last_failure {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hF : 1 < eventualThreshold ε p) :
    test_isBadTime ε p (eventualThreshold ε p - 1) := by
  let F := eventualThreshold ε p
  have hspec := eventualThreshold_spec_of_pos hε hp hpodd
  have hFm1 : 1 ≤ F - 1 := by omega
  have hnot : ¬ IsEventualThreshold ε p (F - 1) := by
    intro hgood
    have hle := eventualThreshold_minimal hgood
    dsimp [F] at hle
    omega
  have hex : ∃ N : ℕ, F - 1 ≤ N ∧
      ε * (N : ℝ) ≤ (legendrePartialSum p N : ℝ) := by
    by_contra hn
    push_neg at hn
    apply hnot
    refine ⟨hFm1, ?_⟩
    intro N hN
    exact hn N hN
  obtain ⟨N, hFN, hbad⟩ := hex
  have hNF : N < F := by
    by_contra hn
    have hgood := hspec.2 N (Nat.le_of_not_gt hn)
    exact (not_lt_of_ge hbad) hgood
  have hN : N = F - 1 := by omega
  simpa [test_isBadTime, F, hN] using hbad

lemma test_truncatedThreshold_eq_eventualThreshold_of_le {ε : ℝ} (hε : 0 < ε)
    {p M : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hFM : eventualThreshold ε p ≤ M + 1) :
    truncatedThreshold ε p M = eventualThreshold ε p := by
  let F := eventualThreshold ε p
  let T := truncatedThreshold ε p M
  have hTF : T ≤ F := truncatedThreshold_le_eventualThreshold
    (exists_eventualThreshold hε hp hpodd)
  apply Nat.le_antisymm hTF
  by_contra hnot
  have hTF' : T < F := Nat.lt_of_not_ge hnot
  have hF1 : 1 < F := (one_le_truncatedThreshold ε p M).trans_lt hTF'
  have hbad := test_eventualThreshold_last_failure hε hp hpodd hF1
  have hFm1T : T ≤ F - 1 := by omega
  have hFm1M : F - 1 ≤ M := by omega
  have hgood := (truncatedThreshold_spec ε p M).2 (F - 1) hFm1T hFm1M
  exact (not_lt_of_ge hbad) hgood

lemma test_threshold_sub_truncated_nonneg {ε : ℝ} (hε : 0 < ε)
    {p M : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    0 ≤ (eventualThreshold ε p : ℝ) - truncatedThreshold ε p M := by
  have hle : (truncatedThreshold ε p M : ℝ) ≤ eventualThreshold ε p := by
    exact_mod_cast truncatedThreshold_le_eventualThreshold
      (exists_eventualThreshold hε hp hpodd)
  linarith

lemma test_threshold_sub_truncated_le_of_lt {ε : ℝ} (hε : 0 < ε)
    {p M : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hM : M < eventualThreshold ε p - 1) :
    (eventualThreshold ε p : ℝ) - truncatedThreshold ε p M ≤
      ((eventualThreshold ε p - 1 : ℕ) : ℝ) + 1 := by
  have hT : 1 ≤ truncatedThreshold ε p M := one_le_truncatedThreshold ε p M
  have hF : 1 ≤ eventualThreshold ε p :=
    one_le_eventualThreshold_of_pos hε hp hpodd
  have hcast : (((eventualThreshold ε p - 1 : ℕ) : ℝ) + 1) =
      (eventualThreshold ε p : ℝ) := by
    rw [Nat.cast_sub hF]
    norm_num
  rw [hcast]
  have hTnonneg : (0 : ℝ) ≤ truncatedThreshold ε p M := by positivity
  linarith

noncomputable def test_thresholdFiber
    (ε : ℝ) (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter fun p => eventualThreshold ε p = N + 1

lemma test_threshold_tail_sum_le_fibers {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) {M B : ℕ}
    (hprime : ∀ p ∈ S, p.Prime ∧ Odd p)
    (hupper : ∀ p ∈ S, eventualThreshold ε p ≤ B + 1) :
    (∑ p ∈ S, ((eventualThreshold ε p : ℝ) -
        truncatedThreshold ε p M)) ≤
      ∑ N ∈ Finset.Icc (M + 1) B,
        ((N + 1 : ℕ) : ℝ) * (test_thresholdFiber ε S N).card := by
  classical
  have hpoint : ∀ p ∈ S,
      ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M) ≤
        ∑ N ∈ Finset.Icc (M + 1) B,
          if eventualThreshold ε p = N + 1 then ((N + 1 : ℕ) : ℝ) else 0 := by
    intro p hpS
    have hp := (hprime p hpS).1
    have hpodd := (hprime p hpS).2
    by_cases hlate : M < eventualThreshold ε p - 1
    · have hF1 : 1 ≤ eventualThreshold ε p :=
        one_le_eventualThreshold_of_pos hε hp hpodd
      have hmem : eventualThreshold ε p - 1 ∈ Finset.Icc (M + 1) B := by
        rw [Finset.mem_Icc]
        constructor
        · omega
        · have := hupper p hpS
          omega
      have hone : eventualThreshold ε p =
          (eventualThreshold ε p - 1) + 1 := by omega
      calc
        ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M) ≤
            (((eventualThreshold ε p - 1 : ℕ) : ℝ) + 1) :=
          test_threshold_sub_truncated_le_of_lt hε hp hpodd hlate
        _ = ((((eventualThreshold ε p - 1) + 1 : ℕ) : ℝ)) := by norm_num
        _ ≤ ∑ N ∈ Finset.Icc (M + 1) B,
              if eventualThreshold ε p = N + 1 then ((N + 1 : ℕ) : ℝ) else 0 := by
          have hs := Finset.single_le_sum
            (s := Finset.Icc (M + 1) B)
            (f := fun N => if eventualThreshold ε p = N + 1 then
              ((N + 1 : ℕ) : ℝ) else 0)
            (fun N _ => by split <;> positivity) hmem
          rw [if_pos hone] at hs
          exact hs
    · have hFM : eventualThreshold ε p ≤ M + 1 := by
        have hF1 := one_le_eventualThreshold_of_pos hε hp hpodd
        omega
      rw [test_truncatedThreshold_eq_eventualThreshold_of_le hε hp hpodd hFM]
      simp only [sub_self]
      positivity
  calc
    (∑ p ∈ S, ((eventualThreshold ε p : ℝ) -
        truncatedThreshold ε p M)) ≤
        ∑ p ∈ S, ∑ N ∈ Finset.Icc (M + 1) B,
          if eventualThreshold ε p = N + 1 then ((N + 1 : ℕ) : ℝ) else 0 := by
      exact Finset.sum_le_sum hpoint
    _ = ∑ N ∈ Finset.Icc (M + 1) B,
        ∑ p ∈ S,
          if eventualThreshold ε p = N + 1 then ((N + 1 : ℕ) : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ N ∈ Finset.Icc (M + 1) B,
        ((N + 1 : ℕ) : ℝ) * (test_thresholdFiber ε S N).card := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [test_thresholdFiber]
      calc
        (∑ p ∈ S, if eventualThreshold ε p = N + 1 then
            ((N + 1 : ℕ) : ℝ) else 0) =
            ∑ p ∈ S.filter (fun p => eventualThreshold ε p = N + 1),
              ((N + 1 : ℕ) : ℝ) := by
                rw [Finset.sum_filter]
        _ = ((N + 1 : ℕ) : ℝ) *
            (S.filter (fun p => eventualThreshold ε p = N + 1)).card := by
              simp only [Finset.sum_const, Finset.card_filter, nsmul_eq_mul,
                Nat.cast_add, Nat.cast_one]
              ring

lemma test_thresholdFiber_subset_endpointBad {ε : ℝ} (hε : 0 < ε)
    {x N : ℕ} (hN : 1 ≤ N) :
    test_thresholdFiber ε (oddPrimesBelow x) N ⊆
      test_endpointBadPrimes ε N x := by
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpOddData := Finset.mem_filter.mp hpData.1
  have hF : eventualThreshold ε p = N + 1 := hpData.2
  have hlast := test_eventualThreshold_last_failure hε hpOddData.2.1
    hpOddData.2.2 (by omega)
  rw [hF] at hlast
  have hsub : N + 1 - 1 = N := by omega
  rw [hsub] at hlast
  exact Finset.mem_filter.mpr
    ⟨hpOddData.1, hpOddData.2.1, hpOddData.2.2, hlast⟩

lemma test_endpointBadPrimes_subset_oddPrimeBad
    (ε : ℝ) (N x : ℕ) :
    test_endpointBadPrimes ε N x ⊆ test_oddPrimeBad ε N x := by
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hpData.1
        omega), hpData.2⟩

lemma test_endpointBadPrimes_subset_oddBadModuli
    (ε : ℝ) (N x : ℕ) :
    test_endpointBadPrimes ε N x ⊆ oddBadModuli ε N x := by
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr
    ⟨hpData.1, hpData.2.2.1, hpData.2.2.2⟩

lemma test_eventually_two_add_const_mul_sqrt_mul_log_le_threeFifths_rpow
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      2 + C * (Real.sqrt x * Real.log x) ≤ x ^ (3 / 5 : ℝ) := by
  let c : ℝ := 1 / (2 * (C + 1))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlog :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound hc
  have hpow := (tendsto_rpow_atTop
    (show (0 : ℝ) < 3 / 5 by norm_num)).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hlog, hpow, eventually_gt_atTop (1 : ℝ)] with x hxlog hxpow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hdeltaPow : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hdeltaPow.le] at hxlog
  have hrpow : Real.sqrt x * x ^ (1 / 10 : ℝ) = x ^ (3 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    congr 2
    norm_num
  have hcoef : C * c ≤ 1 / 2 := by
    dsimp [c]
    have hden : 0 < 2 * (C + 1) := by positivity
    have hquot : C / (2 * (C + 1)) ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith
    convert hquot using 1 <;> ring
  have hmain : C * (Real.sqrt x * Real.log x) ≤
      (1 / 2 : ℝ) * x ^ (3 / 5 : ℝ) := by
    calc
      C * (Real.sqrt x * Real.log x) ≤
          C * (Real.sqrt x * (c * x ^ (1 / 10 : ℝ))) := by
        gcongr
      _ = (C * c) * x ^ (3 / 5 : ℝ) := by rw [← hrpow]; ring
      _ ≤ (1 / 2 : ℝ) * x ^ (3 / 5 : ℝ) := by
        gcongr
  have htwo : 2 ≤ (1 / 2 : ℝ) * x ^ (3 / 5 : ℝ) := by
    nlinarith
  nlinarith

lemma test_eventually_eventualThreshold_le_threeFifths_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      p.Prime → Odd p →
        (eventualThreshold ε p : ℝ) ≤ (p : ℝ) ^ (3 / 5 : ℝ) := by
  have hevent := tendsto_natCast_atTop_atTop.eventually
    (test_eventually_two_add_const_mul_sqrt_mul_log_le_threeFifths_rpow
      ε⁻¹ (inv_nonneg.mpr hε.le))
  filter_upwards [hevent, eventually_ge_atTop 3] with p hpbound hp3
  intro hp hpodd
  have hthreshold := test_eventualThreshold_le_polya hε hp hpodd
  calc
    (eventualThreshold ε p : ℝ) ≤ (test_polyaThreshold ε p : ℕ) := by
      exact_mod_cast hthreshold
    _ ≤ 2 + ε⁻¹ * (Real.sqrt (p : ℝ) * Real.log (p : ℝ)) := by
      rw [test_polyaThreshold, Nat.cast_add, Nat.cast_one]
      have hceil := Nat.ceil_lt_add_one
        (show 0 ≤ (Real.sqrt (p : ℝ) * Real.log (p : ℝ)) / ε by
          positivity)
      have hεne : ε ≠ 0 := hε.ne'
      rw [div_eq_inv_mul, mul_comm] at hceil ⊢
      linarith
    _ ≤ (p : ℝ) ^ (3 / 5 : ℝ) := hpbound

lemma test_sum_Icc_weighted_inv_cube_le {M B : ℕ} (hM : 1 ≤ M) :
    (∑ N ∈ Finset.Icc (M + 1) B,
        ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) ≤ 2 / (M : ℝ) := by
  classical
  by_cases hMB : M + 1 ≤ B
  · have hpoint : ∀ N ∈ Finset.Icc (M + 1) B,
        ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3 ≤
          2 * (1 / ((N - 1 : ℕ) : ℝ) - 1 / (N : ℝ)) := by
      intro N hN
      have hN2 : 2 ≤ N := by
        have := (Finset.mem_Icc.mp hN).1
        omega
      have hNpos : (0 : ℝ) < N := by positivity
      have hNm1pos : (0 : ℝ) < (N - 1 : ℕ) := by
        exact_mod_cast (by omega : 0 < N - 1)
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      have hNreal : (1 : ℝ) < (N : ℝ) := by
        exact_mod_cast (by omega : 1 < N)
      have hNm1real : (0 : ℝ) < (N : ℝ) - 1 := sub_pos.mpr hNreal
      have hrhs : 2 * (1 / ((N : ℝ) - 1) - 1 / (N : ℝ)) =
          2 / ((N : ℝ) * ((N : ℝ) - 1)) := by
        field_simp [hNpos.ne', hNm1real.ne']
        ring
      rw [hrhs]
      rw [div_le_div_iff₀ (pow_pos hNpos 3)
        (mul_pos hNpos hNm1real)]
      push_cast
      ring_nf
      nlinarith [sq_nonneg (N : ℝ)]
    calc
      (∑ N ∈ Finset.Icc (M + 1) B,
          ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) ≤
          ∑ N ∈ Finset.Icc (M + 1) B,
            2 * (1 / ((N - 1 : ℕ) : ℝ) - 1 / (N : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = 2 * (1 / (M : ℝ) - 1 / (B : ℝ)) := by
        rw [← Finset.mul_sum]
        have hset : Finset.Icc (M + 1) B = Finset.Ico (M + 1) (B + 1) := by
          ext N
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [hset]
        have htel := Finset.sum_Ico_sub
          (fun i : ℕ => -(1 / ((i - 1 : ℕ) : ℝ)))
          (show M + 1 ≤ B + 1 by omega)
        have hMcast : (((M + 1 - 1 : ℕ) : ℝ)) = M := by simp
        have hBcast : (((B + 1 - 1 : ℕ) : ℝ)) = B := by simp
        simpa [hMcast, hBcast, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using htel
      _ ≤ 2 / (M : ℝ) := by
        have hBnonneg : 0 ≤ 1 / (B : ℝ) := by positivity
        calc
          2 * (1 / (M : ℝ) - 1 / (B : ℝ)) =
              2 / (M : ℝ) - 2 * (1 / (B : ℝ)) := by ring
          _ ≤ 2 / (M : ℝ) := sub_le_self _ (mul_nonneg (by norm_num) hBnonneg)
  · have hempty : Finset.Icc (M + 1) B = ∅ := by
      exact Finset.Icc_eq_empty hMB
    rw [hempty]
    simp
    positivity

lemma test_sum_Icc_weighted_pow_twenty_le (A B : ℕ) :
    (∑ N ∈ Finset.Icc A B,
        ((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20) ≤ ((B + 1 : ℕ) : ℝ) ^ 22 := by
  have hterm : ∀ N ∈ Finset.Icc A B,
      ((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20 ≤ ((B + 1 : ℕ) : ℝ) ^ 21 := by
    intro N hN
    have hNB : N ≤ B := (Finset.mem_Icc.mp hN).2
    have hN1 : ((N + 1 : ℕ) : ℝ) ≤ (B + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hNB 1
    have hpow : (N : ℝ) ^ 20 ≤ (B + 1 : ℝ) ^ 20 := by
      gcongr
      exact_mod_cast hNB.trans (Nat.le_succ B)
    calc
      ((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20 ≤
          (B + 1 : ℝ) * (B + 1 : ℝ) ^ 20 :=
        mul_le_mul hN1 hpow (by positivity) (by positivity)
      _ = ((B + 1 : ℕ) : ℝ) ^ 21 := by
        push_cast
        ring
  calc
    (∑ N ∈ Finset.Icc A B,
        ((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20) ≤
        ∑ _N ∈ Finset.Icc A B, ((B + 1 : ℕ) : ℝ) ^ 21 :=
      Finset.sum_le_sum hterm
    _ = ((Finset.Icc A B).card : ℝ) * ((B + 1 : ℕ) : ℝ) ^ 21 := by
      simp
    _ ≤ ((B + 1 : ℕ) : ℝ) * ((B + 1 : ℕ) : ℝ) ^ 21 := by
      gcongr
      exact_mod_cast (by rw [Nat.card_Icc]; omega :
        (Finset.Icc A B).card ≤ B + 1)
    _ = ((B + 1 : ℕ) : ℝ) ^ 22 := by ring

lemma test_primeMoment_range_bound {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) {N₀ X₀ M x : ℕ} (hM1 : 1 ≤ M)
    (hMN₀ : N₀ ≤ M) (hx : X₀ ≤ x)
    (hbound : ∀ y ≥ X₀, ∀ N ≥ N₀,
      N ≤ Erdos387.binaryLogScale y ^ 3 →
        ((test_oddPrimeBad ε N y).card : ℝ) ≤
          (ε ^ 20)⁻¹ *
            ((BoundedGaps.Maynard.primeCountTotal (2 * y) : ℝ) / (N : ℝ) ^ 3 +
              4 * C * ((2 * y : ℕ) : ℝ) * (N : ℝ) ^ 20 /
                Real.rpow (Real.log ((2 * y : ℕ) : ℝ)) 100)) :
    (∑ N ∈ Finset.Icc (M + 1) (Erdos387.binaryLogScale x ^ 3),
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
      (ε ^ 20)⁻¹ *
        ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) * (2 / (M : ℝ)) +
          (4 * C * ((2 * x : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
            (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ) ^ 22)) := by
  classical
  let L := Erdos387.binaryLogScale x ^ 3
  have hterm : ∀ N ∈ Finset.Icc (M + 1) L,
      ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card ≤
        (ε ^ 20)⁻¹ *
          ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
              (((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) +
            (4 * C * ((2 * x : ℕ) : ℝ) /
                Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
              (((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20)) := by
    intro N hN
    have hNrange := Finset.mem_Icc.mp hN
    have hN1 : 1 ≤ N := by omega
    have hN₀ : N₀ ≤ N := hMN₀.trans (by omega)
    have hNL : N ≤ Erdos387.binaryLogScale x ^ 3 := hNrange.2
    have hfibEnd := Finset.card_le_card
      (test_thresholdFiber_subset_endpointBad (x := x) hε hN1)
    have hendBad := Finset.card_le_card
      (test_endpointBadPrimes_subset_oddPrimeBad ε N x)
    have hcard : ((test_thresholdFiber ε (oddPrimesBelow x) N).card : ℝ) ≤
        (test_oddPrimeBad ε N x).card := by
      exact_mod_cast hfibEnd.trans hendBad
    have hbad := hbound x hx N hN₀ hNL
    have hweight : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
    calc
      ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card ≤
          ((N + 1 : ℕ) : ℝ) * (test_oddPrimeBad ε N x).card :=
        mul_le_mul_of_nonneg_left hcard hweight
      _ ≤ ((N + 1 : ℕ) : ℝ) *
          ((ε ^ 20)⁻¹ *
            ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) / (N : ℝ) ^ 3 +
              4 * C * ((2 * x : ℕ) : ℝ) * (N : ℝ) ^ 20 /
                Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100)) :=
        mul_le_mul_of_nonneg_left hbad hweight
      _ = _ := by ring
  calc
    (∑ N ∈ Finset.Icc (M + 1) L,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
        ∑ N ∈ Finset.Icc (M + 1) L,
          (ε ^ 20)⁻¹ *
            ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) +
              (4 * C * ((2 * x : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
                (((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20)) :=
      Finset.sum_le_sum hterm
    _ = (ε ^ 20)⁻¹ *
        ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
            (∑ N ∈ Finset.Icc (M + 1) L,
              ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) +
          (4 * C * ((2 * x : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
            (∑ N ∈ Finset.Icc (M + 1) L,
              ((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (ε ^ 20)⁻¹ *
        ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) * (2 / (M : ℝ)) +
          (4 * C * ((2 * x : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
            (((L + 1 : ℕ) : ℝ) ^ 22)) := by
      have hinv := test_sum_Icc_weighted_inv_cube_le (B := L) hM1
      have hpow := test_sum_Icc_weighted_pow_twenty_le (M + 1) L
      have hpi : (0 : ℝ) ≤ BoundedGaps.Maynard.primeCountTotal (2 * x) := by
        positivity
      have hcoeff : 0 ≤ 4 * C * ((2 * x : ℕ) : ℝ) /
          Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100 := by
        exact div_nonneg (by positivity)
          (Real.rpow_nonneg (by positivity) _)
      have hinner := add_le_add
        (mul_le_mul_of_nonneg_left hinv hpi)
        (mul_le_mul_of_nonneg_left hpow hcoeff)
      exact mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr (pow_nonneg hε.le 20))
    _ = _ := by rfl

lemma test_allOddMoment_range_bound {ε : ℝ} (hε : 0 < ε)
    {N₀ L H x : ℕ} (hL1 : 1 ≤ L) (hLN₀ : N₀ ≤ L)
    (hbound : ∀ N ≥ N₀, ∀ y : ℕ,
      ((oddBadModuli ε N y).card : ℝ) ≤
        (ε ^ 20)⁻¹ * ((y : ℝ) / (N : ℝ) ^ 3 + 4 * (N : ℝ) ^ 20)) :
    (∑ N ∈ Finset.Icc (L + 1) H,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
      (ε ^ 20)⁻¹ *
        ((x : ℝ) * (2 / (L : ℝ)) + 4 * (((H + 1 : ℕ) : ℝ) ^ 22)) := by
  classical
  have hterm : ∀ N ∈ Finset.Icc (L + 1) H,
      ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card ≤
        (ε ^ 20)⁻¹ *
          ((x : ℝ) * (((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) +
            4 * (((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20)) := by
    intro N hN
    have hNrange := Finset.mem_Icc.mp hN
    have hN1 : 1 ≤ N := by omega
    have hN₀ : N₀ ≤ N := hLN₀.trans (by omega)
    have hfibEnd := Finset.card_le_card
      (test_thresholdFiber_subset_endpointBad (x := x) hε hN1)
    have hendBad := Finset.card_le_card
      (test_endpointBadPrimes_subset_oddBadModuli ε N x)
    have hcard : ((test_thresholdFiber ε (oddPrimesBelow x) N).card : ℝ) ≤
        (oddBadModuli ε N x).card := by
      exact_mod_cast hfibEnd.trans hendBad
    have hbad := hbound N hN₀ x
    have hweight : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
    calc
      ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card ≤
          ((N + 1 : ℕ) : ℝ) * (oddBadModuli ε N x).card :=
        mul_le_mul_of_nonneg_left hcard hweight
      _ ≤ ((N + 1 : ℕ) : ℝ) *
          ((ε ^ 20)⁻¹ * ((x : ℝ) / (N : ℝ) ^ 3 + 4 * (N : ℝ) ^ 20)) :=
        mul_le_mul_of_nonneg_left hbad hweight
      _ = _ := by ring
  calc
    (∑ N ∈ Finset.Icc (L + 1) H,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
        ∑ N ∈ Finset.Icc (L + 1) H,
          (ε ^ 20)⁻¹ *
            ((x : ℝ) * (((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) +
              4 * (((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20)) :=
      Finset.sum_le_sum hterm
    _ = (ε ^ 20)⁻¹ *
        ((x : ℝ) * (∑ N ∈ Finset.Icc (L + 1) H,
          ((N + 1 : ℕ) : ℝ) / (N : ℝ) ^ 3) +
          4 * (∑ N ∈ Finset.Icc (L + 1) H,
            ((N + 1 : ℕ) : ℝ) * (N : ℝ) ^ 20)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (ε ^ 20)⁻¹ *
        ((x : ℝ) * (2 / (L : ℝ)) + 4 * (((H + 1 : ℕ) : ℝ) ^ 22)) := by
      have hinv := test_sum_Icc_weighted_inv_cube_le (B := H) hL1
      have hpow := test_sum_Icc_weighted_pow_twenty_le (L + 1) H
      have hinner := add_le_add
        (mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ (x : ℝ) by positivity))
        (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4))
      exact mul_le_mul_of_nonneg_left hinner
        (inv_nonneg.mpr (pow_nonneg hε.le 20))

def test_dyadicIndices (H B : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 B + 1)).filter fun j => H < 2 ^ (j + 1)

lemma test_dyadic_cover {H B N : ℕ} (hHN : H < N) (hNB : N ≤ B) :
    let j := Nat.log 2 N
    j ∈ test_dyadicIndices H B ∧ N ∈ Finset.Icc (2 ^ j) (2 * 2 ^ j) := by
  dsimp
  have hN0 : N ≠ 0 := by omega
  have hjmono : Nat.log 2 N ≤ Nat.log 2 B := Nat.log_mono_right hNB
  have hpowle : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hltpow : N < 2 ^ (Nat.log 2 N + 1) := by
    rw [← Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hN0]
    omega
  have hpoweq : 2 ^ (Nat.log 2 N + 1) = 2 * 2 ^ Nat.log 2 N := by ring
  constructor
  · rw [test_dyadicIndices, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by simpa [hpoweq] using hHN.trans hltpow⟩
  · rw [Finset.mem_Icc]
    exact ⟨hpowle, by omega⟩

lemma test_largeFiberSum_le_dyadicBlocks {ε : ℝ} (hε : 0 < ε)
    {H B x : ℕ} :
    (∑ N ∈ Finset.Icc (H + 1) B,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
      (((B + 1 : ℕ) : ℝ) *
        ∑ j ∈ test_dyadicIndices H B,
          ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ)) := by
  classical
  let T := Finset.Icc (H + 1) B
  let active := (oddPrimesBelow x).filter fun p =>
    eventualThreshold ε p - 1 ∈ T
  have hweight : (∑ N ∈ T,
      ((N + 1 : ℕ) : ℝ) *
        (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
      ((B + 1 : ℕ) : ℝ) *
        ∑ N ∈ T, ((test_thresholdFiber ε (oddPrimesBelow x) N).card : ℝ) := by
    calc
      (∑ N ∈ T, ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
          ∑ N ∈ T, ((B + 1 : ℕ) : ℝ) *
            (test_thresholdFiber ε (oddPrimesBelow x) N).card := by
        apply Finset.sum_le_sum
        intro N hN
        have hNB : N ≤ B := (Finset.mem_Icc.mp hN).2
        gcongr
      _ = ((B + 1 : ℕ) : ℝ) *
          ∑ N ∈ T, ((test_thresholdFiber ε (oddPrimesBelow x) N).card : ℝ) := by
        rw [Finset.mul_sum]
  have hfibers : (∑ N ∈ T,
      (test_thresholdFiber ε (oddPrimesBelow x) N).card) = active.card := by
    calc
      (∑ N ∈ T, (test_thresholdFiber ε (oddPrimesBelow x) N).card) =
          ∑ N ∈ T, ((oddPrimesBelow x).filter fun p =>
            eventualThreshold ε p - 1 = N).card := by
        apply Finset.sum_congr rfl
        intro N hN
        congr 1
        ext p
        simp only [test_thresholdFiber, Finset.mem_filter]
        constructor
        · rintro ⟨hpS, hF⟩
          refine ⟨hpS, ?_⟩
          rw [hF]
          omega
        · rintro ⟨hpS, hF⟩
          have hpData := Finset.mem_filter.mp hpS
          have hF1 := one_le_eventualThreshold_of_pos hε hpData.2.1 hpData.2.2
          exact ⟨hpS, by omega⟩
      _ = active.card := by
        simpa [active] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (oddPrimesBelow x) T (fun p => eventualThreshold ε p - 1))
  have hactiveSubset : active ⊆
      (test_dyadicIndices H B).biUnion fun j =>
        test_blockBadPrimes ε (2 ^ j) x := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpOddData := Finset.mem_filter.mp hpData.1
    have htime := Finset.mem_Icc.mp hpData.2
    let N := eventualThreshold ε p - 1
    have hHN : H < N := by dsimp [N]; omega
    have hNB : N ≤ B := htime.2
    obtain ⟨hj, hNblock⟩ := test_dyadic_cover hHN hNB
    have hF1 : 1 < eventualThreshold ε p := by
      dsimp [N] at hHN
      omega
    have hbad := test_eventualThreshold_last_failure hε hpOddData.2.1
      hpOddData.2.2 hF1
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 N, hj, ?_⟩
    rw [test_mem_blockBadPrimes]
    exact ⟨Finset.mem_range.mp hpOddData.1, hpOddData.2.1, hpOddData.2.2,
      ⟨N, hNblock, hbad⟩⟩
  have hcardActive : (active.card : ℝ) ≤
      ∑ j ∈ test_dyadicIndices H B,
        ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ) := by
    calc
      (active.card : ℝ) ≤
          (((test_dyadicIndices H B).biUnion fun j =>
            test_blockBadPrimes ε (2 ^ j) x).card : ℕ) := by
        exact_mod_cast Finset.card_le_card hactiveSubset
      _ ≤ ∑ j ∈ test_dyadicIndices H B,
          ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
  calc
    (∑ N ∈ Finset.Icc (H + 1) B,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
        ((B + 1 : ℕ) : ℝ) *
          ∑ N ∈ T, ((test_thresholdFiber ε (oddPrimesBelow x) N).card : ℝ) :=
      hweight
    _ = ((B + 1 : ℕ) : ℝ) * (active.card : ℝ) := by
      rw [← Nat.cast_sum, hfibers]
    _ ≤ ((B + 1 : ℕ) : ℝ) *
        ∑ j ∈ test_dyadicIndices H B,
          ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ) :=
      mul_le_mul_of_nonneg_left hcardActive (by positivity)

lemma test_blockBadPrimes_simplified_bound {ε : ℝ} (hε : 0 < ε)
    {K H A B x : ℕ} (hH : 1 ≤ H) (hHA : H < 2 * A) (hAB : A ≤ B)
    (hraw : (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_blockBadPrimes ε A x).card : ℝ) ≤
        ((2 * K + 2 : ℕ) : ℝ) *
          ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
            Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
              ((3 * A : ℕ) : ℝ) ^ 300)) :
    ((test_blockBadPrimes ε A x).card : ℝ) ≤
      ((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
        Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
          (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300) := by
  have hA : 1 ≤ A := by omega
  have hApos : (0 : ℝ) < A := by positivity
  have hHpos : (0 : ℝ) < H := by positivity
  have hbaseA : (1 : ℝ) ≤ (3 * A : ℕ) := by
    exact_mod_cast (show 1 ≤ 3 * A by omega)
  have henvExp : Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) ≤
      Real.rpow ((3 * A : ℕ) : ℝ) (1 / 2 : ℝ) := by
    unfold Erdos439.PowerDecay.divisorSubpowerEnvelope
    exact Real.rpow_le_rpow_of_exponent_le hbaseA (by norm_num)
  have hbaseMono : ((3 * A : ℕ) : ℝ) ≤ ((3 * B : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 3 hAB
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have henv : Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) ≤
      Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) :=
    henvExp.trans (Real.rpow_le_rpow (by positivity) hbaseMono hhalf)
  have hRnonneg : 0 ≤ Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hDnonneg : (0 : ℝ) ≤ (2 * K + 2 : ℕ) := by positivity
  have hsumNonneg : 0 ≤ ((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2 := by positivity
  have hraw' : (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_blockBadPrimes ε A x).card : ℝ) ≤
      ((2 * K + 2 : ℕ) : ℝ) *
        ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
            ((3 * A : ℕ) : ℝ) ^ 300) := by
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left henv hsumNonneg)
        (pow_nonneg (by positivity) 300)) hDnonneg)
  have hden : 0 < (ε / 3 * (A : ℝ)) ^ 600 := by positivity
  have hdiv : ((test_blockBadPrimes ε A x).card : ℝ) ≤
      (((2 * K + 2 : ℕ) : ℝ) *
        ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
            ((3 * A : ℕ) : ℝ) ^ 300)) /
        (ε / 3 * (A : ℝ)) ^ 600 :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hraw')
  have hnormalize :
      (((2 * K + 2 : ℕ) : ℝ) *
        ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
            ((3 * A : ℕ) : ℝ) ^ 300)) /
        (ε / 3 * (A : ℝ)) ^ 600 =
      ((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 *
        Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
          ((3 : ℝ) ^ 600 + (3 : ℝ) ^ 300 * (x : ℝ) ^ 2 /
            (A : ℝ) ^ 300) := by
    push_cast
    field_simp [hε.ne', hApos.ne']
  rw [hnormalize] at hdiv
  have hHApow : (H : ℝ) ^ 300 ≤ (2 : ℝ) ^ 300 * (A : ℝ) ^ 300 := by
    have hHAreal : (H : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hHA.le
    have hp := pow_le_pow_left₀ (by positivity) hHAreal 300
    rw [mul_pow] at hp
    exact hp
  have hsecond : (3 : ℝ) ^ 300 * (x : ℝ) ^ 2 / (A : ℝ) ^ 300 ≤
      (6 : ℝ) ^ 600 * ((x : ℝ) ^ 2 / (H : ℝ) ^ 300) := by
    have hA300 : 0 < (A : ℝ) ^ 300 := pow_pos hApos _
    have hH300 : 0 < (H : ℝ) ^ 300 := pow_pos hHpos _
    rw [div_le_iff₀ hA300]
    have hrhs : (6 : ℝ) ^ 600 * ((x : ℝ) ^ 2 / (H : ℝ) ^ 300) *
          (A : ℝ) ^ 300 =
        ((6 : ℝ) ^ 600 * (x : ℝ) ^ 2 * (A : ℝ) ^ 300) /
          (H : ℝ) ^ 300 := by ring
    rw [hrhs, le_div_iff₀ hH300]
    have hx2 : 0 ≤ (x : ℝ) ^ 2 := sq_nonneg _
    calc
      (3 : ℝ) ^ 300 * (x : ℝ) ^ 2 * (H : ℝ) ^ 300 ≤
          (3 : ℝ) ^ 300 * (x : ℝ) ^ 2 *
            ((2 : ℝ) ^ 300 * (A : ℝ) ^ 300) := by
        exact mul_le_mul_of_nonneg_left hHApow
          (mul_nonneg (pow_nonneg (by norm_num) 300) hx2)
      _ = ((3 : ℝ) ^ 300 * (2 : ℝ) ^ 300) *
          ((x : ℝ) ^ 2 * (A : ℝ) ^ 300) := by ring
      _ ≤ (6 : ℝ) ^ 600 * ((x : ℝ) ^ 2 * (A : ℝ) ^ 300) := by
        have hcoeff : (3 : ℝ) ^ 300 * (2 : ℝ) ^ 300 ≤ (6 : ℝ) ^ 600 := by
          calc
            (3 : ℝ) ^ 300 * (2 : ℝ) ^ 300 = (6 : ℝ) ^ 300 := by
              rw [← mul_pow]
              norm_num
            _ ≤ (6 : ℝ) ^ 600 :=
              pow_le_pow_right₀ (a := (6 : ℝ)) (m := 300) (n := 600)
                (by norm_num) (by norm_num)
        exact mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg hx2 (pow_nonneg (by positivity) 300))
      _ = (6 : ℝ) ^ 600 * (x : ℝ) ^ 2 * (A : ℝ) ^ 300 := by ring
  have hfirst : (3 : ℝ) ^ 600 ≤ (6 : ℝ) ^ 600 := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) 600
  have hsum : (3 : ℝ) ^ 600 +
        (3 : ℝ) ^ 300 * (x : ℝ) ^ 2 / (A : ℝ) ^ 300 ≤
      (6 : ℝ) ^ 600 * (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300) := by
    calc
      _ ≤ (6 : ℝ) ^ 600 +
          (6 : ℝ) ^ 600 * ((x : ℝ) ^ 2 / (H : ℝ) ^ 300) :=
        add_le_add hfirst hsecond
      _ = _ := by ring
  let fac : ℝ := ((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 *
    Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ)
  have hfac : 0 ≤ fac := by
    dsimp [fac]
    positivity
  calc
    ((test_blockBadPrimes ε A x).card : ℝ) ≤
        fac * ((3 : ℝ) ^ 600 + (3 : ℝ) ^ 300 * (x : ℝ) ^ 2 /
          (A : ℝ) ^ 300) := by simpa [fac, mul_assoc] using hdiv
    _ ≤ fac * ((6 : ℝ) ^ 600 *
        (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300)) :=
      mul_le_mul_of_nonneg_left hsum hfac
    _ = _ := by
      dsimp [fac]
      ring

lemma test_largeFiberSum_bound {ε : ℝ} (hε : 0 < ε)
    {K A₀ H B x : ℕ} (hH : 1 ≤ H) (hHA₀ : 2 * A₀ ≤ H)
    (hlog : Nat.log 2 B + 1 ≤ H)
    (hraw : ∀ A ≥ A₀,
      (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_blockBadPrimes ε A x).card : ℝ) ≤
        ((2 * K + 2 : ℕ) : ℝ) *
          ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
            Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
              ((3 * A : ℕ) : ℝ) ^ 300)) :
    (∑ N ∈ Finset.Icc (H + 1) B,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
      ((B + 1 : ℕ) : ℝ) * (H : ℝ) *
        (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
          Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
            (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300)) := by
  classical
  by_cases hBzero : B = 0
  · subst B
    simp
  have hlarge := test_largeFiberSum_le_dyadicBlocks hε (H := H) (B := B) (x := x)
  let D : ℝ := ((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
    Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
      (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300)
  have hterm : ∀ j ∈ test_dyadicIndices H B,
      ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ) ≤ D := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjRange := Finset.mem_range.mp hjData.1
    have hHA : H < 2 * 2 ^ j := by
      simpa [pow_succ'] using hjData.2
    have hAj : A₀ ≤ 2 ^ j := by omega
    have hAB : 2 ^ j ≤ B := by
      have hpow := Nat.pow_log_le_self 2 hBzero
      exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)).trans hpow
    exact test_blockBadPrimes_simplified_bound hε hH hHA hAB (hraw _ hAj)
  have hsum : (∑ j ∈ test_dyadicIndices H B,
      ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ)) ≤ (H : ℝ) * D := by
    calc
      (∑ j ∈ test_dyadicIndices H B,
          ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ)) ≤
          ∑ _j ∈ test_dyadicIndices H B, D := Finset.sum_le_sum hterm
      _ = ((test_dyadicIndices H B).card : ℝ) * D := by simp
      _ ≤ (H : ℝ) * D := by
        have hcardNat : (test_dyadicIndices H B).card ≤ H := by
          calc
            (test_dyadicIndices H B).card ≤ (Finset.range (Nat.log 2 B + 1)).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
            _ = Nat.log 2 B + 1 := Finset.card_range _
            _ ≤ H := hlog
        have hcardReal : ((test_dyadicIndices H B).card : ℝ) ≤ H := by
          exact_mod_cast hcardNat
        have hD : 0 ≤ D := by
          dsimp [D]
          positivity
        exact mul_le_mul_of_nonneg_right hcardReal hD
  calc
    (∑ N ∈ Finset.Icc (H + 1) B,
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card) ≤
        ((B + 1 : ℕ) : ℝ) *
          ∑ j ∈ test_dyadicIndices H B,
            ((test_blockBadPrimes ε (2 ^ j) x).card : ℝ) := hlarge
    _ ≤ ((B + 1 : ℕ) : ℝ) * ((H : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp [D]
      ring

noncomputable def test_lowerPowerCutoff (x : ℕ) : ℕ :=
  Nat.floor (Real.rpow (x : ℝ) (1 / 100 : ℝ))

noncomputable def test_upperPowerCutoff (x : ℕ) : ℕ :=
  Nat.floor (Real.rpow (x : ℝ) (3 / 5 : ℝ))

lemma test_lowerPowerCutoff_cast_le (x : ℕ) :
    (test_lowerPowerCutoff x : ℝ) ≤ Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

lemma test_upperPowerCutoff_cast_le (x : ℕ) :
    (test_upperPowerCutoff x : ℝ) ≤ Real.rpow (x : ℝ) (3 / 5 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

lemma test_eventually_half_rpow_le_lowerPowerCutoff :
    ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) ≤
        (test_lowerPowerCutoff x : ℝ) := by
  have hpow := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hlarge := hpow.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlarge] with x hx
  let y := Real.rpow (x : ℝ) (1 / 100 : ℝ)
  change (2 : ℝ) ≤ y at hx
  have hfloor : y - 1 < (Nat.floor y : ℕ) := Nat.sub_one_lt_floor y
  have hhalf : (1 / 2 : ℝ) * y ≤ y - 1 := by linarith
  exact hhalf.trans hfloor.le

lemma test_eventually_binaryLogCube_le_lowerPowerCutoff :
    ∀ᶠ x : ℕ in atTop,
      Erdos387.binaryLogScale x ^ 3 ≤ test_lowerPowerCutoff x := by
  have hsmall := (Erdos746.tendsto_log_pow_div_rpow_nat 3
    (show (0 : ℝ) < 1 / 100 by norm_num)).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / 54 by norm_num))
  filter_upwards [hsmall, test_eventually_half_rpow_le_lowerPowerCutoff,
    eventually_ge_atTop 4] with x hx hfloor hx4
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hxpow : 0 < Real.rpow (x : ℝ) (1 / 100 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlogCube : (Real.log (x : ℝ)) ^ 3 ≤
      (1 / 54 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
    exact ((div_lt_iff₀ hxpow).mp hx).le
  have hL := Erdos387.binaryLogScale_cast_le_three_mul_log hx4
  have hLpow : (Erdos387.binaryLogScale x : ℝ) ^ 3 ≤
      (3 * Real.log (x : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hL 3
  have hcast : ((Erdos387.binaryLogScale x ^ 3 : ℕ) : ℝ) ≤
      (test_lowerPowerCutoff x : ℝ) := by
    calc
      ((Erdos387.binaryLogScale x ^ 3 : ℕ) : ℝ) =
          (Erdos387.binaryLogScale x : ℝ) ^ 3 := by push_cast; rfl
      _ ≤ (3 * Real.log (x : ℝ)) ^ 3 := hLpow
      _ = 27 * (Real.log (x : ℝ)) ^ 3 := by ring
      _ ≤ (1 / 2 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
        nlinarith
      _ ≤ (test_lowerPowerCutoff x : ℝ) := hfloor
  exact_mod_cast hcast

lemma test_eventually_log_upperCutoff_le_lowerPowerCutoff :
    ∀ᶠ x : ℕ in atTop,
      Nat.log 2 (test_upperPowerCutoff x) + 1 ≤ test_lowerPowerCutoff x := by
  have hlogpow := (Erdos746.tendsto_log_pow_div_rpow_nat 1
    (show (0 : ℝ) < 1 / 100 by norm_num)).eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  have hpowLarge := ((tendsto_rpow_atTop
    (show (0 : ℝ) < 1 / 100 by norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (8 : ℝ))
  filter_upwards [hlogpow, test_eventually_half_rpow_le_lowerPowerCutoff,
    hpowLarge, eventually_ge_atTop 4] with x hx hfloor hxpow4 hx4
  have hxpow : 0 < Real.rpow (x : ℝ) (1 / 100 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hratio := (div_lt_iff₀ hxpow).mp hx
  have hBlog : Nat.log 2 (test_upperPowerCutoff x) ≤ Nat.log 2 x := by
    apply Nat.log_mono_right
    have hupperReal := test_upperPowerCutoff_cast_le x
    have hrpowSelf : Real.rpow (x : ℝ) (3 / 5 : ℝ) ≤ (x : ℝ) := by
      apply Real.rpow_le_self_of_one_le
      · exact_mod_cast (by omega : 1 ≤ x)
      · norm_num
    exact_mod_cast hupperReal.trans hrpowSelf
  have hNatLog : (Nat.log 2 x : ℝ) ≤ 3 * Real.log (x : ℝ) := by
    have hL := Erdos387.binaryLogScale_cast_le_three_mul_log hx4
    unfold Erdos387.binaryLogScale at hL
    push_cast at hL
    linarith
  have hcast : ((Nat.log 2 (test_upperPowerCutoff x) + 1 : ℕ) : ℝ) ≤
      (test_lowerPowerCutoff x : ℝ) := by
    calc
      ((Nat.log 2 (test_upperPowerCutoff x) + 1 : ℕ) : ℝ) ≤
          (Nat.log 2 x : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hBlog 1
      _ ≤ 3 * Real.log (x : ℝ) + 1 := by gcongr
      _ ≤ (1 / 2 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
        change (8 : ℝ) ≤ Real.rpow (x : ℝ) (1 / 100 : ℝ) at hxpow4
        have hratio' : Real.log (x : ℝ) <
            (1 / 16 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
          simpa only [pow_one] using hratio
        have hthree : 3 * Real.log (x : ℝ) <
            (3 / 16 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
          linarith
        have hone : (1 : ℝ) ≤
            (5 / 16 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
          nlinarith [hxpow4]
        linarith
      _ ≤ (test_lowerPowerCutoff x : ℝ) := hfloor
  exact_mod_cast hcast

lemma test_eventually_lowerPowerCutoff_le_upperPowerCutoff :
    ∀ᶠ x : ℕ in atTop,
      test_lowerPowerCutoff x ≤ test_upperPowerCutoff x := by
  filter_upwards [eventually_ge_atTop 2,
    test_eventually_half_rpow_le_lowerPowerCutoff] with x hx hlow
  have hxbase : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hexp : (1 / 100 : ℝ) ≤ 3 / 5 := by norm_num
  have hpow : Real.rpow (x : ℝ) (1 / 100 : ℝ) ≤
      Real.rpow (x : ℝ) (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxbase hexp
  have hfloorMono : Nat.floor (Real.rpow (x : ℝ) (1 / 100 : ℝ)) ≤
      Nat.floor (Real.rpow (x : ℝ) (3 / 5 : ℝ)) := Nat.floor_mono hpow
  exact hfloorMono

noncomputable def test_regularOddPrimes (P₀ x : ℕ) : Finset ℕ :=
  (oddPrimesBelow x).filter fun p => P₀ ≤ p

noncomputable def test_exceptionalOddPrimes (P₀ x : ℕ) : Finset ℕ :=
  (oddPrimesBelow x).filter fun p => p < P₀

lemma test_oddPrimesBelow_eq_exceptional_union_regular (P₀ x : ℕ) :
    oddPrimesBelow x = test_exceptionalOddPrimes P₀ x ∪
      test_regularOddPrimes P₀ x := by
  classical
  ext p
  by_cases hp : p < P₀
  · simp [test_exceptionalOddPrimes, test_regularOddPrimes, hp]
  · have hp' : P₀ ≤ p := Nat.le_of_not_gt hp
    simp [test_exceptionalOddPrimes, test_regularOddPrimes, hp, hp']

lemma test_exceptional_regular_disjoint (P₀ x : ℕ) :
    Disjoint (test_exceptionalOddPrimes P₀ x) (test_regularOddPrimes P₀ x) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpE hpR
  have he := (Finset.mem_filter.mp hpE).2
  have hr := (Finset.mem_filter.mp hpR).2
  omega

lemma test_regular_threshold_le_upperCutoff {ε : ℝ} (hε : 0 < ε)
    {P₀ x p : ℕ}
    (hPV : ∀ q ≥ P₀, q.Prime → Odd q →
      (eventualThreshold ε q : ℝ) ≤ (q : ℝ) ^ (3 / 5 : ℝ))
    (hp : p ∈ test_regularOddPrimes P₀ x) :
    eventualThreshold ε p ≤ test_upperPowerCutoff x := by
  have hpData := Finset.mem_filter.mp hp
  have hpOdd := Finset.mem_filter.mp hpData.1
  have hpRpow := hPV p hpData.2 hpOdd.2.1 hpOdd.2.2
  have hpx : p ≤ x := by
    have := Finset.mem_range.mp hpOdd.1
    omega
  have hmono : (p : ℝ) ^ (3 / 5 : ℝ) ≤ (x : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpx) (by norm_num)
  apply Nat.le_floor
  simpa [test_upperPowerCutoff] using hpRpow.trans hmono

lemma test_sum_Icc_three_ranges (f : ℕ → ℝ) {a L H B : ℕ}
    (haL : a ≤ L + 1) (hLH : L ≤ H) (hHB : H ≤ B) :
    (∑ N ∈ Finset.Icc a B, f N) =
      (∑ N ∈ Finset.Icc a L, f N) +
      (∑ N ∈ Finset.Icc (L + 1) H, f N) +
      (∑ N ∈ Finset.Icc (H + 1) B, f N) := by
  have hset (u v : ℕ) : Finset.Icc u v = Finset.Ico u (v + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  simp_rw [hset]
  rw [Finset.sum_Ico_eq_sub f (by omega : a ≤ B + 1),
    Finset.sum_Ico_eq_sub f haL,
    Finset.sum_Ico_eq_sub f (by omega : L + 1 ≤ H + 1),
    Finset.sum_Ico_eq_sub f (by omega : H + 1 ≤ B + 1)]
  ring

noncomputable def test_thresholdTail (ε : ℝ) (M x : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesBelow x,
    ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)

lemma test_thresholdPrimeSum_eq_truncated_add_tail (ε : ℝ) (M x : ℕ) :
    thresholdPrimeSum ε x = test_truncatedOddPrimeSum ε M x +
      test_thresholdTail ε M x := by
  unfold thresholdPrimeSum test_truncatedOddPrimeSum test_thresholdTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

lemma test_thresholdTail_nonneg {ε : ℝ} (hε : 0 < ε) (M x : ℕ) :
    0 ≤ test_thresholdTail ε M x := by
  unfold test_thresholdTail
  apply Finset.sum_nonneg
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  exact test_threshold_sub_truncated_nonneg hε hpData.2.1 hpData.2.2

noncomputable def test_exceptionalTailConstant (ε : ℝ) (P₀ : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesBelow P₀, (eventualThreshold ε p : ℝ)

lemma test_exceptionalTail_bound {ε : ℝ} (hε : 0 < ε) (P₀ M x : ℕ) :
    (∑ p ∈ test_exceptionalOddPrimes P₀ x,
      ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) ≤
      test_exceptionalTailConstant ε P₀ := by
  have hpoint : ∀ p ∈ test_exceptionalOddPrimes P₀ x,
      (eventualThreshold ε p : ℝ) - truncatedThreshold ε p M ≤
        (eventualThreshold ε p : ℝ) := by
    intro p hp
    have hT : (0 : ℝ) ≤ truncatedThreshold ε p M := by positivity
    linarith
  calc
    (∑ p ∈ test_exceptionalOddPrimes P₀ x,
      ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) ≤
        ∑ p ∈ test_exceptionalOddPrimes P₀ x,
          (eventualThreshold ε p : ℝ) := Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ oddPrimesBelow P₀, (eventualThreshold ε p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpData := Finset.mem_filter.mp hp
        have hpOdd := Finset.mem_filter.mp hpData.1
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hpData.2, hpOdd.2⟩
      · intro p hpP hpnot
        positivity
    _ = test_exceptionalTailConstant ε P₀ := rfl

lemma test_regularTail_le_fiberSum {ε : ℝ} (hε : 0 < ε)
    {P₀ M x : ℕ}
    (hPV : ∀ q ≥ P₀, q.Prime → Odd q →
      (eventualThreshold ε q : ℝ) ≤ (q : ℝ) ^ (3 / 5 : ℝ)) :
    (∑ p ∈ test_regularOddPrimes P₀ x,
      ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) ≤
      ∑ N ∈ Finset.Icc (M + 1) (test_upperPowerCutoff x),
        ((N + 1 : ℕ) : ℝ) *
          (test_thresholdFiber ε (oddPrimesBelow x) N).card := by
  have hprime : ∀ p ∈ test_regularOddPrimes P₀ x, p.Prime ∧ Odd p := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hupper : ∀ p ∈ test_regularOddPrimes P₀ x,
      eventualThreshold ε p ≤ test_upperPowerCutoff x + 1 := by
    intro p hp
    have hle := test_regular_threshold_le_upperCutoff hε hPV hp
    exact hle.trans (by omega)
  have htail := test_threshold_tail_sum_le_fibers hε
    (M := M) (B := test_upperPowerCutoff x)
    (test_regularOddPrimes P₀ x) hprime hupper
  exact htail.trans (Finset.sum_le_sum fun N hN => by
    gcongr
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hpData.1).1, hpData.2⟩)

lemma test_thresholdTail_eq_exceptional_add_regular
    (ε : ℝ) (P₀ M x : ℕ) :
    test_thresholdTail ε M x =
      (∑ p ∈ test_exceptionalOddPrimes P₀ x,
        ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) +
      (∑ p ∈ test_regularOddPrimes P₀ x,
        ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) := by
  unfold test_thresholdTail
  rw [test_oddPrimesBelow_eq_exceptional_union_regular,
    Finset.sum_union (test_exceptional_regular_disjoint P₀ x)]

lemma test_eventually_fixed_le_binaryLogCube (M : ℕ) :
    ∀ᶠ x : ℕ in atTop, M ≤ Erdos387.binaryLogScale x ^ 3 := by
  filter_upwards [eventually_ge_atTop (2 ^ M)] with x hx
  have hlog : M ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) hx
  have hscale : M ≤ Erdos387.binaryLogScale x := by
    unfold Erdos387.binaryLogScale
    omega
  have hscaleOne : 1 ≤ Erdos387.binaryLogScale x := by
    unfold Erdos387.binaryLogScale
    omega
  exact hscale.trans (Nat.le_pow (by omega : 0 < 3))

lemma test_thresholdTail_eq_zero_of_one_lt {ε : ℝ} (hε : 1 < ε)
    (M x : ℕ) : test_thresholdTail ε M x = 0 := by
  classical
  unfold test_thresholdTail
  apply Finset.sum_eq_zero
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hF : eventualThreshold ε p = 1 :=
    eventualThreshold_eq_one_of_one_lt hε p
  have hTle : truncatedThreshold ε p M ≤ 1 := by
    rw [← hF]
    exact truncatedThreshold_le_eventualThreshold
      (exists_eventualThreshold (zero_lt_one.trans hε) hpData.2.1 hpData.2.2)
  have hT : truncatedThreshold ε p M = 1 :=
    Nat.le_antisymm hTle (one_le_truncatedThreshold ε p M)
  simp [hF, hT]

lemma test_eventually_log_le_binaryLogScale :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ≤ (Erdos387.binaryLogScale x : ℝ) := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx0 : x ≠ 0 := by omega
  have hlt : x < 2 ^ Erdos387.binaryLogScale x := by
    unfold Erdos387.binaryLogScale
    have h := (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hx0).mp
      (Nat.lt_succ_self (Nat.log 2 x))
    exact h
  have hlog : Real.log (x : ℝ) ≤
      Real.log ((2 ^ Erdos387.binaryLogScale x : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hlt.le
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hlogTwo : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  calc
    Real.log (x : ℝ) ≤
        (Erdos387.binaryLogScale x : ℝ) * Real.log 2 := hlog
    _ ≤ (Erdos387.binaryLogScale x : ℝ) * 1 := by
      gcongr
    _ = _ := by ring

lemma test_tendsto_allOdd_first_normalized_zero :
    Tendsto (fun x : ℕ =>
      ((x : ℝ) * (2 / (Erdos387.binaryLogScale x ^ 3 : ℕ))) /
        test_pntScale x) atTop (nhds 0) := by
  have hmajor : Tendsto (fun x : ℕ => 2 / (Real.log (x : ℝ)) ^ 2)
      atTop (nhds 0) := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinv := hlog.inv_tendsto_atTop
    simpa [div_eq_mul_inv, inv_pow] using (hinv.pow 2).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards [eventually_ge_atTop 2] with x hx
    unfold test_pntScale
    positivity
  · filter_upwards [eventually_ge_atTop 2,
      test_eventually_log_le_binaryLogScale] with x hx hlogL
    unfold test_pntScale
    have hxpos : (0 : ℝ) < x := by positivity
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx)
    have hLpos : (0 : ℝ) < Erdos387.binaryLogScale x := by
      exact_mod_cast Erdos387.binaryLogScale_pos x
    have hL3 : 0 < (Erdos387.binaryLogScale x : ℝ) ^ 3 := pow_pos hLpos _
    have hlog3 : 0 < (Real.log (x : ℝ)) ^ 3 := pow_pos hlogpos _
    have hpow3 := pow_le_pow_left₀ hlogpos.le hlogL 3
    rw [Nat.cast_pow]
    calc
      ((x : ℝ) * (2 / (Erdos387.binaryLogScale x : ℝ) ^ 3)) /
          ((x : ℝ) / Real.log (x : ℝ)) =
          (2 * Real.log (x : ℝ)) /
            (Erdos387.binaryLogScale x : ℝ) ^ 3 := by
        field_simp [hxpos.ne', hlogpos.ne', hL3.ne']
      _ ≤ (2 * Real.log (x : ℝ)) / (Real.log (x : ℝ)) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) hlog3 hpow3
      _ = 2 / (Real.log (x : ℝ)) ^ 2 := by
        field_simp [hlogpos.ne']

lemma test_tendsto_allOdd_power_normalized_zero :
    Tendsto (fun x : ℕ =>
      (((test_lowerPowerCutoff x + 1 : ℕ) : ℝ) ^ 22) / test_pntScale x)
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun x : ℕ => (2 : ℝ) ^ 22 *
      (Real.log (x : ℝ) ^ 1 / Real.rpow (x : ℝ) (39 / 50 : ℝ)))
      atTop (nhds 0) := by
    simpa using (Erdos746.tendsto_log_pow_div_rpow_nat 1
      (show (0 : ℝ) < 39 / 50 by norm_num)).const_mul ((2 : ℝ) ^ 22)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards [eventually_ge_atTop 2] with x hx
    unfold test_pntScale
    have hx1real : (1 : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ x)
    exact div_nonneg (by positivity)
      (div_nonneg (by positivity) (Real.log_nonneg hx1real))
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hxreal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    have hxpow1 : (1 : ℝ) ≤ Real.rpow (x : ℝ) (1 / 100 : ℝ) :=
      Real.one_le_rpow hxreal (by norm_num)
    have hH := test_lowerPowerCutoff_cast_le x
    have hH1 : ((test_lowerPowerCutoff x + 1 : ℕ) : ℝ) ≤
        2 * Real.rpow (x : ℝ) (1 / 100 : ℝ) := by
      push_cast
      linarith
    have hpow22 := pow_le_pow_left₀ (by positivity) hH1 22
    have hxpos : (0 : ℝ) < x := by positivity
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx)
    unfold test_pntScale
    have hrewrite :
        (2 * Real.rpow (x : ℝ) (1 / 100 : ℝ)) ^ 22 *
            Real.log (x : ℝ) / (x : ℝ) =
          (2 : ℝ) ^ 22 *
            (Real.log (x : ℝ) ^ 1 / Real.rpow (x : ℝ) (39 / 50 : ℝ)) := by
      have hpowcombine : (Real.rpow (x : ℝ) (1 / 100 : ℝ)) ^ (22 : ℕ) =
          Real.rpow (x : ℝ) (11 / 50 : ℝ) := by
        rw [← Real.rpow_natCast]
        calc
          Real.rpow (Real.rpow (x : ℝ) (1 / 100 : ℝ)) (22 : ℝ) =
              Real.rpow (x : ℝ) ((1 / 100 : ℝ) * 22) :=
            (Real.rpow_mul hxpos.le (1 / 100 : ℝ) (22 : ℝ)).symm
          _ = Real.rpow (x : ℝ) (11 / 50 : ℝ) := by norm_num
      rw [mul_pow]
      rw [hpowcombine]
      field_simp [hxpos.ne', (Real.rpow_pos_of_pos hxpos (39 / 50 : ℝ)).ne']
      calc
        Real.rpow (x : ℝ) (11 / 50 : ℝ) *
              Real.rpow (x : ℝ) (39 / 50 : ℝ) =
            Real.rpow (x : ℝ) ((11 / 50 : ℝ) + 39 / 50) :=
          (Real.rpow_add hxpos (11 / 50 : ℝ) (39 / 50 : ℝ)).symm
        _ = (x : ℝ) := by norm_num
    calc
      (((test_lowerPowerCutoff x + 1 : ℕ) : ℝ) ^ 22) /
          ((x : ℝ) / Real.log (x : ℝ)) =
          (((test_lowerPowerCutoff x + 1 : ℕ) : ℝ) ^ 22) *
            Real.log (x : ℝ) / (x : ℝ) := by field_simp
      _ ≤ (2 * Real.rpow (x : ℝ) (1 / 100 : ℝ)) ^ 22 *
            Real.log (x : ℝ) / (x : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow22 hlogpos.le) hxpos.le
      _ = _ := hrewrite

lemma test_eventually_primeCounting_tenth_bounds :
    ∀ᶠ x : ℕ in atTop,
      (9 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (Nat.primeCounting x : ℝ) ∧
      (Nat.primeCounting x : ℝ) ≤
          (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  constructor <;> linarith [le_abs_self
    ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ)),
    neg_abs_le
      ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))]

lemma test_eventually_primeCountTotal_two_mul_le :
    ∀ᶠ x : ℕ in atTop,
      (BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) ≤
        3 * test_pntScale x := by
  have htwoTop : Tendsto (fun x : ℕ ↦ 2 * x) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards with x
    simpa only [id_eq] using (show x ≤ 2 * x by omega)
  have hpntTwo := htwoTop.eventually test_eventually_primeCounting_tenth_bounds
  filter_upwards [hpntTwo, eventually_ge_atTop 2] with x hpnt hx
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hlogle : Real.log (x : ℝ) ≤ Real.log ((2 * x : ℕ) : ℝ) := by
    apply Real.log_le_log hxpos
    exact_mod_cast (show x ≤ 2 * x by omega)
  have hfrac : (((2 * x : ℕ) : ℝ) / Real.log ((2 * x : ℕ) : ℝ)) ≤
      2 * (x : ℝ) / Real.log (x : ℝ) := by
    calc
      (((2 * x : ℕ) : ℝ) / Real.log ((2 * x : ℕ) : ℝ)) ≤
          ((2 * x : ℕ) : ℝ) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hlogpos hlogle
      _ = 2 * (x : ℝ) / Real.log (x : ℝ) := by norm_num
  unfold BoundedGaps.Maynard.primeCountTotal test_pntScale
  calc
    (Nat.primeCounting (2 * x) : ℝ) ≤
        (11 / 10 : ℝ) *
          (((2 * x : ℕ) : ℝ) / Real.log ((2 * x : ℕ) : ℝ)) := hpnt.2
    _ ≤ (11 / 10 : ℝ) * (2 * (x : ℝ) / Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hfrac (by norm_num)
    _ = (11 / 5 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by ring
    _ ≤ 3 * ((x : ℝ) / Real.log (x : ℝ)) := by
      have : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
      nlinarith

lemma test_tendsto_primeMoment_error_normalized_zero (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun x : ℕ =>
      ((4 * C * ((2 * x : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
          (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ) ^ 22)) /
        test_pntScale x) atTop (nhds 0) := by
  let D : ℝ := 8 * C * (28 : ℝ) ^ 22
  have hmajor : Tendsto (fun x : ℕ => D / (Real.log (x : ℝ)) ^ 33)
      atTop (nhds 0) := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hinv := hlog.inv_tendsto_atTop
    simpa [D, div_eq_mul_inv, inv_pow] using
      (hinv.pow 33).const_mul D
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards [eventually_ge_atTop 9] with x hx
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hscale : 0 < test_pntScale x := by
      unfold test_pntScale
      exact div_pos (by positivity) hlogpos
    exact div_nonneg
      (mul_nonneg
        (div_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
        (by positivity)) hscale.le
  · filter_upwards [eventually_ge_atTop 9] with x hx
    have hxpos : (0 : ℝ) < x := by positivity
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hlogone : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      have hlog3 : 1 < Real.log (3 : ℝ) := by
        apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        exact Real.exp_one_lt_three
      have hlog9 : 2 < Real.log (9 : ℝ) := by
        rw [show (9 : ℝ) = 3 * 3 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        linarith
      exact (one_lt_two.trans (hlog9.trans_le
        (Real.log_le_log (by norm_num)
          (show (9 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx)))).le
    have hlogle : Real.log (x : ℝ) ≤ Real.log ((2 * x : ℕ) : ℝ) := by
      apply Real.log_le_log hxpos
      exact_mod_cast (show x ≤ 2 * x by omega)
    have hL := Erdos387.binaryLogScale_cast_le_three_mul_log
      (show 4 ≤ x by omega)
    have hLpow : (Erdos387.binaryLogScale x : ℝ) ^ 3 ≤
        (3 * Real.log (x : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hL 3
    have hsum : (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ)) ≤
        28 * (Real.log (x : ℝ)) ^ 3 := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
      calc
        (Erdos387.binaryLogScale x : ℝ) ^ 3 + 1 ≤
            (3 * Real.log (x : ℝ)) ^ 3 + 1 := by linarith
        _ = 27 * (Real.log (x : ℝ)) ^ 3 + 1 := by ring
        _ ≤ 28 * (Real.log (x : ℝ)) ^ 3 := by
          have hone : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ 3 :=
            one_le_pow₀ hlogone
          linarith
    have hpoly : (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ) ^ 22) ≤
        (28 * (Real.log (x : ℝ)) ^ 3) ^ 22 :=
      pow_le_pow_left₀ (by positivity) hsum 22
    have hden : (Real.log (x : ℝ)) ^ 100 ≤
        (Real.log ((2 * x : ℕ) : ℝ)) ^ 100 :=
      pow_le_pow_left₀ hlogpos.le hlogle 100
    have hlogTwopos : 0 < Real.log ((2 * x : ℕ) : ℝ) :=
      hlogpos.trans_le hlogle
    unfold test_pntScale
    have hrpow : Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) (100 : ℝ) =
        Real.log ((2 * x : ℕ) : ℝ) ^ (100 : ℕ) :=
      Real.rpow_natCast _ _
    rw [hrpow]
    calc
      ((4 * C * ((2 * x : ℕ) : ℝ) /
              Real.log ((2 * x : ℕ) : ℝ) ^ 100) *
            (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ) ^ 22)) /
          ((x : ℝ) / Real.log (x : ℝ)) =
          8 * C * Real.log (x : ℝ) *
              (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ) ^ 22) /
            Real.log ((2 * x : ℕ) : ℝ) ^ 100 := by
        field_simp [hxpos.ne', hlogpos.ne', hlogTwopos.ne']
        norm_num [Nat.cast_mul]
        ring
      _ ≤ 8 * C * Real.log (x : ℝ) *
              (28 * Real.log (x : ℝ) ^ 3) ^ 22 /
            Real.log ((2 * x : ℕ) : ℝ) ^ 100 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity)
      _ ≤ 8 * C * Real.log (x : ℝ) *
              (28 * Real.log (x : ℝ) ^ 3) ^ 22 /
            Real.log (x : ℝ) ^ 100 := by
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos hlogpos 100) hden
      _ = D / Real.log (x : ℝ) ^ 33 := by
        dsimp [D]
        field_simp [hlogpos.ne']

lemma test_tendsto_large_envelope_normalized_zero
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    Tendsto (fun x : ℕ =>
      (((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
          (test_lowerPowerCutoff x : ℝ) *
          (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
            Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) *
              (1 + (x : ℝ) ^ 2 /
                (test_lowerPowerCutoff x : ℝ) ^ 300))) /
        test_pntScale x) atTop (nhds 0) := by
  let D : ℝ := ((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600
  let A : ℝ := 4 * D * (1 + (2 : ℝ) ^ 300)
  have hmajor : Tendsto (fun x : ℕ => A *
      (Real.log (x : ℝ) ^ 1 / Real.rpow (x : ℝ) (9 / 100 : ℝ)))
      atTop (nhds 0) := by
    simpa using (Erdos746.tendsto_log_pow_div_rpow_nat 1
      (show (0 : ℝ) < 9 / 100 by norm_num)).const_mul A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards [eventually_ge_atTop 9] with x hx
    have hscale : 0 < test_pntScale x := by
      unfold test_pntScale
      exact div_pos (by positivity)
        (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    exact div_nonneg (by
      dsimp [D]
      positivity) hscale.le
  · filter_upwards [eventually_ge_atTop 9,
      test_eventually_half_rpow_le_lowerPowerCutoff] with x hx hHlower
    have hxpos : (0 : ℝ) < x := by positivity
    have hxone : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hxpow01pos : 0 < Real.rpow (x : ℝ) (1 / 100 : ℝ) :=
      Real.rpow_pos_of_pos hxpos _
    have hxpow60one : (1 : ℝ) ≤ Real.rpow (x : ℝ) (3 / 5 : ℝ) :=
      Real.one_le_rpow hxone (by norm_num)
    have hB := test_upperPowerCutoff_cast_le x
    have hB1 : ((test_upperPowerCutoff x + 1 : ℕ) : ℝ) ≤
        2 * Real.rpow (x : ℝ) (3 / 5 : ℝ) := by
      push_cast
      linarith
    have hH := test_lowerPowerCutoff_cast_le x
    have hrpow300 : (Real.rpow (x : ℝ) (1 / 100 : ℝ)) ^ (300 : ℕ) =
        (x : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast]
      calc
        Real.rpow (Real.rpow (x : ℝ) (1 / 100 : ℝ)) (300 : ℝ) =
            Real.rpow (x : ℝ) ((1 / 100 : ℝ) * 300) :=
          (Real.rpow_mul hxpos.le (1 / 100 : ℝ) (300 : ℝ)).symm
        _ = Real.rpow (x : ℝ) (3 : ℕ) := by norm_num
        _ = (x : ℝ) ^ 3 := Real.rpow_natCast _ _
    have hdenLower :
        ((1 / 2 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ)) ^ 300 ≤
          (test_lowerPowerCutoff x : ℝ) ^ 300 :=
      pow_le_pow_left₀ (by positivity) hHlower 300
    have hfactor : 1 + (x : ℝ) ^ 2 /
          (test_lowerPowerCutoff x : ℝ) ^ 300 ≤
        1 + (2 : ℝ) ^ 300 := by
      have hsmall : (x : ℝ) ^ 2 /
            (test_lowerPowerCutoff x : ℝ) ^ 300 ≤ (2 : ℝ) ^ 300 := by
        calc
          (x : ℝ) ^ 2 / (test_lowerPowerCutoff x : ℝ) ^ 300 ≤
              (x : ℝ) ^ 2 /
                ((1 / 2 : ℝ) * Real.rpow (x : ℝ) (1 / 100 : ℝ)) ^ 300 :=
            div_le_div_of_nonneg_left (by positivity)
              (pow_pos (mul_pos (by norm_num) hxpow01pos) 300) hdenLower
          _ = (2 : ℝ) ^ 300 / (x : ℝ) := by
            rw [mul_pow, hrpow300]
            field_simp [hxpos.ne']
          _ ≤ (2 : ℝ) ^ 300 := by
            apply (div_le_iff₀ hxpos).2
            simpa using mul_le_mul_of_nonneg_left hxone
              (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 300)
      linarith
    have hbase : (((3 * test_upperPowerCutoff x : ℕ) : ℝ)) ≤
        3 * Real.rpow (x : ℝ) (3 / 5 : ℝ) := by
      push_cast
      gcongr
    have hsqrt0 := Real.rpow_le_rpow (by positivity) hbase
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have hsqrt3 : Real.rpow (3 : ℝ) (1 / 2 : ℝ) ≤ 2 := by
      rw [show Real.rpow (3 : ℝ) (1 / 2 : ℝ) = Real.sqrt 3 from
        (Real.sqrt_eq_rpow 3).symm]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hnested :
        Real.rpow (Real.rpow (x : ℝ) (3 / 5 : ℝ)) (1 / 2 : ℝ) =
          Real.rpow (x : ℝ) (3 / 10 : ℝ) := by
      calc
        Real.rpow (Real.rpow (x : ℝ) (3 / 5 : ℝ)) (1 / 2 : ℝ) =
            Real.rpow (x : ℝ) ((3 / 5 : ℝ) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul hxpos.le (3 / 5 : ℝ) (1 / 2 : ℝ)).symm
        _ = _ := by norm_num
    have hsqrt :
        Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) ≤
          2 * Real.rpow (x : ℝ) (3 / 10 : ℝ) := by
      calc
        Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) ≤
            Real.rpow (3 * Real.rpow (x : ℝ) (3 / 5 : ℝ)) (1 / 2 : ℝ) :=
          hsqrt0
        _ = Real.rpow (3 : ℝ) (1 / 2 : ℝ) *
            Real.rpow (Real.rpow (x : ℝ) (3 / 5 : ℝ)) (1 / 2 : ℝ) := by
          exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
            (Real.rpow_nonneg (by positivity) _)
        _ = Real.rpow (3 : ℝ) (1 / 2 : ℝ) *
            Real.rpow (x : ℝ) (3 / 10 : ℝ) := by rw [hnested]
        _ ≤ 2 * Real.rpow (x : ℝ) (3 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right hsqrt3 (Real.rpow_nonneg (by positivity) _)
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    have hpowcombine :
        Real.rpow (x : ℝ) (3 / 5 : ℝ) *
            Real.rpow (x : ℝ) (1 / 100 : ℝ) *
              Real.rpow (x : ℝ) (3 / 10 : ℝ) =
          Real.rpow (x : ℝ) (91 / 100 : ℝ) := by
      calc
        Real.rpow (x : ℝ) (3 / 5 : ℝ) *
              Real.rpow (x : ℝ) (1 / 100 : ℝ) *
                Real.rpow (x : ℝ) (3 / 10 : ℝ) =
            Real.rpow (x : ℝ) ((3 / 5 : ℝ) + 1 / 100) *
              Real.rpow (x : ℝ) (3 / 10 : ℝ) := by
          exact congrArg (fun z => z * Real.rpow (x : ℝ) (3 / 10 : ℝ))
            (Real.rpow_add hxpos (3 / 5 : ℝ) (1 / 100 : ℝ)).symm
        _ = Real.rpow (x : ℝ)
              (((3 / 5 : ℝ) + 1 / 100) + 3 / 10) := by
          exact (Real.rpow_add hxpos ((3 / 5 : ℝ) + 1 / 100)
            (3 / 10 : ℝ)).symm
        _ = Real.rpow (x : ℝ) (91 / 100 : ℝ) := by norm_num
    have hraw :
        ((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
            (test_lowerPowerCutoff x : ℝ) * D *
              Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) *
                (1 + (x : ℝ) ^ 2 /
                  (test_lowerPowerCutoff x : ℝ) ^ 300) ≤
          A * Real.rpow (x : ℝ) (91 / 100 : ℝ) := by
      calc
        ((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
            (test_lowerPowerCutoff x : ℝ) * D *
              Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) *
                (1 + (x : ℝ) ^ 2 /
                  (test_lowerPowerCutoff x : ℝ) ^ 300) ≤
            (2 * Real.rpow (x : ℝ) (3 / 5 : ℝ)) *
              Real.rpow (x : ℝ) (1 / 100 : ℝ) * D *
                (2 * Real.rpow (x : ℝ) (3 / 10 : ℝ)) *
                  (1 + (2 : ℝ) ^ 300) := by
          have hBH : ((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
                (test_lowerPowerCutoff x : ℝ) ≤
              (2 * Real.rpow (x : ℝ) (3 / 5 : ℝ)) *
                Real.rpow (x : ℝ) (1 / 100 : ℝ) :=
            mul_le_mul hB1 hH (by positivity) (by positivity)
          have hBHD := mul_le_mul_of_nonneg_right hBH hD
          have hBHDS :
              (((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
                    (test_lowerPowerCutoff x : ℝ) * D) *
                  Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ)
                    (1 / 2 : ℝ) ≤
                (((2 * Real.rpow (x : ℝ) (3 / 5 : ℝ)) *
                    Real.rpow (x : ℝ) (1 / 100 : ℝ)) * D) *
                  (2 * Real.rpow (x : ℝ) (3 / 10 : ℝ)) :=
            mul_le_mul hBHD hsqrt (Real.rpow_nonneg (by positivity) _)
              (by positivity)
          have hfactorNonneg : 0 ≤ 1 + (x : ℝ) ^ 2 /
              (test_lowerPowerCutoff x : ℝ) ^ 300 :=
            add_nonneg zero_le_one (div_nonneg (sq_nonneg _)
              (pow_nonneg (by positivity) _))
          have hrightNonneg : 0 ≤
              (((2 * Real.rpow (x : ℝ) (3 / 5 : ℝ)) *
                  Real.rpow (x : ℝ) (1 / 100 : ℝ)) * D) *
                (2 * Real.rpow (x : ℝ) (3 / 10 : ℝ)) := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by norm_num)
                    (Real.rpow_nonneg (by positivity) _))
                  (Real.rpow_nonneg (by positivity) _)) hD)
              (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
          exact (mul_le_mul_of_nonneg_right hBHDS hfactorNonneg).trans
            (mul_le_mul_of_nonneg_left hfactor hrightNonneg)
        _ = A * Real.rpow (x : ℝ) (91 / 100 : ℝ) := by
          dsimp [A]
          calc
            (2 * Real.rpow (x : ℝ) (3 / 5 : ℝ)) *
                  Real.rpow (x : ℝ) (1 / 100 : ℝ) * D *
                    (2 * Real.rpow (x : ℝ) (3 / 10 : ℝ)) *
                      (1 + (2 : ℝ) ^ 300) =
                4 * D * (1 + (2 : ℝ) ^ 300) *
                  (Real.rpow (x : ℝ) (3 / 5 : ℝ) *
                    Real.rpow (x : ℝ) (1 / 100 : ℝ) *
                      Real.rpow (x : ℝ) (3 / 10 : ℝ)) := by ring
            _ = 4 * D * (1 + (2 : ℝ) ^ 300) *
                Real.rpow (x : ℝ) (91 / 100 : ℝ) := by rw [hpowcombine]
    have hscale : 0 < test_pntScale x := by
      unfold test_pntScale
      exact div_pos hxpos hlogpos
    have hquot := div_le_div_of_nonneg_right hraw hscale.le
    calc
      (((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
          (test_lowerPowerCutoff x : ℝ) *
          (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
            Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) *
              (1 + (x : ℝ) ^ 2 /
                (test_lowerPowerCutoff x : ℝ) ^ 300))) /
          test_pntScale x ≤
        (A * Real.rpow (x : ℝ) (91 / 100 : ℝ)) / test_pntScale x := by
          simpa [D, mul_assoc] using hquot
      _ = A * (Real.log (x : ℝ) ^ 1 /
          Real.rpow (x : ℝ) (9 / 100 : ℝ)) := by
        unfold test_pntScale
        have hpowOne : Real.rpow (x : ℝ) (91 / 100 : ℝ) *
              Real.rpow (x : ℝ) (9 / 100 : ℝ) = (x : ℝ) := by
          calc
            Real.rpow (x : ℝ) (91 / 100 : ℝ) *
                  Real.rpow (x : ℝ) (9 / 100 : ℝ) =
                Real.rpow (x : ℝ) ((91 / 100 : ℝ) + 9 / 100) :=
              (Real.rpow_add hxpos _ _).symm
            _ = (x : ℝ) := by norm_num
        field_simp [hlogpos.ne',
          (Real.rpow_pos_of_pos hxpos (9 / 100 : ℝ)).ne']
        calc
          A * Real.rpow (x : ℝ) (91 / 100 : ℝ) *
                Real.rpow (x : ℝ) (9 / 100 : ℝ) =
              A * (Real.rpow (x : ℝ) (91 / 100 : ℝ) *
                Real.rpow (x : ℝ) (9 / 100 : ℝ)) := by ring
          _ = A * (x : ℝ) := by rw [hpowOne]

theorem test_uniformlyNegligibleThresholdTail {ε : ℝ} (hε : 0 < ε) :
    Erdos980.UniformlyNegligibleTail (test_thresholdTail ε) test_pntScale := by
  intro δ hδ
  by_cases hε1 : ε ≤ 1
  · obtain ⟨C, hC, Np, Xp, hprime⟩ :=
      test_exists_uniform_oddPrimeBad_bound hε
    obtain ⟨Na, hall⟩ := exists_oddBadModuli_card_bound_simplified hε
    obtain ⟨P₀, hPV⟩ := Filter.eventually_atTop.1
      (test_eventually_eventualThreshold_le_threeFifths_rpow hε)
    obtain ⟨K, hKgt⟩ := exists_nat_gt (4 / ε)
    have hK : 0 < K := by
      have hpos : (0 : ℝ) < (K : ℝ) :=
        (div_pos (by norm_num) hε).trans hKgt
      exact_mod_cast hpos
    have hKε : (4 : ℝ) < ε * K := by
      have h := (div_lt_iff₀ hε).mp hKgt
      nlinarith
    obtain ⟨A₀, hraw⟩ :=
      test_exists_blockBadPrimes_largeSieve_bound hε hε1 hK hKε
    obtain ⟨Mδ, hMδ⟩ := exists_nat_gt (36 * (ε ^ 20)⁻¹ / δ)
    refine ⟨max 1 (max Np (max Na Mδ)), ?_⟩
    intro M hM
    have hM1 : 1 ≤ M := (le_max_left 1 _).trans hM
    have hMNp : Np ≤ M :=
      (le_max_left Np (max Na Mδ)).trans
        ((le_max_right 1 (max Np (max Na Mδ))).trans hM)
    have hMNa : Na ≤ M :=
      (le_max_left Na Mδ).trans
        ((le_max_right Np (max Na Mδ)).trans
          ((le_max_right 1 (max Np (max Na Mδ))).trans hM))
    have hMMδ : Mδ ≤ M :=
      (le_max_right Na Mδ).trans
        ((le_max_right Np (max Na Mδ)).trans
          ((le_max_right 1 (max Np (max Na Mδ))).trans hM))
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hinvpos : 0 < (ε ^ 20)⁻¹ := inv_pos.mpr (pow_pos hε 20)
    have hmainSmall : (ε ^ 20)⁻¹ * (6 / (M : ℝ)) < δ / 6 := by
      have hlargeReal : 36 * (ε ^ 20)⁻¹ / δ < (M : ℝ) :=
        hMδ.trans_le (by exact_mod_cast hMMδ)
      have hcross : 36 * (ε ^ 20)⁻¹ < (M : ℝ) * δ :=
        (div_lt_iff₀ hδ).mp hlargeReal
      rw [show (ε ^ 20)⁻¹ * (6 / (M : ℝ)) =
        (6 * (ε ^ 20)⁻¹) / (M : ℝ) by ring]
      apply (div_lt_iff₀ hMpos).2
      nlinarith
    let E : ℕ → ℝ := fun x =>
      test_exceptionalTailConstant ε P₀ / test_pntScale x
    let PE : ℕ → ℝ := fun x => (ε ^ 20)⁻¹ *
      (((4 * C * ((2 * x : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
          (((Erdos387.binaryLogScale x ^ 3 + 1 : ℕ) : ℝ) ^ 22)) /
        test_pntScale x)
    let AF : ℕ → ℝ := fun x => (ε ^ 20)⁻¹ *
      (((x : ℝ) * (2 / (Erdos387.binaryLogScale x ^ 3 : ℕ))) /
        test_pntScale x)
    let AP : ℕ → ℝ := fun x => (4 * (ε ^ 20)⁻¹) *
      ((((test_lowerPowerCutoff x + 1 : ℕ) : ℝ) ^ 22) /
        test_pntScale x)
    let LG : ℕ → ℝ := fun x =>
      (((test_upperPowerCutoff x + 1 : ℕ) : ℝ) *
          (test_lowerPowerCutoff x : ℝ) *
          (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
            Real.rpow ((3 * test_upperPowerCutoff x : ℕ) : ℝ) (1 / 2 : ℝ) *
              (1 + (x : ℝ) ^ 2 /
                (test_lowerPowerCutoff x : ℝ) ^ 300))) /
        test_pntScale x
    have hEt : Tendsto E atTop (nhds 0) := by
      simpa [E] using test_const_div_pntScale_tendsto_zero
        (test_exceptionalTailConstant ε P₀)
    have hPEt : Tendsto PE atTop (nhds 0) := by
      simpa [PE] using
        (test_tendsto_primeMoment_error_normalized_zero C hC).const_mul
          ((ε ^ 20)⁻¹)
    have hAFt : Tendsto AF atTop (nhds 0) := by
      simpa [AF] using test_tendsto_allOdd_first_normalized_zero.const_mul
        ((ε ^ 20)⁻¹)
    have hAPt : Tendsto AP atTop (nhds 0) := by
      simpa [AP] using test_tendsto_allOdd_power_normalized_zero.const_mul
        (4 * (ε ^ 20)⁻¹)
    have hLGt : Tendsto LG atTop (nhds 0) := by
      simpa [LG] using test_tendsto_large_envelope_normalized_zero hε K
    have hδsix : 0 < δ / 6 := by positivity
    have hEsmall := hEt.eventually (Iio_mem_nhds hδsix)
    have hPEsmall := hPEt.eventually (Iio_mem_nhds hδsix)
    have hAFsmall := hAFt.eventually (Iio_mem_nhds hδsix)
    have hAPsmall := hAPt.eventually (Iio_mem_nhds hδsix)
    have hLGsmall := hLGt.eventually (Iio_mem_nhds hδsix)
    filter_upwards [eventually_ge_atTop Xp,
      test_eventually_fixed_le_binaryLogCube M,
      test_eventually_binaryLogCube_le_lowerPowerCutoff,
      test_eventually_lowerPowerCutoff_le_upperPowerCutoff,
      test_eventually_log_upperCutoff_le_lowerPowerCutoff,
      test_eventually_fixed_le_binaryLogCube (2 * A₀),
      test_eventually_primeCountTotal_two_mul_le,
      test_eventually_pntScale_pos,
      hEsmall, hPEsmall, hAFsmall, hAPsmall, hLGsmall]
      with x hxXp hML hLH hHB hlog hA₀L hpnt hscale
        hEs hPEs hAFs hAPs hLGs
    let L := Erdos387.binaryLogScale x ^ 3
    let H := test_lowerPowerCutoff x
    let B := test_upperPowerCutoff x
    have hL1 : 1 ≤ L := by
      have hLpos : 0 < L := by
        dsimp [L]
        exact pow_pos (Erdos387.binaryLogScale_pos x) 3
      omega
    have hHA₀ : 2 * A₀ ≤ H := hA₀L.trans hLH
    have hH1 : 1 ≤ H := hL1.trans hLH
    have hprimeRange := test_primeMoment_range_bound hε hC hM1 hMNp hxXp
      hprime
    have hallRange := test_allOddMoment_range_bound (N₀ := Na) (L := L)
      (H := H) (x := x) hε hL1 (hMNa.trans hML) hall
    have hlargeRange := test_largeFiberSum_bound (K := K) (A₀ := A₀)
      (H := H) (B := B) (x := x) hε hH1 hHA₀ hlog
        (fun A hA => hraw A hA x)
    have hregular := test_regularTail_le_fiberSum (P₀ := P₀) (M := M)
      (x := x) hε hPV
    have hsplit := test_sum_Icc_three_ranges
      (fun N => ((N + 1 : ℕ) : ℝ) *
        (test_thresholdFiber ε (oddPrimesBelow x) N).card)
      (show M + 1 ≤ L + 1 by omega) hLH hHB
    have hregularBound :
        (∑ p ∈ test_regularOddPrimes P₀ x,
          ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) ≤
          (ε ^ 20)⁻¹ *
            ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ)) +
              (4 * C * ((2 * x : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
                (((L + 1 : ℕ) : ℝ) ^ 22)) +
          (ε ^ 20)⁻¹ *
            ((x : ℝ) * (2 / (L : ℝ)) +
              4 * (((H + 1 : ℕ) : ℝ) ^ 22)) +
          ((B + 1 : ℕ) : ℝ) * (H : ℝ) *
            (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
              Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
                (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300)) := by
      calc
        (∑ p ∈ test_regularOddPrimes P₀ x,
          ((eventualThreshold ε p : ℝ) - truncatedThreshold ε p M)) ≤
            ∑ N ∈ Finset.Icc (M + 1) B,
              ((N + 1 : ℕ) : ℝ) *
                (test_thresholdFiber ε (oddPrimesBelow x) N).card := hregular
        _ = (∑ N ∈ Finset.Icc (M + 1) L,
              ((N + 1 : ℕ) : ℝ) *
                (test_thresholdFiber ε (oddPrimesBelow x) N).card) +
            (∑ N ∈ Finset.Icc (L + 1) H,
              ((N + 1 : ℕ) : ℝ) *
                (test_thresholdFiber ε (oddPrimesBelow x) N).card) +
            (∑ N ∈ Finset.Icc (H + 1) B,
              ((N + 1 : ℕ) : ℝ) *
                (test_thresholdFiber ε (oddPrimesBelow x) N).card) := hsplit
        _ ≤ _ := add_le_add (add_le_add hprimeRange hallRange) hlargeRange
    have hexc := test_exceptionalTail_bound hε P₀ M x
    have htailBound : test_thresholdTail ε M x ≤
        test_exceptionalTailConstant ε P₀ +
          ((ε ^ 20)⁻¹ *
            ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ)) +
              (4 * C * ((2 * x : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
                (((L + 1 : ℕ) : ℝ) ^ 22)) +
          (ε ^ 20)⁻¹ *
            ((x : ℝ) * (2 / (L : ℝ)) +
              4 * (((H + 1 : ℕ) : ℝ) ^ 22)) +
          ((B + 1 : ℕ) : ℝ) * (H : ℝ) *
            (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 * (6 : ℝ) ^ 600 *
              Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
                (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300))) := by
      rw [test_thresholdTail_eq_exceptional_add_regular ε P₀ M x]
      exact add_le_add hexc hregularBound
    have htailDiv := div_le_div_of_nonneg_right htailBound hscale.le
    have hpntMain :
        (ε ^ 20)⁻¹ *
              ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ))) / test_pntScale x ≤
            (ε ^ 20)⁻¹ * (6 / (M : ℝ)) := by
      have hnum := mul_le_mul_of_nonneg_right hpnt
        (by positivity : (0 : ℝ) ≤ 2 / (M : ℝ))
      have hdiv := div_le_div_of_nonneg_right hnum hscale.le
      have hmul := mul_le_mul_of_nonneg_left hdiv hinvpos.le
      calc
        (ε ^ 20)⁻¹ *
              ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ))) / test_pntScale x =
            (ε ^ 20)⁻¹ *
              (((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ))) / test_pntScale x) := by ring
        _ ≤ (ε ^ 20)⁻¹ *
              ((3 * test_pntScale x * (2 / (M : ℝ))) /
                test_pntScale x) := hmul
        _ = (ε ^ 20)⁻¹ * (6 / (M : ℝ)) := by
          field_simp [hscale.ne']
          ring
    rw [abs_of_nonneg (div_nonneg (test_thresholdTail_nonneg hε M x) hscale.le)]
    have hnormalized : test_thresholdTail ε M x / test_pntScale x ≤
        E x +
          ((ε ^ 20)⁻¹ *
              ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ))) / test_pntScale x) +
          PE x + AF x + AP x + LG x := by
      calc
        test_thresholdTail ε M x / test_pntScale x ≤
            (test_exceptionalTailConstant ε P₀ +
              ((ε ^ 20)⁻¹ *
                ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                    (2 / (M : ℝ)) +
                  (4 * C * ((2 * x : ℕ) : ℝ) /
                      Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) *
                    (((L + 1 : ℕ) : ℝ) ^ 22)) +
              (ε ^ 20)⁻¹ *
                ((x : ℝ) * (2 / (L : ℝ)) +
                  4 * (((H + 1 : ℕ) : ℝ) ^ 22)) +
              ((B + 1 : ℕ) : ℝ) * (H : ℝ) *
                (((2 * K + 2 : ℕ) : ℝ) * (ε / 3)⁻¹ ^ 600 *
                  (6 : ℝ) ^ 600 *
                  Real.rpow ((3 * B : ℕ) : ℝ) (1 / 2 : ℝ) *
                    (1 + (x : ℝ) ^ 2 / (H : ℝ) ^ 300)))) /
              test_pntScale x := htailDiv
        _ = E x +
          ((ε ^ 20)⁻¹ *
              ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                (2 / (M : ℝ))) / test_pntScale x) +
          PE x + AF x + AP x + LG x := by
            dsimp [E, PE, AF, AP, LG, L, H, B]
            ring
    calc
      test_thresholdTail ε M x / test_pntScale x ≤
          E x +
            ((ε ^ 20)⁻¹ *
                ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) *
                  (2 / (M : ℝ))) / test_pntScale x) +
            PE x + AF x + AP x + LG x := hnormalized
      _ ≤ E x + (ε ^ 20)⁻¹ * (6 / (M : ℝ)) +
            PE x + AF x + AP x + LG x := by gcongr
      _ < δ := by linarith
  · have hεgt : 1 < ε := lt_of_not_ge hε1
    refine ⟨0, ?_⟩
    intro M _hM
    filter_upwards with x
    simpa [test_thresholdTail_eq_zero_of_one_lt hεgt M x] using hδ

lemma test_truncatedThreshold_mono {ε : ℝ} {p M M' : ℕ} (hMM' : M ≤ M') :
    truncatedThreshold ε p M ≤ truncatedThreshold ε p M' := by
  apply truncatedThreshold_minimal
  have hspec := truncatedThreshold_spec ε p M'
  exact ⟨hspec.1, fun N hm hNM => hspec.2 N hm (hNM.trans hMM')⟩

lemma test_truncatedOddPrimeSum_mono (ε : ℝ) {M M' : ℕ} (hMM' : M ≤ M')
    (x : ℕ) :
    test_truncatedOddPrimeSum ε M x ≤ test_truncatedOddPrimeSum ε M' x := by
  unfold test_truncatedOddPrimeSum
  exact Finset.sum_le_sum fun p _hp => by
    exact_mod_cast test_truncatedThreshold_mono (ε := ε) (p := p) hMM'

lemma test_truncatedOddPrimeSum_nonneg (ε : ℝ) (M x : ℕ) :
    0 ≤ test_truncatedOddPrimeSum ε M x := by
  unfold test_truncatedOddPrimeSum
  positivity

lemma test_thresholdPrimeSum_nonneg (ε : ℝ) (x : ℕ) :
    0 ≤ thresholdPrimeSum ε x := by
  unfold thresholdPrimeSum
  positivity

noncomputable def test_incrementPiece (ε : ℝ) : ℕ → ℕ → ℝ
  | 0, x => test_truncatedOddPrimeSum ε 0 x
  | j + 1, x => test_truncatedOddPrimeSum ε (j + 1) x -
      test_truncatedOddPrimeSum ε j x

noncomputable def test_incrementWeight (ε : ℝ) : ℕ → ℝ
  | 0 => test_residueTruncatedConstant ε 0
  | j + 1 => test_residueTruncatedConstant ε (j + 1) -
      test_residueTruncatedConstant ε j

noncomputable def test_assemblyTail (ε : ℝ) : ℕ → ℕ → ℝ
  | 0, x => thresholdPrimeSum ε x
  | M + 1, x => test_thresholdTail ε M x

lemma test_sum_incrementPiece (ε : ℝ) (M x : ℕ) :
    (∑ j ∈ Finset.range (M + 1), test_incrementPiece ε j x) =
      test_truncatedOddPrimeSum ε M x := by
  induction M with
  | zero => simp [test_incrementPiece]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [test_incrementPiece]
      ring

lemma test_incrementPiece_nonneg (ε : ℝ) (j x : ℕ) :
    0 ≤ test_incrementPiece ε j x := by
  cases j with
  | zero => exact test_truncatedOddPrimeSum_nonneg ε 0 x
  | succ j =>
      simp only [test_incrementPiece]
      exact sub_nonneg.mpr (test_truncatedOddPrimeSum_mono ε (Nat.le_succ j) x)

lemma test_incrementPiece_normalized_tendsto (ε : ℝ) (j : ℕ) :
    Tendsto (fun x => test_incrementPiece ε j x / test_pntScale x)
      atTop (nhds (test_incrementWeight ε j)) := by
  cases j with
  | zero =>
      simpa [test_incrementPiece, test_incrementWeight] using
        test_truncatedOddPrimeSum_normalized_tendsto ε 0
  | succ j =>
      have hnext := test_truncatedOddPrimeSum_normalized_tendsto ε (j + 1)
      have hprev := test_truncatedOddPrimeSum_normalized_tendsto ε j
      simpa [test_incrementPiece, test_incrementWeight, sub_div] using
        hnext.sub hprev

lemma test_thresholdPrimeSum_increment_decomposition (ε : ℝ) (M x : ℕ) :
    thresholdPrimeSum ε x =
      (∑ j ∈ Finset.range M, test_incrementPiece ε j x) +
        test_assemblyTail ε M x := by
  cases M with
  | zero => simp [test_assemblyTail]
  | succ M =>
      rw [test_sum_incrementPiece]
      exact test_thresholdPrimeSum_eq_truncated_add_tail ε M x

lemma test_assemblyTail_nonneg {ε : ℝ} (hε : 0 < ε) (M x : ℕ) :
    0 ≤ test_assemblyTail ε M x := by
  cases M with
  | zero => exact test_thresholdPrimeSum_nonneg ε x
  | succ M => exact test_thresholdTail_nonneg hε M x

lemma test_uniformlyNegligibleAssemblyTail {ε : ℝ} (hε : 0 < ε) :
    Erdos980.UniformlyNegligibleTail (test_assemblyTail ε) test_pntScale := by
  intro δ hδ
  obtain ⟨M₀, hM₀⟩ := test_uniformlyNegligibleThresholdTail hε δ hδ
  refine ⟨M₀ + 1, ?_⟩
  intro M hM
  cases M with
  | zero => omega
  | succ M =>
      have hM' : M₀ ≤ M := by omega
      simpa [test_assemblyTail] using hM₀ M hM'

lemma test_truncatedThreshold_zero (ε : ℝ) (p : ℕ) :
    truncatedThreshold ε p 0 = 1 := by
  apply Nat.le_antisymm
  · simpa using truncatedThreshold_le_succ ε p 0
  · exact one_le_truncatedThreshold ε p 0

lemma test_residueTruncatedConstant_zero (ε : ℝ) :
    test_residueTruncatedConstant ε 0 = 1 := by
  classical
  unfold test_residueTruncatedConstant test_reducedPatternResidues
    test_patternModulus
  simp only [Nat.factorial_zero, mul_one, test_truncatedThreshold_zero]
  have hcard : ((Finset.range 4).filter fun a => a.Coprime 4).card = 2 := by
    decide
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot]
  simp [hcard]

theorem test_erdos_981 {ε : ℝ} (hε : 0 < ε) :
    ∃ cε : ℝ, 0 < cε ∧
      thresholdPrimeSum ε ~[atTop]
        (fun x : ℕ => cε * ((x : ℝ) / Real.log (x : ℝ))) := by
  have hscale := test_eventually_pntScale_pos
  have hpieceNonneg : ∀ j x, 0 ≤ test_incrementPiece ε j x :=
    test_incrementPiece_nonneg ε
  have htailNonneg : ∀ M x, 0 ≤ test_assemblyTail ε M x :=
    test_assemblyTail_nonneg hε
  have hpiece : ∀ j,
      Tendsto (fun x => test_incrementPiece ε j x / test_pntScale x)
        atTop (nhds (test_incrementWeight ε j)) :=
    test_incrementPiece_normalized_tendsto ε
  have hdecomp : ∀ M x,
      thresholdPrimeSum ε x =
        (∑ j ∈ Finset.range M, test_incrementPiece ε j x) +
          test_assemblyTail ε M x :=
    test_thresholdPrimeSum_increment_decomposition ε
  have htail := test_uniformlyNegligibleAssemblyTail hε
  have hweight : Summable (test_incrementWeight ε) :=
    Erdos980.summable_weight_of_fixed_patterns_and_uniformTail_of_nonneg
      (thresholdPrimeSum ε) test_pntScale (test_incrementPiece ε)
      (test_assemblyTail ε) (test_incrementWeight ε) hscale
      hpieceNonneg htailNonneg hpiece hdecomp htail
  have hweightNonneg : ∀ j, 0 ≤ test_incrementWeight ε j :=
    Erdos980.fixedPattern_weight_nonneg test_pntScale
      (test_incrementPiece ε) (test_incrementWeight ε) hscale
      hpieceNonneg hpiece
  have hcOne : (1 : ℝ) ≤ ∑' j, test_incrementWeight ε j := by
    calc
      (1 : ℝ) = test_incrementWeight ε 0 := by
        simp [test_incrementWeight, test_residueTruncatedConstant_zero]
      _ = ∑ j ∈ ({0} : Finset ℕ), test_incrementWeight ε j := by simp
      _ ≤ ∑' j, test_incrementWeight ε j :=
        hweight.sum_le_tsum ({0} : Finset ℕ) (fun j _hj => hweightNonneg j)
  let cε := ∑' j, test_incrementWeight ε j
  have hc : 0 < cε := zero_lt_one.trans_le hcOne
  refine ⟨cε, hc, ?_⟩
  have hequiv :=
    Erdos980.isEquivalent_of_fixed_patterns_and_uniformTail_of_nonneg
      (thresholdPrimeSum ε) test_pntScale (test_incrementPiece ε)
      (test_assemblyTail ε) (test_incrementWeight ε) hscale
      hpieceNonneg htailNonneg hpiece hdecomp htail hc
  simpa [cε, test_pntScale] using hequiv

end Erdos981

import ErdosProblems.Erdos489.SieveParameterBundle
import ErdosProblems.Erdos489.AffineGapWitnesses
import ErdosProblems.Erdos489.MaxGapBound
import ErdosProblems.Erdos489.CountLinear
import ErdosProblems.Erdos489.ActualGapTailBound
import ErdosProblems.Erdos489.EventualKernelTail
import ErdosProblems.Erdos489.EndpointCountTail
import ErdosProblems.Erdos489.SieveGaps

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators

namespace Erdos489

/-- The normalized square mass of sufficiently long actual sifted gaps is
uniformly small on all sufficiently large prefixes. -/
theorem uniform_long_gap_square_tail
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (hB : Set.Infinite {n | divisorSifted p n})
    (hs : Summable fun n => ((Nat.nth p n : ℝ)⁻¹))
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ Nat.nth p n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, ∀ᶠ x : ℕ in atTop,
      (((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ)) < ε := by
  intro ε hε
  have ha2 : ∀ n, 2 ≤ Nat.nth p n := by
    intro n
    exact hp2 _ (Nat.nth_mem_of_infinite hp n)
  obtain ⟨ρ, Y, Q, C, R, hρpos, hρ1, hY, hQ, hC, hsmall,
      hdensity, hCY, hRdensity, hRtail⟩ :=
    exists_sieve_parameter_bundle (Nat.nth p) ha2 hs
  let H0 := max
    (5 * (Q * (coprimePart ((List.range R).map (Nat.nth p)) Q).prod))
    (256 * C ^ 2)
  let b := divisorSiftedEnumeration p
  let gap := divisorSiftedGap p
  let rank := divisorWitnessRank p
  have hb : StrictMono b := Nat.nth_strictMono hB
  have hgapEq : ∀ i, b (i + 1) = b i + gap i := by
    intro i
    dsimp [b, gap, divisorSiftedGap, divisorSiftedEnumeration]
    exact (Nat.add_sub_of_le (hb.monotone (by omega))).symm
  have hwitness : ∀ i, H0 ≤ gap i →
      ∃ T : Finset ℕ, Set.InjOn rank (T : Set ℕ) ∧
        gap i / C ≤ T.card ∧
        (∀ n ∈ T, b i < n ∧ n < b (i + 1)) ∧
        (∀ n ∈ T, Nat.nth p (rank n) ∣ n) := by
    intro i hi
    have hperiod : 5 * (Q *
        (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ gap i :=
      (le_max_left _ _).trans hi
    have hlarge : 256 * C ^ 2 ≤ gap i :=
      (le_max_right _ _).trans hi
    have hcovered : ∀ n, b i < n → n < b i + gap i →
        ∃ a, p a ∧ a ∣ n := by
      intro n hnL hnR
      apply divisorSifted_consecutive_gap_covered p hB i n hnL
      change n < b (i + 1)
      rw [hgapEq i]
      exact hnR
    obtain ⟨T, hint, hcong, hinj, hcard, hhigh, htailrank, hdiv, hpay⟩ :=
      exists_affine_gap_full_witness p hp hp2 R Q (b i) (gap i) C Y ρ
        hQ hY hC hρpos.le hRdensity hdensity hperiod hcovered hRtail
        hsmall hlarge hCY
    have hint' : ∀ n ∈ T, b i < n ∧ n < b (i + 1) := by
      intro n hn
      have hni := hint n hn
      rw [hgapEq i]
      exact hni
    exact ⟨T, hinj, hcard, hint', hdiv⟩
  have hcountLinEv := eventually_mul_count_le_of_isLittleO_sqrt
    p hcount (8 * C) (Nat.mul_pos (by omega) hC)
  obtain ⟨Ncount, hNcount⟩ := Filter.eventually_atTop.mp hcountLinEv
  let X0 := max (max H0 Ncount) (2 * C)
  have hmaxEventually : ∀ᶠ x : ℕ in atTop,
      ∀ i, b i < x → gap i ≤ x := by
    filter_upwards [eventually_ge_atTop X0] with x hx
    have hx' : max (max H0 Ncount) (2 * C) ≤ x := by
      simpa [X0] using hx
    exact eventual_gap_le_prefix p hp b gap rank C H0 Ncount hC
      hgapEq hNcount hwitness x hx'
  let K0 : ℝ := (16 * C ^ 2 : ℕ)
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  let δk := ε / (4 * K0 * (8 * (C : ℝ)))
  let δe := ε / (4 * K0 * 2)
  have hδk : 0 < δk := by dsimp [δk]; positivity
  have hδe : 0 < δe := by dsimp [δe]; positivity
  have haPos : ∀ n, 0 < Nat.nth p n := by
    intro n
    exact lt_of_lt_of_le (by omega : 0 < 2) (ha2 n)
  obtain ⟨Nk, hNk⟩ :=
    rankPairKernel_uniform_finset_tail_of_eventually
      (Nat.nth p) haPos hev δk hδk
  let H := max H0 (C * Nk)
  have hHperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ H :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hHlarge : 256 * C ^ 2 ≤ H :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hNkHC : Nk ≤ H / C := by
    apply (Nat.le_div_iff_mul_le hC).2
    change Nk * C ≤ max H0 (C * Nk)
    rw [Nat.mul_comm]
    exact le_max_right H0 (C * Nk)
  have hendTend := tendsto_count_two_mul_add_one_sq_div p hcount
  have hendEv : ∀ᶠ x : ℕ in atTop,
      (Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ) < δe :=
    (tendsto_order.1 hendTend).2 δe hδe
  refine ⟨H, ?_⟩
  filter_upwards [hmaxEventually, hendEv, eventually_ge_atTop 1] with x hmaxx hendx hx
  have hxpos : 0 < x := by omega
  obtain ⟨J, hbound, hJhigh⟩ := actual_long_gap_sum_bound
    p hp hp2 hB ρ Y Q C R H x hQ hY hC hxpos hρpos.le
    hRdensity hdensity hRtail hsmall hCY hHperiod hHlarge
    (by simpa [b, gap] using hmaxx)
  have hkern : (∑ z ∈ J, rankPairKernel (Nat.nth p) z) < δk := by
    apply hNk J
    intro z hz
    have hzH := hJhigh z hz
    exact ⟨hNkHC.trans hzH.1, hNkHC.trans hzH.2⟩
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hdivbound := div_le_div_of_nonneg_right hbound hxR.le
  have hnormalized :
      ((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) / (x : ℝ) ≤
        K0 * (8 * (C : ℝ) *
            (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
          2 * ((Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ))) := by
    dsimp [K0]
    calc
      _ ≤ (((16 * C ^ 2 : ℕ) : ℝ) *
          (8 * (x : ℝ) * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
            2 * (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ))) / (x : ℝ) :=
        hdivbound
      _ = ((16 * C ^ 2 : ℕ) : ℝ) *
          (8 * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
            2 * ((Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ))) := by
        norm_num only [Nat.cast_pow]
        field_simp
  have hkMul := mul_lt_mul_of_pos_left hkern
    (mul_pos hK0 (by positivity : (0 : ℝ) < 8 * C))
  have heMul := mul_lt_mul_of_pos_left hendx
    (mul_pos hK0 (by norm_num : (0 : ℝ) < 2))
  have hidk : (K0 * (8 * (C : ℝ))) * δk = ε / 4 := by
    dsimp [δk]
    field_simp
  have hide : (K0 * 2) * δe = ε / 4 := by
    dsimp [δe]
    field_simp
  rw [hidk] at hkMul
  rw [hide] at heMul
  have hkern0 : 0 ≤ ∑ z ∈ J, rankPairKernel (Nat.nth p) z := by
    apply Finset.sum_nonneg
    intro z hz
    dsimp [rankPairKernel]
    positivity
  have hend0 : 0 ≤ (Nat.count p (2 * x + 1) : ℝ) ^ 2 / (x : ℝ) := by positivity
  ring_nf at hnormalized hkMul heMul ⊢
  linarith

end Erdos489

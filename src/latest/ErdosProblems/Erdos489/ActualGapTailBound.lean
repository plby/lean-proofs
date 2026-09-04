import ErdosProblems.Erdos489.AffineGapWitnesses
import ErdosProblems.Erdos489.GlobalGapCharging
import ErdosProblems.Erdos489.PairSetCard
import ErdosProblems.Erdos489.SieveGaps

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos489

noncomputable instance divisorSiftedDecidable (p : ℕ → Prop) :
    DecidablePred (divisorSifted p) := Classical.decPred _

noncomputable def divisorSiftedEnumeration (p : ℕ → Prop) : ℕ → ℕ :=
  Nat.nth (divisorSifted p)

noncomputable def divisorSiftedGap (p : ℕ → Prop) (i : ℕ) : ℕ :=
  divisorSiftedEnumeration p (i + 1) - divisorSiftedEnumeration p i

/-- Finite-prefix square-gap tails are bounded by a high-rank kernel tail plus
the square of the forbidden counting function. -/
theorem actual_long_gap_sum_bound
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (hB : Set.Infinite {n | divisorSifted p n})
    (ρ : ℝ) (Y Q C R H x : ℕ)
    (hQ : 1 < Q) (hY : 0 < Y) (hC : 0 < C) (hx : 0 < x)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ))
    (hsmall : ∀ q, Nat.Prime q → q ≤ Y → q ∣ Q)
    (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y)
    (hHperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ H)
    (hHlarge : 256 * C ^ 2 ≤ H)
    (hmax : ∀ i, divisorSiftedEnumeration p i < x →
      divisorSiftedGap p i ≤ x) :
    ∃ J : Finset (ℕ × ℕ),
      ((∑ i ∈ (Finset.range (Nat.count (divisorSifted p) x)).filter
          (fun i => H ≤ divisorSiftedGap p i),
          (divisorSiftedGap p i) ^ 2 : ℕ) : ℝ) ≤
        ((16 * C ^ 2 : ℕ) : ℝ) *
          (8 * (x : ℝ) * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
            2 * (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ)) ∧
      (∀ z ∈ J, H / C ≤ z.1 ∧ H / C ≤ z.2) := by
  classical
  let : DecidablePred (divisorSifted p) := Classical.decPred _
  let b := divisorSiftedEnumeration p
  let gap := divisorSiftedGap p
  let I := (Finset.range (Nat.count (divisorSifted p) x)).filter
    (fun i => H ≤ gap i)
  let rank := divisorWitnessRank p
  have hb : StrictMono b := Nat.nth_strictMono hB
  have hgapEq : ∀ i, b (i + 1) = b i + gap i := by
    intro i
    dsimp [b, gap, divisorSiftedGap, divisorSiftedEnumeration]
    exact (Nat.add_sub_of_le (hb.monotone (by omega))).symm
  have hiStart : ∀ i ∈ I, b i < x := by
    intro i hi
    have hirange := (Finset.mem_filter.mp hi).1
    exact Nat.nth_lt_of_lt_count (Finset.mem_range.mp hirange)
  have hiLong : ∀ i ∈ I, H ≤ gap i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hex : ∀ i ∈ I, ∃ T : Finset ℕ,
      (∀ n ∈ T, b i < n ∧ n < b (i + 1)) ∧
      (∀ n ∈ T, Nat.ModEq Q n 1) ∧
      Set.InjOn rank (T : Set ℕ) ∧
      gap i / C ≤ T.card ∧
      (∀ n ∈ T, gap i / C ≤ rank n) ∧
      (∀ n ∈ T, R ≤ rank n) ∧
      (∀ n ∈ T, Nat.nth p (rank n) ∣ n) ∧
      gap i ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs T).card := by
    intro i hi
    have hcovered : ∀ n, b i < n → n < b i + gap i →
        ∃ a, p a ∧ a ∣ n := by
      intro n hnL hnR
      apply divisorSifted_consecutive_gap_covered p hB i n hnL
      change n < b (i + 1)
      rw [hgapEq i]
      exact hnR
    have hperiod : 5 * (Q *
        (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ gap i :=
      hHperiod.trans (hiLong i hi)
    have hlarge : 256 * C ^ 2 ≤ gap i := hHlarge.trans (hiLong i hi)
    have hfull := exists_affine_gap_full_witness p hp hp2
      R Q (b i) (gap i) C Y ρ hQ hY hC hρ0 hρ hdensity
      hperiod hcovered htail hsmall hlarge hCY
    simpa [rank, hgapEq i] using hfull
  let T : ℕ → Finset ℕ := fun i =>
    if hi : i ∈ I then Classical.choose (hex i hi) else ∅
  have hTspec : ∀ i ∈ I,
      (∀ n ∈ T i, b i < n ∧ n < b (i + 1)) ∧
      (∀ n ∈ T i, Nat.ModEq Q n 1) ∧
      Set.InjOn rank (T i : Set ℕ) ∧
      gap i / C ≤ (T i).card ∧
      (∀ n ∈ T i, gap i / C ≤ rank n) ∧
      (∀ n ∈ T i, R ≤ rank n) ∧
      (∀ n ∈ T i, Nat.nth p (rank n) ∣ n) ∧
      gap i ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs (T i)).card := by
    intro i hi
    dsimp [T]
    rw [dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have ha : ∀ r, 0 < Nat.nth p r := by
    intro r
    exact lt_of_lt_of_le (by omega : 0 < 2)
      (hp2 _ (Nat.nth_mem_of_infinite hp r))
  have hcoord : ∀ i ∈ I, ∀ n ∈ T i, n ≤ 2 * x := by
    intro i hi n hn
    have hnint := (hTspec i hi).1 n hn
    have hstart := hiStart i hi
    have hgmax : gap i ≤ x := by
      apply hmax i
      simpa [b] using hstart
    rw [hgapEq i] at hnint
    omega
  have hN : ∀ i ∈ I, H / C ≤ gap i / C := by
    intro i hi
    exact Nat.div_le_div_right (hiLong i hi)
  obtain ⟨J, hbound, hJhigh, hJmod⟩ :=
    global_gap_charge_le_rankKernel I b gap T rank (Nat.nth p)
      C (2 * x) (H / C) hC (Nat.mul_pos (by omega) hx) hb
      (fun i hi => hgapEq i)
      (fun i hi => (hTspec i hi).1)
      (fun i hi => (hTspec i hi).2.2.1)
      ha
      (fun i hi => (hTspec i hi).2.2.2.2.2.2.1)
      hcoord
      (fun i hi => (hTspec i hi).2.2.2.2.1)
      hN
      (fun i hi => (hTspec i hi).2.2.2.2.2.2.2)
  have hJcard := rank_pair_finset_card_le_count_sq p hp J (2 * x) hJmod
  refine ⟨J, ?_, hJhigh⟩
  have hinside :
      4 * ((2 * x : ℕ) : ℝ) * (C : ℝ) *
          (∑ z ∈ J, rankPairKernel (Nat.nth p) z) + 2 * (J.card : ℝ) ≤
      8 * (x : ℝ) * (C : ℝ) *
          (∑ z ∈ J, rankPairKernel (Nat.nth p) z) +
        2 * (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ) := by
    have hk0 : 0 ≤ ∑ z ∈ J, rankPairKernel (Nat.nth p) z := by
      apply Finset.sum_nonneg
      intro z hz
      dsimp [rankPairKernel]
      positivity
    have hcardR : (J.card : ℝ) ≤
        (((Nat.count p (2 * x + 1)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hJcard
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hK0 : (0 : ℝ) ≤ (16 * C ^ 2 : ℕ) := by positivity
  exact hbound.trans (mul_le_mul_of_nonneg_left hinside hK0)

end Erdos489

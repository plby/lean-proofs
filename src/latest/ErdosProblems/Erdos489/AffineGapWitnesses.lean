import ErdosProblems.Erdos489.QuantitativeCandidateSupply
import ErdosProblems.Erdos489.BoundaryInterior
import ErdosProblems.Erdos489.DivisorWitness
import ErdosProblems.Erdos489.HighRankRepresentatives
import ErdosProblems.Erdos489.QuantitativeCoprimePairs

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos489

/-- A long covered interval contains many distinctly and highly ranked divisor
witnesses in the fixed affine progression. -/
theorem exists_affine_gap_high_rank_witnesses
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R Q L G C : ℕ) (ρ : ℝ)
    (hQ : 1 < Q) (hC : 0 < C) (hGC : 2 * C ≤ G)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (hperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ G)
    (hcovered : ∀ n, L < n → n < L + G → ∃ a, p a ∧ a ∣ n)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ)) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, L < n ∧ n < L + G) ∧
      (∀ n ∈ T, Nat.ModEq Q n 1) ∧
      Set.InjOn (divisorWitnessRank p) (T : Set ℕ) ∧
      G / C ≤ T.card ∧
      (∀ n ∈ T, G / C ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, R ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, Nat.nth p (divisorWitnessRank p n) ∣ n) := by
  let l := (List.range R).map (Nat.nth p)
  let closed := (Finset.Icc L (L + G)).filter
    (affineCandidates (coprimePart l Q) Q)
  let S := closed.filter fun n => L < n ∧ n < L + G
  let label := divisorWitnessRank p
  let a := Nat.nth p
  have hl : ∀ m ∈ l, 2 ≤ m := by
    intro m hm
    rcases List.mem_map.mp hm with ⟨r, hr, rfl⟩
    exact hp2 _ (Nat.nth_mem_of_infinite hp r)
  have hclosed := affineCandidates_coprimePart_linear_supply
    l Q L G hQ hl ρ hρ0 (by simpa [l] using hρ)
    (by simpa [l] using hperiod)
  have hclosedInterval : ∀ n ∈ closed, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  have hparammul := mul_le_mul_of_nonneg_right hdensity
    (show (0 : ℝ) ≤ G by positivity)
  have hfour : 4 * (G : ℝ) / (C : ℝ) ≤
      ρ * (G : ℝ) / (2 * (Q : ℝ)) := by
    calc
      4 * (G : ℝ) / (C : ℝ) =
          ((4 : ℝ) / (C : ℝ)) * (G : ℝ) := by ring
      _ ≤ (ρ / (2 * (Q : ℝ))) * (G : ℝ) := hparammul
      _ = ρ * (G : ℝ) / (2 * (Q : ℝ)) := by ring
  have hclosedDense : 4 * (G : ℝ) / (C : ℝ) ≤ (closed.card : ℝ) :=
    hfour.trans (by simpa [closed] using hclosed)
  have hSDense : 4 * (G : ℝ) / (C : ℝ) - 2 ≤ (S.card : ℝ) := by
    exact (interval_interior_card_cast_lower closed L (L + G)
      hclosedInterval _ hclosedDense)
  have hSsub : S ⊆ closed := Finset.filter_subset _ _
  have hSinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    exact hclosedInterval n (hSsub hn)
  have hSint : ∀ n ∈ S, L < n ∧ n < L + G := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hScov : ∀ n ∈ S, ∃ m, p m ∧ m ∣ n := by
    intro n hn
    exact hcovered n (hSint n hn).1 (hSint n hn).2
  have hSdiv : ∀ n ∈ S, a (label n) ∣ n := by
    intro n hn
    exact nth_divisorWitnessRank_dvd p n (hScov n hn)
  have hSavoid : ∀ n ∈ S, ∀ m ∈ l, ¬m ∣ n := by
    intro n hn
    have hnclosed := hSsub hn
    have hnaff := (Finset.mem_filter.mp hnclosed).2
    exact affineCandidates_coprimePart_avoid_all l Q n hnaff
  have hSrankR : ∀ n ∈ S, R ≤ label n := by
    intro n hn
    exact le_divisorWitnessRank_of_avoid_prefix p n R (hScov n hn)
      (hSavoid n hn)
  have ha : ∀ r, 0 < a r := by
    intro r
    dsimp [a]
    exact lt_of_lt_of_le (by omega : 0 < 2)
      (hp2 _ (Nat.nth_mem_of_infinite hp r))
  have hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤
      1 / (C : ℝ) := by
    apply htail (S.image label)
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    exact hSrankR n hn
  obtain ⟨T, hTS, hinj, hcard, hhigh⟩ :=
    exists_high_rank_divisor_representatives_sub_two
      S L G C a label hC hGC ha hSinterval hSdiv hSDense hmass
  refine ⟨T, ?_, ?_, hinj, hcard, hhigh, ?_, ?_⟩
  · intro n hn
    exact hSint n (hTS hn)
  · intro n hn
    have hnclosed := hSsub (hTS hn)
    exact (Finset.mem_filter.mp hnclosed).2.1
  · intro n hn
    exact hSrankR n (hTS hn)
  · intro n hn
    exact hSdiv n (hTS hn)

/-- Adding the rough-prime numerical hypotheses turns the witnesses above into
a full quadratic coprime-pair payment for the gap. -/
theorem exists_affine_gap_coprime_pair_payment
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R Q L G C Y : ℕ) (ρ : ℝ)
    (hQ : 1 < Q) (hY : 0 < Y) (hC : 0 < C)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (hperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ G)
    (hcovered : ∀ n, L < n → n < L + G → ∃ a, p a ∧ a ∣ n)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ))
    (hsmall : ∀ q, Nat.Prime q → q ≤ Y → q ∣ Q)
    (hG : 256 * C ^ 2 ≤ G) (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, L < n ∧ n < L + G) ∧
      Set.InjOn (divisorWitnessRank p) (T : Set ℕ) ∧
      (∀ n ∈ T, G / C ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, R ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, Nat.nth p (divisorWitnessRank p n) ∣ n) ∧
      G ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs T).card := by
  have hGC : 2 * C ≤ G := by
    have : 2 * C ≤ 256 * C ^ 2 := by nlinarith
    exact this.trans hG
  obtain ⟨T, hint, hcong, hinj, hcard, hhigh, hR, hdiv⟩ :=
    exists_affine_gap_high_rank_witnesses p hp hp2 R Q L G C ρ
      hQ hC hGC hρ0 hρ hdensity hperiod hcovered htail
  have hinterval : ∀ n ∈ T, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    have := hint n hn
    omega
  have hpay := progression_many_coprime_pairs T L G Q Y C
    (by omega) hY hC hinterval hcong hsmall hcard hG hCY
  exact ⟨T, hint, hinj, hhigh, hR, hdiv, hpay⟩

/-- Strengthened packaging retaining the linear cardinality bound together
with the quadratic coprime-pair payment. -/
theorem exists_affine_gap_full_witness
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R Q L G C Y : ℕ) (ρ : ℝ)
    (hQ : 1 < Q) (hY : 0 < Y) (hC : 0 < C)
    (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity ((List.range R).map (Nat.nth p)))
    (hdensity : (4 : ℝ) / (C : ℝ) ≤ ρ / (2 * (Q : ℝ)))
    (hperiod : 5 * (Q *
      (coprimePart ((List.range R).map (Nat.nth p)) Q).prod) ≤ G)
    (hcovered : ∀ n, L < n → n < L + G → ∃ a, p a ∧ a ∣ n)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ 1 / (C : ℝ))
    (hsmall : ∀ q, Nat.Prime q → q ≤ Y → q ∣ Q)
    (hG : 256 * C ^ 2 ≤ G) (hCY : 64 * C ^ 2 ≤ Q ^ 2 * Y) :
    ∃ T : Finset ℕ,
      (∀ n ∈ T, L < n ∧ n < L + G) ∧
      (∀ n ∈ T, Nat.ModEq Q n 1) ∧
      Set.InjOn (divisorWitnessRank p) (T : Set ℕ) ∧
      G / C ≤ T.card ∧
      (∀ n ∈ T, G / C ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, R ≤ divisorWitnessRank p n) ∧
      (∀ n ∈ T, Nat.nth p (divisorWitnessRank p n) ∣ n) ∧
      G ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs T).card := by
  have hGC : 2 * C ≤ G := by
    have : 2 * C ≤ 256 * C ^ 2 := by nlinarith
    exact this.trans hG
  obtain ⟨T, hint, hcong, hinj, hcard, hhigh, hR, hdiv⟩ :=
    exists_affine_gap_high_rank_witnesses p hp hp2 R Q L G C ρ
      hQ hC hGC hρ0 hρ hdensity hperiod hcovered htail
  have hinterval : ∀ n ∈ T, L ≤ n ∧ n ≤ L + G := by
    intro n hn
    have := hint n hn
    omega
  have hpay := progression_many_coprime_pairs T L G Q Y C
    (by omega) hY hC hinterval hcong hsmall hcard hG hCY
  exact ⟨T, hint, hcong, hinj, hcard, hhigh, hR, hdiv, hpay⟩

end Erdos489

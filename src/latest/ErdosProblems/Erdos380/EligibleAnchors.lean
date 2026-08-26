import ErdosProblems.Erdos380.BoxProbability

/-! # The normalized estimate for actual singleton anchors with ten large prime factors -/

open scoped BigOperators Classical

namespace Erdos380

noncomputable def eligibleSingletons (N Q Y : ℕ) : Finset ℕ :=
  (singletonBadUpTo N).filter fun n =>
    Q ≤ topPrime (singletonCofactor n) 9 ∧ largestPrimeFactor n ≤ Y

lemma mem_eligibleSingletons {N Q Y n : ℕ} : n ∈ eligibleSingletons N Q Y ↔
    1 ≤ n ∧ n ≤ N ∧ SingletonBad n ∧
      Q ≤ topPrime (singletonCofactor n) 9 ∧ largestPrimeFactor n ≤ Y := by
  simp [eligibleSingletons, and_assoc]

noncomputable def eligiblePrimeBoxes (N Q Y : ℕ) : Finset (PrimeBox 10) :=
  (eligibleSingletons N Q Y).image (fun n => canonicalPrimeBox n 10)

noncomputable def goodEligibleAnchors (N Q T H D : ℕ) (ε : ℤˣ) (L : ℝ) : Finset ℕ :=
  (eligibleSingletons N Q (T ^ 110)).filter (SmoothShiftAt T H D ε L)

lemma dyadicPrimeIndex_ge {p d : ℕ} (hp : 2 ^ d < p) : d ≤ dyadicPrimeIndex p :=
  Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ d ≤ p - 1)

lemma goodEligibleAnchors_subset_goodPrimeBoxAnchors {N Q T H D : ℕ}
    (hQ : 2 ≤ Q) (ε : ℤˣ) (L : ℝ) :
    goodEligibleAnchors N Q T H D ε L ⊆
      goodPrimeBoxAnchors (eligiblePrimeBoxes N Q (T ^ 110)) T H D ε L := by
  intro n hn
  obtain ⟨hneligible, hnsmooth⟩ := Finset.mem_filter.mp hn
  obtain ⟨_, _, hbad, hlarge, _⟩ := mem_eligibleSingletons.mp hneligible
  have hprime : 1 < topPrime (singletonCofactor n) 9 := by omega
  apply Finset.mem_biUnion.mpr
  refine ⟨canonicalPrimeBox n 10, Finset.mem_image.mpr ⟨n, hneligible, rfl⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨canonicalPrimeRecord n 10, Finset.mem_filter.mpr ⟨?_, ?_⟩,
    hbad.canonicalPrimeRecord_value 10⟩
  · exact hbad.canonicalPrimeRecord_mem_box (by decide) hprime
  · simpa only [hbad.canonicalPrimeRecord_value] using hnsmooth

lemma eligiblePrimeBoxes_valid {N Q Y : ℕ} (hQ : 2 ≤ Q) :
    ∀ b ∈ eligiblePrimeBoxes N Q Y, ValidPrimeBox b := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, _, hbad, hlarge, _⟩ := mem_eligibleSingletons.mp hn
  exact hbad.canonicalPrimeBox_valid (by decide)
    (by change 1 < topPrime (singletonCofactor n) 9; omega)

lemma eligiblePrimeBoxes_size {N Q Y : ℕ} (hQ : 2 ≤ Q) :
    ∀ b ∈ eligiblePrimeBoxes N Q Y, primeBoxBaseValue b ≤ N := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, hnN, hbad, hlarge, _⟩ := mem_eligibleSingletons.mp hn
  exact (hbad.canonicalPrimeBox_base_le (by decide)
    (by change 1 < topPrime (singletonCofactor n) 9; omega)).trans hnN

lemma eligiblePrimeBoxes_scale {N Q Y d : ℕ} (hQ : 2 ≤ Q) (hdQ : 2 ^ d < Q) :
    ∀ b ∈ eligiblePrimeBoxes N Q Y, d ≤ b.1 ∧ ∀ i, d ≤ b.2.1 i := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, _, hbad, hlarge, _⟩ := mem_eligibleSingletons.mp hn
  have hi : ∀ i : Fin 10, d ≤ (canonicalPrimeBox n 10).2.1 i := by
    intro i
    exact dyadicPrimeIndex_ge (hdQ.trans_le (hbad.canonicalPrimeRecord_tuple_ge hlarge i))
  exact ⟨(hi 0).trans ((hbad.canonicalPrimeBox_valid (by decide)
    (by change 1 < topPrime (singletonCofactor n) 9; omega)).2.1 0), hi⟩

lemma eligiblePrimeBoxes_large {N Q Y R : ℕ} (hQ : 2 ≤ Q) (hRQ : R ≤ Q) :
    ∀ b ∈ eligiblePrimeBoxes N Q Y, ∀ i, R ≤ 2 ^ (b.2.1 i + 1) := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, _, hbad, hlarge, _⟩ := mem_eligibleSingletons.mp hn
  exact hbad.canonicalPrimeBox_tuple_upper_ge (by decide)
    (by change 1 < topPrime (singletonCofactor n) 9; omega) (hRQ.trans hlarge)

lemma eligiblePrimeBoxes_pool_bounds {N Q T : ℕ} (hQ : 2 ≤ Q) (hTQ : 2 * T ^ 90 ≤ Q) :
    ∀ b ∈ eligiblePrimeBoxes N Q (T ^ 110), ∀ i,
      T ^ 90 ≤ 2 ^ (b.2.1 i) ∧ 2 ^ (b.2.1 i) ≤ T ^ 110 := by
  intro b hb
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, _, hbad, hlarge, htop⟩ := mem_eligibleSingletons.mp hn
  intro i
  have hqi := hbad.canonicalPrimeRecord_prime_tuple (by decide)
    (by change 1 < topPrime (singletonCofactor n) 9; omega) i
  obtain ⟨hlo, hhi⟩ := dyadicPrimeIndex_bounds hqi.two_le
  have hlow := hTQ.trans (hbad.canonicalPrimeRecord_tuple_ge hlarge i)
  have hhigh := (hbad.canonicalPrimeRecord_tuple_le i).trans htop
  constructor
  · rw [pow_succ'] at hhi
    exact Nat.le_of_mul_le_mul_left (hlow.trans hhi) (by decide : 0 < 2)
  · exact hlo.le.trans hhigh

theorem exists_uniform_goodEligibleAnchors_bound :
    ∃ C K U₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < U₀ ∧ ∃ T₀ d₀ P₀ : ℕ,
      ∀ T ≥ T₀, ∀ N R Q : ℕ, 1 < R → 2 ≤ Q → 2 ^ d₀ < Q →
      2 * T ^ 90 ≤ Q → max P₀ (128 * primeBoxEnlargement 10 * R) ≤ Q →
      ∀ H : ℕ, 0 < H → H ≤ T → (H : ℝ) * (C * (Real.log T ^ 5 / (T : ℝ))) ≤ 1 →
      ∀ D : ℕ, 0 < D → ∀ ε : ℤˣ, ∀ U L : ℝ, U₀ ≤ U → (H : ℝ) ≤ U ^ 48 →
      2 * Real.log D + Real.log H + 111 * U * Real.log T ≤ L →
      ((goodEligibleAnchors N Q T H D ε L).card : ℝ) ≤
        K * (Real.log (N : ℝ) / Real.log (R : ℝ)) * (singletonBadUpTo N).card /
          ((H : ℝ) * U ^ 2) := by
  obtain ⟨C, K, U₀, hC, hK, hU₀, T₀, d₀, P₀, hbound⟩ := exists_uniform_goodPrimeBoxAnchors_bound
  refine ⟨C, K, U₀, hC, hK, hU₀, T₀, d₀, P₀, ?_⟩
  intro T hT N R Q hR hQ hdQ hTQ hPQ H hH hHT hmix D hD ε U L hU hHU hL
  have hscale := eligiblePrimeBoxes_scale (N := N) (Y := T ^ 110) hQ hdQ
  have hpool := eligiblePrimeBoxes_pool_bounds (N := N) hQ hTQ
  have h := hbound T hT N R hR (eligiblePrimeBoxes N Q (T ^ 110))
    (eligiblePrimeBoxes_valid hQ) (eligiblePrimeBoxes_size hQ)
    (fun b hb => (hscale b hb).1) (fun b hb => (hscale b hb).2)
    (eligiblePrimeBoxes_large hQ hPQ)
    (fun b hb i => (hpool b hb i).1) (fun b hb i => (hpool b hb i).2)
    H hH hHT hmix D hD ε U L hU hHU hL
  exact (show ((goodEligibleAnchors N Q T H D ε L).card : ℝ) ≤
      (goodPrimeBoxAnchors (eligiblePrimeBoxes N Q (T ^ 110)) T H D ε L).card by
    exact_mod_cast Finset.card_le_card (goodEligibleAnchors_subset_goodPrimeBoxAnchors hQ ε L)).trans h

end Erdos380

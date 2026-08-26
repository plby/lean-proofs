import ErdosProblems.Erdos380.CanonicalPrimeBoxes
import ErdosProblems.Erdos380.SmoothTupleProbability

/-! # Transferring tuple probabilities to counts of integer anchors -/

open scoped BigOperators Classical

namespace Erdos380

def SmoothShiftAt (T H D : ℕ) (ε : ℤˣ) (L : ℝ) (a : ℕ) : Prop :=
  ∀ j : Fin H, ∃ n : ℕ, 0 < n ∧ (n : ℤ) = (a : ℤ) + signedShift ε j ∧
    largestPrimeFactor n ≤ T ^ 110 ∧ (∀ d : ℕ, d ^ 2 ∣ n → d ≤ D) ∧ L ≤ Real.log n

lemma finite_event_card_le_of_probability_bound {Ω : Type*} (s : Finset Ω)
    (E : Ω → Prop) {δ : ℝ}
    (h : ((s.filter E).card : ℝ) / (s.card : ℝ) ≤ δ) :
    ((s.filter E).card : ℝ) ≤ δ * s.card := by
  classical
  by_cases hz : s.card = 0
  · have hs := Finset.card_eq_zero.mp hz
    simp [hs]
  · exact (div_le_iff₀ (by exact_mod_cast (Nat.pos_of_ne_zero hz))).mp h

lemma primeBoxRecords_event_card_eq {k : ℕ} (b : PrimeBox k) (E : ℕ → Prop) :
    ((primeBoxRecords b).filter fun r => E (primeRecordValue r)).card =
      ∑ p : dyadicPrimes (2 ^ b.1),
        (Finset.univ.filter fun f : ∀ i, dyadicPrimes (2 ^ (b.2.1 i)) =>
          E (primeRecordValue (primeBoxSampleRecord b (p, f)))).card := by
  classical
  rw [primeBoxRecords, Finset.filter_image,
    Finset.card_image_of_injective _ (primeBoxSampleRecord_injective b)]
  simp only [Finset.card_filter, Fintype.sum_prod_type]

lemma primeBoxRecords_event_card_le {k : ℕ} (b : PrimeBox k) (E : ℕ → Prop) {δ : ℝ}
    (h : ∀ p : dyadicPrimes (2 ^ b.1),
      ((Finset.univ.filter fun f : ∀ i, dyadicPrimes (2 ^ (b.2.1 i)) =>
        E (primeRecordValue (primeBoxSampleRecord b (p, f)))).card : ℝ) ≤
      δ * Fintype.card (∀ i, dyadicPrimes (2 ^ (b.2.1 i)))) :
    (((primeBoxRecords b).filter fun r => E (primeRecordValue r)).card : ℝ) ≤
      δ * primeBoxMass b := by
  rw [primeBoxRecords_event_card_eq, Nat.cast_sum]
  calc
    _ ≤ ∑ _p : dyadicPrimes (2 ^ b.1),
        δ * (Fintype.card (∀ i, dyadicPrimes (2 ^ (b.2.1 i))) : ℝ) :=
      Finset.sum_le_sum fun p _ => h p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
        Fintype.card_pi, primeBoxMass, Nat.cast_mul, Nat.cast_prod]
      ring

lemma primeBoxRecords_smoothShift_card_le (b : PrimeBox 10) (T H D : ℕ)
    (ε : ℤˣ) (L δ : ℝ)
    (hprob : ∀ c : ℕ,
      ((Finset.univ.filter fun f : ∀ i, dyadicPrimes (2 ^ (b.2.1 i)) =>
        SmoothShiftEvent (fun i => dyadicPrimes (2 ^ (b.2.1 i))) T H c D ε L f).card : ℝ) /
        (Fintype.card (∀ i, dyadicPrimes (2 ^ (b.2.1 i))) : ℝ) ≤ δ) :
    (((primeBoxRecords b).filter fun r => SmoothShiftAt T H D ε L (primeRecordValue r)).card : ℝ) ≤
      δ * primeBoxMass b := by
  apply primeBoxRecords_event_card_le
  intro p
  have h := finite_event_card_le_of_probability_bound Finset.univ
    (SmoothShiftEvent (fun i => dyadicPrimes (2 ^ (b.2.1 i))) T H (p.val ^ 2 * b.2.2) D ε L)
    (by simpa only [Finset.card_univ] using hprob (p.val ^ 2 * b.2.2))
  have hevent (f : ∀ i, dyadicPrimes (2 ^ (b.2.1 i))) :
      SmoothShiftAt T H D ε L (primeRecordValue (primeBoxSampleRecord b (p, f))) ↔
        SmoothShiftEvent (fun i => dyadicPrimes (2 ^ (b.2.1 i))) T H (p.val ^ 2 * b.2.2) D ε L f := by
    have hvalue : primeRecordValue (primeBoxSampleRecord b (p, f)) =
        (p.val ^ 2 * b.2.2) * tupleNaturalProduct (fun i => dyadicPrimes (2 ^ (b.2.1 i))) f := by
      simp only [primeRecordValue, primeBoxSampleRecord, tupleNaturalProduct]
      ring
    rw [hvalue]
    rfl
  have hfilter := Finset.filter_congr (s := (Finset.univ : Finset (∀ i, dyadicPrimes (2 ^ (b.2.1 i)))))
    (fun f _ => hevent f)
  rw [hfilter]
  simpa only [Finset.card_univ] using h

noncomputable def goodPrimeBoxAnchors (B : Finset (PrimeBox 10)) (T H D : ℕ)
    (ε : ℤˣ) (L : ℝ) : Finset ℕ :=
  B.biUnion fun b => ((primeBoxRecords b).filter fun r =>
    SmoothShiftAt T H D ε L (primeRecordValue r)).image primeRecordValue

lemma goodPrimeBoxAnchors_card_le (B : Finset (PrimeBox 10)) (T H D : ℕ)
    (ε : ℤˣ) (L δ : ℝ)
    (hbox : ∀ b ∈ B,
      (((primeBoxRecords b).filter fun r => SmoothShiftAt T H D ε L (primeRecordValue r)).card : ℝ) ≤
        δ * primeBoxMass b) :
    ((goodPrimeBoxAnchors B T H D ε L).card : ℝ) ≤ δ * ∑ b ∈ B, (primeBoxMass b : ℝ) := by
  have hnat : (goodPrimeBoxAnchors B T H D ε L).card ≤
      ∑ b ∈ B, ((primeBoxRecords b).filter fun r => SmoothShiftAt T H D ε L (primeRecordValue r)).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun b _ => Finset.card_image_le)
  calc
    ((goodPrimeBoxAnchors B T H D ε L).card : ℝ) ≤
        ∑ b ∈ B, (((primeBoxRecords b).filter fun r => SmoothShiftAt T H D ε L (primeRecordValue r)).card : ℝ) := by
      exact_mod_cast hnat
    _ ≤ ∑ b ∈ B, δ * primeBoxMass b := Finset.sum_le_sum hbox
    _ = _ := (Finset.mul_sum ..).symm

/-- A uniform anchor count relative to the original singleton count.
All box, smoothness, and square-divisor hypotheses are explicit. -/
theorem exists_uniform_goodPrimeBoxAnchors_bound :
    ∃ C K U₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < U₀ ∧ ∃ T₀ d₀ P₀ : ℕ,
      ∀ T ≥ T₀, ∀ N R : ℕ, 1 < R → ∀ B : Finset (PrimeBox 10),
      (∀ b ∈ B, ValidPrimeBox b) → (∀ b ∈ B, primeBoxBaseValue b ≤ N) →
      (∀ b ∈ B, d₀ ≤ b.1) → (∀ b ∈ B, ∀ i, d₀ ≤ b.2.1 i) →
      (∀ b ∈ B, ∀ i, max P₀ (128 * primeBoxEnlargement 10 * R) ≤ 2 ^ (b.2.1 i + 1)) →
      (∀ b ∈ B, ∀ i, T ^ 90 ≤ 2 ^ (b.2.1 i)) →
      (∀ b ∈ B, ∀ i, 2 ^ (b.2.1 i) ≤ T ^ 110) →
      ∀ H : ℕ, 0 < H → H ≤ T → (H : ℝ) * (C * (Real.log T ^ 5 / (T : ℝ))) ≤ 1 →
      ∀ D : ℕ, 0 < D → ∀ ε : ℤˣ, ∀ U L : ℝ, U₀ ≤ U → (H : ℝ) ≤ U ^ 48 →
      2 * Real.log D + Real.log H + 111 * U * Real.log T ≤ L →
      ((goodPrimeBoxAnchors B T H D ε L).card : ℝ) ≤
        K * (Real.log (N : ℝ) / Real.log (R : ℝ)) * (singletonBadUpTo N).card /
          ((H : ℝ) * U ^ 2) := by
  obtain ⟨C, Kp, U₀, hC, hKp, hU₀, T₀, hprob⟩ := exists_uniform_smoothShift_probability_bound
  obtain ⟨d₀, P₀, hnorm⟩ := exists_primeBoxMass_normalization 10 (by decide)
  let Kb : ℝ := (60 ^ (10 + 1) * Nat.factorial 10 * (8 * primeBoxEnlargement 10) : ℕ)
  have hKb : 0 < Kb := by dsimp [Kb, primeBoxEnlargement]; positivity
  refine ⟨C, Kp * Kb, U₀, hC, mul_pos hKp hKb, hU₀, T₀, d₀, P₀, ?_⟩
  intro T hT N R hR B hvalid hsize hbase htuple hlarge hlo hhi H hH hHT hmix D hD ε U L hU hHU hL
  have hUpos : 0 < U := hU₀.trans_le hU
  let δ := Kp / ((H : ℝ) * U ^ 2)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hbox (b : PrimeBox 10) (hb : b ∈ B) :
      (((primeBoxRecords b).filter fun r => SmoothShiftAt T H D ε L (primeRecordValue r)).card : ℝ) ≤
        δ * primeBoxMass b := by
    apply primeBoxRecords_smoothShift_card_le
    intro c
    exact hprob T hT (fun i => 2 ^ (b.2.1 i)) (hlo b hb) (hhi b hb)
      H hH hHT hmix c D hD ε U L hU hHU hL
  have hgood := goodPrimeBoxAnchors_card_le B T H D ε L δ hbox
  have hmass : (∑ b ∈ B, (primeBoxMass b : ℝ)) ≤
      Kb * (Real.log (N : ℝ) / Real.log (R : ℝ)) * (singletonBadUpTo N).card := by
    simpa only [Nat.cast_sum, Kb] using hnorm N R hR B hvalid hsize hbase htuple hlarge
  calc
    ((goodPrimeBoxAnchors B T H D ε L).card : ℝ) ≤ δ * ∑ b ∈ B, (primeBoxMass b : ℝ) := hgood
    _ ≤ δ * (Kb * (Real.log (N : ℝ) / Real.log (R : ℝ)) * (singletonBadUpTo N).card) :=
      mul_le_mul_of_nonneg_left hmass hδ
    _ = _ := by dsimp [δ]; ring

end Erdos380

import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.CharacterLargeSieve

/-!
# Elliott's exact-order character large-sieve estimate

This file records the finite large-sieve/counting step in Elliott's argument.
The important point is that the character family is restricted to characters
of **exact** order `k`, rather than characters whose order merely divides `k`.

There are no asymptotics in this module.  The final two results say that any
family of exact-order primitive characters on which a finite amplifier has
size at least `eta` is rare, with the exact large-sieve coefficient
`N + Q^2`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos980.ElliottTail

open BoundedGaps.Maynard

/-- Primitive characters modulo `q` having exact multiplicative order `k`. -/
def exactOrderPrimitiveCharacters (q k : ℕ) :
    Finset (primitiveCharacters q) := by
  classical
  exact Finset.univ.filter fun ψ ↦ orderOf ψ.1 = k

@[simp] theorem mem_exactOrderPrimitiveCharacters {q k : ℕ}
    {ψ : primitiveCharacters q} :
    ψ ∈ exactOrderPrimitiveCharacters q k ↔ orderOf ψ.1 = k := by
  classical
  simp [exactOrderPrimitiveCharacters]

/-- Exact-order characters satisfying the lower bound supplied by an
amplifier. -/
def largeExactOrderPrimitiveCharacters
    (q k : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (eta : ℝ) :
    Finset (primitiveCharacters q) := by
  classical
  exact (exactOrderPrimitiveCharacters q k).filter fun ψ ↦
    eta ≤ ‖∑ n ∈ s, c n * ψ.1 n‖

@[simp] theorem mem_largeExactOrderPrimitiveCharacters
    {q k : ℕ} {s : Finset ℕ} {c : ℕ → ℂ} {eta : ℝ}
    {ψ : primitiveCharacters q} :
    ψ ∈ largeExactOrderPrimitiveCharacters q k s c eta ↔
      orderOf ψ.1 = k ∧ eta ≤ ‖∑ n ∈ s, c n * ψ.1 n‖ := by
  classical
  simp [largeExactOrderPrimitiveCharacters]

theorem largeExactOrderPrimitiveCharacters_subset
    (q k : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (eta : ℝ) :
    largeExactOrderPrimitiveCharacters q k s c eta ⊆
      exactOrderPrimitiveCharacters q k := by
  classical
  exact Finset.filter_subset _ _

/-- Restricting the primitive-character large sieve to exact order `k` does
not change its constant. -/
theorem sum_weighted_norm_sq_exactOrderPrimitiveTwists_subset_Ioc_le
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ∑ ψ ∈ exactOrderPrimitiveCharacters q k,
          ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ ψ ∈ exactOrderPrimitiveCharacters q k,
            ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (Nat.totient q : ℝ) *
            ∑ ψ : primitiveCharacters q,
              ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro ψ _hψ _hnot
          positivity
      · positivity
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s, ‖c n‖ ^ 2 :=
      sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
        Q m0 N s hs c

/-- The elementary amplifier inequality at one modulus: every character in
the exceptional family contributes at least `eta^2` to the second moment. -/
theorem largeExactOrderPrimitiveCharacters_card_mul_sq_le
    {q k : ℕ} {s : Finset ℕ} {c : ℕ → ℂ} {eta : ℝ}
    (heta : 0 ≤ eta) :
    eta ^ 2 *
        ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) ≤
      ∑ ψ ∈ exactOrderPrimitiveCharacters q k,
        ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
  classical
  calc
    eta ^ 2 *
        ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) =
        ∑ _ψ ∈ largeExactOrderPrimitiveCharacters q k s c eta,
          eta ^ 2 := by simp [mul_comm]
    _ ≤ ∑ ψ ∈ largeExactOrderPrimitiveCharacters q k s c eta,
        ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro ψ hψ
      exact pow_le_pow_left₀ heta
        (mem_largeExactOrderPrimitiveCharacters.mp hψ).2 2
    _ ≤ ∑ ψ ∈ exactOrderPrimitiveCharacters q k,
        ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact largeExactOrderPrimitiveCharacters_subset q k s c eta
      · intro ψ _hψ _hnot
        positivity

/-- Weighted exact-order rarity bound, in the direct multiplication form
that remains valid at `eta = 0`. -/
theorem weighted_largeExactOrderPrimitiveCharacters_le
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    {eta : ℝ} (heta : 0 ≤ eta) :
    eta ^ 2 *
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (Nat.totient q : ℝ) *
            ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
  calc
    eta ^ 2 *
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (Nat.totient q : ℝ) *
            ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) =
        ∑ q ∈ Finset.Ioc 0 Q,
          eta ^ 2 * ((q : ℝ) / (Nat.totient q : ℝ) *
            ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ ψ ∈ exactOrderPrimitiveCharacters q k,
            ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hweight : 0 ≤ (q : ℝ) / (Nat.totient q : ℝ) := by
        positivity
      calc
        eta ^ 2 * ((q : ℝ) / (Nat.totient q : ℝ) *
            ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ)) =
            (q : ℝ) / (Nat.totient q : ℝ) *
              (eta ^ 2 *
                ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ)) := by
              ring
        _ ≤ (q : ℝ) / (Nat.totient q : ℝ) *
            ∑ ψ ∈ exactOrderPrimitiveCharacters q k,
              ‖∑ n ∈ s, c n * ψ.1 n‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (largeExactOrderPrimitiveCharacters_card_mul_sq_le heta) hweight
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s, ‖c n‖ ^ 2 :=
      sum_weighted_norm_sq_exactOrderPrimitiveTwists_subset_Ioc_le
        Q m0 N k s hs c

/-- Removing the standard `q / φ(q)` weights only weakens the count. -/
theorem sum_card_largeExactOrderPrimitiveCharacters_le_weighted
    (Q k : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (eta : ℝ) :
    (∑ q ∈ Finset.Ioc 0 Q,
        ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ)) ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) := by
  classical
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
  have hphiPos : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hphiLe : (Nat.totient q : ℝ) ≤ q := by
    exact_mod_cast Nat.totient_le q
  have hweight : (1 : ℝ) ≤ (q : ℝ) / (Nat.totient q : ℝ) := by
    rw [one_le_div₀ hphiPos]
    exact hphiLe
  calc
    ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) =
        1 * ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) := by
          ring
    _ ≤ (q : ℝ) / (Nat.totient q : ℝ) *
          ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hweight (by positivity)

/-- Elliott's finite rarity estimate in unweighted cardinality form. -/
theorem largeExactOrderPrimitiveCharacters_rarity
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    {eta : ℝ} (heta : 0 ≤ eta) :
    eta ^ 2 *
        ∑ q ∈ Finset.Ioc 0 Q,
          ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
  calc
    eta ^ 2 *
        ∑ q ∈ Finset.Ioc 0 Q,
          ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) ≤
        eta ^ 2 *
          ∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (Nat.totient q : ℝ) *
              ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_card_largeExactOrderPrimitiveCharacters_le_weighted Q k s c eta)
        (sq_nonneg eta)
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s, ‖c n‖ ^ 2 :=
      weighted_largeExactOrderPrimitiveCharacters_le
        Q m0 N k s hs c heta

/-- Division form of the rarity estimate for a genuinely positive
amplifier threshold. -/
theorem largeExactOrderPrimitiveCharacters_rarity_div
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    {eta : ℝ} (heta : 0 < eta) :
    (∑ q ∈ Finset.Ioc 0 Q,
        ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ)) ≤
      (((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2) / eta ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos heta)]
  simpa [mul_comm] using
    largeExactOrderPrimitiveCharacters_rarity
      Q m0 N k s hs c heta.le

/-! ## Counting exceptional moduli

The large sieve counts characters.  Elliott needs a count of moduli.  The
next lemma is the exact finite bookkeeping step: a set of moduli with a
nonempty exceptional fiber injects, at the level of cardinalities, into the
disjoint union of those fibers. -/

theorem card_le_sum_card_of_fibers_nonempty
    {Q : ℕ} (bad : Finset ℕ)
    (F : (q : ℕ) → Finset (primitiveCharacters q))
    (hbad : bad ⊆ Finset.Ioc 0 Q)
    (hnonempty : ∀ q ∈ bad, (F q).Nonempty) :
    bad.card ≤ ∑ q ∈ Finset.Ioc 0 Q, (F q).card := by
  calc
    bad.card = ∑ _q ∈ bad, 1 := by simp
    _ ≤ ∑ q ∈ bad, (F q).card := by
      apply Finset.sum_le_sum
      intro q hq
      exact (Finset.one_le_card.mpr (hnonempty q hq))
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q, (F q).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hbad
        (fun _q _hq _hnot ↦ Nat.zero_le _)

/-- Corrected exact-order rarity estimate for moduli.  It is enough to
produce, for every bad modulus, one primitive character of exact order `k`
on which the amplifier is at least `eta`; no choice of witnesses enters the
bound. -/
theorem exactOrder_amplified_moduli_card_mul_sq_le
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    {eta : ℝ} (heta : 0 ≤ eta) (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.Ioc 0 Q)
    (hamplifier : ∀ q ∈ bad,
      ∃ ψ : primitiveCharacters q,
        orderOf ψ.1 = k ∧ eta ≤ ‖∑ n ∈ s, c n * ψ.1 n‖) :
    eta ^ 2 * (bad.card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
  have hnonempty : ∀ q ∈ bad,
      (largeExactOrderPrimitiveCharacters q k s c eta).Nonempty := by
    intro q hq
    obtain ⟨ψ, horder, hlarge⟩ := hamplifier q hq
    exact ⟨ψ, mem_largeExactOrderPrimitiveCharacters.mpr
      ⟨horder, hlarge⟩⟩
  have hcardNat : bad.card ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        (largeExactOrderPrimitiveCharacters q k s c eta).card :=
    card_le_sum_card_of_fibers_nonempty bad
      (fun q ↦ largeExactOrderPrimitiveCharacters q k s c eta)
      hbad hnonempty
  have hcardReal : (bad.card : ℝ) ≤
      ∑ q ∈ Finset.Ioc 0 Q,
        ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    eta ^ 2 * (bad.card : ℝ) ≤
        eta ^ 2 *
          ∑ q ∈ Finset.Ioc 0 Q,
            ((largeExactOrderPrimitiveCharacters q k s c eta).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hcardReal (sq_nonneg eta)
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ s, ‖c n‖ ^ 2 :=
      largeExactOrderPrimitiveCharacters_rarity
        Q m0 N k s hs c heta

/-- Division form of the exact-order exceptional-modulus estimate. -/
theorem exactOrder_amplified_moduli_card_le
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    {eta : ℝ} (heta : 0 < eta) (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.Ioc 0 Q)
    (hamplifier : ∀ q ∈ bad,
      ∃ ψ : primitiveCharacters q,
        orderOf ψ.1 = k ∧ eta ≤ ‖∑ n ∈ s, c n * ψ.1 n‖) :
    (bad.card : ℝ) ≤
      (((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2) / eta ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos heta)]
  simpa [mul_comm] using
    exactOrder_amplified_moduli_card_mul_sq_le
      Q m0 N k s hs c heta.le bad hbad hamplifier

/-! ## The constant amplifier

If a character is one on the whole support, the constant-coefficient
amplifier has its maximal possible norm, namely the support cardinality.
Substitution into the preceding estimate gives the especially transparent
bound `#support * #bad ≤ N + Q²`. -/

theorem norm_constantAmplifier_eq_card
    {q : ℕ} (s : Finset ℕ) (ψ : primitiveCharacters q)
    (hone : ∀ n ∈ s, ψ.1 n = 1) :
    ‖∑ n ∈ s, (1 : ℂ) * ψ.1 n‖ = (s.card : ℝ) := by
  have hsum : (∑ n ∈ s, (1 : ℂ) * ψ.1 n) = (s.card : ℂ) := by
    calc
      (∑ n ∈ s, (1 : ℂ) * ψ.1 n) =
          ∑ _n ∈ s, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [hone n hn]
      _ = (s.card : ℂ) := by simp
  rw [hsum, Complex.norm_natCast]

/-- Before cancellation, the constant amplifier gives a completely exact
finite inequality, also valid for the empty support. -/
theorem exactOrder_trivialOnSet_moduli_card_mul_card_sq_le
    (Q m0 N k : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.Ioc 0 Q)
    (htrivial : ∀ q ∈ bad,
      ∃ ψ : primitiveCharacters q,
        orderOf ψ.1 = k ∧ ∀ n ∈ s, ψ.1 n = 1) :
    (s.card : ℝ) ^ 2 * (bad.card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * (s.card : ℝ) := by
  have hamplifier : ∀ q ∈ bad,
      ∃ ψ : primitiveCharacters q,
        orderOf ψ.1 = k ∧
          (s.card : ℝ) ≤ ‖∑ n ∈ s, (1 : ℂ) * ψ.1 n‖ := by
    intro q hq
    obtain ⟨ψ, horder, hone⟩ := htrivial q hq
    refine ⟨ψ, horder, ?_⟩
    exact (norm_constantAmplifier_eq_card s ψ hone).ge
  simpa using
    (exactOrder_amplified_moduli_card_mul_sq_le
      Q m0 N k s hs (fun _n ↦ (1 : ℂ))
      (by positivity) bad hbad hamplifier)

/-- Cancelling one nonzero copy of the amplifier length gives Elliott's
finite exact-order rarity bound. -/
theorem exactOrder_trivialOnSet_moduli_card_mul_card_le
    (Q m0 N k : ℕ) (s : Finset ℕ) (hs0 : s.Nonempty)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.Ioc 0 Q)
    (htrivial : ∀ q ∈ bad,
      ∃ ψ : primitiveCharacters q,
        orderOf ψ.1 = k ∧ ∀ n ∈ s, ψ.1 n = 1) :
    (s.card : ℝ) * (bad.card : ℝ) ≤
      (N : ℝ) + (Q : ℝ) ^ 2 := by
  have hcardPos : (0 : ℝ) < s.card := by
    exact_mod_cast hs0.card_pos
  apply (mul_le_mul_iff_left₀ hcardPos).mp
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
    exactOrder_trivialOnSet_moduli_card_mul_card_sq_le
      Q m0 N k s hs bad hbad htrivial

/-- Division form: the number of bad moduli is at most the large-sieve
coefficient divided by the length of the constant amplifier. -/
theorem exactOrder_trivialOnSet_moduli_card_le
    (Q m0 N k : ℕ) (s : Finset ℕ) (hs0 : s.Nonempty)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.Ioc 0 Q)
    (htrivial : ∀ q ∈ bad,
      ∃ ψ : primitiveCharacters q,
        orderOf ψ.1 = k ∧ ∀ n ∈ s, ψ.1 n = 1) :
    (bad.card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) / (s.card : ℝ) := by
  have hcardPos : (0 : ℝ) < s.card := by
    exact_mod_cast hs0.card_pos
  rw [le_div_iff₀ hcardPos]
  simpa [mul_comm] using
    exactOrder_trivialOnSet_moduli_card_mul_card_le
      Q m0 N k s hs0 hs bad hbad htrivial

end Erdos980.ElliottTail

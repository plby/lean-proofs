/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes Erdős Problem 387.

Mathematical source:
H. M. Bui, S. Naprienko, K. Pratt, A. Zaharescu,
"Binomial coefficients with divisors avoiding an interval",
arXiv:2605.21221v2 (2026).

Progress log (2026-08-15):
* Phase 1: the mathematical reconstruction and Leanization plan are in
  `tex/387.tex`.
* Phase 2, verified here so far: the exact logical reduction from a
  counterexample for every positive real endpoint; the Archimedean reduction
  from the qualitative fixed-B BNPZ theorem; and, in `CoverAlgebra.lean`, the
  CRT realization, binomial-product identity, divisor splitting, size bound,
  and pairwise-coprimality lemmas used at the algebraic/analytic interface.
  `AnalyticInputs.lean` also derives the exact fixed-modulus dyadic-interval
  PNT used by the public cover proof from the repository's `WeakPNT_AP`, then
  proves the public shifted lower bound for each fixed `(Q,a,h)` and uniformly
  over every fixed finite family.  `CoverLemma.lean` ports and verifies the
  public 1,900-line fixed-parameter covering lemma against that axiom-free PNT
  under the default computational limits.  `CoverBPZPrelude.lean` additionally
  ports the 8,600-line axiom-free public development through the exact point
  immediately preceding its first use of uniform Siegel--Walfisz, and
  `CoverBPZConditional.lean` verifies the remaining wide-cover construction
  with that analytic proposition passed explicitly as a theorem argument.
  `CoverAlgebra.lean` now also packages residual divisor choices as finite
  tuples and proves uniqueness of their product representation under the
  certified pairwise-coprimality hypothesis.  `DivisorStructure.lean`
  formalizes the elementary post-Proposition-6.4 case split: absence of a
  convenient factorization forces a `y ^ 3`-small factor times at most one
  large prime.  `Section6Counting.lean`, `ErrorClasses.lean`, and
  `ErrorCounting.lean` give literal finite sifted/error sets and the complete
  cardinality handoff.  `LocalDensity.lean` proves the exact `k` forbidden
  residue classes modulo every prime greater than `k`, combines them by CRT
  into exactly `k ^ ω(g)` classes for every squarefree modulus `g`, and
  counts their occurrences in finite initial intervals with an explicit
  remainder and in arbitrary half-open intervals.  `BrunSieve.lean` adds the
  lower-bound dual missing from Mathlib's Selberg-sieve API and proves that
  every odd Möbius truncation is a valid lower weight; it now also proves the
  matching upper-sieve theorem for every even truncation.  `BrunMainTerm.lean`
  identifies both main terms with finite subset sums, bounds their tails by a
  finite Euler product, and gives a uniform `[V/2, 3V/2]` comparison under an
  explicit tail hypothesis.  `SieveInstantiation.lean` constructs the literal
  binomial sieve, identifies its sifted sum and multiple sums with the named
  finite candidate sets, evaluates its squarefree local density, combines
  that density with the covering progression by CRT, and proves the uniform
  concrete remainder bound `|R_d| ≤ 4 k ^ ω(d)`, with both lower and upper
  Brun bounds.  Finally, `QualitativeCover.lean` extracts from the public,
  unconditional fixed-parameter cover a natural-number factorization of the
  binomial coefficient into positive, pairwise-coprime residuals whose product
  is exactly `Nat.choose` and whose individual sizes are at most `n / B`.
  `UniformAnalyticInputs.lean` now derives the growing-polylogarithmic shifted
  prime-count estimate from the axiom-free weighted Bombieri--Vinogradov

theorem erdos_387_of_counterexamples
    (h : ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k) :
    False ↔ ∃ c : ℝ, UniversalNearDivisor c := by
  sorry

theorem erdos_387_of_fixedB
    (h : ∀ B : ℕ, 2 ≤ B → ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_eventually_fixedB
    (h : ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_eventually_BNPZ
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ n : ℕ, 1 ≤ k ∧ k < n ∧
        ∀ d : ℕ,
          (d : ℝ) ∈ Set.Ioc (BNPZEndpoint k * n) n → ¬d ∣ n.choose k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_cover_certificates
    (h : ∀ B : ℕ, 2 ≤ B →
      ∃ n k : ℕ, ∃ D : CoverFactorization n k,
        1 ≤ k ∧ k < n ∧
        ∀ e : ℕ → ℕ,
          (∀ i < k, e i ∣ (n - i) / D.g i) →
          ¬((∏ i ∈ Finset.range k, e i : ℕ) : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_absorber_error_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ T z y medium large : ℕ,
          3 ≤ k ∧ 2 ≤ y ∧
          (AbsorberLargeErrors C T z large).card +
              (AbsorberMediumErrors C T z medium large).card +
              (AbsorberConvenientErrors C T z y medium).card +
              (AbsorberAlmostPrimeErrors C T z y medium).card <
            (SiftedAbsorberParameterCandidates C T z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_frozen_roughProduct_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ t₀ T z : ℕ,
          3 ≤ k ∧
          (FrozenRoughProductErrors C t₀ T z).card <
            (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_refined_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large : ℕ,
          2 ≤ y ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedAlmostPrimeErrors S X z y medium).card <
            (RefinedSiftedCandidates S X z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_refined_five_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large secondMin gap : ℕ,
          2 ≤ y ∧ 1 ≤ secondMin ∧
          B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2 ∧
          B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2 ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedComparablePrimeErrors S X z secondMin gap
                medium).card +
              (CoverBPZ.RefinedSeparatedAlmostPrimeErrors S X z y medium
                secondMin gap).card <
            (RefinedSiftedCandidates S X z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry


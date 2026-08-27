/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRestrictedPrimeEdges

/-! # Constructed regular source data for quantitative covering -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

structure RegularSourceConditions {c e : ℝ} {x : ℕ} (D : SourceProbabilityData c e x)
    (a : ℝ) (b : ResidueAssignment (sourceSmallPrimes a x)) : Prop where
  log_ge : 2 ≤ Real.log (x : ℝ)
  interval_nonneg : 0 ≤ sourceIntervalLength c x
  survivor_deviation :
    |((sourceSurvivorVertices a c x b).card : ℝ) - sourceSurvivorMean a c x| <
      sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ))
  bad_prime_count : ((D.badTuplePrimes (sourceSmallPrimes a x) b).card : ℝ) <
    4 * (x : ℝ) / Real.log (x : ℝ) ^ 4
  cardinal_lower : sourceSurvivorMean a c x / 2 ≤ (D.sourceRegularVertices a b).card
  cardinal_upper : ((D.sourceRegularVertices a b).card : ℝ) ≤ 2 * sourceSurvivorMean a c x
  cardinal_sq : ((D.sourceRegularVertices a b).card : ℝ) ≤ (x : ℝ) ^ 2
  vertices_nonempty : (D.sourceRegularVertices a b).Nonempty
  removed_count : ((sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card : ℝ) <
    2 * ((x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2))
  degree : ∀ q ∈ D.sourceRegularVertices a b,
    |D.primeTupleExpectedDegree (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b q -
      D.expectedDegreeScale (sourceSmallPrimes a x)| ≤ 1 / Real.log (Real.log (x : ℝ)) ^ 2
  sparse : ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ q : ℕ,
    D.primeTupleEdgeProbability (sourceSmallPrimes a x) (D.sourceRegularVertices a b) b p q ≤
      (x : ℝ) ^ (-3 / 5 : ℝ)
  codegree : ∀ q ∈ D.sourceRegularVertices a b, ∀ q' ∈ D.sourceRegularVertices a b, q ≠ q' →
    (∑ p ∈ commonPinnedPrimeSet (x / 2) x,
      D.primeTupleEdgePairProbability (sourceSmallPrimes a x)
        (D.sourceRegularVertices a b) b p q q') ≤ (x : ℝ) ^ (-1 / 20 : ℝ)

theorem eventually_exists_regularSourceConditions {a c e : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hepos : 0 < e) (he : e ≤ 1 / 120) :
    ∀ᶠ x : ℕ in atTop, ∃ D : SourceProbabilityData c e x,
      ∃ b : ResidueAssignment (sourceSmallPrimes a x), RegularSourceConditions D a b := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_nonempty_sourceProbabilityData hc hepos,
    eventually_exists_source_good_assignment ha hc (show e ≤ 1 / 12 by linarith),
    eventually_source_cleanup_budget ha hc, eventually_sourceSurvivorMean_ge_log_pow ha hc 0,
    eventually_sourceIntervalLength_bounds hc,
    eventually_sourceRegularVertices_card_le_sq (a := a) (e := e) hc,
    eventually_sourceRegularVertices_degree (e := e) ha hc,
    eventually_sourceRegularVertices_sparsity (c := c) ha he,
    eventually_sourceRegularVertices_codegree ha hc he,
    hlog.eventually (eventually_ge_atTop (2 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (4 : ℝ))] with
      x hD hgood hcleanup hM hy hcardSq hdegree hsparse hcode hL hl
  change 4 ≤ Real.log (Real.log (x : ℝ)) at hl
  obtain ⟨D⟩ := hD
  obtain ⟨b, hsize, hbad, hpin, hlost⟩ := hgood D
  have hMpos : 0 < sourceSurvivorMean a c x := by
    simp only [pow_zero] at hM
    linarith
  have hcard := D.sourceRegularVertices_card_bounds b hl hMpos.le hcleanup hsize hpin hlost
  have hnonempty : (D.sourceRegularVertices a b).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (half_pos hMpos).trans_le hcard.1
  exact ⟨D, b, {
    log_ge := hL
    interval_nonneg := (Nat.cast_nonneg x).trans hy.1
    survivor_deviation := hsize
    bad_prime_count := hbad
    cardinal_lower := hcard.1
    cardinal_upper := hcard.2.1
    cardinal_sq := hcardSq D b
    vertices_nonempty := hnonempty
    removed_count := hcard.2.2
    degree := hdegree D b
    sparse := hsparse D b
    codegree := hcode D b }⟩

theorem exists_regularSourceData_with_degree_range {a T e : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hepos : 0 < e) (he : e ≤ 1 / 120) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ D : SourceProbabilityData c e x, ∃ b : ResidueAssignment (sourceSmallPrimes a x),
        RegularSourceConditions D a b ∧
        T ≤ D.expectedDegreeScale (sourceSmallPrimes a x) ∧
        D.expectedDegreeScale (sourceSmallPrimes a x) ≤ K := by
  obtain ⟨c, K, hc, hK, hscale⟩ := exists_source_expectedDegree_range ha hT
  refine ⟨c, K, hc, hK, ?_⟩
  filter_upwards [eventually_exists_regularSourceConditions ha hc hepos he, hscale] with x hx hC
  obtain ⟨D, b, hb⟩ := hx
  exact ⟨D, b, hb, hC e D⟩

end

end Erdos4b.FGKMT

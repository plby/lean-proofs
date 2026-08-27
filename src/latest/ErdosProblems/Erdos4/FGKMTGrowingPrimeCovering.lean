import ErdosProblems.Erdos4.FGKMTGrowingInitialConfiguration
import ErdosProblems.Erdos4.FGKMTGrowingPartitionBudget
import ErdosProblems.Erdos4.FGKMTGrowingSparsity

/-! Unconditional covering of the target primes at the full FGKMT interval scale. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter Classical ChebyshevIntervals

noncomputable def sourceSurvivors (sources targets : Finset ℕ) (U : Finset targets)
    (b : ∀ p : sources, ZMod p.val) : Finset targets :=
  U.filter (fun q => ∀ p : sources, (q.val : ZMod p.val) ≠ b p)

theorem sourceSurvivors_card_le (sources targets : Finset ℕ) (U V : Finset targets)
    (choice : sources → Finset V) (b : ∀ p : sources, ZMod p.val)
    (hb : ∀ p q, q ∈ choice p → (q.val.val : ZMod p.val) = b p) :
    (sourceSurvivors sources targets U b).card ≤
      (U \ V).card + (Finset.univ \ Finset.univ.biUnion choice).card := by
  let W : Finset V := Finset.univ \ Finset.univ.biUnion choice
  have hsub : sourceSurvivors sources targets U b ⊆
      (U \ V) ∪ W.image (fun q : V => q.val) := by
    intro q hq
    obtain ⟨hqU, havoid⟩ := Finset.mem_filter.mp hq
    by_cases hqV : q ∈ V
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨⟨q, hqV⟩, ?_, rfl⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hcovered
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hcovered
      exact havoid p (hb p ⟨q, hqV⟩ hp)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hqU, hqV⟩))
  calc
    _ ≤ ((U \ V) ∪ W.image (fun q : V => q.val)).card := Finset.card_le_card hsub
    _ ≤ (U \ V).card + (W.image (fun q : V => q.val)).card := Finset.card_union_le _ _
    _ ≤ (U \ V).card + W.card := Nat.add_le_add_left (Finset.card_image_le) _

theorem exists_growing_prime_covering :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      let Y := growingGapLength c x
      let targets := primeInterval x Y
      ∃ (a : ∀ l : growingRandomPrimes x, ZMod (growingRandomValue x l))
        (b : ∀ p : growingSourcePrimes x, ZMod p.val),
        ((sourceSurvivors (growingSourcePrimes x) targets
          (initialSurvivors (growingRandomValue x) Y targets a) b).card : ℝ) ≤
            C * x / Real.log (x : ℝ) := by
  obtain ⟨c, A, B, hc, hA, hB, hinitial⟩ := exists_growing_initial_configuration
  refine ⟨c, B + 4 * A, hc, by positivity, ?_⟩
  filter_upwards [hinitial, eventually_growing_cover_parameters,
    eventually_growing_cover_sparsity, eventually_growing_partition_budget A hA.le,
    eventually_ge_atTop 2] with x hconfig hpar hsparse hpartition hx
  let Y := growingGapLength c x
  let targets := primeInterval x Y
  let sources := growingSourcePrimes x
  let k := sieveDimension (growingIndex x)
  obtain ⟨a, V, ν, _, hV, hmiss, hdegree, hmarginal, hpair, hlegal⟩ := hconfig
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hjpos : (0 : ℝ) < growingIndex x := by exact_mod_cast hpar.1
  have hLpos : 0 < Real.log (x : ℝ) := hjpos.trans_le hpar.2.1
  have hk : 1 ≤ k := by unfold k sieveDimension; exact Nat.one_le_two_pow
  have hεδ := growing_marginal_le_sparsity (show 1 ≤ x by omega)
  have hsquare : (Fintype.card sources : ℝ) * ((x : ℝ) ^ (-4 / 5 : ℝ)) ^ 2 ≤
      ((x : ℝ) ^ (-1 / 5 : ℝ)) ^ 2 := by
    simpa only [Fintype.card_coe] using
      source_count_square_budget (show 1 ≤ x by omega) (growingSourcePrimes_card_le x)
  have hpart : (growingRounds x : ℝ) * Fintype.card V *
      Real.exp (-((1 / 2 : ℝ) ^ growingRounds x) / (6 * (x : ℝ) ^ (-4 / 5 : ℝ))) < 1 := by
    simpa only [Fintype.card_coe, growingCoverDensity] using hpartition V.card hV
  obtain ⟨choice, hchoice, hcard⟩ := source_covering (m := growingRounds x) (r := k) ν hk
    (Real.rpow_pos_of_pos hxpos (-4 / 5 : ℝ)) (Real.rpow_nonneg hxpos.le (-1 / 5 : ℝ))
    hεδ hdegree (fun p e he => (hlegal p e he).1) hmarginal hsquare
    (fun v w hvw => (hpair v w hvw).trans hεδ) hpart hsparse
  have hresidue : ∀ p : sources, ∃ r : ZMod p.val,
      ∀ q ∈ choice p, (q.val.val : ZMod p.val) = r := by
    intro p
    rcases hchoice p with hzero | ⟨e, he, hsub⟩
    · refine ⟨0, ?_⟩
      intro q hq
      simp [hzero] at hq
    · obtain ⟨r, hr⟩ := (hlegal p e he).2
      exact ⟨r, fun q hq => hr q (hsub hq)⟩
  choose b hb using hresidue
  have hcard' : ((Finset.univ \ Finset.univ.biUnion choice).card : ℝ) ≤
      2 * (V.card : ℝ) * growingCoverDensity x := by
    simpa only [Fintype.card_coe, growingCoverDensity] using hcard
  have hκupper := hpar.2.2.2.2.2
  have hκnonneg : 0 ≤ growingCoverDensity x := by
    unfold growingCoverDensity
    positivity
  have hremaining : ((Finset.univ \ Finset.univ.biUnion choice).card : ℝ) ≤
      4 * A * x / Real.log (x : ℝ) := by
    calc
      _ ≤ 2 * (V.card : ℝ) * growingCoverDensity x := hcard'
      _ ≤ 2 * (A * x * (growingIndex x : ℝ) / Real.log (x : ℝ)) *
          (2 / (growingIndex x : ℝ)) := by gcongr
      _ = _ := by field_simp; ring
  refine ⟨a, b, ?_⟩
  have hcount : ((sourceSurvivors sources targets
      (initialSurvivors (growingRandomValue x) Y targets a) b).card : ℝ) ≤
      ((initialSurvivors (growingRandomValue x) Y targets a \ V).card : ℝ) +
      ((Finset.univ \ Finset.univ.biUnion choice).card : ℝ) := by
    exact_mod_cast sourceSurvivors_card_le sources targets
      (initialSurvivors (growingRandomValue x) Y targets a) V choice b hb
  exact hcount.trans ((add_le_add hmiss hremaining).trans_eq (by ring))

end Erdos4.FGKMT

import ErdosProblems.Erdos4.FGKMTInitialConfiguration
import ErdosProblems.Erdos4.FGKMTGrowingTargetCounts
import ErdosProblems.Erdos4.FGKMTGrowingPrimeExposure
import ErdosProblems.Erdos4.FGKMTSmallShifts

/-! Unconditional initial configurations at every sufficiently large endpoint, at full FGKMT18 scale. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter Classical ChebyshevIntervals TupleSurvivalBounds

theorem exists_growing_initial_configuration :
    ∃ c A B : ℝ, 0 < c ∧ 0 < A ∧ 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      let Y := growingGapLength c x
      let targets := primeInterval x Y
      ∃ (a : ∀ l : growingRandomPrimes x, ZMod (growingRandomValue x l))
        (V : Finset targets) (ν : growingSourcePrimes x → FiniteLaw (Finset V)),
        V ⊆ initialSurvivors (growingRandomValue x) Y targets a ∧
        (V.card : ℝ) ≤ A * x * (growingIndex x : ℝ) / Real.log (x : ℝ) ∧
        ((initialSurvivors (growingRandomValue x) Y targets a \ V).card : ℝ) ≤
          B * x / Real.log (x : ℝ) ∧
        (∀ v : V, 4 ≤ ∑ p, (ν p).prob (fun e => v ∈ e)) ∧
        (∀ p v, (ν p).prob (fun e => v ∈ e) ≤ (x : ℝ) ^ (-4 / 5 : ℝ)) ∧
        (∀ v w : V, v ≠ w → (∑ p, (ν p).prob (fun e => v ∈ e ∧ w ∈ e)) ≤
          (x : ℝ) ^ (-4 / 5 : ℝ)) ∧
        (∀ p e, 0 < (ν p).weight e → e.card ≤ sieveDimension (growingIndex x) ∧
          ∃ r : ZMod p.val, ∀ q ∈ e, (q.val.val : ZMod p.val) = r) := by
  obtain ⟨a₀, Cbad, d, ha₀, ha₀1, hCbad, hd, hexposure⟩ := exists_growing_prime_exposure
  obtain ⟨cσ, Cσ, hcσ, hCσ, hdensity⟩ := exists_growing_random_density_bounds
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c := d / (4800 * Cσ * Real.log 2)
  let G := d / 24
  let K := 3 * Real.log 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨c, 2 * (K * G + 1), 2 * ((Cbad + K) * G + 1), hc, by positivity, by positivity, ?_⟩
  filter_upwards [hexposure, hdensity, eventually_growing_gap_length_bounds hc,
    eventually_growing_joint_accuracy.{0}, eventually_growing_center_laws,
    eventually_growing_initial_error_budget, eventually_growing_initial_loss_bounds,
    eventually_growing_target_count, eventually_growing_count_budgets,
    eventually_growingIndex_log_bounds, eventually_growing_outer_log_budget,
    eventually_growing_pre_le_radius, eventually_growingRadius_bounds,
    growingDimension_tendsto.eventually exists_small_admissible_shifts,
    eventually_ge_atTop 2]
    with x hexposure hdensity hlength haccuracy hcenters herror hloss htargets hcounts
      hindex hlogs hDR hR hshifts hx
  let Y := growingGapLength c x
  let targets := primeInterval x Y
  let sources := growingSourcePrimes x
  let k := sieveDimension (growingIndex x)
  let j := (growingIndex x : ℝ)
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let s := growingOuterScale x
  let σ := UnitFourier.unitDensity (growingRandomValue x)
  let ε := 1 / L ^ (80 : ℕ)
  let η := 1 / L ^ (40 : ℕ)
  let α := (x : ℝ) ^ (-9 / 10 : ℝ)
  obtain ⟨hY, hXY, hDY, hY2, h3Y, hYhalf, hYupper⟩ := hlength
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hlogs.1
  have hl : 0 ≤ l := le_trans (by norm_num) hlogs.2.1
  have hspos : 0 < s := by
    have hr := Real.sqrt_pos.mpr hLpos
    have hb := hlogs.2.2.2.1
    change Real.sqrt L ≤ s / 100 at hb
    linarith
  have hσpos : 0 < σ := UnitFourier.unitDensity_pos (growingRandomValue x)
  have hj : (1 : ℝ) ≤ j := by
    dsimp only [j]
    exact_mod_cast hcounts.1
  have hk : 1 ≤ k := by unfold k sieveDimension; exact Nat.one_le_two_pow
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by
    apply (div_le_one (pow_pos hLpos 80)).mpr
    exact one_le_pow₀ hlogs.1
  have hη : 0 ≤ η := by positivity
  have hα : 0 ≤ α := Real.rpow_nonneg hxpos.le _
  obtain ⟨h, hinj, hsmall, hadm⟩ := hshifts
  have hksq : k ^ 2 ≤ growingPrecutoff x := by
    have hh : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right hk (by norm_num)
    change k ^ 2 ≤ 16 * k ^ 4
    omega
  have hbound : ∀ i, h i ≤ growingPrecutoff x := fun i => (hsmall i).2.2.trans hksq
  have hsourceStart : growingRadius x ^ 2 ≤ x / 32 := growingRadius_sq_le_source_start hR.1
  have hRpow : growingRadius x ≤ growingRadius x ^ 2 := by nlinarith [hR.1]
  have hsource : ∀ p ∈ sources, p.Prime ∧ growingRadius x < p ∧ p ≤ x := by
    intro p hp
    have hh := mem_growingSourcePrimes.mp hp
    exact ⟨hh.1, (hRpow.trans hsourceStart).trans_lt hh.2.1, hh.2.2⟩
  have hsources : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p := by
    intro p hp
    exact ⟨(hsource p hp).1, fun i => ((hbound i).trans hDR).trans_lt (hsource p hp).2.1⟩
  have hshift : ∀ p ∈ sources, ∀ i, h i * p ≤ Y := by
    intro p hp i
    exact (Nat.mul_le_mul (hbound i) (hsource p hp).2.2).trans hDY
  obtain ⟨B₀, hB₀x, hB₀, hexposure⟩ := hexposure
  let ell₀ := growingSmallPrimeValue x B₀
  let ell₁ := growingLargePrimeValue x B₀
  let b := sieveSlope (growingIndex x) (growingRadius x)
  obtain ⟨bad₀, hbadsub, hbadcard, hgood⟩ := hexposure h hinj hbound hadm Y hY hXY hDY
  let bad := targetBadSubset targets bad₀
  have htarget : ∀ q ∈ targets, 1 ≤ q ∧ q ≤ Y := by
    intro q hq
    have hh := mem_primeInterval.mp hq
    exact ⟨hh.1.one_le, hh.2.2⟩
  have hproduct : σ * (Y : ℝ) ≤ G * (x : ℝ) * j :=
    initial_scale_product hd hCσ hxpos.le hspos hl (Nat.cast_nonneg Y)
      hdensity.2 hYupper hindex.1
  have h24 : 24 * σ ≤ d * j * (x : ℝ) / Y := by
    apply (le_div_iff₀ hYpos).mpr
    dsimp only [G] at hproduct
    nlinarith only [hproduct]
  have hdegree : ∀ q : targets, q ∉ bad → 24 * σ ≤
      rationalSourceIncidence ell₀ ell₁ b (growingRadius x) h hY sources (fun _ => 1) q.val := by
    intro q hq
    have hqbad : q.val ∉ bad₀ := fun hh => hq ((mem_targetBadSubset targets bad₀ q).mpr hh)
    exact h24.trans (hgood q q.property hqbad)
  have hacc : Accurate (growingRandomValue x) (3 * Y) (3 * k) ε :=
    haccuracy (3 * Y) (by omega) h3Y (↥(growingRandomPrimes x)) (growingRandomValue x)
      (growingRandomValue_injective x) (growingRandomValue_above_start x)
  have hZ : ∀ p ∈ sources, 0 < maskedTranslatedNormalizer ell₀ ell₁ b (growingRadius x) h Y p := by
    intro p hp
    exact (hcenters a₀ ha₀1 B₀ hB₀ hB₀x h hinj hbound hadm Y hY hXY p
      (hsource p hp).1 (hsource p hp).2.1).1.1
  have hatom : ∀ p ∈ sources, ∀ n : TranslatedCenter Y,
      (rationalCenterLaw ell₀ ell₁ b (growingRadius x) h hY p).weight n ≤ α := by
    intro p hp
    exact (hcenters a₀ ha₀1 B₀ hB₀ hB₀x h hinj hbound hadm Y hY hXY p
      (hsource p hp).1 (hsource p hp).2.1).2
  have hbudget : ∀ q : targets, q ∉ bad →
      76 * ε + 4 * (k : ℝ) * α /
        (σ ^ (2 * k - 2) * rationalSourceIncidence ell₀ ell₁ b (growingRadius x)
          h hY sources (fun _ => 1) q.val) + 80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1) ≤ η := by
    intro q hq
    exact herror _ (hdegree q hq)
  obtain ⟨a, V, ν, hVS, _, hV, hmiss, hνdegree, hνmarg, hνpair, hνlegal⟩ :=
    exists_rational_initial_configuration (growingRandomValue x) ell₀ ell₁ b (growingRadius x)
      hk h hinj hY sources targets bad htarget hε0 hε1 hη hα hacc hsources hshift hZ hatom hdegree hbudget
  have hbad : (bad.card : ℝ) ≤ Cbad * Y / (L * j ^ 2) := by
    have hh : (bad.card : ℝ) ≤ bad₀.card := by exact_mod_cast targetBadSubset_card_le targets bad₀
    exact hh.trans hbadcard
  have hN : (targets.card : ℝ) ≤ K * Y / L := htargets Y hXY
  have hcount := initial_configuration_count_budget hσpos.le hxpos.le (Nat.cast_nonneg Y)
    hLpos hj hG.le hK.le hCbad.le (Nat.cast_nonneg targets.card) hcounts.2.1 hcounts.2.2 hN hbad hproduct
  refine ⟨a, V, ν, hVS, hV.trans hcount.1, hmiss.trans hcount.2, hνdegree, ?_, ?_, hνlegal⟩
  · intro p v
    exact (hνmarg p v).trans hloss.2
  · intro v w hvw
    exact (hνpair v w hvw).trans hloss.2

end Erdos4.FGKMT

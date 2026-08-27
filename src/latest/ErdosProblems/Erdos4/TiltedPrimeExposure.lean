import ErdosProblems.Erdos4.TiltedPrimeEdges
import ErdosProblems.Erdos4.TiltedPrimeSurvivorLaw
import ErdosProblems.Erdos4.FGKMTGrowingPrimeExposure
import ErdosProblems.Erdos4.FGKMTGrowingTargetCounts
import ErdosProblems.Erdos4.FGKMTSmallShifts

/-! Unconditional prime-edge data at the stronger tilted interval scale. -/

namespace Erdos4.Tilted

open Filter FGKMT

structure PrimeExposureData (c : ℝ) (x : ℕ) (G C : ℝ) where
  law : growingSourcePrimes x → FiniteLaw (Finset (primeTargets c x))
  bad : Finset (primeTargets c x)
  bad_count : (bad.card : ℝ) ≤ C * gapTarget c x /
    (Real.log (x : ℝ) * (growingIndex x : ℝ) ^ (2 : ℕ))
  degree : ∀ v, v ∉ bad → 32 * primeDensity x ≤ vertexDegree law v
  marginal : ∀ p v, (law p).prob (fun E => v ∈ E) ≤
    (sieveDimension (growingIndex x) : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ)
  pair_degree : ∀ v w, v ≠ w → pairDegree law v w ≤
    (sieveDimension (growingIndex x) : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ)
  legal : ∀ p E, 0 < (law p).weight E → E.card ≤ sieveDimension (growingIndex x) ∧
    ∃ b : ZMod p.val, ∀ v ∈ E, (v.val : ZMod p.val) = b
  density_target : primeDensity x * (gapTarget c x : ℝ) ≤ G * x * (growingIndex x : ℝ)

theorem exists_primeExposureData {G : ℝ} (hG : 0 < G) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℕ in atTop, Nonempty (PrimeExposureData c x G C) := by
  classical
  obtain ⟨a₀, Cbad, d, ha₀, ha₀1, hCbad, hd, hexposure⟩ := exists_growing_prime_exposure
  obtain ⟨cσ, Cσ, _, hCσ, hdensity⟩ := exists_primeDensity_bounds
  let d₀ := min d (48 * G)
  have hd₀ : 0 < d₀ := lt_min hd (by positivity)
  let c := (d₀ / 2) / (4800 * Cσ * Real.log 2)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, Cbad, hc, hCbad, ?_⟩
  filter_upwards [hexposure, hdensity, eventually_gapTarget_bounds hc,
    eventually_growing_center_laws, eventually_growingIndex_log_bounds,
    eventually_growing_pre_le_radius, eventually_growingRadius_bounds,
    growingDimension_tendsto.eventually exists_small_admissible_shifts,
    eventually_outerScale_bounds, eventually_ge_atTop 2]
    with x hexposure hdensity hY hcenters hindex hDR hR hshifts hb hx
  let Y := gapTarget c x
  let targets := primeTargets c x
  let sources := growingSourcePrimes x
  let k := sieveDimension (growingIndex x)
  let j := (growingIndex x : ℝ)
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let s := outerScale x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY.1
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have htpos : 0 < tiltScale x := by linarith [hb.2.2.1]
  have hspos : 0 < s := div_pos hLpos htpos
  have hl : 0 ≤ l := by have hh := hb.2.1; change 1 ≤ l at hh; linarith
  have hAupper : primeDensity x ≤ Cσ * l / s := by
    apply hdensity.2.trans_eq
    dsimp [s, outerScale, l, L]
    field_simp
  have hproduct : primeDensity x * (Y : ℝ) ≤ (d₀ / 48) * (x : ℝ) * j := by
    have hh := initial_scale_product (by positivity : 0 < d₀ / 2) hCσ hxpos.le hspos hl
      (Nat.cast_nonneg Y) hAupper hY.2.2.2.2.2.2.1 hindex.1
    exact hh.trans_eq (by dsimp [j]; ring)
  have h48 : 48 * primeDensity x ≤ d₀ * j * (x : ℝ) / Y := by
    apply (le_div_iff₀ hYpos).mpr
    nlinarith only [hproduct]
  have hk : 1 ≤ k := Nat.one_le_two_pow
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
    exact (Nat.mul_le_mul (hbound i) (hsource p hp).2.2).trans hY.2.2.1
  obtain ⟨B₀, hB₀x, hB₀, hexposure⟩ := hexposure
  let ell₀ := growingSmallPrimeValue x B₀
  let ell₁ := growingLargePrimeValue x B₀
  let b := sieveSlope (growingIndex x) (growingRadius x)
  let centers := fun p => rationalCenterLaw ell₀ ell₁ b (growingRadius x) h hY.1 p
  let laws := fun p : sources => baseTargetEdgeLaw h p.val targets (centers p.val)
  obtain ⟨bad₀, _, hbadcard, hgood⟩ := hexposure h hinj hbound hadm Y hY.1 hY.2.1 hY.2.2.1
  let bad := targetBadSubset targets bad₀
  have htarget : ∀ q : targets, 1 ≤ q.val ∧ q.val ≤ Y := by
    intro q
    have hh := primeTargets_properties q.property
    exact ⟨hh.1.one_le, hh.2.2⟩
  have hatom : ∀ p ∈ sources, ∀ n : TranslatedCenter Y,
      (centers p).weight n ≤ (x : ℝ) ^ (-9 / 10 : ℝ) := by
    intro p hp
    exact (hcenters a₀ ha₀1 B₀ hB₀ hB₀x h hinj hbound hadm Y hY.1 hY.2.1 p
      (hsource p hp).1 (hsource p hp).2.1).2
  have hmarg : ∀ p ∈ sources, ∀ q : targets,
      (baseTargetEdgeLaw h p targets (centers p)).prob (fun E => q ∈ E) ≤
        (k : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ) := by
    intro p hp q
    exact baseTargetEdgeLaw_marginal_le h hinj targets (centers p) (hsource p hp).1.pos
      (hshift p hp) q (htarget q).1 (htarget q).2 (hatom p hp)
  refine ⟨⟨laws, bad, ?_, ?_, (fun p => hmarg p p.property), ?_, ?_, ?_⟩⟩
  · exact (Nat.cast_le.mpr (targetBadSubset_card_le targets bad₀)).trans hbadcard
  · intro q hq
    rw [rational_baseTarget_degree ell₀ ell₁ b (growingRadius x) h hY.1 sources targets q (htarget q).1 (htarget q).2]
    have hqbad : q.val ∉ bad₀ := fun hh => hq ((mem_targetBadSubset targets bad₀ q).mpr hh)
    calc
      _ ≤ 48 * primeDensity x := by nlinarith [primeDensity_pos x]
      _ ≤ d₀ * j * (x : ℝ) / Y := h48
      _ ≤ d * j * (x : ℝ) / Y := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left d (48 * G)) (Nat.cast_nonneg _)) hxpos.le)
        hYpos.le
      _ ≤ _ := hgood q.val q.property hqbad
  · exact baseTargetEdgeLaw_pair_sum_le h hinj sources targets centers hsources (by positivity) hmarg
  · intro p E hE
    exact ⟨baseTargetEdgeLaw_card_le h p.val targets (centers p.val) E hE,
      baseTargetEdgeLaw_residue h p.val targets (centers p.val) E hE⟩
  · apply hproduct.trans
    have hcoef : d₀ / 48 ≤ G := (div_le_iff₀ (by norm_num : (0 : ℝ) < 48)).mpr
      (by dsimp [d₀]; linarith [min_le_right d (48 * G)])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hxpos.le) (Nat.cast_nonneg _)

end Erdos4.Tilted

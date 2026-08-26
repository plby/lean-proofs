import ErdosProblems.Erdos747.AggregateSurvivalParameters

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def thinningBlockSize (K : ℕ) (eta : ℝ) : ℕ := ⌊eta * K / 8⌋₊

def thinningExceptionCount (t : ℕ) (eta : ℝ) : ℕ := ⌊eta * t / 100⌋₊

lemma thinningBlockSize_bounds (K : ℕ) (eta : ℝ)
    (heta : 0 ≤ eta) (hlarge : 16 ≤ eta * K) :
    eta * K / 16 ≤ thinningBlockSize K eta ∧
      (thinningBlockSize K eta : ℝ) ≤ eta * K / 8 := by
  have hf : (thinningBlockSize K eta : ℝ) ≤ eta * K / 8 := Nat.floor_le (by positivity)
  have hlt : eta * K / 8 < (thinningBlockSize K eta : ℝ) + 1 := Nat.lt_floor_add_one _
  exact ⟨by linarith only [hlt, hlarge], hf⟩

lemma thinningExceptionCount_le (t : ℕ) (eta : ℝ) (heta : 0 ≤ eta) :
    (thinningExceptionCount t eta : ℝ) ≤ eta * t / 100 := Nat.floor_le (by positivity)

lemma thinningExceptionCount_ratio_le (t : ℕ) (eta : ℝ) (heta : 0 < eta) :
    (t : ℝ) / ((thinningExceptionCount t eta + 1 : ℕ) : ℝ) ≤ 100 / eta := by
  have he : eta * t / 100 < (thinningExceptionCount t eta : ℝ) + 1 := Nat.lt_floor_add_one _
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((thinningExceptionCount t eta + 1 : ℕ) : ℝ)) heta).mpr
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith only [he]

lemma thinningExceptionCount_scaled_ratio_le (t : ℕ) (eta x : ℝ)
    (heta : 0 < eta) (hx : 0 ≤ x) :
    (t : ℝ) * x / ((thinningExceptionCount t eta + 1 : ℕ) : ℝ) ≤ 100 * x / eta := by
  have h := mul_le_mul_of_nonneg_right (thinningExceptionCount_ratio_le t eta heta) hx
  calc
    _ = ((t : ℝ) / ((thinningExceptionCount t eta + 1 : ℕ) : ℝ)) * x := by ring
    _ ≤ (100 / eta) * x := h
    _ = _ := by ring

lemma thinning_diagnostic_exception_budget (K S t : ℕ) (eta : ℝ)
    (heta : 0 ≤ eta) (hlarge : 16 ≤ eta * K) (hS : 0 < S) (hSK : S ≤ K) :
    (2 : ℝ) * thinningExceptionCount t eta ≤
      (3 / 4 : ℝ) * t * ((thinningBlockSize K eta : ℝ) / S) := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hKR : (0 : ℝ) < K := by exact_mod_cast (hS.trans_le hSK)
  have hd := (thinningBlockSize_bounds K eta heta hlarge).1
  have hdratio : eta / 16 ≤ (thinningBlockSize K eta : ℝ) / S := by
    apply (le_div_iff₀ hSR).mpr
    have hSKR : (S : ℝ) ≤ K := by exact_mod_cast hSK
    have h := mul_le_mul_of_nonneg_left hSKR heta
    linarith only [h, hd]
  have he := thinningExceptionCount_le t eta heta
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hdratio (show 0 ≤ (3 / 4 : ℝ) * t by positivity)
  have hetaT : 0 ≤ eta * t := mul_nonneg heta ht0
  nlinarith only [he, hscaled, hetaT]

lemma thinning_global_budget (K M : ℕ) (eta alpha : ℝ)
    (heta : 0 ≤ eta) (hlarge : 16 ≤ eta * K) (hM : M ≤ K)
    (halpha : 0 ≤ alpha) (hsmall : alpha ≤ eta / 2) :
    ((2 * thinningBlockSize K eta : ℕ) : ℝ) + alpha * M ≤ eta * K := by
  have hd := (thinningBlockSize_bounds K eta heta hlarge).2
  have hMK : (M : ℝ) ≤ K := by exact_mod_cast hM
  have hterm : alpha * M ≤ (eta / 2) * K := mul_le_mul hsmall hMK (by positivity) (by positivity)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hKeta : 0 ≤ eta * K := by positivity
  nlinarith only [hd, hterm, hKeta]

lemma thinning_bottom_card_pos_of_sample
    {n t : ℕ} {H U : Finset (Edge n)} (hH : H ⊆ allEdges n)
    (hU : U ∈ H.powersetCard t) (ht : 0 < t) :
    0 < (allEdges n \ (H \ U)).card := by
  have hsub : U ⊆ allEdges n \ (H \ U) := by
    intro Z hZU
    exact Finset.mem_sdiff.mpr ⟨hH ((Finset.mem_powersetCard.mp hU).1 hZU),
      fun h ↦ (Finset.mem_sdiff.mp h).2 hZU⟩
  have hcard : U.card = t := (Finset.mem_powersetCard.mp hU).2
  exact (show 0 < U.card by omega).trans_le (Finset.card_le_card hsub)

lemma collision_bound_erase_of_succ {n k : ℕ} {H : Finset (Edge n)} {Z : Edge n}
    (hZ : Z ∈ H) (hcollision : 4 * (k + 1) * (k + 1) ≤ H.card) :
    4 * k * k ≤ (H.erase Z).card := by
  have hcard := Finset.card_erase_add_one hZ
  nlinarith only [hcollision, hcard]

end

end Erdos747

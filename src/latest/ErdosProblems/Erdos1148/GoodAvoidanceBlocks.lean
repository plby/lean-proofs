import ErdosProblems.Erdos1148.OrbitBlockPatterns
import ErdosProblems.Erdos1148.OrbitAvoidanceShift
import ErdosProblems.Erdos1148.ModularTimeOne

/-! # Most mass has few exceptional blocks while avoiding a null open set -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter

def halfBadPatterns (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range k).powerset.filter (fun p => 2 * p.card ≤ k)

lemma mem_halfBadPatterns (k : ℕ) (p : Finset ℕ) :
    p ∈ halfBadPatterns k ↔ p ⊆ Finset.range k ∧ 2 * p.card ≤ k := by
  simp only [halfBadPatterns, Finset.mem_filter, Finset.mem_powerset]

lemma halfBadPatterns_card_le (k : ℕ) : (halfBadPatterns k).card ≤ 2 ^ k :=
  (Finset.card_filter_le _ _).trans_eq (by simp only [Finset.card_powerset, Finset.card_range])

noncomputable def goodAvoidanceBlocks (K U : Set ModularOrbitSpace) (n k : ℕ) : Set ModularOrbitSpace :=
  finiteOrbitAvoidance modularTimeOne U (k * n) ∩
    {x | 2 * (orbitBlockPattern modularTimeOne Kᶜ n k x).card ≤ k}

lemma mem_goodAvoidanceBlocks_iff (K U : Set ModularOrbitSpace) (n k : ℕ) (x : ModularOrbitSpace) :
    x ∈ goodAvoidanceBlocks K U n k ↔ x ∈ finiteOrbitAvoidance modularTimeOne U (k * n) ∧
      orbitVisitCount (modularTimeOne^[n]) Kᶜ k x ≤ (k : ℝ) / 2 := by
  change (_ ∧ _) ↔ _ ∧ _
  apply and_congr_right
  intro _
  change 2 * (orbitBlockPattern modularTimeOne Kᶜ n k x).card ≤ k ↔ _
  rw [orbitBlockPattern_card]
  change 2 * (orbitVisitPattern (modularTimeOne^[n]) Kᶜ k x).card ≤ k ↔
    ((orbitVisitPattern (modularTimeOne^[n]) Kᶜ k x).card : ℝ) ≤ (k : ℝ) / 2
  constructor
  · intro h
    have hR : 2 * ((orbitVisitPattern (modularTimeOne^[n]) Kᶜ k x).card : ℝ) ≤ k := by exact_mod_cast h
    linarith only [hR]
  · intro h
    have hR : 2 * ((orbitVisitPattern (modularTimeOne^[n]) Kᶜ k x).card : ℝ) ≤ k := by linarith only [h]
    exact_mod_cast hR

theorem goodAvoidanceBlocks_mass_lower (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ) {K U : Set ModularOrbitSpace}
    (hK : MeasurableSet K) (hU : μ U = 0) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    1 - 2 * μ.real Kᶜ ≤ μ.real (goodAvoidanceBlocks K U n k) := by
  have hae : goodAvoidanceBlocks K U n k =ᵐ[μ]
      {x | orbitVisitCount (modularTimeOne^[n]) Kᶜ k x ≤ (k : ℝ) / 2} := by
    filter_upwards [ae_finiteOrbitAvoidance_of_null hf hU (k * n)] with x hx
    apply propext
    change x ∈ goodAvoidanceBlocks K U n k ↔ orbitVisitCount (modularTimeOne^[n]) Kᶜ k x ≤ (k : ℝ) / 2
    simpa only [hx, true_and] using mem_goodAvoidanceBlocks_iff K U n k x
  have hbound := orbitVisitCount_below_mass_lower (hf.iterate n) hK.compl
    (by norm_num : (0 : ℝ) < 1 / 2) hk
  have heq : μ.real (goodAvoidanceBlocks K U n k) =
      μ.real {x | orbitVisitCount (modularTimeOne^[n]) Kᶜ k x ≤ (k : ℝ) / 2} :=
    congrArg ENNReal.toReal (measure_congr hae)
  rw [heq]
  have ht : (1 / 2 : ℝ) * (k : ℝ) = (k : ℝ) / 2 := by ring
  have hc : μ.real Kᶜ / (1 / 2 : ℝ) = 2 * μ.real Kᶜ := by ring
  simpa only [ht, hc] using hbound

end Erdos1148.DukeArithmetic

/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeStateConsequences
import ErdosProblems.Erdos207.KSSSTrajectories

/-! # Vertex-order indexing and the closed-threat diagonal correction -/

namespace Erdos207

open Finset

noncomputable section

def ksssOrders (q : ℕ) : Finset ℕ := Icc 1 (q - 3)

theorem sum_vertexOrder_eq_sum_ksssOrders (q : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Icc 4 q, f (j - 3)) = ∑ d ∈ ksssOrders q, f d := by
  apply sum_bij (fun j _ ↦ j - 3)
  · intro j hj
    simp only [mem_Icc] at hj
    simp only [ksssOrders, mem_Icc]
    omega
  · intro j hj k hk he
    simp only [mem_Icc] at hj hk
    omega
  · intro d hd
    simp only [ksssOrders, mem_Icc] at hd
    refine ⟨d + 3, ?_, by omega⟩
    simp only [mem_Icc]
    omega
  · intro j hj
    rfl

theorem ksssThreatTrajectory_vertexOrders
    (q : ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) :
    ksssThreatTrajectory (ksssOrders q) a E₀ A₀ t =
      3 * ksssPairTrajectory (ksssOrders q) a E₀ A₀ t +
        ∑ j ∈ Icc 4 q,
          ksssConfigurationTrajectory (ksssOrders q) a E₀ A₀ (j - 3) (j - 4) t := by
  rw [ksssThreatTrajectory]
  congr 1
  rw [← sum_vertexOrder_eq_sum_ksssOrders]
  apply sum_congr rfl
  intro j hj
  have he : j - 3 - 1 = j - 4 := by omega
  rw [he]

theorem CrudeStateBounds.ksss_threat_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {K : CrudeThresholds}
    (h : CrudeStateBounds F S q K)
    (hS : GreedyInvariant F S) (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q)
    (a : ℕ → ℝ) (E₀ A₀ t e : ℝ) (he : 2 ≤ e) (hcommon : (K.common : ℝ) ≤ e)
    {T : TripleOn V} (hT : T ∈ S.available)
    (hpair : ∀ P ∈ T.1.powersetCard 2,
      |((availableTrianglesContainingPair S P).card : ℝ) -
        ksssPairTrajectory (ksssOrders q) a E₀ A₀ t| ≤ e)
    (hterminal : ∀ j ∈ Icc 4 q,
      |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ) -
        ksssConfigurationTrajectory (ksssOrders q) a E₀ A₀ (j - 3) (j - 4) t| ≤ e) :
    |((greedyClosedThreats F S T).card : ℝ) -
      ksssThreatTrajectory (ksssOrders q) a E₀ A₀ t| ≤ ((q : ℝ) + 5) * e := by
  let H := ksssThreatTrajectory (ksssOrders q) a E₀ A₀ t
  have hcount := h.threat_trajectory hS hpack hcard hT
    (ksssPairTrajectory (ksssOrders q) a E₀ A₀ t) e
    (fun j ↦ ksssConfigurationTrajectory (ksssOrders q) a E₀ A₀ (j - 3) (j - 4) t)
    (fun _ ↦ e) hpair hterminal
  rw [← ksssThreatTrajectory_vertexOrders, sum_const, nsmul_eq_mul] at hcount
  change |((greedyClosedThreats F S T).card : ℝ) - (H - 2)| ≤
    (K.common : ℝ) + 3 * e + (Icc 4 q).card * e at hcount
  have hsize : (Icc 4 q).card ≤ q := by rw [Nat.card_Icc]; omega
  have hsizer : ((Icc 4 q).card : ℝ) ≤ q := by exact_mod_cast hsize
  have hs := mul_le_mul_of_nonneg_right hsizer (by linarith : 0 ≤ e)
  have htri := abs_sub_le ((greedyClosedThreats F S T).card : ℝ) (H - 2) H
  have htwo : |H - 2 - H| = 2 := by ring_nf; norm_num
  rw [htwo] at htri
  change |((greedyClosedThreats F S T).card : ℝ) - H| ≤ _
  nlinarith only [hcount, htri, hs, hcommon, he]

end

end Erdos207

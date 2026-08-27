/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreparedLocalDegreeLaw
import ErdosProblems.Erdos207.EventualFixedRandomAllOrders
import ErdosProblems.Erdos207.KSSSPowerExponentChoice

/-! # Instantiate fixed-envelope regularization on the prepared auxiliary triangle families -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem ksss_power_regularization_gaps (q b B k Rmin : ℕ) :
    let R := ksssPowerDenominatorExponent q b B k Rmin
    3 * b + 2 ≤ R ∧ 3 * b * (q - 3) + 1 ≤ R ∧ 6 ≤ R := by
  have hm := Nat.mul_le_mul_left (3 * b) (Nat.sub_le q 3)
  dsimp only [ksssPowerDenominatorExponent, ksssPowerThetaExponent,
    ksssPowerJumpExponent, ksssPowerVarianceExponent, ksssPowerMarginExponent,
    ksssPowerErrorExponent, ksssPowerDeterministicExponent, ksssPowerRawVarianceExponent]
  omega

theorem eventually_regularize_prepared_auxiliary_inputs
    (q b B k Rmin ambientPower decay : ℕ) (massConstant : ℝ≥0) (hmassConstant : 0 < massConstant) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V] {ell : ℕ},
      ∀ (P : FiniteLaw Omega) (W : Vortex V ell) (current : Fin (ell + 1))
        (available old : Omega → TripleSystemOn V) [∀ omega, Nonempty {T // T ∈ available omega}],
      ∀ (F : ℕ → ForbiddenFamilyOn V) (p : ℝ≥0) (y z : ℕ → ℝ≥0),
      (∀ omega T, T ∈ available omega → T.1 ⊆ W.U current) →
      (∀ j ∈ Icc 4 q, SourceVortexWellSpread (W.prefix current) j (F j) (y j) (z j)) →
      t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ (W.U current).card →
      Fintype.card V ≤ t ^ ambientPower →
      1 / (t : ℝ≥0) ^ b ≤ p → p ≤ 1 / t →
      (∀ j ∈ Icc 4 q, y j ≤ t) →
      (∀ j ∈ Icc 4 q, (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient current.val j' 2 * y j') ≤ t) →
      (∀ omega, p ^ 3 * ((W.U current).card : ℝ≥0) ^ 3 / massConstant ≤ (available omega).card) →
      (∀ omega, sourceAuxiliaryDegreeGood W current q t F available old p y omega) →
      ∃ Lstar : ℕ → (omega : Omega) → Finset (Finset {T // T ∈ available omega}),
      ∃ envelope : ℕ → ForbiddenFamilyOn V,
        (∀ j ∈ Icc 4 q,
          FixedRandomOrderResult P (W.prefix current)
            (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega)) j (8192 * t)
            (fun omega ↦ finiteHypergraphOnSubset (available omega)
              (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) j))
            (fun omega ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i omega)) (F j)
            (terminalRandomConfigurations (W.prefix current) j)
            (y j) (z j) ((t : ℝ≥0) ^ 4) (1 / (t : ℝ≥0) ^ decay) (Lstar j) (envelope j)) ∧
        P.probability (fun omega ↦ ∃ j ∈ Icc 4 q, 8192 * t < finiteHypergraphDegreeGap (Lstar j omega)) ≤
          ((Icc 4 q).card : ℝ≥0) / (t : ℝ≥0) ^ decay := by
  classical
  let den := ksssPowerDenominatorExponent q b B k Rmin
  have hgaps := ksss_power_regularization_gaps q b B k Rmin
  obtain ⟨T, hT1, hT⟩ := eventually_exists_fixed_random_all_orders q 2 1 3 4 3 (3 * b) den
    ambientPower decay massConstant hmassConstant (by norm_num) (by norm_num) (by norm_num)
    hgaps.1 hgaps.2.1 hgaps.2.2 (by omega)
  refine ⟨T, hT1, ?_⟩
  intro t ht Omega V _ _ _ _ ell P W current available old _ F p y z hsupport hsource hscale hN
    hpLo hpHi hy hcoeff hmass hdegree
  let I := fun omega ↦ {T // T ∈ available omega}
  let e := fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ available omega)
  let localFamily := fun j omega ↦ finiteHypergraphOnSubset (available omega)
    (localForbiddenConfigurations ((Icc 4 q).biUnion F) (available omega) (old omega) j)
  let coeff := fun j ↦ (t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient current.val j' 2 * y j'
  have hlow : 1 / (t : ℝ≥0) ^ (3 * b) ≤ p ^ 3 := by
    simpa only [div_pow, one_pow, ← pow_mul, Nat.mul_comm b 3] using pow_le_pow_left' hpLo 3
  have hhi : p ^ 3 ≤ 1 / (t : ℝ≥0) ^ 3 := by simpa only [div_pow, one_pow] using pow_le_pow_left' hpHi 3
  have hcoeffBound : ∀ j ∈ Icc 4 q, coeff j ≤ (t : ℝ≥0) ^ 2 := by
    intro j hj
    simpa only [coeff, pow_two] using mul_le_mul_of_nonneg_left (hcoeff j hj)
      (show 0 ≤ (t : ℝ≥0) from zero_le)
  apply hT t ht P (W.prefix current) e
    (fun omega T ↦ by
      simpa only [e, Function.Embedding.subtype_apply, Vortex.prefix_U, vortexPrefixEmbedding_last] using
        hsupport omega T.val T.property) localFamily F (terminalRandomConfigurations (W.prefix current)) y z
    (fun j _ ↦ coeff j) (fun _ ↦ p ^ 3)
  · intro j _ omega
    exact localForbiddenAuxiliary_uniform ((Icc 4 q).biUnion F) (available omega) (old omega) j
  · exact hsource
  · exact hscale
  · exact hN
  · exact fun _ ↦ hlow
  · exact fun _ ↦ hhi
  · exact fun j hj _ ↦ hcoeffBound j hj
  · simpa only [pow_one] using hy
  · intro omega
    simpa only [Fintype.card_coe, Vortex.prefix_terminalSize] using hmass omega
  · intro j hj omega
    exact hdegree omega j hj
  · exact fun _ _ ↦ subset_rfl
  · exact fun _ _ _ _ _ hE ↦ hE

end

end Erdos207

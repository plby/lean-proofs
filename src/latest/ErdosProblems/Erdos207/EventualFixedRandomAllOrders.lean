/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualRegularizationAllInputs
import ErdosProblems.Erdos207.FixedRandomAllOrders
import ErdosProblems.Erdos207.FixedRandomRegularizationPower

/-! # Actual fixed envelopes at every order with a prescribed polynomial failure -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_exists_fixed_random_all_orders
    (q K Y D A v w L R decay : ℕ) (constant : ℝ≥0) (hconstant : 0 < constant)
    (hD : K + 1 ≤ D) (hA : D + 1 ≤ A) (hv : K + 1 ≤ v)
    (hLmass : w + 2 ≤ L) (hLdensity : w * (q - 3) + 1 ≤ L)
    (hLsquare : 2 * D ≤ L) (hLy : D + Y ≤ L) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
        {I : Omega → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
        {ell : ℕ},
      ∀ (P : FiniteLaw Omega) (W : Vortex V ell) (e : (d : Omega) → I d ↪ TripleOn V),
      (∀ d i, (e d i).1 ⊆ W.U (Fin.last ell)) →
      ∀ (localFamily : ℕ → (d : Omega) → Finset (Finset (I d)))
        (F candidates : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0)
        (B : ℕ → Omega → ℝ≥0) (sigma : Omega → ℝ≥0),
      (∀ j ∈ Icc 4 q, ∀ d E, E ∈ localFamily j d → E.card = j - 2) →
      (∀ j ∈ Icc 4 q, SourceVortexWellSpread W j (F j) (y j) (z j)) →
      t ^ L ≤ W.terminalSize → Fintype.card V ≤ t ^ R →
      (∀ d, 1 / (t : ℝ≥0) ^ w ≤ sigma d) → (∀ d, sigma d ≤ 1 / (t : ℝ≥0) ^ v) →
      (∀ j ∈ Icc 4 q, ∀ d, B j d ≤ (t : ℝ≥0) ^ K) →
      (∀ j ∈ Icc 4 q, y j ≤ (t : ℝ≥0) ^ Y) →
      (∀ d, sigma d * (W.terminalSize : ℝ≥0) ^ 3 / constant ≤ Fintype.card (I d)) →
      (∀ j ∈ Icc 4 q, ∀ d, (finiteHypergraphMaxDegree (localFamily j d) : ℝ≥0) ≤
        B j d * sigma d ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3)) →
      (∀ j ∈ Icc 4 q, candidates j ⊆ terminalRandomConfigurations W j) →
      (∀ j ∈ Icc 4 q, ∀ d (E : Finset (I d)), E.card = j - 2 →
        E.map (e d) ∈ terminalRandomConfigurations W j → E.map (e d) ∈ candidates j) →
      ∃ Lstar : ℕ → (d : Omega) → Finset (Finset (I d)), ∃ envelope : ℕ → ForbiddenFamilyOn V,
        (∀ j ∈ Icc 4 q, FixedRandomOrderResult P W e j (8192 * t) (localFamily j)
          (fun d ↦ (Ico 4 j).biUnion (fun i ↦ Lstar i d)) (F j) (candidates j)
          (y j) (z j) ((t : ℝ≥0) ^ A) (1 / (t : ℝ≥0) ^ decay) (Lstar j) (envelope j)) ∧
        P.probability (fun d ↦ ∃ j ∈ Icc 4 q, 8192 * t < finiteHypergraphDegreeGap (Lstar j d)) ≤
          ((Icc 4 q).card : ℝ≥0) / (t : ℝ≥0) ^ decay := by
  classical
  obtain ⟨TI, hTI1, hTI⟩ := eventually_sourceRegularizationAllInputs q K Y D A v w L R constant
    hconstant hD hA hv hLmass hLdensity hLsquare hLy
  let Orders := {j : ℕ // j ∈ Icc 4 q}
  let : Fintype Orders := by dsimp only [Orders]; infer_instance
  have hsingle (j : Orders) := eventually_fixedRandomRegularization_power_budget j.val R decay
    (mem_Icc.mp j.property).1
  let threshold : Orders → ℕ := fun j ↦ (hsingle j).choose
  let T := max TI (univ.sup threshold)
  refine ⟨T, hTI1.trans (le_max_left _ _), ?_⟩
  intro t ht Omega V _ _ _ _ I _ _ _ ell P W e hsupport localFamily F candidates y z B sigma
    huniform hspread hn hN hsigmaLo hsigmaHi hB hy hmass hdegree hC hgeometry
  have htI : TI ≤ t := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ t := hTI1.trans htI
  have hdata (d : Omega) := hTI t htI W (e d) (hsupport d)
    (fun j ↦ localFamily j d) F y z (fun j ↦ B j d) (sigma d)
    (fun j hj ↦ huniform j hj d) hspread hn hN (hsigmaLo d) (hsigmaHi d)
    (fun j hj ↦ hB j hj d) hy (hmass d) (fun j hj ↦ hdegree j hj d)
  obtain ⟨d0, _⟩ := P.exists_mass_pos
  have hq : q ≤ W.terminalSize := (hdata d0).1
  have hinputs : ∀ j ∈ Icc 4 q, ∀ d, SourceRegularizationOrderInput W j (localFamily j d) (F j)
      (8192 * t) t (y j) (z j) ((t : ℝ≥0) ^ A) ((t : ℝ≥0) ^ D) (sigma d) constant (B j d) :=
    fun j hj d ↦ (hdata d).2 j hj
  have hrho : ∀ _j ∈ Icc 4 q, 0 < (1 / (t : ℝ≥0) ^ decay) := by
    intro _ _
    have ht0 : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by omega)
    positivity
  have hepsilon : ∀ j ∈ Icc 4 q, ∀ d,
      (finiteHypergraphMaxDegree (localFamily j d) : ℝ) *
        (2 * Fintype.card (I d) * Real.exp (-((8192 * t : ℕ) : ℝ) / 8192)) ≤
          regularizationGapPowerError j R t := by
    intro j hj d
    have hmax := (hinputs j hj d).maximum_power
    exact regularization_gap_failure_power_bound t W.terminalSize (Fintype.card (I d))
      (finiteHypergraphMaxDegree (localFamily j d)) j R (mem_Icc.mp hj).1
      ((card_le_univ _).trans hN) (card_auxiliary_triangles_le (e d) (W.U (Fin.last ell))
        (hsupport d)) (by omega)
  have hbudget : ∀ j ∈ Icc 4 q,
      (sourceRandomFailureCoefficient W j : ℝ≥0) * ((2 : ℝ≥0) ^ t)⁻¹ +
        regularizationGapPowerError j R t / (1 / (t : ℝ≥0) ^ decay) < 1 := by
    intro j hj
    let jj : Orders := ⟨j, hj⟩
    have htj : threshold jj ≤ t := (le_sup (f := threshold) (mem_univ jj)).trans
      ((le_max_right _ _).trans ht)
    exact (hsingle jj).choose_spec.2 t htj W hN
  obtain ⟨Lstar, envelope, hresult⟩ := exists_fixed_random_all_orders P W e hsupport q hq localFamily F
    candidates (fun _ ↦ 8192 * t) (fun _ ↦ t) y z (fun _ ↦ (t : ℝ≥0) ^ A)
    (fun _ ↦ (t : ℝ≥0) ^ D) (fun j ↦ regularizationGapPowerError j R t)
    (fun _ ↦ 1 / (t : ℝ≥0) ^ decay) (fun _ d ↦ sigma d) (fun _ _ ↦ constant) B
    hinputs hC hgeometry hrho hepsilon hbudget
  refine ⟨Lstar, envelope, hresult, ?_⟩
  have hfail := fixedRandomAllOrders_gap_failure P W e q (fun _ ↦ 8192 * t) localFamily Lstar F
    candidates envelope y z (fun _ ↦ (t : ℝ≥0) ^ A) (fun _ ↦ 1 / (t : ℝ≥0) ^ decay) hresult
  simpa only [sum_const, nsmul_eq_mul, mul_one_div] using hfail

end

end Erdos207

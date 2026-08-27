/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightSystem
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Relative extension weights from joint-inclusion estimates

If a random selected family has product-form joint-inclusion upper bounds,
then deleting that family from a configuration changes a point weight `σ`
to the sum of the old inclusion weight and `σ`.  This is the finite
binomial expansion underlying the relative rooted-weight estimate in the
master iteration.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- All roots which occur inside at least one member of a finite indexed
configuration family. -/
noncomputable def configurationRoots
    {W I : Type*} [Fintype I] [DecidableEq W]
    (F : I → Finset W) : Finset (Finset W) := by
  classical
  exact (univ : Finset I).biUnion fun i ↦ (F i).powerset

lemma mem_configurationRoots_iff
    {W I : Type*} [Fintype I] [DecidableEq W]
    {F : I → Finset W} {A : Finset W} :
    A ∈ configurationRoots F ↔ ∃ i : I, A ⊆ F i := by
  classical
  simp [configurationRoots]

/-- A non-occurring root has zero extension weight. -/
lemma extensionWeight_eq_zero_of_not_mem_configurationRoots
    {W I : Type*} [Fintype I] [DecidableEq W]
    (F : I → Finset W) (pi : W → ℝ≥0) {A : Finset W}
    (hA : A ∉ configurationRoots F) :
    extensionWeight F pi A = 0 := by
  classical
  unfold extensionWeight
  apply sum_eq_zero
  intro i _hi
  rw [if_neg]
  intro hAF
  exact hA (mem_configurationRoots_iff.mpr ⟨i, hAF⟩)

/-- The weight left outside `P` is bounded by summing over all possible
subsets of `U` which may already lie in `P`. -/
lemma setWeight_sdiff_le_powerset_selected
    {W : Type*} [DecidableEq W]
    (sigma : W → ℝ≥0) (U P : Finset W) :
    setWeight sigma (U \ P) ≤
      ∑ S ∈ U.powerset,
        if S ⊆ P then setWeight sigma (U \ S) else 0 := by
  classical
  let S := U ∩ P
  have hSU : S ∈ U.powerset := mem_powerset.mpr inter_subset_left
  have hSP : S ⊆ P := inter_subset_right
  have heq : U \ S = U \ P := by
    ext x
    simp [S]
  have hsingle :
      (if S ⊆ P then setWeight sigma (U \ S) else 0) ≤
        ∑ T ∈ U.powerset,
          if T ⊆ P then setWeight sigma (U \ T) else 0 := by
    refine single_le_sum
      (s := U.powerset)
      (f := fun T ↦ if T ⊆ P then setWeight sigma (U \ T) else 0)
      ?_ hSU
    intro T _hT
    split_ifs <;> exact zero_le
  simpa only [if_pos hSP, heq] using hsingle

/-- Expected residual point weight under an arbitrary finite law. -/
theorem expected_setWeight_sdiff_le_of_joint
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (L : FiniteLaw Ω) (selected : Ω → Finset W)
    (pi sigma : W → ℝ≥0) (C : ℝ≥0) (U : Finset W)
    (hjoint : ∀ S : Finset W, S ⊆ U →
      L.probability (fun ω ↦ S ⊆ selected ω) ≤ C * setWeight pi S) :
    L.expectation (fun ω ↦ setWeight sigma (U \ selected ω)) ≤
      C * setWeight (fun x ↦ pi x + sigma x) U := by
  classical
  calc
    L.expectation (fun ω ↦ setWeight sigma (U \ selected ω)) ≤
        L.expectation (fun ω ↦
          ∑ S ∈ U.powerset,
            if S ⊆ selected ω then setWeight sigma (U \ S) else 0) := by
      apply L.expectation_mono
      intro ω
      exact setWeight_sdiff_le_powerset_selected sigma U (selected ω)
    _ = ∑ S ∈ U.powerset,
        L.probability (fun ω ↦ S ⊆ selected ω) *
          setWeight sigma (U \ S) := by
      unfold FiniteLaw.expectation FiniteLaw.probability
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro S _hS
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro ω _hω
      by_cases hSω : S ⊆ selected ω <;> simp [hSω, mul_assoc]
    _ ≤ ∑ S ∈ U.powerset,
        (C * setWeight pi S) * setWeight sigma (U \ S) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right
        (hjoint S (mem_powerset.mp hS)) zero_le
    _ = C * ∑ S ∈ U.powerset,
        setWeight pi S * setWeight sigma (U \ S) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro S _hS
      ac_rfl
    _ = C * setWeight (fun x ↦ pi x + sigma x) U := by
      congr 1
      unfold setWeight
      rw [Finset.prod_add]

/-- Expected extension weight of the configuration remainders relative to a
random selected family. -/
theorem expected_relativeExtensionWeight_le_of_joint
    {Ω W I : Type*} [Fintype Ω] [Fintype I] [DecidableEq W]
    (L : FiniteLaw Ω) (selected : Ω → Finset W)
    (F : I → Finset W) (pi sigma : W → ℝ≥0) (C : ℝ≥0)
    (d : ℕ) (hcard : ∀ i, (F i).card ≤ d)
    (hjoint : ∀ S : Finset W, S.card ≤ d →
      L.probability (fun ω ↦ S ⊆ selected ω) ≤ C * setWeight pi S)
    (A : Finset W) :
    L.expectation (fun ω ↦
      extensionWeight (fun i ↦ F i \ selected ω) sigma A) ≤
      C * extensionWeight F (fun x ↦ pi x + sigma x) A := by
  classical
  have hpoint : ∀ ω,
      extensionWeight (fun i ↦ F i \ selected ω) sigma A ≤
        ∑ i, if A ⊆ F i then
          setWeight sigma ((F i \ A) \ selected ω) else 0 := by
    intro ω
    unfold extensionWeight
    apply sum_le_sum
    intro i _hi
    by_cases hrel : A ⊆ F i \ selected ω
    · have hAF : A ⊆ F i := fun x hx ↦ (mem_sdiff.mp (hrel hx)).1
      rw [if_pos hrel, if_pos hAF]
      have heq : (F i \ selected ω) \ A = (F i \ A) \ selected ω := by
        ext x
        simp
        tauto
      rw [heq]
    · rw [if_neg hrel]
      exact zero_le
  calc
    L.expectation (fun ω ↦
        extensionWeight (fun i ↦ F i \ selected ω) sigma A) ≤
        L.expectation (fun ω ↦
          ∑ i, if A ⊆ F i then
            setWeight sigma ((F i \ A) \ selected ω) else 0) :=
      L.expectation_mono hpoint
    _ = ∑ i, if A ⊆ F i then
        L.expectation (fun ω ↦
          setWeight sigma ((F i \ A) \ selected ω)) else 0 := by
      unfold FiniteLaw.expectation
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro i _hi
      by_cases hAi : A ⊆ F i
      · simp [hAi]
      · simp [hAi]
    _ ≤ ∑ i, if A ⊆ F i then
        C * setWeight (fun x ↦ pi x + sigma x) (F i \ A) else 0 := by
      apply sum_le_sum
      intro i _hi
      by_cases hAi : A ⊆ F i
      · simp only [if_pos hAi]
        exact expected_setWeight_sdiff_le_of_joint
          L selected pi sigma C (F i \ A) (fun S hS ↦ hjoint S <|
            (card_le_card hS).trans <|
              (card_le_card sdiff_subset).trans (hcard i))
      · simp only [if_neg hAi]
        exact zero_le
    _ = C * extensionWeight F (fun x ↦ pi x + sigma x) A := by
      unfold extensionWeight
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro i _hi
      by_cases hAi : A ⊆ F i <;> simp [hAi]

/-- Markov followed by a finite union bound controls the probability that
some relative-extension root exceeds the common cutoff. -/
theorem FiniteLaw.probability_not_relativeExtensionBound_le_of_joint
    {Ω W I : Type*} [Fintype Ω] [Fintype I] [DecidableEq W]
    (L : FiniteLaw Ω) (selected : Ω → Finset W)
    (F : I → Finset W) (pi sigma : W → ℝ≥0) (C : ℝ≥0)
    (d : ℕ) (hcard : ∀ i, (F i).card ≤ d)
    (hjoint : ∀ S : Finset W, S.card ≤ d →
      L.probability (fun ω ↦ S ⊆ selected ω) ≤ C * setWeight pi S)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound F (fun x ↦ pi x + sigma x) kappa)
    (hkappaOut : 0 < kappaOut) :
    L.probability (fun ω ↦ ¬ HasExtensionBound
      (fun i ↦ F i \ selected ω) sigma kappaOut) ≤
        (configurationRoots F).card * ((C * kappa) / kappaOut) := by
  let Bad : Finset W → Ω → Prop := fun A ω ↦
    kappaOut ≤ extensionWeight (fun i ↦ F i \ selected ω) sigma A
  have hprob : ∀ A : Finset W,
      L.probability (Bad A) ≤ (C * kappa) / kappaOut := by
    intro A
    apply (L.probability_le_expectation_div
      (fun ω ↦ extensionWeight (fun i ↦ F i \ selected ω) sigma A)
      hkappaOut).trans
    exact (div_le_div_iff_of_pos_right hkappaOut).2 <|
      (expected_relativeExtensionWeight_le_of_joint
        L selected F pi sigma C d hcard hjoint A).trans
          (mul_le_mul_of_nonneg_left (hkappa A) zero_le)
  calc
    L.probability (fun ω ↦ ¬ HasExtensionBound
        (fun i ↦ F i \ selected ω) sigma kappaOut) ≤
        L.probability (fun ω ↦
          ∃ A ∈ configurationRoots F, Bad A ω) := by
      apply L.probability_mono
      intro ω hbad
      change ¬ ∀ A, extensionWeight
        (fun i ↦ F i \ selected ω) sigma A ≤ kappaOut at hbad
      simp only [not_forall] at hbad
      obtain ⟨A, hA⟩ := hbad
      have hgt : kappaOut < extensionWeight
          (fun i ↦ F i \ selected ω) sigma A := lt_of_not_ge hA
      have hmem : A ∈ configurationRoots F := by
        by_contra hnot
        have hnot' : A ∉ configurationRoots
            (fun i ↦ F i \ selected ω) := by
          intro hroot
          obtain ⟨i, hi⟩ := mem_configurationRoots_iff.mp hroot
          exact hnot (mem_configurationRoots_iff.mpr
            ⟨i, hi.trans sdiff_subset⟩)
        rw [extensionWeight_eq_zero_of_not_mem_configurationRoots
          (fun i ↦ F i \ selected ω) sigma hnot'] at hgt
        exact (not_lt_of_ge zero_le hgt).elim
      exact ⟨A, hmem, hgt.le⟩
    _ ≤ ∑ A ∈ configurationRoots F, L.probability (Bad A) :=
      L.probability_exists_le (configurationRoots F) Bad
    _ ≤ ∑ _A ∈ configurationRoots F, (C * kappa) / kappaOut := by
      exact sum_le_sum fun A _hA ↦ hprob A
    _ = (configurationRoots F).card * ((C * kappa) / kappaOut) := by
      simp

/-- A finite union bound over the roots occurring in `F` converts the
expected relative-extension estimate into one outcome satisfying the
extension cutoff simultaneously at every root. -/
theorem FiniteLaw.exists_relativeExtensionBound_of_joint
    {Ω W I : Type*} [Fintype Ω] [Fintype I] [DecidableEq W]
    (L : FiniteLaw Ω) (selected : Ω → Finset W)
    (F : I → Finset W) (pi sigma : W → ℝ≥0) (C : ℝ≥0)
    (d : ℕ) (hcard : ∀ i, (F i).card ≤ d)
    (hjoint : ∀ S : Finset W, S.card ≤ d →
      L.probability (fun ω ↦ S ⊆ selected ω) ≤ C * setWeight pi S)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound F (fun x ↦ pi x + sigma x) kappa)
    (hkappaOut : 0 < kappaOut)
    (hsmall : (configurationRoots F).card *
      ((C * kappa) / kappaOut) < 1) :
    ∃ ω : Ω, HasExtensionBound
      (fun i ↦ F i \ selected ω) sigma kappaOut := by
  have hbad := L.probability_not_relativeExtensionBound_le_of_joint
    selected F pi sigma C d hcard hjoint kappa kappaOut hkappa hkappaOut
  have hprob : L.probability (fun ω ↦ ¬ HasExtensionBound
      (fun i ↦ F i \ selected ω) sigma kappaOut) < 1 :=
    hbad.trans_lt hsmall
  have hgood : 0 < L.probability (fun ω ↦ HasExtensionBound
      (fun i ↦ F i \ selected ω) sigma kappaOut) := by
    calc
      0 < 1 - L.probability (fun ω ↦ ¬ HasExtensionBound
          (fun i ↦ F i \ selected ω) sigma kappaOut) :=
        tsub_pos_iff_lt.mpr hprob
      _ = L.probability (fun ω ↦ ¬¬ HasExtensionBound
          (fun i ↦ F i \ selected ω) sigma kappaOut) :=
        (L.probability_not (fun ω ↦ ¬ HasExtensionBound
          (fun i ↦ F i \ selected ω) sigma kappaOut)).symm
      _ = L.probability (fun ω ↦ HasExtensionBound
          (fun i ↦ F i \ selected ω) sigma kappaOut) := by
        congr 1
        funext ω
        simp
  exact L.exists_of_probability_pos hgood

end

end Erdos207

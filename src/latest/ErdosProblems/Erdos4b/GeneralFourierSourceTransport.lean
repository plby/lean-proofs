/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierIndexedSourceKernel

/-!
# Fixed source profiles on a varying primorial tuple

Reindexing preserves the real source coefficient, its simplex support,
and the compact smooth profile family. The selected prime cutoff is
proved to contain only rough primes.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators ContDiff

theorem sourceAnalyticSelbergCoefficient_equiv
    {ι κ J : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ) (d f : κ → ℕ) :
    sourceAnalyticSelbergCoefficient S (fun j i ↦ F j (e.symm i)) G LD LE d f =
      sourceAnalyticSelbergCoefficient S F G LD LE (fun i ↦ d (e i)) (fun i ↦ f (e i)) := by
  unfold sourceAnalyticSelbergCoefficient
  rw [← e.prod_comp (fun i ↦ (ArithmeticFunction.moebius (d i) : ℝ) *
    (ArithmeticFunction.moebius (f i) : ℝ))]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← e.prod_comp (fun i ↦ F j (e.symm i) (Real.log (d i) / LD) * G (Real.log (f i) / LE))]
  simp only [Equiv.symm_apply_apply]

theorem sourceSimplexSupport_equiv
    {ι κ J : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (S : Finset J) (F : J → ι → ℝ → ℝ) {A : ℝ}
    (hF : ∀ j ∈ S, ∀ u : ι → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ A) :
    ∀ j ∈ S, ∀ u : κ → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j (e.symm i) (u i) ≠ 0) → (∑ i, u i) ≤ A := by
  intro j hj u hu hne
  rw [← e.sum_comp u]
  apply hF j hj (fun i ↦ u (e i)) (fun i ↦ hu (e i))
  intro i
  simpa only [Equiv.symm_apply_apply] using hne (e i)

theorem hasCompactSupport_twoFamilySelbergProfiles
    {ι : Type*} (F : ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hF : ∀ i, HasCompactSupport (F i)) (hG : HasCompactSupport G) :
    ∀ i, HasCompactSupport (twoFamilySelbergProfiles F G i) := by
  intro i
  cases i with
  | inl i => exact (hF i).comp_left (g := Complex.ofReal) rfl
  | inr i => exact hG.comp_left (g := Complex.ofReal) rfl

theorem contDiff_twoFamilySelbergProfiles
    {ι : Type*} (F : ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hG : ContDiff ℝ ∞ G) :
    ∀ i, ContDiff ℝ ∞ (twoFamilySelbergProfiles F G i) := by
  intro i
  cases i with
  | inl i => exact Complex.ofRealCLM.contDiff.comp (hF i)
  | inr i => exact Complex.ofRealCLM.contDiff.comp hG

theorem rough_of_mem_selectedFourierPrimeCutoff
    (w : ℕ) (Q : Finset Nat.Primes) {p : ℕ}
    (hp : p ∈ selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) Q) : w < p := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
  exact of_decide_eq_true (Finset.mem_filter.mp hr).2

theorem twoFamily_source_profile_support_ceiling
    {ι J : Type*} (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hF : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hG : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) :
    ∀ j ∈ S, ∀ i t, 0 ≤ t → twoFamilySelbergProfiles (F j) G i t ≠ 0 →
      t ≤ twoFamilySelbergScales (1 / 10) 1 i := by
  intro j hj i t ht hne
  cases i with
  | inl i => exact hF j hj i t ht (fun hz ↦ hne (by simp [twoFamilySelbergProfiles, hz]))
  | inr i => exact hG t ht (fun hz ↦ hne (by simp [twoFamilySelbergProfiles, hz]))

end

end Erdos4b

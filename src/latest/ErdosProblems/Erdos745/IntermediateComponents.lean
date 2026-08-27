import ErdosProblems.Erdos745.ComponentExponential
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Absence of intermediate component sizes above the KSS threshold -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem sum_exp_Ico_le {β : ℝ} (hβ : 0 < β) (m N : ℕ) :
    (∑ k ∈ Finset.Ico m N, Real.exp (-β * k)) ≤
      Real.exp (-β * m) / (1 - Real.exp (-β)) := by
  have hexp (k : ℕ) : Real.exp (-β * k) = Real.exp (-β) ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
  simp only [hexp]
  exact geom_sum_Ico_le_of_lt_one (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by linarith))

/-- Orders strictly above a logarithmic threshold and at most a linear threshold. -/
def intermediateWindow (n : ℕ) (A δ : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k ↦ A * Real.log n < (k : ℝ) ∧ (k : ℝ) ≤ δ * n)

def IntermediateComponent (n : ℕ) (A δ : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ C : G.ConnectedComponent, A * Real.log n < (C.supp.ncard : ℝ) ∧
    (C.supp.ncard : ℝ) ≤ δ * n

theorem intermediateComponent_iff_window (n : ℕ) (A δ : ℝ) (G : SimpleGraph (Fin n)) :
    IntermediateComponent n A δ G ↔
      ∃ C : G.ConnectedComponent, C.supp.ncard ∈ intermediateWindow n A δ := by
  have hcard (C : G.ConnectedComponent) : C.supp.ncard ≤ n := by
    rw [Set.ncard_eq_toFinset_card']
    simpa using Finset.card_le_univ C.supp.toFinset
  simp only [IntermediateComponent, intermediateWindow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, by have := hcard C; omega, hC⟩
  · rintro ⟨C, _, hC⟩
    exact ⟨C, hC⟩

theorem probability_intermediate_le {n : ℕ} (hn : 0 < n) {lam A δ : ℝ}
    (hlam : 0 < lam) (hlamn : lam ≤ n) (hA : 0 ≤ A)
    (hβ : 0 < logarithmicDecay lam - lam * δ) :
    probability lam n (IntermediateComponent n A δ) ≤
      ((n : ℝ) / lam) * Real.exp (-(logarithmicDecay lam - lam * δ) * (A * Real.log n)) /
        (1 - Real.exp (-(logarithmicDecay lam - lam * δ))) := by
  let β := logarithmicDecay lam - lam * δ
  let m := ⌊A * Real.log (n : ℝ)⌋₊ + 1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ A * Real.log (n : ℝ) := mul_nonneg hA (Real.log_nonneg hn1)
  have hm : A * Real.log (n : ℝ) < (m : ℝ) := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (A * Real.log (n : ℝ))
  have hwindow (k : ℕ) (hk : k ∈ intermediateWindow n A δ) :
      0 < k ∧ k ≤ n ∧ (k : ℝ) ≤ δ * n ∧ k ∈ Finset.Ico m (n + 1) := by
    obtain ⟨hkn, hlogk, hkδ⟩ := Finset.mem_filter.mp hk
    have hkn' := Finset.mem_range.mp hkn
    have hk0 : (0 : ℝ) < k := hlog.trans_lt hlogk
    have hmk : m ≤ k := by
      dsimp [m]
      exact Nat.succ_le_iff.mpr ((Nat.floor_lt hlog).mpr hlogk)
    exact ⟨by exact_mod_cast hk0, by omega, hkδ, Finset.mem_Ico.mpr ⟨hmk, hkn'⟩⟩
  have hden : 0 < 1 - Real.exp (-β) := by
    have h := Real.exp_lt_one_iff.mpr (show -β < 0 by dsimp [β]; linarith)
    linarith
  have hevent : IntermediateComponent n A δ =
      (fun G ↦ ∃ C : G.ConnectedComponent, C.supp.ncard ∈ intermediateWindow n A δ) := by
    funext G
    exact propext (intermediateComponent_iff_window n A δ G)
  rw [hevent]
  calc
    _ ≤ ∑ k ∈ intermediateWindow n A δ, componentUpper lam n k :=
      probability_componentOrder_mem_le _ _ _
    _ ≤ ∑ k ∈ intermediateWindow n A δ, (n : ℝ) / lam * Real.exp (-β * k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hw := hwindow k hk
      exact componentUpper_le_exp_linear hn hw.1 hw.2.1 hlam hlamn hw.2.2.1
    _ = (n : ℝ) / lam * ∑ k ∈ intermediateWindow n A δ, Real.exp (-β * k) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (n : ℝ) / lam * ∑ k ∈ Finset.Ico m (n + 1), Real.exp (-β * k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun k hk ↦ (hwindow k hk).2.2.2
      · exact fun _ _ _ ↦ Real.exp_nonneg _
    _ ≤ (n : ℝ) / lam * (Real.exp (-β * m) / (1 - Real.exp (-β))) :=
      mul_le_mul_of_nonneg_left (sum_exp_Ico_le hβ m (n + 1)) (by positivity)
    _ ≤ (n : ℝ) / lam * (Real.exp (-β * (A * Real.log n)) / (1 - Real.exp (-β))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right _ hden.le
      apply Real.exp_le_exp.mpr
      have hβ' : 0 < β := hβ
      nlinarith
    _ = _ := by ring

theorem tendsto_logarithmic_error_zero {lam β A : ℝ} (hAβ : 1 < A * β) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) / lam) * Real.exp (-β * (A * Real.log n)) /
      (1 - Real.exp (-β))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp ((1 - A * β) * Real.log n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (by linarith))
  have h := (hexp.div_const lam).div_const (1 - Real.exp (-β))
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heq : Real.exp ((1 - A * β) * Real.log n) =
      (n : ℝ) * Real.exp (-β * (A * Real.log n)) := by
    rw [show (1 - A * β) * Real.log n = Real.log n + -β * (A * Real.log n) by ring,
      Real.exp_add, Real.exp_log hnR]
  rw [heq]
  ring

/-- Above any coefficient larger than the KSS constant, some linear cutoff
separates logarithmic components from possible macroscopic ones. -/
theorem exists_no_intermediate_components_of_ne_one {lam A : ℝ}
    (hlam0 : 0 < lam) (hne : lam ≠ 1)
    (hA : logarithmicConstant lam < A) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun n ↦ probability lam n (IntermediateComponent n A δ)) atTop (𝓝 0) := by
  have hα : 0 < logarithmicDecay lam := logarithmicDecay_pos hlam0 hne
  have hA0 : 0 < A := (logarithmicConstant_pos_of_ne_one hlam0 hne).trans hA
  have hAα : 1 < A * logarithmicDecay lam := by
    apply (div_lt_iff₀ hα).mp
    simpa only [logarithmicConstant, one_div] using hA
  have hinv : 1 / A < logarithmicDecay lam := by
    apply (div_lt_iff₀ hA0).mpr
    nlinarith
  let δ := (logarithmicDecay lam - 1 / A) / (2 * lam)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hinv) (by positivity)
  have hβeq : logarithmicDecay lam - lam * δ = (logarithmicDecay lam + 1 / A) / 2 := by
    dsimp [δ]
    field_simp
    ring
  have hβ : 0 < logarithmicDecay lam - lam * δ := by rw [hβeq]; positivity
  have hAβ : 1 < A * (logarithmicDecay lam - lam * δ) := by
    rw [hβeq]
    have hcancel : A * (1 / A) = 1 := by field_simp
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ probability_nonneg _ _ _))
    _ (tendsto_logarithmic_error_zero (lam := lam) hAβ)
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop lam] with n hn hlamn
  exact probability_intermediate_le (by omega) hlam0 hlamn hA0.le hβ

theorem exists_no_intermediate_components {lam A : ℝ} (hlam : 1 < lam)
    (hA : logarithmicConstant lam < A) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun n ↦ probability lam n (IntermediateComponent n A δ)) atTop (𝓝 0) :=
  exists_no_intermediate_components_of_ne_one (by linarith) (ne_of_gt hlam) hA

end

end Erdos745

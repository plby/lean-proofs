/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceSmoothRectangle
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite open-grid cells and their upper samples

The only points not lying in a unique cell at every sufficiently fine
mesh are a countable family of grid endpoints. The upper samples tend
to the point and keep the source's termwise upper-endpoint budget.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def sourceGridLower (n : ℕ) (j : Fin (n + 1)) : ℝ := (j.val : ℝ) / (n + 1 : ℝ)

def sourceGridUpper (n : ℕ) (j : Fin (n + 1)) : ℝ := (j.val + 1 : ℝ) / (n + 1 : ℝ)

def SourceGridRegular (t : ℝ) : Prop := ∀ n j : ℕ, t ≠ (j : ℝ) / (n + 1 : ℝ)

theorem sourceGridLower_nonneg (n : ℕ) (j : Fin (n + 1)) : 0 ≤ sourceGridLower n j := by
  unfold sourceGridLower
  positivity

theorem sourceGridLower_lt_upper (n : ℕ) (j : Fin (n + 1)) :
    sourceGridLower n j < sourceGridUpper n j := by
  unfold sourceGridLower sourceGridUpper
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < n + 1)).mpr
  linarith

theorem sourceGridUpper_le_one (n : ℕ) (j : Fin (n + 1)) : sourceGridUpper n j ≤ 1 := by
  unfold sourceGridUpper
  rw [div_le_one (by positivity : (0 : ℝ) < n + 1)]
  exact_mod_cast Nat.succ_le_of_lt j.isLt

theorem sourceGridCell_subset_unit (n : ℕ) (j : Fin (n + 1)) :
    Set.Ioo (sourceGridLower n j) (sourceGridUpper n j) ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro t ht
  exact ⟨lt_of_le_of_lt (sourceGridLower_nonneg n j) ht.1,
    lt_of_lt_of_le ht.2 (sourceGridUpper_le_one n j)⟩

theorem sourceGridCell_floor {n : ℕ} {j : Fin (n + 1)} {t : ℝ}
    (ht : t ∈ Set.Ioo (sourceGridLower n j) (sourceGridUpper n j)) :
    ⌊(n + 1 : ℝ) * t⌋₊ = j.val := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hlo : (j.val : ℝ) < (n + 1 : ℝ) * t := by
    have hh := (div_lt_iff₀ hn).mp ht.1
    simpa only [mul_comm] using hh
  have hhi : (n + 1 : ℝ) * t < j.val + 1 := by
    have hh := (lt_div_iff₀ hn).mp ht.2
    simpa only [mul_comm] using hh
  exact (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg _) hlo.le)).mpr ⟨hlo.le, hhi⟩

theorem sourceGridCell_unique {n : ℕ} {j k : Fin (n + 1)} {t : ℝ}
    (hj : t ∈ Set.Ioo (sourceGridLower n j) (sourceGridUpper n j))
    (hk : t ∈ Set.Ioo (sourceGridLower n k) (sourceGridUpper n k)) : j = k := by
  apply Fin.ext
  exact (sourceGridCell_floor hj).symm.trans (sourceGridCell_floor hk)

theorem sourceGrid_floor_lt {n : ℕ} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ⌊(n + 1 : ℝ) * t⌋₊ < n + 1 := by
  apply (Nat.floor_lt (mul_nonneg (by positivity) ht.1.le)).mpr
  push_cast
  exact (mul_lt_mul_of_pos_left ht.2 (by positivity)).trans_eq (mul_one _)

def sourceGridIndex (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : Fin (n + 1) :=
  ⟨⌊(n + 1 : ℝ) * t⌋₊, sourceGrid_floor_lt ht⟩

theorem mem_sourceGridIndex {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hregular : SourceGridRegular t) (n : ℕ) :
    t ∈ Set.Ioo (sourceGridLower n (sourceGridIndex n ht))
      (sourceGridUpper n (sourceGridIndex n ht)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hlo := Nat.floor_le (mul_nonneg hn.le ht.1.le)
  have hhi := Nat.lt_floor_add_one ((n + 1 : ℝ) * t)
  change (⌊(n + 1 : ℝ) * t⌋₊ : ℝ) / (n + 1 : ℝ) < t ∧
    t < ((⌊(n + 1 : ℝ) * t⌋₊ : ℝ) + 1) / (n + 1 : ℝ)
  constructor
  · apply lt_of_le_of_ne ?_ ?_
    · exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hlo)
    · exact (hregular n ⌊(n + 1 : ℝ) * t⌋₊).symm
  · apply (lt_div_iff₀ hn).mpr
    simpa only [mul_comm] using hhi

def sourceGridUpperSample (n : ℕ) (t : ℝ) : ℝ :=
  ((⌊(n + 1 : ℝ) * t⌋₊ : ℝ) + 1) / (n + 1 : ℝ)

theorem sourceGridUpperSample_bounds {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    t < sourceGridUpperSample n t ∧ sourceGridUpperSample n t ≤ t + 1 / (n + 1 : ℝ) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  constructor
  · apply (lt_div_iff₀ hn).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one ((n + 1 : ℝ) * t)
  · unfold sourceGridUpperSample
    rw [div_le_iff₀ hn]
    have hh := Nat.floor_le (show (0 : ℝ) ≤ (n + 1 : ℝ) * t by positivity)
    field_simp
    nlinarith

theorem tendsto_sourceGridUpperSample {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n ↦ sourceGridUpperSample n t) atTop (𝓝 t) := by
  have hn : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono (fun n ↦ by linarith : (fun n : ℕ ↦ (n : ℝ)) ≤
      (fun n : ℕ ↦ (n + 1 : ℝ))) tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ ↦ t + 1 / (n + 1 : ℝ)) atTop (𝓝 t) := by
    simpa only [one_div, add_zero, Function.comp_def] using
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hn)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n ↦ (sourceGridUpperSample_bounds ht n).1.le)
    (fun n ↦ (sourceGridUpperSample_bounds ht n).2)

theorem ae_sourceGridRegular : ∀ᵐ t : ℝ, SourceGridRegular t := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro j
  exact compl_mem_ae_iff.mpr (measure_singleton _)

theorem ae_sourceGridRegular_coordinates {ι : Type*} [Fintype ι] :
    ∀ᵐ t : ι → ℝ, ∀ i, SourceGridRegular (t i) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro j
  exact Measure.ae_eval_ne (fun _ : ι ↦ (volume : Measure ℝ)) i ((j : ℝ) / (n + 1 : ℝ))

end

end Erdos4b

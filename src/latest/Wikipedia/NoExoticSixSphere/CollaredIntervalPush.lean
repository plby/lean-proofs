import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Ring

/-!
# A time push supported in two endpoint collars

Interpolate between the original time and its clamping to a smaller
closed interval. Original interior points remain interior throughout.
The middle interval is fixed, and each changed time remains in its
original endpoint collar. These facts allow the push to preserve an
actual map which is constant on the two collars.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.CollaredIntervalPush

variable (a b : ℝ) (hab : a ≤ b)

def time : C(unitInterval × ℝ, ℝ) where
  toFun p := (1 - (p.1 : ℝ)) * p.2 + (p.1 : ℝ) * (projIcc a b hab p.2 : ℝ)
  continuous_toFun :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      continuous_snd).add ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)))

theorem time_zero (r : ℝ) : time a b hab (0, r) = r := by
  change (1 - (0 : ℝ)) * r + (0 : ℝ) * _ = r
  simp

theorem time_one (r : ℝ) : time a b hab (1, r) = (projIcc a b hab r : ℝ) := by
  change (1 - (1 : ℝ)) * r + (1 : ℝ) * _ = _
  simp

theorem time_fixed (u : unitInterval) {r : ℝ} (hr : r ∈ Icc a b) :
    time a b hab (u, r) = r := by
  change (1 - (u : ℝ)) * r + (u : ℝ) * (projIcc a b hab r : ℝ) = r
  rw [projIcc_of_mem hab hr]
  ring

theorem time_mem_Icc {s t r : ℝ} (hsa : s ≤ a) (hbt : b ≤ t)
    (hr : r ∈ Icc s t) (u : unitInterval) : time a b hab (u, r) ∈ Icc s t := by
  have hc : (projIcc a b hab r : ℝ) ∈ Icc s t :=
    Icc_subset_Icc hsa hbt (projIcc a b hab r).property
  exact (convex_Icc s t) hr hc (sub_nonneg.mpr u.property.2) u.property.1
    (sub_add_cancel 1 (u : ℝ))

theorem time_mem_Ioo {s t r : ℝ} (hsa : s < a) (hbt : b < t)
    (hr : r ∈ Ioo s t) (u : unitInterval) : time a b hab (u, r) ∈ Ioo s t := by
  have hc : (projIcc a b hab r : ℝ) ∈ Ioo s t :=
    ⟨hsa.trans_le (projIcc a b hab r).property.1,
      (projIcc a b hab r).property.2.trans_lt hbt⟩
  exact (convex_Ioo s t) hr hc (sub_nonneg.mpr u.property.2) u.property.1
    (sub_add_cancel 1 (u : ℝ))

theorem time_mem_left {s r : ℝ} (hr : r ∈ Icc s a) (u : unitInterval) :
    time a b hab (u, r) ∈ Icc s a := by
  change (1 - (u : ℝ)) * r + (u : ℝ) * (projIcc a b hab r : ℝ) ∈ Icc s a
  rw [projIcc_of_le_left hab hr.2]
  exact (convex_Icc s a) hr ⟨hr.1.trans hr.2, le_rfl⟩
    (sub_nonneg.mpr u.property.2) u.property.1 (sub_add_cancel 1 (u : ℝ))

theorem time_mem_right {t r : ℝ} (hr : r ∈ Icc b t) (u : unitInterval) :
    time a b hab (u, r) ∈ Icc b t := by
  change (1 - (u : ℝ)) * r + (u : ℝ) * (projIcc a b hab r : ℝ) ∈ Icc b t
  rw [projIcc_of_right_le hab hr.1]
  exact (convex_Icc b t) hr ⟨le_rfl, hr.1.trans hr.2⟩
    (sub_nonneg.mpr u.property.2) u.property.1 (sub_add_cancel 1 (u : ℝ))

theorem preserves {M N : Type*} (F : ℝ × M → N) {s t : ℝ}
    (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
    (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))
    {r : ℝ} (hr : r ∈ Icc s t) (x : M) (u : unitInterval) :
    F (time a b hab (u, r), x) = F (r, x) := by
  by_cases hl : r ≤ a
  · exact (hleft _ (time_mem_left a b hab ⟨hr.1, hl⟩ u) x).trans
      (hleft r ⟨hr.1, hl⟩ x).symm
  · by_cases hh : b ≤ r
    · exact (hright _ (time_mem_right a b hab ⟨hh, hr.2⟩ u) x).trans
        (hright r ⟨hh, hr.2⟩ x).symm
    · rw [time_fixed a b hab u ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hh).le⟩]

end NoExoticSixSphere.CollaredIntervalPush

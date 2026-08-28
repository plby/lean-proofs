import Wikipedia.NoExoticSixSphere.RegularCollaredCylinder

/-!
# The actual time fold for doubling a collared cylinder

The fold fixes the original unit interval, reflects negative times, and
is constant outside the reflected interval. Its only nonsmooth points
will be handled using the actual constant endpoint collars.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

def foldTime (t : ℝ) : ℝ := min |t| 1

theorem continuous_foldTime : Continuous foldTime := continuous_abs.min continuous_const

theorem foldTime_nonneg (t : ℝ) : 0 ≤ foldTime t := le_min (abs_nonneg t) zero_le_one

theorem foldTime_le_one (t : ℝ) : foldTime t ≤ 1 := min_le_right _ _

theorem foldTime_zero : foldTime 0 = 0 := by norm_num [foldTime]

theorem foldTime_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : foldTime t = t := by
  rw [foldTime, abs_of_nonneg ht.1, min_eq_left ht.2]

theorem foldTime_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : foldTime t = 1 :=
  min_eq_right ht

theorem foldTime_neg (t : ℝ) : foldTime (-t) = foldTime t := by
  simp only [foldTime, abs_neg]

theorem foldTime_interior_iff (t : ℝ) :
    foldTime t ∈ Ioo (0 : ℝ) 1 ↔ 0 < |t| ∧ |t| < 1 := by
  simp [foldTime]

theorem foldTime_positive_germ {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    foldTime =ᶠ[𝓝 t] (fun s ↦ s) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact foldTime_of_mem ⟨hs.1.le, hs.2.le⟩

theorem foldTime_negative_germ {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    foldTime =ᶠ[𝓝 t] (fun s ↦ -s) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  rw [foldTime, abs_of_neg hs.2, min_eq_left (by linarith [hs.1])]

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

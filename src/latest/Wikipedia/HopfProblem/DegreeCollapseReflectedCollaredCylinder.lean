import Wikipedia.HopfProblem.DegreeCollapseReflectedCylinderTime

/-!
# A smooth reflected double of the actual collared cylinder map

The scalar fold is only continuous. The actual constant endpoint collars
make its composite smooth even at the seam and the two clamping points.
The original map is retained on the whole closed unit time interval.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def map : C(ℝ × Sphere m, Sphere n) :=
  d.map.comp ⟨fun p ↦ (foldTime p.1, p.2),
    (continuous_foldTime.comp continuous_fst).prodMk continuous_snd⟩

theorem map_apply (p : ℝ × Sphere m) : map d p = d.map (foldTime p.1, p.2) := rfl

theorem map_original {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Sphere m) :
    map d (t, x) = d.map (t, x) := by
  rw [map_apply, foldTime_of_mem ht]

theorem map_reflected (t : ℝ) (x : Sphere m) : map d (-t, x) = map d (t, x) := by
  simp only [map_apply, foldTime_neg]

theorem map_zero (x : Sphere m) : map d (0, x) = d.leftMap x := by
  rw [map_apply, foldTime_zero]
  exact d.left_eq 0 d.left_mem x

theorem map_outside {t : ℝ} (ht : 1 ≤ |t|) (x : Sphere m) :
    map d (t, x) = d.rightMap x := by
  rw [map_apply, foldTime_of_one_le_abs ht]
  exact d.right_eq 1 d.right_mem x

theorem left_germ {p : ℝ × Sphere m} (hp : foldTime p.1 = 0) :
    (map d : ℝ × Sphere m → Sphere n) =ᶠ[𝓝 p] (fun q ↦ d.leftMap q.2) := by
  have ht : foldTime p.1 ∈ d.leftTimes := by rw [hp]; exact d.left_mem
  have he : ∀ᶠ q : ℝ × Sphere m in 𝓝 p, foldTime q.1 ∈ d.leftTimes :=
    (continuous_foldTime.comp continuous_fst).continuousAt
      (d.leftTimes.isOpen.mem_nhds ht)
  filter_upwards [he] with q hq
  exact d.left_eq _ hq q.2

theorem right_germ {p : ℝ × Sphere m} (hp : foldTime p.1 = 1) :
    (map d : ℝ × Sphere m → Sphere n) =ᶠ[𝓝 p] (fun q ↦ d.rightMap q.2) := by
  have ht : foldTime p.1 ∈ d.rightTimes := by rw [hp]; exact d.right_mem
  have he : ∀ᶠ q : ℝ × Sphere m in 𝓝 p, foldTime q.1 ∈ d.rightTimes :=
    (continuous_foldTime.comp continuous_fst).continuousAt
      (d.rightTimes.isOpen.mem_nhds ht)
  filter_upwards [he] with q hq
  exact d.right_eq _ hq q.2

theorem positive_germ {p : ℝ × Sphere m} (hp : p.1 ∈ Ioo (0 : ℝ) 1) :
    (map d : ℝ × Sphere m → Sphere n) =ᶠ[𝓝 p] d.map := by
  filter_upwards [(foldTime_positive_germ hp).comp_tendsto continuous_fst.continuousAt]
    with q hq
  change foldTime q.1 = q.1 at hq
  rw [map_apply, hq]

theorem negative_germ {p : ℝ × Sphere m} (hp : p.1 ∈ Ioo (-1 : ℝ) 0) :
    (map d : ℝ × Sphere m → Sphere n) =ᶠ[𝓝 p] (fun q ↦ d.map (-q.1, q.2)) := by
  filter_upwards [(foldTime_negative_germ hp).comp_tendsto continuous_fst.continuousAt]
    with q hq
  change foldTime q.1 = -q.1 at hq
  rw [map_apply, hq]

theorem contMDiff_map : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ (map d) := by
  intro p
  by_cases hz : foldTime p.1 = 0
  · exact (d.smooth_left.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq (left_germ d hz)
  by_cases ho : foldTime p.1 = 1
  · exact (d.smooth_right.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq (right_germ d ho)
  have hi : foldTime p.1 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have h := foldTime_nonneg p.1
      exact lt_of_le_of_ne h (Ne.symm hz)
    · exact lt_of_le_of_ne (foldTime_le_one p.1) ho
  have ha := (foldTime_interior_iff p.1).mp hi
  by_cases ht : 0 ≤ p.1
  · rw [abs_of_nonneg ht] at ha
    exact d.smooth_map.contMDiffAt.congr_of_eventuallyEq (positive_germ d ha)
  · have ht' : p.1 < 0 := lt_of_not_ge ht
    have hp : p.1 ∈ Ioo (-1 : ℝ) 0 := by
      rw [abs_of_neg ht'] at ha
      exact ⟨by linarith [ha.2], ht'⟩
    have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞
        (fun q : ℝ × Sphere m ↦ (-q.1, q.2)) := contMDiff_fst.neg.prodMk contMDiff_snd
    exact (d.smooth_map.comp hs).contMDiffAt.congr_of_eventuallyEq (negative_germ d hp)

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

import Wikipedia.NoExoticSixSphere.MooreLoopNormalization
import Mathlib.Topology.Homotopy.Equiv

/-!
# A genuine normalization homotopy between the two loop models

The duration changes continuously to one while the normalized path stays
unchanged. This gives an ordinary homotopy equivalence between Moore loops
and native paths. The duration-one inverse does not preserve the zero-duration
Moore identity; no based inverse or James-space equivalence is asserted.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

def oneDuration (u : I × Loop y₀) : ℝ :=
  (1 - (u.1 : ℝ)) * u.2.duration + (u.1 : ℝ)

theorem oneDuration_nonneg (u : I × Loop y₀) : 0 ≤ oneDuration u :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr u.1.property.2) u.2.duration_nonneg) u.1.property.1

theorem continuous_oneDuration : Continuous (oneDuration (y₀ := y₀)) := by
  have ht : Continuous (fun u : I × Loop y₀ ↦ (u.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub ht).mul (continuous_duration.comp continuous_snd)).add ht

theorem oneDuration_zero (p : Loop y₀) : oneDuration (0, p) = p.duration := by
  simp [oneDuration]

theorem oneDuration_one (p : Loop y₀) : oneDuration (1, p) = 1 := by
  simp [oneDuration]

theorem oneDuration_ofPath (s : I) (c : Path y₀ y₀) : oneDuration (s, ofPath c) = 1 := by
  simp [oneDuration, duration_ofPath]

theorem duration_eq_zero_of_oneDuration_zero (u : I × Loop y₀) (h : oneDuration u = 0) :
    u.2.duration = 0 := by
  have hp := mul_nonneg (sub_nonneg.mpr u.1.property.2) u.2.duration_nonneg
  change (1 - (u.1 : ℝ)) * u.2.duration + (u.1 : ℝ) = 0 at h
  have hs : (u.1 : ℝ) = 0 := le_antisymm (by linarith) u.1.property.1
  simpa only [hs, sub_zero, one_mul, add_zero] using h

def adjustment (u : I × Loop y₀) : Loop y₀ :=
  timed (fun v : I × Loop y₀ ↦ toPath v.2) oneDuration oneDuration_nonneg u

theorem continuous_adjustment : Continuous (adjustment (y₀ := y₀)) :=
  continuous_timed (fun v : I × Loop y₀ ↦ toPath v.2)
    (continuous_toPath.comp continuous_snd) oneDuration continuous_oneDuration
    oneDuration_nonneg (fun u h ↦ toPath_eq_refl_of_duration_zero u.2
      (duration_eq_zero_of_oneDuration_zero u h))

theorem adjustment_zero (p : Loop y₀) : adjustment (0, p) = p :=
  timed_eq_of_duration_eq _ _ _ (0, p) p rfl (oneDuration_zero p)

theorem adjustment_one (p : Loop y₀) : adjustment (1, p) = ofPath (toPath p) := by
  apply ext
  · exact oneDuration_one p
  · intro t
    change (toPath p).extend (t / oneDuration (1, p)) = (ofPath (toPath p)).curve t
    rw [oneDuration_one, div_one, curve_ofPath]

theorem adjustment_ofPath (s : I) (c : Path y₀ y₀) : adjustment (s, ofPath c) = ofPath c := by
  apply ext
  · exact oneDuration_ofPath s c
  · intro t
    change (toPath (ofPath c)).extend (t / oneDuration (s, ofPath c)) = (ofPath c).curve t
    rw [toPath_ofPath, oneDuration_ofPath, div_one, curve_ofPath]

theorem normalization_adjustment (u : I × Loop y₀) : toPath (adjustment u) = toPath u.2 :=
  toPath_timed _ _ _ u (fun h ↦ toPath_eq_refl_of_duration_zero u.2
    (duration_eq_zero_of_oneDuration_zero u h))

def adjustmentHomotopy : (ContinuousMap.id (Loop y₀)).Homotopy
    (realizationMap.comp normalizationMap) where
  toFun := adjustment
  continuous_toFun := continuous_adjustment
  map_zero_left := adjustment_zero
  map_one_left := adjustment_one

def normalizationEquiv : Loop y₀ ≃ₕ Path y₀ y₀ where
  toFun := normalizationMap
  invFun := realizationMap
  left_inv := ⟨adjustmentHomotopy.symm⟩
  right_inv := by rw [normalization_realization]

theorem normalizationEquiv_apply (p : Loop y₀) : normalizationEquiv p = toPath p := rfl

theorem normalizationEquiv_symm_apply (c : Path y₀ y₀) :
    normalizationEquiv.symm c = ofPath c := rfl

end NoExoticSixSphere.Moore.Loop

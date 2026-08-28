import Wikipedia.NoExoticSixSphere.MooreLoopHomotopy

/-!
# Normalization preserves loop multiplication up to an actual homotopy

Changing both Moore durations to one gives the usual half-interval
concatenation of native paths. The resulting homotopy is jointly
continuous in both loops and fixes the pair of constant loops after
normalization. It is not an assertion that James space is a loop space.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

theorem toPath_ofPath_mul (p q : Path y₀ y₀) :
    toPath (ofPath p * ofPath q) = p.trans q := by
  apply Path.ext
  funext t
  rw [toPath_apply, duration_mul, duration_ofPath, duration_ofPath]
  have he : (1 : ℝ) + 1 = 2 := by norm_num
  rw [he]
  change (ofPath p * ofPath q).curve (2 * (t : ℝ)) = p.trans q t
  rw [curve_mul, duration_ofPath, curve_ofPath, curve_ofPath]
  rw [← (p.trans q).extend_extends' t]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [if_pos (by linarith : 2 * (t : ℝ) ≤ 1), p.extend_trans_of_le_half q ht]
  · rw [if_neg (by linarith : ¬ 2 * (t : ℝ) ≤ 1),
      p.extend_trans_of_half_le q (le_of_not_ge ht)]

def normalizedMul : C(Loop y₀ × Loop y₀, Path y₀ y₀) :=
  ⟨fun p ↦ toPath (p.1 * p.2), continuous_toPath.comp continuous_mul⟩

def pathMul : C(Loop y₀ × Loop y₀, Path y₀ y₀) :=
  ⟨fun p ↦ (toPath p.1).trans (toPath p.2),
    (continuous_toPath.comp continuous_fst).path_trans
      (continuous_toPath.comp continuous_snd)⟩

def multiplicationHomotopy : (normalizedMul (y₀ := y₀)).Homotopy pathMul where
  toFun u := toPath (adjustment (u.1, u.2.1) * adjustment (u.1, u.2.2))
  continuous_toFun := by
    have hl : Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ adjustment (u.1, u.2.1)) :=
      continuous_adjustment.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hr : Continuous (fun u : I × (Loop y₀ × Loop y₀) ↦ adjustment (u.1, u.2.2)) :=
      continuous_adjustment.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    exact continuous_toPath.comp (hl.mul hr)
  map_zero_left p := by
    change toPath (adjustment (0, p.1) * adjustment (0, p.2)) = toPath (p.1 * p.2)
    rw [adjustment_zero, adjustment_zero]
  map_one_left p := by
    change toPath (adjustment (1, p.1) * adjustment (1, p.2)) =
      (toPath p.1).trans (toPath p.2)
    rw [adjustment_one, adjustment_one, toPath_ofPath_mul]

theorem curve_adjustment_one (s : I) (t : ℝ) :
    (adjustment (s, (1 : Loop y₀))).curve t = y₀ := by
  change (toPath (1 : Loop y₀)).extend (t / oneDuration (s, (1 : Loop y₀))) = y₀
  rw [toPath_one]
  rfl

theorem multiplicationHomotopy_one (s : I) :
    multiplicationHomotopy (s, ((1 : Loop y₀), 1)) = Path.refl y₀ := by
  apply Path.ext
  funext t
  change toPath (adjustment (s, (1 : Loop y₀)) * adjustment (s, (1 : Loop y₀))) t = y₀
  rw [toPath_apply, curve_mul]
  split_ifs <;> exact curve_adjustment_one s _

end NoExoticSixSphere.Moore.Loop

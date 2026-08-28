import Wikipedia.NoExoticSixSphere.MooreTimedFamily

/-!
# Exact recovery of a Moore loop from its normalized native path

Normalization retains the whole curve once its duration is remembered,
including duration zero. Native paths also have a continuous duration-one
realization. These are actual path identities, before homotopy quotients.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

theorem eq_one_of_duration_zero (p : Loop y₀) (hp : p.duration = 0) : p = 1 := by
  apply ext hp
  intro t
  rw [curve_one]
  by_cases ht : t ≤ 0
  · exact p.curve_of_nonpos t ht
  · exact p.curve_of_duration_le t (hp ▸ le_of_not_ge ht)

theorem toPath_eq_refl_of_duration_zero (p : Loop y₀) (hp : p.duration = 0) :
    toPath p = Path.refl y₀ := by
  rw [eq_one_of_duration_zero p hp, toPath_one]

theorem toPath_extend (p : Loop y₀) (t : ℝ) :
    (toPath p).extend t = p.curve (p.duration * t) := by
  by_cases ht : t ≤ 0
  · rw [(toPath p).extend_of_le_zero ht]
    exact (p.curve_of_nonpos _
      (mul_nonpos_of_nonneg_of_nonpos p.duration_nonneg ht)).symm
  · by_cases h₁ : 1 ≤ t
    · rw [(toPath p).extend_of_one_le h₁]
      apply (p.curve_of_duration_le _ _).symm
      nlinarith [mul_nonneg p.duration_nonneg (sub_nonneg.mpr h₁)]
    · have hi : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_ge ht, le_of_not_ge h₁⟩
      rw [(toPath p).extend_apply hi]
      rfl

theorem toPath_extend_retime (p : Loop y₀) (t : ℝ) :
    (toPath p).extend (t / p.duration) = p.curve t := by
  by_cases hp : p.duration = 0
  · have he := eq_one_of_duration_zero p hp
    rw [he]
    rfl
  · rw [toPath_extend, ← mul_div_assoc, mul_div_cancel_left₀ t hp]

theorem timed_eq_of_duration_eq {X : Type*} (c : X → Path y₀ y₀) (d : X → ℝ)
    (hn : ∀ x, 0 ≤ d x) (x : X) (p : Loop y₀)
    (hc : c x = toPath p) (hd : d x = p.duration) : timed c d hn x = p := by
  apply ext
  · exact hd
  · intro t
    rw [curve_timed, hc, hd, toPath_extend_retime]

theorem timed_original (p : Loop y₀) : timed toPath duration duration_nonneg p = p :=
  timed_eq_of_duration_eq _ _ _ p p rfl rfl

def ofPath (c : Path y₀ y₀) : Loop y₀ :=
  timed id (fun _ : Path y₀ y₀ ↦ 1) (fun _ ↦ zero_le_one) c

theorem duration_ofPath (c : Path y₀ y₀) : (ofPath c).duration = 1 := rfl

theorem curve_ofPath (c : Path y₀ y₀) (t : ℝ) : (ofPath c).curve t = c.extend t := by
  change c.extend (t / 1) = c.extend t
  rw [div_one]

theorem continuous_ofPath : Continuous (ofPath : Path y₀ y₀ → Loop y₀) :=
  continuous_timed id continuous_id (fun _ ↦ 1) continuous_const (fun _ ↦ zero_le_one)
    (fun _ h ↦ False.elim (one_ne_zero h))

theorem toPath_ofPath (c : Path y₀ y₀) : toPath (ofPath c) = c :=
  toPath_timed id (fun _ ↦ 1) (fun _ ↦ zero_le_one) c
    (fun h ↦ False.elim (one_ne_zero h))

def normalizationMap : C(Loop y₀, Path y₀ y₀) := ⟨toPath, continuous_toPath⟩

def realizationMap : C(Path y₀ y₀, Loop y₀) := ⟨ofPath, continuous_ofPath⟩

theorem normalization_realization : normalizationMap.comp realizationMap =
    ContinuousMap.id (Path y₀ y₀) := by
  apply ContinuousMap.ext
  intro c
  exact toPath_ofPath c

end NoExoticSixSphere.Moore.Loop

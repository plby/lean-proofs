import Wikipedia.HopfProblem.DegreeCollapseReflectedHalfRetraction

/-!
# An actual open half of the reflected double has the original half's homotopy type

A small symmetric time interval lies in the constant endpoint collar.
Enlarge the nonnegative half by that negative collar and slide each negative
time to its absolute value. The resulting homotopy stays inside the actual
reflected fiber and the actual open half. Its retraction is the already
constructed global absolute-time retraction.
-/

noncomputable section

open Function Set ContinuousMap Metric
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem exists_seam_width : ∃ ε : ℝ, 0 < ε ∧ Icc (-ε) ε ⊆ seamCollarTimes d := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((seamCollarTimes d).isOpen.mem_nhds (zero_mem_seamCollarTimes d))
  refine ⟨r / 2, by linarith, ?_⟩
  intro t ht
  apply hsub
  change dist t 0 < r
  rw [Real.dist_eq, sub_zero]
  exact (abs_le.mpr ht).trans_lt (by linarith)

def positiveOpen (ε : ℝ) : Set (Fiber d) := {p | -ε < p.val.1}
def negativeOpen (ε : ℝ) : Set (Fiber d) := {p | p.val.1 < ε}

theorem positiveOpen_isOpen (ε : ℝ) : IsOpen (positiveOpen d ε) :=
  isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)

theorem negativeOpen_isOpen (ε : ℝ) : IsOpen (negativeOpen d ε) :=
  isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const

theorem open_halves_cover (ε : ℝ) (hε : 0 < ε) :
    positiveOpen d ε ∪ negativeOpen d ε = univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  change -ε < p.val.1 ∨ p.val.1 < ε
  rcases lt_or_ge (-ε) p.val.1 with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

def negativePositiveHomeomorph (ε : ℝ) : negativeOpen d ε ≃ₜ positiveOpen d ε :=
  (reflection d).subtype (fun p ↦ by
    change p.val.1 < ε ↔ -ε < -p.val.1
    exact neg_lt_neg_iff.symm)

def halfSlideTime (s : unitInterval) (t : ℝ) : ℝ := (1 - s.val) * t + s.val * |t|

theorem halfSlideTime_of_nonneg (s : unitInterval) {t : ℝ} (ht : 0 ≤ t) :
    halfSlideTime s t = t := by
  rw [halfSlideTime, abs_of_nonneg ht]
  ring

theorem halfSlideTime_bounds (s : unitInterval) (t : ℝ) :
    -|t| ≤ halfSlideTime s t ∧ halfSlideTime s t ≤ |t| := by
  have h0 := s.property.1
  have h1 := s.property.2
  have ht0 := neg_abs_le t
  have ht1 := le_abs_self t
  have ha := abs_nonneg t
  dsimp [halfSlideTime]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht0), mul_nonneg h0 ha]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ht1)]

variable (ε : ℝ) (hε : 0 < ε) (hc : Icc (-ε) ε ⊆ seamCollarTimes d)

include hc in
theorem halfSlideTime_fiber (s : unitInterval) (p : positiveOpen d ε) :
    map d (halfSlideTime s p.val.val.1, p.val.val.2) = b := by
  by_cases ht : 0 ≤ p.val.val.1
  · rw [halfSlideTime_of_nonneg s ht]
    exact p.val.property
  · have hn : p.val.val.1 < 0 := lt_of_not_ge ht
    have hp : -ε < p.val.val.1 := p.property
    have ha : |p.val.val.1| < ε := by rw [abs_of_neg hn]; linarith
    have hb := halfSlideTime_bounds s p.val.val.1
    have hs : halfSlideTime s p.val.val.1 ∈ seamCollarTimes d :=
      hc ⟨by linarith, by linarith⟩
    have ho : p.val.val.1 ∈ seamCollarTimes d := hc ⟨hp.le, by linarith⟩
    exact (map_on_seamCollar d _ hs _).trans
      ((map_on_seamCollar d _ ho _).symm.trans p.val.property)

theorem halfSlideTime_mem (s : unitInterval) (p : positiveOpen d ε) :
    -ε < halfSlideTime s p.val.val.1 := by
  by_cases ht : 0 ≤ p.val.val.1
  · rw [halfSlideTime_of_nonneg s ht]
    exact p.property
  · have hn : p.val.val.1 < 0 := lt_of_not_ge ht
    have hp : -ε < p.val.val.1 := p.property
    have hb := (halfSlideTime_bounds s p.val.val.1).1
    rw [abs_of_neg hn, neg_neg] at hb
    exact hp.trans_le hb

def positiveHalfRetraction : C(positiveOpen d ε, NonnegativeHalf d) :=
  (halfRetraction d).comp ⟨Subtype.val, continuous_subtype_val⟩

def halfToPositive : C(NonnegativeHalf d, positiveOpen d ε) :=
  ⟨fun p ↦ ⟨p.val, (neg_lt_zero.mpr hε).trans_le p.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def positiveHalfSlide :
    (ContinuousMap.id (positiveOpen d ε)).Homotopy
      ((halfToPositive d ε hε).comp (positiveHalfRetraction d ε)) where
  toFun q := ⟨⟨(halfSlideTime q.1 q.2.val.val.1, q.2.val.val.2),
    halfSlideTime_fiber d ε hc q.1 q.2⟩, halfSlideTime_mem d ε q.1 q.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_fst.comp (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_snd)))).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_fst.comp (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_snd))).abs))
    · exact continuous_snd.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp [halfSlideTime]) rfl
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (by simp [halfSlideTime, halfToPositive, positiveHalfRetraction,
      halfRetraction]) rfl

def positiveHalfHomotopyEquiv : positiveOpen d ε ≃ₕ NonnegativeHalf d where
  toFun := positiveHalfRetraction d ε
  invFun := halfToPositive d ε hε
  left_inv := ⟨(positiveHalfSlide d ε hε hc).symm⟩
  right_inv := by
    have he : (positiveHalfRetraction d ε).comp (halfToPositive d ε hε) =
        ContinuousMap.id (NonnegativeHalf d) :=
      ContinuousMap.ext (halfRetraction_inclusion d)
    rw [he]

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

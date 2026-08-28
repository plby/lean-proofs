import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith

/-!
# Explicit height-supported interpolation

The tent cutoff centered at a positive height vanishes throughout a
neighborhood of height zero. Thus an arbitrary total extension of a map
continuous only off height zero can be used in a jointly continuous affine
interpolation. The formula retains translation covariance and agrees with
the punctured map at the chosen height and final time.
-/

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction.Interpolation

/-- The explicit tent of half-width `ρ / 2`, centered at height `ρ`. -/
noncomputable def tentWeight (ρ r : ℝ) : ℝ :=
  max 0 (1 - |r - ρ| / (ρ / 2))

theorem tentWeight_continuous (ρ : ℝ) : Continuous (tentWeight ρ) :=
  continuous_const.max
    (continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const (ρ / 2)))

theorem tentWeight_nonneg (ρ r : ℝ) : 0 ≤ tentWeight ρ r :=
  le_max_left _ _

theorem tentWeight_le_one {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) : tentWeight ρ r ≤ 1 := by
  apply max_le zero_le_one
  have hdiv : 0 ≤ |r - ρ| / (ρ / 2) := div_nonneg (abs_nonneg _) (half_pos hρ).le
  linarith

theorem tentWeight_self (ρ : ℝ) : tentWeight ρ ρ = 1 := by
  simp [tentWeight]

theorem tentWeight_eq_zero_of_half_le_abs {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ)
    (hr : ρ / 2 ≤ |r - ρ|) : tentWeight ρ r = 0 := by
  apply max_eq_left
  have hdiv : 1 ≤ |r - ρ| / (ρ / 2) :=
    (le_div_iff₀ (half_pos hρ)).mpr (by simpa only [one_mul] using hr)
  linarith

/-- In particular, the cutoff is identically zero near the central height. -/
theorem tentWeight_eq_zero_of_le_half {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ)
    (hr : r ≤ ρ / 2) : tentWeight ρ r = 0 := by
  apply tentWeight_eq_zero_of_half_le_abs hρ r
  linarith [neg_le_abs (r - ρ)]

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The total affine formula; the values of `b` at height zero are immaterial. -/
noncomputable def interpolate (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (p : unitInterval × X) : E :=
  a p.2 + ((p.1 : ℝ) * tentWeight ρ (h p.2)) • (b p.2 - a p.2)

theorem interpolate_zero (ρ : ℝ) (h : X → ℝ) (a b : X → E) (x : X) :
    interpolate ρ h a b (0, x) = a x := by
  simp [interpolate]

theorem interpolate_eq_left_of_height_le_half (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (hρ : 0 < ρ) (s : unitInterval) (x : X) (hx : h x ≤ ρ / 2) :
    interpolate ρ h a b (s, x) = a x := by
  simp only [interpolate, tentWeight_eq_zero_of_le_half hρ (h x) hx,
    mul_zero, zero_smul, add_zero]

theorem interpolate_fixed_of_height_zero (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (hρ : 0 < ρ) (s : unitInterval) (x : X) (hx : h x = 0) :
    interpolate ρ h a b (s, x) = a x :=
  interpolate_eq_left_of_height_le_half ρ h a b hρ s x
    (by rw [hx]; exact (half_pos hρ).le)

theorem interpolate_one_of_height_eq (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (x : X) (hx : h x = ρ) : interpolate ρ h a b (1, x) = b x := by
  simp [interpolate, hx, tentWeight_self]

/-- Translation covariance needs no group structure or continuity of the
transformation. The punctured map is only required to transform off height zero. -/
theorem interpolate_translate (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (T : X → X) (d : E) (hT : ∀ x, h (T x) = h x)
    (ha : ∀ x, a (T x) = a x + d)
    (hb : ∀ x, h x ≠ 0 → b (T x) = b x + d) (s : unitInterval) (x : X) :
    interpolate ρ h a b (s, T x) = interpolate ρ h a b (s, x) + d := by
  by_cases hx : h x = 0
  · rw [interpolate_fixed_of_height_zero ρ h a b hρ s (T x) ((hT x).trans hx),
      interpolate_fixed_of_height_zero ρ h a b hρ s x hx, ha x]
  · simp only [interpolate, hT x, ha x, hb x hx, add_sub_add_right_eq_sub]
    exact add_right_comm _ _ _

variable [TopologicalSpace X]

/-- Continuity is proved on the punctured region and the open region
below half the chosen height, where the explicit formula equals `a`. -/
theorem interpolate_continuous (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (hρ : 0 < ρ) (hh : Continuous h) (ha : Continuous a)
    (hb : ContinuousOn b {x : X | h x ≠ 0}) : Continuous (interpolate ρ h a b) := by
  have hw : Continuous (fun p : unitInterval × X =>
      (p.1 : ℝ) * tentWeight ρ (h p.2)) :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((tentWeight_continuous ρ).comp (hh.comp continuous_snd))
  have hu : ContinuousOn (interpolate ρ h a b)
      {p : unitInterval × X | h p.2 ≠ 0} :=
    (ha.comp continuous_snd).continuousOn.add
      (hw.continuousOn.smul
        ((hb.comp continuous_snd.continuousOn (fun _ hp => hp)).sub
          (ha.comp continuous_snd).continuousOn))
  have hv : ContinuousOn (interpolate ρ h a b)
      {p : unitInterval × X | h p.2 < ρ / 2} :=
    (ha.comp continuous_snd).continuousOn.congr fun p hp =>
      interpolate_eq_left_of_height_le_half ρ h a b hρ p.1 p.2 hp.le
  have hcover : {p : unitInterval × X | h p.2 ≠ 0} ∪
      {p : unitInterval × X | h p.2 < ρ / 2} = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : h p.2 = 0
    · right
      change h p.2 < ρ / 2
      rw [hp]
      exact half_pos hρ
    · exact Or.inl hp
  rw [← continuousOn_univ, ← hcover]
  exact hu.union_of_isOpen hv
    (isOpen_ne_fun (hh.comp continuous_snd) continuous_const)
    (isOpen_Iio.preimage (hh.comp continuous_snd))

/-- The explicit interpolation as a jointly continuous map. -/
noncomputable def map (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (hρ : 0 < ρ) (hh : Continuous h) (ha : Continuous a)
    (hb : ContinuousOn b {x : X | h x ≠ 0}) : C(unitInterval × X, E) :=
  ⟨interpolate ρ h a b, interpolate_continuous ρ h a b hρ hh ha hb⟩

theorem map_apply (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (hρ : 0 < ρ) (hh : Continuous h) (ha : Continuous a)
    (hb : ContinuousOn b {x : X | h x ≠ 0}) (p : unitInterval × X) :
    map ρ h a b hρ hh ha hb p =
      a p.2 + ((p.1 : ℝ) * tentWeight ρ (h p.2)) • (b p.2 - a p.2) := rfl

/-- The construction is an actual homotopy from `a` to its interpolated
endpoint, not an assumed extension across the central set. -/
noncomputable def homotopy (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (hρ : 0 < ρ) (hh : Continuous h) (ha : Continuous a)
    (hb : ContinuousOn b {x : X | h x ≠ 0}) :
    (⟨a, ha⟩ : C(X, E)).Homotopy
      ⟨fun x => interpolate ρ h a b (1, x),
        (interpolate_continuous ρ h a b hρ hh ha hb).comp
          (continuous_const.prodMk continuous_id)⟩ where
  toFun := interpolate ρ h a b
  continuous_toFun := interpolate_continuous ρ h a b hρ hh ha hb
  map_zero_left := interpolate_zero ρ h a b
  map_one_left _ := rfl

end Wikipedia.HopfProblem.CuspControlledRetraction.Interpolation

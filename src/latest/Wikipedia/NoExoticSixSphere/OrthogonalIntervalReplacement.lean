import Wikipedia.NoExoticSixSphere.OrthogonalLocalSegment
import Wikipedia.NoExoticSixSphere.OrthogonalIntervalCoordinates

/-!
# Insert one local exponential replacement into a whole path

The correction is a continuous orthogonal family which is the identity outside
the chosen time interval. Multiplying these corrections will allow separate
interval replacements to be assembled without discontinuous piecewise choices.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential.IntervalReplacement

open GLOrthonormalization CayleyTransform IntervalCoordinates OrthogonalPaths.ColumnLift

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, OrthogonalOperators n)) (s u : I)

noncomputable def restricted : C(I × X, OrthogonalOperators n) :=
  H.comp ⟨fun p ↦ (Icc.convexComb s u p.1, p.2),
    ((Icc.continuous_convexComb s u).comp continuous_fst).prodMk continuous_snd⟩

theorem restricted_apply (t : I) (x : X) :
    restricted H s u (t, x) = H (Icc.convexComb s u t, x) := rfl

theorem restricted_zero (x : X) : restricted H s u (0, x) = H (s, x) := by
  rw [restricted_apply, Icc.convexComb_zero]

theorem restricted_one (x : X) : restricted H s u (1, x) = H (u, x) := by
  rw [restricted_apply, Icc.convexComb_one]

variable (hsu : s ≤ u)
  (hsmall : ∀ t ∈ Icc s u, ∀ x, (H (s, x))⁻¹ * H (t, x) ∈ (logarithmChart n).source)

include hsu hsmall in
theorem localCondition (p : I × X) :
    (restricted H s u (0, p.2))⁻¹ * restricted H s u p ∈ (logarithmChart n).source := by
  rw [restricted_zero]
  exact hsmall (Icc.convexComb s u p.1)
    ⟨Icc.le_convexComb hsu p.1, Icc.convexComb_le hsu p.1⟩ p.2

noncomputable def lifted : C(I × (I × X), OrthogonalOperators n) :=
  (LocalSegment.replacement (restricted H s u) (localCondition H s u hsu hsmall)).comp
    ⟨fun q ↦ (q.1, (normalize s u q.2.1, q.2.2)),
      continuous_fst.prodMk (((continuous_normalize s u).comp
        (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))⟩

theorem lifted_apply (r t : I) (x : X) :
    lifted H s u hsu hsmall (r, (t, x)) =
      LocalSegment.replacement (restricted H s u) (localCondition H s u hsu hsmall)
        (r, (normalize s u t, x)) := rfl

theorem lifted_zero (t : I) (x : X) :
    lifted H s u hsu hsmall (0, (t, x)) = H (clip s u t, x) := by
  rw [lifted_apply, LocalSegment.replacement_zero, restricted_apply, convexComb_normalize hsu]

theorem lifted_before (r t : I) (x : X) (ht : t ≤ s) :
    lifted H s u hsu hsmall (r, (t, x)) = H (s, x) := by
  rw [lifted_apply, normalize_before hsu ht, LocalSegment.replacement_time_zero, restricted_zero]

theorem lifted_after (r t : I) (x : X) (ht : u ≤ t) :
    lifted H s u hsu hsmall (r, (t, x)) = H (u, x) := by
  rcases lt_or_eq_of_le hsu with hlt | heq
  · rw [lifted_apply, normalize_after hlt ht, LocalSegment.replacement_time_one, restricted_one]
  · subst u
    rw [lifted_apply]
    have hconst : ∀ v, restricted H s s (v, x) = restricted H s s (0, x) := by
      intro v
      simp only [restricted_apply, Icc.convexComb_eq]
    rw [LocalSegment.replacement_stationary _ _ _ _ x hconst,
      restricted_apply, Icc.convexComb_eq]

/-- The correction is supported on the chosen time interval. -/
noncomputable def correction : C(I × (I × X), OrthogonalOperators n) where
  toFun q := lifted H s u hsu hsmall q * (H (clip s u q.2.1, q.2.2))⁻¹
  continuous_toFun := (lifted H s u hsu hsmall).continuous.mul
    ((H.comp (clipMap s u)).continuous.comp continuous_snd).inv

theorem correction_apply (r t : I) (x : X) :
    correction H s u hsu hsmall (r, (t, x)) =
      lifted H s u hsu hsmall (r, (t, x)) * (H (clip s u t, x))⁻¹ := rfl

theorem correction_zero (t : I) (x : X) :
    correction H s u hsu hsmall (0, (t, x)) = 1 := by
  rw [correction_apply, lifted_zero, mul_inv_cancel]

theorem correction_before (r t : I) (x : X) (ht : t ≤ s) :
    correction H s u hsu hsmall (r, (t, x)) = 1 := by
  rw [correction_apply, lifted_before H s u hsu hsmall r t x ht,
    clip_of_le hsu ht, mul_inv_cancel]

theorem correction_after (r t : I) (x : X) (ht : u ≤ t) :
    correction H s u hsu hsmall (r, (t, x)) = 1 := by
  rw [correction_apply, lifted_after H s u hsu hsmall r t x ht,
    clip_of_ge (hsu.trans ht), min_eq_right ht, mul_inv_cancel]

theorem correction_stationary (r t : I) (x : X)
    (hx : ∀ v, H (v, x) = H (0, x)) :
    correction H s u hsu hsmall (r, (t, x)) = 1 := by
  have hconst : ∀ v, restricted H s u (v, x) = restricted H s u (0, x) := by
    intro v
    exact (hx (Icc.convexComb s u v)).trans (hx (Icc.convexComb s u 0)).symm
  rw [correction_apply, lifted_apply,
    LocalSegment.replacement_stationary _ _ _ _ x hconst, restricted_apply,
    hx (Icc.convexComb s u (normalize s u t)), hx (clip s u t), mul_inv_cancel]

/-- Inside the interval, the final correction produces the prescribed exponential segment. -/
theorem correction_one_mul (t : I) (x : X) (ht : t ∈ Icc s u) :
    correction H s u hsu hsmall (1, (t, x)) * H (t, x) =
      H (s, x) * exp ((normalize s u t : ℝ) •
        logarithmChart n ((H (s, x))⁻¹ * H (u, x))) := by
  rw [correction_apply, lifted_apply, LocalSegment.replacement_one,
    clip_of_ge ht.1, min_eq_left ht.2, mul_assoc, inv_mul_cancel, mul_one]
  change restricted H s u (0, x) * exp ((normalize s u t : ℝ) •
    logarithmChart n ((restricted H s u (0, x))⁻¹ * restricted H s u (1, x))) = _
  rw [restricted_zero, restricted_one]

end NoExoticSixSphere.OrthogonalExponential.IntervalReplacement

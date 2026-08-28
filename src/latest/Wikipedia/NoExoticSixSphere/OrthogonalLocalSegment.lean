import Wikipedia.NoExoticSixSphere.OrthogonalExponentialSubdivision

/-!
# Replace a local orthogonal path by an exponential segment

If every increment of a path family lies in the local logarithm domain, linear
interpolation of its logarithms replaces it by an exponential segment. The
homotopy fixes both endpoint slices and all stationary parameters exactly.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential.LocalSegment

open GLOrthonormalization CayleyTransform

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, OrthogonalOperators n))
  (h : ∀ p : I × X, (H (0, p.2))⁻¹ * H p ∈ (logarithmChart n).source)

noncomputable def logs : C(I × X, SkewOperators n) where
  toFun p := logarithmChart n ((H (0, p.2))⁻¹ * H p)
  continuous_toFun := (logarithmChart n).contMDiffOn_toFun.continuousOn.comp_continuous
    ((H.continuous.comp (continuous_const.prodMk continuous_snd)).inv.mul H.continuous) h

theorem exp_logs (p : I × X) : exp (logs H h p) = (H (0, p.2))⁻¹ * H p :=
  exp_logarithmChart _ (h p)

theorem logs_zero (x : X) : logs H h (0, x) = 0 := by
  change logarithmChart n ((H (0, x))⁻¹ * H (0, x)) = 0
  rw [inv_mul_cancel, logarithmChart_one]

theorem logs_of_stationary (x : X) (hx : ∀ t, H (t, x) = H (0, x)) (t : I) :
    logs H h (t, x) = 0 := by
  change logarithmChart n ((H (0, x))⁻¹ * H (t, x)) = 0
  rw [hx t, inv_mul_cancel, logarithmChart_one]

noncomputable def segment : C(I × X, OrthogonalOperators n) where
  toFun p := H (0, p.2) * exp ((p.1 : ℝ) • logs H h (1, p.2))
  continuous_toFun :=
    (H.continuous.comp (continuous_const.prodMk continuous_snd)).mul
      (contMDiff_exp.continuous.comp ((continuous_subtype_val.comp continuous_fst).smul
        ((logs H h).continuous.comp (continuous_const.prodMk continuous_snd))))

noncomputable def replacement : C(I × (I × X), OrthogonalOperators n) where
  toFun q := H (0, q.2.2) * exp
    ((1 - (q.1 : ℝ)) • logs H h q.2 + (q.1 : ℝ) • ((q.2.1 : ℝ) • logs H h (1, q.2.2)))
  continuous_toFun := by
    have hs : Continuous (fun q : I × (I × X) ↦ (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous (fun q : I × (I × X) ↦ (q.2.1 : ℝ)) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hl : Continuous (fun q : I × (I × X) ↦ logs H h q.2) :=
      (logs H h).continuous.comp continuous_snd
    have he : Continuous (fun q : I × (I × X) ↦ logs H h (1, q.2.2)) :=
      (logs H h).continuous.comp (continuous_const.prodMk (continuous_snd.comp continuous_snd))
    exact (H.continuous.comp (continuous_const.prodMk (continuous_snd.comp continuous_snd))).mul
      (contMDiff_exp.continuous.comp
        (((continuous_const.sub hs).smul hl).add (hs.smul (ht.smul he))))

theorem replacement_zero (p : I × X) : replacement H h (0, p) = H p := by
  change H (0, p.2) * exp ((1 - (0 : ℝ)) • logs H h p +
    (0 : ℝ) • ((p.1 : ℝ) • logs H h (1, p.2))) = H p
  rw [sub_zero, one_smul, zero_smul, add_zero, exp_logs,
    ← mul_assoc, mul_inv_cancel, one_mul]

theorem replacement_one (p : I × X) : replacement H h (1, p) = segment H h p := by
  change H (0, p.2) * exp ((1 - (1 : ℝ)) • logs H h p +
    (1 : ℝ) • ((p.1 : ℝ) • logs H h (1, p.2))) = _
  rw [sub_self, zero_smul, one_smul, zero_add]
  rfl

theorem replacement_time_zero (s : I) (x : X) :
    replacement H h (s, (0, x)) = H (0, x) := by
  change H (0, x) * exp ((1 - (s : ℝ)) • logs H h (0, x) +
    (s : ℝ) • ((0 : ℝ) • logs H h (1, x))) = H (0, x)
  rw [logs_zero, smul_zero, zero_smul, smul_zero, add_zero, exp_zero, mul_one]

theorem replacement_time_one (s : I) (x : X) :
    replacement H h (s, (1, x)) = H (1, x) := by
  change H (0, x) * exp ((1 - (s : ℝ)) • logs H h (1, x) +
    (s : ℝ) • ((1 : ℝ) • logs H h (1, x))) = H (1, x)
  rw [one_smul, ← add_smul, sub_add_cancel, one_smul, exp_logs,
    ← mul_assoc, mul_inv_cancel, one_mul]

theorem replacement_stationary (s t : I) (x : X)
    (hx : ∀ u, H (u, x) = H (0, x)) : replacement H h (s, (t, x)) = H (t, x) := by
  change H (0, x) * exp ((1 - (s : ℝ)) • logs H h (t, x) +
    (s : ℝ) • ((t : ℝ) • logs H h (1, x))) = H (t, x)
  rw [logs_of_stationary H h x hx t, logs_of_stationary H h x hx 1,
    smul_zero, smul_zero, smul_zero, add_zero, exp_zero, mul_one, hx t]

/-- A native homotopy relative to both ends and any specified stationary parameters. -/
noncomputable def homotopyRel (S : Set X)
    (hS : ∀ x ∈ S, ∀ t, H (t, x) = H (0, x)) :
    H.HomotopyRel (segment H h) {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} where
  toContinuousMap := replacement H h
  map_zero_left := replacement_zero H h
  map_one_left := replacement_one H h
  prop' s p hp := by
    rcases p with ⟨t, x⟩
    rcases hp with ht | ht | hx
    · change t = 0 at ht
      subst t
      exact replacement_time_zero H h s x
    · change t = 1 at ht
      subst t
      exact replacement_time_one H h s x
    · exact replacement_stationary H h s t x (hS x hx)

end NoExoticSixSphere.OrthogonalExponential.LocalSegment

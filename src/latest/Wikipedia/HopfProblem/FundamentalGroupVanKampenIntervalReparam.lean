import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport

/-!
# Exact interval reparametrizations of paths

These are identities of actual paths, before passing to homotopy classes.
They supply the affine restriction and concatenation formulas used to
extend local path values across a subdivision of the unit interval.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-- An ordered affine parametrization of a subinterval is monotone. -/
theorem convexComb_monotone {a b : I} (hab : a ≤ b) :
    Monotone (Icc.convexComb a b) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + s * b ≤ (1 - (t : ℝ)) * a + t * b
  have hab' : (a : ℝ) ≤ b := hab
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hst')]

/-- Composing affine interval parametrizations interpolates their endpoints. -/
theorem convexComb_comp (a b s t u : I) :
    Icc.convexComb a b (Icc.convexComb s t u) =
      Icc.convexComb (Icc.convexComb a b s) (Icc.convexComb a b t) u := by
  apply Subtype.ext
  simp only [Icc.coe_convexComb]
  ring

/-- A subpath of a subpath is exactly the corresponding affine subpath.
Its endpoints are definitionally equal, so no endpoint cast is needed. -/
theorem subpath_subpath (p : Path x y) (a b s t : I) :
    (p.subpath a b).subpath s t =
      p.subpath (Icc.convexComb a b s) (Icc.convexComb a b t) := by
  ext u
  change p (Icc.convexComb a b (Icc.convexComb s t u)) =
    p (Icc.convexComb (Icc.convexComb a b s) (Icc.convexComb a b t) u)
  rw [convexComb_comp]

/-- The midpoint separating the two halves of a concatenated path. -/
def intervalHalf : I := ⟨1 / 2, by norm_num⟩

@[simp] theorem coe_intervalHalf : (intervalHalf : ℝ) = 1 / 2 := rfl

/-- The first affine half of a concatenation traverses its first path. -/
theorem trans_convexComb_first_half (p : Path x y) (q : Path y z) (t : I) :
    (p.trans q) (Icc.convexComb 0 intervalHalf t) = p t := by
  have ht : (Icc.convexComb 0 intervalHalf t : ℝ) ≤ 1 / 2 := by
    change (1 - (t : ℝ)) * 0 + t * (1 / 2) ≤ 1 / 2
    linarith [t.2.2]
  rw [← Path.extend_apply (p.trans q), Path.extend_trans_of_le_half p q ht]
  have heq : 2 * (Icc.convexComb 0 intervalHalf t : ℝ) = t := by
    change 2 * ((1 - (t : ℝ)) * 0 + t * (1 / 2)) = t
    ring
  rw [heq, Path.extend_apply]

/-- The second affine half of a concatenation traverses its second path,
including the common endpoint at time zero. -/
theorem trans_convexComb_second_half (p : Path x y) (q : Path y z) (t : I) :
    (p.trans q) (Icc.convexComb intervalHalf 1 t) = q t := by
  have ht : 1 / 2 ≤ (Icc.convexComb intervalHalf 1 t : ℝ) := by
    change 1 / 2 ≤ (1 - (t : ℝ)) * (1 / 2) + t * 1
    linarith [t.2.1]
  rw [← Path.extend_apply (p.trans q), Path.extend_trans_of_half_le p q ht]
  have heq : 2 * (Icc.convexComb intervalHalf 1 t : ℝ) - 1 = t := by
    change 2 * ((1 - (t : ℝ)) * (1 / 2) + t * 1) - 1 = t
    ring
  rw [heq, Path.extend_apply]

/-- The midpoint of a concatenation is its common endpoint. -/
@[simp] theorem trans_apply_intervalHalf (p : Path x y) (q : Path y z) :
    (p.trans q) intervalHalf = y := by
  simpa using trans_convexComb_first_half p q 1

/-- Restricting a concatenation to its first half gives its first path,
with only the endpoint equalities transported. -/
theorem trans_subpath_first_half (p : Path x y) (q : Path y z) :
    (p.trans q).subpath 0 intervalHalf =
      p.cast (p.trans q).source (trans_apply_intervalHalf p q) := by
  ext t
  exact trans_convexComb_first_half p q t

/-- Restricting a concatenation to its second half gives its second path,
with only the endpoint equalities transported. -/
theorem trans_subpath_second_half (p : Path x y) (q : Path y z) :
    (p.trans q).subpath intervalHalf 1 =
      q.cast (trans_apply_intervalHalf p q) (p.trans q).target := by
  ext t
  exact trans_convexComb_second_half p q t

end Wikipedia.HopfProblem.FundamentalGroupVanKampen

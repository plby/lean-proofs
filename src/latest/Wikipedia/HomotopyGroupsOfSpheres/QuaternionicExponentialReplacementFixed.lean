import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBrokenPaths

/-!
# Broken-path replacement fixes existing short exponential paths

Linearly varying logarithms are unchanged by logarithmic interpolation. This
applies interval by interval to a single exponential whenever its prefixes
lie in the actual logarithm target. Constant paths are not the only fixed ones.
-/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

open NoExoticSixSphere.IntervalCoordinates

namespace LocalSegment

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, symplecticSubgroup n))
  (h : ∀ p : I × X, (H (0, p.2))⁻¹ * H p ∈ compatibleDomain n)

theorem replacement_eq_of_linear_logs (s t : I) (x : X)
    (hlog : logs H h (t, x) = (t : ℝ) • logs H h (1, x)) :
    replacement H h (s, (t, x)) = H (t, x) := by
  change H (0, x) * exp ((1 - (s : ℝ)) • logs H h (t, x) +
    (s : ℝ) • ((t : ℝ) • logs H h (1, x))) = H (t, x)
  rw [hlog, ← add_smul, sub_add_cancel, one_smul, ← hlog, exp_logs,
    mul_inv_cancel_left]

theorem logs_of_exponential (x : X) (K : SkewSpace n)
    (hpath : ∀ t : I, H (t, x) = H (0, x) * exp ((t : ℝ) • K))
    (hK : ∀ t : I, (t : ℝ) • K ∈ compatibleTarget n) (t : I) :
    logs H h (t, x) = (t : ℝ) • K := by
  change logarithmChart n ((H (0, x))⁻¹ * H (t, x)) = _
  rw [hpath t, inv_mul_cancel_left, logarithmChart_exp _ (hK t).1]

theorem replacement_eq_of_exponential (s t : I) (x : X) (K : SkewSpace n)
    (hpath : ∀ u : I, H (u, x) = H (0, x) * exp ((u : ℝ) • K))
    (hK : ∀ u : I, (u : ℝ) • K ∈ compatibleTarget n) :
    replacement H h (s, (t, x)) = H (t, x) := by
  apply replacement_eq_of_linear_logs H h s t x
  rw [logs_of_exponential H h x K hpath hK t, logs_of_exponential H h x K hpath hK 1]
  change (t : ℝ) • K = (t : ℝ) • ((1 : ℝ) • K)
  rw [one_smul]

end LocalSegment

namespace IntervalReplacement

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, symplecticSubgroup n)) (s u : I)

theorem restricted_exponential (x : X) (a : symplecticSubgroup n) (K : SkewSpace n)
    (hpath : ∀ t : I, H (t, x) = a * exp ((t : ℝ) • K)) (t : I) :
    restricted H s u (t, x) = restricted H s u (0, x) *
      exp ((t : ℝ) • (((u : ℝ) - (s : ℝ)) • K)) := by
  rw [restricted_apply, restricted_zero, hpath (Icc.convexComb s u t), hpath s,
    mul_assoc, smul_smul, ← exp_add_smul]
  apply congrArg (fun c : ℝ ↦ a * exp (c • K))
  rw [Icc.coe_convexComb]
  ring

theorem restricted_prefix_target (hsu : s ≤ u) (K : SkewSpace n)
    (hK : ∀ v ∈ Icc s u, ((v : ℝ) - (s : ℝ)) • K ∈ compatibleTarget n) (t : I) :
    (t : ℝ) • (((u : ℝ) - (s : ℝ)) • K) ∈ compatibleTarget n := by
  have he : (t : ℝ) * ((u : ℝ) - (s : ℝ)) =
      (Icc.convexComb s u t : ℝ) - (s : ℝ) := by rw [Icc.coe_convexComb]; ring
  rw [smul_smul, he]
  exact hK _ ⟨Icc.le_convexComb hsu t, Icc.convexComb_le hsu t⟩

theorem correction_eq_one_of_exponential (hsu : s ≤ u)
    (hsmall : ∀ t ∈ Icc s u, ∀ x, (H (s, x))⁻¹ * H (t, x) ∈ compatibleDomain n)
    (r t : I) (x : X) (a : symplecticSubgroup n) (K : SkewSpace n)
    (hpath : ∀ v : I, H (v, x) = a * exp ((v : ℝ) • K))
    (hK : ∀ v ∈ Icc s u, ((v : ℝ) - (s : ℝ)) • K ∈ compatibleTarget n) :
    correction H s u hsu hsmall (r, (t, x)) = 1 := by
  rw [correction_apply, lifted_apply,
    LocalSegment.replacement_eq_of_exponential (restricted H s u)
      (localCondition H s u hsu hsmall) r (normalize s u t) x (((u : ℝ) - (s : ℝ)) • K)
      (restricted_exponential H s u x a K hpath) (restricted_prefix_target s u hsu K hK),
    restricted_apply, convexComb_normalize hsu, mul_inv_cancel]

end IntervalReplacement

namespace BrokenPaths

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, symplecticSubgroup n)) (t : ℕ → I) (hmono : Monotone t)
  (hsmall : ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
    (H (t i, x))⁻¹ * H (u, x) ∈ compatibleDomain n) (N : ℕ)

theorem deformation_exponential (r v : I) (x : X) (K : SkewSpace n)
    (hpath : ∀ u : I, H (u, x) = H (0, x) * exp ((u : ℝ) • K))
    (hK : ∀ i < N, ∀ u ∈ Icc (t i) (t (i + 1)),
      ((u : ℝ) - (t i : ℝ)) • K ∈ compatibleTarget n) :
    deformation H t hmono hsmall N (r, (v, x)) = H (v, x) := by
  apply deformation_eq_of_corrections_eq_one
  intro i hi
  exact IntervalReplacement.correction_eq_one_of_exponential H (t i) (t (i + 1))
    (hmono i.le_succ) (hsmall i) r v x (H (0, x)) K hpath (hK i hi)

noncomputable def homotopyRel_exponential (S : Set X)
    (hS : ∀ x ∈ S, ∃ K : SkewSpace n,
      (∀ u : I, H (u, x) = H (0, x) * exp ((u : ℝ) • K)) ∧
      ∀ i < N, ∀ u ∈ Icc (t i) (t (i + 1)),
        ((u : ℝ) - (t i : ℝ)) • K ∈ compatibleTarget n) :
    H.HomotopyRel (ending H t hmono hsmall N) {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} where
  toContinuousMap := deformation H t hmono hsmall N
  map_zero_left := deformation_zero H t hmono hsmall N
  map_one_left _ := rfl
  prop' r p hp := by
    rcases p with ⟨v, x⟩
    rcases hp with hv | hv | hx
    · change v = 0 at hv
      subst v
      exact deformation_time_zero H t hmono hsmall N r x
    · change v = 1 at hv
      subst v
      exact deformation_time_one H t hmono hsmall N r x
    · obtain ⟨K, hpath, hK⟩ := hS x hx
      exact deformation_exponential H t hmono hsmall N r v x K hpath hK

end BrokenPaths

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

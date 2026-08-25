import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportAlgebra
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.NormalForm
import StackExchange.Puzzling139335.ReflectionSeparation.Generic

/-!
# A unit support segment of a reflected pair

The piece is a Jordan region in the upward strip over its actual unit base.
Two distinct common points with its reflected copy force either reflection
in the base itself or an upward supporting halfplane for their entire union.
No convexity or boundary-length assumption is used.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

theorem fixed_of_normalValue_eq (e : Plane ≃ᵃⁱ[ℝ] Plane) {ν : Plane} {c : ℝ}
    (hform : ∀ x, e x = x - (2 * (normalValue ν x - c)) • ν)
    {x : Plane} (hx : normalValue ν x = c) : e x = x := by
  rw [hform, hx, sub_self, mul_zero, zero_smul, sub_zero]

/-- Orient the normal so that the whole Jordan region lies on its upper side. -/
theorem exists_oriented_normal {P Q : Set Plane} (hP : IsJordanRegion P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) {ν : Plane} {c : ℝ}
    (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1)
    (hform : ∀ x, e x = x - (2 * (normalValue ν x - c)) • ν) :
    ∃ (μ : Plane) (k : ℝ), μ 0 ^ 2 + μ 1 ^ 2 = 1 ∧
      (∀ x, e x = x - (2 * (normalValue μ x - k)) • μ) ∧
      ∀ x ∈ P, k ≤ normalValue μ x := by
  obtain hle | hge := ReflectionSeparation.subset_le_or_ge_of_fixed_level
    hP e he hdis (normalValue ν) (continuous_normalValue ν) c
    (fun _ hx => fixed_of_normalValue_eq e hform hx)
  · refine ⟨-ν, -c, ?_, ?_, ?_⟩
    · simpa only [PiLp.neg_apply, neg_sq] using hunit
    · intro x
      exact (hform x).trans (reflect_formula_neg ν x c).symm
    · intro x hx
      have h : normalValue ν x ≤ c := hle hx
      change -c ≤ normalValue (-ν) x
      rw [normalValue_neg_left]
      linarith
  · exact ⟨ν, c, hunit, hform, fun x hx => hge hx⟩

/-- Common points of oppositely placed reflected pieces are on the mirror. -/
theorem normalValue_eq_of_mem_inter {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) {ν : Plane} {c : ℝ}
    (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1)
    (hform : ∀ x, e x = x - (2 * (normalValue ν x - c)) • ν)
    (hside : ∀ x ∈ P, c ≤ normalValue ν x) {x : Plane} (hx : x ∈ P ∩ Q) :
    normalValue ν x = c := by
  obtain ⟨y, hy, rfl⟩ := he.symm ▸ hx.2
  have hxy : normalValue ν (e y) = 2 * c - normalValue ν y := by
    rw [hform, normalValue_reflect ν y c hunit]
  have hleft := hside (e y) hx.1
  have hright := hside y hy
  linarith

/-- In the upward strip, two common points leave only the base mirror or
an upward supporting halfplane for the entire reflected pair. -/
theorem normal_reflection_unit_base_dichotomy {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) {ν : Plane} {c : ℝ}
    (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1)
    (hform : ∀ x, e x = x - (2 * (normalValue ν x - c)) • ν)
    (hstrip : ∀ x ∈ P, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1)
    (hbase : segment ℝ (corner 0) (corner 1) ⊆ P)
    (hcommon : (P ∩ Q).Nontrivial) :
    (∀ x, e x = (!₂[x 0, -x 1] : Plane)) ∨
      ∀ x ∈ P ∪ Q, 0 ≤ x 1 := by
  obtain ⟨μ, k, hμ, heμ, hside⟩ :=
    exists_oriented_normal hP e he hdis hunit hform
  by_cases hμy : 0 < μ 1
  · left
    obtain ⟨p, hp, q, hq, hpq⟩ := hcommon
    have hpc := normalValue_eq_of_mem_inter e he hμ heμ hside hp
    have hqc := normalValue_eq_of_mem_inter e he hμ heμ hside hq
    obtain ⟨hμx, hk⟩ := support_two_contacts hμy hstrip
      (hbase (left_mem_segment ℝ (corner 0) (corner 1)))
      (hbase (right_mem_segment ℝ (corner 0) (corner 1)))
      hside hp.1 hq.1 hpq hpc hqc
    have hμysq : μ 1 ^ 2 = 1 := by simpa [hμx] using hμ
    intro x
    rw [heμ]
    apply PlaneIsometries.plane_ext
    · simp [normalValue, hμx, hk]
    · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        normalValue, hμx, zero_mul, zero_add, hk, sub_zero,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination -2 * x 1 * hμysq
  · right
    intro x hx
    rcases hx with hx | hx
    · exact (hstrip x hx).2.2
    · obtain ⟨y, hy, rfl⟩ := he.symm ▸ hx
      rw [heμ]
      exact reflect_y_nonneg (le_of_not_gt hμy) (hstrip y hy).2.2 (hside y hy)

/-- In the base-reflection case the common interface is exactly the full
actual unit base, rather than an arbitrary subset of its supporting line. -/
theorem inter_eq_base_of_base_reflection {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hstrip : ∀ x ∈ P, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1)
    (hbase : segment ℝ (corner 0) (corner 1) ⊆ P)
    (hform : ∀ x, e x = (!₂[x 0, -x 1] : Plane)) :
    P ∩ Q = segment ℝ (corner 0) (corner 1) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hey⟩ := he.symm ▸ hx.2
    have hyx := congrArg (fun z : Plane => z 1) hey
    rw [hform] at hyx
    change -y 1 = x 1 at hyx
    have hxzero : x 1 = 0 := by
      linarith [(hstrip x hx.1).2.2, (hstrip y hy).2.2]
    change x ∈ segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0)
    rw [Schoenflies.mem_segment_horiz,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    exact ⟨hxzero, (hstrip x hx.1).1, (hstrip x hx.1).2.1⟩
  · intro x hx
    refine ⟨hbase hx, ?_⟩
    have hxzero : x 1 = 0 := by
      change x ∈ segment ℝ (Schoenflies.Plane.mk 0 0)
        (Schoenflies.Plane.mk 1 0) at hx
      exact (Schoenflies.mem_segment_horiz.mp hx).1
    rw [← he]
    refine ⟨x, hbase hx, ?_⟩
    rw [hform]
    ext i
    fin_cases i <;> simp [hxzero]

/-- The ordinary complex-axis form is sufficient; the normal is derived,
not included as an extra geometric assumption. -/
theorem reflection_unit_base_dichotomy {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) (c : ℂ) (u : Circle)
    (hform : ∀ p, PlaneIsometries.complexEquiv (e p) =
      c + (u : ℂ) * starRingEnd ℂ ((PlaneIsometries.complexEquiv p - c) / (u : ℂ)))
    (hstrip : ∀ x ∈ P, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1)
    (hbase : segment ℝ (corner 0) (corner 1) ⊆ P)
    (hcommon : (P ∩ Q).Nontrivial) :
    (∀ x, e x = (!₂[x 0, -x 1] : Plane)) ∨
      ∀ x ∈ P ∪ Q, 0 ≤ x 1 := by
  obtain ⟨ν, k, hν, heν⟩ := exists_unit_normal_form e c u hform
  exact normal_reflection_unit_base_dichotomy hP e he hdis hν heν hstrip hbase hcommon

end Puzzling139335.N4MiddleInvolutions.Reflection

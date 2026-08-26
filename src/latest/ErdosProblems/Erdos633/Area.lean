import ErdosProblems.Erdos633.Geometry
import ErdosProblems.Erdos633.Arithmetic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual area additivity for congruent triangle tilings

The area equation here is derived from the geometric definition of a tiling,
including arbitrary T-junctions. It is not supplied as a hypothesis.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators ENNReal

theorem Triangle.convex_carrier (T : Triangle) : Convex ℝ T.carrier :=
  convex_convexHull ℝ _

theorem Triangle.isCompact_carrier (T : Triangle) : IsCompact T.carrier := by
  exact (Set.toFinite {T.a, T.b, T.c}).isCompact_convexHull ℝ

theorem Triangle.volume_lt_top (T : Triangle) : volume T.carrier < ⊤ :=
  T.isCompact_carrier.measure_lt_top

theorem Triangle.volume_frontier (T : Triangle) : volume (frontier T.carrier) = 0 :=
  T.convex_carrier.addHaar_frontier volume

noncomputable def Triangle.area (T : Triangle) : ℝ := (volume T.carrier).toReal

/-- The determinant nondegeneracy condition really gives affine independence. -/
theorem Triangle.affineIndependent (T : Triangle) :
    AffineIndependent ℝ ![T.a, T.b, T.c] := by
  apply (affineIndependent_iff_of_fintype ℝ _).mpr
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hw hv
  change w 0 + (w 1 + w 2) = 0 at hw
  change w 0 • T.a + (w 1 • T.b + w 2 • T.c) = 0 at hv
  have hre := congrArg Complex.re hv
  have him := congrArg Complex.im hv
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.zero_re, Complex.zero_im, smul_eq_mul] at hre him
  let d := (T.b - T.a).re * (T.c - T.a).im - (T.b - T.a).im * (T.c - T.a).re
  have hd : d ≠ 0 := T.nondegenerate
  have h1 : w 1 * d = 0 := by
    dsimp [d]
    linear_combination
      (T.c.im - T.a.im) * hre - (T.c.re - T.a.re) * him -
        (T.a.re * T.c.im - T.a.im * T.c.re) * hw
  have h2 : w 2 * d = 0 := by
    dsimp [d]
    linear_combination
      (T.b.re - T.a.re) * him - (T.b.im - T.a.im) * hre +
        (T.a.re * T.b.im - T.a.im * T.b.re) * hw
  have hw1 : w 1 = 0 := (mul_eq_zero.mp h1).resolve_right hd
  have hw2 : w 2 = 0 := (mul_eq_zero.mp h2).resolve_right hd
  have hw0 : w 0 = 0 := by linarith
  fin_cases i <;> assumption

theorem Triangle.interior_nonempty (T : Triangle) : (interior T.carrier).Nonempty := by
  apply T.convex_carrier.interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [Triangle.carrier, affineSpan_convexHull]
  have hrange : Set.range ![T.a, T.b, T.c] = {T.a, T.b, T.c} := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hrange, T.affineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  norm_num [Complex.finrank_real_complex]

theorem Triangle.area_pos (T : Triangle) : 0 < T.area := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt (Measure.measure_pos_of_nonempty_interior volume T.interior_nonempty)
  · exact ne_of_lt T.volume_lt_top

theorem isometry_volume_image (f : ℂ ≃ᵢ ℂ) (s : Set ℂ) : volume (f '' s) = volume s := by
  have heq : (Measure.euclideanHausdorffMeasure (Module.finrank ℝ ℂ) : Measure ℂ) =
      volume := InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [← heq]
  exact f.isometry.euclideanHausdorffMeasure_image s

theorem aedisjoint_of_disjoint_interiors (P Q : Triangle)
    (h : Disjoint (interior P.carrier) (interior Q.carrier)) :
    AEDisjoint volume P.carrier Q.carrier := by
  have hsub : P.carrier ∩ Q.carrier ⊆ frontier P.carrier ∪ frontier Q.carrier := by
    intro z hz
    by_cases hp : z ∈ interior P.carrier
    · right
      exact ⟨subset_closure hz.2, fun hq => Set.disjoint_left.mp h hp hq⟩
    · left
      exact ⟨subset_closure hz.1, hp⟩
  exact measure_mono_null hsub (measure_union_null P.volume_frontier Q.volume_frontier)

/-- Area additivity does not require congruence of the pieces. -/
theorem TriangleDissection.volume_eq_sum {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) : volume P.carrier = ∑ i, volume (T.tile i).carrier := by
  have hd : Pairwise fun i j => AEDisjoint volume (T.tile i).carrier (T.tile j).carrier := by
    intro i j hij
    exact aedisjoint_of_disjoint_interiors _ _ (T.disjoint hij)
  have hm : ∀ i, NullMeasurableSet (T.tile i).carrier volume :=
    fun i => (T.tile i).convex_carrier.nullMeasurableSet (μ := volume)
  rw [← T.covers, measure_iUnion₀ hd hm, tsum_fintype]

theorem TriangleDissection.area_eq_sum {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) : P.area = ∑ i, (T.tile i).area := by
  unfold Triangle.area
  rw [T.volume_eq_sum, ENNReal.toReal_sum]
  intro i _
  exact ne_of_lt (T.tile i).volume_lt_top

/-- The number of congruent pieces is the multiplicative factor in area. -/
theorem CongruentTiling.volume_eq {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : volume P.carrier = N * volume R.carrier := by
  have hv : ∀ i, volume (T.tile i).carrier = volume R.carrier := by
    intro i
    obtain ⟨f, hf⟩ := T.congruent i
    rw [← hf]
    exact isometry_volume_image f R.carrier
  rw [T.toTriangleDissection.volume_eq_sum]
  simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem CongruentTiling.area_eq {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : P.area = N * R.area := by
  unfold Triangle.area
  rw [T.volume_eq, ENNReal.toReal_mul, ENNReal.toReal_natCast]

theorem CongruentTiling.card_pos {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : 0 < N := by
  by_contra hN
  have hzero : N = 0 := by omega
  have heq := T.area_eq
  rw [hzero, Nat.cast_zero, zero_mul] at heq
  exact (ne_of_gt P.area_pos) heq

/-- There is no extra nonvanishing hypothesis: triangle nondegeneracy already
ensures that division by the tile area is legitimate. -/
theorem CongruentTiling.area_ratio {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : P.area / R.area = N := by
  rw [T.area_eq, mul_div_cancel_right₀ _ (ne_of_gt R.area_pos)]

theorem CongruentTiling.card_unique {P R : Triangle} {N M : ℕ}
    (T : CongruentTiling P R N) (S : CongruentTiling P R M) : N = M := by
  have h : (N : ℝ) = M := T.area_ratio.symm.trans S.area_ratio
  exact_mod_cast h

/-- The geometric tiling, rather than an assumed counting identity, supplies
the area equation used in the rational-square test. -/
theorem CongruentTiling.count_isSquare_iff {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (r q : ℚ) (hr : r ≠ 0)
    (harea : P.area = ((r ^ 2 * q : ℚ) : ℝ) * R.area) :
    IsSquare N ↔ IsSquare q := by
  have hreal : (N : ℝ) = ((r ^ 2 * q : ℚ) : ℝ) := by
    apply mul_right_cancel₀ (ne_of_gt R.area_pos)
    exact T.area_eq.symm.trans harea
  have hrat : (N : ℚ) = r ^ 2 * q := by exact_mod_cast hreal
  exact Erdos633.count_isSquare_iff N r q hr hrat

theorem CongruentTiling.groupOne_U_count_not_isSquare {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (r s : ℚ) (hr : r ≠ 0)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (harea : P.area = ((r ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2)) : ℚ) : ℝ) * R.area) :
    ¬ IsSquare N := by
  intro hN
  exact groupOne_U_not_isSquare s hs0 hs1 ((T.count_isSquare_iff r _ hr harea).mp hN)

end Erdos633

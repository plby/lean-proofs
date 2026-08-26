import ErdosProblems.Erdos633.LocalAngleLedger
import ErdosProblems.Erdos633.AngleCounting

/-!
# The angle-counting obstruction for actual geometric tilings

All counts and local multipliers in this file are extracted from the given
congruent tiling. The local angle equations and their global conservation
laws are theorems, rather than additional tiling hypotheses.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def CongruentTiling.nonouterVertices {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : Finset ℂ := by
  classical
  exact T.labelledDissection.vertexFinset \ P.outerVertexFinset

theorem CongruentTiling.mem_nonouterVertices {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) :
    z ∈ T.nonouterVertices ↔ z ∈ T.labelledDissection.vertexFinset ∧
      z ∉ Set.range P.vertex := by
  classical
  simp [CongruentTiling.nonouterVertices, Triangle.outerVertexFinset, Set.mem_range]

theorem CongruentTiling.nonouter_cornerCount_total_subtype {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) :
    (∑ z : T.nonouterVertices, T.cornerCount z k) + T.outerCornerCount k = N := by
  classical
  have hs : (∑ z : T.nonouterVertices, T.cornerCount z k) =
      ∑ z ∈ T.nonouterVertices, T.cornerCount z k :=
    Finset.sum_coe_sort T.nonouterVertices (fun z : ℂ => T.cornerCount z k)
  rw [hs]
  exact T.nonouter_cornerCount_total k

theorem CongruentTiling.nonouter_local_angle_equation {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : T.nonouterVertices) :
    (T.cornerCount z 0 : ℝ) * R.angleA + (T.cornerCount z 1 : ℝ) * R.angleB +
      (T.cornerCount z 2 : ℝ) * R.angleC = (T.localAngleMultiplier z : ℝ) * Real.pi := by
  have hz := (T.mem_nonouterVertices z).mp z.property
  have h := T.localAngleMultiplier_equation z hz.1 hz.2
  norm_num [CongruentTiling.angleSumAt, Triangle.cornerAngle, Fin.sum_univ_succ] at h
  simpa only [← add_assoc] using h

theorem CongruentTiling.sum_nonouter_angle_multipliers {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) :
    (∑ z ∈ T.nonouterVertices, T.localAngleMultiplier z) + 1 = N := by
  classical
  have houter : ∑ z ∈ P.outerVertexFinset, T.angleSumAt z = Real.pi := by
    calc
      _ = ∑ j : Fin 3, T.angleSumAt (P.vertex j) := by
        unfold Triangle.outerVertexFinset
        apply Finset.sum_image
        intro i _ j _ hij
        exact P.vertex_injective hij
      _ = Real.pi := by simp_rw [T.outer_angleSumAt]; exact P.sum_cornerAngle
  have hsum : (∑ z ∈ T.nonouterVertices, T.angleSumAt z) + Real.pi = N * Real.pi := by
    nth_rw 1 [← houter]
    unfold CongruentTiling.nonouterVertices
    rw [Finset.sum_sdiff T.labelledDissection.outerVertexFinset_subset]
    exact T.sum_angleSumAt
  have hlocal : (∑ z ∈ T.nonouterVertices, T.angleSumAt z) =
      ((∑ z ∈ T.nonouterVertices, T.localAngleMultiplier z : ℕ) : ℝ) * Real.pi := by
    calc
      _ = ∑ z ∈ T.nonouterVertices, (T.localAngleMultiplier z : ℝ) * Real.pi := by
        apply Finset.sum_congr rfl
        intro z hz
        have h := (T.mem_nonouterVertices z).mp hz
        exact T.localAngleMultiplier_equation z h.1 h.2
      _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum]
  rw [hlocal] at hsum
  have hr : (((∑ z ∈ T.nonouterVertices, T.localAngleMultiplier z : ℕ) : ℝ) + 1) *
      Real.pi = (N : ℝ) * Real.pi := by linarith
  have he := mul_right_cancel₀ (ne_of_gt Real.pi_pos) hr
  exact_mod_cast he

theorem CongruentTiling.actual_angle_relation_bound {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hind : IntegerIndependentAngles R.angleA R.angleB)
    (p q : ℕ) (hrel : R.angleC = p * R.angleA + q * R.angleB)
    (ha : T.outerCornerCount 0 = p + 1) (hb : T.outerCornerCount 1 = q + 1)
    (hg : T.outerCornerCount 2 = 0) : p ≤ 2 ∧ q ≤ 2 := by
  classical
  refine angle_relation_bound_of_angle_sums hind p q N
    (fun z : T.nonouterVertices => T.cornerCount z 0)
    (fun z : T.nonouterVertices => T.cornerCount z 1)
    (fun z : T.nonouterVertices => T.cornerCount z 2)
    (fun z : T.nonouterVertices => T.localAngleMultiplier z)
    R.angle_sum hrel ?_ ?_ ?_ ?_ ?_
  · intro z
    exact (T.localAngleMultiplier_bounds z).2
  · exact T.nonouter_local_angle_equation
  · simpa only [ha] using T.nonouter_cornerCount_total_subtype 0
  · simpa only [hb] using T.nonouter_cornerCount_total_subtype 1
  · simpa only [hg, add_zero] using T.nonouter_cornerCount_total_subtype 2

theorem CongruentTiling.missing_outer_angle_relation {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (ha : 0 < T.outerCornerCount 0)
    (hb : 0 < T.outerCornerCount 1) (hg : T.outerCornerCount 2 = 0) :
    R.angleC = ((T.outerCornerCount 0 - 1 : ℕ) : ℝ) * R.angleA +
      ((T.outerCornerCount 1 - 1 : ℕ) : ℝ) * R.angleB := by
  have ha' : T.outerCornerCount 0 = (T.outerCornerCount 0 - 1) + 1 := by omega
  have hb' : T.outerCornerCount 1 = (T.outerCornerCount 1 - 1) + 1 := by omega
  have hout := T.outer_angle_total
  norm_num [Fin.sum_univ_succ, Triangle.cornerAngle, hg] at hout
  rw [ha', hb'] at hout
  push_cast at hout
  linear_combination R.angle_sum - hout

theorem CongruentTiling.outer_counts_le_three_of_missing {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hind : IntegerIndependentAngles R.angleA R.angleB)
    (ha : 0 < T.outerCornerCount 0) (hb : 0 < T.outerCornerCount 1)
    (hg : T.outerCornerCount 2 = 0) :
    T.outerCornerCount 0 ≤ 3 ∧ T.outerCornerCount 1 ≤ 3 := by
  have h := T.actual_angle_relation_bound hind (T.outerCornerCount 0 - 1)
    (T.outerCornerCount 1 - 1) (T.missing_outer_angle_relation ha hb hg)
    (by omega) (by omega) hg
  omega

theorem CongruentTiling.outer_counts_eq_one_of_all_pos {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hpos : ∀ k : Fin 3, 0 < T.outerCornerCount k) :
    ∀ k : Fin 3, T.outerCornerCount k = 1 := by
  have hnonneg (k : Fin 3) : 0 ≤ ((T.outerCornerCount k : ℝ) - 1) * R.cornerAngle k := by
    apply mul_nonneg _ (R.cornerAngle_pos k).le
    have hk : (1 : ℝ) ≤ T.outerCornerCount k := by exact_mod_cast hpos k
    linarith
  have hsum : ∑ k : Fin 3, ((T.outerCornerCount k : ℝ) - 1) * R.cornerAngle k = 0 := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, T.outer_angle_total, R.sum_cornerAngle, sub_self]
  intro k
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum k
    (Finset.mem_univ k)
  have hp := R.cornerAngle_pos k
  have he : (T.outerCornerCount k : ℝ) = 1 := by
    rcases mul_eq_zero.mp ht with h | h
    · linarith
    · exact False.elim ((ne_of_gt hp) h)
  exact_mod_cast he

/-- In the all-positive case the actual three outer angles are a permutation
of the reference angles, not just a multiset with matching total sum. -/
theorem CongruentTiling.outer_angles_permuted_of_all_pos {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hpos : ∀ k : Fin 3, 0 < T.outerCornerCount k) :
    ∃ e : Equiv.Perm (Fin 3), ∀ j, P.cornerAngle j = R.cornerAngle (e j) := by
  classical
  obtain ⟨e, he⟩ := corner_matrix_is_permutation
    (fun j k => T.cornerCount (P.vertex j) k)
    (T.outer_counts_eq_one_of_all_pos hpos) T.outer_cornerCount_pos
  refine ⟨e, ?_⟩
  intro j
  have h := T.outer_angle_count_identity j
  simp_rw [he] at h
  simpa using h.symm

theorem CongruentTiling.single_outer_corner_pos {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hb : T.outerCornerCount 1 = 0)
    (hg : T.outerCornerCount 2 = 0) (j : Fin 3) :
    0 < T.cornerCount (P.vertex j) 0 := by
  obtain ⟨k, hk⟩ := T.outer_cornerCount_pos j
  have hbj := T.cornerCount_eq_zero_of_outer_eq_zero j 1 hb
  have hgj := T.cornerCount_eq_zero_of_outer_eq_zero j 2 hg
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl <;> omega

/-- A single outer angle type has multiplicity exactly three. -/
theorem CongruentTiling.single_outer_count_eq_three {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hind : IntegerIndependentAngles R.angleA R.angleB)
    (hb : T.outerCornerCount 1 = 0) (hg : T.outerCornerCount 2 = 0) :
    T.outerCornerCount 0 = 3 := by
  classical
  have hpos := T.single_outer_corner_pos hb hg
  have hsum : T.cornerCount (P.vertex 0) 0 + T.cornerCount (P.vertex 1) 0 +
      T.cornerCount (P.vertex 2) 0 = T.outerCornerCount 0 := by
    norm_num [CongruentTiling.outerCornerCount, Fin.sum_univ_succ]
    omega
  have hm : 3 ≤ T.outerCornerCount 0 := by
    have h0 := hpos 0
    have h1 := hpos 1
    have h2 := hpos 2
    omega
  have hout := T.outer_angle_total
  norm_num [Fin.sum_univ_succ, Triangle.cornerAngle, hb, hg] at hout
  have hlocal (z : T.nonouterVertices) :=
    (single_outer_local_equations hind (T.outerCornerCount 0)
      (T.localAngleMultiplier z) (T.cornerCount z 0) (T.cornerCount z 1)
      (T.cornerCount z 2) (by omega) R.angle_sum hout
      (T.nonouter_local_angle_equation z)).1
  have hm' : T.outerCornerCount 0 - 1 + 1 = T.outerCornerCount 0 := by omega
  have hbound := angle_relation_coefficient_le_two (T.outerCornerCount 0 - 1) N
    (fun z : T.nonouterVertices => T.cornerCount z 0)
    (fun z : T.nonouterVertices => T.cornerCount z 2)
    (fun z : T.nonouterVertices => T.localAngleMultiplier z)
    (fun z => (T.localAngleMultiplier_bounds z).2)
    (fun z => by simpa only [hm'] using hlocal z)
    (by have h := T.nonouter_cornerCount_total_subtype 0; omega)
    (by simpa only [hg, add_zero] using T.nonouter_cornerCount_total_subtype 2)
  omega

/-- The single-type case is an equilateral outer triangle, with no assumption
that tile edges meet edge-to-edge. -/
theorem CongruentTiling.outer_angles_eq_pi_div_three_of_single_type
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hind : IntegerIndependentAngles R.angleA R.angleB)
    (hb : T.outerCornerCount 1 = 0) (hg : T.outerCornerCount 2 = 0) :
    ∀ j : Fin 3, P.cornerAngle j = Real.pi / 3 := by
  have hc := T.single_outer_count_eq_three hind hb hg
  have hpos := T.single_outer_corner_pos hb hg
  have hsum := hc
  norm_num [CongruentTiling.outerCornerCount, Fin.sum_univ_succ] at hsum
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have hcount (j : Fin 3) : T.cornerCount (P.vertex j) 0 = 1 := by
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl <;> omega
  have hout := T.outer_angle_total
  norm_num [Fin.sum_univ_succ, Triangle.cornerAngle, hb, hg, hc] at hout
  intro j
  have h := T.outer_angle_count_identity j
  have hbj := T.cornerCount_eq_zero_of_outer_eq_zero j 1 hb
  have hgj := T.cornerCount_eq_zero_of_outer_eq_zero j 2 hg
  norm_num [Fin.sum_univ_succ, Triangle.cornerAngle, hcount j, hbj, hgj] at h
  change R.angleA = P.cornerAngle j at h
  linarith

end Erdos633

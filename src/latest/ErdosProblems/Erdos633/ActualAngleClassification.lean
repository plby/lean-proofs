import ErdosProblems.Erdos633.ActualAngleCounting
import ErdosProblems.Erdos633.AnglePartitions
import ErdosProblems.Erdos633.Rationality

/-!
# Angle classification extracted from actual congruent tilings

Reference labels are permuted in the established ledger itself. No claim is
made that changing the reference triangle preserves the isometries selected
by choice in the definition of the labelled tiling.
-/

namespace Erdos633

open scoped BigOperators

/-- Every angle is a rational multiple of pi. -/
def Triangle.CommensurableAngles (P : Triangle) : Prop :=
  ∀ j, P.cornerAngle j / Real.pi ∈ rationalReals

/-- The outer angle equations preserve rational multiples of pi. -/
theorem CongruentTiling.commensurableAngles_of_tile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : R.CommensurableAngles) : P.CommensurableAngles := by
  intro j
  rw [← T.outer_angle_count_identity j, Finset.sum_div]
  apply rationalReals.sum_mem
  intro k _
  rw [mul_div_assoc]
  exact rationalReals.mul_mem (rationalReals_nat (T.cornerCount (P.vertex j) k)) (hR k)

/-- A two-type outer angle equation turns any integer dependence into
rational multiples of pi for all three reference angles. -/
theorem independent_angles_of_noncommensurable (α β γ : ℝ) (hα : 0 < α)
    (hsum : α + β + γ = Real.pi)
    (hnot : ¬(α / Real.pi ∈ rationalReals ∧ β / Real.pi ∈ rationalReals ∧
      γ / Real.pi ∈ rationalReals))
    (u v : ℕ) (hout : (u : ℝ) * α + (v : ℝ) * β = Real.pi) :
    IntegerIndependentAngles α β := by
  intro x y hxy
  by_cases hy : y = 0
  · subst y
    norm_num at hxy
    have hx : x = 0 := hxy.resolve_right (ne_of_gt hα)
    exact ⟨hx, rfl⟩
  · exfalso
    let d : ℤ := (u : ℤ) * y - (v : ℤ) * x
    have hda : (d : ℝ) * α = (y : ℝ) * Real.pi := by
      dsimp [d]
      push_cast
      linear_combination (y : ℝ) * hout - (v : ℝ) * hxy
    have hdb : (d : ℝ) * β = -(x : ℝ) * Real.pi := by
      dsimp [d]
      push_cast
      linear_combination (u : ℝ) * hxy - (x : ℝ) * hout
    have hd : (d : ℝ) ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hda
      have hyR : (y : ℝ) = 0 :=
        (mul_eq_zero.mp hda.symm).resolve_right (ne_of_gt Real.pi_pos)
      exact hy (by exact_mod_cast hyR)
    have haQ : α / Real.pi ∈ rationalReals := by
      have he : α / Real.pi = (y : ℝ) / (d : ℝ) := by
        apply (div_eq_div_iff (ne_of_gt Real.pi_pos) hd).mpr
        nlinarith only [hda]
      rw [he]
      exact rationalReals.div_mem (rationalReals_int y) (rationalReals_int d)
    have hbQ : β / Real.pi ∈ rationalReals := by
      have he : β / Real.pi = -(x : ℝ) / (d : ℝ) := by
        apply (div_eq_div_iff (ne_of_gt Real.pi_pos) hd).mpr
        nlinarith only [hdb]
      rw [he]
      exact rationalReals.div_mem (rationalReals.neg_mem (rationalReals_int x))
        (rationalReals_int d)
    have hcQ : γ / Real.pi ∈ rationalReals := by
      have he : γ / Real.pi = 1 - α / Real.pi - β / Real.pi := by
        field_simp [ne_of_gt Real.pi_pos]
        linarith
      rw [he]
      exact rationalReals.sub_mem (rationalReals.sub_mem rationalReals.one_mem haQ) hbQ
    exact hnot ⟨haQ, hbQ, hcQ⟩

theorem Triangle.sum_cornerAngle_permuted (P : Triangle) (e : Equiv.Perm (Fin 3)) :
    P.cornerAngle (e 0) + P.cornerAngle (e 1) + P.cornerAngle (e 2) = Real.pi := by
  rw [sum_three_permuted, P.sum_cornerAngle]

theorem Triangle.independent_angles_of_not_commensurable (R : Triangle)
    (e : Equiv.Perm (Fin 3)) (hR : ¬ R.CommensurableAngles) (u v : ℕ)
    (hout : (u : ℝ) * R.cornerAngle (e 0) + (v : ℝ) * R.cornerAngle (e 1) = Real.pi) :
    IntegerIndependentAngles (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) := by
  apply independent_angles_of_noncommensurable _ _ _ (R.cornerAngle_pos (e 0))
    (R.sum_cornerAngle_permuted e) _ u v hout
  intro h
  apply hR
  intro j
  have hall (i : Fin 3) : R.cornerAngle (e i) / Real.pi ∈ rationalReals := by
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  simpa using hall (e.symm j)

theorem CongruentTiling.outer_angle_total_permuted {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : Equiv.Perm (Fin 3)) :
    (T.outerCornerCount (e 0) : ℝ) * R.cornerAngle (e 0) +
      (T.outerCornerCount (e 1) : ℝ) * R.cornerAngle (e 1) +
      (T.outerCornerCount (e 2) : ℝ) * R.cornerAngle (e 2) = Real.pi := by
  exact (sum_three_permuted (fun k => (T.outerCornerCount k : ℝ) * R.cornerAngle k) e).trans
    T.outer_angle_total

theorem CongruentTiling.independent_angles_of_missing {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : Equiv.Perm (Fin 3))
    (hR : ¬ R.CommensurableAngles) (hg : T.outerCornerCount (e 2) = 0) :
    IntegerIndependentAngles (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) := by
  apply R.independent_angles_of_not_commensurable e hR
    (T.outerCornerCount (e 0)) (T.outerCornerCount (e 1))
  have h := T.outer_angle_total_permuted e
  simpa only [hg, Nat.cast_zero, zero_mul, add_zero] using h

theorem CongruentTiling.outer_angle_count_identity_permuted {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (T.cornerCount (P.vertex j) (e 0) : ℝ) * R.cornerAngle (e 0) +
      (T.cornerCount (P.vertex j) (e 1) : ℝ) * R.cornerAngle (e 1) +
      (T.cornerCount (P.vertex j) (e 2) : ℝ) * R.cornerAngle (e 2) = P.cornerAngle j := by
  exact (sum_three_permuted
    (fun k => (T.cornerCount (P.vertex j) k : ℝ) * R.cornerAngle k) e).trans
      (T.outer_angle_count_identity j)

theorem CongruentTiling.nonouter_local_angle_equation_permuted
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (e : Equiv.Perm (Fin 3)) (z : T.nonouterVertices) :
    (T.cornerCount z (e 0) : ℝ) * R.cornerAngle (e 0) +
      (T.cornerCount z (e 1) : ℝ) * R.cornerAngle (e 1) +
      (T.cornerCount z (e 2) : ℝ) * R.cornerAngle (e 2) =
        (T.localAngleMultiplier z : ℝ) * Real.pi := by
  have hz := (T.mem_nonouterVertices z).mp z.property
  exact (sum_three_permuted (fun k => (T.cornerCount z k : ℝ) * R.cornerAngle k) e).trans
    (T.localAngleMultiplier_equation z hz.1 hz.2)

theorem CongruentTiling.outer_counts_le_three_of_missing_permuted
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (e : Equiv.Perm (Fin 3))
    (hind : IntegerIndependentAngles (R.cornerAngle (e 0)) (R.cornerAngle (e 1)))
    (ha : 0 < T.outerCornerCount (e 0)) (hb : 0 < T.outerCornerCount (e 1))
    (hg : T.outerCornerCount (e 2) = 0) :
    T.outerCornerCount (e 0) ≤ 3 ∧ T.outerCornerCount (e 1) ≤ 3 := by
  classical
  have hrel : R.cornerAngle (e 2) =
      ((T.outerCornerCount (e 0) - 1 : ℕ) : ℝ) * R.cornerAngle (e 0) +
      ((T.outerCornerCount (e 1) - 1 : ℕ) : ℝ) * R.cornerAngle (e 1) := by
    have hs := R.sum_cornerAngle_permuted e
    have ho := T.outer_angle_total_permuted e
    rw [hg] at ho
    norm_num at ho
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
    linear_combination hs - ho
  have hbound := angle_relation_bound_of_angle_sums hind
    (T.outerCornerCount (e 0) - 1) (T.outerCornerCount (e 1) - 1) N
    (fun z : T.nonouterVertices => T.cornerCount z (e 0))
    (fun z : T.nonouterVertices => T.cornerCount z (e 1))
    (fun z : T.nonouterVertices => T.cornerCount z (e 2))
    (fun z : T.nonouterVertices => T.localAngleMultiplier z)
    (R.sum_cornerAngle_permuted e) hrel
    (fun z => (T.localAngleMultiplier_bounds z).2)
    (T.nonouter_local_angle_equation_permuted e)
    (by have h := T.nonouter_cornerCount_total_subtype (e 0); omega)
    (by have h := T.nonouter_cornerCount_total_subtype (e 1); omega)
    (by simpa only [hg, add_zero] using T.nonouter_cornerCount_total_subtype (e 2))
  omega

/-- The actual two-type case, allowing any missing reference label. -/
theorem CongruentTiling.two_type_angle_classification {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : Equiv.Perm (Fin 3))
    (hind : IntegerIndependentAngles (R.cornerAngle (e 0)) (R.cornerAngle (e 1)))
    (hP : Function.Injective P.cornerAngle)
    (ha : 0 < T.outerCornerCount (e 0)) (hb : 0 < T.outerCornerCount (e 1))
    (hg : T.outerCornerCount (e 2) = 0) :
    PermutedTriple P.cornerAngle R.cornerAngle ∨
      ExceptionalAnglePattern (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) P.cornerAngle ∨
      ExceptionalAnglePattern (R.cornerAngle (e 1)) (R.cornerAngle (e 0)) P.cornerAngle := by
  have hbound := T.outer_counts_le_three_of_missing_permuted e hind ha hb hg
  have hθ (j : Fin 3) : P.cornerAngle j =
      (T.cornerCount (P.vertex j) (e 0) : ℝ) * R.cornerAngle (e 0) +
      (T.cornerCount (P.vertex j) (e 1) : ℝ) * R.cornerAngle (e 1) := by
    have h := T.outer_angle_count_identity_permuted e j
    have hz := T.cornerCount_eq_zero_of_outer_eq_zero j (e 2) hg
    simpa only [hz, Nat.cast_zero, zero_mul, add_zero] using h.symm
  have hpos (j : Fin 3) :
      0 < T.cornerCount (P.vertex j) (e 0) + T.cornerCount (P.vertex j) (e 1) := by
    by_contra h
    have h₀ : T.cornerCount (P.vertex j) (e 0) = 0 := by omega
    have h₁ : T.cornerCount (P.vertex j) (e 1) = 0 := by omega
    have he := hθ j
    rw [h₀, h₁] at he
    norm_num at he
    have hp := P.cornerAngle_pos j
    linarith
  have hout := T.outer_angle_total_permuted e
  rw [hg] at hout
  norm_num at hout
  have h := two_type_angle_partition_classification
    (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) (R.cornerAngle (e 2)) P.cornerAngle
    (fun j => T.cornerCount (P.vertex j) (e 0))
    (fun j => T.cornerCount (P.vertex j) (e 1)) (R.sum_cornerAngle_permuted e)
    (by change 1 ≤ T.outerCornerCount (e 0) ∧ T.outerCornerCount (e 0) ≤ 3; omega)
    (by change 1 ≤ T.outerCornerCount (e 1) ∧ T.outerCornerCount (e 1) ≤ 3; omega)
    hpos hP hθ hout
  rcases h with h | h | h
  · left
    have hr : PermutedTriple R.cornerAngle
        ![R.cornerAngle (e 0), R.cornerAngle (e 1), R.cornerAngle (e 2)] :=
      permutedTriple_of_at e rfl rfl rfl
    exact h.trans hr.symm
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The equilateral conclusion for an arbitrary surviving reference label. -/
theorem CongruentTiling.single_type_angles_permuted {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (e : Equiv.Perm (Fin 3))
    (hind : IntegerIndependentAngles (R.cornerAngle (e 0)) (R.cornerAngle (e 1)))
    (hb : T.outerCornerCount (e 1) = 0) (hg : T.outerCornerCount (e 2) = 0) :
    ∀ j : Fin 3, P.cornerAngle j = Real.pi / 3 := by
  classical
  have hθ (j : Fin 3) :
      (T.cornerCount (P.vertex j) (e 0) : ℝ) * R.cornerAngle (e 0) = P.cornerAngle j := by
    have h := T.outer_angle_count_identity_permuted e j
    have hb' := T.cornerCount_eq_zero_of_outer_eq_zero j (e 1) hb
    have hg' := T.cornerCount_eq_zero_of_outer_eq_zero j (e 2) hg
    simpa only [hb', hg', Nat.cast_zero, zero_mul, add_zero] using h
  have hpos (j : Fin 3) : 0 < T.cornerCount (P.vertex j) (e 0) := by
    by_contra h
    have hz : T.cornerCount (P.vertex j) (e 0) = 0 := by omega
    have he := hθ j
    rw [hz] at he
    norm_num at he
    have hp := P.cornerAngle_pos j
    linarith
  have hs : T.cornerCount (P.vertex 0) (e 0) + T.cornerCount (P.vertex 1) (e 0) +
      T.cornerCount (P.vertex 2) (e 0) = T.outerCornerCount (e 0) := by
    simpa only [Equiv.refl_apply, CongruentTiling.outerCornerCount] using
      sum_three_permuted (fun j => T.cornerCount (P.vertex j) (e 0)) (Equiv.refl _)
  have h₀ := hpos 0
  have h₁ := hpos 1
  have h₂ := hpos 2
  have hm : 3 ≤ T.outerCornerCount (e 0) := by omega
  have hm' : T.outerCornerCount (e 0) - 1 + 1 = T.outerCornerCount (e 0) := by omega
  have hout := T.outer_angle_total_permuted e
  rw [hb, hg] at hout
  norm_num at hout
  have hlocal (z : T.nonouterVertices) :=
    (single_outer_local_equations hind (T.outerCornerCount (e 0))
      (T.localAngleMultiplier z) (T.cornerCount z (e 0)) (T.cornerCount z (e 1))
      (T.cornerCount z (e 2)) (by omega) (R.sum_cornerAngle_permuted e) hout
      (T.nonouter_local_angle_equation_permuted e z)).1
  have hbound := angle_relation_coefficient_le_two (T.outerCornerCount (e 0) - 1) N
    (fun z : T.nonouterVertices => T.cornerCount z (e 0))
    (fun z : T.nonouterVertices => T.cornerCount z (e 2))
    (fun z : T.nonouterVertices => T.localAngleMultiplier z)
    (fun z => (T.localAngleMultiplier_bounds z).2)
    (fun z => by simpa only [hm'] using hlocal z)
    (by rw [hm']; exact T.nonouter_cornerCount_total_subtype (e 0))
    (by simpa only [hg, add_zero] using T.nonouter_cornerCount_total_subtype (e 2))
  have hc : T.outerCornerCount (e 0) = 3 := by omega
  have hcount (j : Fin 3) : T.cornerCount (P.vertex j) (e 0) = 1 := by
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl <;> omega
  norm_num [hc] at hout
  intro j
  have hj := hθ j
  rw [hcount j] at hj
  norm_num at hj
  linarith

/-- Full irrational-angle necessity at the level of actual Euclidean angles:
a scalene outer triangle has the reference angles, or one of the six exceptional
patterns after permuting the reference labels. Angle independence and the finite
coefficient bounds are derived, not additional assumptions of this theorem. -/
theorem CongruentTiling.irrational_scalene_angle_classification
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles) (hP : Function.Injective P.cornerAngle) :
    PermutedTriple P.cornerAngle R.cornerAngle ∨
      ∃ e : Equiv.Perm (Fin 3),
        ExceptionalAnglePattern (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) P.cornerAngle := by
  classical
  have hsingle (e : Equiv.Perm (Fin 3))
      (hb : T.outerCornerCount (e 1) = 0) (hg : T.outerCornerCount (e 2) = 0) : False := by
    have h := T.single_type_angles_permuted e (T.independent_angles_of_missing e hR hg) hb hg
    have he : (0 : Fin 3) = 1 := hP ((h 0).trans (h 1).symm)
    norm_num at he
  by_cases hpos : ∀ k : Fin 3, 0 < T.outerCornerCount k
  · obtain ⟨e, he⟩ := T.outer_angles_permuted_of_all_pos hpos
    left
    refine ⟨e.symm, ?_⟩
    intro j
    simpa using he (e.symm j)
  · push Not at hpos
    obtain ⟨k, hk⟩ := hpos
    let e : Equiv.Perm (Fin 3) := Equiv.swap 2 k
    have hg : T.outerCornerCount (e 2) = 0 := by
      have hz : T.outerCornerCount k = 0 := by omega
      simpa [e] using hz
    by_cases ha : 0 < T.outerCornerCount (e 0)
    · by_cases hb : 0 < T.outerCornerCount (e 1)
      · have hind := T.independent_angles_of_missing e hR hg
        rcases T.two_type_angle_classification e hind hP ha hb hg with h | h | h
        · exact Or.inl h
        · exact Or.inr ⟨e, h⟩
        · right
          refine ⟨(Equiv.swap (0 : Fin 3) 1).trans e, ?_⟩
          simpa [Equiv.swap_apply_def] using h
      · exact False.elim (hsingle e (by omega) hg)
    · let f : Equiv.Perm (Fin 3) := (Equiv.swap (0 : Fin 3) 1).trans e
      have hf₁ : f 1 = e 0 := by simp [f]
      have hf₂ : f 2 = e 2 := by simp [f, Equiv.swap_apply_def]
      exact False.elim (hsingle f (by rw [hf₁]; omega) (by rw [hf₂]; exact hg))

theorem Triangle.equal_angles_of_not_injective_cornerAngle (P : Triangle)
    (hP : ¬ Function.Injective P.cornerAngle) :
    P.angleA = P.angleB ∨ P.angleB = P.angleC ∨ P.angleC = P.angleA := by
  by_contra h
  push Not at h
  obtain ⟨hab, hbc, hca⟩ := h
  apply hP
  intro i j hij
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp_all [Triangle.cornerAngle]

/-- No scalene or independence hypothesis is omitted: every actual tiling by
an incommensurable-angle reference has one of these three angle alternatives. -/
theorem CongruentTiling.irrational_angle_classification
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles) :
    (P.angleA = P.angleB ∨ P.angleB = P.angleC ∨ P.angleC = P.angleA) ∨
      PermutedTriple P.cornerAngle R.cornerAngle ∨
      ∃ e : Equiv.Perm (Fin 3),
        ExceptionalAnglePattern (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) P.cornerAngle := by
  by_cases hP : Function.Injective P.cornerAngle
  · exact Or.inr (T.irrational_scalene_angle_classification hR hP)
  · exact Or.inl (P.equal_angles_of_not_injective_cornerAngle hP)

end Erdos633

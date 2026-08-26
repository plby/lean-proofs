import ErdosProblems.Erdos633.ActualAngleClassification

/-!
# From the angle alternatives to geometric similarity

The similarity relation concerns the actual closed triangles and allows
reflection. Arbitrary vertex permutations preserve both carriers and their
corresponding Euclidean angles.
-/

namespace Erdos633

theorem fin_three_perm_cases (e : Equiv.Perm (Fin 3)) :
    (e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 2) ∨
    (e 0 = 0 ∧ e 1 = 2 ∧ e 2 = 1) ∨
    (e 0 = 1 ∧ e 1 = 0 ∧ e 2 = 2) ∨
    (e 0 = 1 ∧ e 1 = 2 ∧ e 2 = 0) ∨
    (e 0 = 2 ∧ e 1 = 0 ∧ e 2 = 1) ∨
    (e 0 = 2 ∧ e 1 = 1 ∧ e 2 = 0) := by
  have h₀₁ : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h₀₂ : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h₁₂ : e 1 ≠ e 2 := e.injective.ne (by decide)
  omega

theorem Triangle.orientedDoubleArea_vertex_permuted_ne (P : Triangle)
    (e : Equiv.Perm (Fin 3)) :
    orientedDoubleArea (P.vertex (e 0)) (P.vertex (e 1)) (P.vertex (e 2)) ≠ 0 := by
  rcases fin_three_perm_cases e with h | h | h | h | h | h
  all_goals
    obtain ⟨h₀, h₁, h₂⟩ := h
    rw [h₀, h₁, h₂]
  · exact P.nondegenerate
  · exact P.swapBC.nondegenerate
  · exact P.swapAB.nondegenerate
  · exact P.rotate.nondegenerate
  · exact P.rotate.rotate.nondegenerate
  · exact P.swapAC.nondegenerate

def Triangle.relabel (P : Triangle) (e : Equiv.Perm (Fin 3)) : Triangle where
  a := P.vertex (e 0)
  b := P.vertex (e 1)
  c := P.vertex (e 2)
  nondegenerate := P.orientedDoubleArea_vertex_permuted_ne e

theorem Triangle.vertex_relabel (P : Triangle) (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (P.relabel e).vertex j = P.vertex (e j) := by
  fin_cases j <;> rfl

theorem Triangle.relabel_carrier (P : Triangle) (e : Equiv.Perm (Fin 3)) :
    (P.relabel e).carrier = P.carrier := by
  change convexHull ℝ {(P.relabel e).a, (P.relabel e).b, (P.relabel e).c} =
    convexHull ℝ {P.a, P.b, P.c}
  rw [← (P.relabel e).range_vertex, ← P.range_vertex]
  congr 1
  ext z
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨e j, (P.vertex_relabel e j).symm.trans hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨e.symm j, ?_⟩
    rw [P.vertex_relabel, e.apply_symm_apply]
    exact hj

theorem Triangle.cornerAngle_relabel (P : Triangle) (e : Equiv.Perm (Fin 3))
    (j : Fin 3) : (P.relabel e).cornerAngle j = P.cornerAngle (e j) := by
  rcases fin_three_perm_cases e with h | h | h | h | h | h
  all_goals
    obtain ⟨h₀, h₁, h₂⟩ := h
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl <;>
      simp [Triangle.cornerAngle, Triangle.angleA, Triangle.angleB, Triangle.angleC,
        Triangle.relabel, Triangle.vertex, h₀, h₁, h₂, EuclideanGeometry.angle_comm]

/-- Ambient similarity of the closed triangular regions, with positive scale
and an arbitrary ambient isometry (so reflected shapes are included). -/
def Triangle.Similar (P R : Triangle) : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∃ e : ℂ ≃ᵢ ℂ,
    e '' ((fun z : ℂ => (k : ℂ) * z) '' R.carrier) = P.carrier

theorem Triangle.isometry_of_scaled_sides (P R : Triangle) (k : ℝ) (hk : 0 < k)
    (hab : dist P.a P.b = k * dist R.a R.b)
    (hac : dist P.a P.c = k * dist R.a R.c)
    (hbc : dist P.b P.c = k * dist R.b R.c) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' ((fun z : ℂ => (k : ℂ) * z) '' R.carrier) = P.carrier := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  obtain ⟨e, he⟩ := (R.mapSimilarity 0 (k : ℂ) hkC).congruent_of_normSq P
    (by
      change Complex.normSq ((0 + (k : ℂ) * R.b) - (0 + (k : ℂ) * R.a)) = _
      rw [normSq_similarity_sub, Complex.normSq_ofReal, normSq_sub_eq_dist_sq,
        normSq_sub_eq_dist_sq, hab]
      ring)
    (by
      change Complex.normSq ((0 + (k : ℂ) * R.c) - (0 + (k : ℂ) * R.a)) = _
      rw [normSq_similarity_sub, Complex.normSq_ofReal, normSq_sub_eq_dist_sq,
        normSq_sub_eq_dist_sq, hac]
      ring)
    (by
      change Complex.normSq ((0 + (k : ℂ) * R.c) - (0 + (k : ℂ) * R.b)) = _
      rw [normSq_similarity_sub, Complex.normSq_ofReal, normSq_sub_eq_dist_sq,
        normSq_sub_eq_dist_sq, hbc]
      ring)
  refine ⟨e, ?_⟩
  rw [Triangle.mapSimilarity_carrier] at he
  change e '' ((fun z : ℂ => 0 + (k : ℂ) * z) '' R.carrier) = P.carrier at he
  simpa only [zero_add] using he

theorem Triangle.similar_of_scaled_sides (P R : Triangle) (k : ℝ) (hk : 0 < k)
    (hab : dist P.a P.b = k * dist R.a R.b)
    (hac : dist P.a P.c = k * dist R.a R.c)
    (hbc : dist P.b P.c = k * dist R.b R.c) : P.Similar R :=
  ⟨k, hk, P.isometry_of_scaled_sides R k hk hab hac hbc⟩

theorem Triangle.scaled_sides_of_angles_eq (P R : Triangle)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) :
    ∃ k : ℝ, 0 < k ∧ dist P.a P.b = k * dist R.a R.b ∧
      dist P.a P.c = k * dist R.a R.c ∧ dist P.b P.c = k * dist R.b R.c := by
  have hC : P.angleC = R.angleC := by linarith [P.angle_sum, R.angle_sum]
  let k := dist P.a P.b / dist R.a R.b
  have hR : 0 < dist R.a R.b := dist_pos.mpr R.a_ne_b
  have hk : 0 < k := div_pos (dist_pos.mpr P.a_ne_b) hR
  have hab : dist P.a P.b = k * dist R.a R.b := by
    dsimp [k]
    rw [div_mul_cancel₀ _ (ne_of_gt hR)]
  refine ⟨k, hk, hab, ?_, ?_⟩
  · rw [P.sideB_over_C, R.sideB_over_C, hB, hC, hab]
    ring
  · rw [P.sideA_over_C, R.sideA_over_C, hA, hC, hab]
    ring

/-- AA similarity, derived from the sine rule and ambient SSS congruence. -/
theorem Triangle.similar_of_angles_eq (P R : Triangle)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) : P.Similar R := by
  obtain ⟨k, hk, hab, hac, hbc⟩ := P.scaled_sides_of_angles_eq R hA hB
  exact P.similar_of_scaled_sides R k hk hab hac hbc

theorem Triangle.similar_of_permuted_angles (P R : Triangle)
    (h : PermutedTriple P.cornerAngle R.cornerAngle) : P.Similar R := by
  obtain ⟨e, he⟩ := h
  have hA : (P.relabel e).angleA = R.angleA := by
    exact (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : (P.relabel e).angleB = R.angleB := by
    exact (P.cornerAngle_relabel e 1).trans (he 1)
  obtain ⟨k, hk, f, hf⟩ := (P.relabel e).similar_of_angles_eq R hA hB
  exact ⟨k, hk, f, hf.trans (P.relabel_carrier e)⟩

theorem Triangle.area_scale (R : Triangle) (k : ℝ) (hk : 0 < k) :
    (R.mapSimilarity 0 (k : ℂ) (by exact_mod_cast ne_of_gt hk)).area = k ^ 2 * R.area := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  let e := similarityAffineEquiv 0 (k : ℂ) hkC
  have he : R.mapAffineEquiv e = R.mapSimilarity 0 (k : ℂ) hkC := by
    apply Triangle.ext <;> rfl
  have hlin : (e.linear : ℂ →ₗ[ℝ] ℂ) = k • (LinearMap.id : ℂ →ₗ[ℝ] ℂ) := by
    ext z
    change (k : ℂ) * z = k • z
    simp only [Complex.real_smul]
  have h := R.area_mapAffineEquiv e
  rw [he, hlin, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex,
    mul_one, abs_of_nonneg (sq_nonneg k)] at h
  exact h

theorem Triangle.area_eq_of_similarity (P R : Triangle) (k : ℝ) (hk : 0 < k)
    (e : ℂ ≃ᵢ ℂ)
    (he : e '' ((fun z : ℂ => (k : ℂ) * z) '' R.carrier) = P.carrier) :
    P.area = k ^ 2 * R.area := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have hcarrier : (R.mapSimilarity 0 (k : ℂ) hkC).carrier =
      (fun z : ℂ => (k : ℂ) * z) '' R.carrier := by
    rw [Triangle.mapSimilarity_carrier]
    change (fun z : ℂ => 0 + (k : ℂ) * z) '' R.carrier = _
    simp only [zero_add]
  have harea : P.area = (R.mapSimilarity 0 (k : ℂ) hkC).area := by
    unfold Triangle.area
    rw [← he, ← hcarrier, isometry_volume_image]
  exact harea.trans (R.area_scale k hk)

/-- In a geometric reptiling the square of the actual similarity scale is
the number of tiles; it is derived from area additivity. -/
theorem CongruentTiling.similarity_scale_squared {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : ℝ) (hk : 0 < k) (e : ℂ ≃ᵢ ℂ)
    (he : e '' ((fun z : ℂ => (k : ℂ) * z) '' R.carrier) = P.carrier) : k ^ 2 = N := by
  apply mul_right_cancel₀ (ne_of_gt R.area_pos)
  exact (P.area_eq_of_similarity R k hk e he).symm.trans T.area_eq

theorem CongruentTiling.exists_similarity_scale_squared {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (h : P.Similar R) :
    ∃ k : ℝ, 0 < k ∧ k ^ 2 = N ∧
      ∃ e : ℂ ≃ᵢ ℂ, e '' ((fun z : ℂ => (k : ℂ) * z) '' R.carrier) = P.carrier := by
  obtain ⟨k, hk, e, he⟩ := h
  exact ⟨k, hk, T.similarity_scale_squared k hk e he, e, he⟩

theorem Triangle.isosceles_of_equal_angles (P : Triangle)
    (h : P.angleA = P.angleB ∨ P.angleB = P.angleC ∨ P.angleC = P.angleA) : P.Isosceles := by
  rcases h with h | h | h
  · have he : dist P.a P.c = dist P.b P.c := by
      rw [P.sideB_over_A, ← h, mul_div_cancel_right₀ _ (ne_of_gt P.sin_angleA_pos)]
    exact Or.inr (Or.inr (by simpa only [dist_comm] using he))
  · have he : dist P.a P.c = dist P.a P.b := by
      rw [P.sideB_over_C, h, mul_div_cancel_right₀ _ (ne_of_gt P.sin_angleC_pos)]
    exact Or.inl he.symm
  · have he : dist P.b P.c = dist P.a P.b := by
      rw [P.sideA_over_C, h, mul_div_cancel_right₀ _ (ne_of_gt P.sin_angleA_pos)]
    exact Or.inr (Or.inl (by rw [dist_comm P.b P.a]; exact he.symm))

theorem CongruentTiling.irrational_geometric_shape_alternatives
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles) :
    P.Isosceles ∨ P.Similar R ∨
      ∃ e : Equiv.Perm (Fin 3),
        ExceptionalAnglePattern (R.cornerAngle (e 0)) (R.cornerAngle (e 1)) P.cornerAngle := by
  rcases T.irrational_angle_classification hR with h | h | h
  · exact Or.inl (P.isosceles_of_equal_angles h)
  · exact Or.inr (Or.inl (P.similar_of_permuted_angles R h))
  · exact Or.inr (Or.inr h)

end Erdos633

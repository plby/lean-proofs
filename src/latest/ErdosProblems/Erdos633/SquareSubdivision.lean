import ErdosProblems.Erdos633.Coordinates

/-!
# The triangular square grid

The `n × n` index set parametrizes all upward and downward unit triangles in
the standard triangle dilated by `n`. Boundary points are included throughout.
-/

namespace Erdos633

def unitLower (i j : ℤ) : Triangle :=
  standardTriangle.mapSimilarity ⟨i, j⟩ 1 (by norm_num)

def unitUpper (i j : ℤ) : Triangle :=
  standardTriangle.mapSimilarity ⟨i + 1, j + 1⟩ (-1) (by norm_num)

theorem unitLower_mem_iff (i j : ℤ) (z : ℂ) : z ∈ (unitLower i j).carrier ↔
    (i : ℝ) ≤ z.re ∧ (j : ℝ) ≤ z.im ∧ z.re + z.im ≤ i + j + 1 := by
  rw [unitLower, Triangle.mapSimilarity_carrier, Equiv.image_eq_preimage_symm]
  change (z - (⟨i, j⟩ : ℂ)) / 1 ∈ standardTriangle.carrier ↔ _
  rw [standardTriangle_carrier]
  simp only [div_one, Set.mem_ofPred_eq, Complex.sub_re, Complex.sub_im]
  constructor <;> rintro ⟨hx, hy, hs⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem unitUpper_mem_iff (i j : ℤ) (z : ℂ) : z ∈ (unitUpper i j).carrier ↔
    z.re ≤ (i : ℝ) + 1 ∧ z.im ≤ (j : ℝ) + 1 ∧ i + j + 1 ≤ z.re + z.im := by
  rw [unitUpper, Triangle.mapSimilarity_carrier, Equiv.image_eq_preimage_symm]
  change (z - (⟨i + 1, j + 1⟩ : ℂ)) / (-1) ∈ standardTriangle.carrier ↔ _
  rw [standardTriangle_carrier]
  simp only [div_neg, div_one, Set.mem_ofPred_eq, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im]
  constructor <;> rintro ⟨hx, hy, hs⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem unitLower_interior_iff (i j : ℤ) (z : ℂ) : z ∈ interior (unitLower i j).carrier ↔
    (i : ℝ) < z.re ∧ (j : ℝ) < z.im ∧ z.re + z.im < i + j + 1 := by
  rw [unitLower, Triangle.mapSimilarity_interior, Equiv.image_eq_preimage_symm]
  change (z - (⟨i, j⟩ : ℂ)) / 1 ∈ interior standardTriangle.carrier ↔ _
  rw [standardTriangle_interior]
  simp only [div_one, Set.mem_ofPred_eq, Complex.sub_re, Complex.sub_im]
  constructor <;> rintro ⟨hx, hy, hs⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem unitUpper_interior_iff (i j : ℤ) (z : ℂ) : z ∈ interior (unitUpper i j).carrier ↔
    z.re < (i : ℝ) + 1 ∧ z.im < (j : ℝ) + 1 ∧ i + j + 1 < z.re + z.im := by
  rw [unitUpper, Triangle.mapSimilarity_interior, Equiv.image_eq_preimage_symm]
  change (z - (⟨i + 1, j + 1⟩ : ℂ)) / (-1) ∈ interior standardTriangle.carrier ↔ _
  rw [standardTriangle_interior]
  simp only [div_neg, div_one, Set.mem_ofPred_eq, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im]
  constructor <;> rintro ⟨hx, hy, hs⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem unitLower_interior_bounds {i j : ℤ} {z : ℂ}
    (h : z ∈ interior (unitLower i j).carrier) :
    ((i : ℝ) < z.re ∧ z.re < i + 1) ∧ ((j : ℝ) < z.im ∧ z.im < j + 1) := by
  obtain ⟨hx, hy, hs⟩ := (unitLower_interior_iff i j z).mp h
  exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩

theorem unitUpper_interior_bounds {i j : ℤ} {z : ℂ}
    (h : z ∈ interior (unitUpper i j).carrier) :
    ((i : ℝ) < z.re ∧ z.re < i + 1) ∧ ((j : ℝ) < z.im ∧ z.im < j + 1) := by
  obtain ⟨hx, hy, hs⟩ := (unitUpper_interior_iff i j z).mp h
  exact ⟨⟨by linarith, hx⟩, ⟨by linarith, hy⟩⟩

theorem unitLower_disjoint {i j k l : ℤ} (h : (i, j) ≠ (k, l)) :
    Disjoint (interior (unitLower i j).carrier) (interior (unitLower k l).carrier) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have hb := unitLower_interior_bounds hz
  have hc := unitLower_interior_bounds hw
  exact h (Prod.ext (integer_unit_interval_unique hb.1 hc.1)
    (integer_unit_interval_unique hb.2 hc.2))

theorem unitUpper_disjoint {i j k l : ℤ} (h : (i, j) ≠ (k, l)) :
    Disjoint (interior (unitUpper i j).carrier) (interior (unitUpper k l).carrier) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have hb := unitUpper_interior_bounds hz
  have hc := unitUpper_interior_bounds hw
  exact h (Prod.ext (integer_unit_interval_unique hb.1 hc.1)
    (integer_unit_interval_unique hb.2 hc.2))

theorem unitLower_upper_disjoint (i j k l : ℤ) :
    Disjoint (interior (unitLower i j).carrier) (interior (unitUpper k l).carrier) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have hb := unitLower_interior_bounds hz
  have hc := unitUpper_interior_bounds hw
  have hik := integer_unit_interval_unique hb.1 hc.1
  have hjl := integer_unit_interval_unique hb.2 hc.2
  subst k
  subst l
  have hs := ((unitLower_interior_iff i j z).mp hz).2.2
  have ht := ((unitUpper_interior_iff i j z).mp hw).2.2
  linarith

def dilatedStandardTriangle (n : ℕ) (hn : 0 < n) : Triangle :=
  standardTriangle.mapSimilarity 0 (n : ℂ) (by exact_mod_cast ne_of_gt hn)

theorem dilatedStandardTriangle_mem_iff (n : ℕ) (hn : 0 < n) (z : ℂ) :
    z ∈ (dilatedStandardTriangle n hn).carrier ↔
      0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dilatedStandardTriangle, Triangle.mapSimilarity_carrier, Equiv.image_eq_preimage_symm]
  change (z - 0) / (n : ℂ) ∈ standardTriangle.carrier ↔ _
  rw [standardTriangle_carrier]
  simp only [sub_zero, Set.mem_ofPred_eq, Complex.div_natCast_re, Complex.div_natCast_im,
    ← add_div, le_div_iff₀ hnr, div_le_iff₀ hnr, zero_mul, one_mul]

def squareGridTile (n : ℕ) (p : Fin n × Fin n) : Triangle :=
  if p.1.val + p.2.val < n then unitLower p.1.val p.2.val
  else unitUpper ((n : ℤ) - 1 - p.1.val) ((n : ℤ) - 1 - p.2.val)

theorem squareGridTile_subset (n : ℕ) (hn : 0 < n) (p : Fin n × Fin n) :
    (squareGridTile n p).carrier ⊆ (dilatedStandardTriangle n hn).carrier := by
  intro z hz
  rw [dilatedStandardTriangle_mem_iff]
  have hi : (p.1 : ℝ) + 1 ≤ n := by exact_mod_cast Nat.add_one_le_iff.mpr p.1.isLt
  have hj : (p.2 : ℝ) + 1 ≤ n := by exact_mod_cast Nat.add_one_le_iff.mpr p.2.isLt
  have hi0 : (0 : ℝ) ≤ p.1 := by positivity
  have hj0 : (0 : ℝ) ≤ p.2 := by positivity
  by_cases hp : p.1.val + p.2.val < n
  · rw [squareGridTile, if_pos hp, unitLower_mem_iff] at hz
    push_cast at hz
    have hs : (p.1 : ℝ) + p.2 + 1 ≤ n := by exact_mod_cast Nat.add_one_le_iff.mpr hp
    exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2]⟩
  · rw [squareGridTile, if_neg hp, unitUpper_mem_iff] at hz
    push_cast at hz
    have hs : (n : ℝ) ≤ (p.1 : ℝ) + p.2 := by exact_mod_cast Nat.le_of_not_gt hp
    exact ⟨by linarith [hz.2.1, hz.2.2], by linarith [hz.1, hz.2.2],
      by linarith [hz.1, hz.2.1]⟩

theorem squareGrid_covers (n : ℕ) (hn : 0 < n) :
    (⋃ p : Fin n × Fin n, (squareGridTile n p).carrier) =
      (dilatedStandardTriangle n hn).carrier := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun p => squareGridTile_subset n hn p
  · intro z hz
    obtain ⟨hx, hy, hs⟩ := (dilatedStandardTriangle_mem_iff n hn z).mp hz
    obtain ⟨i, hi, hi1, hiStrict⟩ := exists_unit_interval_index n hn z.re hx (by linarith)
    obtain ⟨j, hj, hj1, hjStrict⟩ := exists_unit_interval_index n hn z.im hy (by linarith)
    have hij : i.val + j.val < n := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hi0 : (0 : ℝ) ≤ i := by positivity
      have hj0 : (0 : ℝ) ≤ j := by positivity
      have hlt : (i : ℝ) + j < n := by
        by_cases hxp : 0 < z.re
        · linarith [hiStrict hxp]
        · by_cases hyp : 0 < z.im
          · linarith [hjStrict hyp]
          · linarith
      exact_mod_cast hlt
    by_cases hdiag : z.re + z.im ≤ (i : ℝ) + j + 1
    · apply Set.mem_iUnion.mpr
      refine ⟨(i, j), ?_⟩
      rw [squareGridTile, if_pos hij, unitLower_mem_iff]
      exact ⟨hi, hj, hdiag⟩
    · have hij2 : i.val + j.val + 2 ≤ n := by
        have hlt : (i : ℝ) + j + 1 < n := by linarith
        have hnat : i.val + j.val + 1 < n := by exact_mod_cast hlt
        omega
      let k : Fin n := ⟨n - 1 - i.val, by omega⟩
      let l : Fin n := ⟨n - 1 - j.val, by omega⟩
      have hkl : ¬ k.val + l.val < n := by dsimp [k, l]; omega
      have hk : (n : ℤ) - 1 - k.val = i.val := by dsimp [k]; omega
      have hl : (n : ℤ) - 1 - l.val = j.val := by dsimp [l]; omega
      apply Set.mem_iUnion.mpr
      refine ⟨(k, l), ?_⟩
      rw [squareGridTile, if_neg hkl, hk, hl, unitUpper_mem_iff]
      exact ⟨hi1, hj1, le_of_lt (lt_of_not_ge hdiag)⟩

theorem squareGrid_disjoint (n : ℕ) : Pairwise fun p q : Fin n × Fin n =>
    Disjoint (interior (squareGridTile n p).carrier) (interior (squareGridTile n q).carrier) := by
  intro p q hpq
  by_cases hp : p.1.val + p.2.val < n <;> by_cases hq : q.1.val + q.2.val < n
  · rw [squareGridTile, if_pos hp, squareGridTile, if_pos hq]
    apply unitLower_disjoint
    intro h
    apply hpq
    apply Prod.ext <;> apply Fin.ext
    · have hi := congrArg Prod.fst h
      dsimp at hi
      exact_mod_cast hi
    · have hj := congrArg Prod.snd h
      dsimp at hj
      exact_mod_cast hj
  · rw [squareGridTile, if_pos hp, squareGridTile, if_neg hq]
    exact unitLower_upper_disjoint _ _ _ _
  · rw [squareGridTile, if_neg hp, squareGridTile, if_pos hq]
    exact (unitLower_upper_disjoint _ _ _ _).symm
  · rw [squareGridTile, if_neg hp, squareGridTile, if_neg hq]
    apply unitUpper_disjoint
    intro h
    have hi := congrArg Prod.fst h
    have hj := congrArg Prod.snd h
    apply hpq
    apply Prod.ext <;> apply Fin.ext <;> dsimp at hi hj <;> omega

/-- An affine image of a translated tile is a translate of its affine image.
This special case, unlike arbitrary congruence, survives every affine map. -/
theorem affine_image_translate_congruent (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) (u : ℂ) :
    ∃ f : ℂ ≃ᵢ ℂ, f '' (T.mapAffineEquiv e).carrier =
      ((T.mapSimilarity u 1 (by norm_num)).mapAffineEquiv e).carrier := by
  refine ⟨IsometryEquiv.vaddConst (e.linear u), ?_⟩
  rw [Triangle.mapAffineEquiv_carrier, Triangle.mapAffineEquiv_carrier,
    Triangle.mapSimilarity_carrier]
  simp only [Set.image_image]
  congr 1
  funext z
  change e z + e.linear u = e (u + 1 * z)
  simpa only [vadd_eq_add, one_mul, add_comm] using (e.map_vadd z u).symm

/-- The same assertion holds for a translated half-turn. -/
theorem affine_image_halfTurn_congruent (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) (u : ℂ) :
    ∃ f : ℂ ≃ᵢ ℂ, f '' (T.mapAffineEquiv e).carrier =
      ((T.mapSimilarity u (-1) (by norm_num)).mapAffineEquiv e).carrier := by
  refine ⟨(LinearIsometryEquiv.neg ℝ).toIsometryEquiv.trans
    (IsometryEquiv.vaddConst (e u + e 0)), ?_⟩
  rw [Triangle.mapAffineEquiv_carrier, Triangle.mapAffineEquiv_carrier,
    Triangle.mapSimilarity_carrier]
  simp only [Set.image_image]
  congr 1
  funext z
  change -e z + (e u + e 0) = e (u + (-1) * z)
  have hu := e.map_vadd 0 u
  have hz := e.map_vadd 0 z
  have hs := e.map_vadd 0 (u - z)
  simp only [vadd_eq_add, add_zero, map_sub] at hu hz hs
  rw [neg_one_mul, ← sub_eq_add_neg, hs, hu, hz]
  abel

/-- The entire square grid remains a congruent tiling after any affine
equivalence, because its pieces differ only by translations and half-turns. -/
noncomputable def squareTiling_affine (e : ℂ ≃ᵃ[ℝ] ℂ) (n : ℕ) (hn : 0 < n) :
    CongruentTiling ((dilatedStandardTriangle n hn).mapAffineEquiv e)
      (standardTriangle.mapAffineEquiv e) (n ^ 2) := by
  have hcard : Fintype.card (Fin n × Fin n) = n ^ 2 := by simp [pow_two]
  rw [← hcard]
  apply CongruentTiling.ofIndexed (fun p : Fin n × Fin n => (squareGridTile n p).mapAffineEquiv e)
  · intro p
    by_cases hp : p.1.val + p.2.val < n
    · rw [squareGridTile, if_pos hp]
      exact affine_image_translate_congruent standardTriangle e _
    · rw [squareGridTile, if_neg hp]
      exact affine_image_halfTurn_congruent standardTriangle e _
  · simp only [Triangle.mapAffineEquiv_carrier]
    rw [← Set.image_iUnion, squareGrid_covers n hn]
  · intro p q hpq
    simp only [Triangle.mapAffineEquiv_interior]
    exact Set.disjoint_image_of_injective e.injective (squareGrid_disjoint n hpq)

/-- Coordinates for a subdivision into `n²` pieces: first divide the standard
coordinates by `n`, then send `0,1,I` to the vertices of the triangle. -/
noncomputable def Triangle.subdivisionEquiv (T : Triangle) (n : ℕ) (hn : 0 < n) :
    ℂ ≃ᵃ[ℝ] ℂ :=
  (similarityAffineEquiv 0 (n : ℂ)⁻¹
    (inv_ne_zero (by exact_mod_cast ne_of_gt hn))).trans T.coordinateEquiv

theorem Triangle.subdivisionEquiv_apply (T : Triangle) (n : ℕ) (hn : 0 < n) (z : ℂ) :
    T.subdivisionEquiv n hn z = T.coordinateEquiv ((n : ℂ)⁻¹ * z) := by
  change T.coordinateEquiv (0 + (n : ℂ)⁻¹ * z) = _
  rw [zero_add]

theorem Triangle.dilatedStandard_map_subdivisionEquiv (T : Triangle) (n : ℕ) (hn : 0 < n) :
    (dilatedStandardTriangle n hn).mapAffineEquiv (T.subdivisionEquiv n hn) = T := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  apply Triangle.ext
  · change T.subdivisionEquiv n hn (0 + (n : ℂ) * 0) = T.a
    simp [T.subdivisionEquiv_apply]
  · change T.subdivisionEquiv n hn (0 + (n : ℂ) * 1) = T.b
    simp [T.subdivisionEquiv_apply, hnC]
  · change T.subdivisionEquiv n hn (0 + (n : ℂ) * Complex.I) = T.c
    simp [T.subdivisionEquiv_apply, hnC]

/-- The general square subdivision, with a specific nondegenerate reference tile. -/
noncomputable def Triangle.squareTiling (T : Triangle) (n : ℕ) (hn : 0 < n) :
    CongruentTiling T (standardTriangle.mapAffineEquiv (T.subdivisionEquiv n hn)) (n ^ 2) :=
  (squareTiling_affine (T.subdivisionEquiv n hn) n hn).of_carrier_eq
    (congrArg Triangle.carrier (T.dilatedStandard_map_subdivisionEquiv n hn))

theorem Triangle.admits_square_tiling (T : Triangle) (n : ℕ) (hn : 0 < n) :
    ∃ R : Triangle, Nonempty (CongruentTiling T R (n ^ 2)) :=
  ⟨_, ⟨T.squareTiling n hn⟩⟩

/-- An integer dilation of a triangle tiles by unscaled copies of that triangle.
This version fixes the reference tile, as required for common refinements. -/
noncomputable def Triangle.integerDilateTiling (T : Triangle) (n : ℕ) (hn : 0 < n) :
    CongruentTiling (T.mapSimilarity 0 (n : ℂ) (by exact_mod_cast ne_of_gt hn)) T (n ^ 2) := by
  let u : ℂ := ((n : ℂ) - 1) * T.a
  let e : ℂ ≃ᵃ[ℝ] ℂ := T.coordinateEquiv.trans (AffineEquiv.vaddConst ℝ u)
  have he (z : ℂ) : e z = T.coordinateEquiv z + u := rfl
  have hP : (dilatedStandardTriangle n hn).mapAffineEquiv e =
      T.mapSimilarity 0 (n : ℂ) (by exact_mod_cast ne_of_gt hn) := by
    apply Triangle.ext
    · change e (0 + (n : ℂ) * 0) = 0 + (n : ℂ) * T.a
      rw [he]
      simp only [mul_zero, add_zero, Triangle.coordinateEquiv_zero, zero_add]
      dsimp [u]
      ring
    · change e (0 + (n : ℂ) * 1) = 0 + (n : ℂ) * T.b
      rw [he, T.coordinateEquiv_apply]
      simp only [zero_add, mul_one, Complex.natCast_re, Complex.natCast_im,
        zero_smul, add_zero, Complex.real_smul, Complex.ofReal_natCast]
      dsimp [u]
      ring
    · change e (0 + (n : ℂ) * Complex.I) = 0 + (n : ℂ) * T.c
      rw [he, T.coordinateEquiv_apply]
      simp only [zero_add, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
        Complex.natCast_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, sub_zero, add_zero, zero_add, zero_smul, Complex.real_smul,
        Complex.ofReal_natCast]
      dsimp [u]
      ring
  have hR : standardTriangle.mapAffineEquiv e =
      T.mapIsometry (IsometryEquiv.vaddConst u) := by
    apply Triangle.ext
    · change e 0 = T.a + u
      rw [he, T.coordinateEquiv_zero]
    · change e 1 = T.b + u
      rw [he, T.coordinateEquiv_one]
    · change e Complex.I = T.c + u
      rw [he, T.coordinateEquiv_I]
  have hRef : (IsometryEquiv.vaddConst u) '' T.carrier =
      (standardTriangle.mapAffineEquiv e).carrier := by
    rw [hR, Triangle.mapIsometry_carrier]
  exact ((squareTiling_affine e n hn).changeTile (IsometryEquiv.vaddConst u) hRef).of_carrier_eq
    (congrArg Triangle.carrier hP)

end Erdos633

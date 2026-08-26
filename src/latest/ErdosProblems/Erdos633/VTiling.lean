import ErdosProblems.Erdos633.VGeometry
import ErdosProblems.Erdos633.Arithmetic

/-!
# Actual congruent tilings of the exceptional V family

The four-region geometry is refined to one common tile. The resulting count
is the sum of the three square subdivisions and the parallelogram grid.
-/

namespace Erdos633

/-- A concrete tiling when the three scale ratios and the two grid dimensions
are integers. The witnesses are built from the geometric four-region partition. -/
theorem VShape.tiling_of_integer_scales (v : VShape) (ε : ℝ) (hε : 0 < ε)
    (m n k : ℕ) (hm0 : 0 < m) (hn0 : 0 < n) (hk0 : 0 < k)
    (hm : (m : ℝ) * ε = 1 - v.b) (hn : (n : ℝ) * ε = v.b)
    (hk : (k : ℝ) * ε = v.s) :
    Nonempty (CongruentTiling v.outer
      (v.reference.mapSimilarity 0 (ε : ℂ) (by exact_mod_cast ne_of_gt hε))
      (n ^ 2 + n ^ 2 + k ^ 2 + 2 * m * n)) := by
  let R := v.reference.mapSimilarity 0 (ε : ℂ) (by exact_mod_cast ne_of_gt hε)
  let Tb := v.reference.scaleTiling ε v.b hε v.b_pos n hn0 hn
  let Ts := v.reference.scaleTiling ε v.s hε v.s_pos k hk0 hk
  obtain ⟨e₂, he₂⟩ := v.left_congruent
  obtain ⟨e₃, he₃⟩ := v.upper_congruent
  obtain ⟨e₄, he₄⟩ := v.grid_congruent ε hε
  let T₁ := Tb.of_carrier_eq (congrArg Triangle.carrier v.lower_eq.symm)
  let T₂ := (Tb.mapIsometry e₂).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e₂).trans he₂)
  let T₃ := (Ts.mapIsometry e₃).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e₃).trans he₃)
  let T₄ := (vParallelogram_affine_grid v.outer.coordinateEquiv v.b ε v.b_pos hε
    m n hm0 hn0 hm hn).changeTile e₄ he₄
  have h₁ : ((vLowerTriangle v.b v.b_pos).mapAffineEquiv v.outer.coordinateEquiv).carrier =
      v.outer.coordinateEquiv '' vLowerRegion v.b := by
    rw [Triangle.mapAffineEquiv_carrier, vLowerTriangle_carrier]
  have h₂ : ((vLeftTriangle v.b v.b_pos).mapAffineEquiv v.outer.coordinateEquiv).carrier =
      v.outer.coordinateEquiv '' vLeftRegion v.b := by
    rw [Triangle.mapAffineEquiv_carrier, vLeftTriangle_carrier]
  have h₃ : ((vUpperTriangle v.b v.b_pos v.b_lt_one).mapAffineEquiv
      v.outer.coordinateEquiv).carrier = v.outer.coordinateEquiv '' vUpperRegion v.b := by
    rw [Triangle.mapAffineEquiv_carrier, vUpperTriangle_carrier]
  let T := vRegions_assemble v.outer.coordinateEquiv v.b v.b_pos v.b_lt_one R
    (T₁.toRegionTiling.of_region_eq h₁) (T₂.toRegionTiling.of_region_eq h₂)
    (T₃.toRegionTiling.of_region_eq h₃) T₄
  have hc : Fintype.card (Fin (n ^ 2)) + Fintype.card (Fin (n ^ 2)) +
      Fintype.card (Fin (k ^ 2)) + Fintype.card ((Fin m × Fin n) × Bool) =
      n ^ 2 + n ^ 2 + k ^ 2 + 2 * m * n := by
    simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
    ring
  have hT : Nonempty (CongruentTiling (standardTriangle.mapAffineEquiv
      v.outer.coordinateEquiv) R (n ^ 2 + n ^ 2 + k ^ 2 + 2 * m * n)) := by
    rw [← hc]
    exact ⟨T⟩
  simpa only [Triangle.standard_map_coordinateEquiv] using hT

/-- The common tile for the denominator-`d` construction is `R/d²`. -/
noncomputable def VShape.fractionTile (v : VShape) (d : ℕ) (hd0 : 0 < d) : Triangle :=
  v.reference.mapSimilarity 0 ((1 / (d : ℝ) ^ 2 : ℝ) : ℂ)
    (by
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd0
      exact_mod_cast one_div_ne_zero (pow_ne_zero 2 hd))

/-- For `s = u/d`, the explicit construction has `d²(2d²-u²)` copies of `R/d²`.
Keeping the reference tile explicit permits attachment of further pieces. -/
theorem VShape.tiling_of_fraction_fixed (v : VShape) (u d : ℕ) (hu0 : 0 < u) (hud : u < d)
    (hs : v.s = (u : ℝ) / d) :
    Nonempty (CongruentTiling v.outer (v.fractionTile d (lt_trans hu0 hud))
      (d ^ 2 * (2 * d ^ 2 - u ^ 2))) := by
  have hd0 : 0 < d := lt_trans hu0 hud
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdne := ne_of_gt hdR
  have hsq : u ^ 2 < d ^ 2 := by nlinarith
  have hsub : u ^ 2 ≤ 2 * d ^ 2 := by omega
  let ε : ℝ := 1 / (d : ℝ) ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hm0 : 0 < u ^ 2 := pow_pos hu0 _
  have hn0 : 0 < d ^ 2 - u ^ 2 := Nat.sub_pos_of_lt hsq
  have hk0 : 0 < u * d := Nat.mul_pos hu0 hd0
  have hb : v.b = 1 - ((u : ℝ) / d) ^ 2 := by
    have h := v.s_sq
    rw [hs] at h
    linarith
  have hm : ((u ^ 2 : ℕ) : ℝ) * ε = 1 - v.b := by
    rw [hb]
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hn : ((d ^ 2 - u ^ 2 : ℕ) : ℝ) * ε = v.b := by
    rw [Nat.cast_sub hsq.le, hb]
    dsimp [ε]
    push_cast
    field_simp
  have hk : ((u * d : ℕ) : ℝ) * ε = v.s := by
    rw [hs]
    dsimp [ε]
    push_cast
    field_simp
  have hcount : (d ^ 2 - u ^ 2) ^ 2 + (d ^ 2 - u ^ 2) ^ 2 + (u * d) ^ 2 +
      2 * u ^ 2 * (d ^ 2 - u ^ 2) = d ^ 2 * (2 * d ^ 2 - u ^ 2) := by
    have hreal : (((d ^ 2 - u ^ 2) ^ 2 + (d ^ 2 - u ^ 2) ^ 2 + (u * d) ^ 2 +
        2 * u ^ 2 * (d ^ 2 - u ^ 2) : ℕ) : ℝ) =
        ((d ^ 2 * (2 * d ^ 2 - u ^ 2) : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hsq.le, Nat.cast_sub hsub]
      ring
    exact_mod_cast hreal
  have hT := v.tiling_of_integer_scales ε hε (u ^ 2) (d ^ 2 - u ^ 2) (u * d)
    hm0 hn0 hk0 hm hn hk
  rw [hcount] at hT
  exact hT

/-- The existential form of the exact V-family construction. -/
theorem VShape.tiling_of_fraction (v : VShape) (u d : ℕ) (hu0 : 0 < u) (hud : u < d)
    (hs : v.s = (u : ℝ) / d) :
    ∃ R : Triangle, Nonempty (CongruentTiling v.outer R (d ^ 2 * (2 * d ^ 2 - u ^ 2))) :=
  ⟨_, v.tiling_of_fraction_fixed u d hu0 hud hs⟩

/-- A rational parameter with nonsquare `2-s²` gives an actual nonsquare
congruent tiling of the Euclidean outer triangle. -/
theorem VShape.admitsNonsquareTiling_of_rational (v : VShape) (s : ℚ)
    (hs : v.s = (s : ℝ)) (hns : ¬ IsSquare (2 - s ^ 2)) :
    AdmitsNonsquareTiling v.outer := by
  have hs0 : 0 < s := by exact_mod_cast (hs ▸ v.s_pos)
  have hsR1 : (s : ℝ) < 1 := by
    have hp := v.s_pos
    have hq := v.s_sq
    rw [hs] at hp hq
    nlinarith [v.b_pos]
  have hs1 : s < 1 := by exact_mod_cast hsR1
  obtain ⟨u, d, _, hud, hfrac⟩ := rational_parameter_coordinates hs0.le hs1
  have hu0 : 0 < u := by
    by_contra h
    have hu : u = 0 := by omega
    simp only [hu, Nat.cast_zero, zero_div] at hfrac
    linarith
  have hsfrac : v.s = (u : ℝ) / d := by
    rw [hs, hfrac]
    push_cast
    rfl
  obtain ⟨R, hT⟩ := v.tiling_of_fraction u d hu0 hud hsfrac
  refine ⟨d ^ 2 * (2 * d ^ 2 - u ^ 2), R, ?_, hT⟩
  intro hN
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hud
  have hnum : IsSquare (2 * d ^ 2 - u ^ 2) := by
    have hcast : IsSquare ((d : ℚ) ^ 2 * ((2 * d ^ 2 - u ^ 2 : ℕ) : ℚ)) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using (Rat.isSquare_natCast_iff.mpr hN)
    exact Rat.isSquare_natCast_iff.mp ((isSquare_sq_mul_iff (d : ℚ) _ hdQ).mp hcast)
  apply hns
  rw [hfrac]
  exact (groupOne_V_isSquare_iff hud).mpr hnum

/-- Explicit Euclidean realization for every rational parameter in `(0,1)`. -/
noncomputable def VShape.ofRational (s : ℚ) (hs0 : 0 < s) (hs1 : s < 1) : VShape :=
  VShape.ofParameter (1 - (s : ℝ) ^ 2)
    (by
      have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
      have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
      nlinarith)
    (by
      have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
      nlinarith [sq_pos_of_pos h0])

theorem VShape.ofRational_s (s : ℚ) (hs0 : 0 < s) (hs1 : s < 1) :
    (VShape.ofRational s hs0 hs1).s = (s : ℝ) := by
  change Real.sqrt (1 - (1 - (s : ℝ) ^ 2)) = (s : ℝ)
  rw [show 1 - (1 - (s : ℝ) ^ 2) = (s : ℝ) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_pos (by exact_mod_cast hs0)]

/-- An unconditional parameterized family of actual nonsquare congruent tilings.
Identifying this coordinate family with the angle formulation is separate. -/
theorem rationalV_admitsNonsquareTiling (s : ℚ) (hs0 : 0 < s) (hs1 : s < 1)
    (hns : ¬ IsSquare (2 - s ^ 2)) :
    AdmitsNonsquareTiling (VShape.ofRational s hs0 hs1).outer :=
  (VShape.ofRational s hs0 hs1).admitsNonsquareTiling_of_rational s
    (VShape.ofRational_s s hs0 hs1) hns

/-- A side-length criterion for the entire Euclidean similarity class of the
constructed V family, including arbitrary position and reflected orientation. -/
theorem Triangle.admitsNonsquareTiling_of_V_sides (P : Triangle)
    (s : ℚ) (hs0 : 0 < s) (hs1 : s < 1) (hns : ¬ IsSquare (2 - s ^ 2))
    (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * (1 - (s : ℝ) ^ 2) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * ((s : ℝ) * (2 - (s : ℝ) ^ 2)) ^ 2) :
    AdmitsNonsquareTiling P := by
  let v := VShape.ofRational s hs0 hs1
  have hs : v.s = (s : ℝ) := VShape.ofRational_s s hs0 hs1
  have hb : v.b = 1 - (s : ℝ) ^ 2 := rfl
  have hQ := admitsNonsquareTiling_mapSimilarity
    (rationalV_admitsNonsquareTiling s hs0 hs1 hns) 0 (q : ℂ)
    (by exact_mod_cast ne_of_gt hq)
  apply admitsNonsquareTiling_of_congruent hQ
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * v.outer.b) - (0 + (q : ℂ) * v.outer.a)) = _
    rw [normSq_similarity_sub, v.outer_side_squares.1, Complex.normSq_ofReal, hab]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * v.outer.c) - (0 + (q : ℂ) * v.outer.a)) = _
    rw [normSq_similarity_sub, v.outer_side_squares.2.1, Complex.normSq_ofReal, hb, hac]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * v.outer.c) - (0 + (q : ℂ) * v.outer.b)) = _
    rw [normSq_similarity_sub, v.outer_side_squares.2.2, Complex.normSq_ofReal, hb, hs, hbc]
    ring

/-- The parameter `1/2` specializes the construction to an actual 28-tiling. -/
theorem rationalV_one_half_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (VShape.ofRational (1 / 2) (by norm_num) (by norm_num)).outer R 28) := by
  let v := VShape.ofRational (1 / 2) (by norm_num) (by norm_num)
  have hs : v.s = (1 : ℝ) / 2 := by
    rw [VShape.ofRational_s]
    norm_num
  have h := v.tiling_of_fraction 1 2 (by norm_num) (by norm_num) (by simpa using hs)
  norm_num at h
  exact h

/-- The square exceptional parameter is not discarded: the same construction
gives 1225 tiles when `s = 1/5`. This is not a necessity assertion. -/
theorem rationalV_one_fifth_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (VShape.ofRational (1 / 5) (by norm_num) (by norm_num)).outer R 1225) := by
  let v := VShape.ofRational (1 / 5) (by norm_num) (by norm_num)
  have hs : v.s = (1 : ℝ) / 5 := by
    rw [VShape.ofRational_s]
    norm_num
  have h := v.tiling_of_fraction 1 5 (by norm_num) (by norm_num) (by simpa using hs)
  norm_num at h
  exact h

end Erdos633

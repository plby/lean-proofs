import ErdosProblems.Erdos633.RightTiling

/-!
# Three congruent pieces in the 30-60-90 similarity class

The construction uses vertices `0`, `I`, `sqrt(3)`, the point `sqrt(3)/3`
on the real leg, and the midpoint of the hypotenuse. Two applications of
the general splitting theorem certify coverage and disjointness.
-/

namespace Erdos633

noncomputable def thirtyTriangle : Triangle where
  a := 0
  b := Complex.I
  c := (Real.sqrt 3 : ℂ)
  nondegenerate := by
    change orientedDoubleArea 0 Complex.I (Real.sqrt 3 : ℂ) ≠ 0
    simp [orientedDoubleArea]

noncomputable def thirtySmall : Triangle :=
  thirtyTriangle.splitFirst (1 / 3) (by norm_num)

noncomputable def thirtyRest : Triangle :=
  (thirtyTriangle.splitSecond (1 / 3) (by norm_num)).swapBC.swapAB

theorem thirty_splitPoint :
    thirtyTriangle.coordinateEquiv (⟨0, (1 / 3 : ℝ)⟩ : ℂ) = ((Real.sqrt 3 / 3 : ℝ) : ℂ) := by
  apply Complex.ext
  all_goals simp only [Triangle.coordinateEquiv_apply, thirtyTriangle,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, Complex.zero_re, Complex.zero_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, smul_eq_mul]
  all_goals ring

theorem thirtySmall_vertices : thirtySmall.a = 0 ∧ thirtySmall.b = Complex.I ∧
    thirtySmall.c = ((Real.sqrt 3 / 3 : ℝ) : ℂ) := by
  exact ⟨thirtyTriangle.coordinateEquiv_zero, thirtyTriangle.coordinateEquiv_one,
    thirty_splitPoint⟩

theorem thirtyRest_vertices : thirtyRest.a = (Real.sqrt 3 : ℂ) ∧
    thirtyRest.b = ((Real.sqrt 3 / 3 : ℝ) : ℂ) ∧ thirtyRest.c = Complex.I := by
  exact ⟨thirtyTriangle.coordinateEquiv_I, thirty_splitPoint, thirtyTriangle.coordinateEquiv_one⟩

theorem thirtyRest_carrier : thirtyRest.carrier =
    (thirtyTriangle.splitSecond (1 / 3) (by norm_num)).carrier := by
  simp only [thirtyRest, Triangle.swapAB_carrier, Triangle.swapBC_carrier]

theorem thirty_midpoint :
    thirtyRest.coordinateEquiv (⟨0, (1 / 2 : ℝ)⟩ : ℂ) =
      (⟨Real.sqrt 3 / 2, 1 / 2⟩ : ℂ) := by
  rw [Triangle.coordinateEquiv_apply, thirtyRest_vertices.1,
    thirtyRest_vertices.2.1, thirtyRest_vertices.2.2]
  apply Complex.ext
  all_goals simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.smul_re, Complex.smul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, smul_eq_mul]
  all_goals ring

theorem thirty_first_congruent :
    ∃ e : ℂ ≃ᵢ ℂ, e '' thirtySmall.carrier =
      (thirtyRest.splitFirst (1 / 2) (by norm_num)).carrier := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  suffices h : ∃ e : ℂ ≃ᵢ ℂ, e '' thirtySmall.carrier =
      (thirtyRest.splitFirst (1 / 2) (by norm_num)).swapAC.swapBC.carrier by
    simpa only [Triangle.swapBC_carrier, Triangle.swapAC_carrier] using h
  apply Triangle.congruent_of_normSq
  all_goals simp only [Triangle.swapAC, Triangle.swapAB, Triangle.swapBC,
    Triangle.splitFirst_a, Triangle.splitFirst_b, Triangle.splitFirst_c,
    thirtySmall_vertices.1, thirtySmall_vertices.2.1, thirtySmall_vertices.2.2,
    thirtyRest_vertices.1, thirtyRest_vertices.2.1,
    thirty_midpoint, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  all_goals nlinarith

theorem thirty_second_congruent :
    ∃ e : ℂ ≃ᵢ ℂ, e '' thirtySmall.carrier =
      (thirtyRest.splitSecond (1 / 2) (by norm_num)).carrier := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  suffices h : ∃ e : ℂ ≃ᵢ ℂ, e '' thirtySmall.carrier =
      (thirtyRest.splitSecond (1 / 2) (by norm_num)).swapBC.carrier by
    simpa only [Triangle.swapBC_carrier] using h
  apply Triangle.congruent_of_normSq
  all_goals simp only [Triangle.swapBC, Triangle.splitSecond_a, Triangle.splitSecond_b,
    Triangle.splitSecond_c, thirtySmall_vertices.1, thirtySmall_vertices.2.1,
    thirtySmall_vertices.2.2, thirtyRest_vertices.2.1,
    thirtyRest_vertices.2.2, thirty_midpoint, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  all_goals nlinarith

/-- The standard 30-60-90 triangle has a genuine three-piece congruent tiling. -/
theorem thirty_three_tiling : Nonempty (CongruentTiling thirtyTriangle thirtySmall 3) := by
  obtain ⟨e₁, he₁⟩ := thirty_first_congruent
  obtain ⟨e₂, he₂⟩ := thirty_second_congruent
  let T₁ := (thirtySmall.oneTiling.mapIsometry e₁).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e₁).trans he₁)
  let T₂ := (thirtySmall.oneTiling.mapIsometry e₂).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e₂).trans he₂)
  let TR := thirtyRest.glueSplitTilings (1 / 2) (by norm_num) (by norm_num) T₁ T₂
  let TS := TR.of_carrier_eq thirtyRest_carrier
  exact ⟨thirtyTriangle.glueSplitTilings (1 / 3) (by norm_num) (by norm_num)
    thirtySmall.oneTiling TS⟩

theorem thirty_admitsNonsquareTiling : AdmitsNonsquareTiling thirtyTriangle := by
  exact ⟨3, thirtySmall, by norm_num, thirty_three_tiling⟩

theorem thirtyTriangle_side_squares :
    Complex.normSq (thirtyTriangle.b - thirtyTriangle.a) = 1 ∧
    Complex.normSq (thirtyTriangle.c - thirtyTriangle.a) = 3 ∧
    Complex.normSq (thirtyTriangle.c - thirtyTriangle.b) = 4 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [thirtyTriangle, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  constructor
  · norm_num
  constructor <;> nlinarith

/-- Every triangle with side ratios `1 : sqrt(3) : 2` admits a nonsquare tiling. -/
theorem Triangle.admitsNonsquareTiling_of_thirty_sides (P : Triangle) (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2)
    (hac : Complex.normSq (P.c - P.a) = 3 * q ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = 4 * q ^ 2) : AdmitsNonsquareTiling P := by
  have hQ := admitsNonsquareTiling_mapSimilarity thirty_admitsNonsquareTiling 0 (q : ℂ)
    (by exact_mod_cast ne_of_gt hq)
  apply admitsNonsquareTiling_of_congruent hQ
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * thirtyTriangle.b) -
      (0 + (q : ℂ) * thirtyTriangle.a)) = _
    rw [normSq_similarity_sub, thirtyTriangle_side_squares.1, Complex.normSq_ofReal, hab]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * thirtyTriangle.c) -
      (0 + (q : ℂ) * thirtyTriangle.a)) = _
    rw [normSq_similarity_sub, thirtyTriangle_side_squares.2.1, Complex.normSq_ofReal, hac]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * thirtyTriangle.c) -
      (0 + (q : ℂ) * thirtyTriangle.b)) = _
    rw [normSq_similarity_sub, thirtyTriangle_side_squares.2.2, Complex.normSq_ofReal, hbc]
    ring

end Erdos633

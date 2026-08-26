import ErdosProblems.Erdos633.UGeometry
import ErdosProblems.Erdos633.VTiling

/-!
# Actual nonsquare tilings of the companion U family

The V tiling and an integer square subdivision of the attached triangle
use the same reference tile. Their counts add to
`(2d²-u²)(3d²-u²)`, which is nonsquare for reduced `0 < u < d`.
-/

namespace Erdos633

theorem VShape.uTiling_of_fraction (v : VShape) (u d : ℕ) (hu0 : 0 < u) (hud : u < d)
    (hs : v.s = (u : ℝ) / d) :
    Nonempty (CongruentTiling v.uOuter (v.fractionTile d (lt_trans hu0 hud))
      ((2 * d ^ 2 - u ^ 2) * (3 * d ^ 2 - u ^ 2))) := by
  have hd0 : 0 < d := lt_trans hu0 hud
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdne := ne_of_gt hdR
  have hsq : u ^ 2 < d ^ 2 := by nlinarith
  have hsub : u ^ 2 ≤ 2 * d ^ 2 := by omega
  have hp0 : 0 < 2 * d ^ 2 - u ^ 2 := by omega
  let ε : ℝ := 1 / (d : ℝ) ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : 0 < 1 + v.b := by linarith [v.b_pos]
  have hb : v.b = 1 - ((u : ℝ) / d) ^ 2 := by
    have h := v.s_sq
    rw [hs] at h
    linarith
  have hp : ((2 * d ^ 2 - u ^ 2 : ℕ) : ℝ) * ε = 1 + v.b := by
    rw [Nat.cast_sub hsub, hb]
    dsimp [ε]
    push_cast
    field_simp
    ring
  obtain ⟨TV⟩ := v.tiling_of_fraction_fixed u d hu0 hud hs
  obtain ⟨e, he⟩ := v.uAttached_congruent
  let TD := v.reference.scaleTiling ε (1 + v.b) hε hscale (2 * d ^ 2 - u ^ 2) hp0 hp
  let TA := (TD.mapIsometry e).of_carrier_eq
    ((Triangle.mapIsometry_carrier _ e).trans he)
  let TF := TV.of_carrier_eq (congrArg Triangle.carrier v.uSplitFirst_eq.symm)
  have hT := v.uOuter.glueSplitTilings v.uSplitRatio v.uSplitRatio_pos
    v.uSplitRatio_lt_one TF TA
  have hcount : d ^ 2 * (2 * d ^ 2 - u ^ 2) + (2 * d ^ 2 - u ^ 2) ^ 2 =
      (2 * d ^ 2 - u ^ 2) * (3 * d ^ 2 - u ^ 2) := by
    have hsum : d ^ 2 + (2 * d ^ 2 - u ^ 2) = 3 * d ^ 2 - u ^ 2 := by omega
    calc
      d ^ 2 * (2 * d ^ 2 - u ^ 2) + (2 * d ^ 2 - u ^ 2) ^ 2 =
          (2 * d ^ 2 - u ^ 2) * (d ^ 2 + (2 * d ^ 2 - u ^ 2)) := by ring
      _ = _ := by rw [hsum]
  rw [hcount] at hT
  exact ⟨hT⟩

/-- Every rational U parameter in the nondegenerate range admits a nonsquare
congruent tiling; no additional square-class hypothesis is required. -/
theorem VShape.uAdmitsNonsquareTiling_of_rational (v : VShape) (s : ℚ)
    (hs : v.s = (s : ℝ)) : AdmitsNonsquareTiling v.uOuter := by
  have hs0 : 0 < s := by exact_mod_cast (hs ▸ v.s_pos)
  have hsR1 : (s : ℝ) < 1 := by
    have hp := v.s_pos
    have hq := v.s_sq
    rw [hs] at hp hq
    nlinarith [v.b_pos]
  have hs1 : s < 1 := by exact_mod_cast hsR1
  obtain ⟨u, d, hcoprime, hud, hfrac⟩ := rational_parameter_coordinates hs0.le hs1
  have hu0 : 0 < u := by
    by_contra h
    have hu : u = 0 := by omega
    simp only [hu, Nat.cast_zero, zero_div] at hfrac
    linarith
  have hsfrac : v.s = (u : ℝ) / d := by
    rw [hs, hfrac]
    push_cast
    rfl
  exact ⟨(2 * d ^ 2 - u ^ 2) * (3 * d ^ 2 - u ^ 2), _,
    groupOne_U_numerator_not_isSquare hcoprime hud,
    v.uTiling_of_fraction u d hu0 hud hsfrac⟩

theorem rationalU_admitsNonsquareTiling (s : ℚ) (hs0 : 0 < s) (hs1 : s < 1) :
    AdmitsNonsquareTiling (VShape.ofRational s hs0 hs1).uOuter :=
  (VShape.ofRational s hs0 hs1).uAdmitsNonsquareTiling_of_rational s
    (VShape.ofRational_s s hs0 hs1)

/-- A sufficient side criterion for every position, scale, and orientation
of the constructed U similarity class. -/
theorem Triangle.admitsNonsquareTiling_of_U_sides (P : Triangle)
    (s : ℚ) (hs0 : 0 < s) (hs1 : s < 1) (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2)
    (hac : Complex.normSq (P.c - P.a) =
      q ^ 2 * ((1 - (s : ℝ) ^ 2) * (3 - (s : ℝ) ^ 2)) ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * (2 - (s : ℝ) ^ 2) ^ 2) :
    AdmitsNonsquareTiling P := by
  let v := VShape.ofRational s hs0 hs1
  have hb : v.b = 1 - (s : ℝ) ^ 2 := rfl
  have hQ := admitsNonsquareTiling_mapSimilarity
    (rationalU_admitsNonsquareTiling s hs0 hs1) 0 (q : ℂ)
    (by exact_mod_cast ne_of_gt hq)
  apply admitsNonsquareTiling_of_congruent hQ
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * v.uOuter.b) - (0 + (q : ℂ) * v.uOuter.a)) = _
    rw [normSq_similarity_sub, v.uOuter_side_squares.1, Complex.normSq_ofReal, hab]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * v.uOuter.c) - (0 + (q : ℂ) * v.uOuter.a)) = _
    rw [normSq_similarity_sub, v.uOuter_side_squares.2.1, Complex.normSq_ofReal, hb, hac]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * v.uOuter.c) - (0 + (q : ℂ) * v.uOuter.b)) = _
    rw [normSq_similarity_sub, v.uOuter_side_squares.2.2, Complex.normSq_ofReal, hb, hbc]
    ring

/-- The parameter `1/2` gives an actual 77-piece congruent tiling. -/
theorem rationalU_one_half_tiling :
    ∃ R : Triangle, Nonempty (CongruentTiling
      (VShape.ofRational (1 / 2) (by norm_num) (by norm_num)).uOuter R 77) := by
  let v := VShape.ofRational (1 / 2) (by norm_num) (by norm_num)
  have hs : v.s = (1 : ℝ) / 2 := by
    rw [VShape.ofRational_s]
    norm_num
  have h := v.uTiling_of_fraction 1 2 (by norm_num) (by norm_num) (by simpa using hs)
  norm_num at h
  exact ⟨_, h⟩

end Erdos633

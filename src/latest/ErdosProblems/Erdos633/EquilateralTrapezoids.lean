import ErdosProblems.Erdos633.TrapezoidRows

/-!
# Three rotated trapezoids cover an equilateral triangle

The affine formula in hexagonal coordinates is realized by an actual
120-degree Euclidean rotation. Thus rotating a congruent trapezoid tiling
does not change its reference tile.
-/

namespace Erdos633

theorem hexUnit_sq : hexUnit ^ 2 = hexUnit - 1 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  all_goals simp only [hexUnit, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  all_goals nlinarith

theorem hexUnit_sub_one_normSq : Complex.normSq (hexUnit - 1) = 1 :=
  hexTriangle_side_squares.2.2

theorem hexUnit_sub_one_ne_zero : hexUnit - 1 ≠ 0 := by
  intro h
  have he := hexUnit_sub_one_normSq
  rw [h, map_zero] at he
  norm_num at he

noncomputable def hexRotation (q : ℝ) : ℂ ≃ᵢ ℂ where
  toEquiv := similarityEquiv ((3 * q : ℝ) : ℂ) (hexUnit - 1) hexUnit_sub_one_ne_zero
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro z w
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_eq_norm, ← Complex.normSq_eq_norm_sq]
    change Complex.normSq (((3 * q : ℝ) : ℂ) + (hexUnit - 1) * z -
      (((3 * q : ℝ) : ℂ) + (hexUnit - 1) * w)) = Complex.normSq (z - w)
    rw [normSq_similarity_sub, hexUnit_sub_one_normSq, one_mul]

def hexRotationCoordinates (q : ℝ) (z : ℂ) : ℂ := ⟨3 * q - z.re - z.im, z.re⟩

theorem hexRotation_apply_coordinates (q : ℝ) (z : ℂ) :
    hexRotation q (hexCoordinates z) = hexCoordinates (hexRotationCoordinates q z) := by
  change ((3 * q : ℝ) : ℂ) + (hexUnit - 1) * hexCoordinates z = _
  simp only [hexCoordinates_apply, hexRotationCoordinates]
  push_cast
  linear_combination (z.im : ℂ) * hexUnit_sq

def equilateralTrapOne (q : ℝ) : Set ℂ :=
  {z | q ≤ z.re ∧ 0 ≤ z.im ∧ 2 * q ≤ z.re + z.im ∧ z.re + z.im ≤ 3 * q}

def equilateralTrapTwo (q : ℝ) : Set ℂ :=
  {z | 0 ≤ z.re ∧ z.re ≤ q ∧ q ≤ z.im ∧ z.re + z.im ≤ 3 * q}

theorem equilateralTrap_rotate_zero (q : ℝ) :
    hexRotationCoordinates q '' slantedTrapezoid q (2 * q) = equilateralTrapOne q := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change q ≤ 3 * q - w.re - w.im ∧ 0 ≤ w.re ∧
      2 * q ≤ (3 * q - w.re - w.im) + w.re ∧
      (3 * q - w.re - w.im) + w.re ≤ 3 * q
    exact ⟨by linarith [hw.2.2.2], hw.1,
      by linarith [hw.2.2.1], by linarith [hw.2.1]⟩
  · intro hz
    refine ⟨⟨z.im, 3 * q - z.re - z.im⟩, ?_, ?_⟩
    · exact ⟨hz.2.1, by linarith [hz.2.2.2],
        by linarith [hz.2.2.1], by linarith [hz.1]⟩
    · apply Complex.ext
      · dsimp [hexRotationCoordinates]
        ring
      · rfl

theorem equilateralTrap_rotate_one (q : ℝ) :
    hexRotationCoordinates q '' equilateralTrapOne q = equilateralTrapTwo q := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change 0 ≤ 3 * q - w.re - w.im ∧ 3 * q - w.re - w.im ≤ q ∧
      q ≤ w.re ∧ (3 * q - w.re - w.im) + w.re ≤ 3 * q
    exact ⟨by linarith [hw.2.2.2], by linarith [hw.2.2.1],
      hw.1, by linarith [hw.2.1]⟩
  · intro hz
    refine ⟨⟨z.im, 3 * q - z.re - z.im⟩, ?_, ?_⟩
    · exact ⟨hz.2.2.1, by linarith [hz.2.2.2],
        by linarith [hz.2.1], by linarith [hz.1]⟩
    · apply Complex.ext
      · dsimp [hexRotationCoordinates]
        ring
      · rfl

theorem hexRotation_image_coordinates (q : ℝ) (S : Set ℂ) :
    hexRotation q '' (hexCoordinates '' S) =
      hexCoordinates '' (hexRotationCoordinates q '' S) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  exact hexRotation_apply_coordinates q z

theorem equilateralTraps_cover (q : ℝ) (hq : 0 ≤ q) :
    (slantedTrapezoid q (2 * q) ∪ equilateralTrapOne q) ∪ equilateralTrapTwo q =
      {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 3 * q} := by
  ext z
  simp only [Set.mem_union, slantedTrapezoid, equilateralTrapOne,
    equilateralTrapTwo, Set.mem_ofPred_eq]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨h.1, h.2.1, by linarith [h.2.2.2]⟩
    · exact ⟨by linarith [h.1], h.2.1, h.2.2.2⟩
    · exact ⟨h.1, by linarith [h.2.2.1], h.2.2.2⟩
  · rintro ⟨hx, hy, hs⟩
    by_cases hsum : z.re + z.im ≤ 2 * q
    · by_cases hrow : z.im ≤ q
      · exact Or.inl (Or.inl ⟨hx, hy, hrow, hsum⟩)
      · exact Or.inr ⟨hx, by linarith, by linarith, hs⟩
    · by_cases hxq : q ≤ z.re
      · exact Or.inl (Or.inr ⟨hxq, hy, by linarith, hs⟩)
      · exact Or.inr ⟨hx, by linarith, by linarith, hs⟩

theorem equilateralTraps_disjoint_zero_one (q : ℝ) :
    Disjoint (interior (slantedTrapezoid q (2 * q))) (interior (equilateralTrapOne q)) := by
  apply separated_interiors (linearXPlusY 1) (linearXPlusY_surjective _) (2 * q)
  · intro z hz
    change z.re + 1 * z.im ≤ 2 * q
    linarith [hz.2.2.2]
  · intro z hz
    change 2 * q ≤ z.re + 1 * z.im
    linarith [hz.2.2.1]

theorem equilateralTraps_disjoint_zero_two (q : ℝ) :
    Disjoint (interior (slantedTrapezoid q (2 * q))) (interior (equilateralTrapTwo q)) := by
  exact separated_interiors Complex.imCLM (fun r => ⟨⟨0, r⟩, rfl⟩) q
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.1)

theorem equilateralTraps_disjoint_one_two (q : ℝ) :
    Disjoint (interior (equilateralTrapOne q)) (interior (equilateralTrapTwo q)) := by
  exact (separated_interiors Complex.reCLM (fun r => ⟨(r : ℂ), rfl⟩) q
    (fun _ h => h.2.1) (fun _ h => h.1)).symm

noncomputable def hexEquilateral (n : ℕ) (hn : 0 < n) : Triangle :=
  (dilatedStandardTriangle n hn).mapAffineEquiv hexCoordinates

theorem hexEquilateral_carrier (n : ℕ) (hn : 0 < n) :
    (hexEquilateral n hn).carrier =
      hexCoordinates '' {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ n} := by
  rw [hexEquilateral, Triangle.mapAffineEquiv_carrier]
  congr 1
  ext z
  exact dilatedStandardTriangle_mem_iff n hn z

/-- Three rotated copies of any tiling of the ideal trapezoid produce an
equilateral triangle tiling with exactly three times the number of pieces. -/
noncomputable def equilateralTiling_of_trapezoid (q : ℕ) (hq : 0 < q)
    {R : Triangle} {ι : Type*} [Fintype ι]
    (T : RegionTiling (hexCoordinates '' slantedTrapezoid (q : ℝ) (2 * q)) R ι) :
    CongruentTiling (hexEquilateral (3 * q) (by positivity)) R (3 * Fintype.card ι) := by
  let U := (T.mapIsometry (hexRotation q)).of_region_eq (by
    rw [hexRotation_image_coordinates, equilateralTrap_rotate_zero])
  let V := (U.mapIsometry (hexRotation q)).of_region_eq (by
    rw [hexRotation_image_coordinates, equilateralTrap_rotate_one])
  let F := T.unionThree U V
    (disjoint_interiors_affine_image hexCoordinates (equilateralTraps_disjoint_zero_one q))
    (disjoint_interiors_affine_image hexCoordinates (equilateralTraps_disjoint_zero_two q))
    (disjoint_interiors_affine_image hexCoordinates (equilateralTraps_disjoint_one_two q))
  have hcover : ((hexCoordinates '' slantedTrapezoid (q : ℝ) (2 * q) ∪
      hexCoordinates '' equilateralTrapOne q) ∪ hexCoordinates '' equilateralTrapTwo q) =
        (hexEquilateral (3 * q) (by positivity)).carrier := by
    rw [← Set.image_union, ← Set.image_union, equilateralTraps_cover q (by positivity),
      hexEquilateral_carrier]
    push_cast
    rfl
  have hcard : Fintype.card ((ι ⊕ ι) ⊕ ι) = 3 * Fintype.card ι := by
    simp only [Fintype.card_sum]
    omega
  exact hcard ▸ F.toCongruentTiling _ hcover

end Erdos633

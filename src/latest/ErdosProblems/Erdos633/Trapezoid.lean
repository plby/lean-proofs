import ErdosProblems.Erdos633.VPieces

/-!
# A three-triangle decomposition of a trapezoid

The trapezoid has vertices `(0,0)`, `(L,0)`, `(L-H,H)`, and `(0,H)`.
An arbitrary point `(p,H)` in the relative interior of the top edge is joined
to both bottom vertices. The three resulting closed triangles cover the
trapezoid and have pairwise disjoint interiors.
-/

namespace Erdos633

noncomputable def linearForm (u v : ℝ) : ℂ →L[ℝ] ℝ :=
  u • Complex.reCLM + v • Complex.imCLM

theorem linearForm_apply (u v : ℝ) (z : ℂ) : linearForm u v z = u * z.re + v * z.im :=
  rfl

theorem linearForm_surjective (u v : ℝ) (hu : u ≠ 0) :
    Function.Surjective (linearForm u v) := by
  intro r
  refine ⟨((r / u : ℝ) : ℂ), ?_⟩
  simp only [linearForm_apply, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
  field_simp

structure TrapezoidFan where
  H : ℝ
  L : ℝ
  p : ℝ
  H_pos : 0 < H
  p_pos : 0 < p
  top_right_pos : 0 < L - H - p

theorem TrapezoidFan.L_pos (F : TrapezoidFan) : 0 < F.L := by
  linarith [F.H_pos, F.p_pos, F.top_right_pos]

def TrapezoidFan.region (F : TrapezoidFan) : Set ℂ :=
  {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ F.H ∧ z.re + z.im ≤ F.L}

def TrapezoidFan.leftRegion (F : TrapezoidFan) : Set ℂ :=
  {z | 0 ≤ z.re ∧ F.H * z.re ≤ F.p * z.im ∧ z.im ≤ F.H}

def TrapezoidFan.centerRegion (F : TrapezoidFan) : Set ℂ :=
  {z | 0 ≤ z.im ∧ F.p * z.im ≤ F.H * z.re ∧
    F.H * z.re + (F.L - F.p) * z.im ≤ F.H * F.L}

def TrapezoidFan.rightRegion (F : TrapezoidFan) : Set ℂ :=
  {z | z.re + z.im ≤ F.L ∧
    F.H * F.L ≤ F.H * z.re + (F.L - F.p) * z.im ∧ z.im ≤ F.H}

def TrapezoidFan.left (F : TrapezoidFan) : Triangle where
  a := 0
  b := ⟨0, F.H⟩
  c := ⟨F.p, F.H⟩
  nondegenerate := by
    simpa using neg_ne_zero.mpr (mul_ne_zero (ne_of_gt F.H_pos) (ne_of_gt F.p_pos))

def TrapezoidFan.center (F : TrapezoidFan) : Triangle where
  a := 0
  b := (F.L : ℂ)
  c := ⟨F.p, F.H⟩
  nondegenerate := by
    simpa using mul_ne_zero (ne_of_gt F.L_pos) (ne_of_gt F.H_pos)

def TrapezoidFan.right (F : TrapezoidFan) : Triangle where
  a := (F.L : ℂ)
  b := ⟨F.L - F.H, F.H⟩
  c := ⟨F.p, F.H⟩
  nondegenerate := by
    have h : (F.L - F.H - F.L) * F.H - F.H * (F.p - F.L) =
        F.H * (F.L - F.H - F.p) := by ring
    simpa only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, h] using
      mul_ne_zero (ne_of_gt F.H_pos) (ne_of_gt F.top_right_pos)

theorem TrapezoidFan.leftRegion_convex (F : TrapezoidFan) : Convex ℝ F.leftRegion := by
  have h := (convex_linear_ge Complex.reCLM 0).inter
    ((convex_linear_le (linearForm F.H (-F.p)) 0).inter
      (convex_linear_le Complex.imCLM F.H))
  convert h using 1
  ext z
  simp only [leftRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, linearForm_apply]
  constructor <;> rintro ⟨hx, hs, hy⟩ <;> exact ⟨hx, by linarith, hy⟩

theorem TrapezoidFan.centerRegion_convex (F : TrapezoidFan) :
    Convex ℝ F.centerRegion := by
  have h := (convex_linear_ge Complex.imCLM 0).inter
    ((convex_linear_ge (linearForm F.H (-F.p)) 0).inter
      (convex_linear_le (linearForm F.H (F.L - F.p)) (F.H * F.L)))
  convert h using 1
  ext z
  simp only [centerRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, linearForm_apply]
  constructor <;> rintro ⟨hy, hs, ht⟩ <;> exact ⟨hy, by linarith, ht⟩

theorem TrapezoidFan.rightRegion_convex (F : TrapezoidFan) : Convex ℝ F.rightRegion := by
  have h := (convex_linear_le (linearXPlusY 1) F.L).inter
    ((convex_linear_ge (linearForm F.H (F.L - F.p)) (F.H * F.L)).inter
      (convex_linear_le Complex.imCLM F.H))
  convert h using 1
  ext z
  simp only [rightRegion, Set.mem_ofPred_eq, Set.mem_inter_iff,
    linearXPlusY_apply, one_mul, linearForm_apply]
  rfl

theorem TrapezoidFan.left_carrier (F : TrapezoidFan) : F.left.carrier = F.leftRegion := by
  have hH := ne_of_gt F.H_pos
  have hp := ne_of_gt F.p_pos
  apply Set.Subset.antisymm
  · apply convexHull_min _ F.leftRegion_convex
    intro z hz
    change z ∈ ({0, (⟨0, F.H⟩ : ℂ), ⟨F.p, F.H⟩} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl
    all_goals simp [leftRegion, F.H_pos.le, F.p_pos.le,
      mul_nonneg F.H_pos.le F.p_pos.le, mul_comm]
  · intro z hz
    apply mem_convexHull_three_of_weights 0 ⟨0, F.H⟩ ⟨F.p, F.H⟩ z
      ((F.H - z.im) / F.H) ((F.p * z.im - F.H * z.re) / (F.p * F.H)) (z.re / F.p)
    · exact div_nonneg (by linarith [hz.2.2]) F.H_pos.le
    · exact div_nonneg (by linarith [hz.2.1]) (mul_nonneg F.p_pos.le F.H_pos.le)
    · exact div_nonneg hz.1 F.p_pos.le
    · field_simp
      ring
    · apply Complex.ext
      all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, Complex.zero_re, Complex.zero_im, smul_eq_mul]
      all_goals field_simp
      all_goals ring

theorem TrapezoidFan.center_carrier (F : TrapezoidFan) :
    F.center.carrier = F.centerRegion := by
  have hH := ne_of_gt F.H_pos
  have hL := ne_of_gt F.L_pos
  apply Set.Subset.antisymm
  · apply convexHull_min _ F.centerRegion_convex
    intro z hz
    change z ∈ ({0, (F.L : ℂ), (⟨F.p, F.H⟩ : ℂ)} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl
    all_goals simp only [centerRegion, Set.mem_ofPred_eq, Complex.zero_re,
      Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im]
    all_goals constructor
    all_goals first | exact F.H_pos.le | positivity |
      (constructor <;> nlinarith [F.H_pos, F.L_pos])
  · intro z hz
    apply mem_convexHull_three_of_weights 0 (F.L : ℂ) ⟨F.p, F.H⟩ z
      ((F.H * F.L - F.H * z.re - (F.L - F.p) * z.im) / (F.H * F.L))
      ((F.H * z.re - F.p * z.im) / (F.H * F.L)) (z.im / F.H)
    · exact div_nonneg (by linarith [hz.2.2]) (mul_nonneg F.H_pos.le F.L_pos.le)
    · exact div_nonneg (by linarith [hz.2.1]) (mul_nonneg F.H_pos.le F.L_pos.le)
    · exact div_nonneg hz.1 F.H_pos.le
    · field_simp
      ring
    · apply Complex.ext
      all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, Complex.zero_re, Complex.zero_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul]
      all_goals field_simp
      all_goals ring

theorem TrapezoidFan.right_carrier (F : TrapezoidFan) : F.right.carrier = F.rightRegion := by
  have hH := ne_of_gt F.H_pos
  have hq := ne_of_gt F.top_right_pos
  apply Set.Subset.antisymm
  · apply convexHull_min _ F.rightRegion_convex
    intro z hz
    change z ∈ ({(F.L : ℂ), (⟨F.L - F.H, F.H⟩ : ℂ), ⟨F.p, F.H⟩} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl
    all_goals simp only [rightRegion, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im]
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals nlinarith [F.H_pos, F.top_right_pos]
  · intro z hz
    apply mem_convexHull_three_of_weights (F.L : ℂ) ⟨F.L - F.H, F.H⟩ ⟨F.p, F.H⟩ z
      ((F.H - z.im) / F.H)
      ((F.H * z.re + (F.L - F.p) * z.im - F.H * F.L) / (F.H * (F.L - F.H - F.p)))
      ((F.L - z.re - z.im) / (F.L - F.H - F.p))
    · exact div_nonneg (by linarith [hz.2.2]) F.H_pos.le
    · exact div_nonneg (by linarith [hz.2.1])
        (mul_nonneg F.H_pos.le F.top_right_pos.le)
    · exact div_nonneg (by linarith [hz.1]) F.top_right_pos.le
    · field_simp
      ring
    · apply Complex.ext
      all_goals simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]
      all_goals field_simp
      all_goals ring

theorem TrapezoidFan.regions_cover (F : TrapezoidFan) :
    (F.leftRegion ∪ F.centerRegion) ∪ F.rightRegion = F.region := by
  ext z
  simp only [Set.mem_union, leftRegion, centerRegion, rightRegion, region, Set.mem_ofPred_eq]
  constructor
  · rintro ((h | h) | h)
    · have hy : 0 ≤ z.im := by nlinarith [h.1, h.2.1, F.H_pos, F.p_pos]
      have hx : z.re ≤ F.p := by nlinarith [h.2.1, h.2.2, F.H_pos, F.p_pos]
      exact ⟨h.1, hy, h.2.2, by linarith [F.top_right_pos]⟩
    · have hx : 0 ≤ z.re := by nlinarith [h.1, h.2.1, F.H_pos, F.p_pos]
      have hy : z.im ≤ F.H := by nlinarith [h.2.1, h.2.2, F.L_pos]
      have hsum : z.re + z.im ≤ F.L := by
        have := mul_nonneg F.top_right_pos.le h.1
        nlinarith [h.2.2, F.H_pos]
      exact ⟨hx, h.1, hy, hsum⟩
    · have hy : 0 ≤ z.im := by nlinarith [h.1, h.2.1, F.H_pos, F.top_right_pos]
      have hx : F.p ≤ z.re := by
        have := mul_le_mul_of_nonneg_left h.2.2
          (show 0 ≤ F.L - F.p by linarith [F.H_pos, F.top_right_pos])
        nlinarith [h.2.1, F.H_pos]
      exact ⟨by linarith [F.p_pos], hy, h.2.2, h.1⟩
  · rintro ⟨hx, hy, hyH, hsum⟩
    by_cases hleft : F.H * z.re ≤ F.p * z.im
    · exact Or.inl (Or.inl ⟨hx, hleft, hyH⟩)
    · by_cases hright : F.H * F.L ≤ F.H * z.re + (F.L - F.p) * z.im
      · exact Or.inr ⟨hsum, hright, hyH⟩
      · exact Or.inl (Or.inr ⟨hy, le_of_lt (lt_of_not_ge hleft),
          le_of_lt (lt_of_not_ge hright)⟩)

theorem TrapezoidFan.left_center_disjoint (F : TrapezoidFan) :
    Disjoint (interior F.leftRegion) (interior F.centerRegion) := by
  apply separated_interiors (linearForm F.H (-F.p))
    (linearForm_surjective _ _ (ne_of_gt F.H_pos)) 0
  · intro z hz
    change F.H * z.re + -F.p * z.im ≤ 0
    linarith [hz.2.1]
  · intro z hz
    change 0 ≤ F.H * z.re + -F.p * z.im
    linarith [hz.2.1]

theorem TrapezoidFan.center_right_disjoint (F : TrapezoidFan) :
    Disjoint (interior F.centerRegion) (interior F.rightRegion) := by
  exact separated_interiors (linearForm F.H (F.L - F.p))
    (linearForm_surjective _ _ (ne_of_gt F.H_pos)) (F.H * F.L)
    (fun _ h => h.2.2) (fun _ h => h.2.1)

theorem TrapezoidFan.left_right_disjoint (F : TrapezoidFan) :
    Disjoint (interior F.leftRegion) (interior F.rightRegion) := by
  apply separated_interiors Complex.reCLM (fun r => ⟨(r : ℂ), rfl⟩) F.p
  · intro z hz
    change z.re ≤ F.p
    nlinarith [hz.2.1, hz.2.2, F.H_pos, F.p_pos]
  · intro z hz
    have := mul_le_mul_of_nonneg_left hz.2.2
      (show 0 ≤ F.L - F.p by linarith [F.H_pos, F.top_right_pos])
    change F.p ≤ z.re
    nlinarith [hz.2.1, F.H_pos]

/-- Glue congruent refinements of the three pieces after arbitrary affine
transport. Only the parent decomposition is transported affinely; each
supplied refinement already consists of isometric copies of `R`. -/
noncomputable def TrapezoidFan.glueAffineTilings (F : TrapezoidFan)
    (e : ℂ ≃ᵃ[ℝ] ℂ) {R : Triangle} {nl nc nr : ℕ}
    (Tl : CongruentTiling (F.left.mapAffineEquiv e) R nl)
    (Tc : CongruentTiling (F.center.mapAffineEquiv e) R nc)
    (Tr : CongruentTiling (F.right.mapAffineEquiv e) R nr) :
    RegionTiling (e '' F.region) R ((Fin nl ⊕ Fin nc) ⊕ Fin nr) := by
  have hlc : Disjoint (interior (F.left.mapAffineEquiv e).carrier)
      (interior (F.center.mapAffineEquiv e).carrier) := by
    rw [Triangle.mapAffineEquiv_interior, Triangle.mapAffineEquiv_interior,
      F.left_carrier, F.center_carrier]
    exact Set.disjoint_image_of_injective e.injective F.left_center_disjoint
  have hlr : Disjoint (interior (F.left.mapAffineEquiv e).carrier)
      (interior (F.right.mapAffineEquiv e).carrier) := by
    rw [Triangle.mapAffineEquiv_interior, Triangle.mapAffineEquiv_interior,
      F.left_carrier, F.right_carrier]
    exact Set.disjoint_image_of_injective e.injective F.left_right_disjoint
  have hcr : Disjoint (interior (F.center.mapAffineEquiv e).carrier)
      (interior (F.right.mapAffineEquiv e).carrier) := by
    rw [Triangle.mapAffineEquiv_interior, Triangle.mapAffineEquiv_interior,
      F.center_carrier, F.right_carrier]
    exact Set.disjoint_image_of_injective e.injective F.center_right_disjoint
  apply (Tl.toRegionTiling.unionThree Tc.toRegionTiling Tr.toRegionTiling
    hlc hlr hcr).of_region_eq
  rw [Triangle.mapAffineEquiv_carrier, Triangle.mapAffineEquiv_carrier,
    Triangle.mapAffineEquiv_carrier, F.left_carrier, F.center_carrier,
    F.right_carrier, ← Set.image_union, ← Set.image_union, F.regions_cover]

end Erdos633

import ErdosProblems.Erdos633.VAssembly

/-!
# Splitting a triangle from a vertex to the opposite side

For every `0 < r < 1`, the segment from the second vertex to the point
at fraction `r` along the first-to-third side gives two nondegenerate
triangles. Coverage, disjoint interiors, and gluing of congruent tilings
are proved without an edge-to-edge assumption on the component tilings.
-/

namespace Erdos633

theorem segment_split_lineMap (a c : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    segment ℝ a c = segment ℝ a (AffineMap.lineMap a c r) ∪
      segment ℝ (AffineMap.lineMap a c r) c := by
  have h : segment ℝ (0 : ℝ) 1 = segment ℝ (0 : ℝ) r ∪ segment ℝ r 1 := by
    rw [segment_eq_Icc (by norm_num), segment_eq_Icc hr0, segment_eq_Icc hr1]
    ext x
    simp only [Set.mem_Icc, Set.mem_union]
    constructor
    · intro hx
      by_cases hxr : x ≤ r
      · exact Or.inl ⟨hx.1, hxr⟩
      · exact Or.inr ⟨le_of_lt (lt_of_not_ge hxr), hx.2⟩
    · rintro (hx | hx) <;> constructor <;> linarith [hx.1, hx.2]
  have himage := congrArg (fun S => (AffineMap.lineMap a c : ℝ →ᵃ[ℝ] ℂ) '' S) h
  simpa only [Set.image_union, image_segment, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using himage

theorem convexHull_triangle_split (a b c : ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    convexHull ℝ {a, b, c} = convexHull ℝ {a, b, AffineMap.lineMap a c r} ∪
      convexHull ℝ {AffineMap.lineMap a c r, b, c} := by
  have h := congrArg (fun S => convexJoin ℝ {b} S) (segment_split_lineMap a c r hr0 hr1)
  simp only [convexJoin_union_right, convexJoin_singleton_segment] at h
  simpa only [Set.insert_comm b a, Set.insert_comm b (AffineMap.lineMap a c r)] using h

def standardSplitFirst (r : ℝ) (hr0 : 0 < r) : Triangle where
  a := 0
  b := 1
  c := ⟨0, r⟩
  nondegenerate := by simpa using ne_of_gt hr0

def standardSplitSecond (r : ℝ) (hr1 : r < 1) : Triangle where
  a := ⟨0, r⟩
  b := 1
  c := Complex.I
  nondegenerate := by
    change orientedDoubleArea ⟨0, r⟩ 1 Complex.I ≠ 0
    simpa [orientedDoubleArea] using ne_of_gt (sub_pos.mpr hr1)

theorem standardSplit_covers (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (standardSplitFirst r hr0).carrier ∪ (standardSplitSecond r hr1).carrier =
      standardTriangle.carrier := by
  have hpoint : AffineMap.lineMap (0 : ℂ) Complex.I r = (⟨0, r⟩ : ℂ) := by
    rw [AffineMap.lineMap_apply_module]
    apply Complex.ext <;> simp
  have h := convexHull_triangle_split (0 : ℂ) 1 Complex.I r hr0.le hr1.le
  rw [hpoint] at h
  exact h.symm

theorem standardSplit_disjoint (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Disjoint (interior (standardSplitFirst r hr0).carrier)
      (interior (standardSplitSecond r hr1).carrier) := by
  let f : ℂ →L[ℝ] ℝ := r • Complex.reCLM + Complex.imCLM
  have hf : Function.Surjective f := by
    intro x
    exact ⟨⟨0, x⟩, by simp [f]⟩
  apply separated_interiors f hf r
  · apply convexHull_min _ (convex_linear_le f r)
    intro z hz
    change z ∈ ({0, 1, (⟨0, r⟩ : ℂ)} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl <;> simp [f, hr0.le]
  · apply convexHull_min _ (convex_linear_ge f r)
    intro z hz
    change z ∈ ({(⟨0, r⟩ : ℂ), 1, Complex.I} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl <;> simp [f, hr1.le]

noncomputable def Triangle.splitFirst (T : Triangle) (r : ℝ) (hr0 : 0 < r) : Triangle :=
  (standardSplitFirst r hr0).mapAffineEquiv T.coordinateEquiv

noncomputable def Triangle.splitSecond (T : Triangle) (r : ℝ) (hr1 : r < 1) : Triangle :=
  (standardSplitSecond r hr1).mapAffineEquiv T.coordinateEquiv

@[simp] theorem Triangle.splitFirst_a (T : Triangle) (r : ℝ) (hr0 : 0 < r) :
    (T.splitFirst r hr0).a = T.a := T.coordinateEquiv_zero

@[simp] theorem Triangle.splitFirst_b (T : Triangle) (r : ℝ) (hr0 : 0 < r) :
    (T.splitFirst r hr0).b = T.b := T.coordinateEquiv_one

@[simp] theorem Triangle.splitFirst_c (T : Triangle) (r : ℝ) (hr0 : 0 < r) :
    (T.splitFirst r hr0).c = T.coordinateEquiv (⟨0, r⟩ : ℂ) := rfl

@[simp] theorem Triangle.splitSecond_a (T : Triangle) (r : ℝ) (hr1 : r < 1) :
    (T.splitSecond r hr1).a = T.coordinateEquiv (⟨0, r⟩ : ℂ) := rfl

@[simp] theorem Triangle.splitSecond_b (T : Triangle) (r : ℝ) (hr1 : r < 1) :
    (T.splitSecond r hr1).b = T.b := T.coordinateEquiv_one

@[simp] theorem Triangle.splitSecond_c (T : Triangle) (r : ℝ) (hr1 : r < 1) :
    (T.splitSecond r hr1).c = T.c := T.coordinateEquiv_I

theorem Triangle.split_covers (T : Triangle) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (T.splitFirst r hr0).carrier ∪ (T.splitSecond r hr1).carrier = T.carrier := by
  simp only [Triangle.splitFirst, Triangle.splitSecond, Triangle.mapAffineEquiv_carrier]
  rw [← Set.image_union, standardSplit_covers r hr0 hr1]
  rw [← Triangle.mapAffineEquiv_carrier, Triangle.standard_map_coordinateEquiv]

theorem Triangle.split_disjoint (T : Triangle) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Disjoint (interior (T.splitFirst r hr0).carrier)
      (interior (T.splitSecond r hr1).carrier) := by
  simp only [Triangle.splitFirst, Triangle.splitSecond, Triangle.mapAffineEquiv_carrier]
  exact disjoint_interiors_affine_image T.coordinateEquiv (standardSplit_disjoint r hr0 hr1)

noncomputable def Triangle.glueSplitTilings (T : Triangle) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) {R : Triangle} {N M : ℕ}
    (T₁ : CongruentTiling (T.splitFirst r hr0) R N)
    (T₂ : CongruentTiling (T.splitSecond r hr1) R M) : CongruentTiling T R (N + M) := by
  let S := T₁.toRegionTiling.union T₂.toRegionTiling (T.split_disjoint r hr0 hr1)
  simpa only [Fintype.card_sum, Fintype.card_fin] using
    S.toCongruentTiling T (T.split_covers r hr0 hr1)

end Erdos633

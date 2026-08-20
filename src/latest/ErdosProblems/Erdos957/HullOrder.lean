/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Hull

/-!
# A finite cyclic enumeration API for the vertices of a planar convex hull

This file deliberately does not import `ErdosProblems.Erdos93`: that module
raises the heartbeat limit globally.  The first part below isolates the finite
enumeration facts that require no planar geometry.  The second part records a
minimal interface for the additional geometric properties of a cyclic order.
-/

open Set
open scoped EuclideanGeometry

namespace Erdos957

noncomputable section

/-- The number of vertices of the convex hull of `A`. -/
abbrev hullVertexCount (A : Finset Point) : ℕ := (hullVertices A).card

/-- A canonical finite enumeration of all hull vertices.  No geometric order
is asserted here; `Fintype.equivFin` supplies a bijection with the finite
subtype. -/
noncomputable def hullVertexEquiv (A : Finset Point) :
    Fin (hullVertexCount A) ≃ {x // x ∈ hullVertices A} :=
  by
    simpa [hullVertexCount] using
      (Fintype.equivFin {x // x ∈ hullVertices A}).symm

/-- The underlying embedding of the canonical enumeration into the plane. -/
noncomputable def hullVertexEmbedding (A : Finset Point) :
    Fin (hullVertexCount A) ↪ Point :=
  (hullVertexEquiv A).toEmbedding.trans (Function.Embedding.subtype _)

@[simp]
theorem hullVertexEmbedding_mem (A : Finset Point) (i : Fin (hullVertexCount A)) :
    hullVertexEmbedding A i ∈ hullVertices A :=
  (hullVertexEquiv A i).property

@[simp]
theorem hullVertexEmbedding_mem_A (A : Finset Point) (i : Fin (hullVertexCount A)) :
    hullVertexEmbedding A i ∈ A :=
  hullVertices_subset A (hullVertexEmbedding_mem A i)

/-- The enumeration has exactly the hull vertices as its range. -/
theorem range_hullVertexEmbedding (A : Finset Point) :
    Set.range (hullVertexEmbedding A) = (hullVertices A : Set Point) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact hullVertexEmbedding_mem A i
  · intro hx
    let y : {x // x ∈ hullVertices A} := ⟨x, hx⟩
    exact ⟨(hullVertexEquiv A).symm y, by
      change ((hullVertexEquiv A) ((hullVertexEquiv A).symm y) : Point) = x
      simp [y]⟩

/-- Every hull vertex occurs at a unique index. -/
theorem existsUnique_hullVertexEmbedding_eq (A : Finset Point) {x : Point} :
    x ∈ hullVertices A → ∃! i, hullVertexEmbedding A i = x := by
  intro hx
  obtain ⟨i, hi⟩ := Set.ext_iff.mp (range_hullVertexEmbedding A) x |>.mpr hx
  exact ⟨i, hi, fun j hj ↦ (hullVertexEmbedding A).injective (hj.trans hi.symm)⟩

/-! ## Strict support at one hull vertex -/

/-- Every vertex of a finite convex hull is strictly exposed among the
original finite set.  This is the separation lemma needed to start any
angular or edge-by-edge construction of a cyclic order. -/
theorem hullVertex_exists_strict_support (A : Finset Point) {x : Point}
    (hx : x ∈ hullVertices A) :
    ∃ l : Point →L[ℝ] ℝ,
      (∀ y ∈ A, l y ≤ l x) ∧
      (∀ y ∈ A, y ≠ x → l y < l x) := by
  have hxext : x ∈ (convexHull ℝ (A : Set Point)).extremePoints ℝ :=
    mem_hullVertices.mp hx
  have hxnotLarge :
      x ∉ convexHull ℝ (convexHull ℝ (A : Set Point) \ {x}) :=
    ((convex_convexHull ℝ (A : Set Point)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp
      hxext).2
  have heraseSubset : (A.erase x : Set Point) ⊆
      convexHull ℝ (A : Set Point) \ {x} := by
    intro y hy
    have hy' := Finset.mem_erase.mp hy
    exact ⟨subset_convexHull ℝ (A : Set Point) hy'.2, hy'.1⟩
  have hxnot : x ∉ convexHull ℝ (A.erase x : Set Point) := by
    intro hxerase
    exact hxnotLarge (convexHull_mono heraseSubset hxerase)
  have hclosed : IsClosed (convexHull ℝ (A.erase x : Set Point)) :=
    (Set.Finite.isCompact_convexHull ℝ (A.erase x).finite_toSet).isClosed
  obtain ⟨l, u, hlt, hulx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (A.erase x : Set Point)) hclosed hxnot
  refine ⟨l, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · simpa [hyx]
    · exact (hlt y (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hyx, hy⟩))).le.trans
        hulx.le
  · intro y hy hyx
    exact (hlt y (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hyx, hy⟩))).trans hulx

/-- Equivalently, every hull vertex is an exposed point of the finite set. -/
theorem hullVertex_mem_exposedPoints (A : Finset Point) {x : Point}
    (hx : x ∈ hullVertices A) :
    x ∈ (A : Set Point).exposedPoints ℝ := by
  obtain ⟨l, hle, hlt⟩ := hullVertex_exists_strict_support A hx
  refine ⟨hullVertices_subset A hx, l, ?_⟩
  intro y hy
  refine ⟨hle y hy, fun hxy ↦ ?_⟩
  by_contra hyx
  exact (not_lt_of_ge hxy) (hlt y hy hyx)

/-- A finite convex hull is already the convex hull of its vertices. -/
theorem convexHull_hullVertices (A : Finset Point) :
    convexHull ℝ (hullVertices A : Set Point) = convexHull ℝ (A : Set Point) := by
  have hext :
      (convexHull ℝ (A : Set Point)).extremePoints ℝ =
        (hullVertices A : Set Point) := by
    ext x
    exact mem_hullVertices.symm
  have hcompact : IsCompact (convexHull ℝ (A : Set Point)) :=
    Set.Finite.isCompact_convexHull ℝ A.finite_toSet
  have hclosedVertices : IsClosed (convexHull ℝ (hullVertices A : Set Point)) :=
    Set.Finite.isCompact_convexHull ℝ (hullVertices A).finite_toSet |>.isClosed
  calc
    convexHull ℝ (hullVertices A : Set Point) =
        closure (convexHull ℝ (hullVertices A : Set Point)) :=
      hclosedVertices.closure_eq.symm
    _ = closure (convexHull ℝ
        ((convexHull ℝ (A : Set Point)).extremePoints ℝ)) := by rw [hext]
    _ = convexHull ℝ (A : Set Point) :=
      closure_convexHull_extremePoints hcompact (convex_convexHull ℝ (A : Set Point))

/-! ## Convex independence and an interior center -/

/-- The finite set of hull vertices is convex independent. -/
theorem hullVertices_convexIndependent (A : Finset Point) :
    ConvexIndependent ℝ (Subtype.val : hullVertices A → Point) := by
  apply (convex_convexHull ℝ (A : Set Point)).convexIndependent_extremePoints.mono
  intro x hx
  exact mem_hullVertices.mp hx

/-- No three distinct members of a convex-independent family are collinear. -/
theorem convexIndependent_not_collinear_three
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ι → E} (hc : ConvexIndependent ℝ p)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ {p i, p j, p k} := by
  intro hcol
  rcases Collinear.wbtw_or_wbtw_or_wbtw hcol with h | h | h
  · have hjmem : p j ∈ convexHull ℝ {p i, p k} := by
      rw [convexHull_pair]
      exact h.mem_segment
    have hjidx := hc.mem_convexHull_iff ({i, k} : Set ι) j
    have : p j ∈ convexHull ℝ (p '' ({i, k} : Set ι)) := by
      simpa [Set.image_insert_eq, Set.image_singleton] using hjmem
    have := hjidx.mp this
    simp [hij, hjk] at this
    exact hij this.symm
  · have hkmem : p k ∈ convexHull ℝ {p j, p i} := by
      rw [convexHull_pair]
      exact h.mem_segment
    have hkidx := hc.mem_convexHull_iff ({j, i} : Set ι) k
    have : p k ∈ convexHull ℝ (p '' ({j, i} : Set ι)) := by
      simpa [Set.image_insert_eq, Set.image_singleton] using hkmem
    have := hkidx.mp this
    simp [hjk, hik] at this
    rcases this with hki | hki
    · exact hjk hki.symm
    · exact hik hki.symm
  · have himem : p i ∈ convexHull ℝ {p k, p j} := by
      rw [convexHull_pair]
      exact h.mem_segment
    have hiidx := hc.mem_convexHull_iff ({k, j} : Set ι) i
    have : p i ∈ convexHull ℝ (p '' ({k, j} : Set ι)) := by
      simpa [Set.image_insert_eq, Set.image_singleton] using himem
    have := hiidx.mp this
    simp [hij, hik] at this

/-- Three or more hull vertices force the full convex hull to have a nonempty
interior.  This supplies a center from which an angular order can be formed. -/
theorem convexHull_interior_nonempty_of_three_le_hullVertices
    (A : Finset Point) (hthree : 3 ≤ (hullVertices A).card) :
    (interior (convexHull ℝ (A : Set Point))).Nonempty := by
  obtain ⟨t, htA, htcard⟩ : ∃ t : Finset Point,
      t ⊆ hullVertices A ∧ t.card = 3 :=
    Finset.le_card_iff_exists_subset_card.mp hthree
  have htconv : ConvexIndependent ℝ (Subtype.val : t → Point) :=
    (hullVertices_convexIndependent A).mono htA
  let e : Fin 3 ≃ t := Fintype.equivOfCardEq (by simp [htcard])
  have hnotcol : ¬ Collinear ℝ
      {((e 0 : t) : Point), ((e 1 : t) : Point), ((e 2 : t) : Point)} := by
    apply convexIndependent_not_collinear_three htconv
    · exact fun h ↦ by simpa using e.injective h
    · exact fun h ↦ by simpa using e.injective h
    · exact fun h ↦ by simpa using e.injective h
  have heaff : AffineIndependent ℝ
      (fun i : Fin 3 ↦ ((e i : t) : Point)) := by
    rw [affineIndependent_iff_not_collinear]
    have hrange3 : Set.range (fun i : Fin 3 ↦ ((e i : t) : Point)) =
        {((e 0 : t) : Point), ((e 1 : t) : Point), ((e 2 : t) : Point)} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx
        · exact ⟨0, hx.symm⟩
        · exact ⟨1, hx.symm⟩
        · exact ⟨2, hx.symm⟩
    rw [hrange3]
    exact hnotcol
  have htaff : AffineIndependent ℝ (Subtype.val : t → Point) := by
    exact (affineIndependent_equiv e).mp heaff
  have hspanRange :
      affineSpan ℝ (Set.range (Subtype.val : t → Point)) = ⊤ := by
    apply htaff.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp [htcard, Point]
  have hrange : Set.range (Subtype.val : t → Point) = (t : Set Point) := by
    ext x
    simp
  have hspan : affineSpan ℝ (t : Set Point) = ⊤ := by
    simpa [hrange] using hspanRange
  have hintert : (interior (convexHull ℝ (t : Set Point))).Nonempty := by
    rw [(convex_convexHull ℝ (t : Set Point)).interior_nonempty_iff_affineSpan_eq_top,
      affineSpan_convexHull]
    exact hspan
  apply hintert.mono
  apply interior_mono
  apply convexHull_mono
  exact Finset.coe_subset.mpr (htA.trans (hullVertices_subset A))

/-! ## Angular coordinates and ray uniqueness -/

/-- The standard real-linear identification of the Euclidean plane with
`ℂ`. -/
noncomputable def pointComplexEquiv : Point ≃ₗ[ℝ] ℂ :=
  { toFun := fun x ↦ ⟨x 0, x 1⟩
    invFun := fun z ↦
      z.re • EuclideanSpace.single 0 1 + z.im • EuclideanSpace.single 1 1
    left_inv := by
      intro x
      ext i
      fin_cases i <;> simp
    right_inv := by
      intro z
      apply Complex.ext <;> simp
    map_add' := by
      intro x y
      apply Complex.ext <;> simp
    map_smul' := by
      intro r x
      apply Complex.ext <;> simp }

@[simp]
theorem pointComplexEquiv_re (x : Point) : (pointComplexEquiv x).re = x 0 := rfl

@[simp]
theorem pointComplexEquiv_im (x : Point) : (pointComplexEquiv x).im = x 1 := rfl

/-- Polar argument of `x` around `C`. -/
noncomputable def centerAngle (C x : Point) : ℝ :=
  Complex.arg (pointComplexEquiv (x - C))

/-- The standard determinant on `ℂ`, viewed as the oriented real plane. -/
def complexCross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem complexCross_pointComplexEquiv (u v : Point) :
    complexCross (pointComplexEquiv u) (pointComplexEquiv v) =
      u 0 * v 1 - u 1 * v 0 := by
  rfl

theorem complexCross_eq_norm_mul_sin_sub (z w : ℂ) :
    complexCross z w = ‖z‖ * ‖w‖ * Real.sin (Complex.arg w - Complex.arg z) := by
  simp only [complexCross]
  rw [Real.sin_sub, mul_sub]
  rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
    ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  ring

theorem real_lt_pi_of_pos_of_lt_two_pi_of_sin_pos {t : ℝ}
    (ht0 : 0 < t) (ht2pi : t < 2 * Real.pi) (hsin : 0 < Real.sin t) :
    t < Real.pi := by
  by_contra htpi
  have hy0 : 0 ≤ t - Real.pi := by linarith
  have hypi : t - Real.pi ≤ Real.pi := by linarith
  have hnonneg : 0 ≤ Real.sin (t - Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hy0 hypi
  have hrewrite : Real.sin t = -Real.sin (t - Real.pi) := by
    calc
      Real.sin t = Real.sin ((t - Real.pi) + Real.pi) := by congr 1 <;> ring
      _ = -Real.sin (t - Real.pi) := Real.sin_add_pi _
  rw [hrewrite] at hsin
  linarith

/-- Counterclockwise angular displacement, normalized to the interval
`(0,2π]` according to principal arguments. -/
noncomputable def ccwAngleDiff (z w : ℂ) : ℝ :=
  if Complex.arg z < Complex.arg w then Complex.arg w - Complex.arg z
  else 2 * Real.pi + Complex.arg w - Complex.arg z

theorem sin_ccwAngleDiff (z w : ℂ) :
    Real.sin (ccwAngleDiff z w) = Real.sin (Complex.arg w - Complex.arg z) := by
  simp only [ccwAngleDiff]
  split_ifs
  · rfl
  · rw [show 2 * Real.pi + Complex.arg w - Complex.arg z =
        (Complex.arg w - Complex.arg z) + 2 * Real.pi by ring,
      Real.sin_add_two_pi]

theorem ccwAngleDiff_mem_Ioo_of_complexCross_pos {z w : ℂ}
    (hcross : 0 < complexCross z w) :
    ccwAngleDiff z w ∈ Set.Ioo 0 Real.pi := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp [complexCross] at hcross
  have hw : w ≠ 0 := by
    intro hw
    subst w
    simp [complexCross] at hcross
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  have hsinSub : 0 < Real.sin (Complex.arg w - Complex.arg z) := by
    rw [complexCross_eq_norm_mul_sin_sub] at hcross
    rcases mul_pos_iff.mp hcross with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge hnorm.le) hneg.1)
  have hargne : Complex.arg z ≠ Complex.arg w := by
    intro harg
    rw [harg, sub_self, Real.sin_zero] at hsinSub
    exact (lt_irrefl 0) hsinSub
  by_cases hzw : Complex.arg z < Complex.arg w
  · rw [ccwAngleDiff, if_pos hzw]
    refine ⟨sub_pos.mpr hzw, ?_⟩
    apply real_lt_pi_of_pos_of_lt_two_pi_of_sin_pos (sub_pos.mpr hzw) ?_ hsinSub
    linarith [Complex.neg_pi_lt_arg z, Complex.arg_le_pi w]
  · have hwz : Complex.arg w < Complex.arg z :=
      lt_of_le_of_ne (not_lt.mp hzw) hargne.symm
    rw [ccwAngleDiff, if_neg hzw]
    have hpos : 0 < 2 * Real.pi + Complex.arg w - Complex.arg z := by
      linarith [Complex.neg_pi_lt_arg w, Complex.arg_le_pi z]
    refine ⟨hpos, ?_⟩
    apply real_lt_pi_of_pos_of_lt_two_pi_of_sin_pos hpos
    · linarith
    · rwa [show 2 * Real.pi + Complex.arg w - Complex.arg z =
          (Complex.arg w - Complex.arg z) + 2 * Real.pi by ring,
        Real.sin_add_two_pi]

theorem complexCross_pos_of_ccwAngleDiff_mem_Ioo {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hdiff : ccwAngleDiff z w ∈ Set.Ioo 0 Real.pi) :
    0 < complexCross z w := by
  rw [complexCross_eq_norm_mul_sin_sub, ← sin_ccwAngleDiff]
  exact mul_pos (mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw))
    (Real.sin_pos_of_pos_of_lt_pi hdiff.1 hdiff.2)

/-- The open counterclockwise sector from `z` to `w`, expressed using
principal arguments. -/
def InOpenCCWSector (z w x : ℂ) : Prop :=
  if Complex.arg z < Complex.arg w then
    Complex.arg z < Complex.arg x ∧ Complex.arg x < Complex.arg w
  else
    Complex.arg z < Complex.arg x ∨ Complex.arg x < Complex.arg w

theorem complexCross_pos_of_mem_openCCWSector {z w x : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) (hx : x ≠ 0)
    (hzw : ccwAngleDiff z w ∈ Set.Ioo 0 Real.pi)
    (hxsector : InOpenCCWSector z w x) :
    0 < complexCross z x ∧ 0 < complexCross x w := by
  by_cases hord : Complex.arg z < Complex.arg w
  · rw [InOpenCCWSector, if_pos hord] at hxsector
    rw [ccwAngleDiff, if_pos hord] at hzw
    rw [Set.mem_Ioo] at hzw
    have hzx : ccwAngleDiff z x = Complex.arg x - Complex.arg z := by
      rw [ccwAngleDiff, if_pos hxsector.1]
    have hxw : ccwAngleDiff x w = Complex.arg w - Complex.arg x := by
      rw [ccwAngleDiff, if_pos hxsector.2]
    constructor
    · apply complexCross_pos_of_ccwAngleDiff_mem_Ioo hz hx
      rw [hzx]
      constructor <;> linarith
    · apply complexCross_pos_of_ccwAngleDiff_mem_Ioo hx hw
      rw [hxw]
      constructor <;> linarith
  · rw [InOpenCCWSector, if_neg hord] at hxsector
    rw [ccwAngleDiff, if_neg hord] at hzw
    rw [Set.mem_Ioo] at hzw
    rcases hxsector with hzx | hxw
    · have hzxDiff : ccwAngleDiff z x = Complex.arg x - Complex.arg z := by
        rw [ccwAngleDiff, if_pos hzx]
      have hxwOrder : ¬ Complex.arg x < Complex.arg w := by
        linarith [Complex.neg_pi_lt_arg w, Complex.arg_le_pi x]
      have hxwDiff : ccwAngleDiff x w =
          2 * Real.pi + Complex.arg w - Complex.arg x := by
        rw [ccwAngleDiff, if_neg hxwOrder]
      constructor
      · apply complexCross_pos_of_ccwAngleDiff_mem_Ioo hz hx
        rw [hzxDiff]
        constructor
        · linarith
        · linarith [Complex.neg_pi_lt_arg w, Complex.arg_le_pi x,
            Real.pi_pos]
      · apply complexCross_pos_of_ccwAngleDiff_mem_Ioo hx hw
        rw [hxwDiff]
        constructor
        · linarith [Complex.neg_pi_lt_arg w, Complex.arg_le_pi x,
            Real.pi_pos]
        · linarith
    · have hzxOrder : ¬ Complex.arg z < Complex.arg x := by
        linarith [Complex.neg_pi_lt_arg x, Complex.arg_le_pi z]
      have hzxDiff : ccwAngleDiff z x =
          2 * Real.pi + Complex.arg x - Complex.arg z := by
        rw [ccwAngleDiff, if_neg hzxOrder]
      have hxwDiff : ccwAngleDiff x w = Complex.arg w - Complex.arg x := by
        rw [ccwAngleDiff, if_pos hxw]
      constructor
      · apply complexCross_pos_of_ccwAngleDiff_mem_Ioo hz hx
        rw [hzxDiff]
        constructor
        · linarith [Complex.neg_pi_lt_arg x, Complex.arg_le_pi z,
            Real.pi_pos]
        · linarith
      · apply complexCross_pos_of_ccwAngleDiff_mem_Ioo hx hw
        rw [hxwDiff]
        constructor
        · linarith
        · linarith [Complex.neg_pi_lt_arg x, Complex.arg_le_pi z,
            Real.pi_pos]

/-- A ray from an interior point of a closed convex set meets its frontier at
most once. -/
theorem sameRay_frontier_eq {K : Set Point} (hconv : Convex ℝ K)
    (hclosed : IsClosed K) {C u v : Point} (hC : C ∈ interior K)
    (hu : u ∈ frontier K) (hv : v ∈ frontier K)
    (hray : SameRay ℝ (u - C) (v - C)) : u = v := by
  have hinside : ∀ (w : Point), w ∈ frontier K → ∀ t : ℝ,
      0 < t → t < 1 → C + t • (w - C) ∈ interior K := by
    intro w hw t ht0 ht1
    have hwcl : w ∈ closure K := frontier_subset_closure hw
    have hopen := hconv.openSegment_interior_closure_subset_interior hC hwcl
    apply hopen
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    module
  have hnotfront : ∀ (w : Point), w ∈ frontier K → ∀ t : ℝ,
      0 < t → t < 1 → C + t • (w - C) ∉ frontier K := by
    intro w hw t ht0 ht1 hfront
    exact hfront.2 (hinside w hw t ht0 ht1)
  rcases hray with hzero | hzero | ⟨a, b, ha, hb, hab⟩
  · have huC : u = C := sub_eq_zero.mp hzero
    subst u
    exact False.elim (hu.2 hC)
  · have hvC : v = C := sub_eq_zero.mp hzero
    subst v
    exact False.elim (hv.2 hC)
  · have hscaled : (a / b) • (u - C) = v - C := by
      calc
        (a / b) • (u - C) = b⁻¹ • (a • (u - C)) := by
          rw [div_eq_inv_mul, smul_smul]
        _ = b⁻¹ • (b • (v - C)) := by rw [hab]
        _ = v - C := by rw [inv_smul_smul₀ hb.ne']
    by_cases habLe : a / b ≤ 1
    · by_cases habLt : a / b < 1
      · have hbad := hnotfront u hu (a / b) (div_pos ha hb) habLt
        apply False.elim
        apply hbad
        have : C + (a / b) • (u - C) = v := by
          rw [hscaled]
          abel
        simpa [this] using hv
      · have hone : a / b = 1 := le_antisymm habLe (not_lt.mp habLt)
        have : u - C = v - C := by simpa [hone] using hscaled
        have hadd := congrArg (fun z : Point ↦ z + C) this
        simpa using hadd
    · have hback : (1 / (a / b)) • (v - C) = u - C := by
        rw [← hscaled, one_div, inv_smul_smul₀]
        exact ne_of_gt (div_pos ha hb)
      have hratio : 0 < 1 / (a / b) := by positivity
      have hratioLt : 1 / (a / b) < 1 := by
        rw [div_lt_one (div_pos ha hb)]
        exact lt_of_not_ge habLe
      have hbad := hnotfront v hv (1 / (a / b)) hratio hratioLt
      apply False.elim
      apply hbad
      have : C + (1 / (a / b)) • (v - C) = u := by
        rw [hback]
        abel
      rw [this]
      exact hu

/-- Every hull vertex lies on the frontier of the finite convex hull. -/
theorem hullVertex_mem_frontier (A : Finset Point) {x : Point}
    (hx : x ∈ hullVertices A) :
    x ∈ frontier (convexHull ℝ (A : Set Point)) := by
  have hxext := mem_hullVertices.mp hx
  refine ⟨subset_closure (extremePoints_subset hxext), ?_⟩
  intro hxint
  exact Set.disjoint_left.mp
    (disjoint_interior_extremePoints (convexHull ℝ (A : Set Point))) hxint hxext

/-- Angular coordinates around an interior center are injective on the hull
vertices. -/
theorem centerAngle_injOn_hullVertices (A : Finset Point) {C : Point}
    (hC : C ∈ interior (convexHull ℝ (A : Set Point))) :
    Set.InjOn (centerAngle C) (hullVertices A : Set Point) := by
  intro u hu v hv huv
  have hcomplex : SameRay ℝ (pointComplexEquiv (u - C))
      (pointComplexEquiv (v - C)) :=
    Complex.sameRay_of_arg_eq huv
  have hray : SameRay ℝ (u - C) (v - C) :=
    (SameRay.sameRay_map_iff pointComplexEquiv).mp hcomplex
  apply sameRay_frontier_eq (convex_convexHull ℝ (A : Set Point))
    (Set.Finite.isCompact_convexHull ℝ A.finite_toSet).isClosed hC
  · exact hullVertex_mem_frontier A hu
  · exact hullVertex_mem_frontier A hv
  · exact hray

/-- Sorting by `centerAngle` gives an exact finite enumeration whose angles
are strictly increasing on ordinary `Fin` indices. -/
theorem exists_angleSorted_hullVertexEmbedding (A : Finset Point) {C : Point}
    (hC : C ∈ interior (convexHull ℝ (A : Set Point))) :
    ∃ v : Fin (hullVertexCount A) ↪ Point,
      Set.range v = (hullVertices A : Set Point) ∧
      ∀ i j, i < j → centerAngle C (v i) < centerAngle C (v j) := by
  let H := {x // x ∈ hullVertices A}
  have hangleInj : Function.Injective (fun x : H ↦ centerAngle C x) := by
    intro x y hxy
    apply Subtype.ext
    exact centerAngle_injOn_hullVertices A hC x.property y.property hxy
  letI : LinearOrder H := LinearOrder.lift' (fun x : H ↦ centerAngle C x) hangleInj
  let e : Fin (hullVertexCount A) ≃o H :=
    Fintype.orderIsoFinOfCardEq H (by simp [H, hullVertexCount])
  let v : Fin (hullVertexCount A) ↪ Point :=
    e.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨v, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      let y : H := ⟨x, hx⟩
      exact ⟨e.symm y, by
        change ((e (e.symm y) : H) : Point) = x
        simp [y]⟩
  · intro i j hij
    change centerAngle C (e i) < centerAngle C (e j)
    exact e.strictMono hij

/-! ## The geometric interface required of a cyclic order -/

/-- Signed twice-area of the oriented triangle `p q r`, in the standard
coordinates on `ℝ²`.  Positivity means a strict counterclockwise turn. -/
def orientedTurn (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - q 1) - (q 1 - p 1) * (r 0 - q 0)

/-- The determinant of two vectors in the standard orientation of the
plane. -/
def crossVec (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The determinant against a fixed first vector, as a continuous linear
functional of the second vector. -/
noncomputable def crossFunctional (u : Point) : Point →L[ℝ] ℝ :=
  (-u 1) • EuclideanSpace.proj 0 + (u 0) • EuclideanSpace.proj 1

@[simp]
theorem crossFunctional_apply (u v : Point) :
    crossFunctional u v = crossVec u v := by
  simp [crossFunctional, crossVec]
  ring

theorem crossFunctional_ne_zero {u : Point} (hu : u ≠ 0) :
    crossFunctional u ≠ 0 := by
  intro hzero
  have h0 := congrArg (fun f : Point →L[ℝ] ℝ ↦ f (EuclideanSpace.single 1 1)) hzero
  have h1 := congrArg (fun f : Point →L[ℝ] ℝ ↦ f (EuclideanSpace.single 0 1)) hzero
  simp [crossFunctional, crossVec] at h0 h1
  apply hu
  ext i
  fin_cases i <;> simp [h0, h1]

theorem orientedTurn_eq_crossVec (p q r : Point) :
    orientedTurn p q r = crossVec (q - p) (r - p) := by
  simp [orientedTurn, crossVec]
  ring

/-- The two standard coordinate vectors of the Euclidean plane. -/
noncomputable def planeBasisVector (i : Fin 2) : Point :=
  EuclideanSpace.single i 1

@[simp]
theorem planeBasisVector_apply (i j : Fin 2) :
    planeBasisVector i j = if i = j then 1 else 0 := by
  simp [planeBasisVector, eq_comm]

theorem point_eq_coordinate_sum (x : Point) :
    x = x 0 • planeBasisVector 0 + x 1 • planeBasisVector 1 := by
  ext i
  fin_cases i <;> simp

theorem continuousLinearMap_apply_eq_coordinates (l : Point →L[ℝ] ℝ) (x : Point) :
    l x = l (planeBasisVector 0) * x 0 + l (planeBasisVector 1) * x 1 := by
  rw [point_eq_coordinate_sum x, map_add, map_smul, map_smul]
  simp [mul_comm]

/-- Rotate the coefficient vector of a linear functional counterclockwise by
one quarter turn.  Together with `l`, this is an oriented coordinate system
whenever `l ≠ 0`. -/
noncomputable def quarterTurnFunctional (l : Point →L[ℝ] ℝ) : Point →L[ℝ] ℝ :=
  (-l (planeBasisVector 1)) • EuclideanSpace.proj 0 +
    (l (planeBasisVector 0)) • EuclideanSpace.proj 1

@[simp]
theorem quarterTurnFunctional_apply (l : Point →L[ℝ] ℝ) (x : Point) :
    quarterTurnFunctional l x =
      -l (planeBasisVector 1) * x 0 + l (planeBasisVector 0) * x 1 := by
  simp [quarterTurnFunctional]

theorem support_turn_coordinate_det (l : Point →L[ℝ] ℝ) (u v : Point) :
    l u * quarterTurnFunctional l v - quarterTurnFunctional l u * l v =
      (l (planeBasisVector 0) ^ 2 + l (planeBasisVector 1) ^ 2) * crossVec u v := by
  rw [continuousLinearMap_apply_eq_coordinates l u,
    continuousLinearMap_apply_eq_coordinates l v]
  simp only [quarterTurnFunctional_apply, crossVec]
  ring

theorem support_coefficient_sq_pos {l : Point →L[ℝ] ℝ} (hl : l ≠ 0) :
    0 < l (planeBasisVector 0) ^ 2 + l (planeBasisVector 1) ^ 2 := by
  have hcoeff : l (planeBasisVector 0) ≠ 0 ∨ l (planeBasisVector 1) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hl
    ext x
    rw [continuousLinearMap_apply_eq_coordinates]
    simp [h.1, h.2]
  rcases hcoeff with hcoeff | hcoeff
  · nlinarith [sq_pos_of_ne_zero hcoeff]
  · nlinarith [sq_pos_of_ne_zero hcoeff]

theorem quarterTurn_add_smul_ne_zero {l : Point →L[ℝ] ℝ} (hl : l ≠ 0) (r : ℝ) :
    quarterTurnFunctional l + r • l ≠ 0 := by
  intro hzero
  have h0 := congrArg (fun f : Point →L[ℝ] ℝ ↦ f (planeBasisVector 0)) hzero
  have h1 := congrArg (fun f : Point →L[ℝ] ℝ ↦ f (planeBasisVector 1)) hzero
  have hsq := support_coefficient_sq_pos hl
  simp [quarterTurnFunctional_apply, planeBasisVector_apply] at h0 h1
  have h0' := congrArg (fun t : ℝ ↦ t * l (planeBasisVector 1)) h0
  have h1' := congrArg (fun t : ℝ ↦ t * l (planeBasisVector 0)) h1
  nlinarith

/-- In the standard plane, a vanishing two-by-two determinant says that
three points are collinear. -/
theorem collinear_of_crossVec_sub_eq_zero {p q x : Point} (hpq : p ≠ q)
    (hcross : crossVec (q - p) (x - p) = 0) :
    Collinear ℝ {p, q, x} := by
  have hu : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hcoord : (q - p) 0 ≠ 0 ∨ (q - p) 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    ext i
    fin_cases i <;> simp [h.1, h.2]
  have hxline : x ∈ line[ℝ, p, q] := by
    rw [← vsub_vadd x p, vadd_left_mem_affineSpan_pair]
    rcases hcoord with hcoord | hcoord
    · refine ⟨(x - p) 0 / (q - p) 0, ?_⟩
      ext i
      fin_cases i
      · simp only [smul_eq_mul, PiLp.smul_apply, PiLp.sub_apply]
        exact div_mul_cancel₀ _ hcoord
      · simp only [smul_eq_mul, PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply]
        have hc := hcross
        simp only [crossVec] at hc
        rw [div_mul_eq_mul_div]
        apply (div_eq_iff hcoord).2
        change (x 0 - p 0) * (q 1 - p 1) = (x 1 - p 1) * (q 0 - p 0)
        change (q 0 - p 0) * (x 1 - p 1) -
          (q 1 - p 1) * (x 0 - p 0) = 0 at hc
        nlinarith
    · refine ⟨(x - p) 1 / (q - p) 1, ?_⟩
      ext i
      fin_cases i
      · simp only [smul_eq_mul, PiLp.add_apply, PiLp.smul_apply,
          PiLp.sub_apply]
        have hc := hcross
        simp only [crossVec] at hc
        rw [div_mul_eq_mul_div]
        apply (div_eq_iff hcoord).2
        change (x 1 - p 1) * (q 0 - p 0) = (x 0 - p 0) * (q 1 - p 1)
        change (q 0 - p 0) * (x 1 - p 1) -
          (q 1 - p 1) * (x 0 - p 0) = 0 at hc
        nlinarith
      · simp only [smul_eq_mul, PiLp.smul_apply, PiLp.sub_apply]
        exact div_mul_cancel₀ _ hcoord
  apply (collinear_insert_of_mem_affineSpan_pair hxline).subset
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  tauto

theorem hullVertices_not_collinear_three (A : Finset Point) {p q x : Point}
    (hp : p ∈ hullVertices A) (hq : q ∈ hullVertices A)
    (hx : x ∈ hullVertices A) (hpq : p ≠ q) (hqx : q ≠ x) (hpx : p ≠ x) :
    ¬ Collinear ℝ {p, q, x} := by
  let ip : hullVertices A := ⟨p, hp⟩
  let iq : hullVertices A := ⟨q, hq⟩
  let ix : hullVertices A := ⟨x, hx⟩
  have hipq : ip ≠ iq := fun h ↦ hpq (congrArg Subtype.val h)
  have hiqx : iq ≠ ix := fun h ↦ hqx (congrArg Subtype.val h)
  have hipx : ip ≠ ix := fun h ↦ hpx (congrArg Subtype.val h)
  simpa [ip, iq, ix] using
    convexIndependent_not_collinear_three (hullVertices_convexIndependent A)
      hipq hiqx hipx

/-- `p q` is an exposed edge of `convexHull A`, with no third hull vertex on
its supporting line.  The last conjunct is the strictness needed to rule out
collinear consecutive triples. -/
def IsStrictSupportingEdge (A : Finset Point) (p q : Point) : Prop :=
  p ≠ q ∧
    ∃ l : Point →L[ℝ] ℝ, l ≠ 0 ∧ l p = l q ∧
      (∀ x ∈ A, l x ≤ l p) ∧
      (∀ x ∈ hullVertices A, x ≠ p → x ≠ q → l x < l p)

/-- Gift-wrapping at a hull vertex: there is a counterclockwise outgoing
supporting edge, and every other hull vertex lies strictly to its left.

The construction starts from a functional strictly exposing `p`.  In the
oriented coordinates consisting of that functional and its quarter-turn,
the next vertex maximizes a finite slope.  This is the algebraic core of the
planar hull-order construction and does not require an angular sorting
theorem. -/
theorem hullVertex_exists_ccw_strictSupportingEdge
    (A : Finset Point) (hthree : 3 ≤ (hullVertices A).card) {p : Point}
    (hp : p ∈ hullVertices A) :
    ∃ q : Point, q ∈ hullVertices A ∧ IsStrictSupportingEdge A p q ∧
      ∀ x ∈ hullVertices A, x ≠ p → x ≠ q → 0 < orientedTurn p q x := by
  obtain ⟨l, hle, hlt⟩ := hullVertex_exists_strict_support A hp
  have hl : l ≠ 0 := by
    intro hlzero
    have hnontrivial : (hullVertices A).Nontrivial :=
      Finset.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨q, hq, hpq⟩ := hnontrivial.exists_ne p
    have := hlt q (hullVertices_subset A hq) hpq
    rw [hlzero] at this
    simp at this
  let m : Point →L[ℝ] ℝ := quarterTurnFunctional l
  let d : Point → ℝ := fun x ↦ l p - l x
  let slope : Point → ℝ := fun x ↦ m (x - p) / d x
  have hnontrivial : (hullVertices A).Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have herase : ((hullVertices A).erase p).Nonempty :=
    hnontrivial.erase_nonempty
  obtain ⟨q, hqErase, hqmax⟩ :=
    Finset.exists_max_image ((hullVertices A).erase p) slope herase
  have hqp : q ≠ p := (Finset.mem_erase.mp hqErase).1
  have hpq : p ≠ q := hqp.symm
  have hq : q ∈ hullVertices A := (Finset.mem_erase.mp hqErase).2
  have hdpos : ∀ {x : Point}, x ∈ hullVertices A → x ≠ p → 0 < d x := by
    intro x hx hxp
    exact sub_pos.mpr (hlt x (hullVertices_subset A hx) hxp)
  have hdq : 0 < d q := hdpos hq hqp
  let r : ℝ := slope q
  let L : Point →L[ℝ] ℝ := m + r • l
  have hLne : L ≠ 0 := by
    exact quarterTurn_add_smul_ne_zero hl r
  have hmq : m (q - p) = r * d q := by
    dsimp only [r, slope]
    exact (div_eq_iff hdq.ne').mp rfl
  have hLqp : L (q - p) = 0 := by
    rw [map_sub] at hmq
    simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, map_sub]
    dsimp only [d] at hmq ⊢
    linarith
  have hLpq : L p = L q := by
    have := hLqp
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hslope_le : ∀ {x : Point}, x ∈ hullVertices A → x ≠ p →
      slope x ≤ slope q := by
    intro x hx hxp
    exact hqmax x (Finset.mem_erase.mpr ⟨hxp, hx⟩)
  have hL_hull_le : ∀ x ∈ hullVertices A, L x ≤ L p := by
    intro x hx
    by_cases hxp : x = p
    · simp [hxp]
    · have hdx : 0 < d x := hdpos hx hxp
      have hs : m (x - p) / d x ≤ r := by
        simpa only [slope, r] using hslope_le hx hxp
      have hmle : m (x - p) ≤ r * d x :=
        (div_le_iff₀ hdx).mp hs
      have hsub : L (x - p) ≤ 0 := by
        rw [map_sub] at hmle
        simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, map_sub]
        dsimp only [d] at hmle ⊢
        linarith
      rw [map_sub] at hsub
      linarith
  have hL_A_le : ∀ x ∈ A, L x ≤ L p := by
    have hhalfConvex : Convex ℝ {x : Point | L x ≤ L p} :=
      (convex_Iic (L p)).linear_preimage L.toLinearMap
    have hhull : convexHull ℝ (hullVertices A : Set Point) ⊆
        {x : Point | L x ≤ L p} :=
      convexHull_min hL_hull_le hhalfConvex
    intro x hx
    apply hhull
    rw [convexHull_hullVertices A]
    exact subset_convexHull ℝ (A : Set Point) hx
  have hslope_lt : ∀ {x : Point}, x ∈ hullVertices A → x ≠ p → x ≠ q →
      slope x < slope q := by
    intro x hx hxp hxq
    have hdx : 0 < d x := hdpos hx hxp
    have hsle := hslope_le hx hxp
    apply lt_of_le_of_ne hsle
    intro heq
    have hdetzero :
        l (q - p) * m (x - p) - m (q - p) * l (x - p) = 0 := by
      have hratio : m (x - p) / d x = m (q - p) / d q := by
        simpa only [slope] using heq
      have hmul := (div_eq_div_iff hdx.ne' hdq.ne').mp hratio
      dsimp only [d] at hmul ⊢
      simp only [map_sub] at hmul ⊢
      nlinarith
    have hcrosszero : crossVec (q - p) (x - p) = 0 := by
      rw [support_turn_coordinate_det] at hdetzero
      exact (mul_eq_zero.mp hdetzero).resolve_left
        (ne_of_gt (support_coefficient_sq_pos hl))
    exact (hullVertices_not_collinear_three A hp hq hx hpq hxq.symm hxp.symm)
      (collinear_of_crossVec_sub_eq_zero hpq hcrosszero)
  have hL_hull_lt : ∀ x ∈ hullVertices A, x ≠ p → x ≠ q → L x < L p := by
    intro x hx hxp hxq
    have hdx : 0 < d x := hdpos hx hxp
    have hs : slope x < slope q := hslope_lt hx hxp hxq
    have hm : m (x - p) < r * d x := by
      apply (div_lt_iff₀ hdx).mp
      simpa only [slope, r] using hs
    have hsub : L (x - p) < 0 := by
      rw [map_sub] at hm
      simp only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, map_sub]
      dsimp only [d] at hm ⊢
      linarith
    rw [map_sub] at hsub
    linarith
  refine ⟨q, hq, ⟨hpq, L, hLne, hLpq, hL_A_le, hL_hull_lt⟩, ?_⟩
  intro x hx hxp hxq
  have hdx : 0 < d x := hdpos hx hxp
  have hs : slope x < slope q := hslope_lt hx hxp hxq
  have hm : m (x - p) < r * d x := by
    apply (div_lt_iff₀ hdx).mp
    simpa only [slope, r] using hs
  have hdetpos :
      0 < l (q - p) * m (x - p) - m (q - p) * l (x - p) := by
    dsimp only [d] at hm hmq ⊢
    simp only [map_sub] at hm hmq ⊢
    nlinarith [hdq]
  rw [support_turn_coordinate_det] at hdetpos
  have hcross : 0 < crossVec (q - p) (x - p) := by
    rcases mul_pos_iff.mp hdetpos with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge
        (support_coefficient_sq_pos hl).le) hneg.1)
  rwa [orientedTurn_eq_crossVec]

theorem orientedTurn_swap_last (p q r : Point) :
    orientedTurn p r q = -orientedTurn p q r := by
  simp only [orientedTurn]
  ring

theorem orientedTurn_reverse_edge (p q r : Point) :
    orientedTurn r q p = -orientedTurn p q r := by
  simp only [orientedTurn]
  ring

/-- `q` is the unique counterclockwise gift-wrap successor of `p`: its
directed support line has every other hull vertex strictly on the left. -/
def IsCCWNext (A : Finset Point) (p q : Point) : Prop :=
  q ∈ hullVertices A ∧ IsStrictSupportingEdge A p q ∧
    ∀ x ∈ hullVertices A, x ≠ p → x ≠ q → 0 < orientedTurn p q x

theorem crossFunctional_sub_eq_orientedTurn (p q x : Point) :
    crossFunctional (q - p) x - crossFunctional (q - p) p =
      orientedTurn p q x := by
  simp only [crossFunctional_apply, crossVec, orientedTurn, PiLp.sub_apply]
  ring

/-- The interior center lies strictly to the left of every directed
gift-wrap edge. -/
theorem IsCCWNext.turn_interior_pos {A : Finset Point} {p q C : Point}
    (hthree : 3 ≤ (hullVertices A).card) (hp : p ∈ hullVertices A)
    (hnext : IsCCWNext A p q)
    (hC : C ∈ interior (convexHull ℝ (A : Set Point))) :
    0 < orientedTurn p q C := by
  have hpq : p ≠ q := hnext.2.1.1
  have heraseCard : 1 < ((hullVertices A).erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨r, hrErase, hrq⟩ :=
    Finset.exists_mem_ne heraseCard q
  have hr : r ∈ hullVertices A := (Finset.mem_erase.mp hrErase).2
  have hrp : r ≠ p := (Finset.mem_erase.mp hrErase).1
  have hrturn : 0 < orientedTurn p q r :=
    hnext.2.2 r hr hrp hrq
  let D : Point →L[ℝ] ℝ := crossFunctional (q - p)
  have hDne : D ≠ 0 :=
    crossFunctional_ne_zero (sub_ne_zero.mpr hpq.symm)
  have hD_hull : ∀ x ∈ hullVertices A, D p ≤ D x := by
    intro x hx
    by_cases hxp : x = p
    · simp [hxp]
    by_cases hxq : x = q
    · subst x
      have hzero : orientedTurn p q q = 0 := by simp [orientedTurn]
      rw [← crossFunctional_sub_eq_orientedTurn, sub_eq_zero] at hzero
      exact hzero.symm.le
    · have hturn := hnext.2.2 x hx hxp hxq
      rw [← crossFunctional_sub_eq_orientedTurn] at hturn
      linarith
  have hhalfConvex : Convex ℝ {x : Point | D p ≤ D x} :=
    (convex_Ici (D p)).linear_preimage D.toLinearMap
  have hhullVertices : convexHull ℝ (hullVertices A : Set Point) ⊆
      {x : Point | D p ≤ D x} :=
    convexHull_min hD_hull hhalfConvex
  have hhull : convexHull ℝ (A : Set Point) ⊆ {x : Point | D p ≤ D x} := by
    rw [← convexHull_hullVertices A]
    exact hhullVertices
  have hsurj : Function.Surjective D := by
    have hex : ∃ v : Point, D v ≠ 0 := by
      by_contra h
      push Not at h
      apply hDne
      ext v
      simpa using h v
    obtain ⟨v, hv⟩ := hex
    intro t
    refine ⟨(t / D v) • v, ?_⟩
    simp [hv]
  have hinterior :
      interior {x : Point | D p ≤ D x} = {x : Point | D p < D x} := by
    change interior (D ⁻¹' Set.Ici (D p)) = D ⁻¹' Set.Ioi (D p)
    rw [D.interior_preimage hsurj, interior_Ici]
  have hDC : D p < D C := by
    have := interior_mono hhull hC
    rwa [hinterior] at this
  rw [← crossFunctional_sub_eq_orientedTurn]
  linarith

theorem hullVertex_existsUnique_isCCWNext
    (A : Finset Point) (hthree : 3 ≤ (hullVertices A).card) {p : Point}
    (hp : p ∈ hullVertices A) :
    ∃! q : Point, IsCCWNext A p q := by
  obtain ⟨q, hq, hedge, hturn⟩ :=
    hullVertex_exists_ccw_strictSupportingEdge A hthree hp
  refine ⟨q, ⟨hq, hedge, hturn⟩, ?_⟩
  intro r hr
  by_contra hqr
  have hpq : p ≠ q := hedge.1
  have hpr : p ≠ r := hr.2.1.1
  have hqrTurn : 0 < orientedTurn p q r :=
    hturn r hr.1 hpr.symm hqr
  have hrqTurn : 0 < orientedTurn p r q :=
    hr.2.2 q hq hpq.symm (Ne.symm hqr)
  rw [orientedTurn_swap_last] at hrqTurn
  linarith

/-- The point-valued gift-wrap successor, bundled back into the hull-vertex
subtype. -/
noncomputable def ccwNextVertex (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) (p : hullVertices A) : hullVertices A :=
  ⟨Classical.choose (hullVertex_existsUnique_isCCWNext A hthree p.property),
    (Classical.choose_spec
      (hullVertex_existsUnique_isCCWNext A hthree p.property)).1.1⟩

theorem ccwNextVertex_spec (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) (p : hullVertices A) :
    IsCCWNext A p (ccwNextVertex A hthree p) :=
  (Classical.choose_spec (hullVertex_existsUnique_isCCWNext A hthree p.property)).1

theorem ccwNextVertex_injective (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) :
    Function.Injective (ccwNextVertex A hthree) := by
  intro p r hnext
  apply Subtype.ext
  by_contra hpr
  have hp := ccwNextVertex_spec A hthree p
  have hr := ccwNextVertex_spec A hthree r
  have hnextp : (ccwNextVertex A hthree p : Point) ≠ p := hp.2.1.1.symm
  have hnextr : (ccwNextVertex A hthree r : Point) ≠ r := hr.2.1.1.symm
  have hpturn : 0 < orientedTurn p (ccwNextVertex A hthree p) r :=
    hp.2.2 r r.property (Ne.symm hpr) (by
      intro hrnext
      exact hnextr (by simpa [hnext] using hrnext.symm))
  have hrturn : 0 < orientedTurn r (ccwNextVertex A hthree r) p :=
    hr.2.2 p p.property hpr (by
      intro hpnext
      exact hnextp (by simpa [hnext] using hpnext.symm))
  have hreversed :
      orientedTurn r (ccwNextVertex A hthree r) p =
        -orientedTurn p (ccwNextVertex A hthree p) r := by
    rw [hnext]
    exact orientedTurn_reverse_edge _ _ _
  rw [hreversed] at hrturn
  linarith

/-- The gift-wrap successor is a permutation of the finite hull vertices. -/
noncomputable def ccwNextEquiv (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) : hullVertices A ≃ hullVertices A :=
  Equiv.ofBijective (ccwNextVertex A hthree) ⟨ccwNextVertex_injective A hthree,
    Finite.injective_iff_surjective.mp (ccwNextVertex_injective A hthree)⟩

@[simp]
theorem ccwNextEquiv_apply (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) (p : hullVertices A) :
    ccwNextEquiv A hthree p = ccwNextVertex A hthree p := rfl

/-- A segment on which a nonzero linear functional is maximal lies on the
frontier of the convex hull.  The proof identifies the interior of the
supporting halfspace using the open mapping theorem. -/
theorem segment_subset_frontier_of_linear_support
    {S : Set Point} {p q : Point} (l : Point →L[ℝ] ℝ)
    (hl : l ≠ 0) (hp : p ∈ S) (hq : q ∈ S) (hpq : l p = l q)
    (hmax : ∀ x ∈ S, l x ≤ l p) :
    segment ℝ p q ⊆ frontier (convexHull ℝ S) := by
  have hhalfConvex : Convex ℝ {x : Point | l x ≤ l p} := by
    exact (convex_Iic (l p)).linear_preimage l.toLinearMap
  have hhull : convexHull ℝ S ⊆ {x : Point | l x ≤ l p} :=
    convexHull_min hmax hhalfConvex
  have hpHull : p ∈ convexHull ℝ S := subset_convexHull ℝ S hp
  have hqHull : q ∈ convexHull ℝ S := subset_convexHull ℝ S hq
  have hsurj : Function.Surjective l := by
    have hex : ∃ v : Point, l v ≠ 0 := by
      by_contra h
      push_neg at h
      apply hl
      ext v
      simpa using h v
    obtain ⟨v, hv⟩ := hex
    intro t
    refine ⟨(t / l v) • v, ?_⟩
    simp [hv]
  have hinterior :
      interior {x : Point | l x ≤ l p} = {x : Point | l x < l p} := by
    change interior (l ⁻¹' Set.Iic (l p)) = l ⁻¹' Set.Iio (l p)
    rw [l.interior_preimage hsurj, interior_Iic]
  intro x hx
  have hxHull : x ∈ convexHull ℝ S :=
    (convex_convexHull ℝ S).segment_subset hpHull hqHull hx
  have hlx : l x = l p := by
    rcases hx with ⟨a, b, ha, hb, hab, rfl⟩
    rw [map_add, map_smul, map_smul, hpq, ← add_smul, hab, one_smul]
  refine ⟨subset_closure hxHull, ?_⟩
  intro hxInterior
  have hxHalfInterior := interior_mono hhull hxInterior
  rw [hinterior] at hxHalfInterior
  exact (ne_of_lt hxHalfInterior) hlx

/-- A strict supporting edge is, in particular, a boundary edge of the
finite convex hull. -/
theorem IsStrictSupportingEdge.segment_subset_frontier
    {A : Finset Point} {p q : Point} (h : IsStrictSupportingEdge A p q)
    (hp : p ∈ A) (hq : q ∈ A) :
    segment ℝ p q ⊆ frontier (convexHull ℝ (A : Set Point)) := by
  obtain ⟨-, l, hl, hpq, hmax, -⟩ := h
  exact segment_subset_frontier_of_linear_support l hl hp hq hpq hmax

/-- The cyclic successor on `Fin n`.  Unlike addition by the numeral `1`,
`finRotate` is available without a global `[NeZero n]` instance. -/
abbrev cyclicSucc {n : ℕ} (i : Fin n) : Fin n := finRotate n i

/-- The minimal API expected from a genuine counterclockwise cyclic
enumeration of the vertices of a finite planar convex hull. -/
structure CyclicHullOrder (A : Finset Point) where
  vertex : Fin (hullVertexCount A) ↪ Point
  range_vertex : Set.range vertex = (hullVertices A : Set Point)
  edge_support : ∀ i, IsStrictSupportingEdge A (vertex i) (vertex (cyclicSucc i))
  strict_turn : ∀ i,
    0 < orientedTurn (vertex i) (vertex (cyclicSucc i))
      (vertex (cyclicSucc (cyclicSucc i)))

namespace CyclicHullOrder

variable {A : Finset Point} (P : CyclicHullOrder A)

@[simp]
theorem vertex_mem_hullVertices (i : Fin (hullVertexCount A)) :
    P.vertex i ∈ hullVertices A := by
  have hi : P.vertex i ∈ Set.range P.vertex := ⟨i, rfl⟩
  have hi' : P.vertex i ∈ (hullVertices A : Set Point) := P.range_vertex ▸ hi
  exact hi'

@[simp]
theorem vertex_mem (i : Fin (hullVertexCount A)) : P.vertex i ∈ A :=
  hullVertices_subset A (P.vertex_mem_hullVertices i)

theorem existsUnique_vertex_eq {x : Point} (hx : x ∈ hullVertices A) :
    ∃! i, P.vertex i = x := by
  have hxrange : x ∈ Set.range P.vertex := P.range_vertex.symm ▸ hx
  obtain ⟨i, hi⟩ := hxrange
  exact ⟨i, hi, fun j hj ↦ P.vertex.injective (hj.trans hi.symm)⟩

theorem consecutive_ne (i : Fin (hullVertexCount A)) :
    P.vertex i ≠ P.vertex (cyclicSucc i) :=
  (P.edge_support i).1

theorem turn_pos (i : Fin (hullVertexCount A)) :
    0 < orientedTurn (P.vertex i) (P.vertex (cyclicSucc i))
      (P.vertex (cyclicSucc (cyclicSucc i))) :=
  P.strict_turn i

theorem edge_subset_frontier (i : Fin (hullVertexCount A)) :
    segment ℝ (P.vertex i) (P.vertex (cyclicSucc i)) ⊆
      frontier (convexHull ℝ (A : Set Point)) :=
  (P.edge_support i).segment_subset_frontier (P.vertex_mem i)
    (P.vertex_mem (cyclicSucc i))

end CyclicHullOrder

end

end Erdos957

import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Twice the signed area of the triangle spanned by two planar vectors. -/
def rayDet (x₁ y₁ x₂ y₂ : ℝ) : ℝ := x₁ * y₂ - y₁ * x₂

/-- A point on the top/right boundary of a rectangle, on the same ray as an
interior point. -/
structure RadialBoundary (X D x y : ℝ) where
  bx : ℝ
  yc : ℝ
  scale : ℝ
  bx_nonneg : 0 ≤ bx
  bx_le : bx ≤ X
  yc_nonneg : 0 ≤ yc
  yc_le : yc ≤ D
  on_edge : bx = X ∨ yc = D
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  x_eq : x = scale * bx
  y_eq : y = scale * yc

/-- Every positive point of a positive rectangle is a contraction of a point
on the top/right boundary along its ray from the origin. -/
theorem exists_radialBoundary
    (X D x y : ℝ) (hX : 0 < X) (hD : 0 < D)
    (hx : 0 < x) (hxX : x ≤ X) (hy : 0 < y) (hyD : y ≤ D) :
    Nonempty (RadialBoundary X D x y) := by
  by_cases hright : X * y ≤ D * x
  · let qy := X * y / x
    let t := x / X
    have hqy0 : 0 ≤ qy := by positivity
    have hqyD : qy ≤ D := by
      dsimp [qy]
      exact (div_le_iff₀ hx).2 (by nlinarith)
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_one hX).2 hxX
    refine ⟨{
      bx := X
      yc := qy
      scale := t
      bx_nonneg := hX.le
      bx_le := le_rfl
      yc_nonneg := hqy0
      yc_le := hqyD
      on_edge := Or.inl rfl
      scale_pos := ht0
      scale_le_one := ht1
      x_eq := ?_
      y_eq := ?_ }⟩
    · dsimp [t]
      field_simp
    · dsimp [t, qy]
      field_simp
  · have htop : D * x < X * y := lt_of_not_ge hright
    let qx := D * x / y
    let t := y / D
    have hqx0 : 0 ≤ qx := by positivity
    have hqxX : qx ≤ X := by
      dsimp [qx]
      exact (div_le_iff₀ hy).2 (by nlinarith)
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_one hD).2 hyD
    refine ⟨{
      bx := qx
      yc := D
      scale := t
      bx_nonneg := hqx0
      bx_le := hqxX
      yc_nonneg := hD.le
      yc_le := le_rfl
      on_edge := Or.inr rfl
      scale_pos := ht0
      scale_le_one := ht1
      x_eq := ?_
      y_eq := ?_ }⟩
    · dsimp [t, qx]
      field_simp
    · dsimp [t]
      field_simp

/-- A monotone coordinate along the top/right boundary, scaled so its range is
`[0,2XD]`. -/
noncomputable def boundaryPotential (X D x y : ℝ) : ℝ :=
  if x = X then X * y else 2 * X * D - D * x

/-- For two boundary points in counterclockwise order, their determinant is at
most the increase of the boundary potential. -/
theorem rayDet_le_boundaryPotential_sub
    (X D px py qx qy : ℝ) (hX : 0 < X) (hD : 0 < D)
    (hpx0 : 0 ≤ px) (hpxX : px ≤ X) (hpy0 : 0 ≤ py) (hpyD : py ≤ D)
    (hqx0 : 0 ≤ qx) (hqxX : qx ≤ X) (hqy0 : 0 ≤ qy) (hqyD : qy ≤ D)
    (hpedge : px = X ∨ py = D) (hqedge : qx = X ∨ qy = D)
    (horient : 0 ≤ rayDet px py qx qy) :
    rayDet px py qx qy ≤
      boundaryPotential X D qx qy - boundaryPotential X D px py := by
  by_cases hpx : px = X
  · by_cases hqx : qx = X
    · simp [boundaryPotential, rayDet, hpx, hqx]
      ring_nf
      exact le_rfl
    · have hqy : qy = D := hqedge.resolve_left hqx
      have hprod : 0 ≤ (X - qx) * (D - py) :=
        mul_nonneg (sub_nonneg.mpr hqxX) (sub_nonneg.mpr hpyD)
      simp [boundaryPotential, rayDet, hpx, hqx, hqy]
      nlinarith [hprod]
  · have hpy : py = D := hpedge.resolve_left hpx
    by_cases hqx : qx = X
    · have hpxlt : px < X := lt_of_le_of_ne hpxX hpx
      have hmul1 : px * qy ≤ px * D :=
        mul_le_mul_of_nonneg_left hqyD hpx0
      have hmul2 : px * D < X * D := mul_lt_mul_of_pos_right hpxlt hD
      have : rayDet px py qx qy < 0 := by
        simp [rayDet, hpy, hqx]
        nlinarith
      linarith
    · have hqy : qy = D := hqedge.resolve_left hqx
      simp [boundaryPotential, rayDet, hpx, hqx, hpy, hqy]
      ring_nf
      exact le_rfl

/-- The boundary potential always lies in `[0,2XD]`. -/
theorem boundaryPotential_mem_Icc
    (X D x y : ℝ) (hX : 0 < X) (hD : 0 < D)
    (hx0 : 0 ≤ x) (hxX : x ≤ X) (hy0 : 0 ≤ y) (hyD : y ≤ D)
    (hedge : x = X ∨ y = D) :
    boundaryPotential X D x y ∈ Set.Icc (0 : ℝ) (2 * X * D) := by
  by_cases hx : x = X
  · simp [boundaryPotential, hx]
    constructor <;> nlinarith [mul_nonneg hX.le hy0, mul_le_mul_of_nonneg_left hyD hX.le]
  · have hyedge : y = D := hedge.resolve_left hx
    simp [boundaryPotential, hx, hyedge]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hxX hD.le]
    · nlinarith [mul_nonneg hD.le hx0]

/-- Radially projecting two angularly ordered rectangle points to the boundary
can only increase their determinant, which is then controlled by the boundary
potential. -/
theorem rayDet_le_potential_of_radialBoundary
    (X D px py qx qy : ℝ) (hX : 0 < X) (hD : 0 < D)
    (wp : RadialBoundary X D px py) (wq : RadialBoundary X D qx qy)
    (horient : 0 < rayDet px py qx qy) :
    rayDet px py qx qy ≤
      boundaryPotential X D wq.bx wq.yc - boundaryPotential X D wp.bx wp.yc := by
  rcases wp with ⟨pbx, pyc, pt, hpbx0, hpbxX, hpyc0, hpycD, hpedge,
    hpt0, hpt1, hpx, hpy⟩
  rcases wq with ⟨qbx, qyc, qt, hqbx0, hqbxX, hqyc0, hqycD, hqedge,
    hqt0, hqt1, hqx, hqy⟩
  have hscale :
      rayDet px py qx qy = pt * qt * rayDet pbx pyc qbx qyc := by
    rw [hpx, hpy, hqx, hqy]
    simp only [rayDet]
    ring
  have hprodpos : 0 < pt * qt := mul_pos hpt0 hqt0
  have hbdetpos : 0 < rayDet pbx pyc qbx qyc := by
    have hmulpos : 0 < pt * qt * rayDet pbx pyc qbx qyc := by
      rw [← hscale]
      exact horient
    by_contra hnot
    have hbnonpos : rayDet pbx pyc qbx qyc ≤ 0 := le_of_not_gt hnot
    have := mul_nonpos_of_nonneg_of_nonpos hprodpos.le hbnonpos
    linarith
  have hprodle : pt * qt ≤ 1 := by
    calc
      pt * qt ≤ 1 * qt := mul_le_mul_of_nonneg_right hpt1 hqt0.le
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hqt1 (by norm_num)
      _ = 1 := by ring
  have hinterior_le_boundary : rayDet px py qx qy ≤ rayDet pbx pyc qbx qyc := by
    rw [hscale]
    have := mul_le_mul_of_nonneg_right hprodle hbdetpos.le
    simpa using this
  exact hinterior_le_boundary.trans
    (rayDet_le_boundaryPotential_sub X D pbx pyc qbx qyc hX hD
      hpbx0 hpbxX hpyc0 hpycD hqbx0 hqbxX hqyc0 hqycD
      hpedge hqedge hbdetpos.le)

/-- Fan triangles with vertices in a positive rectangle have total doubled area
at most `2XD`, provided their rays occur in angular order. -/
theorem rectangle_fan_sum_le
    (N : ℕ) (X D : ℝ) (x y : ℕ → ℝ)
    (hX : 0 < X) (hD : 0 < D)
    (hx : ∀ i, 0 < x i) (hxX : ∀ i, x i ≤ X)
    (hy : ∀ i, 0 < y i) (hyD : ∀ i, y i ≤ D)
    (horient : ∀ i < N, 0 < rayDet (x i) (y i) (x (i + 1)) (y (i + 1))) :
    (∑ i ∈ Finset.range N, rayDet (x i) (y i) (x (i + 1)) (y (i + 1))) ≤
      2 * X * D := by
  classical
  let w : ∀ i : ℕ, RadialBoundary X D (x i) (y i) := fun i =>
    Classical.choice (exists_radialBoundary X D (x i) (y i) hX hD
      (hx i) (hxX i) (hy i) (hyD i))
  let p : ℕ → ℝ := fun i => boundaryPotential X D (w i).bx (w i).yc
  have hlocal : ∀ i < N,
      rayDet (x i) (y i) (x (i + 1)) (y (i + 1)) ≤ p (i + 1) - p i := by
    intro i hi
    simpa [p] using rayDet_le_potential_of_radialBoundary X D
      (x i) (y i) (x (i + 1)) (y (i + 1)) hX hD
      (w i) (w (i + 1)) (horient i hi)
  have htel : ∀ M : ℕ,
      (∑ i ∈ Finset.range M, (p (i + 1) - p i)) = p M - p 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∑ i ∈ Finset.range N, rayDet (x i) (y i) (x (i + 1)) (y (i + 1))) ≤
        ∑ i ∈ Finset.range N, (p (i + 1) - p i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlocal i (Finset.mem_range.mp hi)
    _ = p N - p 0 := htel N
    _ ≤ 2 * X * D := by
      have hp0 := boundaryPotential_mem_Icc X D (w 0).bx (w 0).yc hX hD
        (w 0).bx_nonneg (w 0).bx_le (w 0).yc_nonneg (w 0).yc_le (w 0).on_edge
      have hpN := boundaryPotential_mem_Icc X D (w N).bx (w N).yc hX hD
        (w N).bx_nonneg (w N).bx_le (w N).yc_nonneg (w N).yc_le (w N).on_edge
      have hp0' : 0 ≤ p 0 := by simpa [p] using hp0.1
      have hpN' : p N ≤ 2 * X * D := by simpa [p] using hpN.2
      linarith

/-- One-sided primitive-ray packing in its ordered integer form.  If `N+1`
positive lattice rays lie in `0 < a*r-b*s ≤ D`, with both covered coordinates
bounded by `X`, and are listed in strictly increasing slope order, then the
`N` angular sectors each have determinant at least `a*b`. -/
theorem ordered_positive_ray_count_bound
    (N a b X D : ℕ) (r s : ℕ → ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hbsX : ∀ i, b * s i ≤ X)
    (hside : ∀ i, b * s i < a * r i)
    (hstrip : ∀ i, a * r i ≤ b * s i + D)
    (horder : ∀ i < N, r i * s (i + 1) < r (i + 1) * s i) :
    a * b * N ≤ 2 * X * D := by
  let xr : ℕ → ℝ := fun i => (b * s i : ℕ)
  let yr : ℕ → ℝ := fun i => (a * r i : ℕ) - (b * s i : ℕ)
  have hxrpos : ∀ i, 0 < xr i := by
    intro i
    have hpos : 0 < b * s i := Nat.mul_pos hb (hs i)
    dsimp [xr]
    exact_mod_cast hpos
  have hxrX : ∀ i, xr i ≤ (X : ℝ) := by
    intro i
    dsimp [xr]
    exact_mod_cast hbsX i
  have hyrpos : ∀ i, 0 < yr i := by
    intro i
    have hsR : (b * s i : ℕ) < (a * r i : ℕ) := hside i
    have hsR' : ((b * s i : ℕ) : ℝ) < ((a * r i : ℕ) : ℝ) := by
      exact_mod_cast hsR
    dsimp [yr]
    linarith
  have hyrD : ∀ i, yr i ≤ (D : ℝ) := by
    intro i
    have hsR : ((a * r i : ℕ) : ℝ) ≤
        ((b * s i : ℕ) : ℝ) + (D : ℝ) := by
      exact_mod_cast hstrip i
    dsimp [yr]
    linarith
  have hdetid : ∀ i,
      rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) =
        (a : ℝ) * (b : ℝ) *
          ((r (i + 1) : ℝ) * (s i : ℝ) - (r i : ℝ) * (s (i + 1) : ℝ)) := by
    intro i
    simp only [xr, yr, rayDet, Nat.cast_mul]
    ring
  have hdetpos : ∀ i < N,
      0 < rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) := by
    intro i hi
    rw [hdetid i]
    have hord : (r i : ℝ) * (s (i + 1) : ℝ) <
        (r (i + 1) : ℝ) * (s i : ℝ) := by
      exact_mod_cast horder i hi
    positivity
  have hdetlower : ∀ i < N,
      ((a * b : ℕ) : ℝ) ≤ rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) := by
    intro i hi
    rw [hdetid i, Nat.cast_mul]
    have hsucc : r i * s (i + 1) + 1 ≤ r (i + 1) * s i :=
      (Nat.succ_le_iff).2 (horder i hi)
    have hsuccR : ((r i * s (i + 1) : ℕ) : ℝ) + 1 ≤
        ((r (i + 1) * s i : ℕ) : ℝ) := by
      exact_mod_cast hsucc
    have hdelta : (1 : ℝ) ≤
        (r (i + 1) : ℝ) * (s i : ℝ) - (r i : ℝ) * (s (i + 1) : ℝ) := by
      norm_num only [Nat.cast_mul] at hsuccR
      linarith
    have hab0 : 0 ≤ (a : ℝ) * (b : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hdelta hab0
    simpa using this
  have hfan := rectangle_fan_sum_le N (X : ℝ) (D : ℝ) xr yr
    (by exact_mod_cast hX) (by exact_mod_cast hD)
    hxrpos hxrX hyrpos hyrD hdetpos
  have hreal : (N : ℝ) * ((a * b : ℕ) : ℝ) ≤ 2 * (X : ℝ) * (D : ℝ) := by
    calc
      (N : ℝ) * ((a * b : ℕ) : ℝ) =
          ∑ i ∈ Finset.range N, ((a * b : ℕ) : ℝ) := by simp
      _ ≤ ∑ i ∈ Finset.range N,
          rayDet (xr i) (yr i) (xr (i + 1)) (yr (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hdetlower i (Finset.mem_range.mp hi)
      _ ≤ 2 * (X : ℝ) * (D : ℝ) := hfan
  have hnat : N * (a * b) ≤ 2 * X * D := by
    exact_mod_cast hreal
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnat

end Erdos489

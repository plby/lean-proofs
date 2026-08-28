import Wikipedia.HopfProblem.FundamentalGroupVanKampenSquarePaths

/-!
# The boundary identity for one rectangle of a homotopy square

The two routes around a rectangle are joined by coordinatewise affine
interpolation in the unit square.  The interpolation stays in the rectangle,
so local homotopy invariance gives the boundary identity whenever the whole
rectangle maps into one member of the cover.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X]

/-- Affine interpolation of two paths in the square fixes their endpoints. -/
def squarePathHomotopy {x y : I × I} (p q : Path x y) : Path.Homotopy p q where
  toFun u := (Icc.convexComb (p u.2).1 (q u.2).1 u.1,
    Icc.convexComb (p u.2).2 (q u.2).2 u.1)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Icc.continuous_convexComb_prod.comp
        (((p.continuous.comp continuous_snd).fst).prodMk
          (((q.continuous.comp continuous_snd).fst).prodMk continuous_fst))
    · exact Icc.continuous_convexComb_prod.comp
        (((p.continuous.comp continuous_snd).snd).prodMk
          (((q.continuous.comp continuous_snd).snd).prodMk continuous_fst))
  map_zero_left u := by simp
  map_one_left u := by simp
  prop' r u hu := by
    rcases hu with rfl | rfl <;> simp

/-- Interpolation between two points of a closed interval stays in it. -/
theorem convexComb_mem_Icc {s t u v : I} (hu : u ∈ Icc s t) (hv : v ∈ Icc s t)
    (r : I) : Icc.convexComb u v r ∈ Icc s t := by
  change (Icc.convexComb u v r : ℝ) ∈ Icc (s : ℝ) (t : ℝ)
  exact convex_Icc (s : ℝ) (t : ℝ)
    (show (u : ℝ) ∈ Icc (s : ℝ) (t : ℝ) from hu)
    (show (v : ℝ) ∈ Icc (s : ℝ) (t : ℝ) from hv) (unitInterval.one_minus_nonneg r)
    (unitInterval.nonneg r) (sub_add_cancel _ _)

/-- The affine path homotopy stays in every rectangle containing its two paths. -/
theorem squarePathHomotopy_mem_rectangle {x y : I × I} (p q : Path x y)
    (s t a b : I) (hp : ∀ u, p u ∈ Icc s t ×ˢ Icc a b)
    (hq : ∀ u, q u ∈ Icc s t ×ˢ Icc a b) (u : I × I) :
    squarePathHomotopy p q u ∈ Icc s t ×ˢ Icc a b :=
  ⟨convexComb_mem_Icc (hp u.2).1 (hq u.2).1 u.1,
    convexComb_mem_Icc (hp u.2).2 (hq u.2).2 u.1⟩

/-- First horizontal and then vertical around a rectangle. -/
def rectangleHorizontalVertical (s t a b : I) : Path (s, a) (t, b) :=
  ((squareHorizontal (ContinuousMap.id (I × I)) s).subpath a b).trans
    ((squareVertical (ContinuousMap.id (I × I)) b).subpath s t)

/-- First vertical and then horizontal around the same rectangle. -/
def rectangleVerticalHorizontal (s t a b : I) : Path (s, a) (t, b) :=
  ((squareVertical (ContinuousMap.id (I × I)) a).subpath s t).trans
    ((squareHorizontal (ContinuousMap.id (I × I)) t).subpath a b)

theorem rectangleHorizontalVertical_map (F : C(I × I, X)) (s t a b : I) :
    (rectangleHorizontalVertical s t a b).map F.continuous =
      ((squareHorizontal F s).subpath a b).trans
        ((squareVertical F b).subpath s t) := by
  exact Path.map_trans ((squareHorizontal (ContinuousMap.id (I × I)) s).subpath a b)
    ((squareVertical (ContinuousMap.id (I × I)) b).subpath s t) F.continuous

theorem rectangleVerticalHorizontal_map (F : C(I × I, X)) (s t a b : I) :
    (rectangleVerticalHorizontal s t a b).map F.continuous =
      ((squareVertical F a).subpath s t).trans
        ((squareHorizontal F t).subpath a b) := by
  exact Path.map_trans ((squareVertical (ContinuousMap.id (I × I)) a).subpath s t)
    ((squareHorizontal (ContinuousMap.id (I × I)) t).subpath a b) F.continuous

theorem rectangleHorizontalVertical_mem (s t a b : I) (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleHorizontalVertical s t a b u ∈ Icc s t ×ˢ Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨le_rfl, hst⟩, Icc.le_convexComb hab u, Icc.convexComb_le hab u⟩
  · intro u
    exact ⟨⟨Icc.le_convexComb hst u, Icc.convexComb_le hst u⟩, hab, le_rfl⟩

theorem rectangleVerticalHorizontal_mem (s t a b : I) (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleVerticalHorizontal s t a b u ∈ Icc s t ×ˢ Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨Icc.le_convexComb hst u, Icc.convexComb_le hst u⟩, le_rfl, hab⟩
  · intro u
    exact ⟨⟨hst, le_rfl⟩, Icc.le_convexComb hab u, Icc.convexComb_le hab u⟩

/-- An actual endpoint-preserving homotopy between the two rectangle routes. -/
def rectangleBoundaryHomotopy (F : C(I × I, X)) (s t a b : I) :
    Path.Homotopy
      (((squareHorizontal F s).subpath a b).trans
        ((squareVertical F b).subpath s t))
      (((squareVertical F a).subpath s t).trans
        ((squareHorizontal F t).subpath a b)) :=
  ((squarePathHomotopy (rectangleHorizontalVertical s t a b)
    (rectangleVerticalHorizontal s t a b)).map F).cast
      (rectangleHorizontalVertical_map F s t a b)
      (rectangleVerticalHorizontal_map F s t a b)

theorem rectangleBoundaryHomotopy_apply (F : C(I × I, X)) (s t a b : I) (u : I × I) :
    rectangleBoundaryHomotopy F s t a b u =
      F (squarePathHomotopy (rectangleHorizontalVertical s t a b)
        (rectangleVerticalHorizontal s t a b) u) := rfl

/-- If the rectangle maps into a set, so does the whole boundary homotopy. -/
theorem rectangleBoundaryHomotopy_mem (F : C(I × I, X)) (s t a b : I)
    (hst : s ≤ t) (hab : a ≤ b) {A : Set X}
    (hcell : ∀ u ∈ Icc s t ×ˢ Icc a b, F u ∈ A) (u : I × I) :
    rectangleBoundaryHomotopy F s t a b u ∈ A := by
  rw [rectangleBoundaryHomotopy_apply]
  exact hcell _ (squarePathHomotopy_mem_rectangle _ _ s t a b
    (rectangleHorizontalVertical_mem s t a b hst hab)
    (rectangleVerticalHorizontal_mem s t a b hst hab) u)

namespace PathValue

variable {ι G : Type*} [Group G]

/-- Local homotopy invariance identifies the two products around one cell. -/
theorem square_cell_of_local (V : PathValue X G) {U : ι → Set X}
    (L : LocalPathValue U G) (hExt : V.Extends L) (hL : L.HomotopyInvariant)
    (i : ι) (F : C(I × I, X)) (s t a b : I) (hst : s ≤ t) (hab : a ≤ b)
    (hcell : ∀ u ∈ Icc s t ×ˢ Icc a b, F u ∈ U i) :
    V.value ((squareHorizontal F s).subpath a b) *
        V.value ((squareVertical F b).subpath s t) =
      V.value ((squareVertical F a).subpath s t) *
        V.value ((squareHorizontal F t).subpath a b) := by
  let H := rectangleBoundaryHomotopy F s t a b
  have hH : ∀ u, H u ∈ U i := rectangleBoundaryHomotopy_mem F s t a b hst hab hcell
  have hp : ∀ u, ((squareHorizontal F s).subpath a b).trans
      ((squareVertical F b).subpath s t) u ∈ U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_zero_left u)).mp (hH (0, u))
  have hq : ∀ u, ((squareVertical F a).subpath s t).trans
      ((squareHorizontal F t).subpath a b) u ∈ U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_one_left u)).mp (hH (1, u))
  calc
    _ = V.value (((squareHorizontal F s).subpath a b).trans
        ((squareVertical F b).subpath s t)) := (V.trans _ _).symm
    _ = L.value i _ hp := hExt i _ hp
    _ = L.value i _ hq := hL i _ _ hp hq H hH
    _ = V.value (((squareVertical F a).subpath s t).trans
        ((squareHorizontal F t).subpath a b)) := (hExt i _ hq).symm
    _ = _ := V.trans _ _

end PathValue

end Wikipedia.HopfProblem.FundamentalGroupVanKampen

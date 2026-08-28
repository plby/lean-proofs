import Wikipedia.HopfProblem.DegreeCollapseSphereProductLocalFormula

/-!
# Smoothness away from the pole and regularity of the actual sphere products

The exact finite formulas transfer Euclidean smoothness and surjective
derivatives through the original sphere charts. The original product
suspension and smash square are smooth on the full open preimage of
the complement of their pole whenever the original map has that property.
-/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereProductSmoothRegularity

open NoExoticSixSphere SphereComposition CubicalSphereSuspension
open FiniteSphereProductCharts SphereFiniteRepresentative SphereProductLocalFormula

variable {m n : ℕ} (f : Based m n)

def SmoothAway : Prop :=
  ∀ x : Sphere m, f.val x ≠ spherePole n → ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val x

theorem smoothAway_contMDiffOn (hf : SmoothAway f) :
    ContMDiffOn (𝓡 m) (𝓡 n) ∞ f.val {x | f.val x ≠ spherePole n} :=
  fun x hx ↦ (hf x hx).contMDiffWithinAt

theorem product_contMDiffAt (p : V m × ℝ)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hb : f.val (point m p.1) ≠ spherePole n) :
    ContMDiffAt (𝓡 (m + 1)) (𝓡 (n + 1)) ∞
      (productBasedMap f).val ((lineChart m).symm p) :=
  SphereChartRegularity.contMDiffAt_of_inverse_square
    (lineCoordinates m) (lineCoordinates n) (productBasedMap f).val (line f.val) p
    (line_contDiffAt f.val p hf hb).contMDiffAt (line_eventually f p hb)

theorem product_mfderiv_surjective (p : V m × ℝ)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f.val (point m p.1))) :
    Function.Surjective (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1))
      (productBasedMap f).val ((lineChart m).symm p)) :=
  SphereChartRegularity.mfderiv_surjective_of_inverse_square
    (lineCoordinates m) (lineCoordinates n) (productBasedMap f).val (line f.val) p
    (line_contDiffAt f.val p hf hb).contMDiffAt
    ((SphereChartRegularity.mfderiv_surjective_iff_fderiv (line f.val) p).mpr
      (line_fderiv_surjective f.val p hf hb hs))
    (line_eventually f p hb)

theorem square_contMDiffAt (p : V m × V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.2))
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n) :
    ContMDiffAt (𝓡 (m + m)) (𝓡 (n + n)) ∞
      (SphereSmash.squareMap f) ((pairChart m).symm p) :=
  SphereChartRegularity.contMDiffAt_of_inverse_square
    (sumCoordinates m) (sumCoordinates n) (SphereSmash.squareMap f) (square f.val) p
    (square_contDiffAt f.val p hf hg hb hc).contMDiffAt (square_eventually f p hb hc)

theorem square_mfderiv_surjective (p : V m × V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.1))
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val (point m p.2))
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f.val (point m p.1)))
    (ht : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f.val (point m p.2))) :
    Function.Surjective (mfderiv (𝓡 (m + m)) (𝓡 (n + n))
      (SphereSmash.squareMap f) ((pairChart m).symm p)) :=
  SphereChartRegularity.mfderiv_surjective_of_inverse_square
    (sumCoordinates m) (sumCoordinates n) (SphereSmash.squareMap f) (square f.val) p
    (square_contDiffAt f.val p hf hg hb hc).contMDiffAt
    ((SphereChartRegularity.mfderiv_surjective_iff_fderiv (square f.val) p).mpr
      (square_fderiv_surjective f.val p hf hg hb hc hs ht))
    (square_eventually f p hb hc)

theorem product_smoothAway (hf : SmoothAway f) : SmoothAway (productBasedMap f) := by
  intro y hy
  have hyn : y ≠ spherePole (m + 1) := by
    intro h
    exact hy ((congrArg (productBasedMap f).val h).trans (productBasedMap f).property)
  let p := lineChart m y
  have hp : (lineChart m).symm p = y := (lineChart m).left_inv
    (by simpa only [lineChart, chart_source, mem_compl_iff, mem_singleton_iff] using hyn)
  have hb : f.val (point m p.1) ≠ spherePole n := by
    intro h
    exact hy ((congrArg (productBasedMap f).val hp).symm.trans (line_pole f p h))
  exact hp ▸ product_contMDiffAt f p (hf _ hb) hb

theorem square_smoothAway (hf : SmoothAway f) : SmoothAway (SphereSmash.basedSquare f) := by
  intro y hy
  have hyn : y ≠ spherePole (m + m) := by
    intro h
    exact hy ((congrArg (SphereSmash.squareMap f) h).trans (SphereSmash.squareMap_pole f))
  let p := pairChart m y
  have hp : (pairChart m).symm p = y := (pairChart m).left_inv
    (by simpa only [pairChart, chart_source, mem_compl_iff, mem_singleton_iff] using hyn)
  have hb : f.val (point m p.1) ≠ spherePole n := by
    intro h
    exact hy ((congrArg (SphereSmash.squareMap f) hp).symm.trans (square_pole_left f p h))
  have hc : f.val (point m p.2) ≠ spherePole n := by
    intro h
    exact hy ((congrArg (SphereSmash.squareMap f) hp).symm.trans (square_pole_right f p h))
  exact hp ▸ square_contMDiffAt f p (hf _ hb) (hf _ hc) hb hc

theorem product_regular_at_slice (x : Sphere m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val x) (hb : f.val x ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f.val x)) :
    Function.Surjective (mfderiv (𝓡 (m + 1)) (𝓡 (n + 1))
      (productBasedMap f).val (ProductSphereFiber.slice m x)) := by
  have hx : x ≠ spherePole m := by
    intro h
    exact hb ((congrArg f.val h).trans f.property)
  have hp := point_projection m hx
  have hr := product_mfderiv_surjective f (sphereProjection m x, (0 : ℝ))
    (hp.symm ▸ hf) (hp.symm ▸ hb) (hp.symm ▸ hs)
  exact (slice_finite m hx).symm ▸ hr

theorem square_regular_at_pairing (x y : Sphere m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val x)
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f.val y)
    (hb : f.val x ≠ spherePole n) (hc : f.val y ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f.val x))
    (ht : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f.val y)) :
    Function.Surjective (mfderiv (𝓡 (m + m)) (𝓡 (n + n))
      (SphereSmash.squareMap f) (JamesSphere.pairing m (x, y))) := by
  have hx : x ≠ spherePole m := by
    intro h
    exact hb ((congrArg f.val h).trans f.property)
  have hy : y ≠ spherePole m := by
    intro h
    exact hc ((congrArg f.val h).trans f.property)
  have hp := point_projection m hx
  have hq := point_projection m hy
  have hr := square_mfderiv_surjective f (sphereProjection m x, sphereProjection m y)
    (hp.symm ▸ hf) (hq.symm ▸ hg) (hp.symm ▸ hb) (hq.symm ▸ hc)
    (hp.symm ▸ hs) (hq.symm ▸ ht)
  exact (pairing_finite m hx hy).symm ▸ hr

end Wikipedia.HopfProblem.DegreeCollapse.SphereProductSmoothRegularity


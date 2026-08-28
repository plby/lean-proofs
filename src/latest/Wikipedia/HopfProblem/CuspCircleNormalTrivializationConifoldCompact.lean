import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadius

/-!
# Compact normal boundaries and their native toric realization

The genuine squared Euclidean radius level in the two complex normal
coordinates is closed and bounded. Its product with the actual Riemann
sphere is therefore compact. Restricting the already constructed native
toric diffeomorphism gives a homeomorphism onto the corresponding toric
radius level, with the original forward and inverse maps unchanged.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

/-- The actual squared-radius level is closed by continuity of the normal radius. -/
theorem isClosed_radiusSq_level (r : ℝ) :
    IsClosed {v : Fibre | radiusSq v = r ^ 2} :=
  isClosed_eq (contDiff_radiusSq (n := ∞)).continuous continuous_const

/-- Each coordinate norm is at most `|r|` on the actual squared-radius level. -/
theorem radiusSq_level_subset_closedBall (r : ℝ) :
    {v : Fibre | radiusSq v = r ^ 2} ⊆ closedBall (0 : Fibre) |r| := by
  intro v hv
  have hv' : ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 = r ^ 2 := by
    simpa only [mem_ofPred_eq, radiusSq, Complex.normSq_eq_norm_sq] using hv
  rw [mem_closedBall, dist_zero_right, norm_prod_le_iff]
  constructor
  · apply (sq_le_sq₀ (norm_nonneg v.1) (abs_nonneg r)).mp
    rw [sq_abs]
    nlinarith only [hv', sq_nonneg ‖v.2‖]
  · apply (sq_le_sq₀ (norm_nonneg v.2) (abs_nonneg r)).mp
    rw [sq_abs]
    nlinarith only [hv', sq_nonneg ‖v.1‖]

/-- Boundedness is proved in the original finite-dimensional normed fibre. -/
theorem isBounded_radiusSq_level (r : ℝ) :
    Bornology.IsBounded {v : Fibre | radiusSq v = r ^ 2} :=
  (isBounded_closedBall (x := (0 : Fibre)) (r := |r|)).subset
    (radiusSq_level_subset_closedBall r)

/-- The real squared-radius level is compact, including at radius zero. -/
theorem isCompact_radiusSq_level (r : ℝ) :
    IsCompact {v : Fibre | radiusSq v = r ^ 2} :=
  isCompact_of_isClosed_isBounded (isClosed_radiusSq_level r)
    (isBounded_radiusSq_level r)

/-- The original product boundary, using the actual squared Euclidean radius. -/
abbrev ProductBoundary (r : ℝ) :=
  {p : RiemannSphere × Fibre // radiusSq p.2 = r ^ 2}

/-- Compactness comes from the actual compact sphere and compact normal-radius level. -/
instance productBoundaryCompactSpace (r : ℝ) : CompactSpace (ProductBoundary r) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {p : RiemannSphere × Fibre | radiusSq p.2 = r ^ 2}
  convert (isCompact_univ : IsCompact (univ : Set RiemannSphere)).prod
    (isCompact_radiusSq_level r) using 1
  ext p
  simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and]

/-- The radius level inside the unchanged native toric neighborhood. -/
abbrev ToricBoundary (r : ℝ) :=
  {y : toricNeighborhood // radiusSq (toricNeighborhoodDiffeomorph.symm y).2 = r ^ 2}

/-- The existing native toric diffeomorphism restricted to the literal radius level. -/
def productToricBoundaryHomeomorph (r : ℝ) :
    ProductBoundary r ≃ₜ ToricBoundary r :=
  toricNeighborhoodDiffeomorph.toHomeomorph.subtype
    (p := fun p => radiusSq p.2 = r ^ 2)
    (q := fun y => radiusSq (toricNeighborhoodDiffeomorph.symm y).2 = r ^ 2)
    (by intro p; simp only [Diffeomorph.coe_toHomeomorph, Diffeomorph.symm_apply_apply])

/-- The forward map is literally the existing toric diffeomorphism. -/
@[simp] theorem productToricBoundaryHomeomorph_val (r : ℝ) (p : ProductBoundary r) :
    (productToricBoundaryHomeomorph r p).val = toricNeighborhoodDiffeomorph p.val := rfl

/-- The inverse map is literally the inverse of the existing toric diffeomorphism. -/
@[simp] theorem productToricBoundaryHomeomorph_symm_val (r : ℝ) (y : ToricBoundary r) :
    ((productToricBoundaryHomeomorph r).symm y).val =
      toricNeighborhoodDiffeomorph.symm y.val := rfl

/-- The literal toric radius level inherits compactness through the restricted native map. -/
instance toricBoundaryCompactSpace (r : ℝ) : CompactSpace (ToricBoundary r) :=
  (productToricBoundaryHomeomorph r).compactSpace

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

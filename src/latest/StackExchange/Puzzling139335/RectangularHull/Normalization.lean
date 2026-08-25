import StackExchange.Puzzling139335.RectangularHull.CorneredBands
import StackExchange.Puzzling139335.RectangularHull.DissectionTransport
import StackExchange.Puzzling139335.RectangularHull.Normalization.BandSymmetry
import StackExchange.Puzzling139335.RectangularHull.Normalization.Preparation
import StackExchange.Puzzling139335.RectangularHull.Normalization.Relabeling

/-!
# Actual normalization to bottom and top outer bands

An explicit square isometry sends the two opposite corner-bearing hulls
to the bottom and top bands. A permutation labels those pieces zero and
one. Every dissection hypothesis and the protected center are preserved
by these operations, and the actual vertex contacts prove that the common
height is at most one half.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem exists_normalized_outerBands_of_opposite_cornered_bands
    (d : SquareDissection) (hc : d.HasProtectedCenter) {h : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) {i j s : Fin 4} (hij : i ≠ j)
    (hi : convexHull ℝ (d.piece i) = sideBand h s)
    (hj : convexHull ℝ (d.piece j) = sideBand h (s + 2))
    (hcornerless : ∀ k, k ≠ i → k ≠ j → ∀ q, corner q ∉ d.piece k) :
    ∃ d' : SquareDissection, NormalizedOuterBands d' h ∧ d'.HasProtectedCenter := by
  obtain ⟨e, he, hebottom, hetop⟩ := exists_sideBand_normalizing_isometry h s
  obtain ⟨σ, hσ0, hσ1⟩ := exists_piece_relabeling hij
  let d' : SquareDissection := (d.map e he).reindex σ
  have hbottom : convexHull ℝ (d'.piece 0) = axisBox h := by
    change convexHull ℝ (e '' d.piece (σ 0)) = axisBox h
    rw [hσ0]
    calc
      convexHull ℝ (e '' d.piece i) = e '' convexHull ℝ (d.piece i) :=
        (e.toAffineEquiv.toAffineMap.image_convexHull _).symm
      _ = e '' sideBand h s := by rw [hi]
      _ = axisBox h := hebottom
  have htop : convexHull ℝ (d'.piece 1) = horizontalBand (1 - h) 1 := by
    change convexHull ℝ (e '' d.piece (σ 1)) = horizontalBand (1 - h) 1
    rw [hσ1]
    calc
      convexHull ℝ (e '' d.piece j) = e '' convexHull ℝ (d.piece j) :=
        (e.toAffineEquiv.toAffineMap.image_convexHull _).symm
      _ = e '' sideBand h (s + 2) := by rw [hj]
      _ = horizontalBand (1 - h) 1 := hetop
  have hmiddle : ∀ k : Fin 4, k = 2 ∨ k = 3 → ∀ q, corner q ∉ d'.piece k := by
    intro k hk q
    have hne := piece_relabeling_middle_ne hσ0 hσ1 hk
    change corner q ∉ e '' d.piece (σ k)
    exact cornerless_image_square_isometry (hcornerless (σ k) hne.1 hne.2) e he q
  refine ⟨d', NormalizedOuterBands.of_opposite_hulls d' hh0 hh1.le
    hbottom htop hmiddle, ?_⟩
  exact ((d.map e he).reindex_hasProtectedCenter σ).mpr
    ((d.map_hasProtectedCenter e he).mpr hc)

/-- The required normal form is constructed from actual common rectangular hulls. -/
theorem CommonFrames.exists_normalized_outerBands {d : SquareDissection}
    (F : CommonFrames d) (hc : d.HasProtectedCenter) {h : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1)
    (hfirst : ∀ i, ‖(F.frame i).first‖ = 1)
    (hsecond : ∀ i, ‖(F.frame i).second‖ = h) :
    ∃ d' : SquareDissection, NormalizedOuterBands d' h ∧ d'.HasProtectedCenter := by
  obtain ⟨i, j, s, hij, hi, hj, hcornerless⟩ :=
    F.exists_opposite_cornered_bands hh0 hh1 hfirst hsecond
  exact exists_normalized_outerBands_of_opposite_cornered_bands
    d hc hh0 hh1 hij hi hj hcornerless

end Puzzling139335.RectangularHull

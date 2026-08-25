import StackExchange.Puzzling139335.UnitPairs.Defs
import StackExchange.Puzzling139335.SegmentCrossing.Jordan
import StackExchange.Puzzling139335.SegmentCrossing.Overlap

/-! Points on a nondegenerate determinant supporting line lie on the frontier. -/

open Set
open Puzzling139335.UnitPairs Puzzling139335.SegmentCrossing

namespace Puzzling139335.N8

/-- No regularity assumption on `P` is needed: a point of `P` on a
nonconstant supporting line cannot be an interior point. -/
theorem mem_frontier_of_sideDet_support {P : Set Plane} {a b c x : Plane}
    (hnonzero : sideDet a b c ≠ 0)
    (hsupport : ∀ y ∈ P, 0 ≤ sideDet a b c * sideDet a b y)
    (hx : x ∈ P) (hzero : sideDet a b x = 0) : x ∈ frontier P := by
  have hdet : det (b - a) (c - a) ≠ 0 := by
    simpa only [det, PiLp.sub_apply, sideDet] using hnonzero
  have hid (y : Plane) :
      sideDet a b y = detForm (b - a) y - detForm (b - a) a := by
    simp only [sideDet, detForm_apply, det, PiLp.sub_apply]
    ring
  let f : Plane →L[ℝ] ℝ := (-sideDet a b c) • detForm (b - a)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨y, hy⟩ := detForm_surjective_of_det_ne_zero hdet
      (t / (-sideDet a b c))
    refine ⟨y, ?_⟩
    change (-sideDet a b c) * detForm (b - a) y = t
    rw [hy]
    field_simp
  apply mem_frontier_of_linear_support f hf (c := f a) ?_ hx ?_
  · intro y hy
    have hs := hsupport y hy
    rw [hid y] at hs
    change (-sideDet a b c) * detForm (b - a) y ≤
      (-sideDet a b c) * detForm (b - a) a
    nlinarith only [hs]
  · rw [hid x] at hzero
    change (-sideDet a b c) * detForm (b - a) x =
      (-sideDet a b c) * detForm (b - a) a
    rw [sub_eq_zero.mp hzero]

end Puzzling139335.N8

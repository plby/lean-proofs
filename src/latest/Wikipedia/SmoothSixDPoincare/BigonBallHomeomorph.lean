import Wikipedia.SmoothSixDPoincare.WhitneyBigon
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# A genuine ambient homeomorphism carrying the bigon to a Euclidean disk

Convexity, compactness, and an explicit interior point allow the proved gauge
rescaling theorem to identify the cornered bigon with a closed Euclidean disk,
its interior with the open disk, and its full frontier with the standard circle.
This is a topological change of variables, not a smooth corner-straightening map.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

theorem convex_bigon {h : ℝ} (hh : 0 ≤ h) : Convex ℝ (bigon h) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x.2 + b * y.2 ∧
    h * (a * x.1 + b * y.1) ^ 2 + (a * x.2 + b * y.2) ≤ h
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
  have hsq : (a * x.1 + b * y.1) ^ 2 =
      a * x.1 ^ 2 + b * y.1 ^ 2 - a * b * (x.1 - y.1) ^ 2 := by
    calc
      _ = (a + b) * (a * x.1 ^ 2 + b * y.1 ^ 2) - a * b * (x.1 - y.1) ^ 2 := by ring
      _ = _ := by rw [hab, one_mul]
  calc
    _ = a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) -
        h * a * b * (x.1 - y.1) ^ 2 := by rw [hsq]; ring
    _ ≤ a * (h * x.1 ^ 2 + x.2) + b * (h * y.1 ^ 2 + y.2) :=
      sub_le_self _ (mul_nonneg (mul_nonneg (mul_nonneg hh ha) hb) (sq_nonneg _))
    _ ≤ a * h + b * h :=
      add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = h := by rw [← add_mul, hab, one_mul]

theorem bigon_center_mem_interior {h : ℝ} (hh : 0 < h) :
    (0, h / 2) ∈ interior (bigon h) := by
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h / 2 ∧ h / 2 < h * (1 - 0 ^ 2)
  norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
  constructor <;> linarith

theorem interior_bigon_nonempty {h : ℝ} (hh : 0 < h) : (interior (bigon h)).Nonempty :=
  ⟨(0, h / 2), bigon_center_mem_interior hh⟩

/-- The entire ambient plane is homeomorphic to the Euclidean plane, carrying the exact
bigon, its interior, and its frontier to the standard closed disk, open disk, and circle. -/
theorem exists_bigon_disk_homeomorph {h : ℝ} (hh : 0 < h) :
    ∃ e : (ℝ × ℝ) ≃ₜ Hemisphere.Ambient 2,
      e '' bigon h = Metric.closedBall 0 1 ∧
      e '' interior (bigon h) = Metric.ball 0 1 ∧
      e '' frontier (bigon h) = Metric.sphere 0 1 := by
  let L : (ℝ × ℝ) ≃L[ℝ] Hemisphere.Ambient 2 := ContinuousLinearEquiv.ofFinrankEq (by
    simp [Hemisphere.Ambient, Module.finrank_prod])
  let K : Set (Hemisphere.Ambient 2) := L '' bigon h
  have hK : IsCompact K := (isCompact_bigon hh).image L.continuous
  have hc : Convex ℝ K := (convex_bigon hh.le).linear_image L.toLinearEquiv.toLinearMap
  have hLint : L '' interior (bigon h) = interior K :=
    L.toHomeomorph.image_interior (bigon h)
  have hLfront : L '' frontier (bigon h) = frontier K :=
    L.toHomeomorph.image_frontier (bigon h)
  have hne : (interior K).Nonempty := by
    rw [← hLint]
    exact (interior_bigon_nonempty hh).image L
  obtain ⟨e, heint, heclosed, hefront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hK.isBounded
  refine ⟨L.toHomeomorph.trans e, ?_, ?_, ?_⟩
  · calc
      _ = e '' (L '' bigon h) := (image_image e L (bigon h)).symm
      _ = Metric.closedBall 0 1 := by
        change e '' K = _
        rwa [hK.isClosed.closure_eq] at heclosed
  · calc
      _ = e '' (L '' interior (bigon h)) := (image_image e L (interior (bigon h))).symm
      _ = Metric.ball 0 1 := by rw [hLint]; exact heint
  · calc
      _ = e '' (L '' frontier (bigon h)) := (image_image e L (frontier (bigon h))).symm
      _ = Metric.sphere 0 1 := by rw [hLfront]; exact hefront

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel

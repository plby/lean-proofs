import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Linarith

/-!
# Finite packing of positive-length intervals

A family of pairwise disjoint open subintervals of the unit interval is finite
if their lengths have a common positive lower bound.  The proof separates the
left endpoints and uses a finite cover of the compact parameter interval.
-/

open Set Metric

namespace Puzzling139335.CentralRotation.ArcPacking

/-- A uniformly separated indexed family contained in a compact metric set has
only finitely many indices. -/
theorem finite_of_separated_in_compact {ι X : Type*} [PseudoMetricSpace X]
    {a : ι → X} {K : Set X} {δ : ℝ}
    (hK : IsCompact K) (hδ : 0 < δ) (ha : ∀ i, a i ∈ K)
    (hsep : Pairwise fun i j => δ ≤ dist (a i) (a j)) : Finite ι := by
  classical
  obtain ⟨s, -, hs, hcover⟩ := hK.finite_cover_balls (half_pos hδ)
  have hchoice : ∀ i, ∃ c : s, dist (a i) c < δ / 2 := by
    intro i
    obtain ⟨c, hc, hball⟩ := mem_iUnion₂.mp (hcover (ha i))
    exact ⟨⟨c, hc⟩, hball⟩
  choose center hcenter using hchoice
  let : Finite s := hs.to_subtype
  refine Finite.of_injective center ?_
  intro i j hij
  by_contra hne
  have hclose : dist (a i) (a j) < δ := by
    calc
      dist (a i) (a j) ≤ dist (a i) (center i) + dist (a j) (center i) :=
        dist_triangle_right _ _ _
      _ < δ := by
        have hi := hcenter i
        have hj := hcenter j
        rw [← hij] at hj
        linarith
  exact (not_lt_of_ge (hsep hne)) hclose

/-- Pairwise disjoint open intervals, each of length at least `δ > 0`,
separate their left endpoints by at least `δ`. -/
theorem left_endpoints_separated {ι : Type*} {a b : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hlen : ∀ i, δ ≤ b i - a i)
    (hdisj : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) :
    Pairwise fun i j => δ ≤ dist (a i) (a j) := by
  intro i j hij
  have hi := hlen i
  have hj := hlen j
  have hmin := Ioo_disjoint_Ioo.mp (hdisj hij)
  rcases le_total (a i) (a j) with horder | horder
  · rw [max_eq_right horder, min_le_iff] at hmin
    have hib : b i ≤ a j := hmin.resolve_right (by linarith)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr horder)]
    linarith
  · rw [max_eq_left horder, min_le_iff] at hmin
    have hjb : b j ≤ a i := hmin.resolve_left (by linarith)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr horder)]
    linarith

/-- A family of disjoint open subintervals of `[0,1]` with a uniform positive
lower bound on length is finite. -/
theorem finite_of_interval_packing {ι : Type*} {a b : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hlen : ∀ i, δ ≤ b i - a i)
    (hdisj : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) :
    Finite ι := by
  apply finite_of_separated_in_compact (K := Icc (0 : ℝ) 1)
    isCompact_Icc hδ
  · intro i
    have hi := hlen i
    have hib := hb i
    exact ⟨ha i, by linarith⟩
  · exact left_endpoints_separated hδ hlen hdisj

end Puzzling139335.CentralRotation.ArcPacking

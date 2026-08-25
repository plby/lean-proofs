import StackExchange.Puzzling139335.CentralRotation.ArcPacking.Intervals
import StackExchange.Puzzling139335.CentralRotation.ArcPacking.Parameters
import StackExchange.Puzzling139335.CentralRotation.ArcPacking.Span

/-!
# Finite packing of nontrivial subarcs of a fixed Jordan arc

The theorem applies to actual `IsArcBetween` subsets of a fixed arc. Relative
arc interiors mean the arc with its two named endpoints removed. A uniform
positive diameter bound and pairwise disjoint relative interiors force the
index type to be finite.

The proof recovers the actual parameter interval of each subarc, uses uniform
continuity to bound its length from below, and then packs disjoint intervals
in the unit interval. No perimeter, boundary measure, or rectifiability
hypothesis is present.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation.ArcPacking

/-- There are only finitely many subarcs of a fixed Jordan arc with pairwise
disjoint relative interiors and diameter at least a fixed positive value. -/
theorem finite_of_disjoint_subarcs {ι : Type*}
    {N : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hN : IsArcBetween N p q)
    {J : ι → Set Schoenflies.Plane} {a b : ι → Schoenflies.Plane}
    (hJ : ∀ i, IsArcBetween (J i) (a i) (b i))
    (hsub : ∀ i, J i ⊆ N)
    (hdisj : Pairwise fun i j => Disjoint (J i \ {a i, b i}) (J j \ {a j, b j}))
    {δ : ℝ} (hδ : 0 < δ) (hdiam : ∀ i, δ ≤ Metric.diam (J i)) : Finite ι := by
  classical
  obtain ⟨f, hf, hfi, rfl, -, -⟩ := hN
  have hex := fun i => exists_subarc_interval hf hfi (hJ i) (hsub i)
  choose l r hl hr hlr hclosed hopen using hex
  obtain ⟨η, hη, hspan⟩ := exists_uniform_span_lower_bound hf hδ
  refine finite_of_interval_packing hη (fun i => (hl i).1) (fun i => (hr i).2)
    (fun i => hspan (l i) (hl i) (r i) (hr i) (hlr i).le ?_) ?_
  · simpa only [← hclosed i] using hdiam i
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hti' : f t ∈ J i \ {a i, b i} := by
      rw [hopen i]
      exact mem_image_of_mem f hti
    have htj' : f t ∈ J j \ {a j, b j} := by
      rw [hopen j]
      exact mem_image_of_mem f htj
    exact Set.disjoint_left.mp (hdisj hij) hti' htj'

/-- In an infinite family with uniformly positive diameters, two of the actual
subarcs overlap away from both pairs of endpoints. -/
theorem exists_overlap_of_subarcs {ι : Type*} [Infinite ι]
    {N : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hN : IsArcBetween N p q)
    {J : ι → Set Schoenflies.Plane} {a b : ι → Schoenflies.Plane}
    (hJ : ∀ i, IsArcBetween (J i) (a i) (b i))
    (hsub : ∀ i, J i ⊆ N)
    {δ : ℝ} (hδ : 0 < δ) (hdiam : ∀ i, δ ≤ Metric.diam (J i)) :
    ∃ i j, i ≠ j ∧ ((J i \ {a i, b i}) ∩ (J j \ {a j, b j})).Nonempty := by
  classical
  by_contra hoverlap
  have hdisj : Pairwise fun i j =>
      Disjoint (J i \ {a i, b i}) (J j \ {a j, b j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hxi hxj => hoverlap ⟨i, j, hij, x, hxi, hxj⟩
  have : Finite ι := finite_of_disjoint_subarcs hN hJ hsub hdisj hδ hdiam
  exact _root_.not_finite ι

/-- An actual nondegenerate Jordan arc has positive Euclidean diameter. -/
theorem diam_pos_of_isArcBetween {J : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} (hJ : IsArcBetween J p q) : 0 < Metric.diam J :=
  Metric.diam_pos ⟨p, hJ.left_mem, q, hJ.right_mem, endpoints_ne hJ⟩
    hJ.isArc.isCompact.isBounded

/-- Isometric copies of a single actual arc cannot form an infinite family
of subarcs of a fixed arc with pairwise disjoint relative interiors. -/
theorem finite_of_disjoint_isometric_subarcs {ι : Type*}
    {N J : Set Schoenflies.Plane} {p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N p q) (hJ : IsArcBetween J a b)
    {e : ι → Schoenflies.Plane → Schoenflies.Plane} (he : ∀ i, Isometry (e i))
    (hsub : ∀ i, e i '' J ⊆ N)
    (hdisj : Pairwise fun i j =>
      Disjoint ((e i '' J) \ {e i a, e i b}) ((e j '' J) \ {e j a, e j b})) :
    Finite ι :=
  finite_of_disjoint_subarcs hN (fun i => isArcBetween_image_isometry hJ (he i))
    hsub hdisj (diam_pos_of_isArcBetween hJ) (fun i => (he i).diam_image J |>.ge)

/-- In particular, any infinite sequence of isometric copies inside a fixed
Jordan arc contains a pair with intersecting relative interiors. -/
theorem exists_overlap_of_isometric_subarcs {ι : Type*} [Infinite ι]
    {N J : Set Schoenflies.Plane} {p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N p q) (hJ : IsArcBetween J a b)
    {e : ι → Schoenflies.Plane → Schoenflies.Plane} (he : ∀ i, Isometry (e i))
    (hsub : ∀ i, e i '' J ⊆ N) :
    ∃ i j, i ≠ j ∧
      (((e i '' J) \ {e i a, e i b}) ∩ ((e j '' J) \ {e j a, e j b})).Nonempty :=
  exists_overlap_of_subarcs hN (fun i => isArcBetween_image_isometry hJ (he i))
    hsub (diam_pos_of_isArcBetween hJ) (fun i => (he i).diam_image J |>.ge)

end Puzzling139335.CentralRotation.ArcPacking

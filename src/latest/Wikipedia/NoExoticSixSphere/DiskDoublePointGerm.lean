import Wikipedia.NoExoticSixSphere.DiskDoublePointTopology
import Wikipedia.NoExoticSixSphere.MapDoublePointLocalCurve
import Wikipedia.NoExoticSixSphere.FourDiskSingularities

/-!
# Transfer of a reflection chart to the actual disk double-point closure

Inside the disk and an original target chart, the disk's actual double-point
locus agrees with the unrestricted coordinate-map locus. Equality of their
closure germs transfers a local reflection chart through a swap-invariant
neighborhood, without changing either subtype topology.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskDoublePoints

variable {E Y Z : Type*} [NormedAddCommGroup E]

theorem exists_curve_of_closed_germ (g : E → Y) (h : E → Z) (x : E)
    (he : closure (points g) =ᶠ[𝓝 (x, x)] closure (MapDoublePoints.points h))
    (hcurve : ∃ hc : (x, x) ∈ closure (MapDoublePoints.points h),
      ∃ d : OpenPartialHomeomorph (closure (MapDoublePoints.points h)) ℝ,
        (⟨(x, x), hc⟩ : closure (MapDoublePoints.points h)) ∈ d.source ∧
        d ⟨(x, x), hc⟩ = 0 ∧
        (∀ r ∈ d.source, MapDoublePoints.swapClosure h r ∈ d.source) ∧
        ∀ r ∈ d.source, d (MapDoublePoints.swapClosure h r) = -d r) :
    ∃ hc : (x, x) ∈ closure (points g),
      ∃ d : OpenPartialHomeomorph (ClosedPoints g) ℝ,
        (⟨(x, x), hc⟩ : ClosedPoints g) ∈ d.source ∧ d ⟨(x, x), hc⟩ = 0 ∧
        (∀ r ∈ d.source, swapClosure g r ∈ d.source) ∧
        ∀ r ∈ d.source, d (swapClosure g r) = -d r := by
  obtain ⟨hh, c, hcp, hcz, hcs, hcn⟩ := hcurve
  have hc : (x, x) ∈ closure (points g) := (Iff.of_eq he.eq_of_nhds).mpr hh
  let p : ClosedPoints g := ⟨(x, x), hc⟩
  let q : closure (MapDoublePoints.points h) := ⟨(x, x), hh⟩
  obtain ⟨N₀, hN₀eq, hN₀open, hN₀p⟩ := mem_nhds_iff.mp he
  let N := N₀ ∩ Prod.swap ⁻¹' N₀
  have hN : IsOpen N := hN₀open.inter (hN₀open.preimage continuous_swap)
  have hNp : (x, x) ∈ N := ⟨hN₀p, hN₀p⟩
  have hNeq : ∀ y ∈ N, y ∈ closure (points g) ↔
      y ∈ closure (MapDoublePoints.points h) := fun _ hy ↦ Iff.of_eq (hN₀eq hy.1)
  let e := SetGerm.coordinates (closure (points g)) (closure (MapDoublePoints.points h))
    N hNeq hN p q
  have eval {r : ClosedPoints g} (hr : r ∈ e.source) : (e r).val = r.val :=
    SetGerm.coordinates_val _ _ _ _ _ _ _ hr
  have hep : e p = q := Subtype.ext (eval hNp)
  have hswapN {r : ClosedPoints g} (hr : r ∈ e.source) :
      swapClosure g r ∈ e.source := ⟨hr.2, hr.1⟩
  have hcommute {r : ClosedPoints g} (hr : r ∈ e.source) :
      e (swapClosure g r) = MapDoublePoints.swapClosure h (e r) := by
    apply Subtype.ext
    rw [eval (hswapN hr)]
    change Prod.swap r.val = Prod.swap (e r).val
    rw [eval hr]
  let d := e.trans c
  have hdp : p ∈ d.source := by
    refine ⟨hNp, ?_⟩
    change e p ∈ c.source
    rw [hep]
    exact hcp
  refine ⟨hc, d, hdp, ?_, ?_, ?_⟩
  · change c (e p) = 0
    rw [hep]
    exact hcz
  · intro r hr
    refine ⟨hswapN hr.1, ?_⟩
    change e (swapClosure g r) ∈ c.source
    rw [hcommute hr.1]
    exact hcs (e r) hr.2
  · intro r hr
    change c (e (swapClosure g r)) = -c (e r)
    rw [hcommute hr.1]
    exact hcn (e r) hr.2

open GLOrthonormalization Metric

theorem closedPoints_chart_eventuallyEq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Vector 7) M] (g : E → M) (hg : ContinuousOn g (ball 0 1))
    (c : PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞)
    (x : E) (hx : x ∈ ball 0 1) (hxc : g x ∈ c.source) :
    closure (points g) =ᶠ[𝓝 (x, x)] closure (MapDoublePoints.points (c ∘ g)) := by
  let N := ball (0 : E) 1 ∩ g ⁻¹' c.source
  have hN : IsOpen N := hg.isOpen_inter_preimage isOpen_ball c.open_source
  have hxN : x ∈ N := ⟨hx, hxc⟩
  apply FlatDoubleCurve.closure_eventuallyEq_of_eventuallyEq
  filter_upwards [(hN.prod hN).mem_nhds ⟨hxN, hxN⟩] with p hp
  apply propext
  constructor
  · intro hdp
    exact ⟨hdp.2.2.1, congrArg c hdp.2.2.2⟩
  · intro hmp
    exact ⟨hp.1.1, hp.2.1, hmp.1, c.injOn hp.1.2 hp.2.2 hmp.2⟩

end NoExoticSixSphere.DiskDoublePoints

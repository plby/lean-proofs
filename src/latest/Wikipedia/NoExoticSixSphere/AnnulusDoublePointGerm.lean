import Wikipedia.NoExoticSixSphere.AnnulusDoublePointTopology
import Wikipedia.NoExoticSixSphere.MapDoublePointLocalCurve
import Wikipedia.NoExoticSixSphere.FourAnnulusSingularities

/-!
# Reflection charts on the actual annulus double-point closure

Near an interior diagonal point in an original target chart, the annulus
double-point locus agrees with the unrestricted coordinate-map locus.
The equality of closure germs transports a reflection chart through a
swap-invariant neighborhood, retaining the actual subtype topology.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization SphereAnnulus

variable {p : ℕ} {Y Z : Type*}

theorem exists_curve_of_closed_germ (g : Vector (p + 1) → Y) (h : Vector (p + 1) → Z)
    (x : Vector (p + 1))
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
  let a : ClosedPoints g := ⟨(x, x), hc⟩
  let b : closure (MapDoublePoints.points h) := ⟨(x, x), hh⟩
  obtain ⟨N₀, hN₀eq, hN₀open, hN₀a⟩ := mem_nhds_iff.mp he
  let N := N₀ ∩ Prod.swap ⁻¹' N₀
  have hN : IsOpen N := hN₀open.inter (hN₀open.preimage continuous_swap)
  have hNa : (x, x) ∈ N := ⟨hN₀a, hN₀a⟩
  have hNeq : ∀ y ∈ N, y ∈ closure (points g) ↔
      y ∈ closure (MapDoublePoints.points h) := fun _ hy ↦ Iff.of_eq (hN₀eq hy.1)
  let e := SetGerm.coordinates (closure (points g)) (closure (MapDoublePoints.points h))
    N hNeq hN a b
  have eval {r : ClosedPoints g} (hr : r ∈ e.source) : (e r).val = r.val :=
    SetGerm.coordinates_val _ _ _ _ _ _ _ hr
  have hea : e a = b := Subtype.ext (eval hNa)
  have hswapN {r : ClosedPoints g} (hr : r ∈ e.source) :
      swapClosure g r ∈ e.source := ⟨hr.2, hr.1⟩
  have hcommute {r : ClosedPoints g} (hr : r ∈ e.source) :
      e (swapClosure g r) = MapDoublePoints.swapClosure h (e r) := by
    apply Subtype.ext
    rw [eval (hswapN hr)]
    change Prod.swap r.val = Prod.swap (e r).val
    rw [eval hr]
  let d := e.trans c
  have hda : a ∈ d.source := by
    refine ⟨hNa, ?_⟩
    change e a ∈ c.source
    rw [hea]
    exact hcp
  refine ⟨hc, d, hda, ?_, ?_, ?_⟩
  · change c (e a) = 0
    rw [hea]
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

theorem closedPoints_chart_eventuallyEq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Vector 7) M] (g : Vector (p + 1) → M)
    (hg : ContinuousOn g (openDomain p))
    (c : PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞)
    (x : Vector (p + 1)) (hx : x ∈ openDomain p) (hxc : g x ∈ c.source) :
    closure (points g) =ᶠ[𝓝 (x, x)] closure (MapDoublePoints.points (c ∘ g)) := by
  let N := openDomain p ∩ g ⁻¹' c.source
  have hN : IsOpen N := hg.isOpen_inter_preimage (isOpen_openDomain p) c.open_source
  have hxN : x ∈ N := ⟨hx, hxc⟩
  apply FlatDoubleCurve.closure_eventuallyEq_of_eventuallyEq
  filter_upwards [(hN.prod hN).mem_nhds ⟨hxN, hxN⟩] with v hv
  apply propext
  constructor
  · intro hdp
    exact ⟨hdp.2.2.1, congrArg c hdp.2.2.2⟩
  · intro hmp
    exact ⟨hv.1.1, hv.2.1, hmp.1, c.injOn hv.1.2 hv.2.2 hmp.2⟩

end NoExoticSixSphere.AnnulusDoublePoints

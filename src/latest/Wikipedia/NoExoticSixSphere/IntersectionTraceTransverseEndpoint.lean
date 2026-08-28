import Wikipedia.NoExoticSixSphere.TransverseSphereChartDifference
import Wikipedia.NoExoticSixSphere.ZeroSlabHalfLineChart
import Wikipedia.NoExoticSixSphere.ImplicitCurveCoordinates
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# A transverse endpoint has an actual half-line chart without a collar assumption

Adjoining the unchanged time coordinate to the coincidence equation gives
an invertible derivative. The inverse-function theorem yields local
coordinates whose second component is exactly the original time. Restricting
the actual zero equation and closed time slab therefore produces a half-line
chart, even when the sphere families are not constant near the endpoint.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization MapIntersections InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hf hg in
theorem exists_zero_chart_of_spatial_transverse (p : pairs (f 0) (g 0))
    (s z : SphereChart) (c : ManifoldChart M)
    (hx : p.val.1 ∈ s.source) (hy : p.val.2 ∈ z.source) (hc : f 0 p.val.1 ∈ c.source)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f 0) p.val.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g 0) p.val.2))) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      endpoint f g 0 p ∈ d.source ∧
      (∀ q ∈ d.source, (d q).val = q.val.1) ∧
      ∀ q ∈ d.source, (d q).val = 0 ↔ q ∈ ends f g := by
  let P := Vector 3 × Vector 3
  let Φ : P × ℝ → Vector 6 := fun q ↦ coordinateDifference f g s z c (q.2, q.1)
  let U : Set (P × ℝ) := Prod.swap ⁻¹' fullCoordinateDomain f g s z c
  have hswap : ContDiff ℝ ∞ (Prod.swap : P × ℝ → ℝ × P) :=
    contDiff_snd.prodMk contDiff_fst
  have hU : IsOpen U := (isOpen_fullCoordinateDomain f g hf hg s z c).preimage
    hswap.continuous
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    (contDiffOn_coordinateDifference_full f g hf hg s z c).comp hswap.contDiffOn
      (fun _ hq ↦ hq)
  have hs : s.symm (s p.val.1) = p.val.1 := s.left_inv hx
  have hz : z.symm (z p.val.2) = p.val.2 := z.left_inv hy
  have hc' : g 0 p.val.2 ∈ c.source := p.property ▸ hc
  have hbase : ((s p.val.1, z p.val.2), (0 : ℝ)) ∈ U := by
    change (s p.val.1 ∈ s.target ∧ z p.val.2 ∈ z.target) ∧
      (f 0 (s.symm (s p.val.1)) ∈ c.source ∧ g 0 (z.symm (z p.val.2)) ∈ c.source)
    rw [hs, hz]
    exact ⟨⟨s.map_source hx, z.map_source hy⟩, hc, hc'⟩
  have hbij : Bijective (fderiv ℝ (fun q : P ↦ Φ (q, 0)) (s p.val.1, z p.val.2)) :=
    bijective_fderiv_spatial_difference f g hf hg 0 p.val.1 p.val.2 s z c hx hy hc
      p.property ht
  obtain ⟨Ψ, hΨbase, hΨU, hΨform⟩ := ImplicitCurve.exists_parameter_coordinates Φ U hU
    (s p.val.1, z p.val.2) 0 hbase hΦ hbij
  let T₀ := (Homeomorph.prodComm ℝ (Sphere 3 × Sphere 3)).toOpenPartialHomeomorph.trans
    ((s.toOpenPartialHomeomorph.prod z.toOpenPartialHomeomorph).prod
      (OpenPartialHomeomorph.refl ℝ))
  let T := T₀.trans Ψ.toOpenPartialHomeomorph
  have hTform (b : ℝ × (Sphere 3 × Sphere 3)) : T b =
      (coordinateDifference f g s z c (b.1, (s b.2.1, z b.2.2)), b.1) := hΨform (T₀ b)
  have hImage : T.IsImage (space f g) (ZeroSlab.model (Vector 6)) := by
    intro b hb
    have hbU : (b.1, (s b.2.1, z b.2.2)) ∈ fullCoordinateDomain f g s z c := hΨU hb.2
    have hbx : b.2.1 ∈ s.source := hb.1.2.1.1
    have hby : b.2.2 ∈ z.source := hb.1.2.1.2
    have hs' : s.symm (s b.2.1) = b.2.1 := s.left_inv hbx
    have hz' : z.symm (z b.2.2) = b.2.2 := z.left_inv hby
    have hzero := coordinateDifference_zero_iff_full f g s z c
      (b.1, (s b.2.1, z b.2.2)) hbU
    rw [hs', hz'] at hzero
    change ((T b).1 = 0 ∧ (T b).2 ∈ Icc 0 1) ↔ b ∈ space f g
    rw [hTform]
    change (coordinateDifference f g s z c (b.1, (s b.2.1, z b.2.2)) = 0 ∧
      b.1 ∈ Icc 0 1) ↔ (b.1 ∈ Icc 0 1 ∧ f b.1 b.2.1 = g b.1 b.2.2)
    rw [hzero, and_comm]
  let a := endpoint f g 0 p
  let b₀ : ZeroSlab.model (Vector 6) := ⟨(0, 0), rfl, ⟨le_rfl, zero_le_one⟩⟩
  have haT : a.val ∈ T.source :=
    ⟨⟨mem_univ _, ⟨hx, hy⟩, mem_univ _⟩, hΨbase⟩
  let E := SubsetCoordinates.coordinates T hImage a b₀
  let d := E.trans (ZeroSlab.initialChart (Vector 6))
  have hEtime (q : space f g) (hq : q ∈ E.source) : (E q).val.2 = q.val.1 := by
    rw [SubsetCoordinates.coordinates_val T hImage a b₀ hq, hTform]
  have had : a ∈ d.source := by
    refine ⟨haT, (ZeroSlab.initialChart_mem_source (Vector 6) (E a)).mpr ?_⟩
    rw [hEtime a haT]
    exact zero_lt_one
  have hdt (q : space f g) (hq : q ∈ d.source) : (d q).val = q.val.1 := by
    change (ZeroSlab.initialChart (Vector 6) (E q)).val = q.val.1
    rw [ZeroSlab.initialChart_apply, hEtime q hq.1]
  refine ⟨d, had, hdt, ?_⟩
  intro q hq
  have hlt := (ZeroSlab.initialChart_mem_source (Vector 6) (E q)).mp hq.2
  rw [hEtime q hq.1] at hlt
  rw [hdt q hq]
  change q.val.1 = 0 ↔ q.val.1 = 0 ∨ q.val.1 = 1
  exact ⟨Or.inl, fun h ↦ h.elim id (fun h1 ↦ False.elim (hlt.ne h1))⟩

include hf hg in
/-- The original manifold charts are chosen internally. Neither a time collar
nor a local chart on the intersection trace is assumed. -/
theorem exists_zero_halfLine_chart_of_transverse [IsManifold (𝓡 6) ∞ M]
    (p : pairs (f 0) (g 0))
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f 0) p.val.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g 0) p.val.2))) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      endpoint f g 0 p ∈ d.source ∧
      (∀ q ∈ d.source, (d q).val = q.val.1) ∧
      ∀ q ∈ d.source, (d q).val = 0 ↔ q ∈ ends f g := by
  let s : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) p.val.1
  let z : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) p.val.2
  let c : ManifoldChart M := modelChartPartialDiffeomorph (I := 𝓡 6) (f 0 p.val.1)
  exact exists_zero_chart_of_spatial_transverse f g hf hg p s z c
    (mem_extChartAt_source _) (mem_extChartAt_source _) (mem_extChartAt_source _) ht

end NoExoticSixSphere.IntersectionTrace

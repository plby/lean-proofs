import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBasic
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreCharts

/-!
# Actual lattice differences between source and pulled-back target charts

On the common domain of an original source lift and a target lift composed
with the descended map, their difference is a genuine target-lattice
element.  It is locally constant and satisfies the exact compatibility
identity needed for the native pullback bundle's cross-cover gauge.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open PeriodTorusAppellHumbert

variable {p q : PeriodDomain} (L : LatticeLinearMap p q)

/-- The actual overlap of the source chart and the pulled-back target chart. -/
def pullbackCrossBaseSet (i : p.Torus × q.Torus) : Set p.Torus :=
  Core.baseSet p i.1 ∩ L.torusMap ⁻¹' Core.baseSet q i.2

theorem pullbackCrossBaseSet_isOpen (i : p.Torus × q.Torus) :
    IsOpen (pullbackCrossBaseSet L i) :=
  (Core.isOpen_baseSet p i.1).inter
    ((Core.isOpen_baseSet q i.2).preimage L.torusContinuousMap.continuous)

/-- Equality of the projected points puts the actual lift difference in the target lattice. -/
theorem pullbackCrossDeck_mem (i : p.Torus × q.Torus) {x : p.Torus}
    (hx : x ∈ pullbackCrossBaseSet L i) :
    Core.lift q i.2 (L.torusMap x) - L.linear (Core.lift p i.1 x) ∈ q.lattice := by
  apply (Submodule.Quotient.eq q.lattice).mp
  change q.lattice.mkQ (Core.lift q i.2 (L.torusMap x)) =
    q.lattice.mkQ (L.linear (Core.lift p i.1 x))
  rw [Core.lift_project q i.2 hx.2, ← L.torusMap_mkQ,
    Core.lift_project p i.1 hx.1]

/-- The actual cross-chart lattice translation, extended by zero outside its overlap. -/
def pullbackCrossDeck (i : p.Torus × q.Torus) (x : p.Torus) : q.lattice := by
  classical
  exact if hx : x ∈ pullbackCrossBaseSet L i then
    ⟨Core.lift q i.2 (L.torusMap x) - L.linear (Core.lift p i.1 x),
      pullbackCrossDeck_mem L i hx⟩ else 0

theorem pullbackCrossDeck_coe (i : p.Torus × q.Torus) {x : p.Torus}
    (hx : x ∈ pullbackCrossBaseSet L i) :
    (pullbackCrossDeck L i x : ComplexPlane₂) =
      Core.lift q i.2 (L.torusMap x) - L.linear (Core.lift p i.1 x) := by
  classical
  simp only [pullbackCrossDeck, dif_pos hx]

theorem pullbackCrossDeck_spec (i : p.Torus × q.Torus) {x : p.Torus}
    (hx : x ∈ pullbackCrossBaseSet L i) :
    L.linear (Core.lift p i.1 x) + (pullbackCrossDeck L i x : ComplexPlane₂) =
      Core.lift q i.2 (L.torusMap x) := by
  rw [pullbackCrossDeck_coe L i hx]
  abel

theorem pullbackCrossDeck_eq_of_add (i : p.Torus × q.Torus) {x : p.Torus}
    (hx : x ∈ pullbackCrossBaseSet L i) (l : q.lattice)
    (hl : L.linear (Core.lift p i.1 x) + l = Core.lift q i.2 (L.torusMap x)) :
    pullbackCrossDeck L i x = l := by
  apply Subtype.ext
  exact add_left_cancel ((pullbackCrossDeck_spec L i hx).trans hl.symm)

/-- The actual target-lattice difference is constant near every point of the overlap. -/
theorem pullbackCrossDeck_locally_constant (i : p.Torus × q.Torus) {x : p.Torus}
    (hx : x ∈ pullbackCrossBaseSet L i) :
    pullbackCrossDeck L i =ᶠ[𝓝 x] fun _ => pullbackCrossDeck L i x := by
  have hU : ∀ᶠ y in 𝓝 x, y ∈ pullbackCrossBaseSet L i :=
    (pullbackCrossBaseSet_isOpen L i).mem_nhds hx
  have he : (fun y => Core.lift q i.2 (L.torusMap y)) =ᶠ[𝓝 x]
      fun y => L.linear (Core.lift p i.1 y) + pullbackCrossDeck L i x := by
    apply eventuallyEq_of_localHomeomorph_comp_eq
      (DiscreteQuotient.quotient_localHomeomorph q.lattice)
      (((Core.lift q i.2).continuousAt hx.2).comp
        L.torusContinuousMap.continuous.continuousAt)
      ((L.linear.continuous.continuousAt.comp
        ((Core.lift p i.1).continuousAt hx.1)).add continuousAt_const)
      (pullbackCrossDeck_spec L i hx).symm
    filter_upwards [hU] with y hy
    change q.lattice.mkQ (Core.lift q i.2 (L.torusMap y)) =
      q.lattice.mkQ (L.linear (Core.lift p i.1 y) + pullbackCrossDeck L i x)
    rw [map_add, Core.mkQ_lattice, add_zero, ← L.torusMap_mkQ,
      Core.lift_project p i.1 hy.1, Core.lift_project q i.2 hy.2]
  filter_upwards [hU, he] with y hy hey
  exact pullbackCrossDeck_eq_of_add L i hy (pullbackCrossDeck L i x) hey.symm

/-- The exact cross-cover deck identity is an equality in the actual target lattice. -/
theorem pullbackCrossDeck_compatible (i j : p.Torus × q.Torus) {x : p.Torus}
    (hx : x ∈ pullbackCrossBaseSet L i ∩ pullbackCrossBaseSet L j) :
    Core.deck q i.2 j.2 (L.torusMap x) + pullbackCrossDeck L i x =
      pullbackCrossDeck L j x + L.latticeMap (Core.deck p i.1 j.1 x) := by
  apply Subtype.ext
  simp only [Submodule.coe_add, L.latticeMap_coe]
  rw [Core.deck_coe q i.2 j.2 ⟨hx.1.2, hx.2.2⟩,
    pullbackCrossDeck_coe L i hx.1, pullbackCrossDeck_coe L j hx.2,
    Core.deck_coe p i.1 j.1 ⟨hx.1.1, hx.2.1⟩, map_sub]
  abel

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

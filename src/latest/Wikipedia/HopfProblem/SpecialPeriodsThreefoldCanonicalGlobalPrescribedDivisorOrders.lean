import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalPrescribedDivisor

/-!
# Actual zero and pole coefficients of the prescribed tensor line

The tensor Cartier section is holomorphic on the entire complement of
the cusp fibre, including the elliptic central surface.  In the original
native bundle charts its transverse coefficient at that surface has
order exactly two.  The cusp defining chart is a valid bundle chart on
the entire original cusp patch.
-/

noncomputable section

open Set Filter Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalPrescribedDivisor

open Triangle TrianglePeriodFamily.Canonical
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace CuspGeometry.nativeChartedSpace
  specialEllipticPieceChartedSpace

local notation "IF" => modelWithCornersSelf ℂ Model

theorem projection_ne_other_puncture {i j : Threefold.Puncture} (hij : i ≠ j)
    {y : Threefold.Space} (hy : y ∈ (Threefold.liftedPatch (some i) : Set Threefold.Space)) :
    Threefold.projection y ≠ Threefold.puncturePoint j := by
  intro he
  have hm : Threefold.projection y ∈ specialBaseCover.fillingPatch i := hy
  rw [he] at hm
  exact hij ((specialBaseCover.point_mem_fillingPatch_iff j i).mp hm).symm

theorem fourPatch_projection_ne_infty {y : Threefold.Space}
    (hy : y ∈ GlobalEllipticDivisor.patch) :
    Threefold.projectionSphere y ≠ (∞ : RiemannSphere) := by
  intro hinf
  have hb : Threefold.projection y = Threefold.puncturePoint none :=
    triangleSphereUniformization.injective (hinf.trans triangleSphereUniformization_cusp.symm)
  exact projection_ne_other_puncture (i := some .four) (j := none) (by decide) hy hb

theorem cuspPatch_projection_ne_one {y : Threefold.Space}
    (hy : y ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space)) :
    Threefold.projectionSphere y ≠ ((1 : ℂ) : RiemannSphere) := by
  intro hone
  have hb : Threefold.projection y = Threefold.puncturePoint (some .four) :=
    triangleSphereUniformization.injective (hone.trans triangleSphereUniformization_centerTwo.symm)
  exact projection_ne_other_puncture (i := none) (j := some .four) (by decide) hy hb

/-- Both defining factors are valid on the full original cusp patch. -/
theorem cuspPatch_subset_baseSet :
    (Threefold.liftedPatch (some none) : Set Threefold.Space) ⊆
      cartier.transitions.baseSet (true, none) := by
  intro y hy
  exact ⟨GlobalBasePullback.cusp_projection_mem_infinityChart hy,
    (GlobalEllipticDivisor.mem_outside y).mpr (cuspPatch_projection_ne_one hy)⟩

/-- On every finite-base point, the actual tensor bundle coefficient
is exactly the actual effective-divisor section coefficient. -/
theorem finite_localCoefficient (i : GlobalEllipticDivisor.Index) {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    cartier.transitions.localCoefficient cartier.rawSection (false, i) x =
      GlobalEllipticDivisor.transitions.localCoefficient
        GlobalEllipticDivisor.canonicalSection i x := by
  have hfinite : Threefold.projectionSphere x ∈ finiteChart := (mem_finiteChart _).mpr hx
  have hbase : GlobalBasePullback.cartier.transitions.localCoefficient
      GlobalBasePullback.cartier.rawSection false x = 1 :=
    (GlobalBasePullback.cartier.rawSection_localCoefficient false hfinite hfinite).trans
      (GlobalBasePullback.localFraction_finite x)
  have hdiv : GlobalEllipticDivisor.cartierData.transitions.localCoefficient
      GlobalEllipticDivisor.cartierData.rawSection i x =
      GlobalEllipticDivisor.transitions.localCoefficient
        GlobalEllipticDivisor.canonicalSection i x :=
    congrArg (fun s : ∀ y, GlobalEllipticDivisor.divisorBundle.Fiber y =>
      GlobalEllipticDivisor.transitions.localCoefficient s i x)
      GlobalEllipticDivisor.cartierRawSection_eq
  calc
    _ = GlobalBasePullback.cartier.transitions.localCoefficient
          GlobalBasePullback.cartier.rawSection false x *
        GlobalEllipticDivisor.cartierData.transitions.localCoefficient
          GlobalEllipticDivisor.cartierData.rawSection i x :=
      GlobalBasePullback.cartier.tensor_rawSection_localCoefficient
        GlobalEllipticDivisor.cartierData (false, i) x
    _ = 1 * GlobalEllipticDivisor.transitions.localCoefficient
        GlobalEllipticDivisor.canonicalSection i x := congrArg₂ (fun a b : ℂ => a * b) hbase hdiv
    _ = _ := one_mul _

/-- The section extends holomorphically across the elliptic divisor in
the actual tensor bundle, rather than only on the generic set. -/
theorem rawSectionMap_holomorphicAt_of_finite {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    ContMDiffAt IF ((IF).prod 𝓘(ℂ)) ω cartier.rawSectionMap x := by
  let i := GlobalEllipticDivisor.transitions.indexAt x
  have hi : x ∈ GlobalEllipticDivisor.transitions.baseSet i :=
    GlobalEllipticDivisor.transitions.mem_baseSet_at x
  have hfinite : Threefold.projectionSphere x ∈ finiteChart := (mem_finiteChart _).mpr hx
  have htriv : cartier.rawSectionMap x ∈
      (cartier.associatedBundle.localTriv (false, i)).source := ⟨hfinite, hi⟩
  apply ((cartier.associatedBundle.localTriv (false, i)).contMDiffAt_iff htriv).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have hc := GlobalEllipticDivisor.transitions.localCoefficient_holomorphic IF
    GlobalEllipticDivisor.canonicalSection GlobalEllipticDivisor.canonicalSectionMap_holomorphic i
  have hca := hc.contMDiffAt
    ((GlobalEllipticDivisor.transitions.isOpen_baseSet i).mem_nhds hi)
  apply hca.congr_of_eventuallyEq
  have hN : {y : Threefold.Space | Threefold.projectionSphere y ≠ (∞ : RiemannSphere)} ∈ 𝓝 x :=
    GlobalCusp.outside.isOpen.mem_nhds hx
  filter_upwards [hN] with y hy
  exact finite_localCoefficient i hy

theorem rawSectionMap_holomorphicOn_outside_cusp :
    ContMDiffOn IF ((IF).prod 𝓘(ℂ)) ω cartier.rawSectionMap GlobalCusp.outside :=
  fun _ hx => (rawSectionMap_holomorphicAt_of_finite hx).contMDiffWithinAt

/-- The coefficient is taken in the actual tensor bundle chart along
the actual inverse-chart transverse line of the global manifold. -/
def transverseCoefficient (y : GlobalEllipticDivisor.patch) (z : ℂ) : ℂ :=
  cartier.transitions.localCoefficient cartier.rawSection
    (false, some (Sections.patchSectionChart .four y))
    (Sections.patchTransversePoint .four y z).val

theorem transverseCoefficient_eq (y : GlobalEllipticDivisor.patch) :
    transverseCoefficient y = GlobalEllipticDivisor.transverseCoefficient y := by
  funext z
  exact finite_localCoefficient (some (Sections.patchSectionChart .four y))
    (fourPatch_projection_ne_infty (Sections.patchTransversePoint .four y z).property)

theorem transverseCoefficient_analyticAt (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    AnalyticAt ℂ (transverseCoefficient y) 0 := by
  rw [transverseCoefficient_eq]
  exact GlobalEllipticDivisor.transverseCoefficient_analyticAt y hy

/-- The tensor section has the genuine square-times-unit factorization
at every point of the actual second elliptic fibre. -/
theorem transverseCoefficient_factorization (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    transverseCoefficient y =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ 2 * SectionsUnit.discExtension (SectionsUnit.specialUnit .four) z) := by
  rw [transverseCoefficient_eq]
  exact GlobalEllipticDivisor.transverseCoefficient_factorization y hy

theorem transverseCoefficient_order_two (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    analyticOrderAt (transverseCoefficient y) 0 = 2 := by
  rw [transverseCoefficient_eq]
  exact GlobalEllipticDivisor.transverseCoefficient_order_two y hy

theorem section_order_two_everywhere (x : Threefold.Space)
    (hx : x ∈ GlobalEllipticDivisor.support) :
    analyticOrderAt (transverseCoefficient
      ⟨x, GlobalEllipticDivisor.support_subset_patch hx⟩) 0 = 2 :=
  transverseCoefficient_order_two ⟨x, GlobalEllipticDivisor.support_subset_patch hx⟩ hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalPrescribedDivisor

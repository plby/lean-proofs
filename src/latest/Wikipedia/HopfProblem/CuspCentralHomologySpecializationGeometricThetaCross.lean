import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricThetaPaths
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossArcChains
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTwoChainConnecting
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology

/-!
# The actual connecting class of the theta-edge cross product

Splitting each literal oriented edge at its midpoint gives genuine chains
in the two open product cones. Their pole terms cancel for zero-sum edge
weights, leaving precisely the weighted midpoint belt cycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

/-- The northern half-edge product, with the fibre coordinate placed first. -/
def thetaNorthCrossMap (j : Fin 3) : C(unitInterval × CompactFibreTorus, thetaNorth) where
  toFun p := ⟨(p.2, thetaNorthEdgePath j p.1), thetaNorthEdgePath_mem j p.1⟩
  continuous_toFun := (continuous_snd.prodMk
    ((thetaNorthEdgePath j).continuous.comp continuous_fst)).subtype_mk _

/-- The southern half-edge product, with the fibre coordinate placed first. -/
def thetaSouthCrossMap (j : Fin 3) : C(unitInterval × CompactFibreTorus, thetaSouth) where
  toFun p := ⟨(p.2, thetaSouthEdgePath j p.1), thetaSouthEdgePath_mem j p.1⟩
  continuous_toFun := (continuous_snd.prodMk
    ((thetaSouthEdgePath j).continuous.comp continuous_fst)).subtype_mk _

private def northPoleSection : C(CompactFibreTorus, thetaNorth) :=
  (thetaNorthCrossMap 0).comp (crossInsertLeft (0 : unitInterval))

private def southPoleSection : C(CompactFibreTorus, thetaSouth) :=
  (thetaSouthCrossMap 0).comp (crossInsertLeft (1 : unitInterval))

private theorem thetaNorthCrossMap_source (j : Fin 3) :
    (thetaNorthCrossMap j).comp (crossInsertLeft (0 : unitInterval)) = northPoleSection := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (u, thetaNorthEdgePath j 0) = (u, thetaNorthEdgePath 0 0)
  simp only [Path.source]

private theorem thetaNorthCrossMap_target (j : Fin 3) :
    (thetaNorthCrossMap j).comp (crossInsertLeft (1 : unitInterval)) =
      (ContinuousMap.inclusion (Set.inter_subset_left : ThetaBelt ⊆ thetaNorth)).comp
        (thetaBeltSection j) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (u, thetaNorthEdgePath j 1) = (u, thetaMidpoint j)
  rw [Path.target]

private theorem thetaSouthCrossMap_source (j : Fin 3) :
    (thetaSouthCrossMap j).comp (crossInsertLeft (0 : unitInterval)) =
      (ContinuousMap.inclusion (Set.inter_subset_right : ThetaBelt ⊆ thetaSouth)).comp
        (thetaBeltSection j) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (u, thetaSouthEdgePath j 0) = (u, thetaMidpoint j)
  rw [Path.source]

private theorem thetaSouthCrossMap_target (j : Fin 3) :
    (thetaSouthCrossMap j).comp (crossInsertLeft (1 : unitInterval)) = southPoleSection := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (u, thetaSouthEdgePath j 1) = (u, thetaSouthEdgePath 0 1)
  simp only [Path.target]

/-- The actual two-chain obtained from a single northern half-edge. -/
def thetaNorthHalfCrossChain (j : Fin 3)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) : Chains thetaNorth 2 :=
  inducedChain (thetaNorthCrossMap j) 2
    (crossProductEdge unitInterval CompactFibreTorus 1 (pathChain Path.id) b.1)

/-- The actual two-chain obtained from a single southern half-edge. -/
def thetaSouthHalfCrossChain (j : Fin 3)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) : Chains thetaSouth 2 :=
  inducedChain (thetaSouthCrossMap j) 2
    (crossProductEdge unitInterval CompactFibreTorus 1 (pathChain Path.id) b.1)

theorem thetaNorthHalfCrossChain_boundary (j : Fin 3)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ((singularComplex thetaNorth).d 2 1).hom (thetaNorthHalfCrossChain j b) =
      inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : ThetaBelt ⊆ thetaNorth)) 1
        (inducedChain (thetaBeltSection j) 1 b.1) - inducedChain northPoleSection 1 b.1 := by
  rw [thetaNorthHalfCrossChain, ← inducedChain_boundary, crossProductEdge_path_boundary,
    map_sub]
  have ht := congrArg (fun f => inducedChain f 1 b.1) (thetaNorthCrossMap_target j)
  have hs := congrArg (fun f => inducedChain f 1 b.1) (thetaNorthCrossMap_source j)
  simp only [inducedChain_comp, LinearMap.comp_apply] at ht hs
  rw [ht, hs]

theorem thetaSouthHalfCrossChain_boundary (j : Fin 3)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ((singularComplex thetaSouth).d 2 1).hom (thetaSouthHalfCrossChain j b) =
      inducedChain southPoleSection 1 b.1 -
        inducedChain (ContinuousMap.inclusion
          (Set.inter_subset_right : ThetaBelt ⊆ thetaSouth)) 1
          (inducedChain (thetaBeltSection j) 1 b.1) := by
  rw [thetaSouthHalfCrossChain, ← inducedChain_boundary, crossProductEdge_path_boundary,
    map_sub]
  have ht := congrArg (fun f => inducedChain f 1 b.1) (thetaSouthCrossMap_target j)
  have hs := congrArg (fun f => inducedChain f 1 b.1) (thetaSouthCrossMap_source j)
  simp only [inducedChain_comp, LinearMap.comp_apply] at ht hs
  rw [ht, hs]

private theorem zero_sum_zsmul {M : Type} [AddCommGroup M]
    (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) (x : M) : (∑ j, m j • x) = 0 := by
  let f : ℤ →+ M :=
    { toFun := fun n => n • x
      map_zero' := zero_zsmul x
      map_add' := fun a b => add_zsmul x a b }
  change ∑ j, f (m j) = 0
  rw [← map_sum, hm, map_zero]

/-- The weighted actual midpoint-section cycle. -/
def thetaWeightedBeltCycle (m : Fin 3 → ℤ)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ModuleHomology.Cycle (singularComplex ThetaBelt) 1 :=
  ∑ j, m j • ModuleHomology.mapCycles (singularChainMap (thetaBeltSection j)) 1 b

@[simp] theorem thetaWeightedBeltCycle_val (m : Fin 3 → ℤ)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    (thetaWeightedBeltCycle m b).1 = ∑ j, m j • inducedChain (thetaBeltSection j) 1 b.1 := by
  simp only [thetaWeightedBeltCycle, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (ModuleHomology.Cycle (singularComplex ThetaBelt) 1).subtype
    (m j • ModuleHomology.mapCycles (singularChainMap (thetaBeltSection j)) 1 b) = _
  rw [map_zsmul]
  exact congrArg (fun x => m j • x)
    (ModuleHomology.mapCycles_val (singularChainMap (thetaBeltSection j)) 1 b)

theorem thetaWeightedBeltCycle_class (m : Fin 3 → ℤ)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ModuleHomology.cycleClass (singularComplex ThetaBelt) 1 (thetaWeightedBeltCycle m b) =
      thetaBeltSum (fun j => m j •
        ModuleHomology.cycleClass (singularComplex CompactFibreTorus) 1 b) := by
  simp only [thetaWeightedBeltCycle, thetaBeltSum, map_sum, map_zsmul,
    ← ModuleHomology.homologyMap_cycleClass]

/-- The zero-sum weighted northern half-products. -/
def thetaNorthCrossChain (m : Fin 3 → ℤ)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) : Chains thetaNorth 2 :=
  ∑ j, m j • thetaNorthHalfCrossChain j b

/-- The zero-sum weighted southern half-products. -/
def thetaSouthCrossChain (m : Fin 3 → ℤ)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) : Chains thetaSouth 2 :=
  ∑ j, m j • thetaSouthHalfCrossChain j b

theorem thetaNorthCrossChain_boundary (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ((singularComplex thetaNorth).d 2 1).hom (thetaNorthCrossChain m b) =
      inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : ThetaBelt ⊆ thetaNorth)) 1
        (thetaWeightedBeltCycle m b).1 := by
  simp only [thetaNorthCrossChain, thetaWeightedBeltCycle_val, map_sum, map_zsmul,
    thetaNorthHalfCrossChain_boundary, zsmul_sub, Finset.sum_sub_distrib]
  rw [zero_sum_zsmul m hm, sub_zero]

theorem thetaSouthCrossChain_boundary (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ((singularComplex thetaSouth).d 2 1).hom (thetaSouthCrossChain m b) =
      -inducedChain (ContinuousMap.inclusion
        (Set.inter_subset_right : ThetaBelt ⊆ thetaSouth)) 1
        (thetaWeightedBeltCycle m b).1 := by
  simp only [thetaSouthCrossChain, thetaWeightedBeltCycle_val, map_sum, map_zsmul,
    thetaSouthHalfCrossChain_boundary, zsmul_sub, Finset.sum_sub_distrib]
  rw [zero_sum_zsmul m hm, zero_sub]

private theorem inducedChain_path_id {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : inducedChain p.toContinuousMap 1 (pathChain Path.id) = pathChain p := by
  rw [pathChain, inducedChain_simplex]
  rfl

theorem thetaNorthHalfCrossChain_inclusion (j : Fin 3)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    inducedChain (subtypeInclusion thetaNorth) 2 (thetaNorthHalfCrossChain j b) =
      inducedChain (Homeomorph.prodComm Theta CompactFibreTorus :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2
        (crossProductEdge Theta CompactFibreTorus 1 (pathChain (thetaNorthEdgePath j)) b.1) := by
  have hcomp : (subtypeInclusion thetaNorth).comp (thetaNorthCrossMap j) =
      (Homeomorph.prodComm Theta CompactFibreTorus :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)).comp
        ((thetaNorthEdgePath j).toContinuousMap.prodMap (ContinuousMap.id CompactFibreTorus)) := rfl
  rw [thetaNorthHalfCrossChain, ← LinearMap.comp_apply, ← inducedChain_comp, hcomp,
    inducedChain_comp, LinearMap.comp_apply, crossProductEdge_natural,
    inducedChain_path_id, inducedChain_id, LinearMap.id_apply]

theorem thetaSouthHalfCrossChain_inclusion (j : Fin 3)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    inducedChain (subtypeInclusion thetaSouth) 2 (thetaSouthHalfCrossChain j b) =
      inducedChain (Homeomorph.prodComm Theta CompactFibreTorus :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2
        (crossProductEdge Theta CompactFibreTorus 1 (pathChain (thetaSouthEdgePath j)) b.1) := by
  have hcomp : (subtypeInclusion thetaSouth).comp (thetaSouthCrossMap j) =
      (Homeomorph.prodComm Theta CompactFibreTorus :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)).comp
        ((thetaSouthEdgePath j).toContinuousMap.prodMap (ContinuousMap.id CompactFibreTorus)) := by
    rfl
  rw [thetaSouthHalfCrossChain, ← LinearMap.comp_apply, ← inducedChain_comp, hcomp,
    inducedChain_comp, LinearMap.comp_apply, crossProductEdge_natural,
    inducedChain_path_id, inducedChain_id, LinearMap.id_apply]

private theorem thetaSplitCrossChain_expansion (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    crossProductEdge Theta CompactFibreTorus 1 (thetaSplitEdgeCycle m hm).1 b.1 =
      (∑ j, m j • crossProductEdge Theta CompactFibreTorus 1
        (pathChain (thetaNorthEdgePath j)) b.1) +
      ∑ j, m j • crossProductEdge Theta CompactFibreTorus 1
        (pathChain (thetaSouthEdgePath j)) b.1 := by
  let f : Chains Theta 1 →+ Chains (Theta × CompactFibreTorus) 2 :=
    { toFun := fun c => crossProductEdge Theta CompactFibreTorus 1 c b.1
      map_zero' := by rw [map_zero, LinearMap.zero_apply]
      map_add' := fun c d => by rw [map_add, LinearMap.add_apply] }
  change f (∑ j, m j • (pathChain (thetaNorthEdgePath j) +
    pathChain (thetaSouthEdgePath j))) =
      (∑ j, m j • f (pathChain (thetaNorthEdgePath j))) +
      ∑ j, m j • f (pathChain (thetaSouthEdgePath j))
  simp only [map_sum, map_zsmul, map_add, zsmul_add, Finset.sum_add_distrib]

/-- The actual small cycle obtained by gluing the two half-edge cross-chain sums. -/
def thetaCrossSmallCycle (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ModuleHomology.Cycle (smallComplex thetaNorth thetaSouth) 2 :=
  twoChainSmallCycle thetaNorth thetaSouth 1
    (thetaNorthCrossChain m b) (thetaSouthCrossChain m b) (thetaWeightedBeltCycle m b)
    (thetaNorthCrossChain_boundary m hm b) (thetaSouthCrossChain_boundary m hm b)

/-- Its ambient chain is the swapped cross product with the subdivided literal edge cycle. -/
theorem thetaCrossSmallCycle_ambient_val (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    (ModuleHomology.mapCycles (smallInclusion thetaNorth thetaSouth) 2
      (thetaCrossSmallCycle m hm b)).1 =
      inducedChain (ContinuousMap.prodSwap :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2
        (crossProductEdge Theta CompactFibreTorus 1 (thetaSplitEdgeCycle m hm).1 b.1) := by
  rw [thetaCrossSmallCycle, twoChainSmallCycle_ambient_val]
  change inducedChain (subtypeInclusion thetaNorth) 2 (thetaNorthCrossChain m b) +
    inducedChain (subtypeInclusion thetaSouth) 2 (thetaSouthCrossChain m b) = _
  simp only [thetaNorthCrossChain, thetaSouthCrossChain, map_sum, map_zsmul,
    thetaNorthHalfCrossChain_inclusion, thetaSouthHalfCrossChain_inclusion]
  have h := congrArg (inducedChain (Homeomorph.prodComm Theta CompactFibreTorus :
      C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2)
    (thetaSplitCrossChain_expansion m hm b)
  have hswap : (Homeomorph.prodComm Theta CompactFibreTorus :
      C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) = ContinuousMap.prodSwap := by
    ext p <;> rfl
  simpa only [hswap, map_add, map_sum, map_zsmul] using h.symm

/-- The actual glued cycle equals the functorial swap of the actual cycle cross product. -/
theorem thetaCrossSmallCycle_ambient_eq (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ModuleHomology.mapCycles (smallInclusion thetaNorth thetaSouth) 2
        (thetaCrossSmallCycle m hm b) =
      ModuleHomology.mapCycles (singularChainMap (ContinuousMap.prodSwap :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta))) 2
        (crossProductCycles Theta CompactFibreTorus 1 (thetaSplitEdgeCycle m hm) b) := by
  apply Subtype.ext
  exact (thetaCrossSmallCycle_ambient_val m hm b).trans
    (ModuleHomology.mapCycles_val (singularChainMap (ContinuousMap.prodSwap :
      C(Theta × CompactFibreTorus, CompactFibreTorus × Theta))) 2
      (crossProductCycles Theta CompactFibreTorus 1 (thetaSplitEdgeCycle m hm) b)).symm

/-- The glued representative gives the original, unsplit edge cross-product class. -/
theorem thetaCrossSmallCycle_ambient_class (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (b : ModuleHomology.Cycle (singularComplex CompactFibreTorus) 1) :
    ModuleHomology.cycleClass (singularComplex (CompactFibreTorus × Theta)) 2
        (ModuleHomology.mapCycles (smallInclusion thetaNorth thetaSouth) 2
          (thetaCrossSmallCycle m hm b)) =
      singularHomologyMap (ContinuousMap.prodSwap :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2
        (crossProductHomology Theta CompactFibreTorus 1 (thetaEdgeHomology m hm)
          (ModuleHomology.cycleClass (singularComplex CompactFibreTorus) 1 b)) := by
  rw [thetaCrossSmallCycle_ambient_eq, ← ModuleHomology.homologyMap_cycleClass]
  have hsplit : ModuleHomology.cycleClass (singularComplex Theta) 1
      (thetaSplitEdgeCycle m hm) = thetaEdgeHomology m hm := thetaSplitEdgeCycle_class m hm
  have hprod := crossProductHomology_cycleClass Theta CompactFibreTorus 1
    (thetaSplitEdgeCycle m hm) b
  have hc := hprod.symm.trans (congrArg (fun c => crossProductHomology
    Theta CompactFibreTorus 1 c
    (ModuleHomology.cycleClass (singularComplex CompactFibreTorus) 1 b)) hsplit)
  exact congrArg (singularHomologyMap (ContinuousMap.prodSwap :
    C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2) hc

/-- The genuine Mayer--Vietoris connecting homomorphism evaluates the swapped
theta-edge cross product as the weighted actual midpoint belt class. -/
theorem thetaEdgeCross_connecting (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0)
    (a : SingularHomology CompactFibreTorus 1) :
    connectingHomomorphism thetaNorth thetaSouth thetaNorth_isOpen thetaSouth_isOpen
      theta_open_cover 1
      (singularHomologyMap (ContinuousMap.prodSwap :
        C(Theta × CompactFibreTorus, CompactFibreTorus × Theta)) 2
        (crossProductHomology Theta CompactFibreTorus 1 (thetaEdgeHomology m hm) a)) =
      thetaBeltSum (fun j => m j • a) := by
  obtain ⟨b, rfl⟩ := ModuleHomology.cycleClass_surjective
    (singularComplex CompactFibreTorus) 1 a
  rw [← thetaCrossSmallCycle_ambient_class]
  exact (connectingHomomorphism_twoChain thetaNorth thetaSouth
    thetaNorth_isOpen thetaSouth_isOpen theta_open_cover 1
    (thetaNorthCrossChain m b) (thetaSouthCrossChain m b) (thetaWeightedBeltCycle m b)
    (thetaNorthCrossChain_boundary m hm b) (thetaSouthCrossChain_boundary m hm b)).trans
    (thetaWeightedBeltCycle_class m b)

end Wikipedia.HopfProblem.CuspCentralHomology

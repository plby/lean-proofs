import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseSource
import Wikipedia.HopfProblem.FirstHurewiczMap

/-!
# Literal oriented theta edges and their integral singular cycles

The three paths traverse the actual suspension edges from north to south.
A zero-sum integral weighting cancels their common endpoint boundaries.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris

/-- The actual north-to-south path on the indicated suspension edge. -/
def thetaEdgePath (j : Fin 3) :
    Path (Suspension.north : Theta) Suspension.south where
  toFun t := Suspension.mk t j
  continuous_toFun := Suspension.continuous_mk.comp (continuous_id.prodMk continuous_const)
  source' := Suspension.mk_zero j
  target' := Suspension.mk_one j

@[simp] theorem thetaEdgePath_apply (j : Fin 3) (t : unitInterval) :
    thetaEdgePath j t = Suspension.mk t j := rfl

/-- The common endpoints cancel for every zero-sum integral edge weighting. -/
theorem thetaEdgeChain_boundary (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    boundaryOne Theta (∑ j, m j • pathChain (thetaEdgePath j)) = 0 := by
  simp only [map_sum, map_zsmul, boundaryOne_pathChain]
  let d := pointChain (Suspension.south : Theta) - pointChain (Suspension.north : Theta)
  let f : ℤ →+ Chains Theta 0 :=
    { toFun := fun n => n • d
      map_zero' := zero_zsmul d
      map_add' := fun a b => add_zsmul d a b }
  change ∑ j, f (m j) = 0
  rw [← map_sum, hm, map_zero]

/-- The literal weighted sum of the three actual singular edge chains. -/
def thetaEdgeCycle (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) : Cycles1 Theta :=
  mkCycle1 Theta (∑ j, m j • pathChain (thetaEdgePath j)) (thetaEdgeChain_boundary m hm)

@[simp] theorem thetaEdgeCycle_val (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    (thetaEdgeCycle m hm).1 = ∑ j, m j • pathChain (thetaEdgePath j) := rfl

/-- The actual first singular homology class of the weighted theta edges. -/
def thetaEdgeHomology (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    SingularHomology Theta 1 :=
  FirstHurewicz.cycleClass Theta (thetaEdgeCycle m hm)

/-- The actual cycle representative also uses the general-degree cycle API. -/
theorem thetaEdgeHomology_cycleClass (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    thetaEdgeHomology m hm =
      ModuleHomology.cycleClass (FirstHurewicz.singularComplex Theta) 1
        (thetaEdgeCycle m hm) := rfl

/-- The literal path classes compute the image in chains modulo boundaries. -/
theorem thetaEdgeHomology_chainClass (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    FirstHurewicz.homologyToChainClass Theta (thetaEdgeHomology m hm) =
      ∑ j, m j • FirstHurewicz.pathClass (thetaEdgePath j) := by
  rw [thetaEdgeHomology, FirstHurewicz.homologyToChainClass_cycleClass,
    thetaEdgeCycle_val]
  simp only [map_sum, map_zsmul, pathClass]

/-- The literal height-one-half point on an edge. -/
def thetaMidpoint (j : Fin 3) : Theta := Suspension.mk ⟨1 / 2, by norm_num⟩ j

/-- The northern half of a literal edge, with its affine parametrization. -/
def thetaNorthEdgePath (j : Fin 3) :
    Path (Suspension.north : Theta) (thetaMidpoint j) where
  toFun t := Suspension.mk ⟨(t : ℝ) / 2, by
    constructor <;> linarith [t.2.1, t.2.2]⟩ j
  continuous_toFun := Suspension.continuous_mk.comp
    (((continuous_subtype_val.div_const 2).subtype_mk _).prodMk continuous_const)
  source' := by simp
  target' := rfl

/-- The southern half of a literal edge, with its affine parametrization. -/
def thetaSouthEdgePath (j : Fin 3) :
    Path (thetaMidpoint j) (Suspension.south : Theta) where
  toFun t := Suspension.mk ⟨(1 + (t : ℝ)) / 2, by
    constructor <;> linarith [t.2.1, t.2.2]⟩ j
  continuous_toFun := Suspension.continuous_mk.comp
    ((((continuous_const.add continuous_subtype_val).div_const 2).subtype_mk _).prodMk
      continuous_const)
  source' := by simp [thetaMidpoint]
  target' := by simp

@[simp] theorem thetaNorthEdgePath_apply (j : Fin 3) (t : unitInterval) :
    thetaNorthEdgePath j t = Suspension.mk ⟨(t : ℝ) / 2, by
      constructor <;> linarith [t.2.1, t.2.2]⟩ j := rfl

@[simp] theorem thetaSouthEdgePath_apply (j : Fin 3) (t : unitInterval) :
    thetaSouthEdgePath j t = Suspension.mk ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> linarith [t.2.1, t.2.2]⟩ j := rfl

/-- The northern half lies in the actual northern open cone. -/
theorem thetaNorthEdgePath_mem (j : Fin 3) (t : unitInterval) :
    thetaNorthEdgePath j t ∈ (Suspension.northOpen : Set Theta) := by
  change (t : ℝ) / 2 < 3 / 4
  linarith [t.2.2]

/-- The southern half lies in the actual southern open cone. -/
theorem thetaSouthEdgePath_mem (j : Fin 3) (t : unitInterval) :
    thetaSouthEdgePath j t ∈ (Suspension.southOpen : Set Theta) := by
  change 1 / 4 < (1 + (t : ℝ)) / 2
  linarith [t.2.1]

/-- The two affine half paths concatenate to the exact original path. -/
theorem thetaEdgePath_split (j : Fin 3) :
    (thetaNorthEdgePath j).trans (thetaSouthEdgePath j) = thetaEdgePath j := by
  apply Path.ext
  funext t
  rw [Path.trans_apply]
  split_ifs <;> simp only [thetaNorthEdgePath_apply, thetaSouthEdgePath_apply,
    thetaEdgePath_apply]
  · congr 1
    apply Subtype.ext
    dsimp
    ring
  · congr 1
    apply Subtype.ext
    dsimp
    ring

/-- Splitting each edge preserves its endpoint boundary. -/
theorem thetaSplitEdgeChain_boundary (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    boundaryOne Theta (∑ j, m j •
      (pathChain (thetaNorthEdgePath j) + pathChain (thetaSouthEdgePath j))) = 0 := by
  have h (j : Fin 3) : boundaryOne Theta
      (pathChain (thetaNorthEdgePath j) + pathChain (thetaSouthEdgePath j)) =
        boundaryOne Theta (pathChain (thetaEdgePath j)) := by
    rw [map_add, boundaryOne_pathChain, boundaryOne_pathChain, boundaryOne_pathChain]
    abel
  simp only [map_sum, map_zsmul, h]
  simpa only [map_sum, map_zsmul] using thetaEdgeChain_boundary m hm

/-- The actual cycle obtained by subdividing every edge at height one half. -/
def thetaSplitEdgeCycle (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) : Cycles1 Theta :=
  mkCycle1 Theta (∑ j, m j •
    (pathChain (thetaNorthEdgePath j) + pathChain (thetaSouthEdgePath j)))
    (thetaSplitEdgeChain_boundary m hm)

@[simp] theorem thetaSplitEdgeCycle_val (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    (thetaSplitEdgeCycle m hm).1 = ∑ j, m j •
      (pathChain (thetaNorthEdgePath j) + pathChain (thetaSouthEdgePath j)) := rfl

/-- The split and unsplit literal edge cycles define the same actual class. -/
theorem thetaSplitEdgeCycle_class (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    FirstHurewicz.cycleClass Theta (thetaSplitEdgeCycle m hm) =
      thetaEdgeHomology m hm := by
  apply FirstHurewicz.homologyToChainClass_injective Theta
  rw [FirstHurewicz.homologyToChainClass_cycleClass, thetaSplitEdgeCycle_val,
    thetaEdgeHomology_chainClass]
  simp only [map_sum, map_zsmul, map_add]
  change (∑ j, m j • (pathClass (thetaNorthEdgePath j) +
    pathClass (thetaSouthEdgePath j))) = ∑ j, m j • pathClass (thetaEdgePath j)
  simp only [← pathClass_trans, thetaEdgePath_split]

end Wikipedia.HopfProblem.CuspCentralHomology

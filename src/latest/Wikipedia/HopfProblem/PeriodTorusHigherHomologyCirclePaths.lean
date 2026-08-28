import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProductCover
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePathsTranslation

/-!
# The positively oriented circle loop in the two-arc cover

The two paths are actual paths in the open arc subtypes. Their lifts run
from one quarter to three quarters and then to five quarters. The common
endpoints lie in the specified components of the actual intersection.
Their concatenation is the positive one-turn circle loop based at one
quarter, and its chain differs from the sum of the two arc chains by the
boundary of the actual concatenation simplex.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CirclePaths

open CircleTopology FirstHurewicz

/-- A point in the left component of the actual arc intersection. -/
def quarterIntersection : ↥(arcU ∩ arcV) :=
  intersectionHomeomorph.symm (Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩)

/-- A point in the right component of the actual arc intersection. -/
def threeQuarterIntersection : ↥(arcU ∩ arcV) :=
  intersectionHomeomorph.symm (Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩)

def quarterPoint : Circle := quarterIntersection.val

def threeQuarterPoint : Circle := threeQuarterIntersection.val

@[simp] theorem quarterPoint_coe : quarterPoint = ((1 / 4 : ℝ) : Circle) := rfl

@[simp] theorem threeQuarterPoint_coe : threeQuarterPoint = ((3 / 4 : ℝ) : Circle) := rfl

@[simp] theorem quarterIntersection_component :
    intersectionHomeomorph quarterIntersection =
      Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩ :=
  intersectionHomeomorph.apply_symm_apply _

@[simp] theorem threeQuarterIntersection_component :
    intersectionHomeomorph threeQuarterIntersection =
      Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩ :=
  intersectionHomeomorph.apply_symm_apply _

def quarterU : arcU := ⟨quarterPoint, quarterIntersection.property.1⟩

def quarterV : arcV := ⟨quarterPoint, quarterIntersection.property.2⟩

def threeQuarterU : arcU := ⟨threeQuarterPoint, threeQuarterIntersection.property.1⟩

def threeQuarterV : arcV := ⟨threeQuarterPoint, threeQuarterIntersection.property.2⟩

/-- The first positive half-turn lies entirely in the first open arc. -/
def uPath : Path quarterU threeQuarterU where
  toFun t := arcUHomeomorph.symm
    ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by
      have ht := t.property
      constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun := arcUHomeomorph.symm.continuous.comp
    ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
      (fun t => by
        change (1 / 4 : ℝ) + (t : ℝ) / 2 ∈ Ioo (0 : ℝ) 1
        constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change (((1 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) : Circle) =
      ((1 / 4 : ℝ) : Circle)
    norm_num
  target' := by
    apply Subtype.ext
    change (((1 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) : Circle) =
      ((3 / 4 : ℝ) : Circle)
    norm_num

/-- The second positive half-turn has a lift from three quarters to
five quarters, wholly inside the second arc chart. -/
def vPath : Path threeQuarterV quarterV where
  toFun t := arcVHomeomorph.symm
    ⟨(3 / 4 : ℝ) + (t : ℝ) / 2, by
      have ht := t.property
      constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun := arcVHomeomorph.symm.continuous.comp
    ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
      (fun t => by
        change (3 / 4 : ℝ) + (t : ℝ) / 2 ∈ Ioo (1 / 2 : ℝ) (3 / 2)
        constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change (((3 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) : Circle) =
      ((3 / 4 : ℝ) : Circle)
    norm_num
  target' := by
    apply Subtype.ext
    change (((3 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) : Circle) =
      ((1 / 4 : ℝ) : Circle)
    convert AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ) using 1
    norm_num

@[simp] theorem uPath_apply (t : unitInterval) :
    (uPath t : Circle) = (((1 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : Circle) := rfl

@[simp] theorem vPath_apply (t : unitInterval) :
    (vPath t : Circle) = (((3 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : Circle) := rfl

/-- The first arc path regarded as a path in the actual circle. -/
def uCirclePath : Path quarterPoint threeQuarterPoint := uPath.map continuous_subtype_val

/-- The second arc path regarded as a path in the actual circle. -/
def vCirclePath : Path threeQuarterPoint quarterPoint := vPath.map continuous_subtype_val

@[simp] theorem uCirclePath_apply (t : unitInterval) :
    uCirclePath t = (((1 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : Circle) := rfl

@[simp] theorem vCirclePath_apply (t : unitInterval) :
    vCirclePath t = (((3 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : Circle) := rfl

/-- The literal positive one-turn circle loop at one quarter. -/
def quarterLoop : Path quarterPoint quarterPoint where
  toFun t := (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : Circle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_const.add continuous_subtype_val)
  source' := by change (((1 / 4 : ℝ) + (0 : unitInterval) : ℝ) : Circle) = _; simp
  target' := AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ)

@[simp] theorem quarterLoop_apply (t : unitInterval) :
    quarterLoop t = (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : Circle) := rfl

/-- With the standard concatenation parametrization the two half-turns
give exactly, rather than merely up to homotopy, the positive full turn. -/
theorem uCirclePath_trans_vCirclePath : uCirclePath.trans vCirclePath = quarterLoop := by
  apply Path.ext
  funext t
  rw [Path.trans_apply]
  split_ifs <;> simp only [uCirclePath_apply, vCirclePath_apply, quarterLoop_apply]
  · congr 1
    ring
  · congr 1
    ring

/-- The positive unit-period loop based at zero. -/
def positiveLoop : Path (0 : Circle) 0 where
  toFun t := ((t : ℝ) : Circle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := AddCircle.coe_zero (1 : ℝ)
  target' := AddCircle.coe_period (1 : ℝ)

@[simp] theorem positiveLoop_apply (t : unitInterval) :
    positiveLoop t = ((t : ℝ) : Circle) := rfl

@[simp] theorem quarterTranslation_zero :
    circleTranslation (1 / 4) (0 : Circle) = quarterPoint := by
  simp only [circleTranslation_apply, add_zero, quarterPoint_coe]

/-- The quarter-based positive loop is the actual translated zero-based loop. -/
theorem quarterLoop_eq_translation :
    quarterLoop = (positiveLoop.map (circleTranslation (1 / 4)).continuous).cast
      quarterTranslation_zero.symm quarterTranslation_zero.symm := by
  apply Path.ext
  funext t
  change (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : Circle) =
    ((1 / 4 : ℝ) : Circle) + ((t : ℝ) : Circle)
  exact AddCircle.coe_add (1 : ℝ) (1 / 4 : ℝ) (t : ℝ)

/-- The two choices of basepoint give the same genuine positive singular class. -/
theorem quarterLoop_homologyClass :
    loopHomologyClass quarterLoop = loopHomologyClass positiveLoop := by
  have hc : loopHomologyClass quarterLoop =
      loopHomologyClass (positiveLoop.map (circleTranslation (1 / 4)).continuous) := by
    apply homologyToChainClass_injective Circle
    rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass,
      quarterLoop_eq_translation, pathClass_cast]
  exact hc.trans (loopHomologyClass_map_circleTranslation (1 / 4) positiveLoop)

/-- Evaluation identifies the marked one-coordinate torus loop with
the same actual positive circle loop. -/
theorem coordinatePeriodLoop_one_eval :
    (coordinatePeriodLoop 1 ![1]).map (continuous_apply (0 : Fin 1)) = positiveLoop := by
  apply Path.ext
  funext t
  simp only [Path.map_coe, Function.comp_apply, coordinatePeriodLoop_apply,
    Matrix.cons_val_zero, Int.cast_one, mul_one]
  rfl

/-- The sign of the actual concatenation boundary in the arc cover. -/
theorem boundaryTwo_arcConcat :
    boundaryTwo Circle (concatChain uCirclePath vCirclePath) =
      pathChain uCirclePath + pathChain vCirclePath - pathChain quarterLoop := by
  rw [boundaryTwo_concatChain, uCirclePath_trans_vCirclePath]
  abel

/-- The sum of the two actual arc chains is a singular cycle. -/
theorem boundaryOne_arcSum :
    boundaryOne Circle (pathChain uCirclePath + pathChain vCirclePath) = 0 := by
  rw [map_add, boundaryOne_pathChain, boundaryOne_pathChain]
  abel

/-- The actual arc-chain cycle, not a postulated homology representative. -/
def arcSumCycle : Cycles1 Circle :=
  mkCycle1 Circle (pathChain uCirclePath + pathChain vCirclePath) boundaryOne_arcSum

/-- The two arc chains and the literal positive quarter-based loop
represent the same genuine singular homology class. -/
theorem arcSumCycle_class : cycleClass Circle arcSumCycle = loopHomologyClass quarterLoop := by
  apply homologyToChainClass_injective Circle
  rw [homologyToChainClass_cycleClass, homologyToChainClass_loopHomologyClass]
  change chainClass Circle (pathChain uCirclePath + pathChain vCirclePath) = _
  rw [map_add, ← uCirclePath_trans_vCirclePath, pathClass_trans]
  rfl

/-- The sum of the two oriented arc chains represents the marked positive generator. -/
theorem arcSumCycle_positiveLoop_class :
    cycleClass Circle arcSumCycle = loopHomologyClass positiveLoop :=
  arcSumCycle_class.trans quarterLoop_homologyClass

/-- The arc sum agrees with the positive standard one-coordinate torus loop
after the actual continuous coordinate evaluation map. -/
theorem arcSumCycle_coordinatePeriodLoop_class :
    cycleClass Circle arcSumCycle = inducedHomology
      ⟨fun x : ProductTorus 1 => x 0, continuous_apply 0⟩
      (loopHomologyClass (coordinatePeriodLoop 1 ![1])) := by
  rw [inducedHomology_loopHomologyClass, coordinatePeriodLoop_one_eval]
  exact arcSumCycle_positiveLoop_class

section Product

variable (X : Type*) [TopologicalSpace X]

/-- The left intersection point as an actual section over any space. -/
def quarterIntersectionSection : C(X, ↥(productU X ∩ productV X)) :=
  ⟨fun x => ⟨(quarterPoint, x), quarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

/-- The right intersection point as an actual section over any space. -/
def threeQuarterIntersectionSection : C(X, ↥(productU X ∩ productV X)) :=
  ⟨fun x => ⟨(threeQuarterPoint, x), threeQuarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

/-- The quarter point is in the first, not the second, intersection component. -/
@[simp] theorem quarterIntersectionSection_component (x : X) :
    productIntersectionHomotopyEquiv X (quarterIntersectionSection X x) = Sum.inl x := by
  change Sum.map (fun t : Ioo (0 : ℝ) (1 / 2) × X => t.2)
    (fun t : Ioo (1 / 2 : ℝ) 1 × X => t.2)
    (Homeomorph.sumProdDistrib (intersectionHomeomorph quarterIntersection, x)) = _
  rw [quarterIntersection_component]
  rfl

/-- The forward intersection equivalence carries the whole quarter section
to the first summand inclusion, as an equality of actual continuous maps. -/
theorem quarterIntersectionSection_comp :
    (productIntersectionHomotopyEquiv X).toFun.comp (quarterIntersectionSection X) =
      ⟨Sum.inl, continuous_inl⟩ := by
  apply ContinuousMap.ext
  intro x
  exact quarterIntersectionSection_component X x

/-- The three-quarter point is in the second intersection component. -/
@[simp] theorem threeQuarterIntersectionSection_component (x : X) :
    productIntersectionHomotopyEquiv X (threeQuarterIntersectionSection X x) = Sum.inr x := by
  change Sum.map (fun t : Ioo (0 : ℝ) (1 / 2) × X => t.2)
    (fun t : Ioo (1 / 2 : ℝ) 1 × X => t.2)
    (Homeomorph.sumProdDistrib (intersectionHomeomorph threeQuarterIntersection, x)) = _
  rw [threeQuarterIntersection_component]
  rfl

/-- The three-quarter section is the actual second summand inclusion in
the same fixed intersection equivalence. -/
theorem threeQuarterIntersectionSection_comp :
    (productIntersectionHomotopyEquiv X).toFun.comp (threeQuarterIntersectionSection X) =
      ⟨Sum.inr, continuous_inr⟩ := by
  apply ContinuousMap.ext
  intro x
  exact threeQuarterIntersectionSection_component X x

end Product

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CirclePaths

import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySlits

/-!
# Actual covering lifts of the two slit domains

Each slit domain is simply connected and locally path connected. The
proved regular covering therefore gives a unique continuous lift with
any prescribed actual lift of the common basepoint. On each of the three
connected overlap components the two lifts differ by one actual constant
triangle-group element. The middle transition is the identity.

The base lift is kept explicit so the geometric meridian construction can
select its normalized half-triangle lift without any conjugating path.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle

/-- The literal inclusion of the upper slit into the regular quotient. -/
def upperBaseInclusion : C(upperBase, TriangleRegularQuotient) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The literal inclusion of the lower slit into the regular quotient. -/
def lowerBaseInclusion : C(lowerBase, TriangleRegularQuotient) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem upperLift_existsUnique (b : SlitBaseLift) :
    ∃! s : C(upperBase, TriangleRegularPoint),
      s upperBasePoint = b.val ∧ triangleRegularProject ∘ s = upperBaseInclusion :=
  triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    upperBaseInclusion upperBasePoint b.val b.property

theorem lowerLift_existsUnique (b : SlitBaseLift) :
    ∃! s : C(lowerBase, TriangleRegularPoint),
      s lowerBasePoint = b.val ∧ triangleRegularProject ∘ s = lowerBaseInclusion :=
  triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
    lowerBaseInclusion lowerBasePoint b.val b.property

/-- The unique actual upper-slit lift with the specified starting point. -/
def upperLift (b : SlitBaseLift) : C(upperBase, TriangleRegularPoint) :=
  (upperLift_existsUnique b).choose

/-- The unique actual lower-slit lift with the same specified starting point. -/
def lowerLift (b : SlitBaseLift) : C(lowerBase, TriangleRegularPoint) :=
  (lowerLift_existsUnique b).choose

@[simp] theorem upperLift_basepoint (b : SlitBaseLift) :
    upperLift b upperBasePoint = b.val :=
  (upperLift_existsUnique b).choose_spec.1.1

@[simp] theorem lowerLift_basepoint (b : SlitBaseLift) :
    lowerLift b lowerBasePoint = b.val :=
  (lowerLift_existsUnique b).choose_spec.1.1

@[simp] theorem upperLift_project (b : SlitBaseLift) (x : upperBase) :
    triangleRegularProject (upperLift b x) = x.val :=
  congrFun (upperLift_existsUnique b).choose_spec.1.2 x

@[simp] theorem lowerLift_project (b : SlitBaseLift) (x : lowerBase) :
    triangleRegularProject (lowerLift b x) = x.val :=
  congrFun (lowerLift_existsUnique b).choose_spec.1.2 x

theorem upperLift_unique (b : SlitBaseLift) (s : C(upperBase, TriangleRegularPoint))
    (hs : ∀ x, triangleRegularProject (s x) = x.val)
    (hb : s upperBasePoint = b.val) : s = upperLift b :=
  (upperLift_existsUnique b).choose_spec.2 s ⟨hb, funext hs⟩

theorem lowerLift_unique (b : SlitBaseLift) (s : C(lowerBase, TriangleRegularPoint))
    (hs : ∀ x, triangleRegularProject (s x) = x.val)
    (hb : s lowerBasePoint = b.val) : s = lowerLift b :=
  (lowerLift_existsUnique b).choose_spec.2 s ⟨hb, funext hs⟩

/-- The literal inclusion of a strip into the upper slit. -/
def overlapToUpper (i : Fin 3) : C(overlapBase i, upperBase) :=
  ⟨fun x => ⟨x.val, (overlapBase_subset i x.property).1⟩, by fun_prop⟩

/-- The literal inclusion of a strip into the lower slit. -/
def overlapToLower (i : Fin 3) : C(overlapBase i, lowerBase) :=
  ⟨fun x => ⟨x.val, (overlapBase_subset i x.property).2⟩, by fun_prop⟩

def upperLiftOnOverlap (b : SlitBaseLift) (i : Fin 3) :
    C(overlapBase i, TriangleRegularPoint) :=
  (upperLift b).comp (overlapToUpper i)

def lowerLiftOnOverlap (b : SlitBaseLift) (i : Fin 3) :
    C(overlapBase i, TriangleRegularPoint) :=
  (lowerLift b).comp (overlapToLower i)

@[simp] theorem upperLiftOnOverlap_project (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i) : triangleRegularProject (upperLiftOnOverlap b i x) = x.val :=
  upperLift_project b (overlapToUpper i x)

@[simp] theorem lowerLiftOnOverlap_project (b : SlitBaseLift) (i : Fin 3)
    (x : overlapBase i) : triangleRegularProject (lowerLiftOnOverlap b i x) = x.val :=
  lowerLift_project b (overlapToLower i x)

theorem overlapTransition_exists (b : SlitBaseLift) (i : Fin 3) :
    ∃ g : TriangleGroup,
      g • upperLiftOnOverlap b i (overlapBasePoint i) =
        lowerLiftOnOverlap b i (overlapBasePoint i) := by
  apply triangleRegularProject_covering.apply_eq_iff_mem_orbit.mp
  rw [upperLiftOnOverlap_project, lowerLiftOnOverlap_project]

/-- The actual deck element comparing the two normalized sections on a strip. -/
def overlapTransition (b : SlitBaseLift) (i : Fin 3) : TriangleGroup :=
  (overlapTransition_exists b i).choose

theorem overlapTransition_at_point (b : SlitBaseLift) (i : Fin 3) :
    overlapTransition b i • upperLiftOnOverlap b i (overlapBasePoint i) =
      lowerLiftOnOverlap b i (overlapBasePoint i) :=
  (overlapTransition_exists b i).choose_spec

/-- Covering uniqueness, on the actual connected strip, makes this deck element constant. -/
theorem overlapTransition_apply (b : SlitBaseLift) (i : Fin 3) (x : overlapBase i) :
    overlapTransition b i • upperLiftOnOverlap b i x = lowerLiftOnOverlap b i x := by
  have he : (fun y => overlapTransition b i • upperLiftOnOverlap b i y) =
      lowerLiftOnOverlap b i := by
    apply triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
      ((triangleRegularProject_covering.continuous_const_smul _).comp
        (upperLiftOnOverlap b i).continuous)
      (lowerLiftOnOverlap b i).continuous
    · funext y
      change triangleRegularProject (overlapTransition b i • upperLiftOnOverlap b i y) =
        triangleRegularProject (lowerLiftOnOverlap b i y)
      rw [triangleRegularProject_covering.map_smul,
        upperLiftOnOverlap_project, lowerLiftOnOverlap_project]
    · exact overlapTransition_at_point b i
  exact congrFun he x

/-- The constant transition is uniquely determined by its value at any one strip point. -/
theorem overlapTransition_eq_of_apply (b : SlitBaseLift) (i : Fin 3)
    (g : TriangleGroup) (x : overlapBase i)
    (hg : g • upperLiftOnOverlap b i x = lowerLiftOnOverlap b i x) :
    overlapTransition b i = g := by
  let := triangleRegularProject_covering.isCancelSMul
  exact IsCancelSMul.right_cancel _ _ (upperLiftOnOverlap b i x)
    ((overlapTransition_apply b i x).trans hg.symm)

/-- The common normalized basepoint lies in the middle overlap strip. -/
def middleOverlapPoint : overlapBase 1 := by
  refine ⟨slitBasepoint, ?_⟩
  rw [mem_regularOpen, slitBasepoint_coordinate]
  change (1 / 2 : ℂ) ∈ overlapStrip 1
  norm_num [overlapStrip]

@[simp] theorem upperLift_middleOverlapPoint (b : SlitBaseLift) :
    upperLiftOnOverlap b 1 middleOverlapPoint = b.val :=
  upperLift_basepoint b

@[simp] theorem lowerLift_middleOverlapPoint (b : SlitBaseLift) :
    lowerLiftOnOverlap b 1 middleOverlapPoint = b.val :=
  lowerLift_basepoint b

/-- No deck transition occurs on the overlap component containing the common starting point. -/
@[simp] theorem overlapTransition_middle (b : SlitBaseLift) : overlapTransition b 1 = 1 := by
  apply overlapTransition_eq_of_apply b 1 1 middleOverlapPoint
  rw [one_smul, upperLift_middleOverlapPoint, lowerLift_middleOverlapPoint]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

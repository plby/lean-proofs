import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFibres

/-!
# The actual regular coinvariant-circle quotient

The invariant first real-period circle coordinate, paired with the original
base projection, is an open quotient onto the actual regular base times a
circle.  Its literal fibres are three-tori, with the original lattice
representative formula.

This proves a geometric regular part of the source's Seifert heuristic.
It neither extends this quotient through the cusp nor identifies the
constructed six-manifold with a sphere.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.Coinvariant

open SpecialPeriods TrianglePeriodFamily TrianglePeriodFamily.GammaZero
open PeriodTorusHigherHomology Set Topology

/-- The literal level set of the original first circle coordinate. -/
abbrev TorusFibre (c : AddCircle (1 : ℝ)) :=
  {x : RealTorus₄ // fibreGamma x = c}

/-- Every first-coordinate level set is the actual product of the last three circles. -/
def torusFibreHomeomorph (c : AddCircle (1 : ℝ)) :
    TorusFibre c ≃ₜ ProductTorus 3 where
  toFun x i := flatTorusCircleHomeomorph x.val i.succ
  invFun y := ⟨flatTorusCircleHomeomorph.symm (Fin.cons c y), by
    change flatTorusCircleHomeomorph
      (flatTorusCircleHomeomorph.symm (Fin.cons c y)) 0 = c
    rw [Homeomorph.apply_symm_apply]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply flatTorusCircleHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact x.property.symm
    · rfl
  right_inv y := by
    funext i
    exact congrFun (flatTorusCircleHomeomorph.apply_symm_apply (Fin.cons c y)) i.succ
  continuous_toFun := continuous_pi fun i =>
    (continuous_apply i.succ).comp
      (flatTorusCircleHomeomorph.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact flatTorusCircleHomeomorph.symm.continuous.comp
      ((productTorusSuccHomeomorph 3).symm.continuous.comp
        (continuous_const.prodMk continuous_id))

@[simp] theorem torusFibreHomeomorph_symm_val (c : AddCircle (1 : ℝ))
    (y : ProductTorus 3) :
    ((torusFibreHomeomorph c).symm y).val =
      flatTorusCircleHomeomorph.symm (Fin.cons c y) := rfl

/-- The original circle coordinate is open in the actual quotient topology. -/
theorem fibreGamma_isOpenMap : IsOpenMap fibreGamma :=
  (isOpenMap_eval (0 : Fin 4)).comp flatTorusCircleHomeomorph.isOpenMap

variable (D : Data ℂ TriangleRegularPoint)

/-- The genuine regular coinvariant map; neither its source nor its base is replaced. -/
def regularMap : C(D.Space, TriangleRegularQuotient × AddCircle (1 : ℝ)) :=
  ⟨fun x => (D.projection x, familyGamma D x),
    D.projection_continuous.prodMk (familyGamma D).continuous⟩

@[simp] theorem regularMap_quotient (b : TriangleRegularPoint) (x : RealTorus₄) :
    regularMap D (D.quotient (b, x)) = (triangleRegularProject b, fibreGamma x) := rfl

/-- On native period representatives, the circle is precisely γ, with no gauge choice. -/
@[simp] theorem regularMap_quotient_mkQ (b : TriangleRegularPoint) (x : RealPlane₄) :
    regularMap D (D.quotient (b, standardLattice.mkQ x)) =
      (triangleRegularProject b, (x 0 : AddCircle (1 : ℝ))) := by
  rw [regularMap_quotient, fibreGamma_mkQ]

theorem regularMap_surjective : Function.Surjective (regularMap D) := by
  rintro ⟨p, c⟩
  obtain ⟨b, hb⟩ := triangleRegularProject_covering.surjective p
  refine ⟨D.quotient (b, flatTorusCircleHomeomorph.symm (Fin.cons c 0)), ?_⟩
  apply Prod.ext hb
  change flatTorusCircleHomeomorph
    (flatTorusCircleHomeomorph.symm (Fin.cons c 0)) 0 = c
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem regularMap_isOpenMap : IsOpenMap (regularMap D) := by
  apply IsOpenMap.of_comp D.quotient_continuous D.quotient_surjective
  change IsOpenMap (Prod.map triangleRegularProject fibreGamma)
  exact triangleRegularProject_covering.isCoveringMap.isLocalHomeomorph.isOpenMap.prodMap
    fibreGamma_isOpenMap

/-- This is an actual topological quotient, not just a map on coinvariant homology. -/
theorem regularMap_isOpenQuotientMap : IsOpenQuotientMap (regularMap D) :=
  ⟨regularMap_surjective D, (regularMap D).continuous, regularMap_isOpenMap D⟩

/-- The literal fibre over a base lift and a first circle value. -/
abbrev RegularFibre (b : TriangleRegularPoint) (c : AddCircle (1 : ℝ)) :=
  {x : D.Space // regularMap D x = (triangleRegularProject b, c)}

/-- Forget only the first-circle equation, retaining the original base fibre. -/
def fibreToOriginal (b : TriangleRegularPoint) (c : AddCircle (1 : ℝ)) :
    C(RegularFibre D b c, OriginalFibreAt D b) :=
  ⟨fun x => ⟨x.val, congrArg Prod.fst x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The original fibre chart restricted to the actual coinvariant level set. -/
def regularFibreHomeomorph (b : TriangleRegularPoint) (c : AddCircle (1 : ℝ)) :
    RegularFibre D b c ≃ₜ TorusFibre c where
  toFun x := ⟨originalFibreHomeomorphAt D b (fibreToOriginal D b c x),
    (originalFibreHomeomorphAt_gamma D b (fibreToOriginal D b c x)).trans
      (congrArg Prod.snd x.property)⟩
  invFun y := ⟨D.quotient (b, y.val),
    Prod.ext rfl ((familyGamma_quotient D b y.val).trans y.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact (originalFibreHomeomorphAt_symm_val D b
      (originalFibreHomeomorphAt D b (fibreToOriginal D b c x))).symm.trans
      (congrArg Subtype.val
        ((originalFibreHomeomorphAt D b).symm_apply_apply (fibreToOriginal D b c x)))
  right_inv y := by
    apply Subtype.ext
    change originalFibreHomeomorphAt D b
      ⟨D.quotient (b, y.val), _⟩ = y.val
    have he : (⟨D.quotient (b, y.val), rfl⟩ : OriginalFibreAt D b) =
        (originalFibreHomeomorphAt D b).symm y.val :=
      Subtype.ext (originalFibreHomeomorphAt_symm_val D b y.val).symm
    rw [he, Homeomorph.apply_symm_apply]
  continuous_toFun := ((originalFibreHomeomorphAt D b).continuous.comp
    (fibreToOriginal D b c).continuous).subtype_mk _
  continuous_invFun := (D.quotient_continuous.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

/-- The actual fibre is a three-torus, with its inherited subspace topology. -/
def regularFibreTorusHomeomorph (b : TriangleRegularPoint) (c : AddCircle (1 : ℝ)) :
    RegularFibre D b c ≃ₜ ProductTorus 3 :=
  (regularFibreHomeomorph D b c).trans (torusFibreHomeomorph c)

@[simp] theorem regularFibreTorusHomeomorph_symm_val (b : TriangleRegularPoint)
    (c : AddCircle (1 : ℝ)) (y : ProductTorus 3) :
    ((regularFibreTorusHomeomorph D b c).symm y).val =
      D.quotient (b, flatTorusCircleHomeomorph.symm (Fin.cons c y)) := rfl

/-- The fibre parametrization retains all four original real period coordinates. -/
theorem regularFibreTorusHomeomorph_symm_mkQ (b : TriangleRegularPoint)
    (c : ℝ) (y : Fin 3 → ℝ) :
    ((regularFibreTorusHomeomorph D b (c : AddCircle (1 : ℝ))).symm
      (coordinateProjection 3 y)).val =
      D.quotient (b, standardLattice.mkQ (Fin.cons c y)) := by
  rw [regularFibreTorusHomeomorph_symm_val]
  apply congrArg (fun z : RealTorus₄ => D.quotient (b, z))
  apply flatTorusCircleHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, flatTorusCircleHomeomorph_mkQ]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.Coinvariant

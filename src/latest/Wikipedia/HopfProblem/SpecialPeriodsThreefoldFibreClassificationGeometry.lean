import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalFormsFibreLocus
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometryStrata

/-!
# Geometric classification of the actual global fibres

Every finite fibre has its literal subspace topology and an atlas obtained
by restricting the actual ambient immersion charts.  At the two marked
finite values these fibres are the original finite affine quotient
surfaces; all other finite fibres are the original special period tori.

The singular infinity fibre keeps its proved native cusp geometry.  Its
three double curves and two triple points are not asserted to be three
global surface components.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

open EllipticFilling

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

/-- The unchanged literal fibre of the constructed sphere projection. -/
abbrev SphereFibre (b : RiemannSphere) := Threefold.projectionSphere ⁻¹' {b}

/-- Select the already constructed ambient-slice atlas in each finite
case.  No complex structure is transported across an arbitrary equivalence. -/
@[instance_reducible] def finiteFibreChartedSpace (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) : ChartedSpace ComplexPlane₂ (SphereFibre b) := by
  classical
  exact if h₀ : b = ((0 : ℂ) : RiemannSphere) then
    EllipticGeometry.centralSphereFibreChartedSpace .three b
      (EllipticGeometry.sphereValue_three.trans h₀.symm)
  else if h₁ : b = ((1 : ℂ) : RiemannSphere) then
    EllipticGeometry.centralSphereFibreChartedSpace .four b
      (EllipticGeometry.sphereValue_four.trans h₁.symm)
  else Threefold.regularSphereFibreChartedSpace b h_inf h₀ h₁

theorem finiteFibreChartedSpace_of_zero (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) (h₀ : b = ((0 : ℂ) : RiemannSphere)) :
    finiteFibreChartedSpace b h_inf =
      EllipticGeometry.centralSphereFibreChartedSpace .three b
        (EllipticGeometry.sphereValue_three.trans h₀.symm) := by
  simp only [finiteFibreChartedSpace, dif_pos h₀]

theorem finiteFibreChartedSpace_of_one (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) (h₁ : b = ((1 : ℂ) : RiemannSphere)) :
    finiteFibreChartedSpace b h_inf =
      EllipticGeometry.centralSphereFibreChartedSpace .four b
        (EllipticGeometry.sphereValue_four.trans h₁.symm) := by
  have h₀ : b ≠ ((0 : ℂ) : RiemannSphere) := fun h =>
    (one_ne_zero : (1 : ℂ) ≠ 0) (OnePoint.coe_injective (h₁.symm.trans h))
  simp only [finiteFibreChartedSpace, dif_neg h₀, dif_pos h₁]

theorem finiteFibreChartedSpace_of_regular (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere))
    (h₀ : b ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : b ≠ ((1 : ℂ) : RiemannSphere)) :
    finiteFibreChartedSpace b h_inf =
      Threefold.regularSphereFibreChartedSpace b h_inf h₀ h₁ := by
  simp only [finiteFibreChartedSpace, dif_neg h₀, dif_neg h₁]

/-- Every finite fibre is a genuine complex surface, including the
reduced supports of both multiple fibres. -/
theorem finiteFibre_isManifold (b : RiemannSphere) (h_inf : b ≠ (∞ : RiemannSphere)) :
    letI := finiteFibreChartedSpace b h_inf
    IsManifold I₂ ω (SphereFibre b) := by
  classical
  by_cases h₀ : b = ((0 : ℂ) : RiemannSphere)
  · rw [finiteFibreChartedSpace_of_zero b h_inf h₀]
    exact EllipticGeometry.centralSphereFibre_isManifold .three b
      (EllipticGeometry.sphereValue_three.trans h₀.symm)
  by_cases h₁ : b = ((1 : ℂ) : RiemannSphere)
  · rw [finiteFibreChartedSpace_of_one b h_inf h₁]
    exact EllipticGeometry.centralSphereFibre_isManifold .four b
      (EllipticGeometry.sphereValue_four.trans h₁.symm)
  rw [finiteFibreChartedSpace_of_regular b h_inf h₀ h₁]
  exact Threefold.regularSphereFibre_isManifold b h_inf h₀ h₁

/-- The inclusion of every finite fibre is an immersion in the native
global atlas, even when the projection has multiplicity three or four. -/
theorem finiteFibre_inclusion_isImmersionOfComplement (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) :
    letI := finiteFibreChartedSpace b h_inf
    Manifold.IsImmersionOfComplement ℂ I₂ IF ω
      (Subtype.val : SphereFibre b → Threefold.Space) := by
  classical
  by_cases h₀ : b = ((0 : ℂ) : RiemannSphere)
  · rw [finiteFibreChartedSpace_of_zero b h_inf h₀]
    exact EllipticGeometry.centralSphereFibre_inclusion_isImmersionOfComplement .three b
      (EllipticGeometry.sphereValue_three.trans h₀.symm)
  by_cases h₁ : b = ((1 : ℂ) : RiemannSphere)
  · rw [finiteFibreChartedSpace_of_one b h_inf h₁]
    exact EllipticGeometry.centralSphereFibre_inclusion_isImmersionOfComplement .four b
      (EllipticGeometry.sphereValue_four.trans h₁.symm)
  rw [finiteFibreChartedSpace_of_regular b h_inf h₀ h₁]
  exact Threefold.regularSphereFibre_inclusion_isImmersionOfComplement b h_inf h₀ h₁

theorem finiteFibre_inclusion_holomorphic (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) :
    letI := finiteFibreChartedSpace b h_inf
    ContMDiff I₂ IF ω (Subtype.val : SphereFibre b → Threefold.Space) := by
  let := finiteFibreChartedSpace b h_inf
  exact (finiteFibre_inclusion_isImmersionOfComplement b h_inf).contMDiff

/-- The selected finite-fibre atlas has full source and both coordinate
directions equal to slices of actual charts of the glued threefold. -/
theorem finiteFibre_charts_are_ambient_slices (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) (x : SphereFibre b) :
    letI := finiteFibreChartedSpace b h_inf
    ∃ c : OpenPartialHomeomorph Threefold.Space (ℂ × ComplexPlane₂),
      ∃ L : (ComplexPlane₂ × ℂ) ≃L[ℂ] (ℂ × ComplexPlane₂),
        c ∈ IsManifold.maximalAtlas IF ω Threefold.Space ∧
        (chartAt ComplexPlane₂ x).source = Subtype.val ⁻¹' c.source ∧
        (∀ y ∈ (chartAt ComplexPlane₂ x).source,
          c (y : Threefold.Space) = L (chartAt ComplexPlane₂ x y, 0)) ∧
        (∀ u ∈ (chartAt ComplexPlane₂ x).target,
          ((chartAt ComplexPlane₂ x).symm u : Threefold.Space) = c.symm (L (u, 0))) := by
  classical
  by_cases h₀ : b = ((0 : ℂ) : RiemannSphere)
  · rw [finiteFibreChartedSpace_of_zero b h_inf h₀]
    exact EllipticGeometry.centralSphereFibre_charts_are_ambient_slices .three b
      (EllipticGeometry.sphereValue_three.trans h₀.symm) x
  by_cases h₁ : b = ((1 : ℂ) : RiemannSphere)
  · rw [finiteFibreChartedSpace_of_one b h_inf h₁]
    exact EllipticGeometry.centralSphereFibre_charts_are_ambient_slices .four b
      (EllipticGeometry.sphereValue_four.trans h₁.symm) x
  rw [finiteFibreChartedSpace_of_regular b h_inf h₀ h₁]
  exact Threefold.regularSphereFibre_charts_are_ambient_slices b h_inf h₀ h₁ x

/-- At zero the actual fibre, with the common selected ambient atlas,
is the original order-three affine quotient surface. -/
def zeroFibreBiholomorph (h_inf : ((0 : ℂ) : RiemannSphere) ≠ (∞ : RiemannSphere)) :
    letI := finiteFibreChartedSpace ((0 : ℂ) : RiemannSphere) h_inf
    Diffeomorph I₂ I₂ (SpecialCentralSurface .three)
      (SphereFibre ((0 : ℂ) : RiemannSphere)) ω := by
  rw [finiteFibreChartedSpace_of_zero _ h_inf rfl]
  exact EllipticGeometry.zeroFibreBiholomorph

/-- At one the analogous native fibre is the original order-four
affine quotient surface. -/
def oneFibreBiholomorph (h_inf : ((1 : ℂ) : RiemannSphere) ≠ (∞ : RiemannSphere)) :
    letI := finiteFibreChartedSpace ((1 : ℂ) : RiemannSphere) h_inf
    Diffeomorph I₂ I₂ (SpecialCentralSurface .four)
      (SphereFibre ((1 : ℂ) : RiemannSphere)) ω := by
  rw [finiteFibreChartedSpace_of_one _ h_inf rfl]
  exact EllipticGeometry.oneFibreBiholomorph

/-- At any other finite value, every genuine period parameter above that
value gives a biholomorphism onto the same ambient-induced literal fibre. -/
def regularFibreBiholomorph (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere))
    (h₀ : b ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : b ≠ ((1 : ℂ) : RiemannSphere))
    (z : TriangleRegularPoint) (hz : Threefold.regularSphereValue z = b) :
    letI := finiteFibreChartedSpace b h_inf
    Diffeomorph I₂ I₂ (specialPeriodMap.point z.val).Torus (SphereFibre b) ω := by
  rw [finiteFibreChartedSpace_of_regular b h_inf h₀ h₁]
  exact Threefold.regularTorusSphereFibreBiholomorph b h_inf h₀ h₁ z hz

/-- Exhaustive finite-fibre classification, with one selected native
ambient-slice atlas and no supplied global uniformization or lift. -/
theorem finiteFibre_classification (b : RiemannSphere)
    (h_inf : b ≠ (∞ : RiemannSphere)) :
    letI := finiteFibreChartedSpace b h_inf
    IsManifold I₂ ω (SphereFibre b) ∧
      ((b = ((0 : ℂ) : RiemannSphere) ∧
          Nonempty (Diffeomorph I₂ I₂ (SpecialCentralSurface .three) (SphereFibre b) ω)) ∨
        (b = ((1 : ℂ) : RiemannSphere) ∧
          Nonempty (Diffeomorph I₂ I₂ (SpecialCentralSurface .four) (SphereFibre b) ω)) ∨
        (b ≠ ((0 : ℂ) : RiemannSphere) ∧ b ≠ ((1 : ℂ) : RiemannSphere) ∧
          ∃ z : TriangleRegularPoint, Threefold.regularSphereValue z = b ∧
            Nonempty (Diffeomorph I₂ I₂ (specialPeriodMap.point z.val).Torus
              (SphereFibre b) ω))) := by
  classical
  let := finiteFibreChartedSpace b h_inf
  refine ⟨finiteFibre_isManifold b h_inf, ?_⟩
  by_cases h₀ : b = ((0 : ℂ) : RiemannSphere)
  · subst b
    exact Or.inl ⟨rfl, ⟨zeroFibreBiholomorph h_inf⟩⟩
  by_cases h₁ : b = ((1 : ℂ) : RiemannSphere)
  · subst b
    exact Or.inr (Or.inl ⟨rfl, ⟨oneFibreBiholomorph h_inf⟩⟩)
  exact Or.inr (Or.inr ⟨h₀, h₁, Threefold.regularPointOver b h_inf h₀ h₁,
    Threefold.regularPointOver_sphereValue b h_inf h₀ h₁,
    ⟨regularFibreBiholomorph b h_inf h₀ h₁ _
      (Threefold.regularPointOver_sphereValue b h_inf h₀ h₁)⟩⟩)

/-- The central infinity fibre has exactly three double curves and two
distinct triple points, and any two distinct double curves meet exactly
at those two points.  This does not assert three global surface components. -/
theorem cusp_double_curves_and_triple_points :
    (range CuspGeometry.doubleCurve).ncard = 3 ∧
      CuspGeometry.lowerTriplePoint ≠ CuspGeometry.upperTriplePoint ∧
      CuspGeometry.tripleStratum =
        {CuspGeometry.lowerTriplePoint, CuspGeometry.upperTriplePoint} ∧
      CuspGeometry.tripleStratum.ncard = 2 ∧
      (∀ i j : Fin 3, i ≠ j →
        CuspGeometry.doubleCurve i ∩ CuspGeometry.doubleCurve j =
          {CuspGeometry.lowerTriplePoint, CuspGeometry.upperTriplePoint}) ∧
      CuspGeometry.doubleStratum = ⋃ i : Fin 3, CuspGeometry.doubleCurve i :=
  ⟨CuspGeometry.doubleCurves_card, CuspGeometry.triplePoints_distinct,
    CuspGeometry.tripleStratum_eq_pair, CuspGeometry.tripleStratum_card,
    CuspGeometry.doubleCurve_inter_eq_pair, CuspGeometry.doubleStratum_eq_union⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

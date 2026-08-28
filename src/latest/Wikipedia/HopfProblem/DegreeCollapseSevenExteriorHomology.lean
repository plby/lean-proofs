import Wikipedia.HopfProblem.DegreeCollapseSurgeryExteriorSequence
import Wikipedia.NoExoticSixSphere.ProductThirdHomologyFactors
import Wikipedia.HopfProblem.OrbitPairProductSecondHomology
import Wikipedia.HopfProblem.SphereHomologyVanishing

/-!
# The exterior third homology for a three-sphere surgery in dimension seven

The original exterior inclusion is onto on third homology. Its kernel is
exactly the image of the actual meridian. Both facts hold with arbitrary
torsion. If the endpoint's fourth homology vanishes, the meridian is also
injective; that vanishing is an explicit hypothesis, not an inference from
finite third homology or from the boundary alone.
-/

noncomputable section

open Function ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorSequence.Seven

open NoExoticSixSphere
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology SurgeryExteriorRetraction

local instance : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
local instance (s : Sphere 3) : Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

variable {R X Y : Type} [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)) R X Y)

def inclusion : C(R, X) := ⟨d.oldExterior, d.oldExterior_closed.continuous⟩

def sectionMap (v : Sphere 3) : C(Sphere 3, R) :=
  (boundaryMap d).comp (ProductThirdHomology.leftSection v)

def meridianMap (s : Sphere 3) : C(Sphere 3, R) :=
  (boundaryMap d).comp (ProductThirdHomology.rightSection s)

theorem left_on_factors (s v : Sphere 3) (a b : SingularHomology (Sphere 3) 3) :
    leftMap d 3 ((ProductThirdHomology.equivalence s v).symm (a, b)) =
      (singularHomologyMap (sectionMap d v) 3 a +
        singularHomologyMap (meridianMap d s) 3 b, -a) := by
  rw [leftMap_apply]
  apply Prod.ext
  · exact ProductThirdHomology.map_product_class s v (boundaryMap d) a b
  · have h := ProductThirdHomology.equivalence_fst s v
      ((ProductThirdHomology.equivalence s v).symm (a, b))
    rw [LinearEquiv.apply_symm_apply] at h
    exact congrArg Neg.neg h.symm

theorem corner_second_homology : Subsingleton (SingularHomology (Sphere 3 × Sphere 3) 2) := by
  let : Subsingleton (SingularHomology (Sphere 3) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 2 2 (by decide) (by decide)
  exact (OrbitPair.ProductSecondHomology.equivalence (spherePole 3) (spherePole 3)).injective.subsingleton

variable [T2Space X]

theorem right_left_zero (s v : Sphere 3) (a b : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (inclusion d) 3
      (singularHomologyMap (sectionMap d v) 3 a + singularHomologyMap (meridianMap d s) 3 b) +
        singularHomologyMap d.attachingSphere 3 (-a) = 0 := by
  have h : leftMap d 3 ((ProductThirdHomology.equivalence s v).symm (a, b)) ∈
      LinearMap.range (leftMap d 3) := ⟨_, rfl⟩
  rw [exact_at_exterior_core] at h
  change rightMap d 3 (leftMap d 3 ((ProductThirdHomology.equivalence s v).symm (a, b))) = 0 at h
  rw [left_on_factors, rightMap_apply] at h
  exact h

theorem inclusion_section (v : Sphere 3) (a : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (inclusion d) 3 (singularHomologyMap (sectionMap d v) 3 a) =
      singularHomologyMap d.attachingSphere 3 a := by
  have h := right_left_zero d v v a 0
  rw [map_zero, add_zero, map_neg, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp h

theorem inclusion_meridian (s : Sphere 3) (b : SingularHomology (Sphere 3) 3) :
    singularHomologyMap (inclusion d) 3 (singularHomologyMap (meridianMap d s) 3 b) = 0 := by
  have h := right_left_zero d s s 0 b
  simpa only [map_zero, zero_add, neg_zero, add_zero] using h

theorem inclusion_surjective : Surjective (singularHomologyMap (inclusion d) 3) := by
  let : Subsingleton (SingularHomology (Sphere 3 × Sphere 3) 2) := corner_second_homology
  intro x
  have hx : x ∈ LinearMap.ker (connecting d 2) := Subsingleton.elim _ _
  rw [← exact_at_endpoint] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨c.1 + singularHomologyMap (sectionMap d (spherePole 3)) 3 c.2, ?_⟩
  rw [map_add, inclusion_section]
  rw [rightMap_apply] at hc
  exact hc

theorem meridian_range_eq_kernel (s : Sphere 3) :
    LinearMap.range (singularHomologyMap (meridianMap d s) 3) =
      LinearMap.ker (singularHomologyMap (inclusion d) 3) := by
  ext r
  constructor
  · rintro ⟨b, rfl⟩
    exact inclusion_meridian d s b
  · intro hr
    have hp : (r, 0) ∈ LinearMap.ker (rightMap d 3) := by
      change rightMap d 3 (r, 0) = 0
      rw [rightMap_apply, map_zero, add_zero]
      exact hr
    rw [← exact_at_exterior_core] at hp
    obtain ⟨c, hc⟩ := hp
    let k := ProductThirdHomology.equivalence s s c
    have he : (singularHomologyMap (sectionMap d s) 3 k.1 +
        singularHomologyMap (meridianMap d s) 3 k.2, -k.1) = (r, 0) := by
      rw [← left_on_factors]
      change leftMap d 3 ((ProductThirdHomology.equivalence s s).symm
        (ProductThirdHomology.equivalence s s c)) = _
      rw [LinearEquiv.symm_apply_apply]
      exact hc
    have ha : k.1 = 0 := neg_eq_zero.mp (congrArg Prod.snd he)
    refine ⟨k.2, ?_⟩
    have hb := congrArg Prod.fst he
    change singularHomologyMap (sectionMap d s) 3 k.1 +
      singularHomologyMap (meridianMap d s) 3 k.2 = r at hb
    simpa only [ha, map_zero, zero_add] using hb

/-- Fourth-homology vanishing is retained as an explicit hypothesis. -/
theorem meridian_injective [Subsingleton (SingularHomology X 4)] (s : Sphere 3) :
    Injective (singularHomologyMap (meridianMap d s) 3) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  let c := (ProductThirdHomology.equivalence s s).symm (0, b)
  have hc : c ∈ LinearMap.ker (leftMap d 3) := by
    change leftMap d 3 ((ProductThirdHomology.equivalence s s).symm (0, b)) = 0
    rw [left_on_factors, map_zero, zero_add, hb, neg_zero]
    rfl
  rw [← exact_at_corner] at hc
  obtain ⟨x, hx⟩ := hc
  have hc0 : c = 0 := hx.symm.trans ((congrArg (connecting d 3)
    (Subsingleton.elim x 0)).trans (map_zero _))
  have h := congrArg (ProductThirdHomology.equivalence s s) hc0
  change ProductThirdHomology.equivalence s s
    ((ProductThirdHomology.equivalence s s).symm (0, b)) = _ at h
  rw [LinearEquiv.apply_symm_apply, map_zero] at h
  exact congrArg Prod.snd h

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorSequence.Seven

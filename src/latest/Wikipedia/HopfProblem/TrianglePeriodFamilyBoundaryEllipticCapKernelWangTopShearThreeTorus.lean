import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShearBasic
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShearSmall
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegreeConnecting
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations

/-!
# The actual top homology action of a shear over the three-torus

Exchanging the first two circle coordinates makes the shear preserve the
circle used by the native Mayer--Vietoris cover. The fibre map is a two-torus
shear followed by a literal translation. Naturality of the actual signed
connecting map then determines the fourth-homology action.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology CircleTopology CirclePaths

/-- Split the three-torus and exchange its first circle with the external circle. -/
def threeSwapCoordinates : (Circle × ProductTorus 3) ≃ₜ (Circle × (Circle × ProductTorus 2)) where
  toFun p := (p.2 0, (p.1, fun i => p.2 i.succ))
  invFun p := (p.2.1, Fin.cons p.1 p.2.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact Fin.cons_self_tail p.2
  right_inv p := rfl
  continuous_toFun := ((continuous_apply 0).comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_pi fun i =>
      (continuous_apply i.succ).comp continuous_snd))
  continuous_invFun := (continuous_fst.comp continuous_snd).prodMk
    ((productTorusSuccHomeomorph 2).symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

@[simp] theorem threeSwapCoordinates_apply (p : Circle × ProductTorus 3) :
    threeSwapCoordinates p = (p.2 0, (p.1, fun i => p.2 i.succ)) := rfl

@[simp] theorem threeSwapCoordinates_symm_apply (p : Circle × (Circle × ProductTorus 2)) :
    threeSwapCoordinates.symm p = (p.2.1, Fin.cons p.1 p.2.2) := rfl

/-- The actual shear conjugated by the explicit exchange of the circle coordinates. -/
def threeHeadMap (χ : C(ProductTorus 3, Circle)) :
    C(Circle × (Circle × ProductTorus 2), Circle × (Circle × ProductTorus 2)) :=
  (threeSwapCoordinates : C(_, _)).comp
    ((shearOn 3 χ).comp (threeSwapCoordinates.symm : C(_, _)))

@[simp] theorem threeHeadMap_apply (χ : C(ProductTorus 3, Circle))
    (p : Circle × (Circle × ProductTorus 2)) :
    threeHeadMap χ p = (p.1, (p.2.1 - χ (Fin.cons p.1 p.2.2), p.2.2)) := rfl

theorem threeHeadMap_fst (χ : C(ProductTorus 3, Circle))
    (p : Circle × (Circle × ProductTorus 2)) : (threeHeadMap χ p).1 = p.1 := rfl

/-- Literal conjugacy of continuous maps, using the original coordinate homeomorphism. -/
theorem threeSwapCoordinates_shear (χ : C(ProductTorus 3, Circle)) :
    (threeSwapCoordinates : C(_, _)).comp (shearOn 3 χ) =
      (threeHeadMap χ).comp (threeSwapCoordinates : C(_, _)) := by
  apply ContinuousMap.ext
  intro p
  change threeSwapCoordinates (shearOn 3 χ p) =
    threeSwapCoordinates (shearOn 3 χ (threeSwapCoordinates.symm (threeSwapCoordinates p)))
  rw [Homeomorph.symm_apply_apply]

/-- Restrict the actual character to the last two coordinates. -/
def threeTailCharacter (χ : C(ProductTorus 3, Circle)) : C(ProductTorus 2, Circle) :=
  χ.comp (torusTailMap 2)

@[simp] theorem threeTailCharacter_apply (χ : C(ProductTorus 3, Circle)) (y : ProductTorus 2) :
    threeTailCharacter χ y = χ (Fin.cons 0 y) := rfl

theorem threeTailCharacter_add (χ : C(ProductTorus 3, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (x y : ProductTorus 2) :
    threeTailCharacter χ (x + y) = threeTailCharacter χ x + threeTailCharacter χ y := by
  change χ (torusTailMap 2 (x + y)) = χ (torusTailMap 2 x) + χ (torusTailMap 2 y)
  rw [torusTailMap_add, hχ]

/-- The character splits into the first-coordinate value and the actual tail restriction. -/
theorem threeCharacter_split (χ : C(ProductTorus 3, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (t : Circle) (y : ProductTorus 2) :
    χ (Fin.cons t y) = χ (torusHeadCircleMap 2 t) + threeTailCharacter χ y := by
  have h : (Fin.cons t y : ProductTorus 3) = torusHeadCircleMap 2 t + torusTailMap 2 y := by
    rw [torusHeadCircleMap_apply, torusTailMap_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [h, hχ]
  rfl

/-- On every fixed first-circle fibre, the conjugated map is the smaller shear
followed by a translation in the remaining circle coordinate. -/
theorem threeHeadMap_fibre (χ : C(ProductTorus 3, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (t : Circle) :
    Homology.headMapFibre (threeHeadMap χ) t =
      (rightTranslation (-χ (torusHeadCircleMap 2 t), (0 : ProductTorus 2))).comp
        (shearOn 2 (threeTailCharacter χ)) := by
  apply ContinuousMap.ext
  rintro ⟨c, y⟩
  apply Prod.ext
  · change c - χ (Fin.cons t y) =
      (c - threeTailCharacter χ y) + -χ (torusHeadCircleMap 2 t)
    rw [threeCharacter_split χ hχ]
    abel
  · change y = y + 0
    exact (add_zero y).symm

/-- The connecting coordinate is injective because the other degree-four
summand is the vanishing homology of a three-dimensional product torus. -/
theorem threeHeadBoundary_injective :
    Function.Injective (circleBoundary (Circle × ProductTorus 2) 3) := by
  let := circleTorus_homology_subsingleton_of_lt (r := 2) (n := 4) (by decide)
  intro a b hab
  apply (circleProductHomologyEquiv (Circle × ProductTorus 2) 3).injective
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hab

/-- The smaller shear and the actual translation both fix degree-three fibre homology. -/
theorem threeHeadMap_fibre_homologyThree (χ : C(ProductTorus 3, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (t : Circle)
    (a : SingularHomology (Circle × ProductTorus 2) 3) :
    singularHomologyMap (Homology.headMapFibre (threeHeadMap χ) t) 3 a = a := by
  rw [threeHeadMap_fibre χ hχ, singularHomologyMap_comp,
    rightTranslation_singularHomologyMap, LinearMap.id_comp]
  exact shearOn_two_homologyThree (threeTailCharacter χ) (threeTailCharacter_add χ hχ) a

/-- The signed native Mayer--Vietoris coordinate proves the conjugated shear
acts as the identity on all actual fourth homology. -/
theorem threeHeadMap_homologyFour (χ : C(ProductTorus 3, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a : SingularHomology (Circle × (Circle × ProductTorus 2)) 4) :
    singularHomologyMap (threeHeadMap χ) 4 a = a := by
  apply threeHeadBoundary_injective
  rw [Homology.circleBoundary_headMap (threeHeadMap χ) (threeHeadMap_fst χ) 3 a]
  exact threeHeadMap_fibre_homologyThree χ hχ quarterPoint
    (circleBoundary (Circle × ProductTorus 2) 3 a)

/-- Every additive-character shear fixes every actual top-homology class of
the circle times the three-torus. No character or determinant classification is used. -/
theorem shearOn_three_homologyFour (χ : C(ProductTorus 3, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a : SingularHomology (Circle × ProductTorus 3) 4) :
    singularHomologyMap (shearOn 3 χ) 4 a = a := by
  apply (homeomorphHomologyEquiv threeSwapCoordinates 4).injective
  simp only [homeomorphHomologyEquiv_apply]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, threeSwapCoordinates_shear,
    singularHomologyMap_comp, LinearMap.comp_apply]
  exact threeHeadMap_homologyFour χ hχ _

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

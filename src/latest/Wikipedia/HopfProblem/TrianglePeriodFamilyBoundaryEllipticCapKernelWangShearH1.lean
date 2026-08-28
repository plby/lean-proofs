import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShearBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleNormalization
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# First homology of the actual circle shear

The first-coordinate class is the native positive period loop. Its coefficient
is measured by the existing signed circle-homology equivalence. The shear
fixes this first-circle summand and subtracts the character degree from the
head coordinate of every tail first-homology class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology CircleTopology

private theorem loopHomologyClass_add_zero {G : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] (p q : Path (0 : G) 0) :
    loopHomologyClass (p.add q) = loopHomologyClass p + loopHomologyClass q := by
  have hp : (p.prod (Path.refl (0 : G))).map continuous_add =
      p.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply,
      Path.cast_coe, add_zero]
  have hq : ((Path.refl (0 : G)).prod q).map continuous_add =
      q.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply,
      Path.cast_coe, zero_add]
  have h : ((p.prod (Path.refl (0 : G))).trans
      ((Path.refl (0 : G)).prod q)).Homotopic (p.prod q) := by
    rw [Path.trans_prod_eq_prod_trans]
    exact ⟨Path.Homotopic.prodHomotopy (Path.Homotopy.transRefl p)
      (Path.Homotopy.reflTrans q)⟩
  have he := loopHomologyClass_homotopic
    (h.map (⟨fun x : G × G => x.1 + x.2, continuous_add⟩ : C(G × G, G)))
  rw [Path.map_trans, loopHomologyClass_trans, hp, hq] at he
  exact he.symm

private theorem inducedH1_add_of_zero {X G : Type} [TopologicalSpace X]
    [PathConnectedSpace X] [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (f g : C(X, G)) (b : X)
    (hf : f b = 0) (hg : g b = 0) :
    inducedHomology (f + g) = inducedHomology f + inducedHomology g := by
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective b a
  let pf : Path (0 : G) 0 := (p.map f.continuous).cast hf.symm hf.symm
  let pg : Path (0 : G) 0 := (p.map g.continuous).cast hg.symm hg.symm
  have h : p.map (f + g).continuous =
      (pf.add pg).cast (by simp only [ContinuousMap.add_apply, hf, hg])
        (by simp only [ContinuousMap.add_apply, hf, hg]) := by
    ext t
    rfl
  simp only [LinearMap.add_apply, inducedHomology_loopHomologyClass]
  rw [h]
  exact loopHomologyClass_add_zero pf pg

private theorem inducedH1_sub_of_zero {X G : Type} [TopologicalSpace X]
    [PathConnectedSpace X] [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (f g : C(X, G)) (b : X)
    (hf : f b = 0) (hg : g b = 0) :
    inducedHomology (f - g) = inducedHomology f - inducedHomology g := by
  have h := inducedH1_add_of_zero (f - g) g b
    (by simp only [ContinuousMap.sub_apply, hf, hg, sub_self]) hg
  rw [sub_add_cancel] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

/-- The positive first-coordinate period class in the actual five-torus. -/
def headClass : SingularHomology (ProductTorus 5) 1 :=
  loopHomologyClass (coordinatePeriodLoop 5 (Pi.single 0 1))

theorem headClass_eq_image :
    headClass = singularHomologyMap (torusHeadCircleMap 4) 1
      (loopHomologyClass CirclePaths.positiveLoop) :=
  (torusHeadCircleMap_positiveHomology 4).symm

/-- The native circle degree is exactly the coefficient of the head class. -/
theorem headHomology_eq_degree_smul (a : SingularHomology Circle 1) :
    singularHomologyMap (torusHeadCircleMap 4) 1 a =
      circleHomologyOneEquiv a • headClass := by
  have ha : a = circleHomologyOneEquiv a • loopHomologyClass CirclePaths.positiveLoop := by
    simpa only [LinearEquiv.symm_apply_apply] using
      circleHomologyOneEquiv_symm_int (circleHomologyOneEquiv a)
  calc
    _ = singularHomologyMap (torusHeadCircleMap 4) 1
        (circleHomologyOneEquiv a • loopHomologyClass CirclePaths.positiveLoop) :=
      congrArg (singularHomologyMap (torusHeadCircleMap 4) 1) ha
    _ = circleHomologyOneEquiv a • headClass := by
      rw [map_zsmul, torusHeadCircleMap_positiveHomology]
      rfl

/-- The actual shear fixes the full first-circle image on first homology. -/
theorem torusShear_headHomology (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (a : SingularHomology Circle 1) :
    singularHomologyMap (torusShear χ) 1
        (singularHomologyMap (torusHeadCircleMap 4) 1 a) =
      singularHomologyMap (torusHeadCircleMap 4) 1 a := by
  change ((singularHomologyMap (torusShear χ) 1).comp
    (singularHomologyMap (torusHeadCircleMap 4) 1)) a = _
  rw [← singularHomologyMap_comp, torusShear_comp_head χ hχ]

/-- In particular the positive head period class is fixed, with its original sign. -/
theorem torusShear_headClass (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) :
    singularHomologyMap (torusShear χ) 1 headClass = headClass := by
  simpa only [headClass_eq_image] using
    torusShear_headHomology χ hχ (loopHomologyClass CirclePaths.positiveLoop)

/-- On every actual tail first-homology class, the shear subtracts exactly
the character's native circle degree times the positive head class. -/
theorem torusShear_tailHomology (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (torusShear χ) 1
        (singularHomologyMap (torusTailMap 4) 1 b) =
      singularHomologyMap (torusTailMap 4) 1 b -
        circleHomologyOneEquiv (singularHomologyMap χ 1 b) • headClass := by
  have hzero : ((torusHeadCircleMap 4).comp χ) (0 : ProductTorus 4) = 0 := by
    change torusHeadCircleMap 4 (χ 0) = 0
    rw [character_zero χ hχ]
    exact coordinateCircleMap_zero (Pi.single (0 : Fin 5) 1)
  have hsub : singularHomologyMap (torusTailMap 4 - (torusHeadCircleMap 4).comp χ) 1 =
      singularHomologyMap (torusTailMap 4) 1 -
        singularHomologyMap ((torusHeadCircleMap 4).comp χ) 1 := by
    simpa only [singularHomologyMap_one] using
      inducedH1_sub_of_zero (torusTailMap 4) ((torusHeadCircleMap 4).comp χ)
        (0 : ProductTorus 4) (torusTailMap_zero 4) hzero
  calc
    _ = singularHomologyMap (torusTailMap 4 - (torusHeadCircleMap 4).comp χ) 1 b := by
      rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, torusShear_comp_tail]
    _ = singularHomologyMap (torusTailMap 4) 1 b -
        singularHomologyMap ((torusHeadCircleMap 4).comp χ) 1 b := by
      rw [hsub, LinearMap.sub_apply]
    _ = singularHomologyMap (torusTailMap 4) 1 b -
        circleHomologyOneEquiv (singularHomologyMap χ 1 b) • headClass := by
      rw [singularHomologyMap_comp, LinearMap.comp_apply, headHomology_eq_degree_smul]

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

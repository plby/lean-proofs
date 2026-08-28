import Wikipedia.NoExoticSixSphere.JamesSphereConeStageCylinder
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderHomology

/-!
# Projection and prepend give the finite-stage James homology splitting

The actual auxiliary James double cylinder is contractible. Its proved
attaching-map homology isomorphism, followed by the explicit contraction
of the cone factor, identifies the joint map of projection to the kth
word stage and prepend to the next word stage as an isomorphism in every
positive degree. This is the finite-stage statement, not the full James
comparison theorem.
-/

noncomputable section

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.StageHomology

def projection (n k : ℕ) : C(Sphere n × James.stage (spherePole n) k,
    James.stage (spherePole n) k) := ContinuousMap.snd

def coneProjection (n k : ℕ) : C(ReducedCone.Space n × James.stage (spherePole n) k,
    James.stage (spherePole n) k) := ContinuousMap.snd

def coneSection (n k : ℕ) : C(James.stage (spherePole n) k,
    ReducedCone.Space n × James.stage (spherePole n) k) :=
  ⟨fun w ↦ (ReducedCone.base n, w), continuous_const.prodMk continuous_id⟩

def coneProductHomotopy (n k : ℕ) :
    (ContinuousMap.id (ReducedCone.Space n × James.stage (spherePole n) k)).Homotopy
      ((coneSection n k).comp (coneProjection n k)) where
  toFun p := (ReducedCone.contract n (p.1, p.2.1), p.2.2)
  continuous_toFun := ((ReducedCone.contract n).continuous.comp
    (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
  map_zero_left p := Prod.ext (ReducedCone.contract_zero n p.1) rfl
  map_one_left p := Prod.ext (ReducedCone.contract_one n p.1) rfl

def coneProjectionEquiv (n k : ℕ) :
    ContinuousMap.HomotopyEquiv (ReducedCone.Space n × James.stage (spherePole n) k)
      (James.stage (spherePole n) k) where
  toFun := coneProjection n k
  invFun := coneSection n k
  left_inv := ⟨(coneProductHomotopy n k).symm⟩
  right_inv := ContinuousMap.Homotopic.refl _

theorem coneProjection_attachingLeft (n k : ℕ) :
    (coneProjection n k).comp (ConeStage.attachingLeft n k).hom = projection n k := rfl

def rawEquiv (n k d : ℕ) (hd : d ≠ 0) :
    SingularHomology (Sphere n × James.stage (spherePole n) k) d ≃ₗ[ℤ]
      (SingularHomology (James.stage (spherePole n) (k + 1)) d ×
        SingularHomology (ReducedCone.Space n × James.stage (spherePole n) k) d) := by
  let : ContractibleSpace (DoubleMappingCylinder.space
      (ConeStage.attachingLeft n k) (ConeStage.attachingRight n k)) :=
    (inferInstance : ContractibleSpace (ConeStage.doubleSpace n k))
  exact DoubleMappingCylinder.attachingHomologyEquiv
    (ConeStage.attachingLeft n k) (ConeStage.attachingRight n k) d hd

theorem rawEquiv_apply (n k d : ℕ) (hd : d ≠ 0)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    rawEquiv n k d hd a = (singularHomologyMap (stageAction n k) d a,
      singularHomologyMap (ConeStage.attachingLeft n k).hom d a) := by
  let : ContractibleSpace (DoubleMappingCylinder.space
      (ConeStage.attachingLeft n k) (ConeStage.attachingRight n k)) :=
    (inferInstance : ContractibleSpace (ConeStage.doubleSpace n k))
  exact DoubleMappingCylinder.attachingHomologyEquiv_apply
    (ConeStage.attachingLeft n k) (ConeStage.attachingRight n k) d hd a

def projectionActionEquiv (n k d : ℕ) (hd : d ≠ 0) :
    SingularHomology (Sphere n × James.stage (spherePole n) k) d ≃ₗ[ℤ]
      (SingularHomology (James.stage (spherePole n) k) d ×
        SingularHomology (James.stage (spherePole n) (k + 1)) d) :=
  (((rawEquiv n k d hd).toAddEquiv.trans
    ((AddEquiv.refl (SingularHomology (James.stage (spherePole n) (k + 1)) d)).prodCongr
      (homotopyEquivHomologyEquiv (coneProjectionEquiv n k) d).toAddEquiv)).trans
        AddEquiv.prodComm).toIntLinearEquiv

theorem projectionActionEquiv_apply (n k d : ℕ) (hd : d ≠ 0)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    projectionActionEquiv n k d hd a =
      (singularHomologyMap (projection n k) d a, singularHomologyMap (stageAction n k) d a) := by
  apply Prod.ext
  · change singularHomologyMap (coneProjection n k) d (rawEquiv n k d hd a).2 = _
    rw [rawEquiv_apply]
    have h := LinearMap.congr_fun
      (singularHomologyMap_comp (ConeStage.attachingLeft n k).hom (coneProjection n k) d) a
    exact h.symm
  · change (rawEquiv n k d hd a).1 = _
    rw [rawEquiv_apply]

theorem projection_action_bijective (n k d : ℕ) (hd : d ≠ 0) :
    Function.Bijective (fun a : SingularHomology (Sphere n × James.stage (spherePole n) k) d ↦
      (singularHomologyMap (projection n k) d a, singularHomologyMap (stageAction n k) d a)) := by
  have h : (fun a : SingularHomology (Sphere n × James.stage (spherePole n) k) d ↦
      (singularHomologyMap (projection n k) d a, singularHomologyMap (stageAction n k) d a)) =
      projectionActionEquiv n k d hd := by
    funext a
    exact (projectionActionEquiv_apply n k d hd a).symm
  rw [h]
  exact (projectionActionEquiv n k d hd).bijective

end NoExoticSixSphere.JamesSphere.StageHomology

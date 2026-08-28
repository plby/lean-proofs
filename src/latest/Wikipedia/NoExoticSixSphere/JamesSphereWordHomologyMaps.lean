import Wikipedia.NoExoticSixSphere.JamesHomologyStages
import Wikipedia.NoExoticSixSphere.JamesSphereStageHomology

/-!
# The full James projection/action map and its exact finite-stage naturality

Every map here is the literal projection, prepend action, or stage
inclusion on the original James words. Their commuting identities give
the corresponding identities for the actual singular homology maps.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.WordHomology

abbrev Words (n : ℕ) := James.Space (Sphere n) (spherePole n)

abbrev Parameter (n : ℕ) := Sphere n × Words n

def projection (n : ℕ) : C(Parameter n, Words n) := ContinuousMap.snd

def action (n : ℕ) : C(Parameter n, Words n) := James.letterAction (spherePole n)

def inclusion (n k : ℕ) : C(James.stage (spherePole n) k, Words n) :=
  James.HomologyStages.inclusion (spherePole n) k

def transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    C(James.stage (spherePole n) k, James.stage (spherePole n) l) :=
  James.HomologyStages.transition (spherePole n) hkl

def productInclusion (n k : ℕ) : C(Sphere n × James.stage (spherePole n) k, Parameter n) :=
  James.HomologyStages.productInclusion (spherePole n) (Sphere n) k

def productTransition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    C(Sphere n × James.stage (spherePole n) k, Sphere n × James.stage (spherePole n) l) :=
  James.HomologyStages.productTransition (spherePole n) (Sphere n) hkl

theorem projection_stage_map (n k : ℕ) :
    (projection n).comp (productInclusion n k) =
      (inclusion n k).comp (StageHomology.projection n k) := rfl

theorem action_stage_map (n k : ℕ) :
    (action n).comp (productInclusion n k) = (inclusion n (k + 1)).comp (stageAction n k) := rfl

theorem projection_transition_map (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    (StageHomology.projection n l).comp (productTransition n hkl) =
      (transition n hkl).comp (StageHomology.projection n k) := rfl

theorem action_transition_map (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    (stageAction n l).comp (productTransition n hkl) =
      (transition n (Nat.succ_le_succ hkl)).comp (stageAction n k) := rfl

theorem projection_stage (n k d : ℕ)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    singularHomologyMap (projection n) d (singularHomologyMap (productInclusion n k) d a) =
      singularHomologyMap (inclusion n k) d
        (singularHomologyMap (StageHomology.projection n k) d a) := by
  have h := congrArg (fun q ↦ singularHomologyMap q d) (projection_stage_map n k)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem action_stage (n k d : ℕ)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    singularHomologyMap (action n) d (singularHomologyMap (productInclusion n k) d a) =
      singularHomologyMap (inclusion n (k + 1)) d (singularHomologyMap (stageAction n k) d a) := by
  have h := congrArg (fun q ↦ singularHomologyMap q d) (action_stage_map n k)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem projection_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (d : ℕ)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    singularHomologyMap (StageHomology.projection n l) d
      (singularHomologyMap (productTransition n hkl) d a) =
        singularHomologyMap (transition n hkl) d
          (singularHomologyMap (StageHomology.projection n k) d a) := by
  have h := congrArg (fun q ↦ singularHomologyMap q d) (projection_transition_map n hkl)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem action_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (d : ℕ)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    singularHomologyMap (stageAction n l) d (singularHomologyMap (productTransition n hkl) d a) =
      singularHomologyMap (transition n (Nat.succ_le_succ hkl)) d
        (singularHomologyMap (stageAction n k) d a) := by
  have h := congrArg (fun q ↦ singularHomologyMap q d) (action_transition_map n hkl)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem inclusion_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (d : ℕ)
    (a : SingularHomology (James.stage (spherePole n) k) d) :
    singularHomologyMap (inclusion n l) d (singularHomologyMap (transition n hkl) d a) =
      singularHomologyMap (inclusion n k) d a :=
  CompactExhaustionHomology.inclusion_homology_comp (James.stage_mono (spherePole n) hkl) d a

theorem productInclusion_transition (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (d : ℕ)
    (a : SingularHomology (Sphere n × James.stage (spherePole n) k) d) :
    singularHomologyMap (productInclusion n l) d
      (singularHomologyMap (productTransition n hkl) d a) =
        singularHomologyMap (productInclusion n k) d a :=
  (LinearMap.congr_fun
    (singularHomologyMap_comp (productTransition n hkl) (productInclusion n l) d) a).symm

theorem transition_zero (n : ℕ) {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) (d : ℕ)
    (a : SingularHomology (James.stage (spherePole n) k) d)
    (ha : singularHomologyMap (transition n hkl) d a = 0) :
    singularHomologyMap (transition n (hkl.trans hlm)) d a = 0 := by
  have h := LinearMap.congr_fun
    (singularHomologyMap_comp (transition n hkl) (transition n hlm) d) a
  change singularHomologyMap (transition n (hkl.trans hlm)) d a =
    singularHomologyMap (transition n hlm) d (singularHomologyMap (transition n hkl) d a) at h
  rw [h, ha, map_zero]

def projectionActionMap (n d : ℕ) :
    SingularHomology (Parameter n) d →ₗ[ℤ]
      (SingularHomology (Words n) d × SingularHomology (Words n) d) := by
  let F := (singularHomologyMap (projection n) d).toAddMonoidHom.prod
    (singularHomologyMap (action n) d).toAddMonoidHom
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' r a := by
        exact (congrArg F
          (int_smul_eq_zsmul (SingularHomology (Parameter n) d).isModule r a)).trans
            (F.map_zsmul r a) }

end NoExoticSixSphere.JamesSphere.WordHomology

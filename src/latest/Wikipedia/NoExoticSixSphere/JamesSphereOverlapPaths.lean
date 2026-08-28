import Wikipedia.NoExoticSixSphere.JamesSphereOverlapRetraction

/-!
# The actual overlap path space and its sphere-times-loops model

Lifting the proved middle-slice deformation gives a homotopy equivalence
whose forward map is the literal inclusion of path spaces. Composing its
inverse with the checked middle-slice equivalence identifies the overlap
with the sphere times native loops. The resulting homology splitting still
needs its two maps identified with projection and the James loop action.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.Overlap

def fiberEquiv (n : ℕ) :
    HomotopyFiber.Space (middle n) (spherePole (n + 1)) ≃ₕ
      HomotopyFiber.Space (EndingPath.inclusion (overlap n)) (spherePole (n + 1)) :=
  HomotopyFiberDeformationRetract.equivalence (EndingPath.inclusion (overlap n))
    (spherePole (n + 1)) (middleInclusion n) (middleRetraction n)
    (hri := middleRetraction_inclusion n) (H := middleDeformation n)

theorem middle_paths_subset (n : ℕ) :
    EndingPath.restriction (spherePole (n + 1)) (Set.range (middle n)) ⊆
      EndingPath.restriction (spherePole (n + 1)) (overlap n) := by
  intro p hp
  obtain ⟨x, hx⟩ := hp
  change EndingPath.source (spherePole (n + 1)) p ∈ overlap n
  rw [← hx]
  exact (middleInclusion n x).property

def pathInclusion (n : ℕ) :
    C(EndingPath.restriction (spherePole (n + 1)) (Set.range (middle n)),
      EndingPath.restriction (spherePole (n + 1)) (overlap n)) :=
  ContinuousMap.inclusion (middle_paths_subset n)

def pathEquiv (n : ℕ) :
    EndingPath.restriction (spherePole (n + 1)) (Set.range (middle n)) ≃ₕ
      EndingPath.restriction (spherePole (n + 1)) (overlap n) :=
  ((EndingPath.embeddingFiberHomeomorph (middle n) (middle_isClosedEmbedding n).isEmbedding
    (spherePole (n + 1))).symm.toHomotopyEquiv.trans (fiberEquiv n)).trans
      (EndingPath.restrictionHomeomorph (spherePole (n + 1)) (overlap n)).symm.toHomotopyEquiv

theorem pathEquiv_apply_val (n : ℕ)
    (p : EndingPath.restriction (spherePole (n + 1)) (Set.range (middle n))) :
    (pathEquiv n p).val = p.val := rfl

theorem pathEquiv_toFun (n : ℕ) : (pathEquiv n).toFun = pathInclusion n := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact pathEquiv_apply_val n p

theorem pathInclusion_homology_bijective (n k : ℕ) :
    Function.Bijective (singularHomologyMap (pathInclusion n) k) := by
  rw [← pathEquiv_toFun]
  exact (homotopyEquivHomologyEquiv (pathEquiv n) k).bijective

def loopProductEquiv (n : ℕ) :
    EndingPath.restriction (spherePole (n + 1)) (overlap n) ≃ₕ
      Sphere n × Path (spherePole (n + 1)) (spherePole (n + 1)) :=
  (pathEquiv n).symm.trans (middlePathEquiv n)

theorem loopProductEquiv_symm_curve (n : ℕ) (x : Sphere n)
    (p : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    ((loopProductEquiv n).symm (x, p)).val.val =
      (((middleNullhomotopy n).toHomotopy.evalAt x).trans p).toContinuousMap := by
  change (pathEquiv n ((middlePathEquiv n).symm (x, p))).val.val = _
  rw [pathEquiv_apply_val, middlePathEquiv_symm_curve]

theorem loopProductEquiv_symm_source (n : ℕ) (x : Sphere n)
    (p : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    EndingPath.source (spherePole (n + 1)) ((loopProductEquiv n).symm (x, p)).val = middle n x := by
  change EndingPath.source (spherePole (n + 1))
    (pathEquiv n ((middlePathEquiv n).symm (x, p))).val = _
  rw [pathEquiv_apply_val, middlePathEquiv_symm_source]

def generatorCoverHomologyEquiv (n k : ℕ) (hk : k ≠ 0) :
    SingularHomology (Sphere n × Path (spherePole (n + 1)) (spherePole (n + 1))) k ≃ₗ[ℤ]
      (SingularHomology (Path (spherePole (n + 1)) (spherePole (n + 1))) k ×
        SingularHomology (Path (spherePole (n + 1)) (spherePole (n + 1))) k) :=
  (homotopyEquivHomologyEquiv (loopProductEquiv n).symm k).trans
    (punctureCoverHomologyEquiv n k hk)

end NoExoticSixSphere.JamesSphere.Overlap

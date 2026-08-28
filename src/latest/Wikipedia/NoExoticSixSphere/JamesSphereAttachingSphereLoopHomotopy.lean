import Wikipedia.NoExoticSixSphere.JamesSphereAttachingLoopCorrection

/-!
# The corrected attaching loops descend jointly to the product of spheres

The actual cube-to-sphere maps are quotient maps, as is their product
with homotopy time. The checked track identities therefore descend the
entire loop homotopy. Its initial map is the ordered path commutator
and its terminal map is constant on the fat wedge. This homotopy on
the product is sufficient for homology comparisons; no stronger
identity of the two smash-sphere homotopy classes is inferred.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem sphereParameters_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (sphereParameters n) := by
  intro v
  choose u hu using (fun i ↦ SmoothCube.quotient_surjective hn (v i))
  exact ⟨u, funext hu⟩

theorem sphereParameters_isQuotientMap (n : ℕ) (hn : 0 < n) :
    IsQuotientMap (sphereParameters n) :=
  IsQuotientMap.of_surjective_continuous (sphereParameters_surjective n hn)
    (sphereParameters n).continuous

def tailSphereCylinder (n : ℕ) :
    C(I × Parameter n, I × SphereMooreCommutator.Parameter n) :=
  (ContinuousMap.id I).prodMap (sphereParameters n)

theorem tailSphereCylinder_isQuotientMap (n : ℕ) (hn : 0 < n) :
    IsQuotientMap (tailSphereCylinder n) := by
  apply IsQuotientMap.of_surjective_continuous _ (tailSphereCylinder n).continuous
  rintro ⟨s, v⟩
  obtain ⟨u, hu⟩ := sphereParameters_surjective n hn v
  exact ⟨(s, u), Prod.ext rfl hu⟩

theorem loopCorrectionMap_respects (n : ℕ) (p q : I × Parameter n)
    (h : tailSphereCylinder n p = tailSphereCylinder n q) :
    loopCorrectionMap n p = loopCorrectionMap n q := by
  rcases p with ⟨s, v⟩
  rcases q with ⟨t, w⟩
  have he : s = t := congrArg Prod.fst h
  subst t
  exact loopCorrection_respects n s v w (congrArg Prod.snd h)

def sphereLoopCorrection (n : ℕ) (hn : 0 < n) :
    C(I × SphereMooreCommutator.Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  IsQuotientMap.lift (f := tailSphereCylinder n) (tailSphereCylinder_isQuotientMap n hn)
    (loopCorrectionMap n) (loopCorrectionMap_respects n)

theorem sphereLoopCorrection_parameters (n : ℕ) (hn : 0 < n) (s : I) (v : Parameter n) :
    sphereLoopCorrection n hn (s, sphereParameters n v) = loopCorrection n s v :=
  ContinuousMap.congr_fun (IsQuotientMap.lift_comp (tailSphereCylinder_isQuotientMap n hn)
    (loopCorrectionMap n) (loopCorrectionMap_respects n)) (s, v)

def originalSphereLoops (n : ℕ) :
    C(SphereMooreCommutator.Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (reorderPaths n).comp (Moore.Loop.pathCommutator.comp
    (SphereMooreCommutator.pairMap n (MeridianCommutator.meridians n)
      (MeridianCommutator.meridians n)))

theorem originalSphereLoops_parameters (n : ℕ) (v : Parameter n) :
    originalSphereLoops n (sphereParameters n v) = trace n v := reorder_pathCommutator n v

theorem sphereLoopCorrection_zero (n : ℕ) (hn : 0 < n)
    (v : SphereMooreCommutator.Parameter n) :
    sphereLoopCorrection n hn (0, v) = originalSphereLoops n v := by
  obtain ⟨u, rfl⟩ := sphereParameters_surjective n hn v
  rw [sphereLoopCorrection_parameters, loopCorrection_zero, originalSphereLoops_parameters]

theorem sphereLoopCorrection_point (n : ℕ) (hn : 0 < n) (s : I) :
    sphereLoopCorrection n hn (s, SphereMooreCommutator.point n) =
      Path.refl (spherePole (n + 1)) := by
  obtain ⟨u, hu⟩ := sphereParameters_surjective n hn (SphereMooreCommutator.point n)
  rw [← hu, sphereLoopCorrection_parameters]
  apply loopCorrection_poles
  intro i
  exact congrFun hu i

theorem originalSphereLoops_point (n : ℕ) (hn : 0 < n) :
    originalSphereLoops n (SphereMooreCommutator.point n) = Path.refl (spherePole (n + 1)) :=
  (sphereLoopCorrection_zero n hn _).symm.trans (sphereLoopCorrection_point n hn 0)

def correctedSphereLoops (n : ℕ) (hn : 0 < n) :
    C(SphereMooreCommutator.Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (sphereLoopCorrection n hn).comp ⟨fun v ↦ (1, v), continuous_const.prodMk continuous_id⟩

theorem correctedSphereLoops_parameters (n : ℕ) (hn : 0 < n) (v : Parameter n) :
    correctedSphereLoops n hn (sphereParameters n v) = loopCorrection n 1 v :=
  sphereLoopCorrection_parameters n hn 1 v

theorem correctedSphereLoops_boundary (n : ℕ) (hn : 0 < n)
    (v : SphereMooreCommutator.Parameter n) (hv : v ∈ SphereMooreCommutator.Boundary n) :
    correctedSphereLoops n hn v = Path.refl (spherePole (n + 1)) := by
  obtain ⟨u, rfl⟩ := sphereParameters_surjective n hn v
  rw [correctedSphereLoops_parameters]
  apply loopCorrection_one_boundary
  obtain ⟨i, hi⟩ := hv
  exact ⟨i, (SmoothCube.quotient_eq_pole_iff n _).mp hi⟩

def sphereLoopHomotopy (n : ℕ) (hn : 0 < n) :
    (originalSphereLoops n).HomotopyRel (correctedSphereLoops n hn)
      {SphereMooreCommutator.point n} where
  toContinuousMap := sphereLoopCorrection n hn
  map_zero_left := sphereLoopCorrection_zero n hn
  map_one_left _ := rfl
  prop' := by
    intro s v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact (sphereLoopCorrection_point n hn s).trans (originalSphereLoops_point n hn).symm

end NoExoticSixSphere.JamesSphere.AttachingSquare

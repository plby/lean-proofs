import Wikipedia.NoExoticSixSphere.JamesSphereAttachingPerimeter
import Wikipedia.NoExoticSixSphere.JamesSphereMeridianCommutator
import Wikipedia.NoExoticSixSphere.MooreLoopCommutatorNormalization

/-!
# A continuous comparison of the actual attaching trace and smash commutator

The perimeter formula and the duration-normalization homotopy compare
the original cell trace to the actual Moore meridians. The previously
constructed fat-wedge homotopy then gives the smash-sphere factor.
All parameters and the common constant loops are retained. This does
not yet identify the original boundary sphere generator with that of
the resulting suspended smash sphere.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def reorderPaths (n : ℕ) :
    C(Path (spherePole (n + 1)) (spherePole (n + 1)),
      Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨fun p ↦ (p.map (SuspensionCoordinates.reorder n).continuous).cast
      (SuspensionCoordinates.reorder_pole n).symm
      (SuspensionCoordinates.reorder_pole n).symm,
    Path.continuous_uncurry_iff.mp
      ((SuspensionCoordinates.reorder n).continuous.comp continuous_eval)⟩

theorem reorderPaths_trans (n : ℕ)
    (p q : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    reorderPaths n (p.trans q) = (reorderPaths n p).trans (reorderPaths n q) := by
  change ((p.trans q).map (SuspensionCoordinates.reorder n).continuous).cast
    (SuspensionCoordinates.reorder_pole n).symm (SuspensionCoordinates.reorder_pole n).symm = _
  rw [Path.map_trans]
  rfl

theorem reorderPaths_symm (n : ℕ)
    (p : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    reorderPaths n p.symm = (reorderPaths n p).symm := rfl

theorem reorderPaths_refl (n : ℕ) :
    reorderPaths n (Path.refl (spherePole (n + 1))) = Path.refl (spherePole (n + 1)) := by
  apply Path.ext
  funext t
  exact SuspensionCoordinates.reorder_pole n

theorem reorderPaths_meridian (n : ℕ) (x : Sphere n) :
    reorderPaths n (unitLoop n x) = orderedMeridian n x := by
  apply Path.ext
  funext t
  exact (orderedMeridian_reorder n x t).symm

def sphereParameters (n : ℕ) : C(Parameter n, SphereMooreCommutator.Parameter n) :=
  ⟨fun v i ↦ SmoothCube.quotient n (v i),
    continuous_pi (fun i ↦ (SmoothCube.quotient n).continuous.comp (continuous_apply i))⟩

def loopParameters (n : ℕ) :
    C(Parameter n, Moore.Loop (spherePole (n + 1)) × Moore.Loop (spherePole (n + 1))) :=
  (SphereMooreCommutator.pairMap n (MeridianCommutator.meridians n)
    (MeridianCommutator.meridians n)).comp (sphereParameters n)

def baseParameters (n : ℕ) : Set (Parameter n) :=
  {v | ∀ i, SmoothCube.quotient n (v i) = spherePole n}

theorem sphereParameters_base (n : ℕ) (v : Parameter n) (hv : v ∈ baseParameters n) :
    sphereParameters n v = SphereMooreCommutator.point n := funext hv

theorem loopParameters_base (n : ℕ) (v : Parameter n) (hv : v ∈ baseParameters n) :
    loopParameters n v = (1, 1) := by
  apply Prod.ext
  · exact (congrArg (mooreGenerator n) (hv 0)).trans (mooreGenerator_pole n)
  · exact (congrArg (mooreGenerator n) (hv 1)).trans (mooreGenerator_pole n)

theorem reorder_pathCommutator (n : ℕ) (v : Parameter n) :
    reorderPaths n (Moore.Loop.pathCommutator (loopParameters n v)) = trace n v := by
  change reorderPaths n ((((Moore.Loop.toPath (mooreGenerator n
    (SmoothCube.quotient n (v 0)))).trans (Moore.Loop.toPath (mooreGenerator n
      (SmoothCube.quotient n (v 1))))).trans (Moore.Loop.toPath (mooreGenerator n
        (SmoothCube.quotient n (v 0)))).symm).trans (Moore.Loop.toPath (mooreGenerator n
          (SmoothCube.quotient n (v 1)))).symm) = _
  simp only [toPath_mooreGenerator, reorderPaths_trans, reorderPaths_symm,
    reorderPaths_meridian]
  exact (trace_commutator n v).symm

def normalizedCommutator (n : ℕ) :
    C(Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (reorderPaths n).comp (Moore.Loop.normalizationMap.comp
    (Moore.Loop.commutatorMap.comp (loopParameters n)))

def normalizationHomotopy (n : ℕ) :
    (normalizedCommutator n).HomotopyRel (traceMap n) (baseParameters n) where
  toFun u := reorderPaths n
    (Moore.Loop.commutatorNormalizationHomotopy (u.1, loopParameters n u.2))
  continuous_toFun := (reorderPaths n).continuous.comp
    (Moore.Loop.commutatorNormalizationHomotopy.continuous.comp
      (continuous_fst.prodMk ((loopParameters n).continuous.comp continuous_snd)))
  map_zero_left v := congrArg (reorderPaths n)
    (Moore.Loop.commutatorNormalizationHomotopy.map_zero_left (loopParameters n v))
  map_one_left v := (congrArg (reorderPaths n)
    (Moore.Loop.commutatorNormalizationHomotopy.map_one_left (loopParameters n v))).trans
      (reorder_pathCommutator n v)
  prop' := by
    intro s v hv
    change reorderPaths n (Moore.Loop.commutatorNormalizationHomotopy
      (s, loopParameters n v)) = reorderPaths n
        (Moore.Loop.toPath (Moore.Loop.commutatorMap (loopParameters n v)))
    rw [loopParameters_base n v hv]
    exact congrArg (reorderPaths n)
      (Moore.Loop.commutatorNormalizationHomotopy.prop s (1, 1) (Set.mem_singleton _))

def factoredCommutator (n : ℕ) :
    C(Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (reorderPaths n).comp (Moore.Loop.normalizationMap.comp
    ((MeridianCommutator.sphereMap n).comp
      ((SecondStage.arrayPairing n).comp (sphereParameters n))))

def smashHomotopy (n : ℕ) :
    (normalizedCommutator n).HomotopyRel (factoredCommutator n) (baseParameters n) where
  toFun u := reorderPaths n
    (Moore.Loop.toPath (MeridianCommutator.factorHomotopy n (u.1, sphereParameters n u.2)))
  continuous_toFun := (reorderPaths n).continuous.comp
    (Moore.Loop.continuous_toPath.comp ((MeridianCommutator.factorHomotopy n).continuous.comp
      (continuous_fst.prodMk ((sphereParameters n).continuous.comp continuous_snd))))
  map_zero_left v := congrArg (fun p ↦ reorderPaths n (Moore.Loop.toPath p))
    ((MeridianCommutator.factorHomotopy n).map_zero_left (sphereParameters n v))
  map_one_left v := congrArg (fun p ↦ reorderPaths n (Moore.Loop.toPath p))
    ((MeridianCommutator.factorHomotopy n).map_one_left (sphereParameters n v))
  prop' := by
    intro s v hv
    apply congrArg (fun p ↦ reorderPaths n (Moore.Loop.toPath p))
    change MeridianCommutator.factorHomotopy n (s, sphereParameters n v) =
      SphereMooreCommutator.commutator n (MeridianCommutator.meridians n)
        (MeridianCommutator.meridians n) (sphereParameters n v)
    rw [sphereParameters_base n v hv]
    exact (MeridianCommutator.factorHomotopy n).prop s _ (Set.mem_singleton _)

def traceToSmashHomotopy (n : ℕ) :
    (traceMap n).HomotopyRel (factoredCommutator n) (baseParameters n) :=
  (normalizationHomotopy n).symm.trans (smashHomotopy n)

theorem factoredCommutator_boundary (n : ℕ) (v : Parameter n)
    (hv : ∃ i, v i ∈ Cube.boundary (Fin n)) :
    factoredCommutator n v = Path.refl (spherePole (n + 1)) := by
  have hp : sphereParameters n v ∈ SphereMooreCommutator.Boundary n := by
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, SmoothCube.quotient_boundary n (v i) hi⟩
  change reorderPaths n (Moore.Loop.toPath (MeridianCommutator.sphereMap n
    (SecondStage.arrayPairing n (sphereParameters n v)))) = _
  rw [(SphereMooreCommutator.arrayPairing_pole_iff n _).mpr hp,
    MeridianCommutator.sphereMap_pole, Moore.Loop.toPath_one, reorderPaths_refl]

end NoExoticSixSphere.JamesSphere.AttachingSquare

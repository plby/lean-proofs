import Wikipedia.NoExoticSixSphere.JamesSphereActionHomotopy
import Wikipedia.NoExoticSixSphere.CompactParameterPushout
import Wikipedia.HopfProblem.OrbitPairMappingCylinderCofibration

/-!
# The action on the actual mapping cylinder of the James comparison

The checked comparison homotopy glues the word action and native loop
action across the repository's genuine topological mapping cylinder.
The descended action is jointly continuous and preserves the source
subspace exactly. This supplies the relative-pair map used in the James
comparison argument; it does not assume the comparison is an equivalence.
-/

noncomputable section

open CategoryTheory unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.ComparisonCylinder

def comparison (n : ℕ) : TopCat.of (James.Space (Sphere n) (spherePole n)) ⟶
    TopCat.of (Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  TopCat.ofHom (loopComparison n)

abbrev Cylinder (n : ℕ) := MappingCylinder.space (comparison n)

def sourceAction (n : ℕ) : C(Sphere n × James.Space (Sphere n) (spherePole n), Cylinder n) :=
  (MappingCylinder.source (comparison n)).hom.comp (James.letterAction (spherePole n))

def targetAction (n : ℕ) :
    C(Sphere n × Path (spherePole (n + 1)) (spherePole (n + 1)), Cylinder n) :=
  (MappingCylinder.target (comparison n)).hom.comp
    ⟨fun p ↦ (unitLoop n p.1).trans p.2,
      ((continuous_unitLoop n).comp continuous_fst).path_trans continuous_snd⟩

def targetWordAction (n : ℕ) : C(Sphere n × James.Space (Sphere n) (spherePole n), Cylinder n) :=
  (targetAction n).comp ⟨fun p ↦ (p.1, loopComparison n p.2),
    continuous_fst.prodMk ((loopComparison n).continuous.comp continuous_snd)⟩

def extensionHomotopy (n : ℕ) : (sourceAction n).Homotopy (targetWordAction n) := by
  let F : (sourceAction n).Homotopy
      ((MappingCylinder.target (comparison n)).hom.comp
        ((loopComparison n).comp (James.letterAction (spherePole n)))) :=
    (MappingCylinder.sourceTargetHomotopy (comparison n)).compContinuousMap
      (James.letterAction (spherePole n))
  let G : ((MappingCylinder.target (comparison n)).hom.comp
      ((loopComparison n).comp (James.letterAction (spherePole n)))).Homotopy
        (targetWordAction n) :=
    (ContinuousMap.Homotopy.refl (MappingCylinder.target (comparison n)).hom).comp
      (actionHomotopy n)
  exact F.trans G

def cylinderFamily (n : ℕ) :
    C(Sphere n × (I × James.Space (Sphere n) (spherePole n)), Cylinder n) :=
  ⟨fun p ↦ (extensionHomotopy n).symm (p.2.1, (p.1, p.2.2)),
    (extensionHomotopy n).symm.continuous.comp
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩

theorem cylinderFamily_zero (n : ℕ) (x : Sphere n)
    (w : James.Space (Sphere n) (spherePole n)) :
    cylinderFamily n (x, (0, w)) = targetAction n (x, loopComparison n w) :=
  (extensionHomotopy n).symm.map_zero_left (x, w)

theorem cylinderFamily_one (n : ℕ) (x : Sphere n)
    (w : James.Space (Sphere n) (spherePole n)) :
    cylinderFamily n (x, (1, w)) = sourceAction n (x, w) :=
  (extensionHomotopy n).symm.map_one_left (x, w)

theorem families_compatible (n : ℕ) (x : Sphere n)
    (w : James.Space (Sphere n) (spherePole n)) :
    targetAction n (x, comparison n w) = cylinderFamily n
      (x, HomotopyExtension.cylinderEndpoint (TopCat.of (James.Space (Sphere n) (spherePole n)))
        0 w) := (cylinderFamily_zero n x w).symm

def action (n : ℕ) : C(Sphere n × Cylinder n, Cylinder n) :=
  CompactParameterPushout.glue (MappingCylinder.square (comparison n)) (targetAction n)
    (cylinderFamily n) (families_compatible n)

theorem action_target (n : ℕ) (x : Sphere n)
    (c : Path (spherePole (n + 1)) (spherePole (n + 1))) :
    action n (x, MappingCylinder.target (comparison n) c) =
      MappingCylinder.target (comparison n) ((unitLoop n x).trans c) :=
  CompactParameterPushout.glue_inl (MappingCylinder.square (comparison n)) (targetAction n)
    (cylinderFamily n) (families_compatible n) x c

theorem action_cylinder (n : ℕ) (x : Sphere n) (t : I)
    (w : James.Space (Sphere n) (spherePole n)) :
    action n (x, MappingCylinder.cylinder (comparison n) (t, w)) =
      cylinderFamily n (x, (t, w)) :=
  CompactParameterPushout.glue_inr (MappingCylinder.square (comparison n)) (targetAction n)
    (cylinderFamily n) (families_compatible n) x (t, w)

theorem action_source (n : ℕ) (x : Sphere n) (w : James.Space (Sphere n) (spherePole n)) :
    action n (x, MappingCylinder.source (comparison n) w) =
      MappingCylinder.source (comparison n) (James.letter (spherePole n) x * w) := by
  change action n (x, MappingCylinder.cylinder (comparison n) (1, w)) = _
  rw [action_cylinder, cylinderFamily_one]
  rfl

theorem action_preserves_source (n : ℕ) :
    Set.MapsTo (action n)
      (Set.univ ×ˢ Set.range (MappingCylinder.source (comparison n)))
      (Set.range (MappingCylinder.source (comparison n))) := by
  rintro ⟨x, p⟩ ⟨_, w, rfl⟩
  exact ⟨James.letter (spherePole n) x * w, (action_source n x w).symm⟩

theorem action_pole_source (n : ℕ) (w : James.Space (Sphere n) (spherePole n)) :
    action n (spherePole n, MappingCylinder.source (comparison n) w) =
      MappingCylinder.source (comparison n) w := by
  rw [action_source, James.letter_basepoint, one_mul]

end NoExoticSixSphere.JamesSphere.ComparisonCylinder

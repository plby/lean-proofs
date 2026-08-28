import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.EllipticAffineMaps
import Wikipedia.HopfProblem.MatrixPeriodTori

/-!
# Actual torus translations are homologically trivial in every degree

A path from zero to a translation parameter gives an actual continuous
homotopy from the identity to translation. For the complex lattice
quotients the path is the projection of a straight segment to a chosen
lift. Thus every translation on either kind of period torus induces the
identity on genuine integral singular homology in every degree. In
particular, the elliptic affine biholomorphism has exactly the same
singular homology action as its linear part, for every integral twist.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]

/-- Actual right translation on a topological additive group. -/
def rightTranslation (a : G) : C(G, G) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

@[simp] theorem rightTranslation_apply (a x : G) : rightTranslation a x = x + a := rfl

/-- A concrete path to the translation parameter gives a concrete homotopy. -/
def rightTranslationHomotopyAlong {a : G} (p : Path (0 : G) a) :
    (ContinuousMap.id G).Homotopy (rightTranslation a) where
  toFun z := z.2 + p z.1
  continuous_toFun := continuous_snd.add (p.continuous.comp continuous_fst)
  map_zero_left x := by simp
  map_one_left x := by simp

@[simp] theorem rightTranslationHomotopyAlong_apply {a : G} (p : Path (0 : G) a)
    (t : unitInterval) (x : G) :
    rightTranslationHomotopyAlong p (t, x) = x + p t := rfl

/-- In a path-connected topological group the path required above always exists. -/
def rightTranslationHomotopy [PathConnectedSpace G] (a : G) :
    (ContinuousMap.id G).Homotopy (rightTranslation a) :=
  rightTranslationHomotopyAlong (PathConnectedSpace.somePath 0 a)

end TopologicalGroup

/-- The actual singular homology map of translation along a concrete path is the identity. -/
theorem rightTranslation_singularHomologyMap_of_path
    {G : Type} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    {a : G} (p : Path (0 : G) a) (n : ℕ) :
    singularHomologyMap (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_homologyMap (rightTranslationHomotopyAlong p) n, singularHomologyMap_id]

/-- Translation acts trivially on all actual integral singular homology
groups of a path-connected topological additive group. -/
@[simp] theorem rightTranslation_singularHomologyMap
    {G : Type} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    [PathConnectedSpace G] (a : G) (n : ℕ) :
    singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (PathConnectedSpace.somePath 0 a) n

/-- Choose an actual covering-space representative of a quotient translation parameter. -/
def quotientTranslationLift (L : Submodule ℤ ComplexPlane₂) (a : ComplexPlane₂ ⧸ L) :
    ComplexPlane₂ := Classical.choose (L.mkQ_surjective a)

@[simp] theorem quotientTranslationLift_mkQ (L : Submodule ℤ ComplexPlane₂)
    (a : ComplexPlane₂ ⧸ L) : L.mkQ (quotientTranslationLift L a) = a :=
  Classical.choose_spec (L.mkQ_surjective a)

/-- Project the straight segment to the selected translation lift. -/
def quotientTranslationPath (L : Submodule ℤ ComplexPlane₂) (a : ComplexPlane₂ ⧸ L) :
    Path (0 : ComplexPlane₂ ⧸ L) a :=
  ((Path.segment (0 : ComplexPlane₂) (quotientTranslationLift L a)).map
    L.continuous_mkQ).cast (map_zero L.mkQ).symm (quotientTranslationLift_mkQ L a).symm

@[simp] theorem quotientTranslationPath_apply (L : Submodule ℤ ComplexPlane₂)
    (a : ComplexPlane₂ ⧸ L) (t : unitInterval) :
    quotientTranslationPath L a t = L.mkQ ((t : ℝ) • quotientTranslationLift L a) := by
  simp only [quotientTranslationPath, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]

/-- The actual quotient homotopy scales the selected covering-space lift. -/
def quotientTranslationHomotopy (L : Submodule ℤ ComplexPlane₂) (a : ComplexPlane₂ ⧸ L) :
    (ContinuousMap.id (ComplexPlane₂ ⧸ L)).Homotopy (rightTranslation a) :=
  rightTranslationHomotopyAlong (quotientTranslationPath L a)

@[simp] theorem quotientTranslationHomotopy_apply (L : Submodule ℤ ComplexPlane₂)
    (a : ComplexPlane₂ ⧸ L) (t : unitInterval) (x : ComplexPlane₂ ⧸ L) :
    quotientTranslationHomotopy L a (t, x) =
      x + L.mkQ ((t : ℝ) • quotientTranslationLift L a) := by
  change x + quotientTranslationPath L a t = _
  rw [quotientTranslationPath_apply]

/-- Every translation of the actual complex quotient induces the identity on singular homology. -/
theorem quotientTranslation_singularHomologyMap (L : Submodule ℤ ComplexPlane₂)
    (a : ComplexPlane₂ ⧸ L) (n : ℕ) :
    singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (quotientTranslationPath L a) n

end Wikipedia.HopfProblem.PeriodTorusHigherHomology

namespace Wikipedia.HopfProblem.PeriodDomain

open PeriodTorusHigherHomology SingularMayerVietoris

/-- The existing holomorphic period-torus translation is homotopic to the identity
through translations by the projected straight segment of a lift. -/
def translationHomotopy (p : PeriodDomain) (a : p.Torus) :
    (ContinuousMap.id p.Torus).Homotopy
      ((Elliptic.torusTranslation p a).toHomeomorph : C(p.Torus, p.Torus)) :=
  quotientTranslationHomotopy p.lattice a

@[simp] theorem translationHomotopy_apply (p : PeriodDomain) (a : p.Torus)
    (t : unitInterval) (x : p.Torus) :
    p.translationHomotopy a (t, x) =
      x + p.lattice.mkQ ((t : ℝ) • quotientTranslationLift p.lattice a) :=
  quotientTranslationHomotopy_apply p.lattice a t x

/-- All genuine singular homology groups of a period-domain torus are unchanged by translation. -/
@[simp] theorem translation_singularHomologyMap (p : PeriodDomain) (a : p.Torus) (n : ℕ) :
    singularHomologyMap ((Elliptic.torusTranslation p a).toHomeomorph : C(p.Torus, p.Torus)) n =
      LinearMap.id :=
  quotientTranslation_singularHomologyMap p.lattice a n

end Wikipedia.HopfProblem.PeriodDomain

namespace Wikipedia.HopfProblem.FullPeriodMatrix

open PeriodTorusHigherHomology SingularMayerVietoris

/-- Actual translation on an arbitrary full-period torus, without a special period-domain form. -/
def translationContinuousMap (p : FullPeriodMatrix) (a : p.Torus) : C(p.Torus, p.Torus) :=
  rightTranslation a

@[simp] theorem translationContinuousMap_apply (p : FullPeriodMatrix) (a x : p.Torus) :
    p.translationContinuousMap a x = x + a := rfl

/-- The full-period translation has the same explicit quotient homotopy. -/
def translationHomotopy (p : FullPeriodMatrix) (a : p.Torus) :
    (ContinuousMap.id p.Torus).Homotopy (p.translationContinuousMap a) :=
  quotientTranslationHomotopy p.lattice a

@[simp] theorem translationHomotopy_apply (p : FullPeriodMatrix) (a : p.Torus)
    (t : unitInterval) (x : p.Torus) :
    p.translationHomotopy a (t, x) =
      x + p.lattice.mkQ ((t : ℝ) • quotientTranslationLift p.lattice a) :=
  quotientTranslationHomotopy_apply p.lattice a t x

/-- Translation acts as the identity on every actual singular homology
group of a full-period torus. -/
@[simp] theorem translation_singularHomologyMap (p : FullPeriodMatrix) (a : p.Torus) (n : ℕ) :
    singularHomologyMap (p.translationContinuousMap a) n = LinearMap.id :=
  quotientTranslation_singularHomologyMap p.lattice a n

end Wikipedia.HopfProblem.FullPeriodMatrix

namespace Wikipedia.HopfProblem.Elliptic

open PeriodTorusHigherHomology SingularMayerVietoris

/-- The actual affine biholomorphism is the actual linear biholomorphism
followed by the specified torus translation, also as a continuous-map identity. -/
theorem affineBiholomorph_toContinuousMap (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) =
      (rightTranslation (flatProjection p.val ((1 / (j.order : ℝ)) • realCast v))).comp
        ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) := rfl

/-- Scale the actual affine translation to obtain a continuous homotopy
between the linear and affine elliptic biholomorphisms. -/
def affineBiholomorphHomotopy (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    (((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus))).Homotopy
      ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) :=
  (p.val.translationHomotopy
    (flatProjection p.val ((1 / (j.order : ℝ)) • realCast v))).compContinuousMap
      ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus))

/-- The actual affine elliptic action on singular homology is exactly
its linear part in every degree, for every integral twist. -/
theorem affineBiholomorph_singularHomologyMap (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (n : ℕ) :
    singularHomologyMap
        ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) n =
      singularHomologyMap ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) n :=
  (homotopy_homologyMap (affineBiholomorphHomotopy j p v) n).symm

end Wikipedia.HopfProblem.Elliptic

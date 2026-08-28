import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitFlatDeck
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCircle
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusQuotient

/-!
# The original boundary delta-orbit quotient

The quotient by the original positive delta-circle action on the native
elliptic boundary is the mapping torus of the actual projected affine
deck map.  All quotient topologies and cylinder representatives are
retained, including the convention `[t + 1, x] = [t, B x]`.
-/

noncomputable section

open Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic EllipticOrbitFlat
open ThreefoldOverlapMappingTorus.Elliptic

local notation "Circle" => AddCircle (1 : ℝ)

/-- The actual mapping torus of the residual affine homeomorphism. -/
abbrev BoundaryModel (j : Kind) := MappingTorus.Torus (deck j)

/-- Forget only the original delta circle in each native boundary fibre. -/
def boundaryDrop (j : Kind) : C(SpecialBoundary j, BoundaryModel j) :=
  CuspBoundaryGammaZero.mappingTorusMap (flatTorusAffine j j.twist) (deck j)
    dropDeltaMap (dropDelta_deck j)

/-- The real time and all three retained circle coordinates are unchanged. -/
@[simp] theorem boundaryDrop_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    boundaryDrop j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      MappingTorus.mk (deck j) (t, dropDelta x) := rfl

@[simp] theorem boundaryDrop_mkQ (j : Kind) (t : ℝ) (a : RealCoordinates) :
    boundaryDrop j
        (MappingTorus.mk (flatTorusAffine j j.twist) (t, standardLattice.mkQ a)) =
      MappingTorus.mk (deck j)
        (t, PeriodTorusHigherHomology.coordinateProjection 3 (fun i => a i.castSucc)) := rfl

/-- The original mapping-torus base circle is preserved exactly. -/
@[simp] theorem boundaryDrop_base (j : Kind) (x : SpecialBoundary j) :
    MappingTorus.base (deck j) (boundaryDrop j x) =
      MappingTorus.base (flatTorusAffine j j.twist) x :=
  CuspBoundaryGammaZero.mappingTorusMap_base
    (flatTorusAffine j j.twist) (deck j) dropDeltaMap (dropDelta_deck j) x

/-- The map is an open quotient in the two original mapping-torus topologies. -/
theorem boundaryDrop_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (boundaryDrop j) := by
  apply (TrianglePeriodFamily.Boundary.Cylinder.projection_isOpenQuotientMap
    (flatTorusAffine j j.twist)).of_comp_iff.mp
  change IsOpenQuotientMap (MappingTorus.mk (deck j) ∘ Prod.map (id : ℝ → ℝ) dropDelta)
  exact (TrianglePeriodFamily.Boundary.Cylinder.projection_isOpenQuotientMap (deck j)).comp
    (IsOpenQuotientMap.id.prodMap dropDelta_isOpenQuotientMap)

theorem boundaryDrop_surjective (j : Kind) : Function.Surjective (boundaryDrop j) :=
  (boundaryDrop_isOpenQuotientMap j).surjective

/-- The exact original boundary circle translation lies in each fibre. -/
@[simp] theorem boundaryDrop_deltaTranslation (j : Kind) (d : Circle)
    (x : SpecialBoundary j) :
    boundaryDrop j (GaugeIsotopy.boundaryDeltaTranslation j d x) = boundaryDrop j x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) x
  rw [GaugeIsotopy.boundaryDeltaTranslation_mk, boundaryDrop_mk, boundaryDrop_mk,
    dropDelta_add_deltaCircle]

private theorem dropDelta_zpow (j : Kind) (n : ℤ) (x : RealTorus₄) :
    dropDelta ((flatTorusAffine j j.twist ^ n) x) = (deck j ^ n) (dropDelta x) := by
  have hinv (x : RealTorus₄) :
      dropDelta ((flatTorusAffine j j.twist).symm x) = (deck j).symm (dropDelta x) := by
    apply (deck j).injective
    rw [← dropDelta_deck, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
      simp only [zpow_add_one, Homeomorph.mul_apply]
      rw [ih, dropDelta_deck]
  | pred n ih =>
      simp only [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply]
      rw [ih, hinv]

/-- The fibres are precisely the actual original delta-circle orbits,
including all possible integer changes of cylinder representative. -/
theorem boundaryDrop_eq_iff (j : Kind) (x y : SpecialBoundary j) :
    boundaryDrop j x = boundaryDrop j y ↔
      ∃ d : Circle, GaugeIsotopy.boundaryDeltaTranslation j d y = x := by
  constructor
  · intro h
    obtain ⟨⟨s, a⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) x
    obtain ⟨⟨t, b⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) y
    rw [boundaryDrop_mk, boundaryDrop_mk] at h
    obtain ⟨n, ht, hb⟩ := (MappingTorus.mk_eq_mk_iff (deck j) _ _).mp h
    rw [← dropDelta_zpow] at hb
    obtain ⟨d, hd⟩ :=
      (dropDelta_eq_iff ((flatTorusAffine j j.twist ^ (-n)) a) b).mp hb.symm
    refine ⟨d, ?_⟩
    rw [GaugeIsotopy.boundaryDeltaTranslation_mk, ← hd, ht]
    exact MappingTorus.mk_deck (flatTorusAffine j j.twist) n (s, a)
  · rintro ⟨d, rfl⟩
    exact boundaryDrop_deltaTranslation j d y

/-- The orbit relation is that of the already constructed native boundary action. -/
def boundaryOrbitSetoid (j : Kind) : Setoid (SpecialBoundary j) :=
  letI := GaugeIsotopy.boundaryDeltaAction j
  AddAction.orbitRel Circle (SpecialBoundary j)

/-- The genuine original circle-orbit quotient, with its quotient topology. -/
abbrev BoundaryOrbit (j : Kind) := Quotient (boundaryOrbitSetoid j)

def boundaryOrbitProjection (j : Kind) : SpecialBoundary j → BoundaryOrbit j :=
  Quotient.mk (boundaryOrbitSetoid j)

theorem boundaryOrbitProjection_surjective (j : Kind) :
    Function.Surjective (boundaryOrbitProjection j) := Quotient.mk_surjective

theorem boundaryOrbitProjection_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (boundaryOrbitProjection j) := by
  let := GaugeIsotopy.boundaryDeltaAction j
  let := GaugeIsotopy.boundaryDeltaAction_continuous j
  exact AddAction.isOpenQuotientMap_quotientMk

theorem boundaryOrbitProjection_eq_iff (j : Kind) (x y : SpecialBoundary j) :
    boundaryOrbitProjection j x = boundaryOrbitProjection j y ↔
      ∃ d : Circle, GaugeIsotopy.boundaryDeltaTranslation j d y = x := Quotient.eq''

@[simp] theorem boundaryOrbitProjection_deltaTranslation (j : Kind) (d : Circle)
    (x : SpecialBoundary j) :
    boundaryOrbitProjection j (GaugeIsotopy.boundaryDeltaTranslation j d x) =
      boundaryOrbitProjection j x :=
  (boundaryOrbitProjection_eq_iff j _ _).mpr ⟨d, rfl⟩

/-- The two genuine quotient maps have exactly the same fibres and quotient topology. -/
def boundaryOrbitHomeomorph (j : Kind) : BoundaryOrbit j ≃ₜ BoundaryModel j :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph
    (boundaryOrbitProjection j) (boundaryDrop j)
    (boundaryOrbitProjection_isOpenQuotientMap j).isQuotientMap
    (boundaryDrop_isOpenQuotientMap j).isQuotientMap
    (fun x y => (boundaryOrbitProjection_eq_iff j x y).trans (boundaryDrop_eq_iff j x y).symm)

@[simp] theorem boundaryOrbitHomeomorph_projection (j : Kind) (x : SpecialBoundary j) :
    boundaryOrbitHomeomorph j (boundaryOrbitProjection j x) = boundaryDrop j x :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_apply _ _ _ _ _ x

/-- The forward comparison on every original cylinder representative. -/
@[simp] theorem boundaryOrbitHomeomorph_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    boundaryOrbitHomeomorph j
        (boundaryOrbitProjection j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))) =
      MappingTorus.mk (deck j) (t, dropDelta x) := by
  rw [boundaryOrbitHomeomorph_projection, boundaryDrop_mk]

/-- The inverse comparison uses any lifted original fibre representative. -/
@[simp] theorem boundaryOrbitHomeomorph_symm_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    (boundaryOrbitHomeomorph j).symm (MappingTorus.mk (deck j) (t, dropDelta x)) =
      boundaryOrbitProjection j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) := by
  apply (boundaryOrbitHomeomorph j).injective
  rw [Homeomorph.apply_symm_apply, boundaryOrbitHomeomorph_mk]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

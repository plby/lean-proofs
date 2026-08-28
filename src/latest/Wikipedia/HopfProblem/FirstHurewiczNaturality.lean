import Wikipedia.HopfProblem.FirstHurewiczEquivalence
import Wikipedia.HopfProblem.FirstHurewiczChainNaturality

/-!
# Naturality of the first singular Hurewicz map

The map on abelianized fundamental groups is induced by the actual
fundamental-group functor. The map on integral singular homology is induced
by Mathlib's actual singular chain functor. Their Hurewicz square commutes
because mapping a path maps its actual singular one-simplex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}

/-- The actual induced map on additive fundamental-group abelianizations. -/
def inducedAbelianPi1 (f : C(X, Y)) (b : X) :
    AbelianPi1 X b →ₗ[ℤ] AbelianPi1 Y (f b) :=
  (Abelianization.map (FundamentalGroup.map f b)).toAdditive.toIntLinearMap

@[simp] theorem inducedAbelianPi1_of (f : C(X, Y)) (b : X)
    (g : FundamentalGroup X b) :
    inducedAbelianPi1 f b (Additive.ofMul (Abelianization.of g)) =
      Additive.ofMul (Abelianization.of (FundamentalGroup.map f b g)) := rfl

/-- The map on abelianizations sends the class of a loop to the class of its image. -/
@[simp] theorem inducedAbelianPi1_loopClass (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedAbelianPi1 f b (loopClass p) = loopClass (p.map f.continuous) := rfl

/-- Mapping a path maps its actual standard singular one-simplex. -/
theorem pathSimplex_map (f : C(X, Y)) (p : Path x y) :
    pathSimplex (p.map f.continuous) = f.comp (pathSimplex p) := rfl

/-- The actual induced chain map sends a path chain to the chain of the image path. -/
@[simp] theorem inducedChain_pathChain (f : C(X, Y)) (p : Path x y) :
    inducedChain f 1 (pathChain p) = pathChain (p.map f.continuous) := by
  simp only [pathChain, inducedChain_simplex, pathSimplex_map]

@[simp] theorem inducedCycles_loopCycle (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedCycles f (loopCycle p) = loopCycle (p.map f.continuous) := by
  apply Subtype.ext
  rw [inducedCycles_val, loopCycle_val, loopCycle_val, inducedChain_pathChain]

/-- Naturality on actual singular homology classes of loops. -/
@[simp] theorem inducedHomology_loopHomologyClass (f : C(X, Y)) (b : X)
    (p : Path b b) :
    inducedHomology f (loopHomologyClass p) = loopHomologyClass (p.map f.continuous) := by
  rw [loopHomologyClass, inducedHomology_cycleClass, inducedCycles_loopCycle]
  rfl

/-- The actual first singular Hurewicz map is natural for every continuous map. -/
theorem hurewiczMap_natural (f : C(X, Y)) (b : X) (a : AbelianPi1 X b) :
    inducedHomology f (hurewiczMap b a) =
      hurewiczMap (f b) (inducedAbelianPi1 f b a) := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczMap_loopClass, inducedHomology_loopHomologyClass,
    inducedAbelianPi1_loopClass, hurewiczMap_loopClass]

/-- The same naturality square as an equality of integral linear maps. -/
theorem hurewiczMap_natural_comp (f : C(X, Y)) (b : X) :
    (inducedHomology f).comp (hurewiczMap b) =
      (hurewiczMap (f b)).comp (inducedAbelianPi1 f b) :=
  LinearMap.ext (hurewiczMap_natural f b)

/-- Naturality of the first Hurewicz isomorphism on path-connected spaces. -/
theorem firstHurewiczEquiv_natural [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (b : X) (a : AbelianPi1 X b) :
    inducedHomology f (firstHurewiczEquiv b a) =
      firstHurewiczEquiv (f b) (inducedAbelianPi1 f b a) :=
  hurewiczMap_natural f b a

/-- The inverse isomorphisms carry the actual singular homology map back to
the actual map on abelianized fundamental groups. -/
theorem firstHurewiczEquiv_symm_natural [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (b : X) (a : SingularH1 X) :
    (firstHurewiczEquiv (f b)).symm (inducedHomology f a) =
      inducedAbelianPi1 f b ((firstHurewiczEquiv b).symm a) := by
  apply (firstHurewiczEquiv (f b)).injective
  rw [LinearEquiv.apply_symm_apply, ← firstHurewiczEquiv_natural f b,
    LinearEquiv.apply_symm_apply]

/-- A formula identifying the actual singular homology map with the map on
actual fundamental-group abelianizations under the proved Hurewicz isomorphisms. -/
theorem inducedHomology_eq_conjugate [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (b : X) :
    inducedHomology f = (firstHurewiczEquiv (f b)).toLinearMap.comp
      ((inducedAbelianPi1 f b).comp (firstHurewiczEquiv b).symm.toLinearMap) := by
  apply LinearMap.ext
  intro a
  change inducedHomology f a =
    firstHurewiczEquiv (f b) (inducedAbelianPi1 f b ((firstHurewiczEquiv b).symm a))
  rw [← firstHurewiczEquiv_natural, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.FirstHurewicz

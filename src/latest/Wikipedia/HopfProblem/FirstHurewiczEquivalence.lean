import Wikipedia.HopfProblem.FirstHurewiczMap
import Wikipedia.HopfProblem.FirstHurewiczInverse

/-!
# The degree-one singular Hurewicz isomorphism

This identifies the actual fundamental-group abelianization with Mathlib's
actual integral singular first homology. The inverse closes edges using
base paths. Its composite with the forward map differs from the identity
on one-chains by a base-path correction of the boundary; this correction
vanishes on cycles. No replacement homology theory is introduced.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X : Type} [TopologicalSpace X] {b x y : X}

/-- The homology object used here is definitionally Mathlib's singular
homology functor with integral coefficients in degree one. -/
theorem singularH1_eq_functor (X : Type) [TopologicalSpace X] : SingularH1 X =
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) := rfl

/-- The chain of the chosen path to each vertex, extended over the actual
singular zero-chain coproduct. -/
def basePathChain (r : ∀ x : X, Path b x) : Chains X 0 →ₗ[ℤ] Chains X 1 :=
  chainLift X 0 (fun σ => pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))))

@[simp] theorem basePathChain_pointChain (r : ∀ x : X, Path b x) (x : X) :
    basePathChain r (pointChain x) = pathChain (r x) :=
  chainLift_simplex X 0 _ (ContinuousMap.const (Simplex 0) x)

/-- The correction term for closing a path is the chosen base-path chain
of its boundary. -/
theorem edgeClosure_pathChain (r : ∀ x : X, Path b x) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r (pathChain p))) =
      chainClass X (pathChain p) -
        chainClass X (basePathChain r (boundaryOne X (pathChain p))) := by
  have he : edgeLoopCochain r (pathChain p) = basedLoopClass r p :=
    edgeLoopCochain_pathSimplex r p
  rw [he, hurewiczMap_basedLoopClass, boundaryOne_pathChain, map_sub,
    basePathChain_pointChain, basePathChain_pointChain, map_sub]
  change pathClass (r x) + pathClass p - pathClass (r y) =
    pathClass p - (pathClass (r y) - pathClass (r x))
  abel

/-- The exact telescoping identity on actual singular one-chains. -/
theorem edgeClosure_chain_identity (r : ∀ x : X, Path b x) :
    (homologyToChainClass X).comp ((hurewiczMap b).comp (edgeLoopCochain r)) =
      chainClass X - (chainClass X).comp ((basePathChain r).comp (boundaryOne X)) := by
  apply chainMap_ext X 1
  intro σ
  have h := edgeClosure_pathChain r (simplexPath σ)
  simpa only [pathChain, pathSimplex_simplexPath, LinearMap.comp_apply,
    LinearMap.sub_apply] using h

/-- On genuine cycles the boundary correction in the telescoping identity
is zero. -/
theorem edgeClosure_cycle (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) =
      chainClass X c.1 := by
  have h := LinearMap.congr_fun (edgeClosure_chain_identity r) c.1
  change homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) =
    chainClass X c.1 - chainClass X (basePathChain r (boundaryOne X c.1)) at h
  simpa only [cycles1_boundary, map_zero, sub_zero] using h

/-- Closing the edges of the chain of an already based loop recovers its
abelianized fundamental-group class. -/
@[simp] theorem inverseHurewiczMap_loopHomologyClass
    (r : ∀ x : X, Path b x) (p : Path b b) :
    inverseHurewiczMap r (loopHomologyClass p) = loopClass p := by
  rw [loopHomologyClass, inverseHurewiczMap_cycleClass, loopCycle_val]
  exact edgeLoopCochain_loopSimplex r p

/-- The constructed inverse is a left inverse of the actual Hurewicz map. -/
theorem inverseHurewiczMap_hurewiczMap (r : ∀ x : X, Path b x)
    (a : AbelianPi1 X b) : inverseHurewiczMap r (hurewiczMap b a) = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczMap_loopClass, inverseHurewiczMap_loopHomologyClass]

/-- The constructed inverse is a right inverse of the actual Hurewicz map. -/
theorem hurewiczMap_inverseHurewiczMap (r : ∀ x : X, Path b x)
    (a : SingularH1 X) : hurewiczMap b (inverseHurewiczMap r a) = a := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X a
  apply homologyToChainClass_injective X
  rw [inverseHurewiczMap_cycleClass, homologyToChainClass_cycleClass]
  exact edgeClosure_cycle r c

/-- The first singular Hurewicz isomorphism with explicit auxiliary paths.
Its forward map is canonical and independent of those paths. -/
def firstHurewiczEquivOfPaths (r : ∀ x : X, Path b x) :
    AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X where
  toLinearMap := hurewiczMap b
  invFun := inverseHurewiczMap r
  left_inv := inverseHurewiczMap_hurewiczMap r
  right_inv := hurewiczMap_inverseHurewiczMap r

@[simp] theorem firstHurewiczEquivOfPaths_apply (r : ∀ x : X, Path b x)
    (a : AbelianPi1 X b) : firstHurewiczEquivOfPaths r a = hurewiczMap b a := rfl

@[simp] theorem firstHurewiczEquivOfPaths_symm_apply (r : ∀ x : X, Path b x)
    (a : SingularH1 X) : (firstHurewiczEquivOfPaths r).symm a = inverseHurewiczMap r a := rfl

/-- The degree-one Hurewicz theorem for a path-connected topological space,
with Mathlib's actual integral singular homology as its target. -/
def firstHurewiczEquiv (b : X) [PathConnectedSpace X] :
    AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X :=
  firstHurewiczEquivOfPaths (PathConnectedSpace.somePath b)

@[simp] theorem firstHurewiczEquiv_apply (b : X) [PathConnectedSpace X]
    (a : AbelianPi1 X b) : firstHurewiczEquiv b a = hurewiczMap b a := rfl

@[simp] theorem firstHurewiczEquiv_loopClass (b : X) [PathConnectedSpace X]
    (p : Path b b) : firstHurewiczEquiv b (loopClass p) = loopHomologyClass p :=
  hurewiczMap_loopClass b p

/-- Every class of actual integral singular first homology is represented
by one based loop in a path-connected space. -/
theorem loopHomologyClass_surjective (b : X) [PathConnectedSpace X] :
    Function.Surjective (loopHomologyClass (x := b)) := by
  intro a
  obtain ⟨c, hc⟩ := (firstHurewiczEquiv b).surjective a
  obtain ⟨p, hp⟩ := loopClass_surjective c
  refine ⟨p, ?_⟩
  rw [← firstHurewiczEquiv_loopClass, hp, hc]

@[simp] theorem hurewiczMap_of (b : X) (g : FundamentalGroup X b) :
    hurewiczMap b (Additive.ofMul (Abelianization.of g)) = hurewiczFunction b g := rfl

/-- A fundamental-group element has zero integral singular homology class
exactly when it belongs to the actual commutator subgroup. -/
theorem hurewiczFunction_eq_zero_iff (b : X) [PathConnectedSpace X]
    (g : FundamentalGroup X b) :
    hurewiczFunction b g = 0 ↔ g ∈ commutator (FundamentalGroup X b) := by
  rw [← hurewiczMap_of]
  have hi : Function.Injective (hurewiczMap b) := (firstHurewiczEquiv b).injective
  rw [← map_zero (hurewiczMap b), hi.eq_iff]
  change Abelianization.of g = 1 ↔ g ∈ commutator (FundamentalGroup X b)
  rw [← Abelianization.ker_of]
  rfl

/-- The kernel form of the actual degree-one singular Hurewicz theorem. -/
theorem hurewiczPi1_ker (b : X) [PathConnectedSpace X] :
    (hurewiczPi1 b).ker = commutator (FundamentalGroup X b) := by
  ext g
  change hurewiczFunction b g = 0 ↔ g ∈ commutator (FundamentalGroup X b)
  exact hurewiczFunction_eq_zero_iff b g

/-- The Hurewicz homomorphism onto actual integral singular first homology
is surjective for a path-connected space. -/
theorem hurewiczPi1_surjective (b : X) [PathConnectedSpace X] :
    Function.Surjective (hurewiczPi1 b) := by
  intro a
  obtain ⟨p, hp⟩ := loopHomologyClass_surjective b a.toAdd
  refine ⟨loopQuotient p, ?_⟩
  exact congrArg Multiplicative.ofAdd hp

end Wikipedia.HopfProblem.FirstHurewicz

import Wikipedia.HopfProblem.FirstHurewiczPathChains
import Wikipedia.HopfProblem.FirstHurewiczPathAbelianization

/-!
# The degree-one Hurewicz map into actual singular homology

Path chains are first compared modulo actual singular two-boundaries.
The explicit concatenation and homotopy triangles give the required
relations. Based loops are actual cycles, so their classes define a
homomorphism from the fundamental group into Mathlib's singular `H₁`.
It factors through the genuine abelianization by its universal property.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x y z : X}

/-- The class of an arbitrary path chain modulo actual two-boundaries.
For a nonclosed path this is an opcycle class, not a homology class. -/
def pathClass (p : Path x y) : Opchains X := chainClass X (pathChain p)

theorem pathClass_homotopy {p q : Path x y} (H : p.Homotopy q) :
    pathClass p = pathClass q :=
  (chainClass_eq_iff X _ _).mpr
    ⟨correctedHomotopyChain H, boundaryTwo_correctedHomotopyChain H⟩

theorem pathClass_homotopic {p q : Path x y} (h : p.Homotopic q) :
    pathClass p = pathClass q := by
  obtain ⟨H⟩ := h
  exact pathClass_homotopy H

@[simp] theorem pathClass_refl (x : X) : pathClass (Path.refl x) = 0 := by
  change chainClass X (pathChain (Path.refl x)) = 0
  rw [pathChain_refl, ← boundaryTwo_constantTriangleChain]
  exact chainClass_boundary X _

/-- Concatenation is addition modulo actual singular two-boundaries. -/
theorem pathClass_trans (p : Path x y) (q : Path y z) :
    pathClass (p.trans q) = pathClass p + pathClass q := by
  have h := chainClass_boundary X (concatChain p q)
  rw [boundaryTwo_concatChain, map_add, map_sub] at h
  change pathClass q - pathClass (p.trans q) + pathClass p = 0 at h
  apply sub_eq_zero.mp
  calc
    pathClass (p.trans q) - (pathClass p + pathClass q) =
        -(pathClass q - pathClass (p.trans q) + pathClass p) := by abel
    _ = 0 := by rw [h, neg_zero]

@[simp] theorem pathClass_symm (p : Path x y) : pathClass p.symm = -pathClass p := by
  have h := pathClass_homotopic (Path.Homotopic.trans_symm p)
  rw [pathClass_trans, pathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

@[simp] theorem pathClass_cast (p : Path x y) {x' y' : X}
    (hx : x' = x) (hy : y' = y) : pathClass (p.cast hx hy) = pathClass p := rfl

/-- A based loop determines an actual cycle in Mathlib's singular complex. -/
def loopCycle (p : Path x x) : Cycles1 X := mkCycle1 X (pathChain p) (boundaryOne_loop p)

@[simp] theorem loopCycle_val (p : Path x x) : (loopCycle p).1 = pathChain p := rfl

/-- The genuine singular homology class of the singular cycle of a based loop. -/
def loopHomologyClass (p : Path x x) : SingularH1 X := cycleClass X (loopCycle p)

@[simp] theorem homologyToChainClass_loopHomologyClass (p : Path x x) :
    homologyToChainClass X (loopHomologyClass p) = pathClass p := by
  rw [loopHomologyClass, homologyToChainClass_cycleClass]
  rfl

theorem loopHomologyClass_homotopic {p q : Path x x} (h : p.Homotopic q) :
    loopHomologyClass p = loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass]
  exact pathClass_homotopic h

@[simp] theorem loopHomologyClass_refl (x : X) : loopHomologyClass (Path.refl x) = 0 := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, pathClass_refl, map_zero]

theorem loopHomologyClass_trans (p q : Path x x) :
    loopHomologyClass (p.trans q) = loopHomologyClass p + loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, map_add,
    homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass,
    pathClass_trans]

/-- The homotopy-invariant underlying function on the actual loop group. -/
def hurewiczFunction (b : X) : FundamentalGroup X b → SingularH1 X :=
  Quotient.lift (fun p : Path b b => loopHomologyClass p)
    (fun _ _ h => loopHomologyClass_homotopic h)

@[simp] theorem hurewiczFunction_loopQuotient (b : X) (p : Path b b) :
    hurewiczFunction b (loopQuotient p) = loopHomologyClass p := rfl

/-- The degree-one Hurewicz homomorphism. Fundamental-group multiplication
is reverse path concatenation in Mathlib; the target is commutative. -/
def hurewiczPi1 (b : X) : FundamentalGroup X b →* Multiplicative (SingularH1 X) where
  toFun g := Multiplicative.ofAdd (hurewiczFunction b g)
  map_one' := congrArg Multiplicative.ofAdd (loopHomologyClass_refl b)
  map_mul' g h := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
    change Multiplicative.ofAdd (loopHomologyClass (q.trans p)) =
      Multiplicative.ofAdd (loopHomologyClass p + loopHomologyClass q)
    rw [loopHomologyClass_trans, add_comm]

/-- The genuine Hurewicz map on the actual fundamental-group abelianization. -/
def hurewiczMap (b : X) : AbelianPi1 X b →ₗ[ℤ] SingularH1 X where
  toFun := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft
  map_add' := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using map_intCast_smul
      (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft ℤ ℤ n a

@[simp] theorem hurewiczMap_loopClass (b : X) (p : Path b b) :
    hurewiczMap b (loopClass p) = loopHomologyClass p := rfl

theorem homologyToChainClass_hurewiczMap_loopClass (b : X) (p : Path b b) :
    homologyToChainClass X (hurewiczMap b (loopClass p)) = pathClass p := by
  rw [hurewiczMap_loopClass, homologyToChainClass_loopHomologyClass]

/-- Closing an edge using chosen base paths gives the expected chain
formula modulo boundaries. This is the telescoping identity used by the inverse. -/
theorem hurewiczMap_basedLoopClass (b : X) (r : ∀ a : X, Path b a) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (basedLoopClass r p)) =
      pathClass (r x) + pathClass p - pathClass (r y) := by
  change homologyToChainClass X (hurewiczMap b (loopClass (basedLoop r p))) = _
  rw [homologyToChainClass_hurewiczMap_loopClass]
  change pathClass ((r x).trans (p.trans (r y).symm)) = _
  rw [pathClass_trans, pathClass_trans, pathClass_symm]
  abel

end Wikipedia.HopfProblem.FirstHurewicz

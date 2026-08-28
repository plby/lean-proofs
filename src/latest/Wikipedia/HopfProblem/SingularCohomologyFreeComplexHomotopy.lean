import Wikipedia.HopfProblem.SingularCohomologyFreeComplex

/-!
# Duality transports chain homotopies

Reversing a chain homotopy and applying the additive integral module-dual
functor gives a homotopy of the actual cochain pullback maps.  In particular,
a chain homotopy equivalence yields a cochain homotopy equivalence in the
opposite direction, and therefore an isomorphism on actual cohomology.
No freeness or universal-coefficient hypothesis is used in this transport.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree

universe u

variable {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- Precomposition with the components of a chain homotopy. -/
def dualHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (dualMap f) (dualMap g) :=
  integralDualFunctor.mapHomotopy h.op

@[simp] theorem dualHomotopy_hom_apply {f g : K ⟶ L} (h : Homotopy f g)
    (i j : ℕ) (φ : L.X i →ₗ[ℤ] ℤ) :
    ((dualHomotopy h).hom i j).hom φ = φ.comp (h.hom j i).hom := rfl

theorem dualHomotopy_hom_apply_apply {f g : K ⟶ L} (h : Homotopy f g)
    (i j : ℕ) (φ : L.X i →ₗ[ℤ] ℤ) (x : K.X j) :
    ((dualHomotopy h).hom i j).hom φ x = φ ((h.hom j i).hom x) := rfl

/-- Chain-homotopic maps have equal pullbacks on actual integral cohomology. -/
theorem dualHomotopy_homologyMap_eq {f g : K ⟶ L} (h : Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (dualMap f) n =
      HomologicalComplex.homologyMap (dualMap g) n :=
  (dualHomotopy h).homologyMap_eq n

/-- The actual cochain homotopy equivalence contravariantly induced by a
chain homotopy equivalence. -/
def dualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex L) (dualComplex K) where
  hom := dualMap e.hom
  inv := dualMap e.inv
  homotopyHomInvId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy e.homotopyInvHomId
  homotopyInvHomId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy e.homotopyHomInvId

@[simp] theorem dualHomotopyEquiv_hom (e : HomotopyEquiv K L) :
    (dualHomotopyEquiv e).hom = dualMap e.hom := rfl

@[simp] theorem dualHomotopyEquiv_inv (e : HomotopyEquiv K L) :
    (dualHomotopyEquiv e).inv = dualMap e.inv := rfl

/-- The resulting isomorphism between the homology objects of the actual
integral cochain complexes. -/
def dualHomotopyEquiv_homologyIso (e : HomotopyEquiv K L) (n : ℕ) :
    (dualComplex L).homology n ≅ (dualComplex K).homology n :=
  (dualHomotopyEquiv e).toHomologyIso n

@[simp] theorem dualHomotopyEquiv_homologyIso_hom (e : HomotopyEquiv K L) (n : ℕ) :
    (dualHomotopyEquiv_homologyIso e n).hom =
      HomologicalComplex.homologyMap (dualMap e.hom) n := rfl

@[simp] theorem dualHomotopyEquiv_homologyIso_inv (e : HomotopyEquiv K L) (n : ℕ) :
    (dualHomotopyEquiv_homologyIso e n).inv =
      HomologicalComplex.homologyMap (dualMap e.inv) n := rfl

/-- The same genuine cohomology isomorphism as an integral linear equivalence. -/
def dualHomotopyEquiv_homologyEquiv (e : HomotopyEquiv K L) (n : ℕ) :
    (dualComplex L).homology n ≃ₗ[ℤ] (dualComplex K).homology n :=
  (dualHomotopyEquiv_homologyIso e n).toLinearEquiv

@[simp] theorem dualHomotopyEquiv_homologyEquiv_apply (e : HomotopyEquiv K L)
    (n : ℕ) (x : (dualComplex L).homology n) :
    dualHomotopyEquiv_homologyEquiv e n x =
      (HomologicalComplex.homologyMap (dualMap e.hom) n).hom x := rfl

@[simp] theorem dualHomotopyEquiv_homologyEquiv_symm_apply (e : HomotopyEquiv K L)
    (n : ℕ) (x : (dualComplex K).homology n) :
    (dualHomotopyEquiv_homologyEquiv e n).symm x =
      (HomologicalComplex.homologyMap (dualMap e.inv) n).hom x := rfl

end Wikipedia.HopfProblem.SingularCohomologyFree

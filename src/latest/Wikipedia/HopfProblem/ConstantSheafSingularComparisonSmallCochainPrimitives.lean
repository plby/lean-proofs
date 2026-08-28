import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainExtension

/-!
# Actual cocycle and primitive comparison with small cochains

The native cochain homotopies give explicit global representatives and
primitives.  In particular a global cocycle is a coboundary whenever its
restriction to an open cover's small chains is a coboundary.  No abstract
identification of cohomology groups is substituted for these cochain facts.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

namespace SmallCochainComparison

variable {K L : CochainComplex AddCommGrpCat.{0} ℕ}

/-- The original cochain-map square, evaluated at an actual cochain. -/
theorem map_d (f : K ⟶ L) (i j : ℕ) (x : K.X i) :
    L.d i j (f.f i x) = f.f j (K.d i j x) :=
  congrArg (fun k : K.X i ⟶ L.X j => k x) (f.comm i j)

/-- A cochain map takes actual cocycles to actual cocycles. -/
theorem map_cocycle (f : K ⟶ L) (n : ℕ) (x : K.X n)
    (hx : K.d n (n + 1) x = 0) : L.d n (n + 1) (f.f n x) = 0 := by
  rw [map_d, hx, map_zero]

/-- Evaluation of a native cochain homotopy on a positive-degree cocycle. -/
theorem homotopy_on_cocycle {f g : K ⟶ L} (h : Homotopy f g) (n : ℕ)
    (x : K.X (n + 1)) (hx : K.d (n + 1) (n + 2) x = 0) :
    f.f (n + 1) x = L.d n (n + 1) (h.hom (n + 1) n x) + g.f (n + 1) x := by
  have he := h.comm (n + 1)
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at he
  have hx' := congrArg (fun k : K.X (n + 1) ⟶ L.X (n + 1) => k x) he
  change f.f (n + 1) x = h.hom (n + 2) (n + 1) (K.d (n + 1) (n + 2) x) +
    L.d n (n + 1) (h.hom (n + 1) n x) + g.f (n + 1) x at hx'
  simpa only [hx, map_zero, zero_add] using hx'

end SmallCochainComparison

variable {X : Type} [TopologicalSpace X] {ι : Type*}
variable (A : AddCommGrpCat.{0}) (U : ι → Set X)
  (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ)

include hU hcover

/-- A small cocycle is the restriction of a global cocycle up to an actual
small coboundary, with both cochains provided by the native equivalence. -/
theorem smallCochain_cocycle_lift (n : ℕ) (φ : SmallCochains U A (n + 1))
    (hφ : (smallCochainComplex U A).d (n + 1) (n + 2) φ = 0) :
    ∃ ψ : Cochains X A (n + 1),
      (singularCochainComplex X A).d (n + 1) (n + 2) ψ = 0 ∧
      ∃ χ : SmallCochains U A n,
        (smallCochainRestriction A U).f (n + 1) ψ =
          (smallCochainComplex U A).d n (n + 1) χ + φ := by
  let e := smallCochainHomotopyEquiv A U hU hcover
  refine ⟨e.inv.f (n + 1) φ, SmallCochainComparison.map_cocycle e.inv (n + 1) φ hφ,
    e.homotopyInvHomId.hom (n + 1) n φ, ?_⟩
  exact SmallCochainComparison.homotopy_on_cocycle e.homotopyInvHomId n φ hφ

/-- A global cocycle whose small restriction has a primitive has a genuine
global primitive, for every abelian coefficient group. -/
theorem smallCochain_boundary_of_restriction_boundary (n : ℕ)
    (φ : Cochains X A (n + 1))
    (hφ : (singularCochainComplex X A).d (n + 1) (n + 2) φ = 0)
    (χ : SmallCochains U A n)
    (hχ : (smallCochainComplex U A).d n (n + 1) χ =
      (smallCochainRestriction A U).f (n + 1) φ) :
    ∃ ψ : Cochains X A n, (singularCochainComplex X A).d n (n + 1) ψ = φ := by
  let e := smallCochainHomotopyEquiv A U hU hcover
  refine ⟨e.inv.f n χ - e.homotopyHomInvId.hom (n + 1) n φ, ?_⟩
  rw [map_sub, SmallCochainComparison.map_d e.inv n (n + 1) χ, hχ]
  have he := SmallCochainComparison.homotopy_on_cocycle e.homotopyHomInvId n φ hφ
  change e.inv.f (n + 1) ((smallCochainRestriction A U).f (n + 1) φ) =
    (singularCochainComplex X A).d n (n + 1)
      (e.homotopyHomInvId.hom (n + 1) n φ) + φ at he
  rw [he, add_sub_cancel_left]

end Wikipedia.HopfProblem.ConstantSheafSingularComparison

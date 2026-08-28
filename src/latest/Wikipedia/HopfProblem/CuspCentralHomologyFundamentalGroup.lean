import Wikipedia.HopfProblem.CuspCentralHomologyLowDegrees
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.CategoryTheory.Endomorphism

/-!
# The actual fundamental group of the central cusp fibre

The constructed small-radius homotopy equivalence induces an equivalence
of the actual fundamental groupoids. Restricting it to the endomorphism
group of a basepoint gives an isomorphism induced by the genuine central
inclusion. The existing universal-cover marking of the small cusp then
identifies the original central fundamental group with the rank-two
integer deck lattice. No first-homology surrogate is used.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspQuotient CuspRetraction

/-- A homotopy equivalence induces a multiplicative equivalence of the
actual based fundamental groups, through its fundamental-groupoid functor. -/
def homotopyEquivFundamentalGroupEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e.toFun x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

/-- Its forward homomorphism is exactly the map of loops induced by `e`. -/
@[simp] theorem homotopyEquivFundamentalGroupEquiv_toMonoidHom {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) :
    (homotopyEquivFundamentalGroupEquiv e x).toMonoidHom = FundamentalGroup.map e.toFun x :=
  rfl

@[simp] theorem homotopyEquivFundamentalGroupEquiv_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroupEquiv e x γ = FundamentalGroup.map e.toFun x γ := rfl

namespace SmallCentralModel

variable {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {r : ℝ}
    {hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)}

/-- The literal central inclusion at the chosen smaller radius induces
an isomorphism of actual fundamental groups at every original basepoint. -/
def inclusionFundamentalGroupEquiv (M : SmallCentralModel C r hC)
    (x : QuotientCentralFibre C r) :
    FundamentalGroup (QuotientCentralFibre C r) x ≃*
      FundamentalGroup (QuotientSpace C M.radius)
        (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC x) :=
  MulEquiv.ofBijective
    (FundamentalGroup.map
      (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC) x) (by
        rw [← M.inclusion_eq]
        exact (homotopyEquivFundamentalGroupEquiv M.equivalence x).bijective)

@[simp] theorem inclusionFundamentalGroupEquiv_toMonoidHom
    (M : SmallCentralModel C r hC) (x : QuotientCentralFibre C r) :
    (M.inclusionFundamentalGroupEquiv x).toMonoidHom =
      FundamentalGroup.map
        (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC) x := rfl

/-- The actual central fundamental group in the smaller cusp's deck marking. -/
def fundamentalGroupEquiv (M : SmallCentralModel C r hC) (x : QuotientCentralFibre C r) :
    FundamentalGroup (QuotientCentralFibre C r) x ≃* Multiplicative (Fin 2 → ℤ) :=
  (M.inclusionFundamentalGroupEquiv x).trans
    (CuspQuotient.fundamentalGroupEquiv C M.radius M.radius_pos M.radius_lt_one
      M.holomorphic M.smallDrift
      (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC x))

/-- The marking applies the universal-cover marking after the genuine
central-inclusion map of loops; no abelianization intervenes. -/
theorem fundamentalGroupEquiv_inclusion (M : SmallCentralModel C r hC)
    (x : QuotientCentralFibre C r) (γ : FundamentalGroup (QuotientCentralFibre C r) x) :
    M.fundamentalGroupEquiv x γ =
      CuspQuotient.fundamentalGroupEquiv C M.radius M.radius_pos M.radius_lt_one
        M.holomorphic M.smallDrift
        (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC x)
        (FundamentalGroup.map
          (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC) x γ) := rfl

end SmallCentralModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))

/-- The actual fundamental group of the original central cusp fibre is
the rank-two integer group at every basepoint. All small-radius and
homotopy-equivalence data are constructed from the holomorphic input. -/
def centralFundamentalGroupEquiv (x : QuotientCentralFibre C r) :
    FundamentalGroup (QuotientCentralFibre C r) x ≃* Multiplicative (Fin 2 → ℤ) :=
  (smallCentralModel C r hr hC).fundamentalGroupEquiv x

theorem centralFundamentalGroupEquiv_inclusion
    (x : QuotientCentralFibre C r) (γ : FundamentalGroup (QuotientCentralFibre C r) x) :
    let M := smallCentralModel C r hr hC
    centralFundamentalGroupEquiv C r hr hC x γ =
      CuspQuotient.fundamentalGroupEquiv C M.radius M.radius_pos M.radius_lt_one
        M.holomorphic M.smallDrift
        (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC x)
        (FundamentalGroup.map
          (centralIntoSmallerQuotient C r M.radius M.radius_pos M.radius_lt.le hC) x γ) :=
  (smallCentralModel C r hr hC).fundamentalGroupEquiv_inclusion x γ

include hr hC in
theorem central_fundamentalGroup (x : QuotientCentralFibre C r) :
    Nonempty (FundamentalGroup (QuotientCentralFibre C r) x ≃*
      Multiplicative (Fin 2 → ℤ)) :=
  ⟨centralFundamentalGroupEquiv C r hr hC x⟩

end Wikipedia.HopfProblem.CuspCentralHomology

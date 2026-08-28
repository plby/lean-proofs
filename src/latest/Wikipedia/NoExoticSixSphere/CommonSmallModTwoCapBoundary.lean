import Wikipedia.NoExoticSixSphere.CommonSmallModTwoCap

/-!
# The cap boundary identity inside the original overlap

Injectivity of the original overlap-chain inclusion transfers the native
cap boundary formula to the overlap itself. If the input boundary lies
in an annihilated subspace, only the coboundary cap term remains.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SmallRelativeModTwoCochains (Cochain toAbsolute coboundary)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

theorem capInDegree_sub {p q n : ℕ} (h : p + q = n) (α β : Cochain A B p) :
    capInDegree U A V B h (α - β) = capInDegree U A V B h α - capInDegree U A V B h β := by
  apply eq_sub_iff_add_eq.mpr
  rw [← capInDegree_add, sub_add_cancel]

/-- The original common-small inclusion commutes with the native differential. -/
theorem boundary_inclusion (i j : ℕ) (c : (complex U A V B).X i) :
    ((modComplex 2 X).d i j).hom (((inclusion U A V B).f i).hom c) =
      ((inclusion U A V B).f j).hom (((complex U A V B).d i j).hom c) :=
  congrArg (fun m => m.hom c) ((inclusion U A V B).comm i j)

/-- The complete boundary identity holds in the actual overlap chain group. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) :
    ((modComplex 2 (U ∩ V : Set X)).d (q + 1) q).hom
        (capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) α c) =
      capInDegree U A V B (p := p) (q := q) rfl α
          (((complex U A V B).d n (p + q)).hom c) +
        capInDegree U A V B (p := p + 1) (q := q) (n := n) (by omega) (coboundary A B α) c := by
  apply SmallModTwoCap.inclusion_injective (U ∩ V) q
  have hi := congrArg (fun m => m.hom
    (capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) α c))
    ((RelativeCoefficients.inclusion Coefficient (U ∩ V)).comm (q + 1) q)
  apply hi.symm.trans
  apply (congrArg ((modComplex 2 X).d (q + 1) q).hom
    (inclusion_capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) α c)).trans
  apply (ModTwoCapProduct.boundary_capInDegree h (toAbsolute A B p α)
    (((inclusion U A V B).f n).hom c)).trans
  have he₁ := inclusion_capInDegree U A V B (p := p) (q := q) rfl α
    (((complex U A V B).d n (p + q)).hom c)
  have he₂ := inclusion_capInDegree U A V B (p := p + 1) (q := q) (n := n) (by omega)
    (coboundary A B α) c
  rw [boundary_inclusion U A V B n (p + q) c,
    ← SmallRelativeModTwoCochains.toAbsolute_coboundary A B p α]
  exact (congrArg₂ (fun x y => x + y) he₁.symm he₂.symm).trans
    (((RelativeCoefficients.inclusion Coefficient (U ∩ V)).f q).hom.map_add _ _).symm

/-- A boundary in the annihilated piece contributes no cap term, inside the actual overlap. -/
theorem boundary_capInDegree_of_relative_cycle {p q n : ℕ} (h : p + q + 1 = n)
    (α : Cochain A B p) (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (p + q)).hom
        (((complex U A V B).d n (p + q)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (p + q)).hom) :
    ((modComplex 2 (U ∩ V : Set X)).d (q + 1) q).hom
        (capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) α c) =
      capInDegree U A V B (p := p + 1) (q := q) (n := n) (by omega) (coboundary A B α) c := by
  have hz : capInDegree U A V B (p := p) (q := q) rfl α
      (((complex U A V B).d n (p + q)).hom c) = 0 := by
    apply SmallModTwoCap.inclusion_injective (U ∩ V) q
    exact (inclusion_capInDegree U A V B rfl α _).trans
      ((ModTwoCapProduct.capInDegree_eq_zero_of_pullback_zero A rfl (toAbsolute A B p α)
        (SmallRelativeModTwoCochains.pullback_toAbsolute_left A B p α) _ hc).trans
        ((RelativeCoefficients.inclusion Coefficient (U ∩ V)).f q).hom.map_zero.symm)
  exact (boundary_capInDegree U A V B h α c).trans (by rw [hz, zero_add])

/-- Closed small-relative cochains give cycles in the original overlap. -/
theorem cap_is_cycle {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (hα : coboundary A B α = 0) (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (n - 1)).hom
        (((complex U A V B).d n (n - 1)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (n - 1)).hom) :
    ((modComplex 2 (U ∩ V : Set X)).d q (q - 1)).hom (capInDegree U A V B h α c) = 0 := by
  cases q with
  | zero =>
      change ((modComplex 2 (U ∩ V : Set X)).d 0 0).hom _ = 0
      rw [(modComplex 2 (U ∩ V : Set X)).shape 0 0 (by simp)]
      rfl
  | succ q =>
      have hc' : ((inclusion U A V B).f (p + q)).hom
          (((complex U A V B).d n (p + q)).hom c) ∈
        LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f (p + q)).hom := by
        exact (congrArg (fun j => ((inclusion U A V B).f j).hom
          (((complex U A V B).d n j).hom c) ∈
            LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f j).hom)
          (show n - 1 = p + q by omega)).mp hc
      have he := boundary_capInDegree_of_relative_cycle U A V B (p := p) (q := q)
        (n := n) (by omega) α c hc'
      rw [hα, capInDegree_zero, LinearMap.zero_apply] at he
      exact he

end NoExoticSixSphere.CommonSmallModTwoCap

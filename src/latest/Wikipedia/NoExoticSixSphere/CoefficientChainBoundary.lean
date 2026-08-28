import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation

/-!
# Boundary formulas for the native coefficient chains

Evaluate the original simplicial-chain differential on each coefficient
summand. For mod-two coefficients the signs disappear because the
coefficient action is the original action on `ZMod 2`; the native chain
group is not replaced by an assigned vector space.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients

namespace NoExoticSixSphere.CoefficientChains

variable (A : ModuleCat.{0} ℤ) (X : Type) [TopologicalSpace X]

/-- The alternating face formula on an original coefficient summand. -/
theorem boundary_simplex (n : ℕ) (σ : SingularSimplex X (n + 1)) (a : A) :
    ((coefficientComplex A X).d (n + 1) n).hom (simplex A X (n + 1) σ a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplex A X n (σ.comp (simplexFace n i)) a := by
  have h := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := A) (simplexIndex X (n + 1) σ)
  let ev : (A ⟶ ((TopCat.toSSet.obj (TopCat.of X)).chainComplex A).X n) →+
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex A).X n :=
    { toFun := fun f => f.hom a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  rw [map_sum] at he
  simp only [map_zsmul, simplexIndex_face] at he
  exact he

end NoExoticSixSphere.CoefficientChains

namespace NoExoticSixSphere.ModTwoChains

abbrev Coefficient := ModuleCat.of ℤ (ZMod 2)

variable (X : Type) [TopologicalSpace X]

/-- The original mod-two singular chains. -/
abbrev Chains (n : ℕ) := CoefficientChains.Chains Coefficient X n

/-- Negation is the identity on the original coefficient chain group. -/
theorem neg_eq_self (n : ℕ) (c : Chains X n) : -c = c := by
  obtain ⟨f, rfl⟩ := CoefficientChains.fromFinsupp_surjective Coefficient X n c
  have hf : -f = f := by
    ext σ
    exact ZMod.neg_eq_self_mod_two (f σ)
  rw [← map_neg, hf]

theorem add_self_eq_zero (n : ℕ) (c : Chains X n) : c + c = 0 := by
  calc
    c + c = -c + c := congrArg (fun z => z + c) (neg_eq_self X n c).symm
    _ = 0 := neg_add_cancel c

theorem sign_smul_coefficient (k : ℕ) (a : ZMod 2) : (-1 : ℤ) ^ k • a = a := by
  rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    ZMod.neg_eq_self_mod_two, one_pow, one_mul]

/-- The native mod-two boundary is the sum of the original face summands. -/
theorem boundary_simplex (n : ℕ) (σ : SingularSimplex X (n + 1)) (a : ZMod 2) :
    ((modComplex 2 X).d (n + 1) n).hom (CoefficientChains.simplex Coefficient X (n + 1) σ a) =
      ∑ i : Fin (n + 2), CoefficientChains.simplex Coefficient X n
        (σ.comp (simplexFace n i)) a := by
  rw [CoefficientChains.boundary_simplex]
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_zsmul, sign_smul_coefficient]

end NoExoticSixSphere.ModTwoChains

import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsAlgebra
import Mathlib.LinearAlgebra.StdBasis

/-!
# Standard vectors in the binomial coordinate modules

The Pascal decomposition sends each standard coordinate vector to the
corresponding vector in exactly one summand. These are identities between
integral coordinate modules; no homological interpretation is part of their
statements.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

/-- The standard coordinate basis of the binomial module. -/
def binomialCoordinateBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (binomialModule r n) :=
  Pi.basisFun ℤ (Fin (r.choose n))

@[simp] theorem binomialCoordinateBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    binomialCoordinateBasis r n i = Pi.single i 1 :=
  Pi.basisFun_apply ℤ (Fin (r.choose n)) i

@[simp] theorem binomialCoordinateBasis_repr (r n : ℕ) (x : binomialModule r n)
    (i : Fin (r.choose n)) :
    (binomialCoordinateBasis r n).repr x i = x i :=
  Pi.basisFun_repr ℤ (Fin (r.choose n)) x i

/-- A standard vector indexed by the first Pascal block has zero second
component. -/
@[simp] theorem binomialModuleSuccEquiv_single_inl (r n : ℕ)
    (i : Fin (r.choose (n + 1))) :
    binomialModuleSuccEquiv r n
        (Pi.single ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) 1) =
      (Pi.single i 1, 0) := by
  apply Prod.ext
  · funext j
    simp only [binomialModuleSuccEquiv_apply_fst, Pi.single_apply,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq]
  · funext j
    simp only [binomialModuleSuccEquiv_apply_snd, Pi.single_apply,
      Equiv.apply_eq_iff_eq, Sum.inr_ne_inl, if_false,
      Pi.zero_apply]

/-- A standard vector indexed by the second Pascal block has zero first
component. -/
@[simp] theorem binomialModuleSuccEquiv_single_inr (r n : ℕ)
    (i : Fin (r.choose n)) :
    binomialModuleSuccEquiv r n
        (Pi.single ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) 1) =
      (0, Pi.single i 1) := by
  apply Prod.ext
  · funext j
    simp only [binomialModuleSuccEquiv_apply_fst, Pi.single_apply,
      Equiv.apply_eq_iff_eq, Sum.inl_ne_inr, if_false,
      Pi.zero_apply]
  · funext j
    simp only [binomialModuleSuccEquiv_apply_snd, Pi.single_apply,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq]

/-- The degree-zero generator is the unique standard coordinate vector. -/
theorem integerBinomialZeroEquiv_one_single (r : ℕ) (i : Fin (r.choose 0)) :
    integerBinomialZeroEquiv r 1 = Pi.single i 1 := by
  have hsingle : Subsingleton (Fin (r.choose 0)) := by
    rw [Nat.choose_zero_right]
    infer_instance
  funext j
  have hij : i = j := hsingle.elim i j
  subst j
  simp

/-- In top degree the first Pascal block is empty and the top generator lies
entirely in the second block. -/
theorem binomialModuleSuccEquiv_top (n : ℕ) :
    binomialModuleSuccEquiv n n (fun _ => 1) = (0, fun _ => 1) := by
  apply Prod.ext
  · exact binomialModule_eq_zero_of_lt (Nat.lt_succ_self n) _
  · rfl

/-- The top-degree constant generator is the unique standard coordinate
vector. -/
theorem binomialModule_top_one_single (n : ℕ) (i : Fin (n.choose n)) :
    (fun _ : Fin (n.choose n) => (1 : ℤ)) = Pi.single i 1 := by
  have hsingle : Subsingleton (Fin (n.choose n)) := by
    rw [Nat.choose_self]
    infer_instance
  funext j
  have hij : i = j := hsingle.elim i j
  subst j
  simp

end Wikipedia.HopfProblem.PeriodTorusHigherHomology

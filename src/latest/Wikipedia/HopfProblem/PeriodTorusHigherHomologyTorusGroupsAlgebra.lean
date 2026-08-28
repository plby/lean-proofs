import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Binomial coordinate modules

These are integral coordinate modules and their Pascal decomposition, not
definitions of topological homology. In the successor decomposition the
degree-`n + 1` factor precedes the degree-`n` factor.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

/-- The pointwise integral module with `r.choose n` coordinates. -/
abbrev binomialModule (r n : ℕ) := Fin (r.choose n) → ℤ

/-- Pascal's identity as an equivalence of coordinate indices, with the
degree-`n + 1` block first. -/
def binomialPascalIndexEquiv (r n : ℕ) :
    Fin ((r + 1).choose (n + 1)) ≃ Fin (r.choose (n + 1)) ⊕ Fin (r.choose n) :=
  (finCongr ((Nat.choose_succ_succ' r n).trans (Nat.add_comm _ _))).trans
    finSumFinEquiv.symm

/-- Splitting the coordinate module by Pascal's identity. -/
def binomialModuleSuccEquiv (r n : ℕ) :
    binomialModule (r + 1) (n + 1) ≃ₗ[ℤ]
      binomialModule r (n + 1) × binomialModule r n :=
  (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (binomialPascalIndexEquiv r n)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ ℤ)

@[simp] theorem binomialModuleSuccEquiv_apply_fst (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose (n + 1))) :
    (binomialModuleSuccEquiv r n x).1 i =
      x ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) := rfl

@[simp] theorem binomialModuleSuccEquiv_apply_snd (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose n)) :
    (binomialModuleSuccEquiv r n x).2 i =
      x ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) := rfl

/-- The unique degree-zero coordinate identifies the integers with the
degree-zero coordinate module. -/
def integerBinomialZeroEquiv (r : ℕ) : ℤ ≃ₗ[ℤ] binomialModule r 0 :=
  (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (finCongr (Nat.choose_zero_right r)).symm)

@[simp] theorem integerBinomialZeroEquiv_apply (r : ℕ) (z : ℤ)
    (i : Fin (r.choose 0)) : integerBinomialZeroEquiv r z i = z := rfl

/-- Each binomial coordinate module is free over the integers. -/
theorem binomialModule_free (r n : ℕ) : Module.Free ℤ (binomialModule r n) :=
  inferInstance

/-- Each binomial coordinate module is finitely generated over the integers. -/
theorem binomialModule_finite (r n : ℕ) : Module.Finite ℤ (binomialModule r n) :=
  inferInstance

/-- Its integral rank is the indicated binomial coefficient. -/
@[simp] theorem binomialModule_finrank (r n : ℕ) :
    Module.finrank ℤ (binomialModule r n) = r.choose n :=
  Module.finrank_fin_fun ℤ

/-- Above the top degree there are no coordinates. -/
theorem binomialModule_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (binomialModule r n) := by
  change Subsingleton (Fin (r.choose n) → ℤ)
  rw [Nat.choose_eq_zero_of_lt h]
  infer_instance

instance binomialModule_zero_succ_subsingleton (n : ℕ) :
    Subsingleton (binomialModule 0 (n + 1)) :=
  binomialModule_subsingleton_of_lt (Nat.zero_lt_succ n)

/-- In a degree greater than the dimension every coordinate vector is zero. -/
theorem binomialModule_eq_zero_of_lt {r n : ℕ} (h : r < n) (x : binomialModule r n) :
    x = 0 :=
  @Subsingleton.elim (binomialModule r n) (binomialModule_subsingleton_of_lt h) x 0

end Wikipedia.HopfProblem.PeriodTorusHigherHomology

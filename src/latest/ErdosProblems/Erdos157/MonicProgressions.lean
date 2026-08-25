import ErdosProblems.Erdos157.PolynomialCharacters

/-! Exact counts in monic polynomial residue fibers. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def monicResidueFiberEquiv (g : K[X]) (hg : g.Monic) (d : ℕ)
    (hd : g.natDegree ≤ d) (a : AdjoinRoot g) :
    {f : MonicDegreeEq K d // AdjoinRoot.mk g f.1 = a} ≃ MonicDegreeEq K (d - g.natDegree) where
  toFun f := (monicResidueEquiv g hg d hd f.1).2
  invFun Q := ⟨(monicResidueEquiv g hg d hd).symm (a, Q), by
    rw [← monicResidueEquiv_fst g hg d hd]
    exact congrArg Prod.fst ((monicResidueEquiv g hg d hd).apply_symm_apply (a, Q))⟩
  left_inv f := by
    apply Subtype.ext
    apply (monicResidueEquiv g hg d hd).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · rw [monicResidueEquiv_fst]
      exact f.2.symm
    · rfl
  right_inv Q := by
    exact congrArg Prod.snd ((monicResidueEquiv g hg d hd).apply_symm_apply (a, Q))

theorem card_monicResidueFiber (g : K[X]) (hg : g.Monic) (d : ℕ)
    (hd : g.natDegree ≤ d) (a : AdjoinRoot g) :
    Nat.card {f : MonicDegreeEq K d // AdjoinRoot.mk g f.1 = a} =
      Fintype.card K ^ (d - g.natDegree) := by
  rw [Nat.card_congr (monicResidueFiberEquiv g hg d hd a), Nat.card_eq_fintype_card,
    card_monic]

end Erdos157.Elementary.PolynomialCharacters

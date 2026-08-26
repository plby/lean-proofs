import ErdosProblems.Erdos1188.SparseModulusBound

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Parametric near-linear-exponent lower bound
-/

namespace Erdos1188

open scoped BigOperators

/-- All indexed-prime sparse range profiles are counted below the explicit
polynomial-times-polylogarithmic cutoff. -/
theorem primeSparseProfile_count_le_coveringCount (m : ℕ)
    (hm : sparseSeed ≤ m) :
    (∏ i : Fin m,
        (Fintype.card (PrimeSparsePool m i)).choose (nthPrime i.val - 1)) ≤
      coveringCount (sparsePrimeCutoff m) := by
  apply sparseRangeProfile_card_le_coveringCount
    (fun i : Fin m => nthPrime i.val) (nthPrime m) (PrimeSparsePool m)
    (fun i => (nthPrime_prime i.val).two_le) (nthPrime_prime m).two_le
    (sparseNthPrime_pairwise_coprime m)
    (primeSparseClosingFixed m hm) (primeSparseClosingEscape m hm)
    (primeSparseClosing_protects hm) (primeSparseClosingFixed_injective hm)
    (primeSparsePoolSupport m) (sparsePrimeCutoff m)
  intro R c hc
  exact primeSparseSystem_modulus_le_cutoff hm R c hc

/-- Main finite lower bound: independently varying low-product support ranges
at all late coordinates gives exponentially many systems. -/
theorem explicit_sparse_parametric_lower (m : ℕ) (hm : sparseSeed ≤ m) :
    2 ^ sparsePrimeExponent m ≤ coveringCount (sparsePrimeCutoff m) := by
  exact (two_pow_sparsePrimeExponent_le_profile_count m).trans
    (primeSparseProfile_count_le_coveringCount m hm)

end Erdos1188

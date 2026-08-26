/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenKey

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

/-- The auxiliary primes attached to the sixteen indices are distinct. -/
lemma keyAuxPrime16_injective : Function.Injective keyAuxPrime16 := by
  decide +kernel +revert

/-- Every auxiliary prime lies beyond the factorial pre-sieving range. -/
lemma sixteen_lt_keyAuxPrime16 (i : Fin 16) : 16 < keyAuxPrime16 i := by
  decide +kernel +revert

/-- The sixteen adjusted residues are pairwise separated modulo the
auxiliary prime attached to the second residue.  This is the only finite
calculation needed in the affine coprimality argument. -/
lemma keyDelta16_aux_separated (i j : Fin 16) (hij : i ≠ j) :
    ¬(1 + keyDelta16 i ≡ 1 + keyDelta16 j [MOD keyAuxPrime16 j]) := by
  decide +kernel +revert

end Erdos946.SixteenAffine

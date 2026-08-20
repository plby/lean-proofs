import ErdosProblems.Erdos980.NaturalChebotarev.FiniteException
import ErdosProblems.Erdos980.NaturalChebotarev.PNTTransfer
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem
import ErdosProblems.Erdos980.NaturalChebotarev.SplitTransfer.Transfer

/-!
# Natural-density Chebotarev input for Erdős Problem 980

This aggregate exports the unconditional prime ideal theorem for number fields and its
complete-splitting consequence for finite Galois extensions of `ℚ`:

* `PrimeIdealTheorem.primeIdealCount_isEquivalent_natCast_div_log`;
* `SplitTransfer.splitPrimeCount_isEquivalent`.

The second theorem gives the natural density `1 / [L : ℚ]` on the prime-number-theorem
scale, which is the form used for the finite Kummer splitting patterns in Problem 980.
-/

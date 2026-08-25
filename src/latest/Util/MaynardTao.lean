import Util.MaynardTao.Theorem
import Util.MaynardTao.BFT.Result
import Util.MaynardTao.BFT.SinglePrime

/-!
# Unconditional Maynard–Tao theorems

This umbrella module exposes both developments:

* `MaynardTao.maynard_tao`: arbitrarily late prime translates of an admissible
  integer tuple satisfying the explicit exponential size threshold.
* `MaynardBFT.consecutive_primes`: arbitrarily late runs of consecutive primes
  in a coprime residue class, with span at most `q * Cₘ`.

Import `Util.MaynardTao.Theorem` or `Util.MaynardTao.BFT.Result` individually
when only one result is needed. The existing declaration namespaces are
preserved. Neither development imports `ErdosProblems.Axioms`.
-/

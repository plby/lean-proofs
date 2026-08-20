import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.AnalyticAssembly
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.CoefficientLSeries
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.CountingConversion
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.IdealCounting
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.IdealMangoldt
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PoleSubtraction
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.PrimeIdealCounting
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.TauberianAssembly
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WeightedDefs
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WeightedPIT
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.WienerBridge
import ErdosProblems.Erdos980.NaturalChebotarev.PrimeIdealTheorem.ZeroFreeLine

/-!
# Prime ideal theorem infrastructure for Erdős Problem 980

The modules aggregated here develop the natural-density input needed for the completely split
case of Chebotarev.  They include the finite prime-ideal von Mangoldt coefficients, the
Wiener--Ikehara bridge, its inclusive-endpoint assembly, and elementary weighted-to-counting
conversions.  The analytic modules construct the continued Dedekind zeta function's
pole-subtracted logarithmic derivative and prove the zero-free boundary needed for the
Tauberian argument.  `PrimeIdealCounting` concludes the unconditional asymptotic
`#\{𝔭 : N𝔭 ≤ N\} ~ N / log N` for every number field.
-/

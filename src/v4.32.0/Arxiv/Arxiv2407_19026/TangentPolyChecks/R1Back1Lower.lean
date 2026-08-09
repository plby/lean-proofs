import Arxiv.Arxiv2407_19026.TangentPolyChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine


set_option maxHeartbeats 0 in
-- Proof-producing normalization over the full rational grid needs an unbounded heartbeat budget.
set_option maxRecDepth 1000000 in
-- Expanding the recursive affine cover exceeds Lean's default recursion-depth limit.
lemma r1Back1_lower_check :
    checkLowerAffineCover r1Back1T (1 / 100000)
      cfg (387 / 1000) r1Back1Bps = true := by
  norm_num (config := { maxSteps := 10000000 })
    [r1Back1Bps, mediumBreakpoints,
    List.range_eq_range', List.range',
    checkLowerAffineCover, checkLowerBoundAffine1Strict,
    toAffineEnvConst, checkDomainValidAffine,
    evalAffineToInterval?, evalIntervalAffine?,
    LeanCert.Internal.Affine.evalUnchecked,
    r1Back1T, localPoly, horner, r1Back1Cs,
    cfg, z, c, add, mul, neg, sub,
    Expr.sub, Affine.AffineForm.const,
    Affine.AffineForm.add, Affine.AffineForm.mul,
    Affine.AffineForm.neg, Affine.AffineForm.ofInterval,
    Affine.AffineForm.toInterval,
    Affine.AffineForm.deviationBound,
    Affine.AffineForm.sumAbs, Affine.AffineForm.zipWithPad]

end TangentPolyNative
end Arxiv2407_19026

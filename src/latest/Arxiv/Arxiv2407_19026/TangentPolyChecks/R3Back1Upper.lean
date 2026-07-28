import Arxiv.Arxiv2407_19026.TangentPolyChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine

private lemma rat_neg_eq_neg (q : ℚ) : q.neg = -q := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r3Back1_upper_check :
    checkLowerAffineCover (belowOne r3Back1T) (1 / 100000)
      cfg (3 / 8) r3Back1Bps = true := by
  norm_num (config := { maxSteps := 10000000 })
    [r3Back1Bps, mediumBreakpoints,
    List.range_eq_range', List.range',
    checkLowerAffineCover, checkLowerBoundAffine1Strict,
    toAffineEnvConst, checkDomainValidAffine,
    evalAffineToInterval?, evalIntervalAffine?,
    LeanCert.Internal.Affine.evalUnchecked,
    belowOne, r3Back1T, localPoly, horner, r3Back1Cs,
    cfg, z, c, add, mul, neg, sub,
    Expr.sub, Affine.AffineForm.const,
    Affine.AffineForm.add, Affine.AffineForm.mul,
    Affine.AffineForm.neg, Affine.AffineForm.ofInterval,
    Affine.AffineForm.toInterval,
    Affine.AffineForm.deviationBound,
    Affine.AffineForm.sumAbs, Affine.AffineForm.zipWithPad]
  simp only [rat_neg_eq_neg, neg_neg]
  norm_num

end TangentPolyNative
end Arxiv2407_19026

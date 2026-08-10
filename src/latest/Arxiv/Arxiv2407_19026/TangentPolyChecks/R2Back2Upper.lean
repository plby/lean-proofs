import Arxiv.Arxiv2407_19026.TangentPolyChecks.Defs

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine

private lemma rat_neg_eq_neg (q : ℚ) : q.neg = -q := rfl

set_option maxHeartbeats 0 in
-- Proof-producing normalization over the full rational grid needs an unbounded heartbeat budget.
set_option maxRecDepth 1000000 in
-- Expanding the recursive affine cover exceeds Lean's default recursion-depth limit.
lemma r2Back2_upper_check :
    checkLowerAffineCover (belowOne r2Back2T) (1 / 100000)
      cfg (3 / 5) back2Bps = true := by
  norm_num (config := { maxSteps := 10000000 })
    [back2Bps, mediumBreakpoints,
    List.range_eq_range', List.range',
    checkLowerAffineCover, checkLowerBoundAffine1Strict,
    toAffineEnvConst, checkDomainValidAffine,
    evalAffineToInterval?, evalIntervalAffine?,
    LeanCert.Internal.Affine.evalUnchecked,
    belowOne, r2Back2T, localPoly, horner, r2Back2Cs,
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

import Arxiv.Arxiv2407_19026.TangentPolynomialBounds

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine

def r1ForwardBps : List ℚ := mediumBreakpoints 100 169
def r1Back1Bps : List ℚ := mediumBreakpoints 387 213
def r2ForwardBps : List ℚ := mediumBreakpoints 100 168
def r2Back1Bps : List ℚ := mediumBreakpoints 378 222
def r3ForwardBps : List ℚ := mediumBreakpoints 100 168
def r3Back1Bps : List ℚ := mediumBreakpoints 375 225
def back2Bps : List ℚ := mediumBreakpoints 600 400

def belowOne (T : Expr) : Expr := sub (c 1) T

end TangentPolyNative
end Arxiv2407_19026

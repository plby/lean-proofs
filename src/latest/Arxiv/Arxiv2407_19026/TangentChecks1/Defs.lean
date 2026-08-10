import Arxiv.Arxiv2407_19026.TangentNumerics

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine

def β0 : ℚ := 2 / 25
def β1 : ℚ := 9 / 200
def plateauT : Expr := c (99 / 100)

def forwardFine : List ℚ := fineBreakpoints 1000 1690
def forwardMedium : List ℚ := mediumBreakpoints 100 169
def plateauMedium : List ℚ := mediumBreakpoints 269 118
def back1Fine : List ℚ := fineBreakpoints 3870 2130
def back1Medium : List ℚ := mediumBreakpoints 387 213
def back2Fine : List ℚ := fineBreakpoints 6000 4000
def back2Medium : List ℚ := mediumBreakpoints 600 400

end TangentRound1Native
end Arxiv2407_19026

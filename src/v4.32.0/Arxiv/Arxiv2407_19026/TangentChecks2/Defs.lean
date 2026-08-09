import Arxiv.Arxiv2407_19026.TangentNumerics

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine

def β1 : ℚ := 9 / 200
def β2 : ℚ := 33 / 1000
def plateauT : Expr := c (99 / 100)

def forwardFine : List ℚ := fineBreakpoints 1000 1680
def forwardMedium : List ℚ := mediumBreakpoints 100 168
def plateauMedium : List ℚ := mediumBreakpoints 268 110
def back1Fine : List ℚ := fineBreakpoints 3780 2220
def back1Medium : List ℚ := mediumBreakpoints 378 222
def back2Fine : List ℚ := fineBreakpoints 6000 4000
def back2Medium : List ℚ := mediumBreakpoints 600 400

end TangentRound2Native
end Arxiv2407_19026

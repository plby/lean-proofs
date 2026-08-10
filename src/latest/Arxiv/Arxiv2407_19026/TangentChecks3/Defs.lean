import Arxiv.Arxiv2407_19026.TangentNumerics

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine

def β2 : ℚ := 33 / 1000
def β3 : ℚ := 3 / 100
def plateauT : Expr := c (99 / 100)

def forwardFine : List ℚ := fineBreakpoints 1000 1680
def forwardMedium : List ℚ := mediumBreakpoints 100 168
def plateauMedium : List ℚ := mediumBreakpoints 268 107
def back1Fine : List ℚ := fineBreakpoints 3750 2250
def back1Medium : List ℚ := mediumBreakpoints 375 225
def back2Fine : List ℚ := fineBreakpoints 6000 4000
def back2Medium : List ℚ := mediumBreakpoints 600 400

end TangentRound3Native
end Arxiv2407_19026

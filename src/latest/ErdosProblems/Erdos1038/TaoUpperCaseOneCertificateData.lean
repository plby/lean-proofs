import ErdosProblems.Erdos1038.TaoUpperCaseOneCertificateCore

set_option warningAsError false

namespace Erdos1038
noncomputable section

def taoCaseOneInitialIntervals : List RatInterval :=
  uniformRatIntervals (707 / 500) (1 / 1000) 86

def taoCaseOneDirectIntervals : List RatInterval :=
  uniformRatIntervals (3 / 2) (1 / 1000) 200 ++
  uniformRatIntervals (17 / 10) (1 / 1000) 50 ++
  uniformRatIntervals (7 / 4) (1 / 10000) 100 ++
  uniformRatIntervals (44 / 25) (1 / 100000) 200 ++
  uniformRatIntervals (881 / 500) (1 / 100000) 40

end

end Erdos1038


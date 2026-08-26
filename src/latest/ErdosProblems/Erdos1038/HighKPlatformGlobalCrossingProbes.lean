import ErdosProblems.Erdos1038.HighKPlatformCrossingCertificates

/-!
# Whole-range probes for compressed high-`k` crossing certificates

The affine and constant platform regimes each have one monotone negative and
one monotone positive exterior zero.  These exact rational boxes test whether
four branch certificates cover the complete two regimes without per-slab
crossing data.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000

namespace Erdos1038.HighKPlatformGlobalCrossingProbes

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformCrossingCertificates

def logTerms : ℕ := 80
def sqrtSteps : ℕ := 64
def zeroBox : RatInterval := point 0

def affineKBox : RatInterval := ⟨36 / 25, 21 / 10⟩
def affineXmBox : RatInterval :=
  ⟨-641802910676097 / 1000000000000000,
    -528928450561710 / 1000000000000000⟩
def affineXpBox : RatInterval :=
  ⟨1091428751156203 / 1000000000000000,
    1157344632210514 / 1000000000000000⟩

def constantKBox : RatInterval := ⟨21 / 10, 21 / 5⟩
def constantXmBox : RatInterval :=
  ⟨-789424179955935 / 1000000000000000,
    -640884496499893 / 1000000000000000⟩
def constantXpBox : RatInterval :=
  ⟨1031934839326393 / 1000000000000000,
    1133133846533857 / 1000000000000000⟩

def endpointBoxes (side : PlatformCrossingSide)
    (k x : Rat) : Fin 5 → RatInterval :=
  match side with
  | .minus => ![point k, point x, zeroBox, zeroBox, zeroBox]
  | .plus => ![point k, zeroBox, point x, zeroBox, zeroBox]

def envelopeBoxes (side : PlatformCrossingSide)
    (K X : RatInterval) : Fin 5 → RatInterval :=
  match side with
  | .minus => ![K, X, zeroBox, zeroBox, zeroBox]
  | .plus => ![K, zeroBox, X, zeroBox, zeroBox]

def affineMinusEnvelope : Fin 5 → RatInterval :=
  envelopeBoxes .minus affineKBox affineXmBox
def affinePlusEnvelope : Fin 5 → RatInterval :=
  envelopeBoxes .plus affineKBox affineXpBox
def constantMinusEnvelope : Fin 5 → RatInterval :=
  envelopeBoxes .minus constantKBox constantXmBox
def constantPlusEnvelope : Fin 5 → RatInterval :=
  envelopeBoxes .plus constantKBox constantXpBox

def affineMinusSlopeBox : RatInterval :=
  (evalInterval affineMinusEnvelope
    (crossingSlopeE logTerms sqrtSteps .affine .minus)).getD zeroBox
def affinePlusSlopeBox : RatInterval :=
  (evalInterval affinePlusEnvelope
    (crossingSlopeE logTerms sqrtSteps .affine .plus)).getD zeroBox
def constantMinusSlopeBox : RatInterval :=
  (evalInterval constantMinusEnvelope
    (crossingSlopeE logTerms sqrtSteps .constant .minus)).getD zeroBox
def constantPlusSlopeBox : RatInterval :=
  (evalInterval constantPlusEnvelope
    (crossingSlopeE logTerms sqrtSteps .constant .plus)).getD zeroBox

def affineMinusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .affine)
    (rhoE sqrtSteps .affine xmE))
def affinePlusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .affine)
    (rhoE sqrtSteps .affine xpE))
def constantMinusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .constant)
    (rhoE sqrtSteps .constant xmE))
def constantPlusCorrectionE : HighKIntervalExpr 5 :=
  .sub e1 (.mul (rhoZeroE sqrtSteps .constant)
    (rhoE sqrtSteps .constant xpE))

/-! A single midpoint split for the only broad branch whose direct
transverse/slope enclosure is too wide. -/

def affineMidK : Rat := 177 / 100

def affinePlusLeftX : RatInterval :=
  ⟨1091428751156203 / 1000000000000000,
    1142637917473820 / 1000000000000000⟩

def affinePlusRightX : RatInterval :=
  ⟨1142637917473817 / 1000000000000000,
    1157344632210514 / 1000000000000000⟩

def affinePlusLeftK : RatInterval := ⟨affineKBox.lo, affineMidK⟩
def affinePlusRightK : RatInterval := ⟨affineMidK, affineKBox.hi⟩

def affinePlusLeftEnvelope : Fin 5 → RatInterval :=
  envelopeBoxes .plus affinePlusLeftK affinePlusLeftX
def affinePlusRightEnvelope : Fin 5 → RatInterval :=
  envelopeBoxes .plus affinePlusRightK affinePlusRightX

def affinePlusLeftSlopeBox : RatInterval :=
  (evalInterval affinePlusLeftEnvelope
    (crossingSlopeE logTerms sqrtSteps .affine .plus)).getD zeroBox
def affinePlusRightSlopeBox : RatInterval :=
  (evalInterval affinePlusRightEnvelope
    (crossingSlopeE logTerms sqrtSteps .affine .plus)).getD zeroBox

def affinePlusNodeK (i : Fin 9) : Rat :=
  36 / 25 + i * (33 / 400)

def affinePlusNodeXLo : Fin 9 → Rat :=
  ![1091428751156203 / 1000000000000000,
    1111626531329036 / 1000000000000000,
    1125724259865208 / 1000000000000000,
    1135578209993644 / 1000000000000000,
    1142637917473817 / 1000000000000000,
    1147858860197858 / 1000000000000000,
    1151831927612330 / 1000000000000000,
    1154919032079676 / 1000000000000000,
    1157344632210511 / 1000000000000000]

def affinePlusNodeXHi : Fin 9 → Rat :=
  ![1091428751156206 / 1000000000000000,
    1111626531329039 / 1000000000000000,
    1125724259865210 / 1000000000000000,
    1135578209993647 / 1000000000000000,
    1142637917473820 / 1000000000000000,
    1147858860197861 / 1000000000000000,
    1151831927612333 / 1000000000000000,
    1154919032079679 / 1000000000000000,
    1157344632210514 / 1000000000000000]

def affinePlusOctantK (i : Fin 8) : RatInterval :=
  ⟨affinePlusNodeK i.castSucc, affinePlusNodeK i.succ⟩

def affinePlusOctantX (i : Fin 8) : RatInterval :=
  ⟨affinePlusNodeXLo i.castSucc, affinePlusNodeXHi i.succ⟩

def affinePlusOctantEnvelope (i : Fin 8) : Fin 5 → RatInterval :=
  envelopeBoxes .plus (affinePlusOctantK i) (affinePlusOctantX i)

def affinePlusOctantSlopeBox (i : Fin 8) : RatInterval :=
  (evalInterval (affinePlusOctantEnvelope i)
    (crossingSlopeE logTerms sqrtSteps .affine .plus)).getD zeroBox

def affinePlusQuartetK : Fin 4 → RatInterval
  | 0 => ⟨affinePlusNodeK 0, affinePlusNodeK 2⟩
  | 1 => ⟨affinePlusNodeK 2, affinePlusNodeK 4⟩
  | 2 => ⟨affinePlusNodeK 4, affinePlusNodeK 6⟩
  | 3 => ⟨affinePlusNodeK 6, affinePlusNodeK 8⟩

def affinePlusQuartetX : Fin 4 → RatInterval
  | 0 => ⟨affinePlusNodeXLo 0, affinePlusNodeXHi 2⟩
  | 1 => ⟨affinePlusNodeXLo 2, affinePlusNodeXHi 4⟩
  | 2 => ⟨affinePlusNodeXLo 4, affinePlusNodeXHi 6⟩
  | 3 => ⟨affinePlusNodeXLo 6, affinePlusNodeXHi 8⟩

def affinePlusQuartetEnvelope (i : Fin 4) : Fin 5 → RatInterval :=
  envelopeBoxes .plus (affinePlusQuartetK i) (affinePlusQuartetX i)

def affinePlusQuartetSlopeBox (i : Fin 4) : RatInterval :=
  (evalInterval (affinePlusQuartetEnvelope i)
    (crossingSlopeE logTerms sqrtSteps .affine .plus)).getD zeroBox

def affinePlusBoundaryEnvelope (x : Rat) : Fin 5 → RatInterval :=
  envelopeBoxes .plus affineKBox (point x)

def affinePlusRectXNode (j : Fin 5) : Rat :=
  affineXpBox.lo + j * ((affineXpBox.hi - affineXpBox.lo) / 4)

def affinePlusRectX (j : Fin 4) : RatInterval :=
  ⟨affinePlusRectXNode j.castSucc, affinePlusRectXNode j.succ⟩

def affinePlusRectEnvelope (i j : Fin 4) : Fin 5 → RatInterval :=
  envelopeBoxes .plus (affinePlusQuartetK i) (affinePlusRectX j)

def affinePlusRect8XNode (j : Fin 9) : Rat :=
  affineXpBox.lo + j * ((affineXpBox.hi - affineXpBox.lo) / 8)

def affinePlusRect8X (j : Fin 8) : RatInterval :=
  ⟨affinePlusRect8XNode j.castSucc, affinePlusRect8XNode j.succ⟩

def affinePlusRect8Envelope (i j : Fin 8) : Fin 5 → RatInterval :=
  envelopeBoxes .plus (affinePlusOctantK i) (affinePlusRect8X j)

end Erdos1038.HighKPlatformGlobalCrossingProbes

import ErdosProblems.Erdos1038.HighKPlatformIntervalChecker
import ErdosProblems.Erdos1038.KernelDecision
import Mathlib.Analysis.Real.Pi.Bounds

/-! A first exact-rational constant-edge smoke slab. -/

set_option warningAsError false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformIntervalSmoke

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula

def kBox : RatInterval := ⟨5 / 2, 250001 / 100000⟩

def xmBox : RatInterval :=
  ⟨-683501275752737 / 1000000000000000,
    -683500337311906 / 1000000000000000⟩

def xpBox : RatInterval :=
  ⟨1081574488993373 / 1000000000000000,
    1081575237859631 / 1000000000000000⟩

def ellBox : RatInterval :=
  ⟨1834430475762661711090753 / 1000000000000000000000000,
    1834430475762661711090754 / 1000000000000000000000000⟩

def piBox : RatInterval :=
  ⟨314159265358979323846 / 100000000000000000000,
    314159265358979323847 / 100000000000000000000⟩

def boxes : Fin 5 → RatInterval :=
  ![kBox, xmBox, xpBox, ellBox, piBox]

def logTerms : ℕ := 80
def sqrtSteps : ℕ := 64
def trigDoubles : ℕ := 12
def fourierTerms : ℕ := 80

def qCap : Rat := 557 / 200
def rCap : Rat := 1663 / 1000

theorem boxes_ordered : ∀ i, (boxes i).Ordered := by
  intro i
  fin_cases i <;>
    norm_num [boxes, kBox, xmBox, xpBox, ellBox, piBox,
      RatInterval.Ordered]

theorem pi_mem_piBox : piBox.Contains Real.pi := by
  constructor
  · have h := Real.pi_gt_d20.le
    norm_num [piBox] at h ⊢
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num [piBox] at h ⊢
    exact h

theorem api_check : EvalPositive boxes (apiE sqrtSteps .constant) :=
  evalPositive_of_check (by kernel_decide)

theorem qmax_check : EvalPositive boxes (qmaxE sqrtSteps .constant) :=
  evalPositive_of_check (by kernel_decide)

theorem rmax_check : EvalPositive boxes (rmaxE sqrtSteps .constant) :=
  evalPositive_of_check (by kernel_decide)

theorem qcap_check : EvalNegative boxes
    (.sub (qmaxE sqrtSteps .constant) (.rat qCap)) :=
  evalNegative_of_check (by kernel_decide)

theorem rcap_check : EvalNegative boxes
    (.sub (rmaxE sqrtSteps .constant) (.rat rCap)) :=
  evalNegative_of_check (by kernel_decide)

theorem ceff_check : EvalNegative boxes
    (ceffE logTerms sqrtSteps .constant) :=
  evalNegative_of_check (by kernel_decide)

theorem endpoint_check : EvalPositive boxes
    (constantEndpointLowerE logTerms sqrtSteps trigDoubles fourierTerms
      .constant qCap rCap) :=
  evalPositive_of_check (by kernel_decide)

/-- The first positive-width smoke slab, certified solely by exact rational
reduction.  The crossing equations are deliberately hypotheses here; the
separate branch-continuity certificate records what remains to discharge
them from endpoint sign boxes. -/
theorem constant_smoke_slab
    {k xm xp ell : ℝ}
    (hk : kBox.Contains k)
    (hxmBox : xmBox.Contains xm)
    (hxpBox : xpBox.Contains xp)
    (hell : ellBox.Contains ell) :
    PlatformConstantEdgeCalibration k (9 / 5) xm xp
      (-1 / platformExteriorWx k (9 / 5) xm)
      (1 / platformExteriorWx k (9 / 5) xp)
      (platformEffectiveConstant ell k (9 / 5) xm xp
        (-1 / platformExteriorWx k (9 / 5) xm)
        (1 / platformExteriorWx k (9 / 5) xp)) := by
  have hcontains : ∀ i,
      (boxes i).Contains (![k, xm, xp, ell, Real.pi] i) := by
    intro i
    fin_cases i
    · simpa [boxes] using! hk
    · simpa [boxes] using! hxmBox
    · simpa [boxes] using! hxpBox
    · simpa [boxes] using! hell
    · simpa [boxes] using! pi_mem_piBox
  have hxm : xm < highKPlatformEdge .constant k := by
    have := hxmBox.2
    norm_num [xmBox, highKPlatformEdge] at this ⊢
    linarith
  have hxp : xp < highKPlatformEdge .constant k := by
    have := hxpBox.2
    norm_num [xpBox, highKPlatformEdge] at this ⊢
    linarith
  have ha2 : highKPlatformEdge .constant k < 2 := by
    norm_num [highKPlatformEdge]
  have hqCapPos : 0 < (qCap : ℝ) := by norm_num [qCap]
  have hqCapPi : (qCap : ℝ) ≤ Real.pi := by
    norm_num [qCap]
    linarith [Real.pi_gt_three]
  have hrCapPos : 0 < (rCap : ℝ) := by norm_num [rCap]
  have hrCapPi : (rCap : ℝ) ≤ Real.pi := by
    norm_num [rCap]
    linarith [Real.pi_gt_three]
  have hcert := platformConstantEdgeCalibration_of_interval
    (X := boxes) (edge := .constant) (qCap := qCap) (rCap := rCap)
    boxes_ordered hcontains hxm hxp ha2
    (by norm_num [fourierTerms]) hqCapPos hqCapPi hrCapPos hrCapPi
    api_check qmax_check rmax_check qcap_check rcap_check ceff_check
      endpoint_check
  simpa [highKPlatformEdge] using! hcert

end Erdos1038.HighKPlatformIntervalSmoke

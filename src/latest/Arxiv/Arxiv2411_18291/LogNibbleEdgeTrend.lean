import Arxiv.Arxiv2411_18291.LogNibbleEdgeSteps
import Arxiv.Arxiv2411_18291.SmallErrorFrozenEdgeTrend
import Arxiv.Arxiv2411_18291.CliqueRemovalAvailability
import Arxiv.Arxiv2411_18291.NibbleComparisonSequences

/-! # Logarithmic tracking has the required drift on the actual edge process -/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

def logNibbleDegreeUpperComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  logNibbleDegreeUpper k a D (removalDensity k g i)

def logNibbleDegreeLowerComparison (k : ℕ) (a g D : ℝ) (i : ℕ) : ℝ :=
  logNibbleDegreeLower k a D (removalDensity k g i)

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem logNibbleEdge_critical_trends (hqr : r < q) (hk : 3 ≤ q.choose r)
    (hk5 : q.choose r ≤ 5) (H : Finset (Block V q)) (e : Block V r)
    {a g D : ℝ} (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 < D) (i : ℕ)
    (hs : 0 < removalDensity (q.choose r) g (i + 1))
    (hhalf : removalDensity (q.choose r) g i ≤ 2 * removalDensity (q.choose r) g (i + 1))
    (hac : a ≤ ((2 / 5 : ℝ) * removalDensity (q.choose r) g i) ^ (q.choose r))
    (hlarge : 200 * (q.choose r : ℝ) ^ 3 ≤ a ^ 2 * g)
    (hC : ((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1) ≤
      a ^ 2 * D / 100) :
    let p := removalDensity (q.choose r) g i
    let m := nibbleDegreeMain (q.choose r) D p
    let u := logNibbleDegreeError (q.choose r) a D p
    let cu := logNibbleDegreeUpperComparison (q.choose r) a g D
    let cl := logNibbleDegreeLowerComparison (q.choose r) a g D
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      R.Nonempty →
      (∀ f : Block V r, (R.filter fun Q => f.val ⊆ Q.val).Nonempty →
        m - u ≤ ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ m + u) →
      |(R.card : ℝ) - nibbleCliqueMain (q.choose r) g D p| ≤
        logNibbleCliqueError (q.choose r) a g D p →
      (-a ^ 2 * D ≤ frozenEdgeProcess H e cu i ω ∧ frozenEdgeProcess H e cu i ω ≤ 0 →
        (probability r H)[edgeIncrement H e cu i | Filtration.piLE i] ω ≤ 0) ∧
      (0 ≤ frozenEdgeProcess H e cl i ω ∧ frozenEdgeProcess H e cl i ω ≤ a ^ 2 * D →
        0 ≤ (probability r H)[edgeIncrement H e cl i | Filtration.piLE i] ω) := by
  let p := removalDensity (q.choose r) g i
  let cu := logNibbleDegreeUpperComparison (q.choose r) a g D
  let cl := logNibbleDegreeLowerComparison (q.choose r) a g D
  have hstep := removalDensity_difference (q.choose r) g i
  have hsp : removalDensity (q.choose r) g (i + 1) ≤ p := by
    have hh : 0 ≤ (q.choose r : ℝ) / g := by positivity
    dsimp only [p]
    linarith only [hstep, hh]
  have hp := hs.trans_le hsp
  have hp1 := removalDensity_le_one (q.choose r) hg i
  have hk0 : 0 < q.choose r := by omega
  have hkR : (3 : ℝ) ≤ q.choose r := by exact_mod_cast hk
  have P := log_nibble_scalar_conditions hk hk5 hp hp1 ha hac
  obtain ⟨hum, hu2⟩ := P.degree_bounds hD.le
  obtain ⟨hv, hvm⟩ := P.count_bounds hk0 hD.le hg.le hp.le
  have hL := nibbleLogFactor_one_le (q.choose r) hp hp1
  have hu : 0 ≤ logNibbleDegreeError (q.choose r) a D p := by
    unfold logNibbleDegreeError
    positivity
  have hw : 0 ≤ a ^ 2 * D := by positivity
  have hwu : a ^ 2 * D ≤ logNibbleDegreeError (q.choose r) a D p := by
    have hh := mul_le_mul_of_nonneg_right hL hw
    unfold logNibbleDegreeError
    nlinarith only [hh, hw]
  have hcube : 0 ≤ (q.choose r : ℝ) ^ 3 := by positivity
  have hlarge8 : 8 * (q.choose r : ℝ) ^ 3 ≤ a ^ 2 * g := by
    linarith only [hlarge, hcube]
  have hsqcube : (q.choose r : ℝ) ^ 2 ≤ (q.choose r : ℝ) ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ (q.choose r : ℝ) by linarith)
      (sq_nonneg (q.choose r : ℝ))
    nlinarith only [hh]
  have hlarge2 : 200 * (q.choose r : ℝ) ^ 2 ≤ a ^ 2 * g := by
    linarith only [hlarge, hsqcube]
  obtain ⟨_, huneg, hustep, hlabs, hlstep⟩ :=
    logNibbleDegree_step_control hk hg hD.le hs hsp hp1 hhalf hstep P hlarge8
  have hB : 0 ≤ 2 * nibbleEdgeSlope (q.choose r) g D p := by
    unfold nibbleEdgeSlope
    positivity
  have hBw := logNibbleEdgeSlope_le_width hk hg hD.le hp.le hp1 hlarge2
  have hδB : -(cl (i + 1) - cl i) ≤ 2 * nibbleEdgeSlope (q.choose r) g D p :=
    (neg_le_abs _).trans hlabs
  have hcoeff : 3 * ((q.choose r - 1 : ℕ) : ℝ) + 23 / 8 =
      3 * (q.choose r : ℝ) - 1 / 8 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [nibbleEdgeSlope_eq_main_ratio (by omega) hg.ne' hD.ne' hp.ne',
    logNibbleEdgeStepScale_eq hk0 hg.ne' hD.ne' hp.ne'] at hustep hlstep
  have huStep : -(((q.choose r - 1 : ℕ) : ℝ) * nibbleDegreeMain (q.choose r) D p ^ 2 /
      nibbleCliqueMain (q.choose r) g D p) +
      (3 * ((q.choose r - 1 : ℕ) : ℝ) + 23 / 8) * (a ^ 2 * D) *
        nibbleDegreeMain (q.choose r) D p / nibbleCliqueMain (q.choose r) g D p ≤
      cu (i + 1) - cu i := by
    simpa only [hcoeff, mul_div_assoc, mul_assoc, cu, logNibbleDegreeUpperComparison, p]
      using hustep
  have hlStep : cl (i + 1) - cl i ≤
      -(((q.choose r - 1 : ℕ) : ℝ) * nibbleDegreeMain (q.choose r) D p ^ 2 /
        nibbleCliqueMain (q.choose r) g D p) -
      (3 * ((q.choose r - 1 : ℕ) : ℝ) + 23 / 8) * (a ^ 2 * D) *
        nibbleDegreeMain (q.choose r) D p / nibbleCliqueMain (q.choose r) g D p := by
    simpa only [hcoeff, mul_div_assoc, mul_assoc, cl, logNibbleDegreeLowerComparison, p]
      using hlstep
  have hm := (nibbleDegreeMain_pos (k := q.choose r) hD hp).le
  have hh₀ := nibbleCliqueMain_pos hk0 hg hD hp
  filter_upwards [trajectory_support_ae (r := r) H,
    edgeIncrement_condExp_of_removed H e cu i,
    edgeIncrement_condExp_of_removed H e cl i,
    edgeIncrement_nonpos_of_small_error hqr hk5 H e cu i hm hu hw hum hu2 hh₀ hv hvm
      hC huneg huStep,
    edgeIncrement_nonneg_of_small_error hqr hk5 H e cl i hm hu hw hwu hum hu2 hh₀ hv hvm
      hB hBw hδB hlStep] with ω hsupp hremovedu hremovedl hupper hlower
  dsimp only
  intro hR hd hh
  by_cases he : e ∈ cliqueSupport r (trajectoryCliques ω i)
  · exact ⟨fun _ => (hremovedu he).le, fun _ => (hremovedl he).ge⟩
  have huval := frozenEdgeProcess_eq_of_remaining_nonempty H ω hsupp e cu i hR he
  have hlval := frozenEdgeProcess_eq_of_remaining_nonempty H ω hsupp e cl i hR he
  constructor
  · intro hc
    rw [huval] at hc
    change -a ^ 2 * D ≤ _ - (nibbleDegreeMain (q.choose r) D p +
      logNibbleDegreeError (q.choose r) a D p) ∧
      _ - (nibbleDegreeMain (q.choose r) D p + logNibbleDegreeError (q.choose r) a D p) ≤ 0
      at hc
    exact hupper he hR hd hh (by linarith only [hc.1]) (by linarith only [hc.2])
  · intro hc
    rw [hlval] at hc
    change 0 ≤ _ - (nibbleDegreeMain (q.choose r) D p - logNibbleDegreeError (q.choose r) a D p) ∧
      _ - (nibbleDegreeMain (q.choose r) D p - logNibbleDegreeError (q.choose r) a D p) ≤
        a ^ 2 * D at hc
    exact hlower he hR hd hh (by linarith only [hc.1]) (by linarith only [hc.2])

end CliqueRemovalProcess

end Arxiv2411_18291

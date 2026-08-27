import Arxiv.Arxiv2411_18291.NibbleComparisonSequences
import Arxiv.Arxiv2411_18291.FaceCriticalDrift

/-! # A linear face comparison with a constant error envelope -/

noncomputable section

namespace Arxiv2411_18291

def nibbleFaceUpper (k : ℕ) (a n F p : ℝ) : ℝ := p * F + 128 * (k : ℝ) * a * n

def nibbleFaceUpperComparison (k : ℕ) (a g n F : ℝ) (i : ℕ) : ℝ :=
  nibbleFaceUpper k a n F (removalDensity k g i)

theorem nibbleFaceUpperComparison_increment (k : ℕ) (a g n F : ℝ) (i : ℕ) :
    nibbleFaceUpperComparison k a g n F (i + 1) - nibbleFaceUpperComparison k a g n F i =
      -(k : ℝ) * F / g := by
  simp only [nibbleFaceUpperComparison, nibbleFaceUpper, removalDensity_succ]
  ring

theorem nibbleFaceUpper_le_density (k : ℕ) {a n F p : ℝ}
    (hn : 0 ≤ n) (hp : 0 ≤ p) (hFn : F ≤ n) (hap : a ≤ p) :
    nibbleFaceUpper k a n F p ≤ (1 + 128 * (k : ℝ)) * p * n := by
  have hF := mul_le_mul_of_nonneg_left hFn hp
  have ha := mul_le_mul_of_nonneg_right hap
    (mul_nonneg (by positivity : 0 ≤ 128 * (k : ℝ)) hn)
  unfold nibbleFaceUpper
  nlinarith only [hF, ha]

theorem NibbleComparisonParameters.face_upper_drift {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) {p n F d h : ℝ}
    (hp : p₀ ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hF : 0 ≤ F) (hFn : F ≤ n)
    (hdn : d ≤ n)
    (hh : |h - nibbleCliqueMain k g D p| ≤ nibbleCliqueError k a g D p)
    (hcritical : nibbleFaceUpper k a n F p - a * n ≤ d) :
    -(d * (nibbleDegreeMain k D p - nibbleDegreeError k a D p) / h) +
      (k : ℝ) * F / g ≤ 0 := by
  have hk : 0 < k := by have h := P.rank; omega
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hp0 := P.floor_pos.trans_le hp
  obtain ⟨hm, hu, _, _, _, _, _, hh₀, hvhalf, _, _⟩ := P.edge_conditions hp hp1
  have huBound := nibbleDegreeError_le_scaled_main hk P.error_pos.le P.degree_pos hp0
    (P.power_bound hp)
  have hvBound := nibbleCliqueError_le_scaled_main hk P.error_pos.le P.graph_pos
    P.degree_pos hp0 (P.power_bound hp) (P.denominator_bound hp)
  have habs := abs_le.mp hh
  have hhpos : 0 < h := by linarith only [habs.1, hvhalf, hh₀]
  have hhBound : h ≤ (1 + a) * nibbleCliqueMain k g D p := by
    nlinarith only [habs.2, hvBound]
  have hcoeff : 16 * (k : ℝ) + 2 ≤ 128 * k := by linarith only [hkR]
  have hcoeff' := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg P.error_pos.le hn)
  have hcrit : p * F + (16 * (k : ℝ) + 1) * a * n ≤ d := by
    unfold nibbleFaceUpper at hcritical
    nlinarith only [hcritical, hcoeff']
  have hyp : p * F ≤ F := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hF
  have hyn : p * F ≤ n := hyp.trans hFn
  have hloss := face_loss_lower_of_relative_errors hm.le hu hhpos hh₀ P.error_pos.le hn
    (mul_nonneg hp0.le hF) hyn hdn hcrit huBound hhBound
  have heq : nibbleDegreeMain k D p / nibbleCliqueMain k g D p * (p * F) =
      (k : ℝ) * F / g := by
    rw [nibbleDegreeMain_clique_ratio hk P.graph_pos.ne' P.degree_pos.ne' hp0.ne']
    field_simp
  rw [heq] at hloss
  linarith only [hloss]

end Arxiv2411_18291

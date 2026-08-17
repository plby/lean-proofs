import ErdosProblems.Erdos223.Basic

open Metric
open scoped RealInnerProductSpace SimpleGraph

namespace Erdos223.GenericArc

noncomputable section

def point2 (x y : ℝ) : Point 2 := !₂[x, y]

lemma inner_eq_coordinates (u v : Point 2) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_eq_coordinates (u : Point 2) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coordinates]
  ring

lemma dist_point2_sq (x₁ y₁ x₂ y₂ : ℝ) :
    dist (point2 x₁ y₁) (point2 x₂ y₂) ^ 2 =
      (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [real_inner_self_eq_norm_sq, norm_sq_eq_coordinates]
  simp [point2]

def gamma (t : ℝ) : Point 2 :=
  point2 ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))

lemma norm_gamma_sq (t : ℝ) : ‖gamma t‖ ^ 2 = 1 := by
  rw [norm_sq_eq_coordinates]
  simp [gamma, point2]
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

lemma dist_gamma_sq (s t : ℝ) :
    dist (gamma s) (gamma t) ^ 2 =
      4 * (t - s) ^ 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by
  rw [gamma, gamma, dist_point2_sq]
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hs, ht]
  ring

lemma gamma_injective_on_unit {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h : gamma s = gamma t) : s = t := by
  have hc := congrArg (fun z : Point 2 ↦ z 1) h
  simp [gamma, point2] at hc
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hs, ht] at hc
  have hfactor : (s - t) * (1 - s * t) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hst | hprod
  · linarith
  · have hst1 : s = 1 ∧ t = 1 := by
      have : s * t = 1 := by linarith
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs1) ht0,
        mul_nonneg (sub_nonneg.mpr ht1) hs0]
    linarith

def arcEnd (r : ℝ) : ℝ := (Real.sqrt (4 * r ^ 2 - 1))⁻¹

lemma half_lt_inv_sqrt_two : (1 : ℝ) / 2 < 1 / Real.sqrt 2 := by
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.2 (by norm_num))]
  simpa using (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).2 (by norm_num)

lemma arcEnd_pos {r : ℝ} (hr : 1 / 2 < r) : 0 < arcEnd r := by
  unfold arcEnd
  apply inv_pos.mpr (Real.sqrt_pos.2 ?_)
  nlinarith

lemma arcEnd_le_one {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) : arcEnd r ≤ 1 := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hr2 : 1 / 2 ≤ r ^ 2 := by
    have hinv : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      field_simp [hspos.ne']
      nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hrpos.le (by positivity : 0 ≤ (1 / Real.sqrt 2 : ℝ)))
    nlinarith
  have hrad : 1 ≤ 4 * r ^ 2 - 1 := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt (4 * r ^ 2 - 1) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 4 * r ^ 2 - 1 by linarith)
    have hsn := Real.sqrt_nonneg (4 * r ^ 2 - 1)
    nlinarith
  unfold arcEnd
  exact (inv_le_one₀ (by linarith)).2 hsqrt

lemma endpoint_equation {r : ℝ} (hr : 1 / 2 < r) :
    4 * r ^ 2 * arcEnd r ^ 2 / (1 + arcEnd r ^ 2) = 1 := by
  have hrad : 0 < 4 * r ^ 2 - 1 := by nlinarith
  have hsqrt : Real.sqrt (4 * r ^ 2 - 1) ^ 2 = 4 * r ^ 2 - 1 :=
    Real.sq_sqrt hrad.le
  unfold arcEnd
  rw [inv_pow, hsqrt]
  field_simp
  ring

def parameter (r : ℝ) {b : ℕ} (hb : 2 ≤ b) (i : Fin b) : ℝ :=
  (i : ℝ) / ((b - 1 : ℕ) : ℝ) * arcEnd r

lemma parameter_nonneg {r : ℝ} (hr : 1 / 2 < r) {b : ℕ} (hb : 2 ≤ b)
    (i : Fin b) : 0 ≤ parameter r hb i := by
  unfold parameter
  exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (arcEnd_pos hr).le

lemma parameter_le_end {r : ℝ} (hr : 1 / 2 < r) {b : ℕ} (hb : 2 ≤ b)
    (i : Fin b) : parameter r hb i ≤ arcEnd r := by
  have hd : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - 1 by omega)
  have hi : (i : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pred_of_lt i.isLt
  unfold parameter
  have hfrac : (i : ℝ) / ((b - 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hd).2 hi
  nlinarith [arcEnd_pos hr]

lemma parameter_injective {r : ℝ} (hr : 1 / 2 < r) {b : ℕ} (hb : 2 ≤ b) :
    Function.Injective (@parameter r b hb) := by
  intro i j h
  have hd : (((b - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show b - 1 ≠ 0 by omega)
  have he : arcEnd r ≠ 0 := (arcEnd_pos hr).ne'
  unfold parameter at h
  apply Fin.ext
  have hc : (i : ℝ) = j := by
    apply (div_left_inj' hd).mp
    apply mul_right_cancel₀ he
    exact h
  exact_mod_cast hc

def arcPoint (r : ℝ) {b : ℕ} (hb : 2 ≤ b) (i : Fin b) : Point 2 :=
  r • gamma (parameter r hb i)

lemma arcPoint_injective {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) : Function.Injective (@arcPoint r b hb) := by
  have hrhalf : 1 / 2 < r := half_lt_inv_sqrt_two.trans_le hr
  intro i j h
  have hr0 : r ≠ 0 := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hrhalf).ne'
  have hg : gamma (parameter r hb i) = gamma (parameter r hb j) := by
    exact (smul_right_injective (Point 2) hr0) h
  apply parameter_injective hrhalf hb
  apply gamma_injective_on_unit
  · exact parameter_nonneg hrhalf hb i
  · exact (parameter_le_end hrhalf hb i).trans (arcEnd_le_one hr)
  · exact parameter_nonneg hrhalf hb j
  · exact (parameter_le_end hrhalf hb j).trans (arcEnd_le_one hr)
  · exact hg

lemma norm_arcPoint_sq {r : ℝ} (hr : 0 < r) {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    ‖arcPoint r hb i‖ ^ 2 = r ^ 2 := by
  rw [arcPoint, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow, norm_gamma_sq]
  ring

lemma dist_arcPoint_sq {r : ℝ} (hr : 0 < r) {b : ℕ} (hb : 2 ≤ b) (i j : Fin b) :
    dist (arcPoint r hb i) (arcPoint r hb j) ^ 2 = r ^ 2 *
      (4 * (parameter r hb j - parameter r hb i) ^ 2 /
        ((1 + parameter r hb i ^ 2) * (1 + parameter r hb j ^ 2))) := by
  rw [arcPoint, arcPoint, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr,
    mul_pow, dist_gamma_sq]

lemma chord_fraction_le_endpoint {r : ℝ} (hr : 1 / 2 < r)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ arcEnd r) :
    4 * r ^ 2 * (t - s) ^ 2 / ((1 + s ^ 2) * (1 + t ^ 2)) ≤ 1 := by
  let T := arcEnd r
  have hT : 0 ≤ T := (arcEnd_pos hr).le
  have ht0 : 0 ≤ t := hs.trans hst
  have hsqst : (t - s) ^ 2 ≤ t ^ 2 * (1 + s ^ 2) := by
    have haux : 0 ≤ s * (t ^ 2 * s + 2 * t - s) := by
      have hinner : 0 ≤ t ^ 2 * s + 2 * t - s := by
        nlinarith [mul_nonneg (sq_nonneg t) hs]
      exact mul_nonneg hs hinner
    nlinarith
  have htt : t ^ 2 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - t)]
  have hfrac : t ^ 2 * (1 + T ^ 2) ≤ T ^ 2 * (1 + t ^ 2) := by nlinarith
  have hchain : (t - s) ^ 2 * (1 + T ^ 2) ≤
      T ^ 2 * ((1 + s ^ 2) * (1 + t ^ 2)) := calc
    _ ≤ (t ^ 2 * (1 + s ^ 2)) * (1 + T ^ 2) :=
      mul_le_mul_of_nonneg_right hsqst (by positivity)
    _ = (1 + s ^ 2) * (t ^ 2 * (1 + T ^ 2)) := by ring
    _ ≤ (1 + s ^ 2) * (T ^ 2 * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by ring
  have hden1 : 0 < (1 + s ^ 2) * (1 + t ^ 2) := by positivity
  have hden2 : 0 < 1 + T ^ 2 := by positivity
  have hmul : 0 ≤ 4 * r ^ 2 := by positivity
  calc
    _ ≤ 4 * r ^ 2 * T ^ 2 / (1 + T ^ 2) := by
      rw [div_le_div_iff₀ hden1 hden2]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hchain hmul
    _ = 1 := by simpa [T] using endpoint_equation hr

lemma dist_arcPoint_le_one {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) (i j : Fin b) :
    dist (arcPoint r hb i) (arcPoint r hb j) ≤ 1 := by
  have hrhalf : 1 / 2 < r := half_lt_inv_sqrt_two.trans_le hr
  have hrpos : 0 < r := (by linarith)
  rcases le_total (parameter r hb i) (parameter r hb j) with h | h
  · have hsq := dist_arcPoint_sq hrpos hb i j
    have hfrac := chord_fraction_le_endpoint hrhalf
      (parameter_nonneg hrhalf hb i) h (parameter_le_end hrhalf hb j)
    have hsquare : dist (arcPoint r hb i) (arcPoint r hb j) ^ 2 ≤ 1 := by
      calc
        _ = r ^ 2 * (4 * (parameter r hb j - parameter r hb i) ^ 2 /
            ((1 + parameter r hb i ^ 2) * (1 + parameter r hb j ^ 2))) := hsq
        _ = 4 * r ^ 2 * (parameter r hb j - parameter r hb i) ^ 2 /
            ((1 + parameter r hb i ^ 2) * (1 + parameter r hb j ^ 2)) := by ring
        _ ≤ 1 := hfrac
    have hd := dist_nonneg (x := arcPoint r hb i) (y := arcPoint r hb j)
    nlinarith
  · rw [dist_comm]
    have hsq := dist_arcPoint_sq hrpos hb j i
    have hfrac := chord_fraction_le_endpoint hrhalf
      (parameter_nonneg hrhalf hb j) h (parameter_le_end hrhalf hb i)
    have hsquare : dist (arcPoint r hb j) (arcPoint r hb i) ^ 2 ≤ 1 := by
      calc
        _ = r ^ 2 * (4 * (parameter r hb i - parameter r hb j) ^ 2 /
            ((1 + parameter r hb j ^ 2) * (1 + parameter r hb i ^ 2))) := hsq
        _ = 4 * r ^ 2 * (parameter r hb i - parameter r hb j) ^ 2 /
            ((1 + parameter r hb j ^ 2) * (1 + parameter r hb i ^ 2)) := by ring
        _ ≤ 1 := hfrac
    have hd := dist_nonneg (x := arcPoint r hb j) (y := arcPoint r hb i)
    nlinarith

lemma parameter_zero {r : ℝ} {b : ℕ} (hb : 2 ≤ b) :
    parameter r hb (⟨0, by omega⟩ : Fin b) = 0 := by simp [parameter]

lemma parameter_last {r : ℝ} {b : ℕ} (hb : 2 ≤ b) :
    parameter r hb (⟨b - 1, by omega⟩ : Fin b) = arcEnd r := by
  have hd : (((b - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show b - 1 ≠ 0 by omega)
  simp [parameter, hd]

lemma dist_arc_endpoints_eq_one {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) :
    dist (arcPoint r hb ⟨0, by omega⟩) (arcPoint r hb ⟨b - 1, by omega⟩) = 1 := by
  have hrhalf : 1 / 2 < r := half_lt_inv_sqrt_two.trans_le hr
  have hrpos : 0 < r := by linarith
  have hsq := dist_arcPoint_sq hrpos hb
    (⟨0, by omega⟩ : Fin b) (⟨b - 1, by omega⟩ : Fin b)
  rw [parameter_zero, parameter_last] at hsq
  have hsquare : dist (arcPoint r hb ⟨0, by omega⟩)
      (arcPoint r hb ⟨b - 1, by omega⟩) ^ 2 = 1 := calc
    _ = r ^ 2 * (4 * arcEnd r ^ 2 / (1 + arcEnd r ^ 2)) := by simpa using hsq
    _ = 4 * r ^ 2 * arcEnd r ^ 2 / (1 + arcEnd r ^ 2) := by ring
    _ = 1 := endpoint_equation hrhalf
  have hd := dist_nonneg (x := arcPoint r hb ⟨0, by omega⟩)
    (y := arcPoint r hb ⟨b - 1, by omega⟩)
  nlinarith

def configuration (r : ℝ) {b : ℕ} (hb : 2 ≤ b) : Finset (Point 2) :=
  Finset.univ.image (arcPoint r hb)

lemma card_configuration {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) : (configuration r hb).card = b := by
  rw [configuration, Finset.card_image_iff.mpr (arcPoint_injective hr hb).injOn]
  simp

lemma mem_configuration {r : ℝ} {b : ℕ} (hb : 2 ≤ b) (i : Fin b) :
    arcPoint r hb i ∈ configuration r hb := by simp [configuration]

lemma on_circle {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) :
    ∀ y ∈ configuration r hb, dist y 0 = r := by
  rintro y hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
  rw [dist_zero_right]
  have hrpos : 0 < r := by linarith [half_lt_inv_sqrt_two]
  have hs := norm_arcPoint_sq hrpos hb i
  nlinarith [norm_nonneg (arcPoint r hb i)]

lemma isDiameterOne_configuration {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) : IsDiameterOne (configuration r hb) := by
  rw [isDiameterOne_iff]
  constructor
  · simp only [configuration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact dist_arcPoint_le_one hr hb i j
  · exact ⟨arcPoint r hb ⟨0, by omega⟩, mem_configuration hb _,
      arcPoint r hb ⟨b - 1, by omega⟩, mem_configuration hb _,
      dist_arc_endpoints_eq_one hr hb⟩

lemma one_le_count {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {b : ℕ} (hb : 2 ≤ b) : 1 ≤ diameterPairCount (configuration r hb) := by
  rw [diameterPairCount]
  apply Finset.one_le_card.mpr
  refine ⟨s(⟨arcPoint r hb ⟨0, by omega⟩, mem_configuration hb _⟩,
    ⟨arcPoint r hb ⟨b - 1, by omega⟩, mem_configuration hb _⟩), ?_⟩
  rw [SimpleGraph.mem_edgeFinset]
  exact dist_arc_endpoints_eq_one hr hb

end
end Erdos223.GenericArc

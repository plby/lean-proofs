/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos223.Basic

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223

noncomputable section

private def cross (u v : Point 2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

private lemma inner_eq_coordinates (u v : Point 2) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma norm_sq_eq_coordinates (u : Point 2) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coordinates]
  ring

private lemma cross_self (u : Point 2) : cross u u = 0 := by
  simp [cross]
  ring

private lemma cross_antisymm (u v : Point 2) : cross u v = -cross v u := by
  simp [cross]
  ring

private lemma cross_add_right (u v w : Point 2) :
    cross u (v + w) = cross u v + cross u w := by
  simp [cross]
  ring

private lemma cross_smul_right (u v : Point 2) (a : ℝ) :
    cross u (a • v) = a * cross u v := by
  simp [cross]
  ring

private lemma cross_add_left (u v w : Point 2) :
    cross (u + v) w = cross u w + cross v w := by
  simp [cross]
  ring

private lemma cross_smul_left (u v : Point 2) (a : ℝ) :
    cross (a • u) v = a * cross u v := by
  simp [cross]
  ring

private def point2 (x y : ℝ) : Point 2 := !₂[x, y]

private lemma norm_point2_sq (x y : ℝ) :
    ‖point2 x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [norm_sq_eq_coordinates]
  simp [point2]

private lemma dist_point2_sq (x₁ y₁ x₂ y₂ : ℝ) :
    dist (point2 x₁ y₁) (point2 x₂ y₂) ^ 2 =
      (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [dist_eq_norm, norm_sq_eq_coordinates]
  simp [point2]

private def gamma (t : ℝ) : Point 2 :=
  point2 ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))

private lemma norm_gamma (t : ℝ) : ‖gamma t‖ = 1 := by
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  have hsq := norm_point2_sq ((1 - t ^ 2) / (1 + t ^ 2))
    (2 * t / (1 + t ^ 2))
  have hexpr :
      ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 +
          (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
    field_simp [hd]
    ring
  have hnormsq : ‖gamma t‖ ^ 2 = 1 := by
    rw [show gamma t = point2 ((1 - t ^ 2) / (1 + t ^ 2))
      (2 * t / (1 + t ^ 2)) by rfl, hsq, hexpr]
  nlinarith [norm_nonneg (gamma t)]

private lemma dist_gamma_sq (s t : ℝ) :
    dist (gamma s) (gamma t) ^ 2 =
      4 * (t - s) ^ 2 / ((1 + s ^ 2) * (1 + t ^ 2)) := by
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  rw [gamma, gamma, dist_point2_sq]
  field_simp [hs, ht]
  ring

private lemma dist_gamma_le_one {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 3 * t ^ 2 ≤ 1) :
    dist (gamma s) (gamma t) ≤ 1 := by
  have hden : 0 < (1 + s ^ 2) * (1 + t ^ 2) := by positivity
  have hpoly : 4 * (t - s) ^ 2 ≤ (1 + s ^ 2) * (1 + t ^ 2) := by
    have haux : 0 ≤ s * (8 * t - s * (3 - t ^ 2)) := by
      have : 0 ≤ 8 * t - s * (3 - t ^ 2) := by
        nlinarith [sq_nonneg (t - s)]
      positivity
    nlinarith [sq_nonneg s, sq_nonneg t]
  have hsq : dist (gamma s) (gamma t) ^ 2 ≤ 1 := by
    rw [dist_gamma_sq]
    exact (div_le_one hden).2 hpoly
  have hn : 0 ≤ dist (gamma s) (gamma t) := dist_nonneg
  nlinarith

private lemma gamma_injective_on_arc {s t : ℝ}
    (hs : 0 ≤ s) (hs' : 3 * s ^ 2 ≤ 1)
    (ht : 0 ≤ t) (ht' : 3 * t ^ 2 ≤ 1)
    (h : gamma s = gamma t) : s = t := by
  have hc := congrArg (fun z : Point 2 ↦ z 1) h
  simp [gamma, point2] at hc
  have hds : 1 + s ^ 2 ≠ 0 := by positivity
  have hdt : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hds, hdt] at hc
  have hst : s * t < 1 := by
    nlinarith [sq_nonneg (s - t)]
  have : (s - t) * (1 - s * t) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp this with hst0 | hprod
  · linarith
  · nlinarith

private def arcEnd : ℝ := Real.sqrt 3 / 3

private lemma arcEnd_pos : 0 < arcEnd := by
  have : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  exact div_pos this (by norm_num)

private lemma three_mul_arcEnd_sq : 3 * arcEnd ^ 2 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  rw [arcEnd]
  nlinarith

private def arcParameter {m : ℕ} (hm : 1 < m) (i : Fin m) : ℝ :=
  (i : ℝ) / ((m - 1 : ℕ) : ℝ) * arcEnd

private lemma arcParameter_nonneg {m : ℕ} (hm : 1 < m) (i : Fin m) :
    0 ≤ arcParameter hm i := by
  have hi : 0 ≤ (i : ℝ) := by positivity
  have hd : 0 < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_iff_lt.2 hm
  exact mul_nonneg (div_nonneg hi hd.le) arcEnd_pos.le

private lemma arcParameter_le_end {m : ℕ} (hm : 1 < m) (i : Fin m) :
    arcParameter hm i ≤ arcEnd := by
  have hd : 0 < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_iff_lt.2 hm
  have hi : (i : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_pred_of_lt i.isLt
  rw [arcParameter]
  have : (i : ℝ) / ((m - 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hd).2 hi
  nlinarith [arcEnd_pos.le]

private lemma arcParameter_sq_le {m : ℕ} (hm : 1 < m) (i : Fin m) :
    3 * arcParameter hm i ^ 2 ≤ 1 := by
  have h0 := arcParameter_nonneg hm i
  have hle := arcParameter_le_end hm i
  have he := three_mul_arcEnd_sq
  nlinarith [sq_nonneg (arcParameter hm i - arcEnd)]

private lemma arcParameter_injective {m : ℕ} (hm : 1 < m) :
    Function.Injective (arcParameter hm) := by
  intro i j hij
  have hd : (((m - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hm
  have he : arcEnd ≠ 0 := ne_of_gt arcEnd_pos
  have hc : (i : ℝ) = (j : ℝ) := by
    apply (div_left_inj' hd).mp
    apply mul_right_cancel₀ he
    simpa only [arcParameter] using hij
  exact Fin.ext (by exact_mod_cast hc)

private def rimPoint {m : ℕ} (hm : 1 < m) (i : Fin m) : Point 2 :=
  gamma (arcParameter hm i)

private lemma rimPoint_injective {m : ℕ} (hm : 1 < m) :
    Function.Injective (rimPoint hm) := by
  intro i j hij
  apply arcParameter_injective hm
  exact gamma_injective_on_arc
    (arcParameter_nonneg hm i) (arcParameter_sq_le hm i)
    (arcParameter_nonneg hm j) (arcParameter_sq_le hm j) hij

private def rimEmbedding {m : ℕ} (hm : 1 < m) : Fin m ↪ Point 2 where
  toFun := rimPoint hm
  inj' := rimPoint_injective hm

private noncomputable def planeConfiguration (n : ℕ) (hn : 3 ≤ n) :
    Finset (Point 2) := by
  let m := n - 1
  have hm : 1 < m := by omega
  exact insert 0 (Finset.univ.map (rimEmbedding hm))

private lemma zero_not_mem_rim {m : ℕ} (hm : 1 < m) :
    (0 : Point 2) ∉ Finset.univ.map (rimEmbedding hm) := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_map.mp h
  have hn := norm_gamma (arcParameter hm i)
  change rimPoint hm i = 0 at hi
  change ‖rimPoint hm i‖ = 1 at hn
  rw [hi] at hn
  simpa using hn

private lemma card_planeConfiguration (n : ℕ) (hn : 3 ≤ n) :
    (planeConfiguration n hn).card = n := by
  let m := n - 1
  have hm : 1 < m := by omega
  change (insert 0 (Finset.univ.map (rimEmbedding hm))).card = n
  rw [Finset.card_insert_of_notMem (zero_not_mem_rim hm)]
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  omega

private lemma rim_mem_planeConfiguration (n : ℕ) (hn : 3 ≤ n)
    (i : Fin (n - 1)) :
    rimPoint (show 1 < n - 1 by omega) i ∈ planeConfiguration n hn := by
  change rimPoint (show 1 < n - 1 by omega) i ∈
    insert 0 (Finset.univ.map (rimEmbedding (show 1 < n - 1 by omega)))
  exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private lemma zero_mem_planeConfiguration (n : ℕ) (hn : 3 ≤ n) :
    (0 : Point 2) ∈ planeConfiguration n hn := by
  change (0 : Point 2) ∈
    insert 0 (Finset.univ.map (rimEmbedding (show 1 < n - 1 by omega)))
  exact Finset.mem_insert_self _ _

private lemma dist_zero_rim {m : ℕ} (hm : 1 < m) (i : Fin m) :
    dist (0 : Point 2) (rimPoint hm i) = 1 := by
  rw [dist_zero_left, rimPoint, norm_gamma]

private lemma dist_rim_le_one {m : ℕ} (hm : 1 < m) (i j : Fin m) :
    dist (rimPoint hm i) (rimPoint hm j) ≤ 1 := by
  rcases le_total (arcParameter hm i) (arcParameter hm j) with hij | hji
  · exact dist_gamma_le_one (arcParameter_nonneg hm i) hij (arcParameter_sq_le hm j)
  · rw [dist_comm]
    exact dist_gamma_le_one (arcParameter_nonneg hm j) hji (arcParameter_sq_le hm i)

private lemma isDiameterOne_planeConfiguration (n : ℕ) (hn : 3 ≤ n) :
    IsDiameterOne (planeConfiguration n hn) := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    rw [planeConfiguration] at hx hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · simp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
      exact (dist_zero_rim (show 1 < n - 1 by omega) j).le
    · obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      rw [dist_comm]
      exact (dist_zero_rim (show 1 < n - 1 by omega) i).le
    · obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
      exact dist_rim_le_one (show 1 < n - 1 by omega) i j
  · let i : Fin (n - 1) := ⟨0, by omega⟩
    refine ⟨0, zero_mem_planeConfiguration n hn,
      rimPoint (show 1 < n - 1 by omega) i, rim_mem_planeConfiguration n hn i, ?_⟩
    exact dist_zero_rim (show 1 < n - 1 by omega) i

private def firstIndex {m : ℕ} (hm : 1 < m) : Fin m :=
  ⟨0, by omega⟩

private def lastIndex {m : ℕ} (hm : 1 < m) : Fin m :=
  ⟨m - 1, by omega⟩

private lemma firstIndex_ne_lastIndex {m : ℕ} (hm : 1 < m) :
    firstIndex hm ≠ lastIndex hm := by
  intro h
  have := congrArg Fin.val h
  simp [firstIndex, lastIndex] at this
  omega

private lemma arcParameter_first {m : ℕ} (hm : 1 < m) :
    arcParameter hm (firstIndex hm) = 0 := by
  simp [arcParameter, firstIndex]

private lemma arcParameter_last {m : ℕ} (hm : 1 < m) :
    arcParameter hm (lastIndex hm) = arcEnd := by
  have hd : (((m - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hm
  simp [arcParameter, lastIndex, hd]

private lemma dist_first_last_rim {m : ℕ} (hm : 1 < m) :
    dist (rimPoint hm (firstIndex hm)) (rimPoint hm (lastIndex hm)) = 1 := by
  have hsq := dist_gamma_sq (0 : ℝ) arcEnd
  have he2 : arcEnd ^ 2 = 1 / 3 := by nlinarith [three_mul_arcEnd_sq]
  have hsq' : dist (gamma 0) (gamma arcEnd) ^ 2 = 1 := by
    rw [hsq]
    norm_num [he2]
  rw [rimPoint, rimPoint, arcParameter_first, arcParameter_last]
  have hn : 0 ≤ dist (gamma 0) (gamma arcEnd) := dist_nonneg
  nlinarith

private lemma planeConfiguration_count_lower (n : ℕ) (hn : 3 ≤ n) :
    n ≤ diameterPairCount (planeConfiguration n hn) := by
  let A := planeConfiguration n hn
  let G := diameterGraph A
  let m := n - 1
  have hm : 1 < m := by omega
  let c : {x // x ∈ A} := ⟨0, zero_mem_planeConfiguration n hn⟩
  let rv (i : Fin m) : {x // x ∈ A} :=
    ⟨rimPoint hm i, rim_mem_planeConfiguration n hn i⟩
  have hadj (i : Fin m) : G.Adj c (rv i) := by
    exact dist_zero_rim hm i
  let e : Fin m ↪ G.neighborSet c :=
    ⟨fun i ↦ ⟨rv i, hadj i⟩, by
      intro i j hij
      have hv : rv i = rv j := congrArg Subtype.val hij
      exact rimPoint_injective hm (congrArg Subtype.val hv)⟩
  have hdeg : m ≤ G.degree c := by
    rw [← G.card_neighborSet_eq_degree c]
    simpa using Fintype.card_le_of_injective e e.injective
  let i := firstIndex hm
  let j := lastIndex hm
  have hc_ne_i : c ≠ rv i := by
    intro h
    have hv := congrArg (fun z : {x // x ∈ A} ↦ (z : Point 2)) h
    have hz : (0 : Point 2) ≠ rimPoint hm i := by
      intro hz
      have hnorm := norm_gamma (arcParameter hm i)
      change ‖rimPoint hm i‖ = 1 at hnorm
      rw [← hz] at hnorm
      simpa using hnorm
    exact hz hv
  have hc_ne_j : c ≠ rv j := by
    intro h
    have hv := congrArg (fun z : {x // x ∈ A} ↦ (z : Point 2)) h
    have hz : (0 : Point 2) ≠ rimPoint hm j := by
      intro hz
      have hnorm := norm_gamma (arcParameter hm j)
      change ‖rimPoint hm j‖ = 1 at hnorm
      rw [← hz] at hnorm
      simpa using hnorm
    exact hz hv
  have hproper : G.incidenceFinset c ⊂ G.edgeFinset := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨G.incidenceFinset_subset c, ?_⟩
    intro heq
    have hedge : s(rv i, rv j) ∈ G.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact dist_first_last_rim hm
    have hinc : s(rv i, rv j) ∈ G.incidenceFinset c := heq.symm.subset hedge
    rw [G.mem_incidenceFinset, G.mk'_mem_incidenceSet_iff] at hinc
    exact hinc.2.elim hc_ne_i hc_ne_j
  have hlt : G.degree c < G.edgeFinset.card := by
    rw [← G.card_incidenceFinset_eq_degree c]
    exact Finset.card_lt_card hproper
  change n ≤ G.edgeFinset.card
  omega

/-! ## The planar upper bound -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma inner_ge_half_of_unit_of_dist_le_one {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : dist x y ≤ 1) :
    (1 / 2 : ℝ) ≤ ⟪x, y⟫ := by
  have hnorm : ‖x - y‖ ≤ 1 := by simpa [dist_eq_norm] using hxy
  have hsquare : ‖x - y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - y)]
  have h := norm_sub_sq_real x y
  rw [hx, hy] at h
  nlinarith

private lemma eq_of_unit_smul_eq_unit_of_inner_pos {x y : E} {a : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hip : 0 < ⟪x, y⟫)
    (h : a • x = y) : x = y := by
  have habs : |a| = 1 := by
    have := congrArg norm h
    simpa [norm_smul, hx, hy] using this
  have ha : a = 1 ∨ a = -1 := (abs_eq (by norm_num : (1 : ℝ) ≥ 0)).mp habs
  rcases ha with rfl | rfl
  · simpa using h
  · have : ⟪x, y⟫ = -1 := by
      rw [← h]
      simp [hx]
    linarith

private lemma coeff_sum_gt_one {x y z : E} {a b : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b)
    (hrepr : z = a • x + b • y) : 1 < a + b := by
  have hc : ⟪x, y⟫ < 1 :=
    (inner_lt_one_iff_real_of_norm_eq_one hx hy).2 hxy
  have hsq : 1 = a ^ 2 + 2 * a * b * ⟪x, y⟫ + b ^ 2 := by
    have hzinner : ⟪z, z⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hz]
      norm_num
    rw [hrepr] at hzinner
    have hxx : ⟪x, x⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hx]
      norm_num
    have hyy : ⟪y, y⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hy]
      norm_num
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hxx, hyy] at hzinner
    have hyx : ⟪y, x⟫ = ⟪x, y⟫ := (real_inner_comm y x).symm
    rw [hyx] at hzinner
    nlinarith
  nlinarith [mul_pos ha hb]

private lemma inner_ge_half_norm_sq_of_unit_of_dist_le_one {x y : E}
    (hy : ‖y‖ = 1) (hxy : dist x y ≤ 1) :
    ‖x‖ ^ 2 / 2 ≤ ⟪x, y⟫ := by
  have hnorm : ‖x - y‖ ≤ 1 := by simpa [dist_eq_norm] using hxy
  have hsquare : ‖x - y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - y)]
  have h := norm_sub_sq_real x y
  rw [hy] at h
  nlinarith

private lemma inner_eq_half_norm_sq_of_unit_of_dist_eq_one {x y : E}
    (hy : ‖y‖ = 1) (hxy : dist x y = 1) :
    ⟪x, y⟫ = ‖x‖ ^ 2 / 2 := by
  have hnorm : ‖x - y‖ = 1 := by simpa [dist_eq_norm] using hxy
  have h := norm_sub_sq_real x y
  rw [hy, hnorm] at h
  nlinarith

private lemma positive_combination_neighbor_eq_zero {u v w x : E} {a b : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b)
    (hwrepr : w = a • u + b • v)
    (hxu : dist x u ≤ 1) (hxv : dist x v ≤ 1)
    (hxw : dist x w = 1) : x = 0 := by
  by_contra hx0
  have hspos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hxu' : ‖x‖ ^ 2 / 2 ≤ ⟪x, u⟫ :=
    inner_ge_half_norm_sq_of_unit_of_dist_le_one hu hxu
  have hxv' : ‖x‖ ^ 2 / 2 ≤ ⟪x, v⟫ :=
    inner_ge_half_norm_sq_of_unit_of_dist_le_one hv hxv
  have hxw' : ⟪x, w⟫ = ‖x‖ ^ 2 / 2 :=
    inner_eq_half_norm_sq_of_unit_of_dist_eq_one hw hxw
  have hau : a * (‖x‖ ^ 2 / 2) ≤ a * ⟪x, u⟫ :=
    mul_le_mul_of_nonneg_left hxu' ha.le
  have hbv : b * (‖x‖ ^ 2 / 2) ≤ b * ⟪x, v⟫ :=
    mul_le_mul_of_nonneg_left hxv' hb.le
  rw [hwrepr, inner_add_right, real_inner_smul_right,
    real_inner_smul_right] at hxw'
  have hstrict : ‖x‖ ^ 2 / 2 < (a + b) * (‖x‖ ^ 2 / 2) := by
    nlinarith [mul_pos (sub_pos.mpr hab) hspos]
  nlinarith

private lemma three_unit_vectors_positive_combination
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    {u v w : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (duv : dist u v ≤ 1) (duw : dist u w ≤ 1) (dvw : dist v w ≤ 1) :
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 1 < a + b ∧ w = a • u + b • v) ∨
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 1 < a + b ∧ u = a • v + b • w) ∨
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 1 < a + b ∧ v = a • u + b • w) := by
  have iuv : (1 / 2 : ℝ) ≤ ⟪u, v⟫ :=
    inner_ge_half_of_unit_of_dist_le_one hu hv duv
  have iuw : (1 / 2 : ℝ) ≤ ⟪u, w⟫ :=
    inner_ge_half_of_unit_of_dist_le_one hu hw duw
  have ivw : (1 / 2 : ℝ) ≤ ⟪v, w⟫ :=
    inner_ge_half_of_unit_of_dist_le_one hv hw dvw
  have iuvp : 0 < ⟪u, v⟫ := lt_of_lt_of_le (by norm_num) iuv
  have iuwp : 0 < ⟪u, w⟫ := lt_of_lt_of_le (by norm_num) iuw
  have ivwp : 0 < ⟪v, w⟫ := lt_of_lt_of_le (by norm_num) ivw
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have huvli : LinearIndependent ℝ ![u, v] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro c hcv
    exact huv (eq_of_unit_smul_eq_unit_of_inner_pos hu hv iuvp hcv)
  have hspan : Submodule.span ℝ (Set.range ![u, v]) = ⊤ :=
    huvli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  let B : Module.Basis (Fin 2) ℝ E := Module.Basis.mk huvli hspan.ge
  let a : ℝ := B.repr w 0
  let b : ℝ := B.repr w 1
  have hwrepr : w = a • u + b • v := by
    rw [← B.sum_repr w, Fin.sum_univ_two]
    simp only [a, b, B, Module.Basis.mk_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  have ha0 : a ≠ 0 := by
    intro ha
    have hsmul : b • v = w := by simpa [ha] using hwrepr.symm
    have := eq_of_unit_smul_eq_unit_of_inner_pos hv hw ivwp hsmul
    exact hvw this
  have hb0 : b ≠ 0 := by
    intro hb
    have hsmul : a • u = w := by simpa [hb] using hwrepr.symm
    have := eq_of_unit_smul_eq_unit_of_inner_pos hu hw iuwp hsmul
    exact huw this
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · left
      exact ⟨a, b, ha, hb, coeff_sum_gt_one hu hv hw huv ha hb hwrepr, hwrepr⟩
    · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hb) hb0
      right; left
      let c : ℝ := -b / a
      let d : ℝ := 1 / a
      have hc : 0 < c := by exact div_pos (neg_pos.mpr hbneg) ha
      have hd : 0 < d := by exact one_div_pos.mpr ha
      have hurepr : u = c • v + d • w := by
        apply smul_right_injective E ha0
        rw [hwrepr]
        simp only [smul_add, smul_smul]
        dsimp [c, d]
        field_simp
        module
      exact ⟨c, d, hc, hd, coeff_sum_gt_one hv hw hu hvw hc hd hurepr, hurepr⟩
  · have haneg : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha0
    have hb : 0 < b := by
      by_contra hb
      have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hb) hb0
      have hi : 0 < ⟪w, u⟫ := by
        rw [real_inner_comm]
        exact iuwp
      have hc : 0 < ⟪v, u⟫ := by
        rw [real_inner_comm]
        exact iuvp
      have heq : ⟪w, u⟫ = a + b * ⟪v, u⟫ := by
        rw [hwrepr]
        simp [inner_add_left, real_inner_smul_left, hu]
      nlinarith [mul_neg_of_neg_of_pos hbneg hc]
    right; right
    let c : ℝ := -a / b
    let d : ℝ := 1 / b
    have hc : 0 < c := by exact div_pos (neg_pos.mpr haneg) hb
    have hd : 0 < d := by exact one_div_pos.mpr hb
    have hvrepr : v = c • u + d • w := by
      apply smul_right_injective E hb0
      rw [hwrepr]
      simp only [smul_add, smul_smul]
      dsimp [c, d]
      field_simp
      module
    exact ⟨c, d, hc, hd, coeff_sum_gt_one hu hw hv huw hc hd hvrepr, hvrepr⟩

private lemma three_unit_neighbors_have_leaf
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    {u v w : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (duv : dist u v ≤ 1) (duw : dist u w ≤ 1) (dvw : dist v w ≤ 1) :
    (∀ x : E, dist x u ≤ 1 → dist x v ≤ 1 → dist x w = 1 → x = 0) ∨
    (∀ x : E, dist x v ≤ 1 → dist x w ≤ 1 → dist x u = 1 → x = 0) ∨
    (∀ x : E, dist x u ≤ 1 → dist x w ≤ 1 → dist x v = 1 → x = 0) := by
  rcases three_unit_vectors_positive_combination hdim hu hv hw huv huw hvw duv duw dvw with
    ⟨a, b, ha, hb, hab, hwrepr⟩ | ⟨a, b, ha, hb, hab, hurepr⟩ |
      ⟨a, b, ha, hb, hab, hvrepr⟩
  · left
    intro x hxu hxv hxw
    exact positive_combination_neighbor_eq_zero hu hv hw ha hb hab hwrepr hxu hxv hxw
  · right; left
    intro x hxv hxw hxu
    exact positive_combination_neighbor_eq_zero hv hw hu ha hb hab hurepr hxv hxw hxu
  · right; right
    intro x hxu hxw hxv
    exact positive_combination_neighbor_eq_zero hu hw hv ha hb hab hvrepr hxu hxw hxv

private lemma three_diameter_neighbors_have_leaf_at
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    {p u v w : E}
    (hpu : dist p u = 1) (hpv : dist p v = 1) (hpw : dist p w = 1)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (duv : dist u v ≤ 1) (duw : dist u w ≤ 1) (dvw : dist v w ≤ 1) :
    (∀ x : E, dist x u ≤ 1 → dist x v ≤ 1 → dist x w = 1 → x = p) ∨
    (∀ x : E, dist x v ≤ 1 → dist x w ≤ 1 → dist x u = 1 → x = p) ∨
    (∀ x : E, dist x u ≤ 1 → dist x w ≤ 1 → dist x v = 1 → x = p) := by
  have hu : ‖u - p‖ = 1 := by
    simpa [dist_eq_norm, norm_sub_rev] using hpu
  have hv : ‖v - p‖ = 1 := by
    simpa [dist_eq_norm, norm_sub_rev] using hpv
  have hw : ‖w - p‖ = 1 := by
    simpa [dist_eq_norm, norm_sub_rev] using hpw
  have huv' : u - p ≠ v - p := (sub_left_injective (b := p)).ne huv
  have huw' : u - p ≠ w - p := (sub_left_injective (b := p)).ne huw
  have hvw' : v - p ≠ w - p := (sub_left_injective (b := p)).ne hvw
  have duv' : dist (u - p) (v - p) ≤ 1 := by simpa using duv
  have duw' : dist (u - p) (w - p) ≤ 1 := by simpa using duw
  have dvw' : dist (v - p) (w - p) ≤ 1 := by simpa using dvw
  rcases three_unit_neighbors_have_leaf hdim hu hv hw huv' huw' hvw' duv' duw' dvw' with
    hleaf | hleaf | hleaf
  · left
    intro x hxu hxv hxw
    have hx0 := hleaf (x - p) (by simpa using hxu) (by simpa using hxv) (by simpa using hxw)
    exact sub_eq_zero.mp hx0
  · right; left
    intro x hxv hxw hxu
    have hx0 := hleaf (x - p) (by simpa using hxv) (by simpa using hxw) (by simpa using hxu)
    exact sub_eq_zero.mp hx0
  · right; right
    intro x hxu hxw hxv
    have hx0 := hleaf (x - p) (by simpa using hxu) (by simpa using hxw) (by simpa using hxv)
    exact sub_eq_zero.mp hx0

private theorem graph_edge_card_le_of_maxDegree_le_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.maxDegree ≤ 2) :
    G.edgeFinset.card ≤ Fintype.card V := by
  have hsum : (∑ v : V, G.degree v) ≤ ∑ _v : V, 2 := by
    exact Finset.sum_le_sum fun v _ ↦ (G.degree_le_maxDegree v).trans hG
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hsum' : 2 * G.edgeFinset.card ≤ Fintype.card V * 2 := by
    simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using hsum
  omega

universe u

private theorem graph_edge_card_le_of_induce_peeling
    {V : Type u} [Fintype V]
    (Good : ∀ (W : Type u) [Fintype W], SimpleGraph W → Prop)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : Good V G)
    (hstep : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Good W H →
        H.maxDegree ≤ 2 ∨
          ∃ v : W, H.degree v ≤ 1 ∧
            Good {x : W // x ∈ ({v}ᶜ : Set W)} (H.induce ({v}ᶜ : Set W))) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      rcases hstep V G hG with hdeg | ⟨v, hv, hGood⟩
      · exact (graph_edge_card_le_of_maxDegree_le_two G hdeg).trans_eq hn
      · let K := G.induce ({v}ᶜ : Set V)
        have hnpos : 0 < n := by
          rw [← hn, Fintype.card_pos_iff]
          exact ⟨v⟩
        have hcardK : Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} = n - 1 := by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          rw [Fintype.card_subtype_compl]
          simp [hn]
        have hcardKlt : Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} < n := by omega
        have hind := ih _ hcardKlt K hGood rfl
        have hedgeK := G.card_edgeFinset_induce_compl_singleton v
        have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
        dsimp [K] at hind
        omega

private theorem graph_edge_card_le_of_comap_alternative
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (halt : ∀ (W : Type u) [Fintype W] [DecidableEq W] (f : W ↪ V)
      [DecidableRel (G.comap f).Adj],
      (G.comap f).maxDegree ≤ 2 ∨ ∃ v : W, (G.comap f).degree v ≤ 1) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  let Good : ∀ (W : Type u) [Fintype W], SimpleGraph W → Prop :=
    fun W _ H ↦ ∃ f : W ↪ V, H = G.comap f
  apply graph_edge_card_le_of_induce_peeling Good G
  · exact ⟨Function.Embedding.refl V, rfl⟩
  · intro W _ _ H _ hGood
    rcases hGood with ⟨f, rfl⟩
    rcases halt W f with hdeg | ⟨v, hv⟩
    · exact Or.inl hdeg
    · refine Or.inr ⟨v, hv, ?_⟩
      let j : {x : W // x ∈ ({v}ᶜ : Set W)} ↪ W :=
        Function.Embedding.subtype (fun x ↦ x ∈ ({v}ᶜ : Set W))
      exact ⟨j.trans f, rfl⟩

private theorem diameterGraph_comap_alternative (A : Finset (Point 2))
    (hA : IsDiameterOne A) :
    ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (f : W ↪ {x // x ∈ A})
      [DecidableRel ((diameterGraph A).comap f).Adj],
      ((diameterGraph A).comap f).maxDegree ≤ 2 ∨
        ∃ v : W, ((diameterGraph A).comap f).degree v ≤ 1 := by
  classical
  let G := diameterGraph A
  intro W _ _ f _
  let H := G.comap f
  by_cases hdeg : H.maxDegree ≤ 2
  · exact Or.inl hdeg
  · right
    have hmax : 3 ≤ H.maxDegree := by omega
    cases isEmpty_or_nonempty W with
    | inl hempty =>
        let : IsEmpty W := hempty
        have : H.maxDegree = 0 := H.maxDegree_of_subsingleton
        omega
    | inr hnonempty =>
      let : Nonempty W := hnonempty
      obtain ⟨p, hpmax⟩ := H.exists_maximal_degree_vertex
      have hpdeg : 3 ≤ H.degree p := by omega
      obtain ⟨T, hTsub, hTcard⟩ :=
        Finset.exists_subset_card_eq hpdeg
      rw [Finset.card_eq_three] at hTcard
      obtain ⟨q₁, q₂, q₃, hq₁q₂, hq₁q₃, hq₂q₃, rfl⟩ := hTcard
      have hpq₁ : H.Adj p q₁ := by
        rw [← H.mem_neighborFinset]
        exact hTsub (by simp)
      have hpq₂ : H.Adj p q₂ := by
        rw [← H.mem_neighborFinset]
        exact hTsub (by simp)
      have hpq₃ : H.Adj p q₃ := by
        rw [← H.mem_neighborFinset]
        exact hTsub (by simp)
      let P (x : W) : Point 2 := ((f x : {x // x ∈ A}) : Point 2)
      have hpq₁' : dist (P p) (P q₁) = 1 := hpq₁
      have hpq₂' : dist (P p) (P q₂) = 1 := hpq₂
      have hpq₃' : dist (P p) (P q₃) = 1 := hpq₃
      have hPq₁q₂ : P q₁ ≠ P q₂ := by
        intro h
        apply hq₁q₂
        apply f.injective
        exact Subtype.ext h
      have hPq₁q₃ : P q₁ ≠ P q₃ := by
        intro h
        apply hq₁q₃
        apply f.injective
        exact Subtype.ext h
      have hPq₂q₃ : P q₂ ≠ P q₃ := by
        intro h
        apply hq₂q₃
        apply f.injective
        exact Subtype.ext h
      have hq₁q₂dist : dist (P q₁) (P q₂) ≤ 1 :=
        hA.dist_le (f q₁).property (f q₂).property
      have hq₁q₃dist : dist (P q₁) (P q₃) ≤ 1 :=
        hA.dist_le (f q₁).property (f q₃).property
      have hq₂q₃dist : dist (P q₂) (P q₃) ≤ 1 :=
        hA.dist_le (f q₂).property (f q₃).property
      have hleaf := three_diameter_neighbors_have_leaf_at (E := Point 2) (by simp)
        hpq₁' hpq₂' hpq₃' hPq₁q₂ hPq₁q₃ hPq₂q₃
        hq₁q₂dist hq₁q₃dist hq₂q₃dist
      have degree_le_one_of_unique_neighbor (q : W)
          (hu : ∀ x : Point 2, x ∈ A → dist x (P q) = 1 → x = P p) :
          H.degree q ≤ 1 := by
        rw [← H.card_neighborFinset_eq_degree q]
        have hs : H.neighborFinset q ⊆ {p} := by
          intro x hx
          rw [Finset.mem_singleton]
          rw [H.mem_neighborFinset] at hx
          change dist (P q) (P x) = 1 at hx
          apply f.injective
          apply Subtype.ext
          apply hu (P x) (f x).property
          simpa [dist_comm] using hx
        exact (Finset.card_le_card hs).trans_eq (by simp)
      rcases hleaf with hleaf₃ | hleaf₁ | hleaf₂
      · refine ⟨q₃, degree_le_one_of_unique_neighbor q₃ ?_⟩
        intro x hx hdist
        exact hleaf₃ x
          (hA.dist_le hx (f q₁).property)
          (hA.dist_le hx (f q₂).property) hdist
      · refine ⟨q₁, degree_le_one_of_unique_neighbor q₁ ?_⟩
        intro x hx hdist
        exact hleaf₁ x
          (hA.dist_le hx (f q₂).property)
          (hA.dist_le hx (f q₃).property) hdist
      · refine ⟨q₂, degree_le_one_of_unique_neighbor q₂ ?_⟩
        intro x hx hdist
        exact hleaf₂ x
          (hA.dist_le hx (f q₁).property)
          (hA.dist_le hx (f q₃).property) hdist

/-- Hopf--Pannwitz upper bound: a planar diameter graph has at most one
diameter edge per point. -/
theorem diameterPairCount_le_card_plane (A : Finset (Point 2))
    (hA : IsDiameterOne A) :
    diameterPairCount A ≤ A.card := by
  have hbound := graph_edge_card_le_of_comap_alternative (diameterGraph A)
    (diameterGraph_comap_alternative A hA)
  simpa [diameterPairCount] using hbound

/-- The exceptional two-point planar value. -/
theorem f_plane_two : f 2 2 = 1 :=
  f_two 2 (by omega)

/-- Complete Hopf--Pannwitz--Erdős formula in the plane for `n ≥ 3`. -/
theorem f_plane (n : ℕ) (hn : 3 ≤ n) : f 2 n = n := by
  apply Nat.le_antisymm
  · apply f_le_of_forall (d := 2) (n := n) (B := n) (by omega) (by omega)
    intro A hcard hdiam
    simpa [hcard] using diameterPairCount_le_card_plane A hdiam
  · apply le_f_of_exists
    exact ⟨planeConfiguration n hn, card_planeConfiguration n hn,
      isDiameterOne_planeConfiguration n hn, planeConfiguration_count_lower n hn⟩

end

end Erdos223

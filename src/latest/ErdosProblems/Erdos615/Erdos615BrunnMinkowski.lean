/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Prékopa--Leindler and Brunn--Minkowski in finite-dimensional real coordinate
spaces.  Mathlib v4.33.0 does not yet contain Brunn--Minkowski, so this file
supplies the localized analytic theorem used by the Erdős 615 construction.

The proof is by the standard tensorization of the one-dimensional
Prékopa--Leindler inequality.  It is adapted to current Mathlib APIs from the
complete Lean 3 development by Albert Chua.
-/

import Mathlib

open Set Real MeasureTheory
open scoped ENNReal Pointwise Topology

namespace Erdos615.BrunnMinkowski

theorem ennreal_geomMean_le_arithMean2_weighted
    (w₁ w₂ : ℝ) (p₁ p₂ : ℝ≥0∞)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ ≤ ENNReal.ofReal w₁ * p₁ + ENNReal.ofReal w₂ * p₂ := by
  wlog hp : p₁ ≤ p₂ generalizing w₁ w₂ p₁ p₂
  · convert this w₂ w₁ p₂ p₁ hw₂ hw₁ (by linarith) (le_of_not_ge hp) using 1
    · rw [mul_comm]
    · rw [add_comm]
  rcases eq_or_ne p₂ ∞ with rfl | hp₂
  · rcases eq_or_lt_of_le hw₂ with rfl | hw₂pos
    · simp only [add_zero] at hw
      subst w₁
      simp
    · simp [hw₂pos]
  have hp₂lt : p₂ < ∞ := lt_top_iff_ne_top.mpr hp₂
  have hp₁lt : p₁ < ∞ := hp.trans_lt hp₂lt
  rw [← ENNReal.coe_toNNReal hp₁lt.ne, ← ENNReal.coe_toNNReal hp₂lt.ne,
    ← ENNReal.coe_rpow_of_nonneg _ hw₁, ← ENNReal.coe_rpow_of_nonneg _ hw₂,
    ← ENNReal.coe_mul, ENNReal.ofReal, ENNReal.ofReal,
    ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  have hnn : w₁.toNNReal + w₂.toNNReal = 1 := by
    apply NNReal.eq
    simpa [Real.toNNReal_of_nonneg hw₁, Real.toNNReal_of_nonneg hw₂] using hw
  convert NNReal.geom_mean_le_arith_mean2_weighted
    w₁.toNNReal w₂.toNNReal p₁.toNNReal p₂.toNNReal hnn using 1 <;>
      simp [Real.toNNReal_of_nonneg hw₁, Real.toNNReal_of_nonneg hw₂]

lemma brunnMinkowski_compact_one
    {A B : Set ℝ} (A_ne : A.Nonempty) (B_ne : B.Nonempty)
    (hA : IsCompact A) (hB : IsCompact B) :
    volume A + volume B ≤ volume (A + B) := by
  let A' := A + {sInf B}
  let B' := {sSup A} + B
  have hA' : volume A = volume A' := by
    simp [A', add_singleton, image_add_right]
  have hB' : volume B = volume B' := by
    simp [B', singleton_add, image_add_left]
  have hinter : volume (A' ∩ B') = 0 := by
    convert (volume_singleton : volume ({sSup A + sInf B} : Set ℝ) = 0)
    rw [eq_singleton_iff_unique_mem]
    refine ⟨?_, ?_⟩
    · exact ⟨by simpa [A'] using hA.sSup_mem A_ne,
        by simpa [B'] using hB.sInf_mem B_ne⟩
    · intro x hx
      rw [mem_inter_iff] at hx
      apply mem_singleton_iff.mpr
      apply le_antisymm
      · rcases hx.1 with ⟨a, ha, b, hb, rfl⟩
        rw [mem_singleton_iff.mp hb]
        exact add_le_add (le_csSup hA.bddAbove ha) le_rfl
      · rcases hx.2 with ⟨a, ha, b, hb, rfl⟩
        rw [mem_singleton_iff.mp ha]
        exact add_le_add le_rfl (csInf_le hB.bddBelow hb)
  have hA'meas : MeasurableSet A' := by
    have hc : IsCompact A' := by
      change IsCompact (A + {sInf B})
      rw [add_singleton]
      exact hA.image (continuous_id.add continuous_const)
    exact hc.measurableSet
  rw [hA', hB', ← measure_union_add_inter' hA'meas B', hinter, add_zero]
  apply measure_mono
  refine union_subset (add_subset_add_left ?_) (add_subset_add_right ?_)
  · exact singleton_subset_iff.mpr (hB.sInf_mem B_ne)
  · exact singleton_subset_iff.mpr (hA.sSup_mem A_ne)

abbrev CompactPiece (A : Set ℝ) :=
  {K : Set ℝ // K ⊆ A ∧ IsCompact K ∧ K.Nonempty}

lemma volume_eq_iSup_compactPiece
    {A : Set ℝ} (A_meas : MeasurableSet A) :
    volume A = ⨆ K : CompactPiece A, volume K.val := by
  rw [A_meas.measure_eq_iSup_isCompact volume]
  apply le_antisymm
  · refine iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hKc ↦ ?_
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp
    · exact le_iSup_of_le ⟨K, hKA, hKc, hKne⟩ le_rfl
  · refine iSup_le fun K ↦ le_iSup_of_le K.val <|
      le_iSup_of_le K.property.1 <| le_iSup_of_le K.property.2.1 le_rfl

lemma brunnMinkowski_one
    {A B : Set ℝ} (A_meas : MeasurableSet A) (B_meas : MeasurableSet B)
    (A_ne : A.Nonempty) (B_ne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a, ha⟩ := A_ne
  obtain ⟨b, hb⟩ := B_ne
  let : Nonempty (CompactPiece A) :=
    ⟨⟨{a}, singleton_subset_iff.mpr ha, isCompact_singleton, singleton_nonempty a⟩⟩
  let : Nonempty (CompactPiece B) :=
    ⟨⟨{b}, singleton_subset_iff.mpr hb, isCompact_singleton, singleton_nonempty b⟩⟩
  rw [volume_eq_iSup_compactPiece A_meas, volume_eq_iSup_compactPiece B_meas]
  apply ENNReal.iSup_add_iSup_le
  intro K L
  exact (brunnMinkowski_compact_one K.property.2.2 L.property.2.2
    K.property.2.1 L.property.2.1).trans
      (measure_mono (add_subset_add K.property.1 L.property.1))

theorem lintegral_eq_lintegral_meas_lt_ennreal
    {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞}
    (μ : Measure α) [SigmaFinite μ] (f_meas : Measurable f) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ (t : ℝ) in Ioi 0, μ {a | ENNReal.ofReal t < f a} := by
  rcases eq_or_lt_of_le (show 0 ≤ μ {a | f a = ∞} from bot_le) with hzero | hpos
  · have hfinite : ∀ᵐ a ∂μ, f a < ∞ := by
      rw [ae_iff]
      simpa only [not_lt, top_le_iff] using hzero.symm
    convert lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg)
      (f_meas.ennreal_toReal.aemeasurable) using 1
    · exact lintegral_congr_ae
        (ofReal_toReal_ae_eq hfinite).symm
    · refine setLIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      apply measure_congr
      filter_upwards [hfinite] with a ha
      exact propext <| ENNReal.ofReal_lt_iff_lt_toReal (mem_Ioi.mp ht).le ha.ne
  · have hne : μ {a | f a = ∞} ≠ 0 := hpos.ne'
    have hleft : ∫⁻ ω, f ω ∂μ = ∞ :=
      lintegral_eq_top_of_measure_eq_top_ne_zero f_meas.aemeasurable hne
    rw [hleft]
    apply le_antisymm ?_ le_top
    calc
      (∞ : ℝ≥0∞) = μ {a | f a = ∞} * volume (Ioi (0 : ℝ)) := by
        rw [volume_Ioi, ENNReal.mul_top hne]
      _ = ∫⁻ (_t : ℝ) in Ioi 0, μ {a | f a = ∞} := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ (t : ℝ) in Ioi 0, μ {a | ENNReal.ofReal t < f a} := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        apply measure_mono
        intro a ha
        rw [mem_setOf_eq, ha]
        exact ENNReal.ofReal_lt_top

lemma prekopa_slice_one
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)
    (a_pos : 0 < a) (b_pos : 0 < b) {u v w : ℝ≥0∞}
    (hu : ∃ x, u < g x) (hv : ∃ y, v < h y)
    (hw : w ≤ u ^ a * v ^ b) :
    volume {x | w < f x} ≥
      ENNReal.ofReal a * volume {x | u < g x} +
        ENNReal.ofReal b * volume {y | v < h y} := by
  have hscale : ∀ {r : ℝ}, 0 ≤ r → ∀ s : Set ℝ,
      volume (r • s) = ENNReal.ofReal r * volume s := by
    intro r hr s
    simpa using volume.addHaar_smul_of_nonneg hr s
  rw [← hscale a_pos.le, ← hscale b_pos.le]
  rcases hu with ⟨x, hx⟩
  rcases hv with ⟨y, hy⟩
  calc
    volume (a • {x | u < g x}) + volume (b • {y | v < h y})
        ≤ volume (a • {x | u < g x} + b • {y | v < h y}) :=
      brunnMinkowski_one
      ((measurableSet_lt measurable_const g_meas).const_smul₀ a)
      ((measurableSet_lt measurable_const h_meas).const_smul₀ b)
      ⟨a * x, smul_mem_smul_set hx⟩
      ⟨b * y, smul_mem_smul_set hy⟩
    _ ≤ volume {x | w < f x} := by
      apply measure_mono
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      rw [mem_setOf_eq] at hx hy ⊢
      calc
        w ≤ u ^ a * v ^ b := hw
        _ < g x ^ a * h y ^ b :=
          ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx a_pos)
            (ENNReal.rpow_lt_rpow hy b_pos)
        _ ≤ f (a * x + b * y) := f_ineq x y

lemma prekopa_leindler_one_iSup_top
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)
    (a_pos : 0 < a) (b_pos : 0 < b)
    (hg : 0 < ∫⁻ x, g x) (hh_top : ⨆ x, h x = ∞) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b := by
  suffices hfinf : ∞ ≤ ∫⁻ x, f x by
    exact (eq_top_iff.mpr hfinf).symm.le.trans' le_top
  obtain ⟨u, u_pos, hu⟩ :
      ∃ t : ℝ≥0∞, 0 < t ∧ 0 < volume {x | t < g x} := by
    rw [lintegral_eq_lintegral_meas_lt_ennreal volume g_meas] at hg
    by_contra hnot
    push_neg at hnot
    have hzero : ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < g x} = 0 := by
      intro t ht
      exact le_antisymm (hnot (ENNReal.ofReal t) (ENNReal.ofReal_pos.mpr ht)) bot_le
    have : (∫⁻ (t : ℝ) in Ioi 0, volume {x | ENNReal.ofReal t < g x}) = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro t ht
      exact hzero t (mem_Ioi.mp ht)
    exact (hg.ne' (by simpa [this] using this)).elim
  let c := volume {x | u < g x}
  have hc : 0 < c := hu
  suffices hnat : ∀ n : ℕ, (n : ℝ≥0∞) * (ENNReal.ofReal a * c) ≤ ∫⁻ x, f x by
    calc
      ∞ = (⨆ n : ℕ, (n : ℝ≥0∞)) * (ENNReal.ofReal a * c) := by
        rw [ENNReal.iSup_natCast, ENNReal.top_mul]
        exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr a_pos).ne' hc.ne').ne'
      _ ≤ ∫⁻ x, f x := by
        rw [ENNReal.iSup_mul]
        exact iSup_le hnat
  intro n
  rcases n.eq_zero_or_pos with rfl | n_pos
  · simp
  have hlevel : ENNReal.ofReal a * c ≤ volume {x | (n : ℝ≥0∞) ≤ f x} := by
    have hstrict : ENNReal.ofReal a * c ≤ volume {x | (n : ℝ≥0∞) < f x} := by
      have hu_exists : ∃ x, u < g x := nonempty_of_measure_ne_zero hu.ne'
      have u_fin : u < ∞ := by
        by_contra hutop
        have : u = ∞ := top_unique (not_lt.mp hutop)
        subst u
        simpa using hu
      obtain ⟨v, v_fin, huv⟩ :
          ∃ v : ℝ≥0∞, v < ∞ ∧ (n : ℝ≥0∞) ≤ u ^ a * v ^ b := by
        have hua_pos : 0 < u ^ a := ENNReal.rpow_pos_of_nonneg u_pos a_pos.le
        refine ⟨((n : ℝ≥0∞) / u ^ a) ^ b⁻¹, ?_, ?_⟩
        · exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 b_pos.le)
            (ENNReal.div_lt_top ENNReal.coe_ne_top hua_pos.ne').ne
        · have hua_fin : u ^ a ≠ ∞ :=
            (ENNReal.rpow_lt_top_of_nonneg a_pos.le u_fin.ne).ne
          rw [← ENNReal.rpow_mul, inv_mul_cancel₀ b_pos.ne', ENNReal.rpow_one,
            ENNReal.mul_div_cancel hua_pos.ne' hua_fin]
      obtain ⟨y, hy⟩ : ∃ y, v < h y :=
        (iSup_eq_top.mp hh_top) v v_fin
      exact (le_self_add.trans <| prekopa_slice_one f g h f_meas g_meas h_meas
        a b hab f_ineq a_pos b_pos hu_exists ⟨y, hy⟩ huv)
    exact hstrict.trans <| measure_mono fun z hz ↦ by
      change (n : ℝ≥0∞) < f z at hz
      change (n : ℝ≥0∞) ≤ f z
      exact hz.le
  calc
    (n : ℝ≥0∞) * (ENNReal.ofReal a * c)
        ≤ (n : ℝ≥0∞) * volume {x | (n : ℝ≥0∞) ≤ f x} :=
      by gcongr
    _ ≤ ∫⁻ x, f x := mul_meas_ge_le_lintegral f_meas n

lemma prekopa_leindler_one_iSup_one
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b)
    (a_pos : 0 < a) (b_pos : 0 < b)
    (hg : ⨆ x, g x = 1) (hh : ⨆ x, h x = 1) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b := by
  rw [lintegral_eq_lintegral_meas_lt_ennreal volume f_meas,
    lintegral_eq_lintegral_meas_lt_ennreal volume g_meas,
    lintegral_eq_lintegral_meas_lt_ennreal volume h_meas]
  refine (ennreal_geomMean_le_arithMean2_weighted a b
    (∫⁻ (t : ℝ) in Ioi 0, volume {x | ENNReal.ofReal t < g x})
    (∫⁻ (t : ℝ) in Ioi 0, volume {x | ENNReal.ofReal t < h x})
    a_pos.le b_pos.le hab).trans ?_
  rw [← lintegral_const_mul, ← lintegral_const_mul, ← lintegral_add_left]
  · apply setLIntegral_mono'
    · exact measurableSet_Ioi
    · intro t ht
      rcases lt_or_ge (ENNReal.ofReal t) 1 with ht1 | ht1
      · apply prekopa_slice_one f g h f_meas g_meas h_meas
          a b hab f_ineq a_pos b_pos
        · exact lt_iSup_iff.mp (hg ▸ ht1)
        · exact lt_iSup_iff.mp (hh ▸ ht1)
        · rcases eq_or_ne (ENNReal.ofReal t) 0 with ht0 | ht0
          · simpa [ht0]
          · rw [← ENNReal.rpow_add a b ht0 ENNReal.ofReal_ne_top,
              hab, ENNReal.rpow_one]
      · apply le_trans (le_of_eq ?_) bot_le
        change ENNReal.ofReal a * volume {x | ENNReal.ofReal t < g x} +
          ENNReal.ofReal b * volume {x | ENNReal.ofReal t < h x} = (0 : ℝ≥0∞)
        rw [add_eq_zero]
        constructor
        · apply mul_eq_zero_of_right
          rw [show {x | ENNReal.ofReal t < g x} = ∅ by
            ext x
            simp only [mem_setOf_eq, not_lt, mem_empty_iff_false, iff_false]
            exact ((le_iSup g x).trans_eq hg).trans ht1]
          exact measure_empty
        · apply mul_eq_zero_of_right
          rw [show {x | ENNReal.ofReal t < h x} = ∅ by
            ext x
            simp only [mem_setOf_eq, not_lt, mem_empty_iff_false, iff_false]
            exact ((le_iSup h x).trans_eq hh).trans ht1]
          exact measure_empty
  all_goals
    apply Antitone.measurable
    intro t₁ t₂ ht
    dsimp only
    gcongr

theorem prekopa_leindler_one
    (f g h : ℝ → ℝ≥0∞)
    (f_meas : Measurable f) (g_meas : Measurable g) (h_meas : Measurable h)
    (a b : ℝ) (a_nonneg : 0 ≤ a) (b_nonneg : 0 ≤ b) (hab : a + b = 1)
    (f_ineq : ∀ x y, f (a * x + b * y) ≥ g x ^ a * h y ^ b) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b := by
  rcases a_nonneg.eq_or_lt with rfl | a_pos
  · have hb : b = 1 := by linarith
    subst b
    convert lintegral_mono (fun y ↦ show h y ≤ f y by
      simpa using f_ineq 0 y) using 1 <;> simp
  rcases b_nonneg.eq_or_lt with rfl | b_pos
  · have ha : a = 1 := by linarith
    subst a
    convert lintegral_mono (fun x ↦ show g x ≤ f x by
      simpa using f_ineq x 0) using 1 <;> simp
  rcases eq_or_lt_of_le (show 0 ≤ ∫⁻ x, g x from bot_le) with hg_zero | hg_pos
  · rw [← hg_zero, ENNReal.zero_rpow_of_pos a_pos, zero_mul]
    exact bot_le
  rcases eq_or_lt_of_le (show 0 ≤ ∫⁻ x, h x from bot_le) with hh_zero | hh_pos
  · rw [← hh_zero, ENNReal.zero_rpow_of_pos b_pos, mul_zero]
    exact bot_le
  have cg_pos : 0 < ⨆ x, g x := by
    by_contra hcg
    have hcg0 : ⨆ x, g x = 0 := bot_unique (not_lt.mp hcg)
    have : g = 0 := funext fun x ↦ bot_unique ((le_iSup g x).trans_eq hcg0)
    subst g
    simpa using hg_pos
  have ch_pos : 0 < ⨆ x, h x := by
    by_contra hch
    have hch0 : ⨆ x, h x = 0 := bot_unique (not_lt.mp hch)
    have : h = 0 := funext fun x ↦ bot_unique ((le_iSup h x).trans_eq hch0)
    subst h
    simpa using hh_pos
  rcases eq_or_ne (⨆ x, h x) ∞ with ch_top | ch_fin
  · exact prekopa_leindler_one_iSup_top f g h f_meas g_meas h_meas
      a b hab f_ineq a_pos b_pos hg_pos ch_top
  rcases eq_or_ne (⨆ x, g x) ∞ with cg_top | cg_fin
  · rw [mul_comm]
    apply prekopa_leindler_one_iSup_top f h g f_meas h_meas g_meas
      b a (by linarith) _ b_pos a_pos hh_pos cg_top
    intro x y
    convert f_ineq y x using 1 <;> ring_nf
  have cg_lt_top : (⨆ x, g x) < ∞ := lt_top_iff_ne_top.mpr cg_fin
  have ch_lt_top : (⨆ x, h x) < ∞ := lt_top_iff_ne_top.mpr ch_fin
  let cgi := (⨆ x, g x)⁻¹
  let chi := (⨆ x, h x)⁻¹
  let c := cgi ^ a * chi ^ b
  have cgi_pos : 0 < cgi := ENNReal.inv_pos.mpr cg_fin
  have chi_pos : 0 < chi := ENNReal.inv_pos.mpr ch_fin
  have cgi_fin : cgi < ∞ := ENNReal.inv_lt_top.mpr cg_pos
  have chi_fin : chi < ∞ := ENNReal.inv_lt_top.mpr ch_pos
  have c_pos : 0 < c := ENNReal.mul_pos
    (ENNReal.rpow_pos cgi_pos cgi_fin.ne).ne'
    (ENNReal.rpow_pos chi_pos chi_fin.ne).ne'
  have c_fin : c < ∞ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg a_pos.le cgi_fin.ne)
    (ENNReal.rpow_lt_top_of_nonneg b_pos.le chi_fin.ne)
  let f' := fun x ↦ c * f x
  let g' := fun x ↦ cgi * g x
  let h' := fun x ↦ chi * h x
  have f'_meas : Measurable f' := f_meas.const_mul c
  have g'_meas : Measurable g' := g_meas.const_mul cgi
  have h'_meas : Measurable h' := h_meas.const_mul chi
  have f'_ineq : ∀ x y, f' (a * x + b * y) ≥ g' x ^ a * h' y ^ b := by
    intro x y
    dsimp only [f', g', h']
    rw [ENNReal.mul_rpow_of_nonneg _ _ a_pos.le,
      ENNReal.mul_rpow_of_nonneg _ _ b_pos.le]
    change cgi ^ a * g x ^ a * (chi ^ b * h y ^ b) ≤ c * f (a * x + b * y)
    calc
      _ = c * (g x ^ a * h y ^ b) := by simp only [c]; ac_rfl
      _ ≤ c * f (a * x + b * y) := by gcongr; exact f_ineq x y
  have hnorm := prekopa_leindler_one_iSup_one f' g' h'
    f'_meas g'_meas h'_meas a b hab f'_ineq a_pos b_pos
  have hg' : ⨆ x, g' x = 1 := by
    rw [show g' = fun x ↦ cgi * g x from rfl, ← ENNReal.mul_iSup]
    exact ENNReal.inv_mul_cancel cg_pos.ne' cg_fin
  have hh' : ⨆ x, h' x = 1 := by
    rw [show h' = fun x ↦ chi * h x from rfl, ← ENNReal.mul_iSup]
    exact ENNReal.inv_mul_cancel ch_pos.ne' ch_fin
  specialize hnorm hg' hh'
  dsimp only [f', g', h'] at hnorm
  rw [lintegral_const_mul' c f c_fin.ne,
    lintegral_const_mul' cgi g cgi_fin.ne,
    lintegral_const_mul' chi h chi_fin.ne] at hnorm
  rw [ENNReal.mul_rpow_of_nonneg _ _ a_pos.le,
    ENNReal.mul_rpow_of_nonneg _ _ b_pos.le] at hnorm
  have hnorm' : c * (∫⁻ x, f x) ≥
      c * ((∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b) := by
    calc
      _ ≥ cgi ^ a * (∫⁻ x, g x) ^ a *
          (chi ^ b * (∫⁻ x, h x) ^ b) := hnorm
      _ = _ := by simp only [c]; ac_rfl
  calc
    (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b =
        c⁻¹ * (c * ((∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel c_pos.ne' c_fin.ne, one_mul]
    _ ≤ c⁻¹ * (c * ∫⁻ x, f x) := by
      simpa only [mul_comm] using mul_le_mul_left hnorm' c⁻¹
    _ = ∫⁻ x, f x := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel c_pos.ne' c_fin.ne, one_mul]

/-! ### Tensorization to finite real coordinate spaces -/

/-- The Prékopa--Leindler property for a real module with its specified volume. -/
def HasPrekopaLeindler (E : Type*) [AddCommMonoid E] [Module ℝ E]
    [MeasureSpace E] : Prop :=
  ∀ (f g h : E → ℝ≥0∞),
    Measurable f → Measurable g → Measurable h →
    ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    (∀ x y, f (a • x + b • y) ≥ g x ^ a * h y ^ b) →
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b

theorem hasPrekopaLeindler_of_measurePreserving_linearEquiv
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E] [MeasureSpace E]
    [AddCommMonoid F] [Module ℝ F] [MeasureSpace F]
    (e : E ≃ₗ[ℝ] F)
    (he : MeasurePreserving e (volume : Measure E) (volume : Measure F))
    (hE : HasPrekopaLeindler E) : HasPrekopaLeindler F := by
  intro f g h hf hg hh a b ha hb hab hineq
  have hcomp : ∀ x y,
      (f ∘ e) (a • x + b • y) ≥ (g ∘ e) x ^ a * (h ∘ e) y ^ b := by
    intro x y
    simpa using hineq (e x) (e y)
  have H := hE (f ∘ e) (g ∘ e) (h ∘ e)
    (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable)
    a b ha hb hab hcomp
  change (∫⁻ x, f (e x)) ≥
    (∫⁻ x, g (e x)) ^ a * (∫⁻ x, h (e x)) ^ b at H
  rw [he.lintegral_comp hf, he.lintegral_comp hg, he.lintegral_comp hh] at H
  exact H

theorem hasPrekopaLeindler_prod
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E] [MeasureSpace E]
    [AddCommMonoid F] [Module ℝ F] [MeasureSpace F]
    [SigmaFinite (volume : Measure E)] [SigmaFinite (volume : Measure F)]
    (hE : HasPrekopaLeindler E) (hF : HasPrekopaLeindler F) :
    HasPrekopaLeindler (E × F) := by
  intro f g h hf hg hh a b ha hb hab hineq
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable,
    lintegral_prod _ hg.aemeasurable, lintegral_prod _ hh.aemeasurable]
  apply hE
  · exact hf.lintegral_prod_right'
  · exact hg.lintegral_prod_right'
  · exact hh.lintegral_prod_right'
  · exact ha
  · exact hb
  · exact hab
  · intro x₁ y₁
    apply hF
    · exact hf.comp measurable_prodMk_left
    · exact hg.comp measurable_prodMk_left
    · exact hh.comp measurable_prodMk_left
    · exact ha
    · exact hb
    · exact hab
    · intro x₂ y₂
      simpa using hineq (x₁, x₂) (y₁, y₂)

theorem hasPrekopaLeindler_real : HasPrekopaLeindler ℝ := by
  intro f g h hf hg hh a b ha hb hab hineq
  simpa only [smul_eq_mul] using
    prekopa_leindler_one f g h hf hg hh a b ha hb hab hineq

theorem hasPrekopaLeindler_fin_zero : HasPrekopaLeindler (Fin 0 → ℝ) := by
  intro f g h hf hg hh a b ha hb hab hineq
  simp only [lintegral_unique, volume_pi, Measure.pi_univ, Finset.prod_fin_eq_prod_range,
    Finset.prod_range_zero, mul_one]
  convert hineq 0 0

theorem hasPrekopaLeindler_fin_one : HasPrekopaLeindler (Fin 1 → ℝ) := by
  let e : ℝ ≃ₗ[ℝ] (Fin 1 → ℝ) :=
    (LinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have he : MeasurePreserving e := by
    exact (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ)).symm
  exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
    hasPrekopaLeindler_real

theorem hasPrekopaLeindler_sum
    {I J : Type*} [Fintype I] [Fintype J]
    (hI : HasPrekopaLeindler (I → ℝ))
    (hJ : HasPrekopaLeindler (J → ℝ)) :
    HasPrekopaLeindler (I ⊕ J → ℝ) := by
  let e : ((I → ℝ) × (J → ℝ)) ≃ₗ[ℝ] (I ⊕ J → ℝ) :=
    (LinearEquiv.sumPiEquivProdPi ℝ I J (fun _ ↦ ℝ)).symm
  have he : MeasurePreserving e := by
    exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J ↦ ℝ)).symm
  exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
    (hasPrekopaLeindler_prod hI hJ)

theorem hasPrekopaLeindler_fin : ∀ n : ℕ, HasPrekopaLeindler (Fin n → ℝ)
  | 0 => hasPrekopaLeindler_fin_zero
  | n + 1 => by
      let ei : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let e : (Fin n ⊕ Fin 1 → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ) :=
        LinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + 1) ↦ ℝ) ei
      have he : MeasurePreserving e := by
        exact volume_measurePreserving_piCongrLeft (fun _ : Fin (n + 1) ↦ ℝ) ei
      exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
        (hasPrekopaLeindler_sum (hasPrekopaLeindler_fin n)
          hasPrekopaLeindler_fin_one)

theorem prekopa_leindler_fin {n : ℕ}
    (f g h : (Fin n → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hineq : ∀ x y, f (a • x + b • y) ≥ g x ^ a * h y ^ b) :
    ∫⁻ x, f x ≥ (∫⁻ x, g x) ^ a * (∫⁻ x, h x) ^ b :=
  hasPrekopaLeindler_fin n f g h hf hg hh a b ha hb hab hineq

theorem brunnMinkowski_multiplicative {n : ℕ}
    (A B : Set (Fin n → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b := by
  rw [← measure_toMeasurable (a • A + b • B)]
  let C := toMeasurable volume (a • A + b • B)
  have hC : MeasurableSet C := measurableSet_toMeasurable _ _
  have H := prekopa_leindler_fin
    (C.indicator fun _ ↦ (1 : ℝ≥0∞))
    (A.indicator fun _ ↦ (1 : ℝ≥0∞))
    (B.indicator fun _ ↦ (1 : ℝ≥0∞))
    (measurable_const.indicator hC) (measurable_const.indicator hA)
    (measurable_const.indicator hB) a b ha.le hb.le hab ?_
  · simpa [C, measure_toMeasurable, lintegral_indicator_const hC,
      lintegral_indicator_const hA, lintegral_indicator_const hB] using H
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy : a • x + b • y ∈ C := by
          apply subset_toMeasurable (volume : Measure (Fin n → ℝ))
          exact ⟨a • x, ⟨x, hx, rfl⟩, b • y, ⟨y, hy, rfl⟩, rfl⟩
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hxy]
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

theorem brunnMinkowski_multiplicative_of_hasPrekopaLeindler
    {E : Type*} [AddCommMonoid E] [Module ℝ E] [MeasureSpace E]
    (hPL : HasPrekopaLeindler E)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b := by
  rw [← measure_toMeasurable (a • A + b • B)]
  let C := toMeasurable volume (a • A + b • B)
  have hC : MeasurableSet C := measurableSet_toMeasurable _ _
  have H := hPL
    (C.indicator fun _ ↦ (1 : ℝ≥0∞))
    (A.indicator fun _ ↦ (1 : ℝ≥0∞))
    (B.indicator fun _ ↦ (1 : ℝ≥0∞))
    (measurable_const.indicator hC) (measurable_const.indicator hA)
    (measurable_const.indicator hB) a b ha.le hb.le hab ?_
  · simpa [C, measure_toMeasurable, lintegral_indicator_const hC,
      lintegral_indicator_const hA, lintegral_indicator_const hB] using H
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy : a • x + b • y ∈ C := by
          apply subset_toMeasurable (volume : Measure E)
          exact ⟨a • x, ⟨x, hx, rfl⟩, b • y, ⟨y, hy, rfl⟩, rfl⟩
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hxy]
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hb]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha]

theorem hasPrekopaLeindler_euclidean (n : ℕ) :
    HasPrekopaLeindler (EuclideanSpace ℝ (Fin n)) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  have he : MeasurePreserving e := by
    change MeasurePreserving (@WithLp.toLp 2 (Fin n → ℝ)) volume volume
    exact PiLp.volume_preserving_toLp (Fin n)
  exact hasPrekopaLeindler_of_measurePreserving_linearEquiv e he
    (hasPrekopaLeindler_fin n)

theorem brunnMinkowski_multiplicative_euclidean {n : ℕ}
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    volume (a • A + b • B) ≥ volume A ^ a * volume B ^ b :=
  brunnMinkowski_multiplicative_of_hasPrekopaLeindler
    (hasPrekopaLeindler_euclidean n) A B hA hB a b ha hb hab

theorem euclidean_isodiametric {n : ℕ}
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) (d : ℝ) (hd : 0 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    volume A ≤ volume (Metric.closedBall (0 : Fin n → ℝ) (d / 2)) := by
  let M : Set (Fin n → ℝ) := ((2 : ℝ)⁻¹ • A) + ((2 : ℝ)⁻¹ • (-A))
  have hnegA : MeasurableSet (-A) := hA.neg
  have hBM : volume M ≥
      volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
    exact brunnMinkowski_multiplicative A (-A) hA hnegA
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num) (by norm_num)
  have hmeasureNeg : volume (-A) = volume A := Measure.measure_neg volume A
  have hrpow : volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ = volume A := by
    rw [← ENNReal.rpow_add_of_nonneg (x := volume A)
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num)]
    norm_num
  have hvolAM : volume A ≤ volume M := by
    calc
      volume A = volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ := hrpow.symm
      _ = volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
        rw [hmeasureNeg]
      _ ≤ volume M := hBM
  refine hvolAM.trans (measure_mono ?_)
  intro z hz
  rcases hz with ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨ny, hny, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • ny‖ =
        (2 : ℝ)⁻¹ * ‖x - (-ny)‖ := by
      rw [sub_neg_eq_add, ← smul_add, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hhalf]
    _ = (2 : ℝ)⁻¹ * dist x (-ny) := by rw [dist_eq_norm]
    _ ≤ (2 : ℝ)⁻¹ * d :=
      mul_le_mul_of_nonneg_left (hdiam x hx (-ny) hny) hhalf
    _ = d / 2 := by ring

theorem euclideanSpace_isodiametric {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (d : ℝ) (hd : 0 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    volume A ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (d / 2)) := by
  let M : Set (EuclideanSpace ℝ (Fin n)) :=
    ((2 : ℝ)⁻¹ • A) + ((2 : ℝ)⁻¹ • (-A))
  have hnegA : MeasurableSet (-A) := hA.neg
  have hBM : volume M ≥
      volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
    exact brunnMinkowski_multiplicative_euclidean A (-A) hA hnegA
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num) (by norm_num)
  have hmeasureNeg : volume (-A) = volume A := Measure.measure_neg volume A
  have hrpow : volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ = volume A := by
    rw [← ENNReal.rpow_add_of_nonneg (x := volume A)
      (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) (by norm_num)]
    norm_num
  have hvolAM : volume A ≤ volume M := by
    calc
      volume A = volume A ^ (2 : ℝ)⁻¹ * volume A ^ (2 : ℝ)⁻¹ := hrpow.symm
      _ = volume A ^ (2 : ℝ)⁻¹ * volume (-A) ^ (2 : ℝ)⁻¹ := by
        rw [hmeasureNeg]
      _ ≤ volume M := hBM
  refine hvolAM.trans (measure_mono ?_)
  intro z hz
  rcases hz with ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨ny, hny, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖(2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • ny‖ =
        (2 : ℝ)⁻¹ * ‖x - (-ny)‖ := by
      rw [sub_neg_eq_add, ← smul_add, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hhalf]
    _ = (2 : ℝ)⁻¹ * dist x (-ny) := by rw [dist_eq_norm]
    _ ≤ (2 : ℝ)⁻¹ * d :=
      mul_le_mul_of_nonneg_left (hdiam x hx (-ny) hny) hhalf
    _ = d / 2 := by ring

theorem sphere_isodiametric {n : ℕ} (hn : 0 < n)
    (A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hA : MeasurableSet A) (d : ℝ) (hd1 : 1 ≤ d)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ d) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere A ≤
      ENNReal.ofReal ((d / 2) ^ n) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ := by
  let C : Set (EuclideanSpace ℝ (Fin n)) :=
    Set.Ioo (0 : ℝ) 1 • ((↑) '' A)
  have hnorm (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property
  have hcone : ∀ p ∈ C, ∀ q ∈ C, dist p q ≤ d := by
    intro p hp q hq
    rcases hp with ⟨r, hr, xr, hxr, rfl⟩
    rcases hxr with ⟨x, hx, rfl⟩
    rcases hq with ⟨s, hs, ys, hys, rfl⟩
    rcases hys with ⟨y, hy, rfl⟩
    have hxy : dist (x : EuclideanSpace ℝ (Fin n)) y ≤ d := by
      simpa only [Subtype.dist_eq] using hdiam x hx y hy
    have aux (hrs : r ≤ s) : dist
        (r • (x : EuclideanSpace ℝ (Fin n))) (s • (y : EuclideanSpace ℝ (Fin n))) ≤ d := by
      have hr0 : 0 ≤ r := hr.1.le
      have hrs0 : 0 ≤ s - r := sub_nonneg.mpr hrs
      calc
        dist (r • (x : EuclideanSpace ℝ (Fin n))) (s • (y : EuclideanSpace ℝ (Fin n))) =
            ‖r • ((x : EuclideanSpace ℝ (Fin n)) - y) + (r - s) • y‖ := by
          rw [dist_eq_norm]
          congr 1
          module
        _ ≤ ‖r • ((x : EuclideanSpace ℝ (Fin n)) - y)‖ + ‖(r - s) • (y : EuclideanSpace ℝ (Fin n))‖ :=
          norm_add_le _ _
        _ = r * dist (x : EuclideanSpace ℝ (Fin n)) y + (s - r) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hr0, abs_of_nonpos (sub_nonpos.mpr hrs), hnorm y,
            mul_one, dist_eq_norm]
          ring
        _ ≤ r * d + (s - r) := by gcongr
        _ ≤ d := by nlinarith [hr.2, hs.2]
    rcases le_total r s with hrs | hsr
    · exact aux hrs
    · rw [dist_comm]
      have hyx : dist (y : EuclideanSpace ℝ (Fin n)) x ≤ d := by
        simpa [dist_comm] using hxy
      have hs0 : 0 ≤ s := hs.1.le
      have hsr0 : 0 ≤ r - s := sub_nonneg.mpr hsr
      calc
        dist (s • (y : EuclideanSpace ℝ (Fin n))) (r • (x : EuclideanSpace ℝ (Fin n))) =
            ‖s • ((y : EuclideanSpace ℝ (Fin n)) - x) + (s - r) • x‖ := by
          rw [dist_eq_norm]
          congr 1
          module
        _ ≤ ‖s • ((y : EuclideanSpace ℝ (Fin n)) - x)‖ + ‖(s - r) • (x : EuclideanSpace ℝ (Fin n))‖ :=
          norm_add_le _ _
        _ = s * dist (y : EuclideanSpace ℝ (Fin n)) x + (r - s) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hs0, abs_of_nonpos (sub_nonpos.mpr hsr), hnorm x,
            mul_one, dist_eq_norm]
          ring
        _ ≤ s * d + (r - s) := by gcongr
        _ ≤ d := by nlinarith [hr.2, hs.2]
  have hCsubset : C ⊆ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro p hp
    rcases hp with ⟨r, hr, xr, hxr, rfl⟩
    rcases hxr with ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.1.le, hnorm x, mul_one]
    exact hr.2.le
  have hclosureSubset : closure C ⊆ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    closure_minimal hCsubset Metric.isClosed_closedBall
  have hbounded : Bornology.IsBounded (closure C) :=
    Metric.isBounded_closedBall.subset hclosureSubset
  have hdiamC : Metric.diam C ≤ d :=
    Metric.diam_le_of_forall_dist_le (by linarith) hcone
  have hdiamClosure : ∀ p ∈ closure C, ∀ q ∈ closure C, dist p q ≤ d := by
    intro p hp q hq
    exact (Metric.dist_le_diam_of_mem hbounded hp hq).trans (by
      simpa only [Metric.diam_closure] using hdiamC)
  have hvolC : volume C ≤ volume
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (d / 2)) :=
    (measure_mono subset_closure).trans <|
      euclideanSpace_isodiametric (closure C) isClosed_closure.measurableSet d
        (by linarith) hdiamClosure
  rw [Measure.toSphere_apply' volume hA]
  simp only [finrank_euclideanSpace_fin]
  calc
    (n : ℝ≥0∞) * volume C ≤
        (n : ℝ≥0∞) * volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (d / 2)) := by gcongr
    _ = (n : ℝ≥0∞) *
        (ENNReal.ofReal ((d / 2) ^ n) * volume
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
      rw [Measure.addHaar_closedBall' volume (0 : EuclideanSpace ℝ (Fin n)) (by linarith),
        finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal ((d / 2) ^ n) * volume.toSphere Set.univ := by
      rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
        Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
      ac_rfl

lemma Gamma_half_step_sq_le {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ^ 2 ≤ x * Real.Gamma x ^ 2 := by
  have H := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    hx (add_pos hx zero_lt_one) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hGx : 0 ≤ Real.Gamma x := (Real.Gamma_pos_of_pos hx).le
  have hGx1 : 0 ≤ Real.Gamma (x + 1) :=
    (Real.Gamma_pos_of_pos (add_pos hx zero_lt_one)).le
  have harg : (1 / 2 : ℝ) * x + 1 / 2 * (x + 1) = x + 1 / 2 := by ring
  rw [harg] at H
  have hsqrt : Real.Gamma x ^ (1 / 2 : ℝ) *
      Real.Gamma (x + 1) ^ (1 / 2 : ℝ) =
      Real.sqrt (Real.Gamma x * Real.Gamma (x + 1)) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hGx hGx1]
  rw [hsqrt, Real.Gamma_add_one hx.ne'] at H
  have hsquare := Real.sq_sqrt (mul_nonneg hGx (mul_nonneg hx.le hGx))
  have hGhalf : 0 ≤ Real.Gamma (x + 1 / 2) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  nlinarith [Real.sqrt_nonneg (Real.Gamma x * (x * Real.Gamma x))]

lemma unitBallConstant_le_sqrt_mul_succ (n : ℕ) :
    Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) ≤
      Real.sqrt (n + 1 : ℝ) *
        (Real.sqrt Real.pi ^ (n + 1) /
          Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) := by
  let x : ℝ := (n : ℝ) / 2 + 1
  have hx : 0 < x := by positivity
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGhalf : 0 < Real.Gamma (x + 1 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hsquare := Gamma_half_step_sq_le hx
  have hsqrtx : Real.Gamma (x + 1 / 2) ≤ Real.sqrt x * Real.Gamma x := by
    have hsqrt_sq : (Real.sqrt x * Real.Gamma x) ^ 2 = x * Real.Gamma x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hx.le]
    have hsqrt_nonneg : 0 ≤ Real.sqrt x * Real.Gamma x :=
      mul_nonneg (Real.sqrt_nonneg _) hGx.le
    nlinarith
  have hxle : x ≤ (n + 1 : ℝ) := by
    dsimp only [x]
    norm_num
  have hsqrtle : Real.sqrt x ≤ Real.sqrt (n + 1 : ℝ) :=
    Real.sqrt_le_sqrt hxle
  have honepi : 1 ≤ Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    linarith [Real.pi_gt_three]
  have hGammaBound : Real.Gamma (x + 1 / 2) ≤
      Real.sqrt (n + 1 : ℝ) * Real.sqrt Real.pi * Real.Gamma x := by
    calc
      Real.Gamma (x + 1 / 2) ≤ Real.sqrt x * Real.Gamma x := hsqrtx
      _ ≤ Real.sqrt (n + 1 : ℝ) * Real.Gamma x := by gcongr
      _ ≤ Real.sqrt (n + 1 : ℝ) * Real.sqrt Real.pi * Real.Gamma x := by
        have hG : Real.Gamma x ≤ Real.sqrt Real.pi * Real.Gamma x := by
          nlinarith
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hG
            (Real.sqrt_nonneg (n + 1 : ℝ))
  have hpow : 0 ≤ Real.sqrt Real.pi ^ n := pow_nonneg (Real.sqrt_nonneg _) _
  have harg2 : (((n + 1 : ℕ) : ℝ) / 2 + 1) = x + 1 / 2 := by
    dsimp only [x]
    push_cast
    ring
  rw [harg2, ← mul_div_assoc, div_le_div_iff₀ hGx hGhalf]
  calc
    Real.sqrt Real.pi ^ n * Real.Gamma (x + 1 / 2) ≤ Real.sqrt Real.pi ^ n *
        (Real.sqrt (n + 1 : ℝ) * Real.sqrt Real.pi * Real.Gamma x) := by gcongr
    _ = _ := by rw [pow_succ]; ring

lemma exists_orthonormalBasis_zero_eq {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ
        (EuclideanSpace ℝ (Fin (n + 1))), b 0 = x := by
  let v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun _ ↦ x
  have hv : Orthonormal ℝ (({0} : Set (Fin (n + 1))).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa [v] using hx
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))
      (ι := Fin (n + 1)) (by simp) hv with ⟨b, hb⟩
  exact ⟨b, hb 0 (by simp)⟩

lemma euclidean_unitBall_slab_volume_bound {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    volume {y : EuclideanSpace ℝ (Fin (n + 1)) |
        ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} ≤
      ENNReal.ofReal (2 * t) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rcases exists_orthonormalBasis_zero_eq x hx with ⟨b, hb⟩
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) 0
  let coord : EuclideanSpace ℝ (Fin (n + 1)) → ℝ × (Fin n → ℝ) :=
    fun y ↦ split (WithLp.ofLp (b.repr y))
  let tailBall : Set (Fin n → ℝ) :=
    (WithLp.toLp 2) ⁻¹'
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let R : Set (ℝ × (Fin n → ℝ)) := Set.Icc (-t) t ×ˢ tailBall
  have hcoord : MeasurePreserving coord volume volume := by
    exact (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) 0).comp
        ((PiLp.volume_preserving_ofLp (Fin (n + 1))).comp
          b.measurePreserving_repr)
  have htailMeas : MeasurableSet tailBall := by
    exact measurableSet_closedBall.preimage
      (PiLp.volume_preserving_toLp (Fin n)).measurable
  have hRMeas : MeasurableSet R := measurableSet_Icc.prod htailMeas
  have htailVol : volume tailBall =
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet
  have hsubset : {y : EuclideanSpace ℝ (Fin (n + 1)) |
      ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} ⊆ coord ⁻¹' R := by
    intro y hy
    have hfirst : (coord y).1 = inner ℝ x y := by
      simp [coord, split, hb, OrthonormalBasis.repr_apply_apply]
    have htail : ‖WithLp.toLp 2 (coord y).2‖ ≤ 1 := by
      let z := b.repr y
      have hnormz : ‖z‖ = ‖y‖ := b.repr.norm_map y
      have hsqTail : ‖WithLp.toLp 2 (coord y).2‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        rw [Fin.sum_univ_succAbove (fun i : Fin (n + 1) ↦
          ‖z.ofLp i‖ ^ 2) 0]
        simp only [coord, split, z, MeasurableEquiv.piFinSuccAbove_apply]
        exact le_add_of_nonneg_left (sq_nonneg _)
      have htailz : ‖WithLp.toLp 2 (coord y).2‖ ≤ ‖z‖ :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsqTail
      exact htailz.trans (by simpa [hnormz] using hy.1)
    constructor
    · constructor
      · rw [hfirst]
        exact neg_le_of_abs_le hy.2
      · rw [hfirst]
        exact (le_abs_self _).trans hy.2
    · simpa [tailBall, Metric.mem_closedBall, dist_zero_right] using htail
  calc
    volume {y : EuclideanSpace ℝ (Fin (n + 1)) |
        ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} ≤ volume (coord ⁻¹' R) :=
      measure_mono hsubset
    _ = volume R := hcoord.measure_preimage hRMeas.nullMeasurableSet
    _ = volume (Set.Icc (-t) t) * volume tailBall := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
    _ = ENNReal.ofReal (2 * t) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      rw [Real.volume_Icc, htailVol]
      congr 2
      ring

lemma euclidean_unitBall_volume_step {n : ℕ} (hn : 0 < n) :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
      ENNReal.ofReal (Real.sqrt (n + 1 : ℝ)) *
        volume (Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (unitBallConstant_le_sqrt_mul_succ n)

lemma spherical_equatorial_strip_bound {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere
        {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤ t} ≤
      ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere Set.univ := by
  let A : Set (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    {y | |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤ t}
  let C : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    Set.Ioo (0 : ℝ) 1 • ((↑) '' A)
  have hA : MeasurableSet A := by
    dsimp only [A]
    measurability
  have hnorm (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.property
  have hCsubset : C ⊆ {y : EuclideanSpace ℝ (Fin (n + 1)) |
      ‖y‖ ≤ 1 ∧ |inner ℝ x y| ≤ t} := by
    intro p hp
    rcases hp with ⟨r, hr, yr, hyr, rfl⟩
    rcases hyr with ⟨y, hy, rfl⟩
    constructor
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1.le, hnorm y,
        mul_one]
      exact hr.2.le
    · rw [inner_smul_right, abs_mul, abs_of_nonneg hr.1.le]
      calc
        r * |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| ≤
            1 * |inner ℝ x (y : EuclideanSpace ℝ (Fin (n + 1)))| := by
          exact mul_le_mul_of_nonneg_right hr.2.le (abs_nonneg _)
        _ ≤ t := by simpa [A] using hy
  have hCvol : volume C ≤ ENNReal.ofReal (2 * t) *
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (measure_mono hCsubset).trans (euclidean_unitBall_slab_volume_bound x hx t ht)
  have hstep := euclidean_unitBall_volume_step hn
  rw [Measure.toSphere_apply' volume hA]
  simp only [finrank_euclideanSpace_fin]
  calc
    ((n + 1 : ℕ) : ℝ≥0∞) * volume C ≤
        ((n + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (2 * t) *
            volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
      gcongr
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (2 * t) *
            (ENNReal.ofReal (Real.sqrt (n + 1 : ℝ)) *
              volume (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) := by
      gcongr
    _ = ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
        volume.toSphere Set.univ := by
      rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
        Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
      calc
        ((n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (2 * t) *
              (ENNReal.ofReal (Real.sqrt (n + 1 : ℝ)) *
                volume (Metric.ball
                  (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) =
            ((n + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal (2 * t) *
                ENNReal.ofReal (Real.sqrt (n + 1 : ℝ))) *
              volume (Metric.ball
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by ac_rfl
        _ = ((n + 1 : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
              volume (Metric.ball
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t)]
        _ = ENNReal.ofReal (2 * t * Real.sqrt (n + 1 : ℝ)) *
            (((n + 1 : ℕ) : ℝ≥0∞) *
              volume (Metric.ball
                (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by ac_rfl

end Erdos615.BrunnMinkowski

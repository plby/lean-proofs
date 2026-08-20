import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: PlanarNonparallelHalfOpenTerminalTriangle]
lemma PlanarNonparallelHalfOpenTerminalTriangle
    (x dA dB : EuclideanSpace ℝ (Fin 2)) (t k : ℝ)
    (ht : 0 < t)
    (hk : 0 < k)
    (hli : LinearIndependent ℝ ![dA, dB]) :
    ∃ Q : Set (EuclideanSpace ℝ (Fin 2)),
      Convex ℝ Q ∧
      IsCompact (closure Q) ∧
      x ∈ closure Q ∧
     (x + t • dB) ∈ Q ∧
     x ∉ Q ∧
      (∃ q ∈ Q, q ≠ x + t • dB ∧
        ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ r = k * s ∧ s + r < t ∧
          s + r = t / 2 ∧
          q = x + s • dA + r • dB) ∧
     Q \ ({x + t • dB} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
        {q | ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ k * s ≤ r ∧ s + r < t ∧
         q = x + s • dA + r • dB} ∧
      Q ∩
          ({q | ∃ s : ℝ, q = x + s • dA} ∪
            {q | ∃ r : ℝ, q = x + r • dB}) =
        ({x + t • dB} : Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  let C := Fin 2 → ℝ
  let basis : Fin 2 → E := ![dA, dB]
  let L : C →ₗ[ℝ] E := Fintype.linearCombination ℝ basis
  let chart : C → E := fun z => x + L z
  let y0 : C := ![0, t]
  let O : Set C :=
    {z | 0 < z 0 ∧ 0 < z 1 ∧ k * z 0 ≤ z 1 ∧ z 0 + z 1 < t}
  let T : Set C := O ∪ {y0}
  let Q : Set E := chart '' T
  have hL_apply (z : C) : L z = z 0 • dA + z 1 • dB := by
    dsimp [L]
    rw [Fintype.linearCombination_apply]
    rw [Fin.sum_univ_two]
    simp [basis]
  have hL_inj : Function.Injective L := by
    simpa [L, basis] using hli.fintypeLinearCombination_injective
  have hchart_inj : Function.Injective chart := by
    intro z w hzw
    apply hL_inj
    dsimp [chart] at hzw
    exact add_left_cancel hzw
  have hychart : chart y0 = x + t • dB := by
    simp [chart, y0, hL_apply]
  have hTconvex : Convex ℝ T := by
    rw [convex_iff_add_mem]
    intro z hz w hw a b ha hb hab
    rcases hz with hz | hz
    · rcases hw with hw | hw
      · left
        rcases hz with ⟨hz0, hz1, hzK, hzsum⟩
        rcases hw with ⟨hw0, hw1, hwK, hwsum⟩
        dsimp [O] at hz0 hz1 hzK hzsum hw0 hw1 hwK hwsum ⊢
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          subst a
          subst b
          simpa using ⟨hw0, hw1, hwK, hwsum⟩
        · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have haz0 : 0 < a * z 0 := mul_pos haPos hz0
          have haz1 : 0 < a * z 1 := mul_pos haPos hz1
          have hbw0 : 0 ≤ b * w 0 := mul_nonneg hb (le_of_lt hw0)
          have hbw1 : 0 ≤ b * w 1 := mul_nonneg hb (le_of_lt hw1)
          have hza : a * (z 0 + z 1) < a * t :=
            mul_lt_mul_of_pos_left hzsum haPos
          have hwb : b * (w 0 + w 1) ≤ b * t :=
            mul_le_mul_of_nonneg_left (le_of_lt hwsum) hb
          have hzaK : a * (k * z 0) ≤ a * z 1 :=
            mul_le_mul_of_nonneg_left hzK (le_of_lt haPos)
          have hwbK : b * (k * w 0) ≤ b * w 1 :=
            mul_le_mul_of_nonneg_left hwK hb
          constructor
          · change 0 < a * z 0 + b * w 0
            exact add_pos_of_pos_of_nonneg haz0 hbw0
          constructor
          · change 0 < a * z 1 + b * w 1
            exact add_pos_of_pos_of_nonneg haz1 hbw1
          constructor
          · change k * (a * z 0 + b * w 0) ≤ a * z 1 + b * w 1
            nlinarith
          · change (a * z 0 + b * w 0) + (a * z 1 + b * w 1) < t
            nlinarith
      · have hwy : w = y0 := by simpa using hw
        subst w
        by_cases ha0 : a = 0
        · right
          have hb1 : b = 1 := by linarith
          subst a
          subst b
          simp
        · left
          have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          rcases hz with ⟨hz0, hz1, hzK, hzsum⟩
          dsimp [O] at hz0 hz1 hzK hzsum ⊢
          have hzaK : a * (k * z 0) ≤ a * z 1 :=
            mul_le_mul_of_nonneg_left hzK (le_of_lt haPos)
          have hza : a * (z 0 + z 1) < a * t :=
            mul_lt_mul_of_pos_left hzsum haPos
          have hbt : 0 ≤ b * t := mul_nonneg hb (le_of_lt ht)
          constructor
          · change 0 < a * z 0 + b * 0
            nlinarith
          constructor
          · change 0 < a * z 1 + b * t
            nlinarith
          constructor
          · change k * (a * z 0 + b * 0) ≤ a * z 1 + b * t
            nlinarith
          · change (a * z 0 + b * 0) + (a * z 1 + b * t) < t
            nlinarith
    · have hzy : z = y0 := by simpa using hz
      subst z
      rcases hw with hw | hw
      · by_cases hb0 : b = 0
        · right
          have ha1 : a = 1 := by linarith
          subst a
          subst b
          simp
        · left
          have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          rcases hw with ⟨hw0, hw1, hwK, hwsum⟩
          dsimp [O] at hw0 hw1 hwK hwsum ⊢
          have hwbK : b * (k * w 0) ≤ b * w 1 :=
            mul_le_mul_of_nonneg_left hwK (le_of_lt hbPos)
          have hwb : b * (w 0 + w 1) < b * t :=
            mul_lt_mul_of_pos_left hwsum hbPos
          have hat : 0 ≤ a * t := mul_nonneg ha (le_of_lt ht)
          constructor
          · change 0 < a * 0 + b * w 0
            nlinarith
          constructor
          · change 0 < a * t + b * w 1
            nlinarith
          constructor
          · change k * (a * 0 + b * w 0) ≤ a * t + b * w 1
            nlinarith
          · change (a * 0 + b * w 0) + (a * t + b * w 1) < t
            nlinarith
      · have hwy : w = y0 := by simpa using hw
        subst w
        right
        ext i
        fin_cases i
        · change a * 0 + b * 0 = 0
          ring
        · change a * t + b * t = t
          nlinarith
  have hQconvex : Convex ℝ Q := by
    have hlin : Convex ℝ (L '' T) := hTconvex.linear_image L
    have htrans : Convex ℝ ((fun z : E => x + z) '' (L '' T)) :=
      hlin.translate x
    simpa only [Q, chart, Set.image_image, Function.comp_apply] using htrans
  have hQbounded : Bornology.IsBounded Q := by
    rw [Metric.isBounded_iff_subset_closedBall x]
    refine ⟨t * (‖dA‖ + ‖dB‖), ?_⟩
    rintro q ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hdiff : chart z - x = L z := by simp [chart]
    rw [hdiff, hL_apply]
    rcases hz with hz | hz
    · rcases hz with ⟨hz0, hz1, hzsum⟩
      have hz0t : z 0 < t := by linarith
      have hz1t : z 1 < t := by linarith
      calc
        ‖z 0 • dA + z 1 • dB‖ ≤ ‖z 0 • dA‖ + ‖z 1 • dB‖ :=
          norm_add_le _ _
        _ = z 0 * ‖dA‖ + z 1 * ‖dB‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hz0, abs_of_pos hz1]
        _ ≤ t * ‖dA‖ + t * ‖dB‖ := by
         exact add_le_add
            (mul_le_mul_of_nonneg_right (le_of_lt hz0t) (norm_nonneg dA))
            (mul_le_mul_of_nonneg_right (le_of_lt hz1t) (norm_nonneg dB))
        _ = t * (‖dA‖ + ‖dB‖) := by ring
    · have hzy : z = y0 := by simpa using hz
      subst z
      simp only [y0, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, zero_smul, zero_add]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hnonneg := norm_nonneg dA
      nlinarith [mul_nonneg (le_of_lt ht) hnonneg]
  have hQcompact : IsCompact (closure Q) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hQbounded.closure
  have hxclosure : x ∈ closure Q := by
    rw [Metric.mem_closure_iff]
    intro eps heps
    let K : ℝ := k + 2
    let M : ℝ := ‖dA‖ + (k + 1) * ‖dB‖ + 1
    let delta : ℝ := min (t / (2 * K)) (eps / (2 * M))
    have hK : 0 < K := by dsimp [K]; linarith
    have hM : 0 < M := by
      dsimp [M]
      have hk1 : 0 ≤ k + 1 := by linarith
      nlinarith [norm_nonneg dA, norm_nonneg dB,
        mul_nonneg hk1 (norm_nonneg dB)]
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact lt_min (by positivity) (div_pos heps (by positivity))
    have hdelta_t : delta ≤ t / (2 * K) := min_le_left _ _
    have hdelta_eps : delta ≤ eps / (2 * M) := min_le_right _ _
    let z : C := ![delta, (k + 1) * delta]
    refine ⟨chart z, ?_, ?_⟩
    · exact ⟨z, by
        left
        dsimp [O, z]
        constructor
        · simpa using hdelta
        constructor
        · have hk1 : 0 < k + 1 := by linarith
          change 0 < (k + 1) * delta
          positivity
        · constructor
          · nlinarith
          · have hmul : K * delta ≤ t / 2 := by
              calc
                K * delta ≤ K * (t / (2 * K)) :=
                  mul_le_mul_of_nonneg_left hdelta_t (le_of_lt hK)
                _ = t / 2 := by field_simp
            dsimp [K] at hmul
            change delta + (k + 1) * delta < t
            nlinarith, rfl⟩
    · rw [dist_eq_norm]
      have hdiff : x - chart z = -(L z) := by simp [chart]
      rw [hdiff, norm_neg, hL_apply]
      have hnorm :
          ‖delta • dA + ((k + 1) * delta) • dB‖ ≤
            delta * (‖dA‖ + (k + 1) * ‖dB‖) := by
        have hk1 : 0 < k + 1 := by linarith
        have hkd : 0 < (k + 1) * delta := mul_pos hk1 hdelta
        calc
          ‖delta • dA + ((k + 1) * delta) • dB‖ ≤
              ‖delta • dA‖ + ‖((k + 1) * delta) • dB‖ :=
            norm_add_le _ _
          _ = delta * (‖dA‖ + (k + 1) * ‖dB‖) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos hdelta, abs_of_pos hkd]
            ring
      have hsumM : ‖dA‖ + (k + 1) * ‖dB‖ < M := by
        dsimp [M]
        linarith
      have hstrict : delta * (‖dA‖ + (k + 1) * ‖dB‖) < delta * M :=
        mul_lt_mul_of_pos_left hsumM hdelta
      have hbound : delta * M ≤ eps / 2 := by
        calc
          delta * M ≤ (eps / (2 * M)) * M :=
            mul_le_mul_of_nonneg_right hdelta_eps (le_of_lt hM)
          _ = eps / 2 := by field_simp
      exact lt_of_le_of_lt hnorm (by linarith)
  have hyQ : x + t • dB ∈ Q := by
    exact ⟨y0, Set.mem_union_right O (Set.mem_singleton y0), hychart⟩
  have hxnotQ : x ∉ Q := by
    rintro ⟨z, hz, hzx⟩
    have hLzero : L z = 0 := by
      dsimp [chart] at hzx
      have hsame : x + L z = x + 0 := by simpa using hzx
      exact add_left_cancel hsame
    have hzZero : z = 0 := hL_inj (by simpa using hLzero)
    rcases hz with hz | hz
    · have hzpos : 0 < z 0 := hz.1
      rw [hzZero] at hzpos
      change 0 < 0 at hzpos
      linarith
    · have hzy : z = y0 := by simpa using hz
      have hzeroT : (0 : ℝ) = t := by
        have hfun := congrFun (hzZero.symm.trans hzy) (1 : Fin 2)
        dsimp [C, y0] at hfun
        exact hfun
      linarith
  have hboundary : ∃ q ∈ Q, q ≠ x + t • dB ∧
      ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ r = k * s ∧ s + r < t ∧
        s + r = t / 2 ∧
        q = x + s • dA + r • dB := by
    let K : ℝ := k + 1
    have hK : 0 < K := by dsimp [K]; linarith
    let s : ℝ := t / (2 * K)
    let r : ℝ := k * s
    have hs : 0 < s := div_pos ht (by positivity)
    have hr : 0 < r := by dsimp [r]; positivity
    have hsum_eq : s + r = t / 2 := by
      have hKs : K * s = t / 2 := by
        dsimp [s]
        field_simp
      dsimp [K, r] at hKs ⊢
      nlinarith
    have hsum : s + r < t := by
      nlinarith
    let z : C := ![s, r]
    refine ⟨chart z, ?_, ?_, s, r, hs, hr, by simp [r], hsum, hsum_eq, ?_⟩
    · refine ⟨z, ?_, rfl⟩
      left
      exact ⟨by simpa [z] using hs, by simpa [z] using hr,
        by simp [z, r], by simpa [z] using hsum⟩
    · intro heq
      have hzEq : z = y0 := hchart_inj (heq.trans hychart.symm)
      have hz0 := congrFun hzEq 0
      dsimp [z, y0] at hz0
      linarith
    · simp [chart, z, hL_apply, add_assoc]
  have hsector :
      Q \ ({x + t • dB} : Set E) ⊆
       {q | ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ k * s ≤ r ∧ s + r < t ∧
          q = x + s • dA + r • dB} := by
    rintro q ⟨⟨z, hz, hzq⟩, hqne⟩
    rcases hz with hz | hz
    · rcases hz with ⟨hz0, hz1, hzK, hzsum⟩
      refine ⟨z 0, z 1, hz0, hz1, hzK, hzsum, ?_⟩
      rw [← hzq]
      simp [chart, hL_apply, add_assoc]
    · have hzy : z = y0 := by simpa using hz
      have hqy : q = x + t • dB := hzq ▸ hzy ▸ hychart
      exact False.elim (hqne (by simpa [hqy]))
  have hbranch :
      Q ∩
          ({q | ∃ s : ℝ, q = x + s • dA} ∪
            {q | ∃ r : ℝ, q = x + r • dB}) =
        ({x + t • dB} : Set E) := by
    ext q
    constructor
    · rintro ⟨⟨z, hz, hzq⟩, haxis⟩
      rcases hz with hz | hz
      · rcases hz with ⟨hz0, hz1, _hzK, _hzsum⟩
        rcases haxis with ⟨s, hs⟩ | ⟨r, hr⟩
        · let w : C := ![s, 0]
          have hcw : chart w = x + s • dA := by simp [chart, w, hL_apply]
          have hzw : z = w := hchart_inj (hzq.trans (hs.trans hcw.symm))
          have hw1 := congrFun hzw 1
          dsimp [w] at hw1
          linarith
        · let w : C := ![0, r]
          have hcw : chart w = x + r • dB := by simp [chart, w, hL_apply]
          have hzw : z = w := hchart_inj (hzq.trans (hr.trans hcw.symm))
          have hw0 := congrFun hzw 0
          dsimp [w] at hw0
          linarith
      · have hzy : z = y0 := by simpa using hz
        have hqy : q = x + t • dB := hzq ▸ hzy ▸ hychart
        simpa [hqy]
    · intro hq
      have hqy : q = x + t • dB := by simpa using hq
      subst q
      refine ⟨hyQ, ?_⟩
      right
      exact ⟨t, rfl⟩
  exact ⟨Q, hQconvex, hQcompact, hxclosure, hyQ, hxnotQ,
    hboundary, hsector, hbranch⟩

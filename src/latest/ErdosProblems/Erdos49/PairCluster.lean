import ErdosProblems.Erdos49.SmoothReciprocal
import ErdosProblems.Erdos49.TripleCluster

/-!
# The two-prime cluster

We count the representations `n = d p₂ p₁` by splitting at
`p₂ = sqrt (N / (dL))`.  Below the split two applications of the prime
counting upper bound suffice.  Above it, the possible `p₂` lie in a short
multiplicative interval, so Mertens' theorem supplies the second logarithm.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def pairSplit (N L d : ℕ) : ℕ := Nat.sqrt (N / (d * L))

def pairUpper (N d : ℕ) : ℕ := Nat.sqrt (N / d)

def pairLowCover (N L D Y : ℕ) : Finset ℕ :=
  (smoothUpTo D L).biUnion fun d ↦
    (Analytic.primeInterval (Y + 1) (pairSplit N L d)).biUnion fun p₂ ↦
      (Analytic.primeInterval p₂ (min (p₂ * L) (N / (d * p₂)))).image
        fun p₁ ↦ d * p₂ * p₁

def pairHighCover (N L D Y : ℕ) : Finset ℕ :=
  (smoothUpTo D L).biUnion fun d ↦
    (Analytic.primeInterval (max (Y + 1) (pairSplit N L d + 1))
      (pairUpper N d)).biUnion fun p₂ ↦
      (Analytic.primeInterval p₂ (min (p₂ * L) (N / (d * p₂)))).image
        fun p₁ ↦ d * p₂ * p₁

lemma pairExceptional_subset_low_union_high
    {N L D R Y : ℕ} (hL : 0 < L) (hYdef : Y = R / L) :
    pairExceptional N L D R ⊆
      pairLowCover N L D Y ∪ pairHighCover N L D Y := by
  intro n hn
  have hndata := Finset.mem_filter.mp hn
  rcases hndata.2 with
    ⟨d, p₂, p₁, hd, hdD, hdsmooth, hp₂, hp₁, hRp₂,
      hp₂p₁, hp₁max, hnfac⟩
  have hnN := (Finset.mem_Icc.mp hndata.1).2
  have hdp₂pos : 0 < d * p₂ := Nat.mul_pos hd hp₂.pos
  have hp₁quot : p₁ ≤ N / (d * p₂) := by
    apply (Nat.le_div_iff_mul_le hdp₂pos).2
    calc
      p₁ * (d * p₂) = n := by rw [hnfac]; ring
      _ ≤ N := hnN
  have hp₂sq : p₂ ^ 2 ≤ N / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    calc
      p₂ ^ 2 * d = d * p₂ * p₂ := by ring
      _ ≤ d * p₂ * p₁ := Nat.mul_le_mul_left (d * p₂) hp₂p₁
      _ = n := hnfac.symm
      _ ≤ N := hnN
  have hp₂upper : p₂ ≤ pairUpper N d := by
    exact Nat.le_sqrt'.2 hp₂sq
  have hYp₂ : Y < p₂ := by
    rw [hYdef]
    exact (Nat.div_lt_iff_lt_mul hL).2 hRp₂
  have hdmem : d ∈ smoothUpTo D L := mem_smoothUpTo.mpr ⟨hdD, hdsmooth⟩
  have hp₁mem : p₁ ∈
      Analytic.primeInterval p₂ (min (p₂ * L) (N / (d * p₂))) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp₂p₁, le_min hp₁max hp₁quot⟩, hp₁⟩
  by_cases hlow : p₂ ≤ pairSplit N L d
  · apply Finset.mem_union_left
    unfold pairLowCover
    apply Finset.mem_biUnion.mpr
    refine ⟨d, hdmem, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p₂, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hlow⟩, hp₂⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨p₁, hp₁mem, hnfac.symm⟩
  · apply Finset.mem_union_right
    unfold pairHighCover
    apply Finset.mem_biUnion.mpr
    refine ⟨d, hdmem, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p₂, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hp₂upper⟩, hp₂⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨p₁, hp₁mem, hnfac.symm⟩

lemma pairUpper_le_split_mul
    {N L d : ℕ} (hL : 0 < L) (hd : 0 < d) :
    pairUpper N d ≤ (pairSplit N L d + 1) * L := by
  let m := N / d
  let q := m / L
  let X := Nat.sqrt q
  let V := Nat.sqrt m
  have hqdef : q = N / (d * L) := by
    simp only [q, m, Nat.div_div_eq_div_mul]
  have hXsq : X ^ 2 ≤ q := Nat.sqrt_le' q
  have hqnext : q < (X + 1) ^ 2 := Nat.lt_succ_sqrt' q
  have hV : V ^ 2 ≤ m := Nat.sqrt_le' m
  have hmdecomp : L * (m / L) + m % L = m := Nat.div_add_mod m L
  have hmod : m % L < L := Nat.mod_lt m hL
  have hm : m < (q + 1) * L := by
    calc
      m = L * (m / L) + m % L := hmdecomp.symm
      _ = m / L * L + m % L := by ring
      _ < m / L * L + L := Nat.add_lt_add_left hmod _
      _ = (q + 1) * L := by simp only [q]; ring
  have hLone : 1 ≤ L := by omega
  have hsquare : V ^ 2 < ((X + 1) * L) ^ 2 := by
    calc
      V ^ 2 ≤ m := hV
      _ < (q + 1) * L := hm
      _ ≤ (X + 1) ^ 2 * L :=
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt hqnext)
      _ ≤ (X + 1) ^ 2 * L ^ 2 := by
        gcongr
        calc
          L = L * 1 := by ring
          _ ≤ L * L := Nat.mul_le_mul_left L hLone
          _ = L ^ 2 := by ring
      _ = ((X + 1) * L) ^ 2 := by ring
  have hVX : V < (X + 1) * L :=
    (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).1 hsquare
  simpa only [pairUpper, pairSplit, m, V, X, q, hqdef] using hVX.le

lemma pairSplit_sq_mul_le_div {N L d : ℕ} (hL : 0 < L) :
    pairSplit N L d ^ 2 * L ≤ N / d := by
  apply (Nat.le_div_iff_mul_le hL).1
  rw [Nat.div_div_eq_div_mul]
  exact Nat.sqrt_le' (N / (d * L))

lemma primeInterval_card_le_primeCounting (u v : ℕ) :
    (Analytic.primeInterval u v).card ≤ Nat.primeCounting v := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  have h := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp h.1).2, h.2⟩

lemma primeCounting_scaled_upper
    {X₀ Y v : ℕ} (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y) (hYv : Y ≤ v)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    (Nat.primeCounting v : ℝ) ≤ 4 * v / Real.log (Y - 1 : ℕ) := by
  have hvX₀ : X₀ ≤ v := hX₀Y.trans hYv
  have hmain := hprime v hvX₀
  have hlogY : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  have hlogmono : Real.log (Y - 1 : ℕ) ≤ Real.log (v : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < Y - 1 by omega)
    · exact_mod_cast (show Y - 1 ≤ v by omega)
  calc
    (Nat.primeCounting v : ℝ) ≤ 4 * v / Real.log v := hmain
    _ ≤ 4 * v / Real.log (Y - 1 : ℕ) := by
      exact div_le_div_of_nonneg_left (by positivity) hlogY hlogmono

def pairCoefficient (L Y : ℕ) : ℝ :=
  (16 + 4 * (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError)) /
    Real.log (Y - 1 : ℕ) ^ 2

lemma primeInterval_sum_cast_scaled_upper
    {X₀ Y u v : ℕ} (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y) (hYv : Y ≤ v)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    (∑ p ∈ Analytic.primeInterval u v, (p : ℝ)) ≤
      4 * (v : ℝ) ^ 2 / Real.log (Y - 1 : ℕ) := by
  let S := Analytic.primeInterval u v
  have hcard : (S.card : ℝ) ≤ Nat.primeCounting v := by
    exact_mod_cast primeInterval_card_le_primeCounting u v
  have hpi := primeCounting_scaled_upper hY hX₀Y hYv hprime
  calc
    (∑ p ∈ Analytic.primeInterval u v, (p : ℝ)) ≤
        ∑ _p ∈ S, (v : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    _ = (S.card : ℝ) * v := by simp
    _ ≤ (Nat.primeCounting v : ℝ) * v := by gcongr
    _ ≤ (4 * v / Real.log (Y - 1 : ℕ)) * v := by gcongr
    _ = 4 * (v : ℝ) ^ 2 / Real.log (Y - 1 : ℕ) := by ring

lemma pairLow_inner_sum_le
    {N L d X₀ Y : ℕ} (hL : 0 < L) (hd : 0 < d)
    (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    (∑ p₂ ∈ Analytic.primeInterval (Y + 1) (pairSplit N L d),
      ((Analytic.primeInterval p₂
        (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤
      16 * ((N / d : ℕ) : ℝ) / Real.log (Y - 1 : ℕ) ^ 2 := by
  let X := pairSplit N L d
  let S := Analytic.primeInterval (Y + 1) X
  have hlog : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  by_cases hYX : Y ≤ X
  · have hsumP := primeInterval_sum_cast_scaled_upper
      hY hX₀Y hYX hprime (u := Y + 1)
    have hinner :
        (∑ p₂ ∈ S,
          ((Analytic.primeInterval p₂
            (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤
          ∑ p₂ ∈ S, 4 * (p₂ : ℝ) * L /
            Real.log (Y - 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro p₂ hp₂
      have hp₂data := Finset.mem_filter.mp hp₂
      have hp₂I := Finset.mem_Icc.mp hp₂data.1
      have hYL : Y ≤ p₂ * L := by
        have hLone : 1 ≤ L := by omega
        nlinarith
      calc
        ((Analytic.primeInterval p₂
          (min (p₂ * L) (N / (d * p₂)))).card : ℝ) ≤
            Nat.primeCounting (p₂ * L) := by
          exact_mod_cast (primeInterval_card_le_primeCounting p₂
            (min (p₂ * L) (N / (d * p₂)))).trans
              (Nat.monotone_primeCounting (min_le_left _ _))
        _ ≤ 4 * (p₂ * L : ℕ) / Real.log (Y - 1 : ℕ) :=
          primeCounting_scaled_upper hY hX₀Y hYL hprime
        _ = 4 * (p₂ : ℝ) * L / Real.log (Y - 1 : ℕ) := by
          push_cast
          ring
    change (∑ p₂ ∈ S, ((Analytic.primeInterval p₂
      (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤ _
    apply hinner.trans
    calc
      (∑ p₂ ∈ S, 4 * (p₂ : ℝ) * L / Real.log (Y - 1 : ℕ)) =
          (4 * L / Real.log (Y - 1 : ℕ)) *
            (∑ p₂ ∈ S, (p₂ : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ (4 * L / Real.log (Y - 1 : ℕ)) *
          (4 * (X : ℝ) ^ 2 / Real.log (Y - 1 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [S, X] using hsumP) (by positivity)
      _ = 16 * ((X ^ 2 * L : ℕ) : ℝ) /
          Real.log (Y - 1 : ℕ) ^ 2 := by
        push_cast
        field_simp
        ring
      _ ≤ 16 * ((N / d : ℕ) : ℝ) /
          Real.log (Y - 1 : ℕ) ^ 2 := by
        gcongr
        exact_mod_cast pairSplit_sq_mul_le_div (N := N) (d := d) hL
  · have hS : S = ∅ := by
      simp [S, Analytic.primeInterval]
      intro x hYx hx hp
      omega
    change (∑ p₂ ∈ S, ((Analytic.primeInterval p₂
      (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤ _
    rw [hS]
    simp only [Finset.sum_empty]
    positivity

lemma pairHigh_inner_sum_le
    {N L d X₀ Y : ℕ} (hL : 0 < L) (hd : 0 < d)
    (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    (∑ p₂ ∈ Analytic.primeInterval
        (max (Y + 1) (pairSplit N L d + 1)) (pairUpper N d),
      ((Analytic.primeInterval p₂
        (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤
      4 * ((N / d : ℕ) : ℝ) *
        (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
          Real.log (Y - 1 : ℕ) ^ 2 := by
  let X := pairSplit N L d
  let U := max (Y + 1) (X + 1)
  let V := pairUpper N d
  let S := Analytic.primeInterval U V
  have hlog : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  by_cases hUV : U ≤ V
  · have hYU : Y ≤ U := by simp only [U]; omega
    have hLone : 1 ≤ L := by omega
    have hVK : V ≤ U * L := by
      calc
        V ≤ (X + 1) * L := by
          simpa only [V, X] using pairUpper_le_split_mul
            (N := N) (d := d) hL hd
        _ ≤ U * L := Nat.mul_le_mul_right L (le_max_right _ _)
    have hrecip := primeReciprocalInterval_scaled_upper
      hY hYU hUV hLone hVK
    have hterm (p₂ : ℕ) (hp₂ : p₂ ∈ S) :
        ((Analytic.primeInterval p₂
          (min (p₂ * L) (N / (d * p₂)))).card : ℝ) ≤
            (4 * ((N / d : ℕ) : ℝ) / Real.log (Y - 1 : ℕ)) *
              ((1 : ℝ) / p₂) := by
      have hp₂data := Finset.mem_filter.mp hp₂
      have hp₂I := Finset.mem_Icc.mp hp₂data.1
      have hYp₂ : Y ≤ p₂ := hYU.trans hp₂I.1
      let Q := N / (d * p₂)
      by_cases hYQ : Y ≤ Q
      · have hcard :
            ((Analytic.primeInterval p₂
              (min (p₂ * L) Q)).card : ℝ) ≤ Nat.primeCounting Q := by
          exact_mod_cast (primeInterval_card_le_primeCounting p₂
            (min (p₂ * L) Q)).trans
              (Nat.monotone_primeCounting (min_le_right _ _))
        have hpi := primeCounting_scaled_upper hY hX₀Y hYQ hprime
        have hQcast : (Q : ℝ) ≤ ((N / d : ℕ) : ℝ) * ((1 : ℝ) / p₂) := by
          change ((N / (d * p₂) : ℕ) : ℝ) ≤ _
          rw [← Nat.div_div_eq_div_mul]
          calc
            (((N / d) / p₂ : ℕ) : ℝ) ≤
                ((N / d : ℕ) : ℝ) / p₂ := Nat.cast_div_le
            _ = ((N / d : ℕ) : ℝ) * ((1 : ℝ) / p₂) := by ring
        calc
          ((Analytic.primeInterval p₂
            (min (p₂ * L) (N / (d * p₂)))).card : ℝ) ≤
              Nat.primeCounting Q := hcard
          _ ≤ 4 * Q / Real.log (Y - 1 : ℕ) := hpi
          _ ≤ 4 * (((N / d : ℕ) : ℝ) * ((1 : ℝ) / p₂)) /
              Real.log (Y - 1 : ℕ) := by gcongr
          _ = (4 * ((N / d : ℕ) : ℝ) /
              Real.log (Y - 1 : ℕ)) * ((1 : ℝ) / p₂) := by ring
      · have hEmpty : Analytic.primeInterval p₂
            (min (p₂ * L) (N / (d * p₂))) = ∅ := by
          simp [Analytic.primeInterval]
          intro x hp₂x hxL hxQ hxPrime
          omega
        rw [hEmpty]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    change (∑ p₂ ∈ S, ((Analytic.primeInterval p₂
      (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤ _
    calc
      (∑ p₂ ∈ S, ((Analytic.primeInterval p₂
        (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤
          ∑ p₂ ∈ S, (4 * ((N / d : ℕ) : ℝ) /
            Real.log (Y - 1 : ℕ)) * ((1 : ℝ) / p₂) := by
        exact Finset.sum_le_sum hterm
      _ = (4 * ((N / d : ℕ) : ℝ) /
          Real.log (Y - 1 : ℕ)) * primeReciprocalInterval U V := by
        unfold primeReciprocalInterval
        rw [Finset.mul_sum]
      _ ≤ (4 * ((N / d : ℕ) : ℝ) /
          Real.log (Y - 1 : ℕ)) *
          ((Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
            Real.log (Y - 1 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 4 * ((N / d : ℕ) : ℝ) *
          (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
            Real.log (Y - 1 : ℕ) ^ 2 := by
        field_simp
  · have hS : S = ∅ := by
      simp [S, Analytic.primeInterval]
      intro x hUx hxV hp
      omega
    change (∑ p₂ ∈ S, ((Analytic.primeInterval p₂
      (min (p₂ * L) (N / (d * p₂)))).card : ℝ)) ≤ _
    rw [hS]
    simp only [Finset.sum_empty]
    positivity [mertensReciprocalError_nonneg]

lemma pairLowCover_card_real_le
    {N L D X₀ Y : ℕ} (hL : 0 < L) (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    ((pairLowCover N L D Y).card : ℝ) ≤
      (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
        (16 / Real.log (Y - 1 : ℕ) ^ 2) := by
  have hlog : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  unfold pairLowCover
  calc
    ((((smoothUpTo D L).biUnion fun d ↦
      (Analytic.primeInterval (Y + 1) (pairSplit N L d)).biUnion fun p₂ ↦
        (Analytic.primeInterval p₂
          (min (p₂ * L) (N / (d * p₂)))).image
            fun p₁ ↦ d * p₂ * p₁).card : ℝ)) ≤
        ∑ d ∈ smoothUpTo D L,
          ∑ p₂ ∈ Analytic.primeInterval (Y + 1) (pairSplit N L d),
            ((Analytic.primeInterval p₂
              (min (p₂ * L) (N / (d * p₂)))).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun d hd ↦ Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun p₂ hp₂ ↦ Finset.card_image_le))
    _ ≤ ∑ d ∈ smoothUpTo D L,
        16 * ((N / d : ℕ) : ℝ) / Real.log (Y - 1 : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hdmem
      exact pairLow_inner_sum_le hL
        (Nat.pos_of_ne_zero (smooth_ne_zero (mem_smoothUpTo.mp hdmem).2))
        hY hX₀Y hprime
    _ ≤ ∑ d ∈ smoothUpTo D L,
        16 * ((N : ℝ) * ((1 : ℝ) / d)) /
          Real.log (Y - 1 : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd0 := smooth_ne_zero (mem_smoothUpTo.mp hdmem).2
      have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      calc
        16 * ((N / d : ℕ) : ℝ) / Real.log (Y - 1 : ℕ) ^ 2 ≤
            16 * ((N : ℝ) / d) / Real.log (Y - 1 : ℕ) ^ 2 := by
          gcongr
        _ = 16 * ((N : ℝ) * ((1 : ℝ) / d)) /
            Real.log (Y - 1 : ℕ) ^ 2 := by ring
    _ = (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
        (16 / Real.log (Y - 1 : ℕ) ^ 2) := by
      calc
        (∑ d ∈ smoothUpTo D L,
          16 * ((N : ℝ) * ((1 : ℝ) / d)) /
            Real.log (Y - 1 : ℕ) ^ 2) =
            ∑ d ∈ smoothUpTo D L,
              ((N : ℝ) * ((1 : ℝ) / d)) *
                (16 / Real.log (Y - 1 : ℕ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = (∑ d ∈ smoothUpTo D L,
              (N : ℝ) * ((1 : ℝ) / d)) *
                (16 / Real.log (Y - 1 : ℕ) ^ 2) := by
          rw [Finset.sum_mul]
        _ = (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
              (16 / Real.log (Y - 1 : ℕ) ^ 2) := by
          rw [Finset.mul_sum]

lemma pairHighCover_card_real_le
    {N L D X₀ Y : ℕ} (hL : 0 < L) (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    ((pairHighCover N L D Y).card : ℝ) ≤
      (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
        (4 * (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
          Real.log (Y - 1 : ℕ) ^ 2) := by
  have hlog : 0 < Real.log ((Y - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y - 1 by omega))
  unfold pairHighCover
  calc
    ((((smoothUpTo D L).biUnion fun d ↦
      (Analytic.primeInterval (max (Y + 1) (pairSplit N L d + 1))
        (pairUpper N d)).biUnion fun p₂ ↦
          (Analytic.primeInterval p₂
            (min (p₂ * L) (N / (d * p₂)))).image
              fun p₁ ↦ d * p₂ * p₁).card : ℝ)) ≤
        ∑ d ∈ smoothUpTo D L,
          ∑ p₂ ∈ Analytic.primeInterval
            (max (Y + 1) (pairSplit N L d + 1)) (pairUpper N d),
            ((Analytic.primeInterval p₂
              (min (p₂ * L) (N / (d * p₂)))).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun d hd ↦ Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun p₂ hp₂ ↦ Finset.card_image_le))
    _ ≤ ∑ d ∈ smoothUpTo D L,
        4 * ((N / d : ℕ) : ℝ) *
          (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
            Real.log (Y - 1 : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hdmem
      exact pairHigh_inner_sum_le hL
        (Nat.pos_of_ne_zero (smooth_ne_zero (mem_smoothUpTo.mp hdmem).2))
        hY hX₀Y hprime
    _ ≤ ∑ d ∈ smoothUpTo D L,
        4 * ((N : ℝ) * ((1 : ℝ) / d)) *
          (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
            Real.log (Y - 1 : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      calc
        4 * ((N / d : ℕ) : ℝ) *
            (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
              Real.log (Y - 1 : ℕ) ^ 2 ≤
          4 * ((N : ℝ) / d) *
            (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
              Real.log (Y - 1 : ℕ) ^ 2 := by
            gcongr
            positivity [mertensReciprocalError_nonneg]
        _ = 4 * ((N : ℝ) * ((1 : ℝ) / d)) *
            (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
              Real.log (Y - 1 : ℕ) ^ 2 := by ring
    _ = (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
        (4 * (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
          Real.log (Y - 1 : ℕ) ^ 2) := by
      let C := 4 * (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
        Real.log (Y - 1 : ℕ) ^ 2
      calc
        (∑ d ∈ smoothUpTo D L,
          4 * ((N : ℝ) * ((1 : ℝ) / d)) *
            (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
              Real.log (Y - 1 : ℕ) ^ 2) =
            ∑ d ∈ smoothUpTo D L,
              ((N : ℝ) * ((1 : ℝ) / d)) * C := by
          apply Finset.sum_congr rfl
          intro d hd
          simp only [C]
          ring
        _ = (∑ d ∈ smoothUpTo D L,
              (N : ℝ) * ((1 : ℝ) / d)) * C := by
          rw [Finset.sum_mul]
        _ = (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) * C := by
          rw [Finset.mul_sum]

theorem pairExceptional_card_real_le
    {N L D R X₀ Y : ℕ} (hL : 0 < L) (hYdef : Y = R / L)
    (hY : 3 ≤ Y) (hX₀Y : X₀ ≤ Y)
    (hprime : ∀ x : ℕ, X₀ ≤ x →
      (Nat.primeCounting x : ℝ) ≤ 4 * x / Real.log x) :
    ((pairExceptional N L D R).card : ℝ) ≤
      (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
        pairCoefficient L Y := by
  have hsubset := pairExceptional_subset_low_union_high
    (N := N) (L := L) (D := D) (R := R) hL hYdef
  have hcard : ((pairExceptional N L D R).card : ℝ) ≤
      (pairLowCover N L D Y).card + (pairHighCover N L D Y).card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans
      (Finset.card_union_le (pairLowCover N L D Y) (pairHighCover N L D Y))
  have hlow := pairLowCover_card_real_le hL hY hX₀Y hprime
    (N := N) (D := D)
  have hhigh := pairHighCover_card_real_le hL hY hX₀Y hprime
    (N := N) (D := D)
  apply hcard.trans
  calc
    ((pairLowCover N L D Y).card : ℝ) +
        (pairHighCover N L D Y).card ≤
      (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
          (16 / Real.log (Y - 1 : ℕ) ^ 2) +
        (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
          (4 * (Real.log (2 * L : ℕ) + 2 * mertensReciprocalError) /
            Real.log (Y - 1 : ℕ) ^ 2) := add_le_add hlow hhigh
    _ = (N : ℝ) * (∑ d ∈ smoothUpTo D L, (1 : ℝ) / d) *
        pairCoefficient L Y := by
      unfold pairCoefficient
      ring

#print axioms pairExceptional_card_real_le

#print axioms pairExceptional_subset_low_union_high
#print axioms pairUpper_le_split_mul

end

end Erdos49

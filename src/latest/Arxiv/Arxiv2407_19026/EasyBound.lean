import Arxiv.Arxiv2407_19026.Easy

/-!
# The explicit bound far from the diagonal

This file formalizes Theorem `t:easy` and Corollary `c:easy`.  Squared bounds
are used internally to avoid artificial square-root and rounding issues for
the integer-valued Ramsey number.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

/-- The square of the real threshold in Theorem `t:easy`. -/
def easyBoundSq (x p : ℝ) (k l : ℕ) : ℝ :=
  16 * (k + l : ℝ) ^ 2 /
    (x ^ k * (1 - p) ^ (2 * l))

lemma pow_le_pow_two_of_two_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) : a ^ n ≤ a ^ 2 := by
  have hn' : n = 2 + (n - 2) := by omega
  rw [hn', pow_add]
  have hpow : a ^ (n - 2) ≤ 1 := pow_le_one₀ ha0 ha1
  simpa using mul_le_mul_of_nonneg_left hpow (pow_nonneg ha0 2)

/-- The squared explicit bound implies the lower bound on `n` used to absorb
the `-n/4` error in the max-cut estimate. -/
lemma four_mul_add_le_of_easyBoundSq {x p : ℝ} (hx : 0 < x)
    (hxp : x < p) (hp : p < 1) {k l n : ℕ} (hk : 2 ≤ k) (hl : 1 ≤ l)
    (hn : easyBoundSq x p k l ≤ (n : ℝ) ^ 2) :
    4 * (k + l : ℝ) ≤ p * (1 - p) * n := by
  have hp0 : 0 < p := hx.trans hxp
  have hy0 : 0 < 1 - p := sub_pos.mpr hp
  have hx1 : x ≤ 1 := le_trans (le_of_lt hxp) (le_of_lt hp)
  have hy1 : 1 - p ≤ 1 := by linarith
  have hden :
      0 < x ^ k * (1 - p) ^ (2 * l) :=
    mul_pos (pow_pos hx _) (pow_pos hy0 _)
  have hraw :
      16 * (k + l : ℝ) ^ 2 ≤
        (n : ℝ) ^ 2 * (x ^ k * (1 - p) ^ (2 * l)) := by
    exact (div_le_iff₀ hden).1 hn
  have hxpow : x ^ k ≤ p ^ 2 := by
    calc
      x ^ k ≤ x ^ 2 :=
        pow_le_pow_two_of_two_le (le_of_lt hx) hx1 hk
      _ ≤ p ^ 2 := by nlinarith [sq_nonneg (p - x)]
  have hypow : (1 - p) ^ (2 * l) ≤ (1 - p) ^ 2 := by
    exact pow_le_pow_two_of_two_le (le_of_lt hy0) hy1 (by omega)
  have hdenle :
      x ^ k * (1 - p) ^ (2 * l) ≤ p ^ 2 * (1 - p) ^ 2 :=
    mul_le_mul hxpow hypow (pow_nonneg (le_of_lt hy0) _) (pow_nonneg (le_of_lt hp0) _)
  have hraw' :
      16 * (k + l : ℝ) ^ 2 ≤
        (n : ℝ) ^ 2 * (p ^ 2 * (1 - p) ^ 2) :=
    hraw.trans (mul_le_mul_of_nonneg_left hdenle (sq_nonneg _))
  have hleft : 0 ≤ 4 * (k + l : ℝ) := by positivity
  have hright : 0 ≤ p * (1 - p) * (n : ℝ) := by positivity
  nlinarith [sq_nonneg (p * (1 - p) * (n : ℝ) - 4 * (k + l : ℝ))]

/-- The blue-neighborhood step preserves the squared explicit bound. -/
lemma easyBoundSq_blue_step {x p : ℝ} (hx : 0 < x) (hxp : x < p)
    (hp : p < 1) {k l n m : ℕ} (hk : 1 ≤ k) (hl : 2 ≤ l)
    (hn : easyBoundSq x p k l ≤ (n : ℝ) ^ 2)
    (hm : (((k + l - 1 : ℕ) : ℝ) / (k + l)) * (1 - p) * n ≤ m) :
    easyBoundSq x p k (l - 1) ≤ (m : ℝ) ^ 2 := by
  have hy0 : 0 < 1 - p := sub_pos.mpr hp
  let q : ℝ := (((k + l - 1 : ℕ) : ℝ) / (k + l))
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hscale0 : 0 ≤ (q * (1 - p)) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hn hscale0
  have hm' : q * (1 - p) * (n : ℝ) ≤ m := by
    simpa [q] using hm
  have hmSq :
      (q * (1 - p) * (n : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hleft0 : 0 ≤ q * (1 - p) * (n : ℝ) := by positivity
    nlinarith [hm', sq_nonneg ((m : ℝ) - q * (1 - p) * n)]
  have hpow :
      (1 - p) ^ (2 * l) =
        (1 - p) ^ (2 * (l - 1)) * (1 - p) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hsum : k + l - 1 = k + (l - 1) := by omega
  have hidentity :
      (q * (1 - p)) ^ 2 * easyBoundSq x p k l =
        easyBoundSq x p k (l - 1) := by
    have hxne : x ≠ 0 := ne_of_gt hx
    have hyne : 1 - p ≠ 0 := ne_of_gt hy0
    dsimp [q, easyBoundSq]
    rw [hpow, hsum]
    push_cast
    field_simp
  calc
    easyBoundSq x p k (l - 1) =
        (q * (1 - p)) ^ 2 * easyBoundSq x p k l := hidentity.symm
    _ ≤ (q * (1 - p)) ^ 2 * (n : ℝ) ^ 2 := hmul
    _ = (q * (1 - p) * (n : ℝ)) ^ 2 := by ring
    _ ≤ (m : ℝ) ^ 2 := hmSq

/-- The squared explicit bound supplies the threshold required by
`candidate_good_of_excess`. -/
lemma easyThreshold_le_scaled_easyBoundSq {x p : ℝ} (hx : 0 < x)
    (hxp : x < p) (hp : p < 1)
    (hgold : (1 - p) ^ 2 = (1 - x) * (p - x))
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    easyThreshold x p k l l ≤
      (1 - p) ^ 2 / (4 * (k + l : ℝ)) * easyBoundSq x p k l := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hone_x : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr (hxp.trans hp))
  have hp_x : p - x ≠ 0 := ne_of_gt (sub_pos.mpr hxp)
  have hs : (k + l : ℝ) ≠ 0 := by positivity
  have hxpow : x ^ k = x ^ (k - 1) * x := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  have hypow :
      (1 - p) ^ (2 * l) =
        (1 - p) ^ 2 * ((1 - x) ^ (l - 1) * (p - x) ^ (l - 1)) := by
    calc
      (1 - p) ^ (2 * l) = ((1 - p) ^ 2) ^ l := by rw [← pow_mul]
      _ = ((1 - x) * (p - x)) ^ l := by rw [hgold]
      _ = ((1 - x) * (p - x)) ^ (l - 1) * ((1 - x) * (p - x)) := by
        conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ]
      _ = (1 - p) ^ 2 * ((1 - x) ^ (l - 1) * (p - x) ^ (l - 1)) := by
        rw [mul_pow, hgold]
        ring
  rw [easyThreshold, easyBoundSq, hxpow, hypow]
  have hden :
      0 < (1 - x) ^ (l - 1) * (p - x) ^ (l - 1) :=
    mul_pos (pow_pos (sub_pos.mpr (hxp.trans hp)) _)
      (pow_pos (sub_pos.mpr hxp) _)
  field_simp
  rw [div_le_div_iff₀ hden hden]
  nlinarith

/-- If every blue degree is below the induction threshold, the max-cut
argument produces a candidate whose excess has the size required in
Theorem `t:easy`. -/
lemma exists_candidate_of_blue_degree_lt {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V]
    (G : SimpleGraph V) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s : ℕ) (hs : 1 ≤ s)
    (hblue : ∀ v : V,
      ((s - 1 : ℕ) : ℝ) / s * (1 - p) * Fintype.card V >
        (blueNeighborsIn G v univ).card)
    (habsorb :
      (s : ℝ) ≤ p * (1 - p) * Fintype.card V) :
    ∃ C : Candidate G, C.X ∪ C.Y = univ ∧
      (1 - p) ^ 2 * (Fintype.card V : ℝ) ^ 2 / (4 * s) <
        C.excess p := by
  classical
  let N : ℝ := Fintype.card V
  let q : ℝ := ((s - 1 : ℕ) : ℝ) / s
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hspos : 0 < (s : ℝ) := by positivity
  have hq :
      q = 1 - 1 / (s : ℝ) := by
    dsimp [q]
    rw [Nat.cast_sub hs]
    field_simp
    ring
  have hdegree : ∀ v : V,
      (p + (1 - p) / s) * N - 1 <
        (redNeighborsIn G v univ).card := by
    intro v
    have hpart := card_redNeighbors_add_card_blueNeighbors G v
    have hpartR :
        ((redNeighborsIn G v univ).card : ℝ) +
              (blueNeighborsIn G v univ).card + 1 = N := by
      dsimp [N]
      exact_mod_cast hpart
    have hb := hblue v
    change ((blueNeighborsIn G v univ).card : ℝ) <
      q * (1 - p) * N at hb
    have hraw :
        N - q * (1 - p) * N - 1 <
          (redNeighborsIn G v univ).card := by
      linarith
    calc
      (p + (1 - p) / s) * N - 1 =
          N - q * (1 - p) * N - 1 := by
        rw [hq]
        ring
      _ < (redNeighborsIn G v univ).card := hraw
  have hsum :
      N * ((p + (1 - p) / s) * N - 1) <
        (redEdgesBetween G univ univ : ℝ) := by
    have h := sum_lt_sum_of_nonempty (s := (univ : Finset V))
      (by simp) (fun v _ ↦ hdegree v)
    simp only [sum_const, card_univ, nsmul_eq_mul] at h
    rw [redEdgesBetween_eq_sum_card]
    push_cast
    simpa [N] using h
  obtain ⟨X, Y, hXY, hunion, hcut⟩ :=
    exists_partition_redEdgesBetween_le_four_mul G univ
  have hcutR :
      (redEdgesBetween G univ univ : ℝ) ≤
        4 * redEdgesBetween G X Y := by
    exact_mod_cast hcut
  have hcardNat :
      X.card + Y.card = Fintype.card V := by
    rw [← card_union_of_disjoint hXY, hunion, card_univ]
  have hcardR :
      (X.card : ℝ) + Y.card = N := by
    dsimp [N]
    exact_mod_cast hcardNat
  have hproduct :
      4 * (X.card : ℝ) * Y.card ≤ N ^ 2 := by
    nlinarith [sq_nonneg ((X.card : ℝ) - Y.card)]
  have hcutLower :
      ((p + (1 - p) / s) * N ^ 2 - N) / 4 <
        (redEdgesBetween G X Y : ℝ) := by
    nlinarith [hsum, hcutR]
  have hexcessLower :
      (((1 - p) / s) * N ^ 2 - N) / 4 <
        excessBetween p G X Y := by
    rw [excessBetween]
    have hpXY :
        4 * (p * (X.card : ℝ) * Y.card) ≤ p * N ^ 2 :=
      by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hproduct (le_of_lt hp0)
    nlinarith [hcutLower, hpXY]
  have habsorbN :
      (s : ℝ) * N ≤ p * (1 - p) * N ^ 2 := by
    have h := mul_le_mul_of_nonneg_right habsorb (le_of_lt hNpos)
    nlinarith
  have htarget :
      (1 - p) ^ 2 * N ^ 2 / (4 * s) ≤
        (((1 - p) / s) * N ^ 2 - N) / 4 := by
    field_simp
    nlinarith [habsorbN]
  have hpos :
      0 < excessBetween p G X Y := by
    exact lt_of_le_of_lt
      (show 0 ≤ (1 - p) ^ 2 * N ^ 2 / (4 * s) by positivity)
      (htarget.trans_lt hexcessLower)
  let C : Candidate G :=
    { X := X
      Y := Y
      X_nonempty := left_nonempty_of_excessBetween_pos hpos
      Y_nonempty := right_nonempty_of_excessBetween_pos hpos
      disjoint := hXY }
  refine ⟨C, ?_, ?_⟩
  · exact hunion
  · simpa [C, Candidate.excess, N] using htarget.trans_lt hexcessLower

/-- Squared, integer-exact form of Theorem `t:easy`.  It avoids hiding a
ceiling in the paper's real-valued display: every natural `n` above the
squared threshold has the asserted Ramsey property. -/
theorem ramseyProperty_of_easyBoundSq {x p : ℝ} (hx : 0 < x)
    (hxp : x < p) (hp : p < 1)
    (hgold : (1 - p) ^ 2 = (1 - x) * (p - x))
    {k l n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hn : easyBoundSq x p k l ≤ (n : ℝ) ^ 2) :
    RamseyProperty k l n := by
  classical
  have hp0 : 0 < p := hx.trans hxp
  induction l generalizing n with
  | zero => omega
  | succ l ih =>
      have hboundPos : 0 < easyBoundSq x p k (l + 1) := by
        apply div_pos
        · positivity
        · exact mul_pos (pow_pos hx _)
            (pow_pos (sub_pos.mpr hp) _)
      have hnSqPos : 0 < (n : ℝ) ^ 2 :=
        lt_of_lt_of_le hboundPos hn
      have hnpos : 0 < n := by
        by_contra hn0
        have : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst n
        norm_num at hnSqPos
      have hnone : 1 ≤ n := hnpos
      by_cases hkone : k = 1
      · subst k
        exact Erdos1014.ramseyProperty_mono_vertices hnone
          (Erdos1014.ramseyProperty_one_left (l + 1))
      · have hktwo : 2 ≤ k := by omega
        by_cases hlzero : l = 0
        · subst l
          exact Erdos1014.ramseyProperty_mono_vertices hnone
            (Erdos1014.ramseyProperty_one_right k)
        · have hlone : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hlzero
          have hltwo : 2 ≤ l + 1 := by omega
          intro G hbad
          let q : ℝ :=
            (((k + (l + 1) - 1 : ℕ) : ℝ) / (k + (l + 1)))
          by_cases hlarge :
              ∃ v : Fin n,
                q * (1 - p) * n ≤
                  (blueNeighborsIn G v univ).card
          · obtain ⟨v, hv⟩ := hlarge
            let B := blueNeighborsIn G v univ
            have hstep :
                easyBoundSq x p k l ≤ (B.card : ℝ) ^ 2 := by
              apply easyBoundSq_blue_step hx hxp hp hk hltwo hn
              simpa [q, B] using hv
            have hprop : RamseyProperty k l B.card :=
              ih hlone hstep
            rcases red_or_blue_of_ramseyProperty B hprop with
              ⟨K, hKB, hK⟩ | ⟨K, hKB, hK⟩
            · exact hbad.1 K hK
            · have hKcompl : Gᶜ.IsNClique l K := by
                simpa using hK
              have hinsCompl : Gᶜ.IsNClique (l + 1) (insert v K) :=
                hKcompl.insert fun u hu ↦ by
                  have huB : u ∈ B := hKB hu
                  exact (mem_redNeighborsIn Gᶜ v u univ).1
                    (by simpa [B, blueNeighborsIn] using huB) |>.2
              have hins : G.IsNIndepSet (l + 1) (insert v K) := by
                simpa using hinsCompl
              exact hbad.2 (insert v K) hins
          · push Not at hlarge
            letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
            have habsorb4 :
                4 * ((k + (l + 1) : ℕ) : ℝ) ≤
                  p * (1 - p) * n :=
              by
                simpa only [Nat.cast_add] using
                  four_mul_add_le_of_easyBoundSq hx hxp hp hktwo
                    (by omega) hn
            have habsorb :
                ((k + (l + 1) : ℕ) : ℝ) ≤
                  p * (1 - p) * n := by
              nlinarith
            have hblue : ∀ v : Fin n,
                (((k + (l + 1)) - 1 : ℕ) : ℝ) /
                    ((k + (l + 1) : ℕ) : ℝ) * (1 - p) *
                    Fintype.card (Fin n) >
                  (blueNeighborsIn G v univ).card := by
              intro v
              simpa [q] using hlarge v
            obtain ⟨C, hCuniv, hCexcess⟩ :=
              exists_candidate_of_blue_degree_lt G p hp0 hp
                (k + (l + 1)) (by omega) hblue (by simpa using habsorb)
            have hscale0 :
                0 ≤ (1 - p) ^ 2 /
                    (4 * ((k + (l + 1) : ℕ) : ℝ)) := by positivity
            have hthreshold :
                easyThreshold x p k (l + 1) (l + 1) ≤
                  C.excess p := by
              calc
                easyThreshold x p k (l + 1) (l + 1) ≤
                    (1 - p) ^ 2 /
                        (4 * ((k + (l + 1) : ℕ) : ℝ)) *
                      easyBoundSq x p k (l + 1) :=
                  by
                    simpa only [Nat.cast_add] using
                      easyThreshold_le_scaled_easyBoundSq
                        (k := k) (l := l + 1) hx hxp hp hgold hk (by omega)
                _ ≤ (1 - p) ^ 2 /
                        (4 * ((k + (l + 1) : ℕ) : ℝ)) *
                      (n : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_left hn hscale0
                _ = (1 - p) ^ 2 *
                      (Fintype.card (Fin n) : ℝ) ^ 2 /
                      (4 * ((k + (l + 1) : ℕ) : ℝ)) := by
                  simp
                  ring
                _ ≤ C.excess p := le_of_lt hCexcess
            have hgood :
                C.Good k (l + 1) (l + 1) :=
              candidate_good_of_excess G x p hx hxp hp C
                k (l + 1) (l + 1) hk (by omega) (by omega) hthreshold
            rcases hgood with
              ⟨K, hKsub, hK⟩ | ⟨K, hKsub, hK⟩ | ⟨K, hKsub, hK⟩
            · exact hbad.1 K hK
            · exact hbad.2 K hK
            · exact hbad.2 K hK

/-- The parameter `x` selected in Theorem `t:easy`. -/
def goldenX (p : ℝ) : ℝ :=
  (1 + Real.sqrt 5) / 2 * p + (1 - Real.sqrt 5) / 2

/-- The lower endpoint of the admissible interval for `p` in Theorem
`t:easy`. -/
def goldenCut : ℝ :=
  (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1)

lemma one_lt_sqrt_five : 1 < Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
    Real.sqrt_nonneg 5]

lemma goldenX_pos {p : ℝ} (hp : goldenCut < p) :
    0 < goldenX p := by
  have hden : 0 < Real.sqrt 5 + 1 := by
    nlinarith [Real.sqrt_nonneg 5]
  have h := (div_lt_iff₀ hden).1 hp
  dsimp [goldenX]
  nlinarith

lemma goldenX_lt {p : ℝ} (hp : p < 1) :
    goldenX p < p := by
  have hs : 1 < Real.sqrt 5 := one_lt_sqrt_five
  dsimp [goldenX]
  nlinarith

lemma goldenX_identity (p : ℝ) :
    (1 - p) ^ 2 = (1 - goldenX p) * (p - goldenX p) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  dsimp [goldenX]
  nlinarith

/-- Integer-rounded form of Theorem `t:easy` for arbitrary admissible
`x,p`.  The square root is exactly the real expression displayed in the
paper, while the natural ceiling records the unavoidable integer rounding. -/
theorem ramseyNumber_le_ceil_sqrt_easyBoundSq {x p : ℝ} (hx : 0 < x)
    (hxp : x < p) (hp : p < 1)
    (hgold : (1 - p) ^ 2 = (1 - x) * (p - x))
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ramseyNumber k l ≤
      ⌈Real.sqrt (easyBoundSq x p k l)⌉₊ := by
  have hsq0 : 0 ≤ easyBoundSq x p k l := by
    apply div_nonneg
    · positivity
    · exact mul_nonneg (pow_nonneg (le_of_lt hx) _)
        (pow_nonneg (le_of_lt (sub_pos.mpr hp)) _)
  let B := Real.sqrt (easyBoundSq x p k l)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = easyBoundSq x p k l := by
    simpa [B] using Real.sq_sqrt hsq0
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hthreshold :
      easyBoundSq x p k l ≤ ((⌈B⌉₊ : ℕ) : ℝ) ^ 2 := by
    rw [← hBsq]
    nlinarith [sq_nonneg ((⌈B⌉₊ : ℝ) - B)]
  exact Erdos1014.ramseyNumber_le_of_property
    (ramseyProperty_of_easyBoundSq hx hxp hp hgold hk hl hthreshold)

/-- Theorem `t:easy`, with the paper's golden-ratio parameter substituted
and the integer ceiling made explicit. -/
theorem ramseyNumber_le_golden_easyBound {p : ℝ}
    (hp0 : goldenCut < p) (hp1 : p < 1)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ramseyNumber k l ≤
      ⌈Real.sqrt (easyBoundSq (goldenX p) p k l)⌉₊ := by
  exact ramseyNumber_le_ceil_sqrt_easyBoundSq
    (goldenX_pos hp0) (goldenX_lt hp1) hp1
    (goldenX_identity p) hk hl

/-- The optimizing choice of `p` used in Corollary `c:easy`. -/
def optimizedP (k l : ℕ) : ℝ :=
  ((Real.sqrt 5 + 1) * k + (2 * Real.sqrt 5 - 2) * l) /
    ((Real.sqrt 5 + 1) * (k + 2 * l))

lemma goldenCut_lt_iff_goldenX_pos {p : ℝ} :
    goldenCut < p ↔ 0 < goldenX p := by
  have hden : 0 < Real.sqrt 5 + 1 := by
    nlinarith [Real.sqrt_nonneg 5]
  change (Real.sqrt 5 - 1) / (Real.sqrt 5 + 1) < p ↔
    0 < (1 + Real.sqrt 5) / 2 * p + (1 - Real.sqrt 5) / 2
  rw [div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith

lemma goldenX_optimizedP {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    goldenX (optimizedP k l) = (k : ℝ) / (k + 2 * l) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hden1 : Real.sqrt 5 + 1 ≠ 0 := by
    nlinarith [Real.sqrt_nonneg 5]
  have hden2 : (k : ℝ) + 2 * l ≠ 0 := by positivity
  dsimp [goldenX, optimizedP]
  field_simp
  nlinarith

lemma one_sub_optimizedP {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    1 - optimizedP k l =
      4 * l / ((Real.sqrt 5 + 1) * (k + 2 * l)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hden1 : Real.sqrt 5 + 1 ≠ 0 := by
    nlinarith [Real.sqrt_nonneg 5]
  have hden2 : (k : ℝ) + 2 * l ≠ 0 := by positivity
  dsimp [optimizedP]
  field_simp
  ring

lemma optimizedP_lt_one {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    optimizedP k l < 1 := by
  have h := one_sub_optimizedP hk hl
  have hs : 0 < Real.sqrt 5 + 1 := by
    nlinarith [Real.sqrt_nonneg 5]
  have hkl : 0 < (k : ℝ) + 2 * l := by positivity
  have : 0 < 4 * (l : ℝ) /
      ((Real.sqrt 5 + 1) * ((k : ℝ) + 2 * l)) := by positivity
  linarith

lemma goldenCut_lt_optimizedP {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    goldenCut < optimizedP k l := by
  rw [goldenCut_lt_iff_goldenX_pos, goldenX_optimizedP hk hl]
  positivity

/-- The square of the explicit expression in Corollary `c:easy`. -/
def easyCorollaryBoundSq (k l : ℕ) : ℝ :=
  16 * (k + l : ℝ) ^ 2 /
    (((k : ℝ) / (k + 2 * l)) ^ k *
      (4 * l / ((Real.sqrt 5 + 1) * (k + 2 * l))) ^ (2 * l))

lemma easyBoundSq_optimizedP {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    easyBoundSq (goldenX (optimizedP k l)) (optimizedP k l) k l =
      easyCorollaryBoundSq k l := by
  rw [easyBoundSq, easyCorollaryBoundSq, goldenX_optimizedP hk hl,
    one_sub_optimizedP hk hl]

/-- Corollary `c:easy`, in an integer-exact squared form.  Expanding the
square root gives the displayed product in the paper. -/
theorem ramseyNumber_le_easyCorollaryBound {k l : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ramseyNumber k l ≤ ⌈Real.sqrt (easyCorollaryBoundSq k l)⌉₊ := by
  simpa [easyBoundSq_optimizedP hk hl] using
    ramseyNumber_le_golden_easyBound
      (goldenCut_lt_optimizedP hk hl) (optimizedP_lt_one hk hl) hk hl

end Arxiv2407_19026

import Arxiv.Arxiv2407_19026.MulticolorEasy

/-!
# The explicit elementary multicolor bound

This file formalizes Theorem `t:easy2` in a fixed-weight form.  Substituting
`theta i = l i / ∑ i, l i` produces the factor `Theta(l)` in the paper.

The displayed factor `2 (k + l)` in Corollary `c:easy2` is inconsistent
with both Theorem `t:easy2` and its stated substitution; the proved
integer-exact corollary retains the resulting factor `4 (k + l)`.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

/-- The square of the fixed-weight bound in Theorem `t:easy2`. -/
def multiEasyBoundSq {c : ℕ} (x p : ℝ) (theta : Fin c → ℝ)
    (k : ℕ) (l : Fin c → ℕ) : ℝ :=
  16 * (k + ∑ i, l i : ℕ) ^ 2 /
    (x ^ k * (1 - p) ^ (2 * ∑ i, l i) *
      ∏ i, theta i ^ (2 * l i))

lemma theta_le_one {c : ℕ} {theta : Fin c → ℝ}
    (htheta : ∀ i, 0 < theta i) (hthetaSum : ∑ i, theta i = 1) :
    ∀ i, theta i ≤ 1 := by
  intro i
  have hi : theta i ≤ ∑ j, theta j := Finset.single_le_sum
    (fun j _ => (htheta j).le) (Finset.mem_univ i)
  simpa [hthetaSum] using hi

lemma multiEasyBoundSq_pos {c : ℕ} {x p : ℝ}
    {theta : Fin c → ℝ} (hx : 0 < x) (hp : p < 1)
    (htheta : ∀ i, 0 < theta i)
    {k : ℕ} (hk : 1 ≤ k) (l : Fin c → ℕ) :
    0 < multiEasyBoundSq x p theta k l := by
  unfold multiEasyBoundSq
  apply div_pos
  · positivity
  · exact mul_pos
      (mul_pos (pow_pos hx _) (pow_pos (sub_pos.mpr hp) _))
      (Finset.prod_pos fun i _ => pow_pos (htheta i) _)

/-- The multicolor bound dominates the corresponding two-color bound with
the blue parameters replaced by their sum. -/
lemma easyBoundSq_le_multiEasyBoundSq {c : ℕ} {x p : ℝ}
    {theta : Fin c → ℝ}
    (hx : 0 < x) (hp : p < 1)
    (htheta : ∀ i, 0 < theta i) (hthetaSum : ∑ i, theta i = 1)
    (k : ℕ) (l : Fin c → ℕ) :
    easyBoundSq x p k (∑ i, l i) ≤
      multiEasyBoundSq x p theta k l := by
  have htheta1 := theta_le_one htheta hthetaSum
  have hprod0 :
      0 < ∏ i, theta i ^ (2 * l i) :=
    Finset.prod_pos fun i _ => pow_pos (htheta i) _
  have hprod1 :
      ∏ i, theta i ^ (2 * l i) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact pow_nonneg (htheta i).le _
    · intro i _
      exact pow_le_one₀ (htheta i).le (htheta1 i)
  unfold easyBoundSq multiEasyBoundSq
  let A : ℝ :=
    x ^ k * (1 - p) ^ (2 * ∑ i, l i)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hden :
      A * ∏ i, theta i ^ (2 * l i) ≤ A * 1 :=
    mul_le_mul_of_nonneg_left hprod1 hA.le
  have hnum0 :
      0 ≤ 16 * ((k : ℝ) + ∑ i, (l i : ℝ)) ^ 2 := by positivity
  have hquot :=
    div_le_div_of_nonneg_left
      (a := 16 * ((k : ℝ) + ∑ i, (l i : ℝ)) ^ 2)
      (b := A) (c := A * ∏ i, theta i ^ (2 * l i))
      hnum0 (mul_pos hA hprod0) (by simpa using hden)
  simpa [A] using hquot

private lemma prod_theta_two_mul_lowerVector {c : ℕ}
    (theta : Fin c → ℝ) (l : Fin c → ℕ)
    (i : Fin c) (hli : 1 ≤ l i) :
    (∏ j, theta j ^ (2 * l j)) =
      theta i ^ 2 * ∏ j, theta j ^ (2 * lowerVector l i j) := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin c)) := Finset.mem_univ i
  have hfun :
      (fun j => theta j ^ (2 * lowerVector l i j)) =
        Function.update (fun j => theta j ^ (2 * l j)) i
          (theta i ^ (2 * (l i - 1))) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [lowerVector]
    · simp [lowerVector, hji]
  rw [hfun, Finset.prod_update_of_mem hi]
  have hprod :
      (∏ j ∈ (Finset.univ : Finset (Fin c)) \ {i},
          theta j ^ (2 * l j)) *
          theta i ^ (2 * l i) =
        ∏ j : Fin c, theta j ^ (2 * l j) := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.prod_erase_mul (Finset.univ : Finset (Fin c))
        (fun j => theta j ^ (2 * l j)) hi
  rw [← hprod]
  have hexp : 2 * l i = 2 * (l i - 1) + 2 := by omega
  rw [hexp, pow_add]
  ring

/-- A large neighborhood in color `i` preserves the squared multicolor
bound after lowering `l i`. -/
lemma multiEasyBoundSq_blue_step {c : ℕ}
    {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hp : p < 1) (htheta : ∀ i, 0 < theta i)
    {k n m : ℕ} (l : Fin c → ℕ) (i : Fin c) (hli : 2 ≤ l i)
    (hn : multiEasyBoundSq x p theta k l ≤ (n : ℝ) ^ 2)
    (hm : (((k + ∑ j, l j - 1 : ℕ) : ℝ) /
          (k + ∑ j, l j)) * theta i * (1 - p) * n ≤ m) :
    multiEasyBoundSq x p theta k (lowerVector l i) ≤ (m : ℝ) ^ 2 := by
  let q : ℝ :=
    ((k + ∑ j, l j - 1 : ℕ) : ℝ) / (k + ∑ j, l j)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hscale0 : 0 ≤ (q * theta i * (1 - p)) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hn hscale0
  have hm' : q * theta i * (1 - p) * (n : ℝ) ≤ m := by
    simpa [q] using hm
  have hmSq :
      (q * theta i * (1 - p) * (n : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hleft0 : 0 ≤ q * theta i * (1 - p) * (n : ℝ) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg hq0 (htheta i).le)
          (sub_pos.mpr hp).le)
        (Nat.cast_nonneg n)
    nlinarith [hm', sq_nonneg ((m : ℝ) -
      q * theta i * (1 - p) * n)]
  have hsumLower := sum_lowerVector i (by omega : 1 ≤ l i)
  have hprod := prod_theta_two_mul_lowerVector theta l i (by omega)
  have hsumPos : 0 < k + ∑ j, l j := by
    have hile : l i ≤ ∑ j, l j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i)
    omega
  have hidentity :
      (q * theta i * (1 - p)) ^ 2 *
          multiEasyBoundSq x p theta k l =
        multiEasyBoundSq x p theta k (lowerVector l i) := by
    let T : ℕ := ∑ j, l j
    let P : ℝ := ∏ j, theta j ^ (2 * lowerVector l i j)
    let A : ℝ := x ^ k * (1 - p) ^ (2 * (T - 1)) * P
    have hT1 : 1 ≤ T := by
      dsimp [T]
      have hile : l i ≤ ∑ j, l j := Finset.single_le_sum
        (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i)
      omega
    have hpow :
        (1 - p) ^ (2 * T) =
          (1 - p) ^ 2 * (1 - p) ^ (2 * (T - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [T] at hpow
    have hOld :
        multiEasyBoundSq x p theta k l =
          16 * ((k + T : ℕ) : ℝ) ^ 2 /
            ((theta i * (1 - p)) ^ 2 * A) := by
      unfold multiEasyBoundSq
      dsimp [T, P, A]
      rw [hpow, hprod]
      ring_nf
    have hsumK :
        k + ((∑ j, l j) - 1) = k + ∑ j, l j - 1 := by
      omega
    have hNew :
        multiEasyBoundSq x p theta k (lowerVector l i) =
          16 * ((k + T - 1 : ℕ) : ℝ) ^ 2 / A := by
      unfold multiEasyBoundSq
      dsimp [T, P, A]
      rw [hsumLower, hsumK]
    have hApos : 0 < A := by
      dsimp [A, P]
      exact mul_pos
        (mul_pos (pow_pos hx _) (pow_pos (sub_pos.mpr hp) _))
        (Finset.prod_pos fun j _ => pow_pos (htheta j) _)
    have hbasepos : 0 < theta i * (1 - p) :=
      mul_pos (htheta i) (sub_pos.mpr hp)
    have halgebra (s r b a : ℝ)
        (hs : s ≠ 0) (hb : b ≠ 0) (ha : a ≠ 0) :
        ((r / s) * b) ^ 2 * (16 * s ^ 2 / (b ^ 2 * a)) =
          16 * r ^ 2 / a := by
      field_simp
    rw [hOld, hNew]
    simpa [q, T, mul_assoc] using
      halgebra
        (((k + T : ℕ) : ℝ))
        (((k + T - 1 : ℕ) : ℝ))
        (theta i * (1 - p)) A
        (by positivity) hbasepos.ne' hApos.ne'
  calc
    multiEasyBoundSq x p theta k (lowerVector l i) =
        (q * theta i * (1 - p)) ^ 2 *
          multiEasyBoundSq x p theta k l := hidentity.symm
    _ ≤ (q * theta i * (1 - p)) ^ 2 * (n : ℝ) ^ 2 := hmul
    _ = (q * theta i * (1 - p) * (n : ℝ)) ^ 2 := by ring
    _ ≤ (m : ℝ) ^ 2 := hmSq

lemma card_blueNeighbors_eq_sum_colorCells {V : Type*} [Fintype V]
    {c : ℕ} (C : MultiColoring V c) (v : V) :
    (blueNeighborsIn (C.graph 0) v univ).card =
      ∑ i : Fin c, (multiNeighborsIn C v i.succ univ).card := by
  classical
  have hdisj := multiNeighbors_pairwiseDisjoint C v
    (Finset.univ : Finset V)
  have hU := biUnion_multiNeighbors_eq_erase C v
    (Finset.univ : Finset V)
  have hcardAll :
      ∑ q : Fin (c + 1), (multiNeighborsIn C v q univ).card =
        Fintype.card V - 1 := by
    have hcard := Finset.card_biUnion hdisj
    rw [hU, Finset.card_erase_of_mem (Finset.mem_univ v)] at hcard
    simpa using hcard.symm
  rw [Fin.sum_univ_succ] at hcardAll
  have htwo :=
    card_redNeighbors_add_card_blueNeighbors (C.graph 0) v
  rw [multiNeighborsIn_zero] at hcardAll
  omega

/-- If every individual blue-color degree is below its weighted threshold,
the two-color max-cut argument supplies a multicolor candidate. -/
lemma exists_multiCandidate_of_color_degree_lt
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {c : ℕ} (hc : 1 ≤ c) (C : MultiColoring V c)
    {theta : Fin c → ℝ}
    (hthetaSum : ∑ i, theta i = 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (s : ℕ) (hs : 1 ≤ s)
    (hcolor : ∀ v : V, ∀ i : Fin c,
      ((s - 1 : ℕ) : ℝ) / s * theta i * (1 - p) *
          Fintype.card V >
        (multiNeighborsIn C v i.succ univ).card)
    (habsorb : (s : ℝ) ≤
      p * (1 - p) * Fintype.card V) :
    ∃ D : MultiCandidate C, D.X ∪ D.Y = univ ∧
      (1 - p) ^ 2 * (Fintype.card V : ℝ) ^ 2 / (4 * s) <
        D.excess p := by
  classical
  let q : ℝ := ((s - 1 : ℕ) : ℝ) / s
  have huniv : (Finset.univ : Finset (Fin c)).Nonempty := by
    let i0 : Fin c := ⟨0, hc⟩
    exact ⟨i0, Finset.mem_univ i0⟩
  have hblue : ∀ v : V,
      q * (1 - p) * Fintype.card V >
        (blueNeighborsIn (C.graph 0) v univ).card := by
    intro v
    have hsum :
        (∑ i : Fin c,
          ((multiNeighborsIn C v i.succ univ).card : ℝ)) <
          ∑ i : Fin c, q * theta i * (1 - p) * Fintype.card V := by
      apply Finset.sum_lt_sum_of_nonempty huniv
      intro i _
      simpa [q] using hcolor v i
    have hright :
        (∑ i, q * theta i * (1 - p) * Fintype.card V) =
          q * (1 - p) * Fintype.card V := by
      calc
        (∑ i, q * theta i * (1 - p) * Fintype.card V) =
            (∑ i, theta i) *
              (q * (1 - p) * Fintype.card V) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = q * (1 - p) * Fintype.card V := by
          rw [hthetaSum]
          ring
    rw [hright] at hsum
    rw [card_blueNeighbors_eq_sum_colorCells C v]
    exact_mod_cast hsum
  obtain ⟨E, hUnion, hExcess⟩ :=
    exists_candidate_of_blue_degree_lt (C.graph 0) p hp0 hp1 s hs
      (by simpa [q] using hblue) habsorb
  let D : MultiCandidate C :=
    { X := E.X
      Y := E.Y
      X_nonempty := E.X_nonempty
      Y_nonempty := E.Y_nonempty
      disjoint := E.disjoint }
  exact ⟨D, hUnion, by
    simpa [D, MultiCandidate.excess, Candidate.excess] using hExcess⟩

/-- The multicolor threshold is paid for by the same scaled squared bound
as in the two-color argument.  The missing `c - 1` powers in the
multicolor denominator only make that denominator larger. -/
lemma multiEasyThreshold_le_scaled_multiEasyBoundSq {c : ℕ}
    (hc : 1 ≤ c) {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (hgold : (1 - p) ^ 2 = (1 - x) * (p - x))
    (htheta : ∀ i, 0 < theta i)
    {k : ℕ} (hk : 1 ≤ k) (l : Fin c → ℕ)
    (hl : ∀ i, 1 ≤ l i) :
    multiEasyThreshold x p theta k l l ≤
      (1 - p) ^ 2 / (4 * (k + ∑ i, l i : ℝ)) *
        multiEasyBoundSq x p theta k l := by
  let T : ℕ := ∑ i, l i
  let P : ℝ := ∏ i, theta i ^ (2 * l i)
  have hTge : c ≤ T := by
    calc
      c = ∑ _i : Fin c, 1 := by simp
      _ ≤ ∑ i, l i := Finset.sum_le_sum fun i _ => hl i
  have hT1 : 1 ≤ T := le_trans hc hTge
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ => pow_pos (htheta i) _
  have hthetaPow :
      (∏ i, theta i ^ (l i + l i)) = P := by
    dsimp [P]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    omega
  have hone0 : 0 < 1 - x := sub_pos.mpr (hxp.trans hp)
  have hpx0 : 0 < p - x := sub_pos.mpr hxp
  have hone1 : 1 - x ≤ 1 := by linarith
  have hpx1 : p - x ≤ 1 := by linarith
  have hexp : T - c ≤ T - 1 := by omega
  have honePow :
      (1 - x) ^ (T - 1) ≤ (1 - x) ^ (T - c) :=
    pow_le_pow_of_le_one hone0.le hone1 hexp
  have hpxPow :
      (p - x) ^ (T - 1) ≤ (p - x) ^ (T - c) :=
    pow_le_pow_of_le_one hpx0.le hpx1 hexp
  let Dsmall : ℝ :=
    x ^ (k - 1) * (1 - x) ^ (T - 1) *
      (p - x) ^ (T - 1) * P
  let Dmulti : ℝ :=
    x ^ (k - 1) * (1 - x) ^ (T - c) *
      (p - x) ^ (T - c) * P
  have hDsmall : 0 < Dsmall := by
    dsimp [Dsmall]
    positivity
  have hDmulti : 0 < Dmulti := by
    dsimp [Dmulti]
    positivity
  have hden : Dsmall ≤ Dmulti := by
    dsimp [Dsmall, Dmulti]
    have hfirst :
        x ^ (k - 1) * (1 - x) ^ (T - 1) ≤
          x ^ (k - 1) * (1 - x) ^ (T - c) :=
      mul_le_mul_of_nonneg_left honePow (pow_nonneg hx.le _)
    have hsecond :
        x ^ (k - 1) * (1 - x) ^ (T - 1) *
            (p - x) ^ (T - 1) ≤
          x ^ (k - 1) * (1 - x) ^ (T - c) *
            (p - x) ^ (T - c) :=
      mul_le_mul hfirst hpxPow
        (pow_nonneg hpx0.le _)
        (mul_nonneg (pow_nonneg hx.le _) (pow_nonneg hone0.le _))
    exact mul_le_mul_of_nonneg_right hsecond hPpos.le
  have hthresholdQuot :
      multiEasyThreshold x p theta k l l ≤
        easyThreshold x p k T T / P := by
    have hmulti :
        multiEasyThreshold x p theta k l l =
          ((k + T : ℕ) : ℝ) / Dmulti := by
      simp only [multiEasyThreshold, multiEasyDenominator]
      rw [hthetaPow]
    have heasy :
        easyThreshold x p k T T / P =
          ((k + T : ℕ) : ℝ) / Dsmall := by
      unfold easyThreshold
      dsimp [Dsmall]
      field_simp [hPpos.ne']
      norm_num
    rw [hmulti, heasy]
    exact div_le_div_of_nonneg_left
      (by positivity) hDsmall hden
  have hboundQuot :
      multiEasyBoundSq x p theta k l =
        easyBoundSq x p k T / P := by
    unfold multiEasyBoundSq easyBoundSq
    dsimp [T, P]
    field_simp [hPpos.ne']
    norm_num
  have htwo :=
    easyThreshold_le_scaled_easyBoundSq hx hxp hp hgold hk hT1
  have hdiv := div_le_div_of_nonneg_right htwo hPpos.le
  calc
    multiEasyThreshold x p theta k l l ≤
        easyThreshold x p k T T / P := hthresholdQuot
    _ ≤ ((1 - p) ^ 2 / (4 * (k + T : ℝ)) *
          easyBoundSq x p k T) / P := hdiv
    _ = (1 - p) ^ 2 / (4 * (k + ∑ i, l i : ℝ)) *
          multiEasyBoundSq x p theta k l := by
      rw [hboundQuot]
      dsimp [T]
      ring

/-- Map a clique in a pulled-back coloring to the original coloring. -/
private lemma isNClique_comap_map {V W : Type*} {G : SimpleGraph V}
    {f : W ↪ V} {n : ℕ} {K : Finset W}
    (hK : (G.comap f).IsNClique n K) :
    G.IsNClique n (K.map f) :=
  hK.map.mono (SimpleGraph.map_comap_le f G)

/-- Squared, integer-exact fixed-weight form of Theorem `t:easy2`.
Every finite complete coloring above the displayed squared threshold has
the required red clique or one of the prescribed blue cliques. -/
theorem multiRamseyProperty_of_multiEasyBoundSq {c : ℕ}
    (hc : 1 ≤ c) {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (hgold : (1 - p) ^ 2 = (1 - x) * (p - x))
    (htheta : ∀ i, 0 < theta i)
    (hthetaSum : ∑ i, theta i = 1)
    {k n : ℕ} (hk : 1 ≤ k) (l : Fin c → ℕ)
    (hl : ∀ i, 1 ≤ l i)
    (hn : multiEasyBoundSq x p theta k l ≤ (n : ℝ) ^ 2) :
    MultiRamseyProperty k l n := by
  classical
  intro V instF instD hcard C
  have hncard : (n : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hcard
  have hncardSq :
      (n : ℝ) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hcard0 : 0 ≤ (Fintype.card V : ℝ) := by positivity
    nlinarith
  have hboundCard :
      multiEasyBoundSq x p theta k l ≤
        (Fintype.card V : ℝ) ^ 2 :=
    hn.trans hncardSq
  have hboundPos :=
    multiEasyBoundSq_pos hx hp htheta hk l
  have hcardSqPos :
      0 < (Fintype.card V : ℝ) ^ 2 :=
    hboundPos.trans_le hboundCard
  have hVcardPos : 0 < Fintype.card V := by
    by_contra hzero
    have hcardZero : Fintype.card V = 0 := by omega
    rw [hcardZero] at hcardSqPos
    norm_num at hcardSqPos
  letI : Nonempty V := Fintype.card_pos_iff.mp hVcardPos
  by_cases hkone : k = 1
  · subst k
    exact Or.inl
      ⟨{Classical.choice (inferInstance : Nonempty V)}, by simp⟩
  have hk2 : 2 ≤ k := by omega
  by_cases hlbase : ∃ i, l i ≤ 1
  · obtain ⟨i, hi⟩ := hlbase
    have hli : l i = 1 := le_antisymm hi (hl i)
    exact Or.inr ⟨i,
      {Classical.choice (inferInstance : Nonempty V)}, by simp [hli]⟩
  have hl2 : ∀ i, 2 ≤ l i := by
    intro i
    by_contra hi
    exact hlbase ⟨i, by omega⟩
  let T : ℕ := ∑ i, l i
  let s : ℕ := k + T
  let q : ℝ := ((s - 1 : ℕ) : ℝ) / s
  have hT1 : 1 ≤ T := by
    let i0 : Fin c := ⟨0, hc⟩
    have hile : l i0 ≤ ∑ i, l i := Finset.single_le_sum
      (fun i _ => Nat.zero_le (l i)) (Finset.mem_univ i0)
    dsimp [T]
    exact (hl i0).trans hile
  have hs : 1 ≤ s := by
    dsimp [s]
    omega
  by_cases hlarge :
      ∃ v : V, ∃ i : Fin c,
        q * theta i * (1 - p) * Fintype.card V ≤
          (multiNeighborsIn C v i.succ univ).card
  · obtain ⟨v, i, hi⟩ := hlarge
    let B := multiNeighborsIn C v i.succ (univ : Finset V)
    have hstep :
        multiEasyBoundSq x p theta k (lowerVector l i) ≤
          (B.card : ℝ) ^ 2 := by
      apply multiEasyBoundSq_blue_step hx hp htheta l i (hl2 i)
        hboundCard
      simpa [q, s, T, B] using hi
    have hlLower : ∀ j, 1 ≤ lowerVector l i j := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [lowerVector, Function.update_self]
        have hli2 := hl2 i
        omega
      · simpa [lowerVector, hji] using hl j
    have hprop :
        MultiRamseyProperty k (lowerVector l i) B.card :=
      multiRamseyProperty_of_multiEasyBoundSq hc hx hxp hp hgold
        htheta hthetaSum hk (lowerVector l i) hlLower hstep
    let W := {u : V // u ∈ B}
    let f : W ↪ V := Function.Embedding.subtype _
    have hWcard : B.card ≤ Fintype.card W := by
      simp [W]
    have hgood :
        MultiGood (C.comap f) k (lowerVector l i) :=
      hprop W hWcard (C.comap f)
    rcases hgood with hred | hblue
    · rcases hred with ⟨K, hK⟩
      exact Or.inl ⟨K.map f, isNClique_comap_map hK⟩
    · rcases hblue with ⟨j, K, hK⟩
      by_cases hji : j = i
      · subst j
        let K' := K.map f
        have hK' : (C.graph i.succ).IsNClique
            (lowerVector l i i) K' :=
          isNClique_comap_map hK
        have hadj : ∀ u ∈ K', (C.graph i.succ).Adj v u := by
          intro u hu
          rcases Finset.mem_map.mp hu with ⟨w, hw, rfl⟩
          exact
            (mem_multiNeighborsIn C v w.1 i.succ univ).1 w.2 |>.2
        have hins := hK'.insert hadj
        refine Or.inr ⟨i, insert v K', ?_⟩
        simpa only [lowerVector, Function.update_self,
          Nat.sub_add_cancel (hl i)]
          using hins
      · refine Or.inr ⟨j, K.map f, ?_⟩
        have hK' := isNClique_comap_map hK
        simpa [lowerVector, hji] using hK'
  · push Not at hlarge
    have hp0 : 0 < p := hx.trans hxp
    have heasyCard :
        easyBoundSq x p k T ≤
          (Fintype.card V : ℝ) ^ 2 := by
      exact
        (easyBoundSq_le_multiEasyBoundSq
          hx hp htheta hthetaSum k l).trans hboundCard
    have habsorb4 :
        4 * (k + T : ℝ) ≤
          p * (1 - p) * Fintype.card V :=
      four_mul_add_le_of_easyBoundSq hx hxp hp hk2 hT1 heasyCard
    have habsorb :
        (s : ℝ) ≤ p * (1 - p) * Fintype.card V := by
      dsimp [s]
      push_cast
      nlinarith
    have hcolor : ∀ v : V, ∀ i : Fin c,
        ((s - 1 : ℕ) : ℝ) / s * theta i * (1 - p) *
            Fintype.card V >
          (multiNeighborsIn C v i.succ univ).card := by
      intro v i
      simpa [q] using hlarge v i
    obtain ⟨D, _hDuniv, hDexcess⟩ :=
      exists_multiCandidate_of_color_degree_lt hc C hthetaSum
        p hp0 hp s hs hcolor habsorb
    have hscale0 :
        0 ≤ (1 - p) ^ 2 / (4 * (k + T : ℝ)) := by
      positivity
    have hthreshold :
        multiEasyThreshold x p theta k l l ≤ D.excess p := by
      calc
        multiEasyThreshold x p theta k l l ≤
            (1 - p) ^ 2 / (4 * (k + ∑ i, l i : ℝ)) *
              multiEasyBoundSq x p theta k l :=
          multiEasyThreshold_le_scaled_multiEasyBoundSq
            hc hx hxp hp hgold htheta hk l hl
        _ ≤ (1 - p) ^ 2 / (4 * (k + T : ℝ)) *
              (Fintype.card V : ℝ) ^ 2 := by
          dsimp [T]
          exact mul_le_mul_of_nonneg_left hboundCard hscale0
        _ = (1 - p) ^ 2 * (Fintype.card V : ℝ) ^ 2 /
              (4 * s) := by
          dsimp [s]
          push_cast
          ring
        _ ≤ D.excess p := le_of_lt hDexcess
    have hgood :=
      multiCandidate_good_of_excess hc hx hxp hp htheta hthetaSum
        D k l l hk hl hl hthreshold
    rcases hgood with hred | hblueX | hblueY
    · rcases hred with ⟨K, _hKsub, hK⟩
      exact Or.inl ⟨K, hK⟩
    · rcases hblueX with ⟨i, K, _hKsub, hK⟩
      exact Or.inr ⟨i, K, hK⟩
    · rcases hblueY with ⟨i, K, _hKsub, hK⟩
      exact Or.inr ⟨i, K, hK⟩
termination_by ∑ i, l i
decreasing_by
  rw [sum_lowerVector i (hl i)]
  have hsumPos : 0 < ∑ j, l j := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (by simpa [T] using hT1)
  exact Nat.sub_lt hsumPos Nat.zero_lt_one

/-- Integer-rounded fixed-weight form of Theorem `t:easy2`. -/
theorem multiRamseyNumber_le_ceil_sqrt_multiEasyBoundSq {c : ℕ}
    (hc : 1 ≤ c) {x p : ℝ} {theta : Fin c → ℝ}
    (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (hgold : (1 - p) ^ 2 = (1 - x) * (p - x))
    (htheta : ∀ i, 0 < theta i)
    (hthetaSum : ∑ i, theta i = 1)
    {k : ℕ} (hk : 1 ≤ k) (l : Fin c → ℕ)
    (hl : ∀ i, 1 ≤ l i) :
    multiRamseyNumber hc k l ≤
      ⌈Real.sqrt (multiEasyBoundSq x p theta k l)⌉₊ := by
  classical
  have hsq0 : 0 ≤ multiEasyBoundSq x p theta k l :=
    (multiEasyBoundSq_pos hx hp htheta hk l).le
  let B := Real.sqrt (multiEasyBoundSq x p theta k l)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = multiEasyBoundSq x p theta k l := by
    simpa [B] using Real.sq_sqrt hsq0
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hthreshold :
      multiEasyBoundSq x p theta k l ≤
        ((⌈B⌉₊ : ℕ) : ℝ) ^ 2 := by
    rw [← hBsq]
    nlinarith [sq_nonneg ((⌈B⌉₊ : ℝ) - B)]
  exact Nat.find_min' (multiRamseyProperty_exists hc k l)
    (multiRamseyProperty_of_multiEasyBoundSq
      hc hx hxp hp hgold htheta hthetaSum hk l hl hthreshold)

/-- Theorem `t:easy2` after substituting the paper's golden-ratio choice
of `x`. -/
theorem multiRamseyNumber_le_golden_multiEasyBound {c : ℕ}
    (hc : 1 ≤ c) {p : ℝ} (hp0 : goldenCut < p) (hp1 : p < 1)
    {theta : Fin c → ℝ} (htheta : ∀ i, 0 < theta i)
    (hthetaSum : ∑ i, theta i = 1)
    {k : ℕ} (hk : 1 ≤ k) (l : Fin c → ℕ)
    (hl : ∀ i, 1 ≤ l i) :
    multiRamseyNumber hc k l ≤
      ⌈Real.sqrt
        (multiEasyBoundSq (goldenX p) p theta k l)⌉₊ := by
  exact multiRamseyNumber_le_ceil_sqrt_multiEasyBoundSq
    hc (goldenX_pos hp0) (goldenX_lt hp1) hp1
    (goldenX_identity p) htheta hthetaSum hk l hl

/-- The weight `theta_i = l_i / ∑_j l_j` selected in Section 5. -/
def normalizedTheta {c : ℕ} (l : Fin c → ℕ) (i : Fin c) : ℝ :=
  (l i : ℝ) / (∑ j, l j : ℕ)

lemma normalizedTheta_pos {c : ℕ} (l : Fin c → ℕ) (hl : ∀ i, 1 ≤ l i) :
    ∀ i, 0 < normalizedTheta l i := by
  intro i
  have hliNat : 0 < l i := Nat.zero_lt_of_lt (hl i)
  have hli : 0 < (l i : ℝ) := by exact_mod_cast hliNat
  have hile : l i ≤ ∑ j, l j := Finset.single_le_sum
    (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i)
  have hsum : 0 < ((∑ j, l j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le
      (Nat.zero_lt_of_lt (hl i)) hile)
  exact div_pos hli hsum

lemma normalizedTheta_sum {c : ℕ} (hc : 1 ≤ c)
    (l : Fin c → ℕ) (hl : ∀ i, 1 ≤ l i) :
    ∑ i, normalizedTheta l i = 1 := by
  let i0 : Fin c := ⟨0, hc⟩
  have hile : l i0 ≤ ∑ j, l j := Finset.single_le_sum
    (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i0)
  have hsumNat : 0 < ∑ j, l j :=
    Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt (hl i0)) hile
  unfold normalizedTheta
  rw [← Finset.sum_div]
  push_cast
  apply div_self
  exact_mod_cast hsumNat.ne'

/-- The factor `Theta(l)` from the paper. -/
def multicolorThetaFactor {c : ℕ} (l : Fin c → ℕ) : ℝ :=
  ∏ i, (((∑ j, l j : ℕ) : ℝ) / l i) ^ l i

lemma prod_inv_normalizedTheta_pow_eq_thetaFactor {c : ℕ}
    (l : Fin c → ℕ) :
    (∏ i, (normalizedTheta l i)⁻¹ ^ l i) =
      multicolorThetaFactor l := by
  unfold normalizedTheta multicolorThetaFactor
  apply Finset.prod_congr rfl
  intro i _
  rw [inv_div]

/-- Separating the color-weight contribution from the two-color squared
bound. -/
lemma multiEasyBoundSq_eq_easyBoundSq_div_prod {c : ℕ}
    {x p : ℝ} {theta : Fin c → ℝ}
    (htheta : ∀ i, 0 < theta i) (k : ℕ) (l : Fin c → ℕ) :
    multiEasyBoundSq x p theta k l =
      easyBoundSq x p k (∑ i, l i) /
        ∏ i, theta i ^ (2 * l i) := by
  let P : ℝ := ∏ i, theta i ^ (2 * l i)
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun i _ => pow_pos (htheta i) _
  unfold multiEasyBoundSq easyBoundSq
  field_simp [P, hPpos.ne']
  norm_num

/-- The square of the explicit expression in Corollary `c:easy2`.
Its extra denominator has square root reciprocal equal to
`multicolorThetaFactor l`. -/
def multiEasyCorollaryBoundSq {c : ℕ}
    (k : ℕ) (l : Fin c → ℕ) : ℝ :=
  easyCorollaryBoundSq k (∑ i, l i) /
    ∏ i, normalizedTheta l i ^ (2 * l i)

lemma multiEasyBoundSq_optimizedP {c : ℕ} (hc : 1 ≤ c)
    {k : ℕ} (hk : 1 ≤ k) (l : Fin c → ℕ)
    (hl : ∀ i, 1 ≤ l i) :
    multiEasyBoundSq
        (goldenX (optimizedP k (∑ i, l i)))
        (optimizedP k (∑ i, l i))
        (normalizedTheta l) k l =
      multiEasyCorollaryBoundSq k l := by
  let i0 : Fin c := ⟨0, hc⟩
  have hile : l i0 ≤ ∑ j, l j := Finset.single_le_sum
    (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i0)
  have hsum : 1 ≤ ∑ j, l j := (hl i0).trans hile
  rw [multiEasyBoundSq_eq_easyBoundSq_div_prod
    (normalizedTheta_pos l hl) k l]
  rw [easyBoundSq_optimizedP hk hsum]
  rfl

/-- Corollary `c:easy2`, with the optimizing `p`, normalized color
weights, and the unavoidable integer ceiling made explicit. -/
theorem multiRamseyNumber_le_multiEasyCorollaryBound {c : ℕ}
    (hc : 1 ≤ c) {k : ℕ} (hk : 1 ≤ k)
    (l : Fin c → ℕ) (hl : ∀ i, 1 ≤ l i) :
    multiRamseyNumber hc k l ≤
      ⌈Real.sqrt (multiEasyCorollaryBoundSq k l)⌉₊ := by
  let i0 : Fin c := ⟨0, hc⟩
  have hile : l i0 ≤ ∑ j, l j := Finset.single_le_sum
    (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i0)
  have hsum : 1 ≤ ∑ j, l j := (hl i0).trans hile
  have hmain :=
    multiRamseyNumber_le_golden_multiEasyBound
      hc
      (goldenCut_lt_optimizedP hk hsum)
      (optimizedP_lt_one hk hsum)
      (normalizedTheta_pos l hl)
      (normalizedTheta_sum hc l hl)
      hk l hl
  rw [multiEasyBoundSq_optimizedP hc hk l hl] at hmain
  exact hmain

end Arxiv2407_19026

import Mathlib
import ErdosProblems.Erdos220.Basic

open scoped BigOperators

namespace Erdos220

open Finset

/-- Starting positions lying in an internal reduced-residue gap and leaving at
least `h` steps before its right endpoint. -/
abbrev InternalGapStart (n h : ℕ) :=
  Σ k : Fin (n.totient - 1), Fin (internalGap n k - h)

/-- The integer represented by an internal gap start. -/
noncomputable def internalGapStartValue {n h : ℕ} (z : InternalGapStart n h) : ℕ :=
  reducedResidue n (gapLeftIndex n z.1) + z.2.val

lemma reducedResidue_add_internalGap (n : ℕ) (k : Fin (n.totient - 1)) :
    reducedResidue n (gapLeftIndex n k) + internalGap n k =
      reducedResidue n (gapRightIndex n k) := by
  rw [internalGap, Nat.add_sub_of_le (Nat.le_of_lt (reducedResidue_gap_lt n k))]

lemma not_coprime_strictly_between_reducedResidues
    {n y : ℕ} (k : Fin (n.totient - 1))
    (hleft : reducedResidue n (gapLeftIndex n k) < y)
    (hright : y < reducedResidue n (gapRightIndex n k)) :
    ¬ n.Coprime y := by
  intro hycop
  have hylt : y < n := hright.trans (reducedResidue_lt n _)
  have hymem : y ∈ reducedResidueFinset n :=
    mem_reducedResidueFinset.mpr ⟨hylt, hycop⟩
  rw [← image_reducedResidue_univ] at hymem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hymem
  have hki : gapLeftIndex n k < i := by
    apply (reducedResidue n).lt_iff_lt.mp
    simpa [hi] using hleft
  have hik : i < gapRightIndex n k := by
    apply (reducedResidue n).lt_iff_lt.mp
    simpa [hi] using hright
  change k.val < i.val at hki
  change i.val < k.val + 1 at hik
  omega

lemma internalGapStartValue_lt_right {n h : ℕ} (z : InternalGapStart n h) :
    internalGapStartValue z < reducedResidue n (gapRightIndex n z.1) := by
  have hj : z.2.val < internalGap n z.1 := by
    omega
  rw [← reducedResidue_add_internalGap]
  exact Nat.add_lt_add_left hj _

lemma internalGapStartValue_mem_emptyWindows {n h : ℕ} (z : InternalGapStart n h) :
    internalGapStartValue z ∈ emptyWindows n h := by
  rw [mem_emptyWindows_iff_forall]
  constructor
  · exact (internalGapStartValue_lt_right z).trans (reducedResidue_lt n _)
  · intro t ht1 hth htCoprime
    have hjt : z.2.val + t < internalGap n z.1 := by
      have hj := z.2.isLt
      omega
    have hleft : reducedResidue n (gapLeftIndex n z.1) <
        internalGapStartValue z + t := by
      dsimp [internalGapStartValue]
      omega
    have hright : internalGapStartValue z + t <
        reducedResidue n (gapRightIndex n z.1) := by
      rw [← reducedResidue_add_internalGap]
      dsimp [internalGapStartValue]
      omega
    exact not_coprime_strictly_between_reducedResidues z.1 hleft hright htCoprime

lemma internalGapStartValue_injective (n h : ℕ) :
    Function.Injective
      (internalGapStartValue : InternalGapStart n h → ℕ) := by
  rintro ⟨k, j⟩ ⟨l, m⟩ heq
  have hkl : k = l := by
    apply le_antisymm
    · by_contra hnle
      have hlk : l < k := lt_of_not_ge hnle
      have hidx : gapRightIndex n l ≤ gapLeftIndex n k := by
        simp only [gapRightIndex, gapLeftIndex, Fin.mk_le_mk]
        omega
      have hres : reducedResidue n (gapRightIndex n l) ≤
          reducedResidue n (gapLeftIndex n k) :=
        (reducedResidue n).monotone hidx
      have hmright : internalGapStartValue (⟨l, m⟩ : InternalGapStart n h) <
          reducedResidue n (gapRightIndex n l) :=
        internalGapStartValue_lt_right _
      have hkj : reducedResidue n (gapLeftIndex n k) ≤
          internalGapStartValue (⟨k, j⟩ : InternalGapStart n h) := by
        simp [internalGapStartValue]
      omega
    · by_contra hnle
      have hkl' : k < l := lt_of_not_ge hnle
      have hidx : gapRightIndex n k ≤ gapLeftIndex n l := by
        simp only [gapRightIndex, gapLeftIndex, Fin.mk_le_mk]
        omega
      have hres : reducedResidue n (gapRightIndex n k) ≤
          reducedResidue n (gapLeftIndex n l) :=
        (reducedResidue n).monotone hidx
      have hjright : internalGapStartValue (⟨k, j⟩ : InternalGapStart n h) <
          reducedResidue n (gapRightIndex n k) :=
        internalGapStartValue_lt_right _
      have hlm : reducedResidue n (gapLeftIndex n l) ≤
          internalGapStartValue (⟨l, m⟩ : InternalGapStart n h) := by
        simp [internalGapStartValue]
      omega
  subst l
  have hjm : j = m := by
    apply Fin.ext
    dsimp [internalGapStartValue] at heq
    omega
  subst m
  rfl

/-- Every internal gap contributes all of its possible empty-window starts,
and starts arising from distinct gaps are distinct. -/
lemma sum_internalGap_sub_le_card_emptyWindows (n h : ℕ) :
    ∑ k : Fin (n.totient - 1), (internalGap n k - h) ≤
      (emptyWindows n h).card := by
  let f : InternalGapStart n h → {x // x ∈ emptyWindows n h} :=
    fun z ↦ ⟨internalGapStartValue z, internalGapStartValue_mem_emptyWindows z⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply internalGapStartValue_injective n h
    exact congrArg Subtype.val hzw
  have hcard := Fintype.card_le_of_injective f hf
  simpa [InternalGapStart] using hcard

/-- One-dimensional layer cake for a natural square, with all levels above
`d` harmlessly included. -/
lemma nat_square_layer_cake_self (d : ℕ) :
    d ^ 2 = d + 2 * ∑ h ∈ Ioc 0 d, (d - h) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le d)]
      simp only [Nat.sub_self, add_zero]
      have hsum : ∑ x ∈ Ioc 0 d, (d + 1 - x) =
          (∑ x ∈ Ioc 0 d, (d - x)) + d := by
        calc
          ∑ x ∈ Ioc 0 d, (d + 1 - x) =
              ∑ x ∈ Ioc 0 d, ((d - x) + 1) := by
                apply sum_congr rfl
                intro x hx
                have hxd : x ≤ d := (mem_Ioc.mp hx).2
                omega
          _ = (∑ x ∈ Ioc 0 d, (d - x)) + d := by
            rw [sum_add_distrib]
            simp
      rw [hsum]
      nlinarith

lemma nat_square_layer_cake (d N : ℕ) (hdN : d ≤ N) :
    d ^ 2 = d + 2 * ∑ h ∈ Ioc 0 N, (d - h) := by
  rw [nat_square_layer_cake_self d]
  congr 2
  apply sum_subset
  · intro x hx
    rw [mem_Ioc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hdN⟩
  · intro x hxN hxd
    rw [mem_Ioc] at hxN
    have hdx : d < x := by
      by_contra hnot
      exact hxd (mem_Ioc.mpr ⟨hxN.1, Nat.le_of_not_gt hnot⟩)
    simp [Nat.sub_eq_zero_of_le hdx.le]

/-- The excess-mass function of the internal gaps. -/
noncomputable def internalGapExcess (n h : ℕ) : ℝ :=
  ∑ k : Fin (n.totient - 1), ((internalGap n k - h : ℕ) : ℝ)

lemma internalGapExcess_nonneg (n h : ℕ) : 0 ≤ internalGapExcess n h := by
  apply Finset.sum_nonneg
  intro k hk
  exact Nat.cast_nonneg _

lemma internalGapExcess_le_card_emptyWindows (n h : ℕ) :
    internalGapExcess n h ≤ ((emptyWindows n h).card : ℝ) := by
  rw [internalGapExcess]
  exact_mod_cast sum_internalGap_sub_le_card_emptyWindows n h

lemma sum_internalGap_cast_le (n : ℕ) :
    ∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ≤ (n : ℝ) := by
  by_cases hsmall : n.totient ≤ 1
  · have hempty : ∀ k : Fin (n.totient - 1), False := by
      intro k
      have := k.isLt
      omega
    have hsum : ∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact (hempty k).elim
    rw [hsum]
    positivity
  · have htwo : 2 ≤ n.totient := by omega
    let a : ℕ → ℝ := fun i ↦
      if hi : i < n.totient then ((reducedResidue n ⟨i, hi⟩ : ℕ) : ℝ) else 0
    let b : ℕ → ℝ := fun i ↦
      if hi : i < n.totient - 1 then (internalGap n ⟨i, hi⟩ : ℝ) else 0
    have heq :
        (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) =
          ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) := by
      calc
        (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) =
            ∑ k : Fin (n.totient - 1), b k := by
              apply sum_congr rfl
              intro k hk
              simp [b, k.isLt]
        _ = ∑ k ∈ range (n.totient - 1), b k := by
              rw [Fin.sum_univ_eq_sum_range]
        _ = ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) := by
              apply sum_congr rfl
              intro k hk
              have hklt : k < n.totient - 1 := mem_range.mp hk
              have hk0 : k < n.totient := by omega
              have hk1 : k + 1 < n.totient := by omega
              simp only [b, dif_pos hklt, internalGap, gapRightIndex, gapLeftIndex]
              have hgap : reducedResidue n ⟨k, hk0⟩ ≤
                  reducedResidue n ⟨k + 1, hk1⟩ := by
                apply Nat.le_of_lt
                apply (reducedResidue n).strictMono
                simp
              rw [Nat.cast_sub hgap]
              simp [a, hk0, hk1]
    calc
      (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) =
          ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) := heq
      _ = a (n.totient - 1) - a 0 := by
            have hs := Finset.sum_range_sub' a (n.totient - 1)
            calc
              ∑ k ∈ range (n.totient - 1), (a (k + 1) - a k) =
                  - ∑ k ∈ range (n.totient - 1), (a k - a (k + 1)) := by
                    rw [← sum_neg_distrib]
                    apply sum_congr rfl
                    intro k hk
                    ring
              _ = a (n.totient - 1) - a 0 := by rw [hs]; ring
      _ ≤ (n : ℝ) := by
            have hlast : n.totient - 1 < n.totient := by omega
            have hzero : 0 < n.totient := by omega
            have hlt : reducedResidue n ⟨n.totient - 1, hlast⟩ < n :=
              reducedResidue_lt n _
            simp only [a, dif_pos hlast, dif_pos hzero]
            have hlast_le :
                ((reducedResidue n ⟨n.totient - 1, hlast⟩ : ℕ) : ℝ) ≤ n := by
              exact_mod_cast Nat.le_of_lt hlt
            have hfirst_nonneg :
                0 ≤ ((reducedResidue n ⟨0, hzero⟩ : ℕ) : ℝ) := by positivity
            linarith

/-- The internal gap squares are bounded by the first moment plus the finite
sum of their excess masses. -/
lemma gapSquareSum_le_internalGapExcess (n : ℕ) :
    gapSquareSum n ≤ (n : ℝ) +
      2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h := by
  rw [gapSquareSum_eq_sum_internalGap]
  have hlayer :
      (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ^ 2) =
        (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) +
          2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h := by
    calc
      (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ^ 2) =
          ∑ k : Fin (n.totient - 1),
            (((internalGap n k) ^ 2 : ℕ) : ℝ) := by
              apply sum_congr rfl
              intro k hk
              norm_num
      _ = ∑ k : Fin (n.totient - 1),
            (((internalGap n k) +
              2 * ∑ h ∈ Ioc 0 n, (internalGap n k - h) : ℕ) : ℝ) := by
              apply sum_congr rfl
              intro k hk
              rw [nat_square_layer_cake (internalGap n k) n (internalGap_le_n n k)]
      _ = (∑ k : Fin (n.totient - 1), (internalGap n k : ℝ)) +
          2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h := by
            push_cast
            simp only [sum_add_distrib, internalGapExcess]
            rw [← mul_sum, sum_comm]
  rw [hlayer]
  gcongr
  exact sum_internalGap_cast_le n

lemma gapSquareSum_le_emptyWindows_layer (n : ℕ) :
    gapSquareSum n ≤ (n : ℝ) +
      2 * ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ) := by
  calc
    gapSquareSum n ≤ (n : ℝ) +
        2 * ∑ h ∈ Ioc 0 n, internalGapExcess n h :=
      gapSquareSum_le_internalGapExcess n
    _ ≤ (n : ℝ) +
        2 * ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ) := by
      gcongr with h hh
      exact internalGapExcess_le_card_emptyWindows n h

private theorem concrete_emptyWindow_tail_deduction
    (E : ℕ → ℝ) (N K : ℕ) (q phi B secondMoment : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hphi_le_q : phi ≤ q) (hB : 0 ≤ B)
    (hK_pos : 0 < K) (hK_le_N : K ≤ N)
    (hK_lower : q / phi ≤ (K : ℝ))
    (hK_upper : (K : ℝ) ≤ 2 * q / phi)
    (hE_trivial : ∀ h ∈ Ioc 0 N, E h ≤ q)
    (hE_analytic : ∀ h ∈ Ioc K N,
      E h * (h : ℝ) ^ 2 * phi ^ 2 ≤ B * q ^ 3)
    (hlayer : secondMoment = q + 2 * ∑ h ∈ Ioc 0 N, E h) :
    secondMoment ≤ (5 + 2 * B) * q ^ 2 / phi := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hphi0 : phi ≠ 0 := ne_of_gt hphi
  have hK_real_pos : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  have hcoeff_nonneg : 0 ≤ B * q ^ 3 / phi ^ 2 := by positivity
  have hsplit :
      ∑ h ∈ Ioc 0 N, E h =
        (∑ h ∈ Ioc 0 K, E h) + ∑ h ∈ Ioc K N, E h := by
    rw [← sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    rw [Ioc_union_Ioc_eq_Ioc (Nat.zero_le K) hK_le_N]
  have hsmall : ∑ h ∈ Ioc 0 K, E h ≤ (K : ℝ) * q := by
    calc
      ∑ h ∈ Ioc 0 K, E h ≤ ∑ _h ∈ Ioc 0 K, q := by
        apply sum_le_sum
        intro h hh
        exact hE_trivial h (by
          rw [mem_Ioc] at hh ⊢
          exact ⟨hh.1, hh.2.trans hK_le_N⟩)
      _ = (K : ℝ) * q := by simp
  have hlarge_pointwise : ∀ h ∈ Ioc K N,
      E h ≤ (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
    intro h hh
    have hh_nat_pos : 0 < h := lt_of_lt_of_le hK_pos (mem_Ioc.mp hh).1.le
    have hh_real_pos : 0 < (h : ℝ) := by exact_mod_cast hh_nat_pos
    have hden_pos : 0 < (h : ℝ) ^ 2 * phi ^ 2 := by positivity
    have hdiv : E h ≤ B * q ^ 3 / ((h : ℝ) ^ 2 * phi ^ 2) := by
      apply (le_div_iff₀ hden_pos).2
      simpa only [mul_assoc] using hE_analytic h hh
    calc
      E h ≤ B * q ^ 3 / ((h : ℝ) ^ 2 * phi ^ 2) := hdiv
      _ = (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
        field_simp [ne_of_gt hh_real_pos, hphi0]
  have hinv_tail :
      (∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹)) ≤ ((K : ℝ)⁻¹) := by
    calc
      (∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹))
          ≤ ((K : ℝ)⁻¹) - ((N : ℝ)⁻¹) :=
        sum_Ioc_inv_sq_le_sub (by omega) hK_le_N
      _ ≤ ((K : ℝ)⁻¹) := sub_le_self _ (inv_nonneg.mpr (by positivity))
  have hlarge :
      ∑ h ∈ Ioc K N, E h ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := by
    calc
      ∑ h ∈ Ioc K N, E h
          ≤ ∑ h ∈ Ioc K N,
              (B * q ^ 3 / phi ^ 2) * (((h : ℝ) ^ 2)⁻¹) := by
        exact sum_le_sum hlarge_pointwise
      _ = (B * q ^ 3 / phi ^ 2) *
            ∑ h ∈ Ioc K N, (((h : ℝ) ^ 2)⁻¹) := by
        rw [mul_sum]
      _ ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv_tail hcoeff_nonneg
  have hq_le_Kphi : q ≤ (K : ℝ) * phi := (div_le_iff₀ hphi).mp hK_lower
  have hinvK_le : ((K : ℝ)⁻¹) ≤ phi / q := by
    apply (le_div_iff₀ hq).2
    have hq_div_K : q / (K : ℝ) ≤ phi := by
      apply (div_le_iff₀ hK_real_pos).2
      simpa [mul_comm] using hq_le_Kphi
    simpa [div_eq_mul_inv, mul_comm] using hq_div_K
  have hlarge_final : ∑ h ∈ Ioc K N, E h ≤ B * q ^ 2 / phi := by
    calc
      ∑ h ∈ Ioc K N, E h
          ≤ (B * q ^ 3 / phi ^ 2) * ((K : ℝ)⁻¹) := hlarge
      _ ≤ (B * q ^ 3 / phi ^ 2) * (phi / q) :=
        mul_le_mul_of_nonneg_left hinvK_le hcoeff_nonneg
      _ = B * q ^ 2 / phi := by
        field_simp [hq0, hphi0]
  have hsmall_final : ∑ h ∈ Ioc 0 K, E h ≤ 2 * q ^ 2 / phi := by
    calc
      ∑ h ∈ Ioc 0 K, E h ≤ (K : ℝ) * q := hsmall
      _ ≤ (2 * q / phi) * q := mul_le_mul_of_nonneg_right hK_upper hq.le
      _ = 2 * q ^ 2 / phi := by ring
  have hfirst_moment : q ≤ q ^ 2 / phi := by
    apply (le_div_iff₀ hphi).2
    nlinarith
  rw [hlayer, hsplit]
  calc
    q + 2 * ((∑ h ∈ Ioc 0 K, E h) + ∑ h ∈ Ioc K N, E h)
        ≤ q + 2 * (2 * q ^ 2 / phi + B * q ^ 2 / phi) := by gcongr
    _ ≤ q ^ 2 / phi + 2 * (2 * q ^ 2 / phi + B * q ^ 2 / phi) := by gcongr
    _ = (5 + 2 * B) * q ^ 2 / phi := by ring

/-- Concrete finite deduction used by Erdős Problem 220.  The sole analytic
hypothesis is the division-free empty-window estimate supplied by the
Montgomery--Vaughan moment argument. -/
theorem gapSquareSum_le_of_emptyWindows_bound
    (n : ℕ) (hn : 0 < n) (B : ℝ) (hB : 0 ≤ B)
    (hEmpty : ∀ h : ℕ, 1 ≤ h → h ≤ n →
      ((emptyWindows n h).card : ℝ) * (h : ℝ) ^ 2 *
          (n.totient : ℝ) ^ 2 ≤ B * (n : ℝ) ^ 3) :
    gapSquareSum n ≤ (5 + 2 * B) * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
  let K : ℕ := ⌈(n : ℝ) / (n.totient : ℝ)⌉₊
  have hphiNat : 0 < n.totient := totient_pos_of_pos hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hphiR : 0 < (n.totient : ℝ) := by exact_mod_cast hphiNat
  have hphi_le_nR : (n.totient : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.totient_le n
  have hratio_one : (1 : ℝ) ≤ (n : ℝ) / (n.totient : ℝ) := by
    rw [le_div_iff₀ hphiR]
    simpa using hphi_le_nR
  have hK_pos : 0 < K := by
    dsimp [K]
    exact Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hratio_one)
  have hK_lower : (n : ℝ) / (n.totient : ℝ) ≤ (K : ℝ) := by
    simpa [K] using Nat.le_ceil ((n : ℝ) / (n.totient : ℝ))
  have hK_upper : (K : ℝ) ≤ 2 * (n : ℝ) / (n.totient : ℝ) := by
    have hceil : (⌈(n : ℝ) / (n.totient : ℝ)⌉₊ : ℝ) ≤
        2 * ((n : ℝ) / (n.totient : ℝ)) := by
      exact Nat.ceil_le_two_mul (by linarith [hratio_one])
    simpa [K, mul_div_assoc] using hceil
  have hK_le_n : K ≤ n := by
    dsimp [K]
    rw [Nat.ceil_le]
    apply (div_le_iff₀ hphiR).2
    have hphi_one : (1 : ℝ) ≤ (n.totient : ℝ) := by exact_mod_cast hphiNat
    nlinarith
  have htail :
      (n : ℝ) + 2 *
          ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ) ≤
        (5 + 2 * B) * (n : ℝ) ^ 2 / (n.totient : ℝ) := by
    apply concrete_emptyWindow_tail_deduction
        (fun h ↦ ((emptyWindows n h).card : ℝ)) n K
        (n : ℝ) (n.totient : ℝ) B
        ((n : ℝ) + 2 *
          ∑ h ∈ Ioc 0 n, ((emptyWindows n h).card : ℝ))
        hnR hphiR hphi_le_nR hB hK_pos hK_le_n hK_lower hK_upper
    · intro h hh
      exact_mod_cast card_emptyWindows_le n h
    · intro h hh
      have hKh : K < h := (mem_Ioc.mp hh).1
      exact hEmpty h (by omega) (mem_Ioc.mp hh).2
    · rfl
  exact (gapSquareSum_le_emptyWindows_layer n).trans htail

end Erdos220

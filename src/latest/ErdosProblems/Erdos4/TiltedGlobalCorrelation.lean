import ErdosProblems.Erdos4.TiltedBlockCorrelation
import ErdosProblems.Erdos4.CollisionModuli

/-!
# Global block correlations

Only common prime divisors contribute the large tilt factor. The remaining
local errors are supported on collision primes of the disjoint union.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve CollisionModuli

theorem inv_baseline_le_exp {s : ℕ} (hs : 2 ≤ s) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 / baseline s u ≤ Real.exp (2 / (s : ℝ)) := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have ha0 := atom_nonneg hs hu0
  have ha := atom_le_inv hs hu0 hu1
  have ha2 : atom s u ≤ 1 / 2 :=
    ha.trans (one_div_le_one_div_of_le (by norm_num) hsR)
  have hB : 0 < 1 - atom s u := by linarith
  rw [baseline_eq_one_sub_atom hs hu0]
  calc
    _ ≤ 1 + 2 * atom s u := by
      apply (div_le_iff₀ hB).mpr
      nlinarith [mul_nonneg ha0 (show 0 ≤ 1 - 2 * atom s u by linarith)]
    _ ≤ 1 + 2 * (1 / (s : ℝ)) := add_le_add le_rfl (mul_le_mul_of_nonneg_left ha (show (0 : ℝ) ≤ 2 by norm_num))
    _ = 1 + 2 / (s : ℝ) := by ring
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (2 / (s : ℝ))

theorem inv_tilted_beta_le {s : ℕ} (hs : 2 ≤ s) (τ : ℝ) (hτ : 0 ≤ τ) :
    1 / beta s ((s : ℝ) ^ (-τ)) ≤ (s : ℝ) ^ τ * Real.exp (2 / (s : ℝ)) := by
  have hu0 := (rpow_tilt_pos hs τ).le
  have hu1 := rpow_tilt_le_one hs hτ
  calc
    _ = (s : ℝ) ^ τ * (1 / baseline s ((s : ℝ) ^ (-τ))) := by
      rw [beta_eq_baseline_mul, Real.rpow_neg (Nat.cast_nonneg _) τ]
      simp only [one_div, mul_inv_rev, inv_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_baseline_le_exp hs hu0 hu1)
      (Real.rpow_nonneg (Nat.cast_nonneg _) τ)

theorem local_pair_ratio_exp_le (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (E F : Finset (ZMod s)) {K : ℕ}
    (hE : E.card ≤ K) (hF : F.card ≤ K) (hsmall : 2 * K + 1 ≤ s) :
    (residueLaw s hs τ hτ).prob (fun a => a ∉ E ∪ F) /
        ((residueLaw s hs τ hτ).prob (fun a => a ∉ E) *
          (residueLaw s hs τ hτ).prob (fun a => a ∉ F)) ≤
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then (s : ℝ) ^ τ else 1) *
        Real.exp ((2 + 8 * (K : ℝ)) / (s : ℝ)) := by
  classical
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hD : (0 : ℝ) < s - 1 := by linarith
  have hc : ((E.erase 0 ∩ F.erase 0).card : ℝ) ≤ K := by
    exact_mod_cast ((Finset.card_le_card Finset.inter_subset_left).trans Finset.card_erase_le).trans hE
  have hcdiv : ((E.erase 0 ∩ F.erase 0).card : ℝ) / ((s : ℝ) - 1) ≤ 2 * (K : ℝ) / s := by
    apply (div_le_div_iff₀ hD hspos).mpr
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith [mul_nonneg hK0 (show 0 ≤ (s : ℝ) - 2 by linarith)]
  have hshort :
      1 + 4 * (((E.erase 0 ∩ F.erase 0).card : ℝ) / ((s : ℝ) - 1)) ≤
        Real.exp (8 * (K : ℝ) / s) := by
    calc
      _ ≤ 1 + 4 * (2 * (K : ℝ) / s) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hcdiv (show (0 : ℝ) ≤ 4 by norm_num))
      _ = 1 + 8 * (K : ℝ) / s := by ring
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (8 * (K : ℝ) / s)
  have hfactor :
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 / beta s ((s : ℝ) ^ (-τ)) else 1) ≤
        (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then (s : ℝ) ^ τ else 1) *
          Real.exp (2 / (s : ℝ)) := by
    split_ifs
    · exact inv_tilted_beta_le hs τ hτ
    · simpa only [one_mul] using Real.one_le_exp (by positivity : 0 ≤ 2 / (s : ℝ))
  have hfac0 : 0 ≤
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 / beta s ((s : ℝ) ^ (-τ)) else 1) := by
    split_ifs
    · exact div_nonneg zero_le_one (beta_nonneg hs (rpow_tilt_pos hs τ).le)
    · norm_num
  calc
    _ ≤ _ := localLaw_pair_ratio_le s hs _ (rpow_tilt_pos hs τ) (rpow_tilt_le_one hs hτ) E F
      (by omega) (by omega)
    _ ≤ ((if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then (s : ℝ) ^ τ else 1) *
        Real.exp (2 / (s : ℝ))) * Real.exp (8 * (K : ℝ) / s) :=
      mul_le_mul hfactor hshort (by positivity) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

omit [Fintype P] [DecidableEq P] in
theorem residues_disjoint_of_injective_union (T U : Finset ℕ) (l : P)
    (hdis : Disjoint T U) (hinj : Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) (↑(T ∪ U) : Set ℕ)) :
    Disjoint (residues ell T l) (residues ell U l) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨n, hn, hna⟩ := Finset.mem_image.mp ha
  obtain ⟨m, hm, hma⟩ := Finset.mem_image.mp hb
  have hnm := hinj (Finset.mem_union_left U hn) (Finset.mem_union_right T hm) (hna.trans hma.symm)
  exact (Finset.disjoint_left.mp hdis hn) (hnm ▸ hm)

theorem local_pair_ratio_le_one_of_disjoint (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (E F : Finset (ZMod s)) (hdis : Disjoint E F)
    (hE : 2 * E.card ≤ s - 1) (hF : 2 * F.card ≤ s - 1) :
    (residueLaw s hs τ hτ).prob (fun a => a ∉ E ∪ F) /
        ((residueLaw s hs τ hτ).prob (fun a => a ∉ E) *
          (residueLaw s hs τ hτ).prob (fun a => a ∉ F)) ≤ 1 := by
  have hz : ¬((0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F) :=
    fun h => (Finset.disjoint_left.mp hdis h.1) h.2
  have hinter : E.erase 0 ∩ F.erase 0 = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (hdis.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))
  have hh := localLaw_pair_ratio_le s hs _ (rpow_tilt_pos hs τ) (rpow_tilt_le_one hs hτ) E F hE hF
  simpa only [residueLaw, if_neg hz, hinter, Finset.card_empty, Nat.cast_zero, zero_div, mul_zero, add_zero, one_mul]
    using hh

def blockGcd (T U : Finset ℕ) : ℕ := Nat.gcd (∏ n ∈ T, n) (∏ n ∈ U, n)

noncomputable def commonDivisorTilt (τ : ℝ) (T U : Finset ℕ) : ℝ :=
  ∏ l, if ell l ∣ blockGcd T U then (ell l : ℝ) ^ τ else 1

omit [DecidableEq P] [∀ l, Fact (ell l).Prime] in
theorem commonDivisorTilt_nonneg (τ : ℝ) (T U : Finset ℕ) :
    0 ≤ commonDivisorTilt ell τ T U := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · norm_num

omit [DecidableEq P] in
theorem commonDivisorTilt_eq (hinj : Function.Injective ell) (τ : ℝ) (T U : Finset ℕ)
    (hG : Squarefree (blockGcd T U))
    (hcomplete : ∀ p ∈ (blockGcd T U).primeFactors, ∃ l, ell l = p) :
    commonDivisorTilt ell τ T U = (blockGcd T U : ℝ) ^ τ := by
  have hh := divisor_tilt_product ell hinj (-τ) hG.ne_zero hcomplete
  simp only [neg_neg] at hh
  rw [commonDivisorTilt, hh, nat_prod_rpow, Nat.prod_primeFactors_of_squarefree hG]

omit [Fintype P] [DecidableEq P] in
theorem shared_zero_iff (T U : Finset ℕ) (l : P) :
    (0 : ZMod (ell l)) ∈ residues ell T l ∧ (0 : ZMod (ell l)) ∈ residues ell U l ↔
      ell l ∣ blockGcd T U := by
  rw [zero_mem_residues_iff, zero_mem_residues_iff, blockGcd, Nat.dvd_gcd_iff]

theorem sieveLaw_pair_ratio_le (τ : ℝ) (hτ : 0 ≤ τ) (T U : Finset ℕ)
    (hdis : Disjoint T U) {K : ℕ} (hT : T.card ≤ K) (hU : U.card ≤ K)
    (hsmall : ∀ l, 2 * K + 1 ≤ ell l) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a (T ∪ U)) /
        ((sieveLaw ell τ hτ).prob (fun a => Survives ell a T) *
          (sieveLaw ell τ hτ).prob (fun a => Survives ell a U)) ≤
      commonDivisorTilt ell τ T U * Real.exp ((2 + 8 * (K : ℝ)) *
        ∑ l ∈ collisionPrimes ell (T ∪ U), 1 / (ell l : ℝ)) := by
  classical
  let error := fun l : P => if l ∈ collisionPrimes ell (T ∪ U) then (2 + 8 * (K : ℝ)) / ell l else 0
  have hlocal (l : P) :
      (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).prob
          (fun a => a ∉ residues ell (T ∪ U) l) /
        ((residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).prob
            (fun a => a ∉ residues ell T l) *
          (residueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ).prob
            (fun a => a ∉ residues ell U l)) ≤
      (if ell l ∣ blockGcd T U then (ell l : ℝ) ^ τ else 1) * Real.exp (error l) := by
    have hcardT : (residues ell T l).card ≤ K := Finset.card_image_le.trans hT
    have hcardU : (residues ell U l).card ≤ K := Finset.card_image_le.trans hU
    have hres : residues ell (T ∪ U) l = residues ell T l ∪ residues ell U l := Finset.image_union _ _
    rw [hres]
    by_cases hc : l ∈ collisionPrimes ell (T ∪ U)
    · have hh := local_pair_ratio_exp_le (ell l) (Fact.out : (ell l).Prime).two_le τ hτ
        (residues ell T l) (residues ell U l) hcardT hcardU (hsmall l)
      simpa only [shared_zero_iff, error, if_pos hc] using hh
    · have hinj : Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) (↑(T ∪ U) : Set ℕ) := by
        by_contra hn
        exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hn⟩)
      have hd := residues_disjoint_of_injective_union ell T U l hdis hinj
      have hnot : ¬ell l ∣ blockGcd T U := by
        intro h
        obtain ⟨hzT, hzU⟩ := (shared_zero_iff ell T U l).mpr h
        exact (Finset.disjoint_left.mp hd hzT) hzU
      have hh := local_pair_ratio_le_one_of_disjoint (ell l) (Fact.out : (ell l).Prime).two_le
        τ hτ (residues ell T l) (residues ell U l) hd (by have := hsmall l; omega)
        (by have := hsmall l; omega)
      simpa only [error, if_neg hc, if_neg hnot, Real.exp_zero, mul_one] using hh
  rw [sieveLaw_survival_product, sieveLaw_survival_product, sieveLaw_survival_product,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  calc
    _ ≤ ∏ l, ((if ell l ∣ blockGcd T U then (ell l : ℝ) ^ τ else 1) * Real.exp (error l)) := by
      apply Finset.prod_le_prod
      · intro l _
        exact div_nonneg (FiniteLaw.prob_nonneg _ _) (mul_nonneg (FiniteLaw.prob_nonneg _ _) (FiniteLaw.prob_nonneg _ _))
      · intro l _
        exact hlocal l
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      unfold error collisionPrimes
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> ring

/-- A quantitative unrooted correlation bound, sufficient for (4.11). -/
theorem sieveLaw_pair_ratio_uniform (hinj : Function.Injective ell)
    (τ : ℝ) (hτ : 0 ≤ τ) (T U : Finset ℕ) (hdis : Disjoint T U)
    {K Y : ℕ} (hT : T.card ≤ K) (hU : U.card ≤ K) (hsmall : ∀ l, 2 * K + 1 ≤ ell l)
    (hY : 1 ≤ Y) (hbound : ∀ n ∈ T ∪ U, n ≤ Y) {w : ℝ}
    (hw : 0 < w) (hlarge : ∀ l, w ≤ ell l)
    (hG : Squarefree (blockGcd T U))
    (hcomplete : ∀ p ∈ (blockGcd T U).primeFactors, ∃ l, ell l = p) :
    (sieveLaw ell τ hτ).prob (fun a => Survives ell a (T ∪ U)) /
        ((sieveLaw ell τ hτ).prob (fun a => Survives ell a T) *
          (sieveLaw ell τ hτ).prob (fun a => Survives ell a U)) ≤
      (blockGcd T U : ℝ) ^ τ * Real.exp ((2 + 8 * (K : ℝ)) *
        ((T ∪ U).card : ℝ) ^ 2 * Real.log Y / (w * Real.log 2)) := by
  have hh := sieveLaw_pair_ratio_le ell τ hτ T U hdis hT hU hsmall
  rw [commonDivisorTilt_eq ell hinj τ T U hG hcomplete] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply Real.exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left
    (collision_reciprocal_le ell hinj (T ∪ U) hY hbound hw hlarge)
    (show 0 ≤ 2 + 8 * (K : ℝ) by positivity)
  exact hc.trans_eq (by ring)

end Erdos4.Tilted

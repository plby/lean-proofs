import ErdosProblems.Erdos4.TiltedRootedCorrelation
import ErdosProblems.Erdos4.TiltedGlobalCorrelation

/-! Global rooted correlations use the gcd of companion products only. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve CollisionModuli

noncomputable def rootedResidueLaw (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) : FiniteLaw (ZMod s) :=
  rootedLocalLaw s hs ((s : ℝ) ^ (-τ)) (rpow_tilt_pos hs τ) (rpow_tilt_le_one hs hτ) (v : ZMod s)

theorem rooted_local_pair_ratio_exp_le (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) (E F : Finset (ZMod s))
    (hvE : (v : ZMod s) ∉ E) (hvF : (v : ZMod s) ∉ F) {K : ℕ}
    (hE : E.card ≤ K) (hF : F.card ≤ K) (hsmall : 2 * (K + 1) + 1 ≤ s) :
    (rootedResidueLaw s hs τ hτ v).prob (fun a => a ∉ E ∪ F) /
        ((rootedResidueLaw s hs τ hτ v).prob (fun a => a ∉ E) *
          (rootedResidueLaw s hs τ hτ v).prob (fun a => a ∉ F)) ≤
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then (s : ℝ) ^ τ else 1) *
        Real.exp (8 * ((K : ℝ) + 1) / s) := by
  classical
  have hh := rootedLocalLaw_pair_ratio_le s hs _ (rpow_tilt_pos hs τ) (rpow_tilt_le_one hs hτ)
    (v : ZMod s) E F hvE hvF (by omega) (by omega)
  have hinv : 1 / (s : ℝ) ^ (-τ) = (s : ℝ) ^ τ := by
    rw [Real.rpow_neg (Nat.cast_nonneg _) τ, one_div, inv_inv]
  rw [hinv] at hh
  apply hh.trans
  have hfac0 : 0 ≤ (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then (s : ℝ) ^ τ else 1) := by
    split_ifs <;> positivity
  apply mul_le_mul_of_nonneg_left _ hfac0
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hD : (0 : ℝ) < s - 1 := by linarith
  have hc : ((E.erase 0 ∩ F.erase 0).card : ℝ) ≤ K := by
    exact_mod_cast ((Finset.card_le_card Finset.inter_subset_left).trans Finset.card_erase_le).trans hE
  have hnum : ((E.erase 0 ∩ F.erase 0).card : ℝ) +
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 else 0) ≤ (K : ℝ) + 1 := by
    split_ifs <;> linarith
  have hdiv : (((E.erase 0 ∩ F.erase 0).card : ℝ) +
      if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 else 0) / ((s : ℝ) - 1) ≤
      2 * ((K : ℝ) + 1) / s := by
    apply (div_le_div_iff₀ hD hspos).mpr
    nlinarith [mul_nonneg (show 0 ≤ (K : ℝ) + 1 by positivity) (show 0 ≤ (s : ℝ) - 2 by linarith)]
  calc
    _ ≤ 1 + 4 * (2 * ((K : ℝ) + 1) / s) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 4 by norm_num))
    _ = 1 + 8 * ((K : ℝ) + 1) / s := by ring
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (8 * ((K : ℝ) + 1) / s)

theorem rooted_local_pair_ratio_le_one_of_disjoint (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) (E F : Finset (ZMod s))
    (hvE : (v : ZMod s) ∉ E) (hvF : (v : ZMod s) ∉ F) (hdis : Disjoint E F)
    (hE : 2 * (E.card + 1) ≤ s - 1) (hF : 2 * (F.card + 1) ≤ s - 1) :
    (rootedResidueLaw s hs τ hτ v).prob (fun a => a ∉ E ∪ F) /
        ((rootedResidueLaw s hs τ hτ v).prob (fun a => a ∉ E) *
          (rootedResidueLaw s hs τ hτ v).prob (fun a => a ∉ F)) ≤ 1 := by
  have hz : ¬((0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F) :=
    fun h => (Finset.disjoint_left.mp hdis h.1) h.2
  have hinter : E.erase 0 ∩ F.erase 0 = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (hdis.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))
  have hh := rootedLocalLaw_pair_ratio_le s hs _ (rpow_tilt_pos hs τ) (rpow_tilt_le_one hs hτ)
    (v : ZMod s) E F hvE hvF hE hF
  simpa only [rootedResidueLaw, if_neg hz, hinter, Finset.card_empty, Nat.cast_zero, zero_add,
    zero_div, mul_zero, add_zero, one_mul] using hh

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem rootedSieveLaw_survival_product (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) (T : Finset ℕ) :
    (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a T) =
      ∏ l, (rootedResidueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ v).prob
        (fun a => a ∉ residues ell T l) :=
  rootedSieveLaw_prob_all ell τ hτ v (fun l a => a ∉ residues ell T l)

theorem rootedSieveLaw_survival_insert (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) (T : Finset ℕ) :
    (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a T) =
      (sieveLaw ell τ hτ).prob (fun a => Survives ell a (insert v T)) /
        (sieveLaw ell τ hτ).prob (fun a => Survives ell a {v}) := by
  classical
  rw [rootedSieveLaw, FiniteLaw.condition_prob _ _ _ _ (sieveLaw_singleton_pos ell τ hτ v).ne']
  have heq : (fun a => Survives ell a {v} ∧ Survives ell a T) =
      (fun a => Survives ell a (insert v T)) := by
    funext a
    exact propext (survives_insert ell a v T).symm
  rw [heq]

theorem rootedSieveLaw_pair_ratio_le (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) (T U : Finset ℕ)
    (hvT : ∀ l, (v : ZMod (ell l)) ∉ residues ell T l)
    (hvU : ∀ l, (v : ZMod (ell l)) ∉ residues ell U l)
    (hdis : Disjoint T U) {K : ℕ} (hT : T.card ≤ K) (hU : U.card ≤ K)
    (hsmall : ∀ l, 2 * (K + 1) + 1 ≤ ell l) :
    (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a (T ∪ U)) /
        ((rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a T) *
          (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a U)) ≤
      commonDivisorTilt ell τ T U * Real.exp (8 * ((K : ℝ) + 1) *
        ∑ l ∈ collisionPrimes ell (T ∪ U), 1 / (ell l : ℝ)) := by
  classical
  let error := fun l : P => if l ∈ collisionPrimes ell (T ∪ U) then 8 * ((K : ℝ) + 1) / ell l else 0
  have hlocal (l : P) :
      (rootedResidueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ v).prob
          (fun a => a ∉ residues ell (T ∪ U) l) /
        ((rootedResidueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ v).prob
            (fun a => a ∉ residues ell T l) *
          (rootedResidueLaw (ell l) (Fact.out : (ell l).Prime).two_le τ hτ v).prob
            (fun a => a ∉ residues ell U l)) ≤
      (if ell l ∣ blockGcd T U then (ell l : ℝ) ^ τ else 1) * Real.exp (error l) := by
    have hcardT : (residues ell T l).card ≤ K := Finset.card_image_le.trans hT
    have hcardU : (residues ell U l).card ≤ K := Finset.card_image_le.trans hU
    have hres : residues ell (T ∪ U) l = residues ell T l ∪ residues ell U l := Finset.image_union _ _
    rw [hres]
    by_cases hc : l ∈ collisionPrimes ell (T ∪ U)
    · have hh := rooted_local_pair_ratio_exp_le (ell l) (Fact.out : (ell l).Prime).two_le τ hτ v
        (residues ell T l) (residues ell U l) (hvT l) (hvU l) hcardT hcardU (hsmall l)
      simpa only [shared_zero_iff, error, if_pos hc] using hh
    · have hinj : Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) (↑(T ∪ U) : Set ℕ) := by
        by_contra hn
        exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hn⟩)
      have hd := residues_disjoint_of_injective_union ell T U l hdis hinj
      have hnot : ¬ell l ∣ blockGcd T U := by
        intro h
        obtain ⟨hzT, hzU⟩ := (shared_zero_iff ell T U l).mpr h
        exact (Finset.disjoint_left.mp hd hzT) hzU
      have hh := rooted_local_pair_ratio_le_one_of_disjoint (ell l) (Fact.out : (ell l).Prime).two_le
        τ hτ v (residues ell T l) (residues ell U l) (hvT l) (hvU l) hd
        (by have := hsmall l; omega) (by have := hsmall l; omega)
      simpa only [error, if_neg hc, if_neg hnot, Real.exp_zero, mul_one] using hh
  rw [rootedSieveLaw_survival_product, rootedSieveLaw_survival_product, rootedSieveLaw_survival_product,
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

/-- Equation (5.9), at the level of conditional joint-to-product probabilities. -/
theorem rootedSieveLaw_pair_ratio_uniform (hinj : Function.Injective ell)
    (τ : ℝ) (hτ : 0 ≤ τ) (v : ℕ) (T U : Finset ℕ)
    (hvT : ∀ l, (v : ZMod (ell l)) ∉ residues ell T l)
    (hvU : ∀ l, (v : ZMod (ell l)) ∉ residues ell U l)
    (hdis : Disjoint T U) {K Y : ℕ} (hT : T.card ≤ K) (hU : U.card ≤ K)
    (hsmall : ∀ l, 2 * (K + 1) + 1 ≤ ell l) (hY : 1 ≤ Y) (hbound : ∀ n ∈ T ∪ U, n ≤ Y)
    {w : ℝ} (hw : 0 < w) (hlarge : ∀ l, w ≤ ell l)
    (hG : Squarefree (blockGcd T U))
    (hcomplete : ∀ p ∈ (blockGcd T U).primeFactors, ∃ l, ell l = p) :
    (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a (T ∪ U)) /
        ((rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a T) *
          (rootedSieveLaw ell τ hτ v).prob (fun a => Survives ell a U)) ≤
      (blockGcd T U : ℝ) ^ τ * Real.exp (8 * ((K : ℝ) + 1) *
        ((T ∪ U).card : ℝ) ^ 2 * Real.log Y / (w * Real.log 2)) := by
  have hh := rootedSieveLaw_pair_ratio_le ell τ hτ v T U hvT hvU hdis hT hU hsmall
  rw [commonDivisorTilt_eq ell hinj τ T U hG hcomplete] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply Real.exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left
    (collision_reciprocal_le ell hinj (T ∪ U) hY hbound hw hlarge)
    (show 0 ≤ 8 * ((K : ℝ) + 1) by positivity)
  exact hc.trans_eq (by ring)

end Erdos4.Tilted

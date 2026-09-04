import ErdosProblems.Erdos747.UpperEngine
import Mathlib.Data.Fintype.BigOperators

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Uniform fixed-size samples as conditioned Bernoulli samples -/

/-- Independent labels on the elements of `s`.  Declaring an element
selected when its label lies below `M` gives independent Bernoulli
selection with parameter `M / |s|`. -/
abbrev LabelSample {α : Type*} (s : Finset α) := ↥s → Fin s.card

def lowLabels (K M : ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun i ↦ i.1 < M

def highLabels (K M : ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun i ↦ M ≤ i.1

@[simp] lemma mem_lowLabels {K M : ℕ} (i : Fin K) :
    i ∈ lowLabels K M ↔ i.1 < M := by
  simp [lowLabels]

@[simp] lemma mem_highLabels {K M : ℕ} (i : Fin K) :
    i ∈ highLabels K M ↔ M ≤ i.1 := by
  simp [highLabels]

/-- Labels below `M` are canonically `Fin M`. -/
def lowLabelsEquiv (K M : ℕ) : ↥(lowLabels K M) ≃ Fin (min M K) where
  toFun i := ⟨i.1.1, by
    have hiM : i.1.1 < M := (mem_lowLabels i.1).mp i.2
    have hiK : i.1.1 < K := i.1.2
    exact lt_min hiM hiK⟩
  invFun i := ⟨⟨i.1, by
    exact lt_of_lt_of_le i.2 (min_le_right M K)⟩, by
      apply (mem_lowLabels _).mpr
      exact lt_of_lt_of_le i.2 (min_le_left M K)⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv i := by
    apply Fin.ext
    rfl

@[simp] lemma card_lowLabels (K M : ℕ) :
    (lowLabels K M).card = min M K := by
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr (lowLabelsEquiv K M)

/-- Labels at least `M` are canonically the complementary final interval. -/
def highLabelsEquiv (K M : ℕ) : ↥(highLabels K M) ≃ Fin (K - M) where
  toFun i := ⟨i.1.1 - M, by
    have hiM : M ≤ i.1.1 := (mem_highLabels i.1).mp i.2
    have hiK : i.1.1 < K := i.1.2
    omega⟩
  invFun i := ⟨⟨M + i.1, by
    have hi : i.1 < K - M := i.2
    omega⟩, by
      apply (mem_highLabels _).mpr
      exact Nat.le_add_right M i.1⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hiM : M ≤ i.1.1 := (mem_highLabels i.1).mp i.2
    change M + (i.1.1 - M) = i.1.1
    omega
  right_inv i := by
    apply Fin.ext
    change (M + i.1) - M = i.1
    omega

@[simp] lemma card_highLabels (K M : ℕ) :
    (highLabels K M).card = K - M := by
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr (highLabelsEquiv K M)

/-- The subset selected by a label configuration. -/
def labelSelected {α : Type*} (s : Finset α) (M : ℕ)
    (omega : LabelSample s) : Finset ↥s :=
  Finset.univ.filter fun x ↦ (omega x).1 < M

@[simp] lemma mem_labelSelected {α : Type*} (s : Finset α) (M : ℕ)
    (omega : LabelSample s) (x : ↥s) :
    x ∈ labelSelected s M omega ↔ (omega x).1 < M := by
  simp [labelSelected]

/-- Coordinatewise label choices producing a prescribed selected subset. -/
def labelsForSubset {α : Type*} (s : Finset α) (M : ℕ)
    (H : Finset ↥s) (x : ↥s) : Finset (Fin s.card) :=
  if x ∈ H then lowLabels s.card M else highLabels s.card M

lemma labelSelected_fiber_eq_piFinset {α : Type*}
    (s : Finset α) (M : ℕ) (H : Finset ↥s) :
    (Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ labelSelected s M omega = H) =
      Fintype.piFinset (labelsForSubset s M H) := by
  ext omega
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.mem_piFinset]
  constructor
  · intro hselected x
    by_cases hx : x ∈ H
    · rw [labelsForSubset, if_pos hx, mem_lowLabels]
      exact (mem_labelSelected s M omega x).mp
        (hselected.symm ▸ hx)
    · rw [labelsForSubset, if_neg hx, mem_highLabels]
      exact le_of_not_gt fun hlt ↦ hx
        (hselected ▸ (mem_labelSelected s M omega x).mpr hlt)
  · intro hlabels
    ext x
    by_cases hx : x ∈ H
    · have hxlow := hlabels x
      rw [labelsForSubset, if_pos hx, mem_lowLabels] at hxlow
      simp only [mem_labelSelected, hx, hxlow]
    · have hxhigh := hlabels x
      rw [labelsForSubset, if_neg hx, mem_highLabels] at hxhigh
      simp only [mem_labelSelected, hx, iff_false]
      omega

/-- Every fixed `M`-subset has the same number of label configurations in
its fiber. -/
lemma card_labelSelected_fiber {α : Type*}
    (s : Finset α) (M : ℕ) (H : Finset ↥s)
    (hM : M ≤ s.card) (hH : H.card = M) :
    ((Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ labelSelected s M omega = H)).card =
      M ^ M * (s.card - M) ^ (s.card - M) := by
  rw [labelSelected_fiber_eq_piFinset, Fintype.card_piFinset]
  have hcardOutside : ((Finset.univ : Finset ↥s) \ H).card =
      s.card - M := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ H),
      Finset.card_univ, Fintype.card_coe, hH]
  calc
    (∏ x : ↥s, (labelsForSubset s M H x).card) =
        (∏ x ∈ H, M) *
          ∏ x ∈ (Finset.univ : Finset ↥s) \ H, (s.card - M) := by
      change (∏ x ∈ (Finset.univ : Finset ↥s),
        (labelsForSubset s M H x).card) = _
      simp only [labelsForSubset, apply_ite, card_lowLabels,
        card_highLabels, min_eq_left hM]
      rw [Finset.prod_ite]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.filter_notMem_eq_sdiff]
    _ = M ^ M * (s.card - M) ^ (s.card - M) := by
      simp only [Finset.prod_const, hH, hcardOutside]

/-- Label configurations whose selected set has size `M` are partitioned
into the equal fibers indexed by `M`-subsets. -/
lemma card_labelSelected_slice {α : Type*}
    (s : Finset α) (M : ℕ) (hM : M ≤ s.card) :
    ((Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ (labelSelected s M omega).card = M)).card =
      s.card.choose M *
        (M ^ M * (s.card - M) ^ (s.card - M)) := by
  let A := (Finset.univ : Finset (LabelSample s)).filter
    (fun omega ↦ (labelSelected s M omega).card = M)
  let T := (Finset.univ : Finset ↥s).powersetCard M
  let f : LabelSample s → Finset ↥s := labelSelected s M
  have hmap : ∀ omega ∈ A, f omega ∈ T := by
    intro omega homega
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp homega).2⟩
  have hfiber : ∀ H ∈ T,
      finiteMapFiber A f H =
        (Finset.univ : Finset (LabelSample s)).filter
          (fun omega ↦ labelSelected s M omega = H) := by
    intro H hH
    have hHcard : H.card = M := (Finset.mem_powersetCard.mp hH).2
    ext omega
    simp only [finiteMapFiber, Finset.mem_filter, Finset.mem_univ,
      true_and, A, f]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨h ▸ hHcard, h⟩
  have hsum := sum_card_finiteMapFiber_eq_card A T f hmap
  rw [← hsum]
  calc
    (∑ H ∈ T, (finiteMapFiber A f H).card) =
        ∑ _H ∈ T,
          (M ^ M * (s.card - M) ^ (s.card - M)) := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [hfiber H hH]
      exact card_labelSelected_fiber s M H hM
        (Finset.mem_powersetCard.mp hH).2
    _ = s.card.choose M *
          (M ^ M * (s.card - M) ^ (s.card - M)) := by
      rw [Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_coe]
      simp only [nsmul_eq_mul]
      norm_num

/-- The same equal-fiber count, restricted by an arbitrary event on the
selected `M`-subset. -/
lemma card_labelSelected_event_slice {α : Type*}
    (s : Finset α) (M : ℕ) (P : Finset ↥s → Prop)
    (hM : M ≤ s.card) :
    ((Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦
          (labelSelected s M omega).card = M ∧
            P (labelSelected s M omega))).card =
      (((Finset.univ : Finset ↥s).powersetCard M).filter P).card *
        (M ^ M * (s.card - M) ^ (s.card - M)) := by
  let A := (Finset.univ : Finset (LabelSample s)).filter
    (fun omega ↦ (labelSelected s M omega).card = M ∧
      P (labelSelected s M omega))
  let T := ((Finset.univ : Finset ↥s).powersetCard M).filter P
  let f : LabelSample s → Finset ↥s := labelSelected s M
  have hmap : ∀ omega ∈ A, f omega ∈ T := by
    intro omega homega
    have h := (Finset.mem_filter.mp homega).2
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, h.1⟩, h.2⟩
  have hfiber : ∀ H ∈ T,
      finiteMapFiber A f H =
        (Finset.univ : Finset (LabelSample s)).filter
          (fun omega ↦ labelSelected s M omega = H) := by
    intro H hH
    have hHT := Finset.mem_filter.mp hH
    have hHcard : H.card = M :=
      (Finset.mem_powersetCard.mp hHT.1).2
    have hHP : P H := hHT.2
    ext omega
    simp only [finiteMapFiber, Finset.mem_filter, Finset.mem_univ,
      true_and, A, f]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨⟨h ▸ hHcard, h ▸ hHP⟩, h⟩
  have hsum := sum_card_finiteMapFiber_eq_card A T f hmap
  rw [← hsum]
  calc
    (∑ H ∈ T, (finiteMapFiber A f H).card) =
        ∑ _H ∈ T,
          (M ^ M * (s.card - M) ^ (s.card - M)) := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [hfiber H hH]
      exact card_labelSelected_fiber s M H hM
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hH).1).2
    _ = T.card *
          (M ^ M * (s.card - M) ^ (s.card - M)) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      norm_num
    _ = _ := by rfl

/-- The unnormalized mass of the `j`th atom of
`Binomial(K, M / K)`, with denominators cleared. -/
def binomialLabelMass (K M j : ℕ) : ℕ :=
  K.choose j * M ^ j * (K - M) ^ (K - j)

/-- Adjacent cleared binomial masses satisfy the usual ratio identity. -/
lemma binomialLabelMass_succ_cross (K M j : ℕ) (hj : j < K) :
    binomialLabelMass K M (j + 1) * ((j + 1) * (K - M)) =
      binomialLabelMass K M j * ((K - j) * M) := by
  have hsub : K - j = (K - (j + 1)) + 1 := by omega
  unfold binomialLabelMass
  calc
    (K.choose (j + 1) * M ^ (j + 1) *
          (K - M) ^ (K - (j + 1))) * ((j + 1) * (K - M)) =
        (K.choose (j + 1) * (j + 1)) *
          (M ^ (j + 1) * (K - M) ^ (K - (j + 1)) *
            (K - M)) := by ring
    _ = (K.choose j * (K - j)) *
          (M ^ (j + 1) * (K - M) ^ (K - (j + 1)) *
            (K - M)) := by
      rw [Nat.choose_succ_right_eq]
    _ = (K.choose j * M ^ j * (K - M) ^ (K - j)) *
          ((K - j) * M) := by
      rw [hsub, pow_succ, pow_succ]
      ring

/-- The cleared binomial masses increase up to the parameter `M`. -/
lemma binomialLabelMass_le_succ_of_lt_mode
    (K M j : ℕ) (hM : M ≤ K) (hj : j < M) :
    binomialLabelMass K M j ≤ binomialLabelMass K M (j + 1) := by
  have hjK : j < K := hj.trans_le hM
  by_cases hMK : M = K
  · have hexp : 0 < K - j := Nat.sub_pos_of_lt hjK
    simp [binomialLabelMass, hMK, zero_pow hexp.ne']
  · have hMKlt : M < K := lt_of_le_of_ne hM hMK
    have hden : 0 < (j + 1) * (K - M) :=
      Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hMKlt)
    apply Nat.le_of_mul_le_mul_right (c := (j + 1) * (K - M)) _ hden
    rw [binomialLabelMass_succ_cross K M j hjK]
    apply Nat.mul_le_mul_left
    calc
      (j + 1) * (K - M) ≤ M * (K - M) :=
        Nat.mul_le_mul_right (K - M) (by omega)
      _ ≤ M * (K - j) :=
        Nat.mul_le_mul_left M (Nat.sub_le_sub_left (by omega) K)
      _ = (K - j) * M := by ac_rfl

/-- The cleared binomial masses decrease after the parameter `M`. -/
lemma binomialLabelMass_succ_le_of_mode_le
    (K M j : ℕ) (hM : M ≤ K) (hMj : M ≤ j) (hj : j < K) :
    binomialLabelMass K M (j + 1) ≤ binomialLabelMass K M j := by
  have hMKlt : M < K := hMj.trans_lt hj
  have hden : 0 < (j + 1) * (K - M) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hMKlt)
  apply Nat.le_of_mul_le_mul_right (c := (j + 1) * (K - M)) _ hden
  rw [binomialLabelMass_succ_cross K M j hj]
  apply Nat.mul_le_mul_left
  calc
    (K - j) * M ≤ (K - j) * (j + 1) :=
      Nat.mul_le_mul_left (K - j) (by omega)
    _ ≤ (K - M) * (j + 1) :=
      Nat.mul_le_mul_right (j + 1) (Nat.sub_le_sub_left hMj K)
    _ = (j + 1) * (K - M) := by ac_rfl

/-- Monotonicity of the cleared masses on the interval ending at the mode. -/
lemma binomialLabelMass_mono_left
    (K M j k : ℕ) (hM : M ≤ K) (hjk : j ≤ k) (hkM : k ≤ M) :
    binomialLabelMass K M j ≤ binomialLabelMass K M k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
      exact (ih (by omega)).trans
        (binomialLabelMass_le_succ_of_lt_mode K M k hM (by omega))

/-- Monotonicity of the cleared masses on the interval starting at the mode. -/
lemma binomialLabelMass_mono_right
    (K M j k : ℕ) (hM : M ≤ K) (hMj : M ≤ j)
    (hjk : j ≤ k) (hkK : k ≤ K) :
    binomialLabelMass K M k ≤ binomialLabelMass K M j := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
      exact (binomialLabelMass_succ_le_of_mode_le K M k hM
        (by omega) (by omega)).trans (ih (by omega))

/-- The `M`th atom is a mode of the cleared binomial mass sequence. -/
lemma binomialLabelMass_le_mode
    (K M j : ℕ) (hM : M ≤ K) (hj : j ≤ K) :
    binomialLabelMass K M j ≤ binomialLabelMass K M M := by
  by_cases hjM : j ≤ M
  · exact binomialLabelMass_mono_left K M j M hM hjM le_rfl
  · exact binomialLabelMass_mono_right K M M j hM (by omega)
      (by omega) hj

/-- The cleared binomial masses sum to the total number `K^K` of label
configurations. -/
lemma sum_binomialLabelMass (K M : ℕ) (hM : M ≤ K) :
    ∑ j ∈ Finset.range (K + 1), binomialLabelMass K M j = K ^ K := by
  simpa [binomialLabelMass, Nat.add_sub_of_le hM, mul_comm,
    mul_left_comm, mul_assoc] using (add_pow M (K - M) K).symm

/-- Since the `M`th atom is a mode among `K+1` atoms, its cleared mass is
at least a `1/(K+1)` fraction of all label configurations. -/
lemma pow_le_succ_mul_binomialLabelMass_mode
    (K M : ℕ) (hM : M ≤ K) :
    K ^ K ≤ (K + 1) * binomialLabelMass K M M := by
  rw [← sum_binomialLabelMass K M hM]
  calc
    (∑ j ∈ Finset.range (K + 1), binomialLabelMass K M j) ≤
        ∑ _j ∈ Finset.range (K + 1), binomialLabelMass K M M := by
      apply Finset.sum_le_sum
      intro j hj
      exact binomialLabelMass_le_mode K M j hM
        (by simpa using Finset.mem_range.mp hj)
    _ = (K + 1) * binomialLabelMass K M M := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      norm_num

/-- The probability that independent `Fin K` labels select exactly `M`
points is at least `1/(K+1)`, stated without division as a cardinal bound. -/
lemma labelSelected_slice_card_lower {α : Type*}
    (s : Finset α) (M : ℕ) (hM : M ≤ s.card) :
    s.card ^ s.card ≤ (s.card + 1) *
      ((Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ (labelSelected s M omega).card = M)).card := by
  rw [card_labelSelected_slice s M hM]
  simpa [binomialLabelMass, mul_assoc] using
    pow_le_succ_mul_binomialLabelMass_mode s.card M hM

/-- Restricting a finite uniform space to a nonempty slice costs at most
the reciprocal of the slice density. -/
lemma finsetProbability_restrict_le_mul_univ {Ω : Type*} [Fintype Ω]
    (S : Finset Ω) (P : Ω → Prop) (c : ℝ)
    (hS : S.Nonempty)
    (hcard : ((Finset.univ : Finset Ω).card : ℝ) ≤ c * S.card) :
    finsetProbability S P ≤
      c * finsetProbability (Finset.univ : Finset Ω) P := by
  have hSpos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hUpos : (0 : ℝ) < (Finset.univ : Finset Ω).card := by
    exact hSpos.trans_le (by
      exact_mod_cast Finset.card_le_card (Finset.subset_univ S))
  have hnum : ((S.filter P).card : ℝ) ≤
      (((Finset.univ : Finset Ω).filter P).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (by
      intro omega homega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp homega).2⟩)
  unfold finsetProbability
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hSpos).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hUpos).2
  calc
    ((S.filter P).card : ℝ) *
          ((Finset.univ : Finset Ω).card : ℝ) ≤
        (((Finset.univ : Finset Ω).filter P).card : ℝ) *
          ((Finset.univ : Finset Ω).card : ℝ) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (((Finset.univ : Finset Ω).filter P).card : ℝ) *
          (c * S.card) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = c * (((Finset.univ : Finset Ω).filter P).card : ℝ) *
          S.card := by ring

/-- Uniform sampling from `M`-subsets is exactly independent labeling
conditioned on selecting `M` elements. -/
lemma finsetProbability_powersetCard_eq_labelSelected_conditional
    {α : Type*} (s : Finset α) (M : ℕ)
    (P : Finset ↥s → Prop) (hM : M ≤ s.card) :
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M) P =
      finsetProbability
        ((Finset.univ : Finset (LabelSample s)).filter
          (fun omega ↦ (labelSelected s M omega).card = M))
        (fun omega ↦ P (labelSelected s M omega)) := by
  have hfilter :
      (((Finset.univ : Finset (LabelSample s)).filter
          (fun omega ↦ (labelSelected s M omega).card = M)).filter
        (fun omega ↦ P (labelSelected s M omega))) =
      (Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ (labelSelected s M omega).card = M ∧
          P (labelSelected s M omega)) := by
    ext omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hfactorPos : 0 <
      M ^ M * (s.card - M) ^ (s.card - M) := by
    have hself : ∀ a : ℕ, 0 < a ^ a := by
      intro a
      by_cases ha : a = 0
      · simp [ha]
      · exact Nat.pow_pos (Nat.pos_of_ne_zero ha)
    exact Nat.mul_pos (hself M) (hself (s.card - M))
  have hchoosePos : 0 < s.card.choose M := Nat.choose_pos hM
  have hfactorNe :
      ((M ^ M * (s.card - M) ^ (s.card - M) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hfactorPos.ne'
  have hchooseNe : ((s.card.choose M : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hchoosePos.ne'
  have hselfPowNe : ∀ a : ℕ, ((a ^ a : ℕ) : ℝ) ≠ 0 := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · exact_mod_cast (Nat.pow_pos (Nat.pos_of_ne_zero ha)).ne'
  unfold finsetProbability
  rw [hfilter, card_labelSelected_event_slice s M P hM,
    card_labelSelected_slice s M hM, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_coe]
  norm_num only [Nat.cast_mul]
  field_simp [hfactorNe, hchooseNe, hselfPowNe M,
    hselfPowNe (s.card - M)]
  rw [mul_div_cancel_right₀ _ (hselfPowNe (s.card - M))]

/-- The all-density conditioning transfer: a uniform fixed-size event is
bounded by `K+1` times its independent-label realization. -/
lemma finsetProbability_powersetCard_le_labelSelected
    {α : Type*} (s : Finset α) (M : ℕ)
    (P : Finset ↥s → Prop) (hM : M ≤ s.card) :
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M) P ≤
      (s.card + 1 : ℝ) *
        finsetProbability (Finset.univ : Finset (LabelSample s))
          (fun omega ↦ P (labelSelected s M omega)) := by
  let S := (Finset.univ : Finset (LabelSample s)).filter
    (fun omega ↦ (labelSelected s M omega).card = M)
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    rw [card_labelSelected_slice s M hM]
    exact Nat.mul_pos (Nat.choose_pos hM) (by
      have hself : ∀ a : ℕ, 0 < a ^ a := by
        intro a
        by_cases ha : a = 0
        · simp [ha]
        · exact Nat.pow_pos (Nat.pos_of_ne_zero ha)
      exact Nat.mul_pos (hself M) (hself (s.card - M)))
  have htotal : (Finset.univ : Finset (LabelSample s)).card =
      s.card ^ s.card := by
    simp [LabelSample, Fintype.card_fun]
  have hcard :
      (((Finset.univ : Finset (LabelSample s)).card : ℕ) : ℝ) ≤
        (s.card + 1 : ℝ) * S.card := by
    rw [htotal]
    exact_mod_cast labelSelected_slice_card_lower s M hM
  rw [finsetProbability_powersetCard_eq_labelSelected_conditional
    s M P hM]
  exact finsetProbability_restrict_le_mul_univ S
    (fun omega ↦ P (labelSelected s M omega)) (s.card + 1) hS hcard

/-! ### Marginal label laws -/

/-- A function on a finite type is equivalently a pair of functions on a
chosen subset and its complement. -/
def piSplitEquiv {ι β : Type*} [Fintype ι] (Y : Finset ι) :
    (ι → β) ≃ ((↥Y → β) × ({x : ι // x ∉ Y} → β)) where
  toFun omega :=
    (fun y ↦ omega y.1, fun y ↦ omega y.1)
  invFun p x := if hx : x ∈ Y then p.1 ⟨x, hx⟩
    else p.2 ⟨x, hx⟩
  left_inv omega := by
    funext x
    by_cases hx : x ∈ Y <;> simp [hx]
  right_inv p := by
    apply Prod.ext
    · funext y
      simp [y.2]
    · funext y
      have hy : y.1 ∉ Y := y.2
      simp [hy]

@[simp] lemma piSplitEquiv_apply_fst {ι β : Type*} [Fintype ι]
    (Y : Finset ι) (omega : ι → β) :
    (piSplitEquiv Y omega).1 = fun y ↦ omega y.1 := rfl

/-- Under a uniform product, an event depending only on the first
coordinate has the uniform first-coordinate probability. -/
lemma finsetProbability_univ_prod_fst
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (P : A → Prop) :
    finsetProbability (Finset.univ : Finset (A × B))
        (fun p ↦ P p.1) =
      finsetProbability (Finset.univ : Finset A) P := by
  have hfilter :
      (Finset.univ : Finset (A × B)).filter (fun p ↦ P p.1) =
        ((Finset.univ : Finset A).filter P).product
          (Finset.univ : Finset B) := by
    ext p
    simp
  have hBpos : 0 < Fintype.card B := Fintype.card_pos
  have hBne : ((Fintype.card B : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hBpos.ne'
  have hprodcard :
      (((Finset.univ : Finset A).filter P).product
        (Finset.univ : Finset B)).card =
      ((Finset.univ : Finset A).filter P).card *
        (Finset.univ : Finset B).card :=
    Finset.card_product _ _
  unfold finsetProbability
  rw [hfilter, hprodcard, Finset.card_univ, Finset.card_univ,
    Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ hBne]
  simp

/-- Restricting independent uniform labels to a fixed coordinate block
leaves independent uniform labels on that block. -/
lemma labelRestriction_probability_eq {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (Q : (↥Y → Fin s.card) → Prop) (hs : s.Nonempty) :
    finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦ Q (fun y ↦ omega y.1)) =
      finsetProbability (Finset.univ : Finset (↥Y → Fin s.card)) Q := by
  have hK : 0 < s.card := Finset.card_pos.mpr hs
  let b0 : Fin s.card := ⟨0, hK⟩
  let B := {x : ↥s // x ∉ Y} → Fin s.card
  let : Nonempty B :=
    ⟨fun _ ↦ b0⟩
  let E : LabelSample s ≃ ((↥Y → Fin s.card) × B) :=
    piSplitEquiv (β := Fin s.card) Y
  have hfiltercard :
      ((Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ Q (fun y ↦ omega y.1))).card =
      (((Finset.univ : Finset (↥Y → Fin s.card)).filter Q).product
        (Finset.univ : Finset B)).card := by
    refine Finset.card_bij
      (s := (Finset.univ : Finset (LabelSample s)).filter
        (fun omega ↦ Q (fun y ↦ omega y.1)))
      (t := ((Finset.univ : Finset (↥Y → Fin s.card)).filter Q).product
        (Finset.univ : Finset B))
      (fun omega _ ↦ E omega) ?_ ?_ ?_
    · intro omega homega
      have hQ := (Finset.mem_filter.mp homega).2
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_univ _⟩
      change Q (fun y ↦ omega y.1)
      exact hQ
    · intro omega₁ _ omega₂ _ heq
      exact E.injective heq
    · intro p hp
      refine ⟨E.symm p, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, E.apply_symm_apply p⟩
      have hQ := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      have hfst : (E (E.symm p)).1 = p.1 :=
        congrArg Prod.fst (E.apply_symm_apply p)
      have hrestriction : (fun y ↦ E.symm p y.1) = p.1 := by
        change (fun y ↦ E.symm p y.1) = p.1 at hfst
        exact hfst
      rw [hrestriction]
      exact hQ
  have htotal :
      (Finset.univ : Finset (LabelSample s)).card =
        (Finset.univ : Finset (↥Y → Fin s.card)).card *
          (Finset.univ : Finset B).card := by
    simp only [Finset.card_univ]
    exact (Fintype.card_congr E).trans
      (Fintype.card_prod (↥Y → Fin s.card) B)
  have hBpos : 0 < (Finset.univ : Finset B).card := by
    simpa only [Finset.card_univ] using (Fintype.card_pos : 0 < Fintype.card B)
  have hBne : (((Finset.univ : Finset B).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hBpos.ne'
  have hprodcard :
      (((Finset.univ : Finset (↥Y → Fin s.card)).filter Q).product
        (Finset.univ : Finset B)).card =
      ((Finset.univ : Finset (↥Y → Fin s.card)).filter Q).card *
        (Finset.univ : Finset B).card :=
    Finset.card_product _ _
  unfold finsetProbability
  rw [hfiltercard, hprodcard, htotal, Nat.cast_mul,
    Nat.cast_mul, mul_div_mul_right _ _ hBne]

/-- Reindex a partial label assignment by `Fin Y.card` and regard each
label as an element of the full finite population. -/
def partialLabelsIidEquiv {α : Type*} (s : Finset α) (Y : Finset ↥s) :
    (↥Y → Fin s.card) ≃
      IidSample (Finset.univ : Finset (Fin s.card)) Y.card where
  toFun tau i := ⟨tau (Y.equivFin.symm i), Finset.mem_univ _⟩
  invFun omega y := (omega (Y.equivFin y)).1
  left_inv tau := by
    funext y
    simp
  right_inv omega := by
    funext i
    apply Subtype.ext
    simp

/-- Uniform probability is preserved by the partial-label/iid
reindexing.  This direct cardinal proof is insensitive to the concrete
`Fintype` implementations used for finite function spaces. -/
lemma partialLabels_probability_eq_iid {α : Type*}
    (s : Finset α) (Y : Finset ↥s)
    (Q : IidSample (Finset.univ : Finset (Fin s.card)) Y.card → Prop) :
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ Q (partialLabelsIidEquiv s Y tau)) =
      finsetProbability
        (Finset.univ : Finset
          (IidSample (Finset.univ : Finset (Fin s.card)) Y.card)) Q := by
  let E := partialLabelsIidEquiv s Y
  have hfiltercard :
      ((Finset.univ : Finset (↥Y → Fin s.card)).filter
        (fun tau ↦ Q (E tau))).card =
      ((Finset.univ : Finset
        (IidSample (Finset.univ : Finset (Fin s.card)) Y.card)).filter Q).card := by
    refine Finset.card_bij
      (s := (Finset.univ : Finset (↥Y → Fin s.card)).filter
        (fun tau ↦ Q (E tau)))
      (t := (Finset.univ : Finset
        (IidSample (Finset.univ : Finset (Fin s.card)) Y.card)).filter Q)
      (fun tau _ ↦ E tau) ?_ ?_ ?_
    · intro tau htau
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp htau).2⟩
    · intro tau₁ _ tau₂ _ heq
      exact E.injective heq
    · intro omega homega
      refine ⟨E.symm omega, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, E.apply_symm_apply omega⟩
      simpa only [E.apply_symm_apply] using (Finset.mem_filter.mp homega).2
  have htotal :
      (Finset.univ : Finset (↥Y → Fin s.card)).card =
        (Finset.univ : Finset
          (IidSample (Finset.univ : Finset (Fin s.card)) Y.card)).card := by
    simp only [Finset.card_univ]
    exact Fintype.card_congr E
  unfold finsetProbability
  rw [hfiltercard, htotal]

/-- Number of low labels in a partial label assignment, as a real-valued
sum in the form used by the iid Chernoff lemmas. -/
def partialLabelHitSum {α : Type*} (s : Finset α) (M : ℕ)
    (Y : Finset ↥s) (tau : ↥Y → Fin s.card) : ℝ :=
  ∑ y : ↥Y, if (tau y).1 < M then 1 else 0

/-- Indicator of the low-label block, expressed through the underlying
natural value so it is independent of finite-set membership instances. -/
def lowLabelIndicator (K M : ℕ) (i : Fin K) : ℝ :=
  if i.1 < M then 1 else 0

lemma iidSum_partialLabelsIidEquiv {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (tau : ↥Y → Fin s.card) :
    iidSum (lowLabelIndicator s.card M) Y.card
        (partialLabelsIidEquiv s Y tau) =
      partialLabelHitSum s M Y tau := by
  unfold iidSum partialLabelHitSum
  rw [← Y.equivFin.sum_comp]
  apply Finset.sum_congr rfl
  intro y hy
  simp [partialLabelsIidEquiv, lowLabelIndicator]

lemma partialLabelHitSum_upper_probability_eq_iid {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s) (k : ℝ) :
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ k ≤ partialLabelHitSum s M Y tau) =
      finsetProbability
        (Finset.univ : Finset
          (IidSample (Finset.univ : Finset (Fin s.card)) Y.card))
        (fun omega ↦ k ≤ iidSum (lowLabelIndicator s.card M)
          Y.card omega) := by
  calc
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ k ≤ partialLabelHitSum s M Y tau) =
      finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ k ≤ iidSum (lowLabelIndicator s.card M) Y.card
          (partialLabelsIidEquiv s Y tau)) := by
            apply finsetProbability_congr_event
            intro tau htau
            rw [iidSum_partialLabelsIidEquiv]
    _ = _ := partialLabels_probability_eq_iid s Y
      (fun omega : IidSample
          (Finset.univ : Finset (Fin s.card)) Y.card ↦
        k ≤ iidSum (lowLabelIndicator s.card M) Y.card omega)

lemma partialLabelHitSum_lower_probability_eq_iid {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s) (k : ℝ) :
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ partialLabelHitSum s M Y tau ≤ k) =
      finsetProbability
        (Finset.univ : Finset
          (IidSample (Finset.univ : Finset (Fin s.card)) Y.card))
        (fun omega ↦ iidSum (lowLabelIndicator s.card M)
          Y.card omega ≤ k) := by
  calc
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ partialLabelHitSum s M Y tau ≤ k) =
      finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ iidSum (lowLabelIndicator s.card M) Y.card
          (partialLabelsIidEquiv s Y tau) ≤ k) := by
            apply finsetProbability_congr_event
            intro tau htau
            rw [iidSum_partialLabelsIidEquiv]
    _ = _ := partialLabels_probability_eq_iid s Y
      (fun omega : IidSample
          (Finset.univ : Finset (Fin s.card)) Y.card ↦
        iidSum (lowLabelIndicator s.card M) Y.card omega ≤ k)

lemma iidLowLabels_upper_tail_exp_le
    (K M t : ℕ) (theta k : ℝ) (hK : 0 < K) (hM : M ≤ K)
    (htheta : 0 ≤ theta) :
    finsetProbability
        (Finset.univ : Finset
          (IidSample (Finset.univ : Finset (Fin K)) t))
        (fun omega ↦ k ≤ iidSum (lowLabelIndicator K M) t omega) ≤
      Real.exp ((t : ℝ) * ((M : ℝ) / K) *
        (Real.exp theta - 1) - theta * k) := by
  have hL : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  simpa [lowLabelIndicator, iidSum, card_lowLabels, min_eq_left hM,
      Finset.card_univ, Fintype.card_fin] using
    (iidHitCount_upper_tail_exp_le
      (Finset.univ : Finset (Fin K)) (lowLabels K M)
      (Finset.subset_univ _) t theta k hL htheta)

lemma iidLowLabels_lower_tail_exp_le
    (K M t : ℕ) (theta k : ℝ) (hK : 0 < K) (hM : M ≤ K)
    (htheta : 0 ≤ theta) :
    finsetProbability
        (Finset.univ : Finset
          (IidSample (Finset.univ : Finset (Fin K)) t))
        (fun omega ↦ iidSum (lowLabelIndicator K M) t omega ≤ k) ≤
      Real.exp ((t : ℝ) * ((M : ℝ) / K) *
        (Real.exp (-theta) - 1) + theta * k) := by
  have hL : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  simpa [lowLabelIndicator, iidSum, card_lowLabels, min_eq_left hM,
      Finset.card_univ, Fintype.card_fin] using
    (iidHitCount_lower_tail_exp_le
      (Finset.univ : Finset (Fin K)) (lowLabels K M)
      (Finset.subset_univ _) t theta k hL htheta)

/-- Upper Chernoff tail for the low-label count on a fixed coordinate
block. -/
lemma partialLabelHitSum_upper_tail_exp_le {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (theta k : ℝ) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ k ≤ partialLabelHitSum s M Y tau) ≤
      Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
        (Real.exp theta - 1) - theta * k) := by
  rw [partialLabelHitSum_upper_probability_eq_iid]
  exact iidLowLabels_upper_tail_exp_le s.card M Y.card theta k
    (Finset.card_pos.mpr hs) hM htheta

/-- Lower Chernoff tail for the low-label count on a fixed coordinate
block. -/
lemma partialLabelHitSum_lower_tail_exp_le {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (theta k : ℝ) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability (Finset.univ : Finset (↥Y → Fin s.card))
        (fun tau ↦ partialLabelHitSum s M Y tau ≤ k) ≤
      Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
        (Real.exp (-theta) - 1) + theta * k) := by
  rw [partialLabelHitSum_lower_probability_eq_iid]
  exact iidLowLabels_lower_tail_exp_le s.card M Y.card theta k
    (Finset.card_pos.mpr hs) hM htheta

/-- The partial low-label sum is exactly the cardinality of the selected
set inside the tested coordinate block. -/
lemma partialLabelHitSum_restrictLabels {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (omega : LabelSample s) :
    partialLabelHitSum s M Y (fun y ↦ omega y.1) =
      (((labelSelected s M omega) ∩ Y).card : ℝ) := by
  unfold partialLabelHitSum
  rw [← Finset.sum_subtype Y (fun _ ↦ Iff.rfl)
    (fun x ↦ if (omega x).1 < M then (1 : ℝ) else 0),
    Finset.sum_boole]
  norm_cast
  congr 1
  ext x
  simp [labelSelected, and_comm]

/-- Upper tail for label-selected hits in a fixed coordinate block. -/
lemma labelSelectedHit_upper_tail_exp_le {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (theta k : ℝ) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦ k ≤
          (((labelSelected s M omega) ∩ Y).card : ℝ)) ≤
      Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
        (Real.exp theta - 1) - theta * k) := by
  let Q : (↥Y → Fin s.card) → Prop := fun tau ↦
    k ≤ partialLabelHitSum s M Y tau
  calc
    finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦ k ≤
          (((labelSelected s M omega) ∩ Y).card : ℝ)) =
      finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦ Q (fun y ↦ omega y.1)) := by
          apply finsetProbability_congr_event
          intro omega homega
          dsimp only [Q]
          rw [partialLabelHitSum_restrictLabels]
    _ = finsetProbability (Finset.univ : Finset (↥Y → Fin s.card)) Q :=
      labelRestriction_probability_eq s M Y Q hs
    _ ≤ _ := partialLabelHitSum_upper_tail_exp_le
      s M Y theta k hs hM htheta

/-- Lower tail for label-selected hits in a fixed coordinate block. -/
lemma labelSelectedHit_lower_tail_exp_le {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (theta k : ℝ) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦
          (((labelSelected s M omega) ∩ Y).card : ℝ) ≤ k) ≤
      Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
        (Real.exp (-theta) - 1) + theta * k) := by
  let Q : (↥Y → Fin s.card) → Prop := fun tau ↦
    partialLabelHitSum s M Y tau ≤ k
  calc
    finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦
          (((labelSelected s M omega) ∩ Y).card : ℝ) ≤ k) =
      finsetProbability (Finset.univ : Finset (LabelSample s))
        (fun omega ↦ Q (fun y ↦ omega y.1)) := by
          apply finsetProbability_congr_event
          intro omega homega
          dsimp only [Q]
          rw [partialLabelHitSum_restrictLabels]
    _ = finsetProbability (Finset.univ : Finset (↥Y → Fin s.card)) Q :=
      labelRestriction_probability_eq s M Y Q hs
    _ ≤ _ := partialLabelHitSum_lower_tail_exp_le
      s M Y theta k hs hM htheta

/-- All-density Chernoff upper tail for a uniform `M`-subset. -/
lemma powersetCardHitCount_upper_tail_exp_le {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (theta k : ℝ) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ k ≤ ((H ∩ Y).card : ℝ)) ≤
      (s.card + 1 : ℝ) *
        Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp theta - 1) - theta * k) := by
  calc
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ k ≤ ((H ∩ Y).card : ℝ)) ≤
      (s.card + 1 : ℝ) *
        finsetProbability (Finset.univ : Finset (LabelSample s))
          (fun omega ↦ k ≤
            ((((labelSelected s M omega) ∩ Y).card : ℕ) : ℝ)) :=
      finsetProbability_powersetCard_le_labelSelected s M _ hM
    _ ≤ (s.card + 1 : ℝ) *
        Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp theta - 1) - theta * k) :=
      mul_le_mul_of_nonneg_left
        (labelSelectedHit_upper_tail_exp_le
          s M Y theta k hs hM htheta) (by positivity)

/-- All-density Chernoff lower tail for a uniform `M`-subset. -/
lemma powersetCardHitCount_lower_tail_exp_le {α : Type*}
    (s : Finset α) (M : ℕ) (Y : Finset ↥s)
    (theta k : ℝ) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ ((H ∩ Y).card : ℝ) ≤ k) ≤
      (s.card + 1 : ℝ) *
        Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp (-theta) - 1) + theta * k) := by
  calc
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ ((H ∩ Y).card : ℝ) ≤ k) ≤
      (s.card + 1 : ℝ) *
        finsetProbability (Finset.univ : Finset (LabelSample s))
          (fun omega ↦
            ((((labelSelected s M omega) ∩ Y).card : ℕ) : ℝ) ≤ k) :=
      finsetProbability_powersetCard_le_labelSelected s M _ hM
    _ ≤ (s.card + 1 : ℝ) *
        Real.exp ((Y.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp (-theta) - 1) + theta * k) :=
      mul_le_mul_of_nonneg_left
        (labelSelectedHit_lower_tail_exp_le
          s M Y theta k hs hM htheta) (by positivity)

/-! ### Transport back from subtype subsets -/

/-- Forget the membership proofs in a finite set of elements of `s`. -/
def finsetSubtypeVal {α : Type*} (s : Finset α) (H : Finset ↥s) :
    Finset α :=
  H.map ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩

@[simp] lemma card_finsetSubtypeVal {α : Type*}
    (s : Finset α) (H : Finset ↥s) :
    (finsetSubtypeVal s H).card = H.card := by
  simp [finsetSubtypeVal]

lemma finsetSubtypeVal_subset {α : Type*}
    (s : Finset α) (H : Finset ↥s) :
    finsetSubtypeVal s H ⊆ s := by
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact y.2

/-- Pull a subset of `s` back to the subtype `↥s`. -/
def finsetSubtypeOfSubset {α : Type*} (s G : Finset α) : Finset ↥s :=
  s.attach.filter fun x ↦ x.1 ∈ G

lemma finsetSubtypeVal_ofSubset {α : Type*}
    (s G : Finset α) (hG : G ⊆ s) :
    finsetSubtypeVal s (finsetSubtypeOfSubset s G) = G := by
  ext x
  simp only [finsetSubtypeVal, finsetSubtypeOfSubset, Finset.mem_map,
    Finset.mem_filter, Finset.mem_attach]
  constructor
  · rintro ⟨y, ⟨hy, hyG⟩, rfl⟩
    exact hyG
  · intro hxG
    exact ⟨⟨x, hG hxG⟩, ⟨trivial, hxG⟩, rfl⟩

/-- Uniform `M`-subsets of `s` are the same finite probability space as
uniform `M`-subsets of its subtype, after forgetting membership proofs. -/
lemma finsetProbability_powersetSubtypeVal {α : Type*}
    (s : Finset α) (M : ℕ) (P : Finset α → Prop) :
    finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ P (finsetSubtypeVal s H)) =
      finsetProbability (s.powersetCard M) P := by
  have hfiltercard :
      (((Finset.univ : Finset ↥s).powersetCard M).filter
        (fun H ↦ P (finsetSubtypeVal s H))).card =
      ((s.powersetCard M).filter P).card := by
    refine Finset.card_bij
      (s := ((Finset.univ : Finset ↥s).powersetCard M).filter
        (fun H ↦ P (finsetSubtypeVal s H)))
      (t := (s.powersetCard M).filter P)
      (fun H _ ↦ finsetSubtypeVal s H) ?_ ?_ ?_
    · intro H hH
      have hHp := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hH).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr
          ⟨finsetSubtypeVal_subset s H, by simpa using hHp.2⟩,
          (Finset.mem_filter.mp hH).2⟩
    · intro H₁ hH₁ H₂ hH₂ heq
      apply Finset.ext
      intro x
      have hxval : ∀ H : Finset ↥s,
          x ∈ H ↔ x.1 ∈ finsetSubtypeVal s H := by
        intro H
        simp only [finsetSubtypeVal, Finset.mem_map]
        constructor
        · exact fun hx ↦ ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, hval⟩
          have hxy : y = x := Subtype.ext hval
          simpa [hxy] using hy
      rw [hxval H₁, hxval H₂, heq]
    · intro G hG
      have hGp := Finset.mem_filter.mp hG
      have hGpow := Finset.mem_powersetCard.mp hGp.1
      let H := finsetSubtypeOfSubset s G
      have hval : finsetSubtypeVal s H = G :=
        finsetSubtypeVal_ofSubset s G hGpow.1
      have hHcard : H.card = M := by
        rw [← card_finsetSubtypeVal s H, hval, hGpow.2]
      have hHpow : H ∈ (Finset.univ : Finset ↥s).powersetCard M :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hHcard⟩
      exact ⟨H, Finset.mem_filter.mpr
        ⟨hHpow, hval ▸ hGp.2⟩, hval⟩
  unfold finsetProbability
  rw [hfiltercard, Finset.card_powersetCard,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_coe]

end

end Erdos747

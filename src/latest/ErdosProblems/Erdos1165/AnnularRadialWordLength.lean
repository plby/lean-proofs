/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialWordOfList
import ErdosProblems.Erdos1165.AnnularRadialProfileWords

/-!
# Length of an admissible radial word

For a nearest-neighbour label word starting at one and ending at zero, the
number of transitions is twice the total number of upward transitions plus
one.  This file records that exact identity and the resulting uniform cutoff
for a word carrying one constrained Appendix-A profile.
-/

open scoped BigOperators

namespace Erdos1165.AnnularRadialWordLength

open AppendixFirstMoment AnnularRadialLabelWord
  AnnularRadialProfileWords AnnularIntegratedProfileKernel

noncomputable section

/-- Number of upward steps in a finite radial-label list. -/
def radialListTotalUpSteps {n : ℕ} : List (Fin (n + 2)) → ℕ
  | source :: target :: tail =>
      (if source.val + 1 = target.val then 1 else 0) +
        radialListTotalUpSteps (target :: tail)
  | _ => 0

private theorem radialListUpcrossingCount_zero_of_chain {n : ℕ} :
    ∀ labels : List (Fin (n + 2)),
      labels.IsChain
          (fun left right ↦ Nat.dist left.val right.val = 1) →
        radialListUpcrossingCount 0 labels = 0
  | [], _ => rfl
  | [_], _ => rfl
  | source :: target :: tail, hchain => by
      have hparts := List.isChain_cons_cons.mp hchain
      rw [radialListUpcrossingCount]
      have hne : ¬ (source.val = 0 - 1 ∧ target.val = 0) := by
        rintro ⟨_, htarget⟩
        have hsource : source.val = 0 := by omega
        have : source = target := Fin.ext (by omega)
        subst target
        simp at hparts
      rw [if_neg hne, zero_add]
      exact radialListUpcrossingCount_zero_of_chain (target :: tail) hparts.2

private theorem sum_one_edge_upcrossingCount
    {n : ℕ} (source target : Fin (n + 2))
    (hadjacent : Nat.dist source.val target.val = 1) :
    ∑ k : Fin (n + 2),
        (if source.val = k.val - 1 ∧ target.val = k.val then 1 else 0) =
      if source.val + 1 = target.val then 1 else 0 := by
  by_cases hup : source.val + 1 = target.val
  · rw [if_pos hup, Finset.sum_eq_single target]
    · have htargetPos : 0 < target.val := by omega
      have hsource : source.val = target.val - 1 := by omega
      simp [hsource]
    · intro other _ hne
      by_cases hcondition :
          source.val = other.val - 1 ∧ target.val = other.val
      · exfalso
        apply hne
        exact Fin.ext hcondition.2.symm
      · simp [hcondition]
    · simp
  · rw [if_neg hup]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro hcondition
    by_cases hk : k.val = 0
    · have hsource : source.val = 0 := by omega
      have htarget : target.val = 0 := by omega
      have : source = target := Fin.ext (by omega)
      subst target
      simp at hadjacent
    · apply hup
      omega

private theorem sum_radialListUpcrossingCount_eq_totalUpSteps {n : ℕ} :
    ∀ labels : List (Fin (n + 2)),
      labels.IsChain
          (fun left right ↦ Nat.dist left.val right.val = 1) →
        (∑ k : Fin (n + 2),
          radialListUpcrossingCount k.val labels) =
          radialListTotalUpSteps labels
  | [], _ => by simp [radialListTotalUpSteps, radialListUpcrossingCount]
  | [_], _ => by simp [radialListTotalUpSteps, radialListUpcrossingCount]
  | source :: target :: tail, hchain => by
      have hparts := List.isChain_cons_cons.mp hchain
      simp only [radialListUpcrossingCount, radialListTotalUpSteps]
      rw [Finset.sum_add_distrib,
        sum_one_edge_upcrossingCount source target hparts.1,
        sum_radialListUpcrossingCount_eq_totalUpSteps (target :: tail) hparts.2]

private theorem transitionLength_add_last_eq_two_mul_upSteps_add_first {n : ℕ} :
    ∀ (first : Fin (n + 2)) (tail : List (Fin (n + 2))),
      (first :: tail).IsChain
          (fun left right ↦ Nat.dist left.val right.val = 1) →
      (first :: tail).length - 1 +
          ((first :: tail).getLast (by simp)).val =
        2 * radialListTotalUpSteps (first :: tail) + first.val
  | first, [], _ => by simp [radialListTotalUpSteps]
  | first, target :: tail, hchain => by
      have hparts := List.isChain_cons_cons.mp hchain
      have ih := transitionLength_add_last_eq_two_mul_upSteps_add_first
        target tail hparts.2
      have hcases : target.val = first.val + 1 ∨
          target.val + 1 = first.val := by
        unfold Nat.dist at hparts
        by_cases hle : first.val ≤ target.val
        · have : first.val - target.val = 0 := Nat.sub_eq_zero_of_le hle
          rw [this, zero_add] at hparts
          omega
        · have hle' : target.val ≤ first.val := by omega
          have : target.val - first.val = 0 := Nat.sub_eq_zero_of_le hle'
          rw [this, Nat.add_zero] at hparts
          omega
      rcases hcases with hup | hdown
      · have hlast :
            ((first :: target :: tail).getLast (by simp)).val =
              ((target :: tail).getLast (by simp)).val := by simp
        simp only [List.length_cons, Nat.add_sub_cancel,
          radialListTotalUpSteps, if_pos hup.symm]
        simp only [List.length_cons, Nat.add_sub_cancel] at ih
        rw [hlast]
        omega
      · have hnup : ¬ first.val + 1 = target.val := by omega
        have hlast :
            ((first :: target :: tail).getLast (by simp)).val =
              ((target :: tail).getLast (by simp)).val := by simp
        simp only [List.length_cons, Nat.add_sub_cancel,
          radialListTotalUpSteps, if_neg hnup]
        simp only [List.length_cons, Nat.add_sub_cancel] at ih
        rw [hlast]
        omega

private theorem transitionLength_add_last_eq_two_mul_upSteps_add_head
    {n : ℕ} (labels : List (Fin (n + 2))) (hne : labels ≠ [])
    (hchain : labels.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1)) :
    labels.length - 1 + (labels.getLast hne).val =
      2 * radialListTotalUpSteps labels + (labels.head hne).val := by
  obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  simpa using
    (transitionLength_add_last_eq_two_mul_upSteps_add_first first tail hchain)

/-- Exact transition-length identity for every admissible radial word. -/
theorem radialLabelWord_transitionLength_eq_two_mul_sum_upcrossings_add_one
    {n L : ℕ} (word : RadialLabelWord n L) :
    L = 2 * (∑ k : Fin (n + 2), radialUpcrossingCount word k) + 1 := by
  have hchain : word.toList.IsChain
      (fun left right ↦ Nat.dist left.val right.val = 1) := by
    rw [RadialLabelWord.toList, List.isChain_ofFn]
    intro i hi
    exact word.adjacent ⟨i, by omega⟩
  have hnonempty : word.toList ≠ [] := by
    rw [← List.length_pos_iff]
    simp
  have hfirst : word.toList.head hnonempty = ⟨1, by omega⟩ := by
    simpa [RadialLabelWord.toList, List.ofFn_succ] using word.startsAtOne
  have htotal := transitionLength_add_last_eq_two_mul_upSteps_add_head
    word.toList hnonempty hchain
  have hfirstVal := congrArg Fin.val hfirst
  have hlastVal : (word.toList.getLast hnonempty).val = 0 := by
    rw [List.getLast_eq_getElem]
    simp only [RadialLabelWord.toList, List.length_ofFn,
      List.getElem_ofFn, Nat.add_sub_cancel]
    have hindex : (⟨L, by omega⟩ : Fin (L + 1)) = Fin.last L :=
      Fin.ext rfl
    rw [hindex, word.endsAtZero]
  norm_num at hfirstVal
  rw [word.length_toList] at htotal
  have hsumList := sum_radialListUpcrossingCount_eq_totalUpSteps
    word.toList hchain
  have hsumWord : (∑ k : Fin (n + 2), radialUpcrossingCount word k) =
      radialListTotalUpSteps word.toList := by
    rw [← hsumList]
    apply Finset.sum_congr rfl
    intro k _
    unfold radialUpcrossingCount
    split_ifs with hk
    · rw [hk]
      symm
      exact radialListUpcrossingCount_zero_of_chain word.toList hchain
    · rfl
  rw [hsumWord]
  omega

private theorem radialListUpcrossingCount_one_eq_zero_of_nozero_sources
    {n : ℕ} : ∀ labels : List (Fin (n + 2)),
      (∀ i (hi : i + 1 < labels.length),
        (labels[i]'(by omega) : ℕ) ≠ 0) →
      radialListUpcrossingCount 1 labels = 0
  | [], _ => rfl
  | [_], _ => rfl
  | source :: target :: tail, hnonzero => by
      have hsource : source.val ≠ 0 := by
        simpa using hnonzero 0 (by simp)
      rw [radialListUpcrossingCount, if_neg]
      · rw [zero_add]
        apply radialListUpcrossingCount_one_eq_zero_of_nozero_sources
        intro i hi
        have h := hnonzero (i + 1) (by simpa using hi)
        simpa using h
      · rintro ⟨hsourceZero, _⟩
        exact hsource (by omega)

/-- A radial word cannot contain an upward `0 → 1` transition because its
only zero is the final label. -/
theorem radialUpcrossingCount_one_eq_zero
    {n L : ℕ} (word : RadialLabelWord n L) :
    radialUpcrossingCount word ⟨1, by omega⟩ = 0 := by
  unfold radialUpcrossingCount
  rw [dif_neg (by norm_num)]
  apply radialListUpcrossingCount_one_eq_zero_of_nozero_sources
  intro i hi
  have hiL : i < L := by
    rw [word.length_toList] at hi
    omega
  change ((List.ofFn word.level)[i]'(by simp; omega) : ℕ) ≠ 0
  rw [List.getElem_ofFn]
  exact word.beforeFinal_ne_zero ⟨i, hiL⟩

/-- A raw radial word carrying a constrained internal profile and a
successful terminal count automatically lies below the standard finite-word
cutoff.  This theorem is intentionally stated before bounded packaging. -/
theorem radialLabelWord_transitionLength_le_profileRadialWordMaxTransitions
    {n L : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (word : RadialLabelWord n L)
    (hinternal : ∀ i : Fin (n - 1),
      radialUpcrossingCount word
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i)
    (hterminal : radialUpcrossingCount word ⟨n + 1, by omega⟩ ≤ n ^ 3) :
    L ≤ profileRadialWordMaxTransitions n := by
  let f : Fin (n + 2) → ℕ := fun k ↦ radialUpcrossingCount word k
  let internal : Finset (Fin (n + 2)) :=
    Finset.univ.filter fun k ↦ 2 ≤ k.val ∧ k.val ≤ n
  let terminal : Fin (n + 2) := ⟨n + 1, by omega⟩
  have hterminalNotInternal : terminal ∉ internal := by
    simp [terminal, internal]
  have hinternalTerm : ∀ k ∈ internal, f k ≤ 3 * n ^ 2 := by
    intro k hk
    have hkrange : 2 ≤ k.val ∧ k.val ≤ n := by
      simpa [internal] using hk
    let i : Fin (n - 1) := ⟨k.val - 2, by omega⟩
    have hindex : (⟨scaleIndex i, by unfold scaleIndex; omega⟩ :
        Fin (n + 2)) = k := by
      apply Fin.ext
      dsimp only [i, scaleIndex]
      omega
    change radialUpcrossingCount word k ≤ 3 * n ^ 2
    rw [← hindex, hinternal i]
    exact constrainedProfile_entry_le_three_mul_n_sq hdelta hm i
  have hinternalSum : (∑ k ∈ internal, f k) ≤ 3 * n ^ 3 := by
    have hsum := Finset.sum_le_card_nsmul internal f (3 * n ^ 2)
      hinternalTerm
    have hcard : internal.card ≤ n := by
      let embed : {k // k ∈ internal} → Fin n := fun k ↦
        ⟨k.1.val - 2, by
          have hk := k.2
          simp only [internal, Finset.mem_filter, Finset.mem_univ,
            true_and] at hk
          omega⟩
      have hinjective : Function.Injective embed := by
        intro left right heq
        apply Subtype.ext
        apply Fin.ext
        have hval := congrArg Fin.val heq
        have hleft := left.2
        have hright := right.2
        simp only [embed, internal, Finset.mem_filter, Finset.mem_univ,
          true_and] at hval hleft hright
        omega
      simpa [embed] using Fintype.card_le_of_injective embed hinjective
    calc
      (∑ k ∈ internal, f k) ≤ internal.card • (3 * n ^ 2) := hsum
      _ ≤ n * (3 * n ^ 2) := by
        simpa [nsmul_eq_mul] using Nat.mul_le_mul_right (3 * n ^ 2) hcard
      _ = 3 * n ^ 3 := by ring
  have hsumSupport : (∑ k : Fin (n + 2), f k) =
      f terminal + ∑ k ∈ internal, f k := by
    have hsubset : insert terminal internal ⊆
        (Finset.univ : Finset (Fin (n + 2))) := by simp
    have hzero : ∀ k ∈ (Finset.univ : Finset (Fin (n + 2))),
        k ∉ insert terminal internal → f k = 0 := by
      intro k _ hkoutside
      have hkTerminal : k ≠ terminal := by
        intro heq
        apply hkoutside
        simp [heq]
      have hkInternal : k ∉ internal := by
        intro hmem
        apply hkoutside
        simp [hmem]
      have hksmall : k.val = 0 ∨ k.val = 1 := by
        by_contra hnot
        have hk2 : 2 ≤ k.val := by omega
        have hkn1 : k.val ≤ n + 1 := by omega
        have hkn : k.val ≤ n := by
          by_contra hnotLe
          have hknp1 : k.val = n + 1 := by omega
          apply hkTerminal
          exact Fin.ext hknp1
        apply hkInternal
        simp [internal, hk2, hkn]
      rcases hksmall with hk0 | hk1
      · have heq : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [heq]
        exact radialUpcrossingCount_zero word
      · have heq : k = ⟨1, by omega⟩ := Fin.ext hk1
        rw [heq]
        exact radialUpcrossingCount_one_eq_zero word
    have hsum := Finset.sum_subset (f := f) hsubset hzero
    rw [Finset.sum_insert hterminalNotInternal] at hsum
    simpa using hsum.symm
  have hsumBound : (∑ k : Fin (n + 2), f k) ≤ 4 * n ^ 3 := by
    rw [hsumSupport]
    have hterminal' : f terminal ≤ n ^ 3 := by
      exact hterminal
    omega
  rw [radialLabelWord_transitionLength_eq_two_mul_sum_upcrossings_add_one word]
  change 2 * (∑ k : Fin (n + 2), f k) + 1 ≤
    profileRadialWordMaxTransitions n
  unfold profileRadialWordMaxTransitions
  omega

/-- A raw radial word realizing one exact internal profile and a successful
terminal count lies below the profile-dependent cutoff.  No parabolic-window
assumption is used. -/
theorem radialLabelWord_transitionLength_le_exactProfileRadialWordMaxTransitions
    {n L : ℕ} (hn : 2 ≤ n) {m : Profile n}
    (word : RadialLabelWord n L)
    (hinternal : ∀ i : Fin (n - 1),
      radialUpcrossingCount word
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i)
    (hterminal : radialUpcrossingCount word ⟨n + 1, by omega⟩ ≤ n ^ 3) :
    L ≤ exactProfileRadialWordMaxTransitions m := by
  let f : Fin (n + 2) → ℕ := fun k ↦ radialUpcrossingCount word k
  let internal : Finset (Fin (n + 2)) :=
    Finset.univ.filter fun k ↦ 2 ≤ k.val ∧ k.val ≤ n
  let terminal : Fin (n + 2) := ⟨n + 1, by omega⟩
  have hterminalNotInternal : terminal ∉ internal := by
    simp [terminal, internal]
  let embed : Fin (n - 1) → Fin (n + 2) := fun i ↦
    ⟨scaleIndex i, by unfold scaleIndex; omega⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp only [embed, scaleIndex] at hval
    omega
  have hinternalImage : Finset.univ.image embed = internal := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      simp [internal, embed, scaleIndex]
      omega
    · intro hk
      have hkrange : 2 ≤ k.val ∧ k.val ≤ n := by
        simpa [internal] using hk
      let i : Fin (n - 1) := ⟨k.val - 2, by omega⟩
      refine ⟨i, ?_⟩
      apply Fin.ext
      dsimp only [embed, i, scaleIndex]
      omega
  have hinternalSum :
      (∑ k ∈ internal, f k) = (profileList m).sum := by
    rw [← hinternalImage, Finset.sum_image hembed.injOn]
    calc
      (∑ i : Fin (n - 1), f (embed i)) =
          ∑ i : Fin (n - 1), m i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hinternal i
      _ = (profileList m).sum := by
        simp only [profileList, List.sum_ofFn]
  have hsumSupport : (∑ k : Fin (n + 2), f k) =
      f terminal + ∑ k ∈ internal, f k := by
    have hsubset : insert terminal internal ⊆
        (Finset.univ : Finset (Fin (n + 2))) := by simp
    have hzero : ∀ k ∈ (Finset.univ : Finset (Fin (n + 2))),
        k ∉ insert terminal internal → f k = 0 := by
      intro k _ hkoutside
      have hkTerminal : k ≠ terminal := by
        intro heq
        apply hkoutside
        simp [heq]
      have hkInternal : k ∉ internal := by
        intro hmem
        apply hkoutside
        simp [hmem]
      have hksmall : k.val = 0 ∨ k.val = 1 := by
        by_contra hnot
        have hk2 : 2 ≤ k.val := by omega
        have hkn1 : k.val ≤ n + 1 := by omega
        have hkn : k.val ≤ n := by
          by_contra hnotLe
          have hknp1 : k.val = n + 1 := by omega
          apply hkTerminal
          exact Fin.ext hknp1
        apply hkInternal
        simp [internal, hk2, hkn]
      rcases hksmall with hk0 | hk1
      · have heq : k = ⟨0, by omega⟩ := Fin.ext hk0
        rw [heq]
        exact radialUpcrossingCount_zero word
      · have heq : k = ⟨1, by omega⟩ := Fin.ext hk1
        rw [heq]
        exact radialUpcrossingCount_one_eq_zero word
    have hsum := Finset.sum_subset (f := f) hsubset hzero
    rw [Finset.sum_insert hterminalNotInternal] at hsum
    simpa using hsum.symm
  have hsumBound : (∑ k : Fin (n + 2), f k) ≤
      (profileList m).sum + n ^ 3 := by
    rw [hsumSupport]
    rw [hinternalSum]
    have hterminal' : f terminal ≤ n ^ 3 := hterminal
    omega
  rw [radialLabelWord_transitionLength_eq_two_mul_sum_upcrossings_add_one word]
  change 2 * (∑ k : Fin (n + 2), f k) + 1 ≤
    exactProfileRadialWordMaxTransitions m
  unfold exactProfileRadialWordMaxTransitions
  omega

end

end Erdos1165.AnnularRadialWordLength

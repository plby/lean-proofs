import Mathlib

/-!
# Packing marked, perturbed centres

This file formalizes the deterministic greedy-packing lemma used in the
outer switching argument for Erdős Problem 636.  The cross-multiplied form
avoids choosing a convention for division by the spacing `s`.
-/

open scoped BigOperators

namespace Erdos636.MarkedPacking

/-- A finite set of indices is `R`-separated in the order of the indices if
each later centre is at least `R` above each earlier centre. -/
def SeparatedInOrder (x : ℕ → ℝ) (R : ℝ) (S : Finset ℕ) : Prop :=
  ∀ ⦃j⦄, j ∈ S → ∀ ⦃k⦄, k ∈ S → j < k → R ≤ x k - x j

lemma separatedInOrder_mono {x : ℕ → ℝ} {R : ℝ} {S T : Finset ℕ}
    (hS : SeparatedInOrder x R S) (hTS : T ⊆ S) :
    SeparatedInOrder x R T := by
  intro j hj k hk hjk
  exact hS (hTS hj) (hTS hk) hjk

/-- The real-valued cross-multiplied form of the marked packing lemma.

The perturbation charged between two indices is the sum over the
right-open/left-closed integer interval `(j,k]`.  The selected set is
pairwise `R`-separated in index order.  Its cardinality estimate is slightly
stronger than (4.4) in the accompanying write-up: there is no final `+s`
endpoint loss. -/
theorem exists_separated_subset_cross_mul
    (x r : ℕ → ℝ) (t : ℕ) {s R : ℝ}
    (hs : 0 < s) (hR : 0 < R)
    (hr : ∀ u ∈ Finset.Icc 1 t, 0 ≤ r u)
    (hgrowth : ∀ ⦃j k : ℕ⦄, j < k → k ≤ t →
      ((k - j : ℕ) : ℝ) * s - ∑ u ∈ Finset.Ioc j k, r u ≤ x k - x j)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (t + 1)) :
    ∃ J' : Finset ℕ,
      J' ⊆ J ∧ SeparatedInOrder x R J' ∧
        (J.card : ℝ) * s ≤
          (((⌈R / s⌉₊ + 2) * J'.card : ℕ) : ℝ) * s +
            ∑ u ∈ Finset.Icc 1 t, r u := by
  classical
  let A : ℕ := ⌈R / s⌉₊ + 2
  have hApos : 0 < A := by simp [A]
  have hceil : R ≤ (⌈R / s⌉₊ : ℝ) * s := by
    have hs0 : 0 ≤ s := hs.le
    have hratio : R / s ≤ (⌈R / s⌉₊ : ℝ) := Nat.le_ceil _
    calc
      R = (R / s) * s := by field_simp
      _ ≤ (⌈R / s⌉₊ : ℝ) * s := mul_le_mul_of_nonneg_right hratio hs0
  let P : Finset ℕ → Prop := fun M ↦
    ∀ a : ℕ, a ∈ M → (∀ u ∈ M, a ≤ u) → M ⊆ Finset.range (t + 1) →
      ∃ S : Finset ℕ,
        S ⊆ M ∧ a ∈ S ∧ SeparatedInOrder x R S ∧
          (M.card : ℝ) * s ≤
            ((A * S.card : ℕ) : ℝ) * s + ∑ u ∈ Finset.Ioc a t, r u
  have hP : ∀ M : Finset ℕ, P M := by
    intro M
    induction M using Finset.strongInductionOn with
    | _ M ih =>
      intro j hjM hjmin hM
      have hMne : M.Nonempty := ⟨j, hjM⟩
      have hjle : j ≤ t := by
        have := hM hjM
        simp only [Finset.mem_range] at this
        omega
      let K : Finset ℕ := M.filter fun k ↦ R ≤ x k - x j
      by_cases hK : K.Nonempty
      · let k : ℕ := K.min' hK
        have hkK : k ∈ K := Finset.min'_mem K hK
        have hkM : k ∈ M := (Finset.mem_filter.mp hkK).1
        have hksep : R ≤ x k - x j := (Finset.mem_filter.mp hkK).2
        have hjk : j < k := by
          have hjle' : j ≤ k := hjmin k hkM
          exact lt_of_le_of_ne hjle' fun hEq ↦ by
            rw [← hEq] at hksep
            simp at hksep
            linarith
        have hkle : k ≤ t := by
          have := hM hkM
          simp only [Finset.mem_range] at this
          omega
        let B : Finset ℕ := M.filter fun u ↦ u < k
        let T : Finset ℕ := M.filter fun u ↦ k ≤ u
        have hjB : j ∈ B := by simp [B, hjM, hjk]
        have hBne : B.Nonempty := ⟨j, hjB⟩
        have hkT : k ∈ T := by simp [T, hkM]
        have hTne : T.Nonempty := ⟨k, hkT⟩
        have hTM : T ⊆ M := fun u hu ↦ (Finset.mem_filter.mp hu).1
        have hTproper : T ⊂ M := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hTM, ?_⟩
          intro hEq
          have : j ∈ T := hEq ▸ hjM
          have := (Finset.mem_filter.mp this).2
          omega
        have hTrange : T ⊆ Finset.range (t + 1) := hTM.trans hM
        have hkmin : T.min' hTne = k := by
          apply Nat.le_antisymm
          · exact Finset.min'_le T k hkT
          · exact Finset.le_min' T hTne k fun u hu ↦ (Finset.mem_filter.mp hu).2
        obtain ⟨S, hST, hkS, hSsep, hScard⟩ :=
          ih T hTproper k hkT (fun u hu ↦ (Finset.mem_filter.mp hu).2) hTrange
        let v : ℕ := B.max' hBne
        have hvB : v ∈ B := Finset.max'_mem B hBne
        have hvM : v ∈ M := (Finset.mem_filter.mp hvB).1
        have hvk : v < k := (Finset.mem_filter.mp hvB).2
        have hjv : j ≤ v := Finset.le_max' B j hjB
        have hBsubset : B ⊆ Finset.Icc j v := by
          intro u hu
          exact Finset.mem_Icc.mpr
            ⟨hjmin u (Finset.mem_filter.mp hu).1, Finset.le_max' B u hu⟩
        have hBcard : B.card ≤ v - j + 1 := by
          calc
            B.card ≤ (Finset.Icc j v).card := Finset.card_le_card hBsubset
            _ = v - j + 1 := by rw [Nat.card_Icc]; omega
        have hvnotK : v ∉ K := by
          intro hvK
          have hkv : k ≤ v := Finset.min'_le K v hvK
          omega
        have hvnear : x v - x j < R := by
          have : ¬R ≤ x v - x j := by
            simpa [K, hvM] using hvnotK
          exact lt_of_not_ge this
        have hblock : (B.card : ℝ) * s ≤
            ((⌈R / s⌉₊ + 1 : ℕ) : ℝ) * s +
              ∑ u ∈ Finset.Ioc j v, r u := by
          have hcardcast : (B.card : ℝ) ≤ (v - j + 1 : ℕ) := by
            exact_mod_cast hBcard
          have hmulcard := mul_le_mul_of_nonneg_right hcardcast hs.le
          by_cases hjvEq : j = v
          · have hvj : v - j = 0 := by omega
            have hIoc : Finset.Ioc j v = ∅ := by rw [← hjvEq]; simp
            have : (B.card : ℝ) * s ≤ s := by
              simpa [hvj, Nat.cast_add, Nat.cast_one] using hmulcard
            have hceilnonneg : (0 : ℝ) ≤ (⌈R / s⌉₊ : ℝ) := by positivity
            rw [hIoc]
            simp only [Finset.sum_empty, add_zero]
            push_cast
            nlinarith
          · have hjvlt : j < v := lt_of_le_of_ne hjv hjvEq
            have hvle : v ≤ t := (Nat.le_of_lt hvk).trans hkle
            have hg := hgrowth hjvlt hvle
            have hmulcard' : (B.card : ℝ) * s ≤
                (((v - j : ℕ) : ℝ) + 1) * s := by
              simpa [Nat.cast_add, Nat.cast_one] using hmulcard
            push_cast
            nlinarith
        have hBTdisj : Disjoint B T := by
          refine Finset.disjoint_left.mpr ?_
          intro u huB huT
          have huB' := (Finset.mem_filter.mp huB).2
          have huT' := (Finset.mem_filter.mp huT).2
          omega
        have hMBT : M = B ∪ T := by
          ext u
          simp only [B, T, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hu
            by_cases huk : u < k
            · exact Or.inl ⟨hu, huk⟩
            · exact Or.inr ⟨hu, by omega⟩
          · exact fun h ↦ h.elim And.left And.left
        have hcardMBT : M.card = B.card + T.card := by
          rw [hMBT, Finset.card_union_of_disjoint hBTdisj]
        let S' : Finset ℕ := insert j S
        have hjnotS : j ∉ S := by
          intro hjS
          have hjT := hST hjS
          have := (Finset.mem_filter.mp hjT).2
          omega
        have hScard' : S'.card = S.card + 1 := by simp [S', hjnotS]
        have hS'M : S' ⊆ M := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | huS
          · exact hjM
          · exact hTM (hST huS)
        have hS'sep : SeparatedInOrder x R S' := by
          intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | haS
          · rcases Finset.mem_insert.mp hb with rfl | hbS
            · omega
            · have hbT := hST hbS
              have hkb : k ≤ b := (Finset.mem_filter.mp hbT).2
              by_cases hkbEq : k = b
              · simpa [hkbEq] using hksep
              · have hkbLt : k < b := lt_of_le_of_ne hkb hkbEq
                have htail : R ≤ x b - x k := hSsep hkS hbS hkbLt
                linarith
          · rcases Finset.mem_insert.mp hb with rfl | hbS
            · have haT := hST haS
              have hka : k ≤ a := (Finset.mem_filter.mp haT).2
              omega
            · exact hSsep haS hbS hab
        have herrSplit :
            (∑ u ∈ Finset.Ioc j v, r u) +
                (∑ u ∈ Finset.Ioc k t, r u) ≤
              ∑ u ∈ Finset.Ioc j t, r u := by
          let E : Finset ℕ := Finset.Ioc j v ∪ Finset.Ioc k t
          have hdisjE : Disjoint (Finset.Ioc j v) (Finset.Ioc k t) := by
            refine Finset.disjoint_left.mpr ?_
            simp only [Finset.mem_Ioc]
            omega
          have hEsub : E ⊆ Finset.Ioc j t := by
            intro u hu
            rcases Finset.mem_union.mp hu with hu | hu
            · have huv := Finset.mem_Ioc.mp hu
              exact Finset.mem_Ioc.mpr ⟨huv.1, huv.2.trans (Nat.le_of_lt hvk) |>.trans hkle⟩
            · have hut := Finset.mem_Ioc.mp hu
              exact Finset.mem_Ioc.mpr ⟨hjk.trans hut.1, hut.2⟩
          rw [← Finset.sum_union hdisjE]
          exact Finset.sum_le_sum_of_subset_of_nonneg hEsub fun u hu _ ↦ by
            apply hr u
            have hu' := Finset.mem_Ioc.mp hu
            exact Finset.mem_Icc.mpr ⟨by omega, hu'.2⟩
        refine ⟨S', hS'M, ?_, hS'sep, ?_⟩
        · simp [S']
        · rw [hcardMBT, Nat.cast_add, add_mul, hScard']
          have hcoef : ((A * (S.card + 1) : ℕ) : ℝ) =
              ((⌈R / s⌉₊ + 1 : ℕ) : ℝ) + ((A * S.card : ℕ) : ℝ) + 1 := by
            simp [A, Nat.mul_add]
            ring
          rw [hcoef]
          nlinarith
      · let S : Finset ℕ := {j}
        have hSM : S ⊆ M := by simpa [S] using hjM
        have hSsep : SeparatedInOrder x R S := by
          intro a ha b hb hab
          simp only [S, Finset.mem_singleton] at ha hb
          omega
        let v : ℕ := M.max' hMne
        have hvM : v ∈ M := Finset.max'_mem M hMne
        have hjv : j ≤ v := hjmin v hvM
        have hMsub : M ⊆ Finset.Icc j v := by
          intro u hu
          exact Finset.mem_Icc.mpr ⟨hjmin u hu, Finset.le_max' M u hu⟩
        have hMcard : M.card ≤ v - j + 1 := by
          calc
            M.card ≤ (Finset.Icc j v).card := Finset.card_le_card hMsub
            _ = v - j + 1 := by rw [Nat.card_Icc]; omega
        have hvnear : x v - x j < R := by
          have hvnot : v ∉ K := fun hvK ↦ hK ⟨v, hvK⟩
          have : ¬R ≤ x v - x j := by simpa [K, hvM] using hvnot
          exact lt_of_not_ge this
        have hblock : (M.card : ℝ) * s ≤
            ((⌈R / s⌉₊ + 1 : ℕ) : ℝ) * s +
              ∑ u ∈ Finset.Ioc j v, r u := by
          have hcardcast : (M.card : ℝ) ≤ (v - j + 1 : ℕ) := by
            exact_mod_cast hMcard
          have hmulcard := mul_le_mul_of_nonneg_right hcardcast hs.le
          by_cases hjvEq : j = v
          · have hvj : v - j = 0 := by omega
            have hIoc : Finset.Ioc j v = ∅ := by rw [← hjvEq]; simp
            have : (M.card : ℝ) * s ≤ s := by
              simpa [hvj, Nat.cast_add, Nat.cast_one] using hmulcard
            have hceilnonneg : (0 : ℝ) ≤ (⌈R / s⌉₊ : ℝ) := by positivity
            rw [hIoc]
            simp only [Finset.sum_empty, add_zero]
            push_cast
            nlinarith
          · have hjvlt : j < v := lt_of_le_of_ne hjv hjvEq
            have hg := hgrowth hjvlt (by
              have := hM hvM
              simp only [Finset.mem_range] at this
              omega)
            have hmulcard' : (M.card : ℝ) * s ≤
                (((v - j : ℕ) : ℝ) + 1) * s := by
              simpa [Nat.cast_add, Nat.cast_one] using hmulcard
            push_cast
            nlinarith
        have herrSub : (∑ u ∈ Finset.Ioc j v, r u) ≤
            ∑ u ∈ Finset.Ioc j t, r u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            have huv := Finset.mem_Ioc.mp hu
            exact Finset.mem_Ioc.mpr ⟨huv.1, huv.2.trans (by
              have := hM hvM
              simp only [Finset.mem_range] at this
              omega)⟩
          · intro u hu _
            apply hr u
            have hu' := Finset.mem_Ioc.mp hu
            exact Finset.mem_Icc.mpr ⟨by omega, hu'.2⟩
        refine ⟨S, hSM, ?_, hSsep, ?_⟩
        · simp [S]
        · have hcoef : (⌈R / s⌉₊ + 1 : ℕ) ≤ A := by simp [A]
          have hcoefReal : ((⌈R / s⌉₊ + 1 : ℕ) : ℝ) * s ≤ (A : ℝ) * s := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcoef) hs.le
          have hScardone : S.card = 1 := by simp [S]
          rw [hScardone, Nat.mul_one]
          exact hblock.trans (add_le_add hcoefReal herrSub)
  by_cases hJne : J.Nonempty
  · let j : ℕ := J.min' hJne
    have hjJ : j ∈ J := Finset.min'_mem J hJne
    have hjmin : ∀ u ∈ J, j ≤ u := fun u hu ↦ Finset.min'_le J u hu
    obtain ⟨J', hJ'J, _, hsep, hcard⟩ := hP J j hjJ hjmin hJ
    refine ⟨J', hJ'J, hsep, ?_⟩
    have hErrSub : (∑ u ∈ Finset.Ioc j t, r u) ≤
        ∑ u ∈ Finset.Icc 1 t, r u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        have hu' := Finset.mem_Ioc.mp hu
        exact Finset.mem_Icc.mpr ⟨by omega, hu'.2⟩
      · intro u hu _
        exact hr u hu
    have hraise : ((A * J'.card : ℕ) : ℝ) * s +
          ∑ u ∈ Finset.Ioc j t, r u ≤
        ((A * J'.card : ℕ) : ℝ) * s + ∑ u ∈ Finset.Icc 1 t, r u := by
      simpa [add_comm] using
        (add_le_add_left hErrSub (((A * J'.card : ℕ) : ℝ) * s))
    have hcard' := hcard.trans hraise
    simpa [A, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, add_comm] using hcard'
  · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJne
    subst J
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · intro j hj
      simp at hj
    · norm_num
      exact Finset.sum_nonneg fun u hu ↦ hr u hu

/-- Integer-budget form of the packing estimate.  If the total perturbation
is at most `e * s`, then the cardinality inequality is entirely in `ℕ`.
This is the natural-number cross-multiplication used by the outer assembly. -/
theorem exists_separated_subset_nat_budget
    (x r : ℕ → ℝ) (t e : ℕ) {s R : ℝ}
    (hs : 0 < s) (hR : 0 < R)
    (hr : ∀ u ∈ Finset.Icc 1 t, 0 ≤ r u)
    (hgrowth : ∀ ⦃j k : ℕ⦄, j < k → k ≤ t →
      ((k - j : ℕ) : ℝ) * s - ∑ u ∈ Finset.Ioc j k, r u ≤ x k - x j)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (t + 1))
    (herror : (∑ u ∈ Finset.Icc 1 t, r u) ≤ (e : ℝ) * s) :
    ∃ J' : Finset ℕ,
      J' ⊆ J ∧ SeparatedInOrder x R J' ∧
        J.card ≤ (⌈R / s⌉₊ + 2) * J'.card + e := by
  obtain ⟨J', hJ'J, hsep, hpack⟩ :=
    exists_separated_subset_cross_mul x r t hs hR hr hgrowth J hJ
  refine ⟨J', hJ'J, hsep, ?_⟩
  have hscaled : (J.card : ℝ) * s ≤
      ((((⌈R / s⌉₊ + 2) * J'.card + e : ℕ) : ℝ)) * s := by
    calc
      (J.card : ℝ) * s ≤
          (((⌈R / s⌉₊ + 2) * J'.card : ℕ) : ℝ) * s +
            ∑ u ∈ Finset.Icc 1 t, r u := hpack
      _ ≤ (((⌈R / s⌉₊ + 2) * J'.card : ℕ) : ℝ) * s + (e : ℝ) * s :=
        by simpa [add_comm] using
          (add_le_add_left herror
            ((((⌈R / s⌉₊ + 2) * J'.card : ℕ) : ℝ) * s))
      _ = ((((⌈R / s⌉₊ + 2) * J'.card + e : ℕ) : ℝ)) * s := by
        push_cast
        ring
  have hreal : (J.card : ℝ) ≤
      (((⌈R / s⌉₊ + 2) * J'.card + e : ℕ) : ℝ) :=
    le_of_mul_le_mul_right hscaled hs
  exact_mod_cast hreal

/-- Explicit positive-linear consequence of
`exists_separated_subset_cross_mul`.  If at least `θ t` indices are marked
and the total perturbation costs at most half of `θ t s`, the greedy packing
retains at least `θ t / (2 (⌈R/s⌉₊+2))` indices. -/
theorem exists_separated_subset_linear
    (x r : ℕ → ℝ) (t : ℕ) {s R θ : ℝ}
    (hs : 0 < s) (hR : 0 < R) (_hθ : 0 < θ)
    (hr : ∀ u ∈ Finset.Icc 1 t, 0 ≤ r u)
    (hgrowth : ∀ ⦃j k : ℕ⦄, j < k → k ≤ t →
      ((k - j : ℕ) : ℝ) * s - ∑ u ∈ Finset.Ioc j k, r u ≤ x k - x j)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (t + 1))
    (hmarked : θ * t ≤ (J.card : ℝ))
    (herror : (∑ u ∈ Finset.Icc 1 t, r u) ≤ θ / 2 * t * s) :
    ∃ J' : Finset ℕ,
      J' ⊆ J ∧ SeparatedInOrder x R J' ∧
        θ / (2 * (⌈R / s⌉₊ + 2 : ℕ)) * t ≤ (J'.card : ℝ) := by
  obtain ⟨J', hJ'J, hsep, hpack⟩ :=
    exists_separated_subset_cross_mul x r t hs hR hr hgrowth J hJ
  refine ⟨J', hJ'J, hsep, ?_⟩
  let A : ℝ := (⌈R / s⌉₊ + 2 : ℕ)
  have hA : 0 < A := by positivity
  have hmarkScaled : θ * t * s ≤ (J.card : ℝ) * s :=
    mul_le_mul_of_nonneg_right hmarked hs.le
  have hhalfScaled : θ / 2 * t * s ≤ A * (J'.card : ℝ) * s := by
    have hpack' : (J.card : ℝ) * s ≤
        A * (J'.card : ℝ) * s + ∑ u ∈ Finset.Icc 1 t, r u := by
      simpa [A, Nat.cast_mul] using hpack
    nlinarith
  have hhalf : θ / 2 * t ≤ A * (J'.card : ℝ) := by
    apply le_of_mul_le_mul_right (a := s) _ hs
    simpa [mul_assoc] using hhalfScaled
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by norm_num) hA)]
  dsimp [A] at hhalf ⊢
  nlinarith

end Erdos636.MarkedPacking

import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Maximal consecutive runs in a finite set of natural numbers -/

namespace Erdos1148.DukeArithmetic

theorem exists_maximal_nat_run (V : Finset ℕ) {v : ℕ} (hv : v ∈ V) :
    ∃ a b : ℕ, a ≤ v ∧ v ≤ b ∧ Finset.Icc a b ⊆ V ∧
      (a = 0 ∨ a - 1 ∉ V) ∧ b + 1 ∉ V := by
  classical
  let A := (Finset.Icc 0 v).filter (fun a => Finset.Icc a v ⊆ V)
  have hA : A.Nonempty := by
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩, ?_⟩⟩
    intro k hk
    have heq : k = v := by have := Finset.mem_Icc.mp hk; omega
    simpa only [heq] using hv
  let a := A.min' hA
  have ha := Finset.mem_filter.mp (A.min'_mem hA)
  have hav : a ≤ v := (Finset.mem_Icc.mp ha.1).2
  have hal : a = 0 ∨ a - 1 ∉ V := by
    by_cases haz : a = 0
    · exact Or.inl haz
    · right
      intro hprev
      have hamem : a - 1 ∈ A := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, ?_⟩
        intro k hk
        have hki := Finset.mem_Icc.mp hk
        by_cases hka : k < a
        · have heq : k = a - 1 := by omega
          rwa [heq]
        · exact ha.2 (Finset.mem_Icc.mpr ⟨by omega, hki.2⟩)
      have hmin : a ≤ a - 1 := A.min'_le _ hamem
      omega
  let B := V.filter (fun b => v ≤ b ∧ Finset.Icc v b ⊆ V)
  have hB : B.Nonempty := by
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, le_rfl, ?_⟩⟩
    intro k hk
    have heq : k = v := by have := Finset.mem_Icc.mp hk; omega
    simpa only [heq] using hv
  let b := B.max' hB
  have hb := Finset.mem_filter.mp (B.max'_mem hB)
  have hvb : v ≤ b := hb.2.1
  have hbr : b + 1 ∉ V := by
    intro hnext
    have hbmem : b + 1 ∈ B := by
      apply Finset.mem_filter.mpr
      refine ⟨hnext, by omega, ?_⟩
      intro k hk
      have hki := Finset.mem_Icc.mp hk
      by_cases hkb : k ≤ b
      · exact hb.2.2 (Finset.mem_Icc.mpr ⟨hki.1, hkb⟩)
      · have heq : k = b + 1 := by omega
        rwa [heq]
    have hmax : b + 1 ≤ b := B.le_max' _ hbmem
    omega
  refine ⟨a, b, hav, hvb, ?_, hal, hbr⟩
  intro k hk
  have hki := Finset.mem_Icc.mp hk
  by_cases hkv : k ≤ v
  · exact ha.2 (Finset.mem_Icc.mpr ⟨hki.1, hkv⟩)
  · exact hb.2.2 (Finset.mem_Icc.mpr ⟨by omega, hki.2⟩)

def maximalNatRuns (V : Finset ℕ) : Finset (ℕ × ℕ) :=
  (V ×ˢ V).filter (fun p => p.1 ≤ p.2 ∧ Finset.Icc p.1 p.2 ⊆ V ∧
    (p.1 = 0 ∨ p.1 - 1 ∉ V) ∧ p.2 + 1 ∉ V)

lemma mem_maximalNatRuns_iff (V : Finset ℕ) (p : ℕ × ℕ) :
    p ∈ maximalNatRuns V ↔ p.1 ≤ p.2 ∧ Finset.Icc p.1 p.2 ⊆ V ∧
      (p.1 = 0 ∨ p.1 - 1 ∉ V) ∧ p.2 + 1 ∉ V := by
  rw [maximalNatRuns, Finset.mem_filter, Finset.mem_product]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨h.2.1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩),
      h.2.1 (Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩)⟩, h⟩

theorem biUnion_maximalNatRuns (V : Finset ℕ) :
    (maximalNatRuns V).biUnion (fun p => Finset.Icc p.1 p.2) = V := by
  classical
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hv⟩
    exact ((mem_maximalNatRuns_iff V p).mp hp).2.1 hv
  · intro hv
    obtain ⟨a, b, hav, hvb, hsub, hleft, hright⟩ := exists_maximal_nat_run V hv
    exact ⟨(a, b), (mem_maximalNatRuns_iff V (a, b)).mpr
      ⟨hav.trans hvb, hsub, hleft, hright⟩, Finset.mem_Icc.mpr ⟨hav, hvb⟩⟩

theorem maximalNatRuns_end_lt_start {V : Finset ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ maximalNatRuns V) (hq : q ∈ maximalNatRuns V) (hpq : p.1 < q.1) :
    p.2 < q.1 := by
  have hp' := (mem_maximalNatRuns_iff V p).mp hp
  have hq' := (mem_maximalNatRuns_iff V q).mp hq
  by_contra h
  have hprev : q.1 - 1 ∈ V := hp'.2.1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rcases hq'.2.2.1 with hzero | hnot
  · omega
  · exact hnot hprev

theorem maximalNatRuns_fst_injOn (V : Finset ℕ) :
    Set.InjOn Prod.fst (maximalNatRuns V : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  have hp' := (mem_maximalNatRuns_iff V p).mp hp
  have hq' := (mem_maximalNatRuns_iff V q).mp hq
  apply Prod.ext heq
  apply le_antisymm
  · by_contra h
    have hmem : q.2 + 1 ∈ V := hp'.2.1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact hq'.2.2.2 hmem
  · by_contra h
    have hmem : p.2 + 1 ∈ V := hq'.2.1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact hp'.2.2.2 hmem

theorem maximalNatRuns_pairwise_disjoint (V : Finset ℕ) :
    (maximalNatRuns V : Set (ℕ × ℕ)).PairwiseDisjoint (fun p => Finset.Icc p.1 p.2) := by
  intro p hp q hq hne
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  have hvp' := Finset.mem_Icc.mp hvp
  have hvq' := Finset.mem_Icc.mp hvq
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · have := maximalNatRuns_end_lt_start hp hq hlt
    omega
  · exact hne (maximalNatRuns_fst_injOn V hp hq heq)
  · have := maximalNatRuns_end_lt_start hq hp hgt
    omega

theorem card_eq_sum_maximalNatRuns (V : Finset ℕ) :
    V.card = ∑ p ∈ maximalNatRuns V, (p.2 + 1 - p.1) := by
  calc
    _ = ((maximalNatRuns V).biUnion (fun p => Finset.Icc p.1 p.2)).card :=
      congrArg Finset.card (biUnion_maximalNatRuns V).symm
    _ = ∑ p ∈ maximalNatRuns V, (Finset.Icc p.1 p.2).card :=
      Finset.card_biUnion (maximalNatRuns_pairwise_disjoint V)
    _ = _ := by simp only [Nat.card_Icc]

theorem sum_maximalNatRuns_duration_add_card (V : Finset ℕ) :
    (∑ p ∈ maximalNatRuns V, (p.2 - p.1)) + (maximalNatRuns V).card = V.card := by
  calc
    _ = ∑ p ∈ maximalNatRuns V, ((p.2 - p.1) + 1) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ p ∈ maximalNatRuns V, (p.2 + 1 - p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hle := ((mem_maximalNatRuns_iff V p).mp hp).1
      omega
    _ = V.card := (card_eq_sum_maximalNatRuns V).symm

theorem sum_long_maximalNatRuns_duration (V : Finset ℕ) :
    (∑ p ∈ (maximalNatRuns V).filter (fun p => p.1 < p.2), (p.2 - p.1)) +
      (maximalNatRuns V).card = V.card := by
  have heq : (∑ p ∈ (maximalNatRuns V).filter (fun p => p.1 < p.2), (p.2 - p.1)) =
      ∑ p ∈ maximalNatRuns V, (p.2 - p.1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h
    · rfl
    · omega
  rw [heq]
  exact sum_maximalNatRuns_duration_add_card V

end Erdos1148.DukeArithmetic

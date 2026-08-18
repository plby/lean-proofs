import ErdosProblems.Erdos1161.CycleBounds
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Concrete

open scoped BigOperators
open Equiv

namespace Erdos1161

noncomputable def liftFinPerm {n : ℕ} (e : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  e.extendDomain (Equiv.ofInjective
    (⟨Fin.succ, Fin.succ_injective n⟩ : Fin n ↪ Fin (n + 1)).1
    (⟨Fin.succ, Fin.succ_injective n⟩ : Fin n ↪ Fin (n + 1)).2)

@[simp] theorem liftFinPerm_zero {n : ℕ} (e : Perm (Fin n)) :
  liftFinPerm e 0 = 0 := by
  rw [liftFinPerm, Perm.extendDomain_apply_not_subtype]
  simp

@[simp] theorem liftFinPerm_succ {n : ℕ} (e : Perm (Fin n)) (x : Fin n) :
    liftFinPerm e x.succ = (e x).succ := by
  exact Perm.extendDomain_apply_image e _ x

theorem cycleType_liftFinPerm {n : ℕ} (e : Perm (Fin n)) :
    (liftFinPerm e).cycleType = e.cycleType := by
  unfold liftFinPerm
  rw [Perm.cycleType_extendDomain]

theorem decomposeFin_symm_eq {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.decomposeFin.symm (p, e) = swap 0 p * liftFinPerm e := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp
  · simp

theorem isCycle_swap_mul_of_mem_support_of_not_mem_support
    {α : Type*} [Fintype α] [DecidableEq α] {c : Perm α} (hc : c.IsCycle)
    {x q : α} (hq : q ∈ c.support) (hx : x ∉ c.support) :
    (swap x q * c).IsCycle := by
  let l := c.toList q
  have hl2 : 2 ≤ l.length := by
    simpa [l] using
      (Perm.two_le_length_toList_iff_mem_support (p := c) (x := q)).mpr hq
  have hlnodup : l.Nodup := by
    simpa [l] using Perm.nodup_toList c q
  have hxl : x ∉ l := by
    intro hmem
    have hsc : c.SameCycle q x := (Perm.mem_toList_iff.mp hmem).1
    have hfixed : c q = q ↔ c x = x := hsc.apply_eq_self_iff
    exact (Perm.mem_support.mp hq) (hfixed.mpr (Perm.notMem_support.mp hx))
  have hform : l.formPerm = c := by
    change (c.toList q).formPerm = c
    rw [Perm.formPerm_toList, hc.cycleOf_eq (Perm.mem_support.mp hq)]
  have hlne : l ≠ [] := by
    intro h
    simp [h] at hl2
  obtain ⟨a, t, hlt⟩ := List.exists_cons_of_ne_nil hlne
  have haq : a = q := by
    have hfirst := Perm.toList_getElem_zero c q hq
    change l[0]'_ = q at hfirst
    simp only [hlt, List.getElem_cons_zero] at hfirst
    exact hfirst
  subst a
  rw [← hform, hlt, ← List.formPerm_cons_cons]
  exact List.isCycle_formPerm (by simpa [hlt] using hlnodup.cons hxl)
    (by simpa [hlt] using Nat.succ_le_succ hl2)

theorem card_support_swap_mul_of_mem_support_of_not_mem_support
    {α : Type*} [Fintype α] [DecidableEq α] {c : Perm α} (hc : c.IsCycle)
    {x q : α} (hq : q ∈ c.support) (hx : x ∉ c.support) :
    (swap x q * c).support.card = c.support.card + 1 := by
  let l := c.toList q
  have hlnodup : l.Nodup := by simpa [l] using Perm.nodup_toList c q
  have hxl : x ∉ l := by
    intro hmem
    have hsc : c.SameCycle q x := (Perm.mem_toList_iff.mp hmem).1
    have hfixed : c q = q ↔ c x = x := hsc.apply_eq_self_iff
    exact (Perm.mem_support.mp hq) (hfixed.mpr (Perm.notMem_support.mp hx))
  have hl2 : 2 ≤ l.length := by
    simpa [l] using
      (Perm.two_le_length_toList_iff_mem_support (p := c) (x := q)).mpr hq
  have hlne : l ≠ [] := by
    intro h
    simp [h] at hl2
  have hform : l.formPerm = c := by
    change (c.toList q).formPerm = c
    rw [Perm.formPerm_toList, hc.cycleOf_eq (Perm.mem_support.mp hq)]
  obtain ⟨a, t, hlt⟩ := List.exists_cons_of_ne_nil hlne
  have haq : a = q := by
    have hfirst := Perm.toList_getElem_zero c q hq
    change l[0]'_ = q at hfirst
    simpa only [hlt, List.getElem_cons_zero] using hfirst
  subst a
  have heq : swap x q * c = (x :: l).formPerm := by
    rw [hlt, List.formPerm_cons_cons]
    rw [← hlt, hform]
  rw [heq, List.support_formPerm_of_nodup (x :: l) (hlnodup.cons hxl)]
  · rw [List.card_toFinset, List.dedup_eq_self.mpr (hlnodup.cons hxl)]
    simp [l, Perm.length_toList, hc.cycleOf_eq (Perm.mem_support.mp hq)]
  · intro y hy
    have hlen := congrArg List.length hy
    have hzero : l.length = 0 := by simpa using hlen
    omega

@[simp] theorem totalCycleCount_eq {n : ℕ} (e : Perm (Fin n)) :
    Erdos1161.totalCycleCount e = e.cycleType.card + (n - e.cycleType.sum) := by
  simp [Erdos1161.totalCycleCount, Erdos1161.fullCycleType,
    Erdos1161.fixedPointCount_eq]

theorem totalCycleCount_eq_card_sub_support {n : ℕ} (e : Perm (Fin n)) :
    Erdos1161.totalCycleCount e = e.cycleType.card + (n - e.support.card) := by
  rw [totalCycleCount_eq, e.sum_cycleType]

theorem totalCycleCount_liftFinPerm {n : ℕ} (e : Perm (Fin n)) :
    Erdos1161.totalCycleCount (liftFinPerm e) = Erdos1161.totalCycleCount e + 1 := by
  rw [totalCycleCount_eq, totalCycleCount_eq, cycleType_liftFinPerm]
  have hsum : e.cycleType.sum ≤ n := by simpa using e.sum_cycleType_le
  omega

theorem totalCycleCount_decomposeFin_symm {n : ℕ} (p : Fin (n + 1))
    (e : Perm (Fin n)) :
    Erdos1161.totalCycleCount (Perm.decomposeFin.symm (p, e)) =
      if p = 0 then Erdos1161.totalCycleCount e + 1
      else Erdos1161.totalCycleCount e := by
  rw [decomposeFin_symm_eq]
  by_cases hp0 : p = 0
  · subst p
    rw [if_pos rfl]
    rw [show swap (0 : Fin (n + 1)) 0 = 1 by
      ext x
      simp [Perm.one_def], one_mul]
    simpa using totalCycleCount_liftFinPerm e
  · rw [if_neg hp0]
    obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero hp0
    let f := liftFinPerm e
    let p : Fin (n + 1) := a.succ
    have hp0' : p ≠ 0 := Fin.succ_ne_zero a
    have hf0 : f 0 = 0 := liftFinPerm_zero e
    by_cases ha : e a = a
    · have hfp : f p = p := by simp [f, p, ha]
      have hd : Perm.Disjoint (swap 0 p) f := by
        intro y
        by_cases hy0 : y = 0
        · exact Or.inr (by simpa [hy0] using hf0)
        by_cases hyp : y = p
        · exact Or.inr (by simpa [hyp] using hfp)
        exact Or.inl (swap_apply_of_ne_of_ne hy0 hyp)
      have hswapcycle : (swap 0 p).IsCycle := Perm.isCycle_swap hp0'.symm
      have hswapcard : (swap 0 p).support.card = 2 :=
        Perm.card_support_swap hp0'.symm
      rw [totalCycleCount_eq_card_sub_support,
        totalCycleCount_eq_card_sub_support, hd.cycleType_mul, hd.card_support_mul,
        hswapcycle.cycleType, hswapcard]
      rw [cycleType_liftFinPerm]
      have hesupp : e.support.card < n := by
        calc
          e.support.card < (Finset.univ : Finset (Fin n)).card := by
            apply Finset.card_lt_card
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨Finset.subset_univ _, ?_⟩
            intro heq
            have hamem : a ∈ e.support := by rw [heq]; simp
            exact (Perm.notMem_support.mpr ha) hamem
          _ = n := by simp
      have hfsupp : f.support.card = e.support.card := by
        rw [← f.sum_cycleType, ← e.sum_cycleType, cycleType_liftFinPerm]
      simp only [Multiset.card_add, Multiset.card_singleton]
      omega
    · have hpmem : p ∈ f.support := by
        rw [Perm.mem_support]
        simpa [f, p] using ha
      let c := f.cycleOf p
      let r := f * c⁻¹
      have hc : c.IsCycle := Perm.isCycle_cycleOf f (Perm.mem_support.mp hpmem)
      have hcmem : c ∈ f.cycleFactorsFinset := by
        exact Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hpmem
      have hdrc : Perm.Disjoint r c := by
        exact Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hcmem
      have hrc : r * c = f := by simp [r]
      have hcr : c * r = f := (hdrc.commute.eq.symm).trans hrc
      have h0notc : 0 ∉ c.support := by
        intro hmem
        exact (Perm.notMem_support.mpr hf0)
          (Perm.mem_cycleFactorsFinset_support_le hcmem hmem)
      have hpc : p ∈ c.support := by
        rw [Perm.mem_support]
        change f.cycleOf p p ≠ p
        rw [Perm.cycleOf_apply_self]
        exact Perm.mem_support.mp hpmem
      let h := swap 0 p * c
      have hhcycle : h.IsCycle := by
        exact isCycle_swap_mul_of_mem_support_of_not_mem_support hc hpc h0notc
      have hhcard : h.support.card = c.support.card + 1 := by
        exact card_support_swap_mul_of_mem_support_of_not_mem_support hc hpc h0notc
      have hdrh : Perm.Disjoint r h := by
        intro y
        by_cases hry : r y = y
        · exact Or.inl hry
        right
        have hyr : y ∈ r.support := Perm.mem_support.mpr hry
        have hyc : y ∉ c.support := by
          intro hyc
          exact (Finset.disjoint_left.mp hdrc.disjoint_support) hyr hyc
        have hcy : c y = y := Perm.notMem_support.mp hyc
        have hy0 : y ≠ 0 := by
          intro hy
          subst y
          have : 0 ∈ f.support := by
            rw [← hrc, hdrc.support_mul]
            exact Finset.mem_union_left _ hyr
          exact (Perm.notMem_support.mpr hf0) this
        have hyp : y ≠ p := by
          intro hy
          subst y
          exact hyc hpc
        simp [h, hcy, swap_apply_of_ne_of_ne hy0 hyp]
      have hdecomp : swap 0 p * f = h * r := by
        rw [← hcr]
        simp [h, mul_assoc]
      have hfsupp : f.support.card = e.support.card := by
        rw [← f.sum_cycleType, ← e.sum_cycleType, cycleType_liftFinPerm]
      have hftype : f.cycleType.card = e.cycleType.card := by
        rw [cycleType_liftFinPerm]
      have hrcType : f.cycleType.card = r.cycleType.card + c.cycleType.card := by
        rw [← hrc, hdrc.cycleType_mul, Multiset.card_add]
      have hrcSupport : f.support.card = r.support.card + c.support.card := by
        rw [← hrc, hdrc.card_support_mul]
      have hhType : h.cycleType.card = 1 := by rw [hhcycle.cycleType]; simp
      have hcType : c.cycleType.card = 1 := by rw [hc.cycleType]; simp
      rw [hdecomp, totalCycleCount_eq_card_sub_support,
        totalCycleCount_eq_card_sub_support, hdrh.symm.cycleType_mul,
        hdrh.symm.card_support_mul, Multiset.card_add]
      omega

theorem exactCycleCount_zero (ell : ℕ) :
    Erdos1161.exactCycleCount 0 ell = if ell = 0 then 1 else 0 := by
  classical
  rw [Erdos1161.exactCycleCount]
  rw [show (Finset.univ : Finset (Perm (Fin 0))) = {1} by
    ext σ
    simp [Subsingleton.elim σ 1]]
  have htc : ∀ σ : Perm (Fin 0), Erdos1161.totalCycleCount σ = 0 := by
    intro σ
    rw [totalCycleCount_eq]
    have hσ : σ = 1 := Subsingleton.elim σ 1
    subst σ
    simp
  by_cases h : ell = 0
  · subst ell
    have hall :
        ({1} : Finset (Perm (Fin 0))).filter
          (fun σ ↦ Erdos1161.totalCycleCount σ = 0) = {1} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact And.left
      · intro _
        exact ⟨Subsingleton.elim σ 1, htc σ⟩
    rw [hall]
    simp
  · have hempty :
        ({1} : Finset (Perm (Fin 0))).filter
          (fun σ ↦ Erdos1161.totalCycleCount σ = ell) = ∅ := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty,
        iff_false, not_and]
      intro _ hcard
      exact h (by rw [← hcard, htc σ])
    rw [hempty]
    simp [h]

theorem exactCycleCount_succ_succ (n ell : ℕ) :
    Erdos1161.exactCycleCount (n + 1) (ell + 1) =
      n * Erdos1161.exactCycleCount n (ell + 1) +
        Erdos1161.exactCycleCount n ell := by
  classical
  rw [Erdos1161.exactCycleCount, Finset.univ_perm_fin_succ]
  simp only [Finset.filter_map, Finset.card_map, Function.Embedding.coeFn_mk,
    Function.comp_apply]
  let A : Finset (Fin (n + 1) × Perm (Fin n)) :=
    ({0} : Finset (Fin (n + 1))) ×ˢ
      (Finset.univ.filter fun e : Perm (Fin n) ↦
        Erdos1161.totalCycleCount e = ell)
  let B : Finset (Fin (n + 1) × Perm (Fin n)) :=
    ((Finset.univ : Finset (Fin (n + 1))).erase 0) ×ˢ
      (Finset.univ.filter fun e : Perm (Fin n) ↦
        Erdos1161.totalCycleCount e = ell + 1)
  have hfilter :
      (Finset.univ.filter fun pe : Fin (n + 1) × Perm (Fin n) ↦
        Erdos1161.totalCycleCount (Perm.decomposeFin.symm pe) = ell + 1) =
        A ∪ B := by
    ext pe
    rcases pe with ⟨p, e⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      A, B, Finset.mem_product, Finset.mem_singleton, Finset.mem_erase]
    rw [totalCycleCount_decomposeFin_symm]
    by_cases hp : p = 0
    · subst p
      simp
    · simp [hp]
  rw [hfilter, Finset.card_union_of_disjoint]
  · simp [A, B, Erdos1161.exactCycleCount, Nat.add_comm]
  · rw [Finset.disjoint_left]
    intro pe hA hB
    rcases pe with ⟨p, e⟩
    simp [A, B] at hA hB
    exact hB.1 hA.2.symm

theorem totalCycleCount_pos {n : ℕ} (hn : 0 < n) (e : Perm (Fin n)) :
    0 < Erdos1161.totalCycleCount e := by
  rw [Erdos1161.totalCycleCount, Multiset.card_pos]
  intro hzero
  have hsum := Erdos1161.sum_fullCycleType e
  rw [hzero] at hsum
  simp at hsum
  omega

theorem totalCycleCount_le {n : ℕ} (e : Perm (Fin n)) :
    Erdos1161.totalCycleCount e ≤ n := by
  let mu := Erdos1161.fullCycleType e
  have card_le_sum_of_one_le (nu : Multiset ℕ)
      (hpos : ∀ a ∈ nu, 1 ≤ a) : nu.card ≤ nu.sum := by
    induction nu using Multiset.induction_on with
    | empty => simp
    | @cons a nu ih =>
        rw [Multiset.card_cons, Multiset.sum_cons]
        have ha : 1 ≤ a := hpos a (by simp)
        have htail : ∀ b ∈ nu, 1 ≤ b := by
          intro b hb
          exact hpos b (by simp [hb])
        have := ih htail
        omega
  have hcard : mu.card ≤ mu.sum := card_le_sum_of_one_le mu fun a ha ↦
    Erdos1161.one_le_of_mem_fullCycleType (σ := e) ha
  calc
    Erdos1161.totalCycleCount e = mu.card := rfl
    _ ≤ mu.sum := hcard
    _ = n := Erdos1161.sum_fullCycleType e

theorem exactCycleCount_succ_zero (n : ℕ) :
    Erdos1161.exactCycleCount (n + 1) 0 = 0 := by
  rw [Erdos1161.exactCycleCount, Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro e _
  exact (totalCycleCount_pos (Nat.zero_lt_succ n) e).ne'

theorem exactCycleCount_eq_stirlingFirst : ∀ n ell : ℕ,
    Erdos1161.exactCycleCount n ell = Nat.stirlingFirst n ell
  | 0, ell => by
      rw [exactCycleCount_zero]
      cases ell <;> simp [Nat.stirlingFirst]
  | n + 1, ell => by
      cases ell with
      | zero => rw [exactCycleCount_succ_zero, Nat.stirlingFirst_succ_zero]
      | succ ell =>
          rw [exactCycleCount_succ_succ, exactCycleCount_eq_stirlingFirst,
            exactCycleCount_eq_stirlingFirst, Nat.stirlingFirst_succ_succ]

/-- The number of permutations having more than `t` cycles, fixed points included. -/
def cycleCountTail (n t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Perm (Fin n))).filter fun e ↦
    t < Erdos1161.totalCycleCount e).card

theorem cycleCountTail_eq_stirlingCycleTail (n t : ℕ) :
    cycleCountTail n t = Erdos1161.stirlingCycleTail n t := by
  classical
  let S := (Finset.range (n + 1)).filter fun ell ↦ t < ell
  have hevent :
      ((Finset.univ : Finset (Perm (Fin n))).filter fun e ↦
        t < Erdos1161.totalCycleCount e) =
      Finset.univ.filter (fun e : Perm (Fin n) ↦
        Erdos1161.totalCycleCount e ∈ S) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S,
      Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · intro ht
      exact ⟨totalCycleCount_le e, ht⟩
    · exact And.right
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Perm (Fin n))) S Erdos1161.totalCycleCount
  calc
    cycleCountTail n t =
        ∑ ell ∈ S, Erdos1161.exactCycleCount n ell := by
      rw [cycleCountTail, hevent]
      simpa [Erdos1161.exactCycleCount] using h.symm
    _ = ∑ ell ∈ S, Nat.stirlingFirst n ell := by
      apply Finset.sum_congr rfl
      intro ell _
      exact exactCycleCount_eq_stirlingFirst n ell
    _ = Erdos1161.stirlingCycleTail n t := by
      rfl

theorem two_pow_mul_cycleCountTail_le (n t : ℕ) :
    2 ^ t * cycleCountTail n t ≤ (n + 1).factorial := by
  rw [cycleCountTail_eq_stirlingCycleTail]
  exact Erdos1161.two_pow_mul_stirlingCycleTail_le n t

theorem cycleCountTail_rational_probability_le (n t : ℕ) :
    (cycleCountTail n t : ℚ) / (n.factorial : ℚ) ≤
      (n + 1 : ℚ) / (2 ^ t : ℚ) := by
  have h := two_pow_mul_cycleCountTail_le n t
  rw [Nat.factorial_succ] at h
  rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < n.factorial)
    (by positivity : (0 : ℚ) < 2 ^ t)]
  have hq : ((2 ^ t * cycleCountTail n t : ℕ) : ℚ) ≤
      (((n + 1) * n.factorial : ℕ) : ℚ) := by exact_mod_cast h
  simpa [mul_comm] using hq

end Erdos1161

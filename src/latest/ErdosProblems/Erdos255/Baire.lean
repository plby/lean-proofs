/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

noncomputable section

namespace Erdos255Baire

def prefixCount (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℕ :=
  Nat.count (fun n ↦ z n < x) N

def discrepancy (z : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (prefixCount z N x : ℝ) - (N : ℝ) * x

def regularDomain (z : ℕ → ℝ) : Set ℝ :=
  Ioo 0 1 \ Set.range z

private lemma regularDomain_isGδ (z : ℕ → ℝ) : IsGδ (regularDomain z) := by
  change IsGδ (Ioo (0 : ℝ) 1 ∩ (Set.range z)ᶜ)
  exact isOpen_Ioo.isGδ.inter (Set.countable_range z).isGδ_compl

private lemma regularDomain_nonempty (z : ℕ → ℝ) : (regularDomain z).Nonempty := by
  have hd : Dense (Set.range z)ᶜ := (Set.countable_range z).dense_compl ℝ
  have ho : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hn : (Ioo (0 : ℝ) 1).Nonempty := ⟨1 / 2, by norm_num⟩
  obtain ⟨x, hx, hz⟩ := hd.inter_open_nonempty _ ho hn
  exact ⟨x, hx, hz⟩

private lemma threshold_continuous (z : ℕ → ℝ) (n : ℕ) :
    Continuous (fun x : regularDomain z ↦ if z n < (x : ℝ) then (1 : ℝ) else 0) := by
  let s : Set (regularDomain z) := {x | z n < (x : ℝ)}
  have hsopen : IsOpen s := by
    exact isOpen_Ioi.preimage continuous_subtype_val
  have hsclosed : IsClosed s := by
    have heq : sᶜ = {x : regularDomain z | (x : ℝ) < z n} := by
      ext x
      have hne : (x : ℝ) ≠ z n := by
        intro h
        exact x.property.2 ⟨n, h.symm⟩
      simp only [s, mem_compl_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact lt_of_le_of_ne (not_lt.mp h) hne
      · exact fun h ↦ not_lt.mpr h.le
    have hcopen : IsOpen sᶜ := by
      rw [heq]
      exact isOpen_Iio.preimage continuous_subtype_val
    simpa only [compl_compl] using hcopen.isClosed_compl
  have hsclopen : IsClopen s := ⟨hsclosed, hsopen⟩
  apply Continuous.if
  · intro x hx
    rw [hsclopen.frontier_eq] at hx
    exact hx.elim
  · fun_prop
  · fun_prop

private lemma prefixCount_continuous (z : ℕ → ℝ) (N : ℕ) :
    Continuous (fun x : regularDomain z ↦ (prefixCount z N (x : ℝ) : ℝ)) := by
  induction N with
  | zero =>
      simpa [prefixCount] using
        (continuous_const : Continuous (fun _ : regularDomain z ↦ (0 : ℝ)))
  | succ N ih =>
      convert ih.add (threshold_continuous z N) using 1
      all_goals
        ext x
        simp [prefixCount, Nat.count_succ]

private lemma discrepancy_continuous (z : ℕ → ℝ) (N : ℕ) :
    Continuous (fun x : regularDomain z ↦ discrepancy z N (x : ℝ)) := by
  exact (prefixCount_continuous z N).sub
    (continuous_const.mul continuous_subtype_val)

def boundedLayer (z : ℕ → ℝ) (m : ℕ) : Set (regularDomain z) :=
  {x | ∀ N, |discrepancy z N (x : ℝ)| ≤ m}

private lemma boundedLayer_closed (z : ℕ → ℝ) (m : ℕ) :
    IsClosed (boundedLayer z m) := by
  have hN : ∀ N : ℕ, IsClosed {x : regularDomain z |
      |discrepancy z N (x : ℝ)| ≤ m} := by
    intro N
    exact isClosed_Iic.preimage ((discrepancy_continuous z N).abs)
  have heq : boundedLayer z m = ⋂ N : ℕ,
      {x : regularDomain z | |discrepancy z N (x : ℝ)| ≤ m} := by
    ext x
    simp [boundedLayer]
  rw [heq]
  exact isClosed_iInter hN

private lemma threshold_continuousWithinAt_Iic (c x : ℝ) :
    ContinuousWithinAt (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0) (Iic x) x := by
  by_cases hcx : c < x
  · have he : ∀ᶠ y in nhdsWithin x (Iic x), c < y :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcx)
    have heq : Filter.EventuallyEq (nhdsWithin x (Iic x))
        (fun _ : ℝ ↦ (1 : ℝ)) (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0) := by
      filter_upwards [he] with y hy
      simp [hy]
    change Tendsto (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0)
      (nhdsWithin x (Iic x)) (nhds (if c < x then (1 : ℝ) else 0))
    rw [if_pos hcx]
    exact continuousWithinAt_const.congr' heq
  · have heq : Filter.EventuallyEq (nhdsWithin x (Iic x))
        (fun _ : ℝ ↦ (0 : ℝ)) (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hcy : ¬ c < y := fun h ↦ hcx (h.trans_le hy)
      simp [hcy]
    change Tendsto (fun y : ℝ ↦ if c < y then (1 : ℝ) else 0)
      (nhdsWithin x (Iic x)) (nhds (if c < x then (1 : ℝ) else 0))
    rw [if_neg hcx]
    exact continuousWithinAt_const.congr' heq

private lemma prefixCount_continuousWithinAt_Iic (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ ↦ (prefixCount z N y : ℝ)) (Iic x) x := by
  induction N with
  | zero =>
      simpa [prefixCount] using
        (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ ↦ (0 : ℝ)) (Iic x) x)
  | succ N ih =>
      convert ih.add (threshold_continuousWithinAt_Iic (z N) x) using 1
      all_goals
        ext y
        simp [prefixCount, Nat.count_succ]

private lemma discrepancy_continuousWithinAt_Iic (z : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ContinuousWithinAt (discrepancy z N) (Iic x) x := by
  exact (prefixCount_continuousWithinAt_Iic z N x).sub
    (continuousWithinAt_const.mul continuousWithinAt_id)

private lemma extend_bound_from_regularDomain
    (z : ℕ → ℝ) (m : ℕ) {l r : ℝ} (hl0 : 0 < l) (hr1 : r < 1)
    (hbound : ∀ x : regularDomain z, (x : ℝ) ∈ Ioo l r →
      ∀ N, |discrepancy z N (x : ℝ)| ≤ m) :
    ∀ x ∈ Ioo l r, ∀ N, |discrepancy z N x| ≤ m := by
  intro x hx N
  let S : Set ℝ := Ioo l x ∩ (Set.range z)ᶜ
  have hd : Dense (Set.range z)ᶜ := (Set.countable_range z).dense_compl ℝ
  have hsubcl : Ioo l x ⊆ closure S := by
    simpa only [S] using hd.open_subset_closure_inter (isOpen_Ioo (a := l) (b := x))
  have hxclI : x ∈ closure (Ioo l x) := by
    rw [closure_Ioo hx.1.ne]
    exact ⟨hx.1.le, le_rfl⟩
  have hxcl : x ∈ closure S := by
    exact (isClosed_closure.closure_subset_iff.mpr hsubcl) hxclI
  have hmaps : MapsTo (fun y ↦ |discrepancy z N y|) S (Iic (m : ℝ)) := by
    intro y hy
    have hyreg : y ∈ regularDomain z := ⟨
      ⟨hl0.trans hy.1.1, (hy.1.2.trans hx.2).trans hr1⟩, hy.2⟩
    exact hbound ⟨y, hyreg⟩ ⟨hy.1.1, hy.1.2.trans hx.2⟩ N
  have hcont : ContinuousWithinAt (fun y ↦ |discrepancy z N y|) S x := by
    exact (continuous_abs.continuousAt.comp_continuousWithinAt
      (discrepancy_continuousWithinAt_Iic z N x)).mono fun y hy ↦ hy.1.2.le
  exact (isClosed_Iic.closure_subset (hcont.mem_closure hxcl hmaps))

private lemma count_Ico_add_count_lt (z : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    Nat.count (fun n ↦ a ≤ z n ∧ z n < b) N + prefixCount z N a = prefixCount z N b := by
  induction N with
  | zero => simp [prefixCount]
  | succ N ih =>
      simp only [Nat.count_succ, prefixCount]
      change Nat.count (fun n ↦ a ≤ z n ∧ z n < b) N +
        Nat.count (fun n ↦ z n < a) N = Nat.count (fun n ↦ z n < b) N at ih
      by_cases ha : z N < a
      · have hb : z N < b := ha.trans_le hab
        have hna : ¬ a ≤ z N := not_le_of_gt ha
        simp [ha, hb, hna]
        omega
      · by_cases hb : z N < b
        · have hale : a ≤ z N := le_of_not_gt ha
          simp [ha, hb, hale]
          omega
        · simp [ha, hb]
          omega

private lemma count_comp_nth_of_infinite
    (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hp : {n | p n}.Infinite) (K : ℕ) :
    Nat.count (fun j ↦ q (Nat.nth p j)) K =
      Nat.count (fun n ↦ p n ∧ q n) (Nat.nth p K) := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun j _ ↦ Nat.nth p j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨(Nat.nth_lt_nth hp).2 hj.1, Nat.nth_mem_of_infinite hp j, hj.2⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    exact Nat.nth_injective hp heq
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have hnrange : n ∈ Set.range (Nat.nth p) := by
      rw [Nat.range_nth_of_infinite hp]
      exact hn.2.1
    obtain ⟨j, hj⟩ := hnrange
    subst n
    have hjK : j < K := (Nat.nth_lt_nth hp).1 hn.1
    exact ⟨j, by simp [hjK, hn.2.2], rfl⟩

private lemma natCount_congr (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ n, p n ↔ q n) (N : ℕ) : Nat.count p N = Nat.count q N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Nat.count_succ]
      rw [ih]
      simp [h N]

def NoUniformStarDiscrepancy : Prop :=
  ∀ w : ℕ → ℝ, (∀ n, w n ∈ Ico (0 : ℝ) 1) →
    ∀ C : ℝ, ∃ N : ℕ, ∃ x ∈ Icc (0 : ℝ) 1,
      C < |discrepancy w N x|

private lemma local_uniform_impossible
    (hstar : NoUniformStarDiscrepancy) (z : ℕ → ℝ)
    {a b C : ℝ} (hab : a < b)
    (hbound : ∀ N x, x ∈ Icc a b → |discrepancy z N x| ≤ C) : False := by
  let p : ℕ → Prop := fun n ↦ a ≤ z n ∧ z n < b
  classical
  have hpinf : {n | p n}.Infinite := by
    by_contra hp
    have hpfin : {n | p n}.Finite := Set.not_infinite.mp hp
    let B : ℕ := hpfin.toFinset.card
    let L : ℝ := b - a
    have hL : 0 < L := sub_pos.mpr hab
    obtain ⟨N, hN⟩ := exists_nat_gt (((B : ℝ) + 2 * C) / L)
    have hlarge : (B : ℝ) + 2 * C < (N : ℝ) * L := by
      have := (mul_lt_mul_of_pos_right hN hL)
      field_simp [L, hL.ne'] at this
      nlinarith
    have hcount : Nat.count p N ≤ B := by
      exact Nat.count_le_card hpfin N
    have hid : discrepancy z N b - discrepancy z N a =
        (Nat.count p N : ℝ) - (N : ℝ) * L := by
      have hc := count_Ico_add_count_lt z hab.le N
      have hc' : Nat.count p N + prefixCount z N a = prefixCount z N b := by
        have hcnt : Nat.count p N =
            @Nat.count (fun n ↦ a ≤ z n ∧ z n < b) (fun _ ↦ instDecidableAnd) N :=
          @natCount_congr p (fun n ↦ a ≤ z n ∧ z n < b) (fun _ ↦ instDecidableAnd)
            (fun _ ↦ instDecidableAnd) (fun _ ↦ Iff.rfl) N
        rw [hcnt]
        exact hc
      have hcR : (prefixCount z N b : ℝ) =
          (Nat.count p N : ℝ) + prefixCount z N a := by
        exact_mod_cast hc'.symm
      unfold discrepancy
      rw [hcR]
      dsimp [L]
      ring
    have ha := hbound N a ⟨le_rfl, hab.le⟩
    have hb := hbound N b ⟨hab.le, le_rfl⟩
    have hcountR : (Nat.count p N : ℝ) ≤ B := by exact_mod_cast hcount
    rcases abs_le.mp ha with ⟨ha_lower, ha_upper⟩
    rcases abs_le.mp hb with ⟨hb_lower, hb_upper⟩
    nlinarith [hid]
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  let w : ℕ → ℝ := fun k ↦ (z (Nat.nth p k) - a) / L
  have hw : ∀ k, w k ∈ Ico (0 : ℝ) 1 := by
    intro k
    have hk := Nat.nth_mem_of_infinite hpinf k
    change a ≤ z (Nat.nth p k) ∧ z (Nat.nth p k) < b at hk
    constructor
    · exact div_nonneg (sub_nonneg.mpr hk.1) hL.le
    · rw [div_lt_one hL]
      dsimp [L]
      linarith
  obtain ⟨K, y, hy, hbad⟩ := hstar w hw (4 * C)
  let T : ℕ := Nat.nth p K
  let x : ℝ := a + L * y
  have hx : x ∈ Icc a b := by
    dsimp [x, L]
    constructor <;> nlinarith [hy.1, hy.2]
  have hpT : Nat.count p T = K := by
    exact Nat.count_nth_of_infinite hpinf K
  have hendNat : K + prefixCount z T a = prefixCount z T b := by
    have hc := count_Ico_add_count_lt z hab.le T
    have hc' : Nat.count p T + prefixCount z T a = prefixCount z T b := by
      have hcnt : Nat.count p T =
          @Nat.count (fun n ↦ a ≤ z n ∧ z n < b) (fun _ ↦ instDecidableAnd) T :=
        @natCount_congr p (fun n ↦ a ≤ z n ∧ z n < b) (fun _ ↦ instDecidableAnd)
          (fun _ ↦ instDecidableAnd) (fun _ ↦ Iff.rfl) T
      rw [hcnt]
      exact hc
    rwa [hpT] at hc'
  have hprefixW : prefixCount w K y =
      Nat.count (fun n ↦ p n ∧ z n < x) T := by
    calc
      prefixCount w K y = Nat.count (fun j ↦ z (Nat.nth p j) < x) K := by
        unfold prefixCount
        apply natCount_congr
        intro j
        dsimp [w, x]
        rw [div_lt_iff₀ hL]
        constructor <;> intro h <;> linarith
      _ = Nat.count (fun n ↦ p n ∧ z n < x) T := by
        exact count_comp_nth_of_infinite p (fun n ↦ z n < x) hpinf K
  have hxle : x ≤ b := hx.2
  have hprefixNat : prefixCount w K y + prefixCount z T a = prefixCount z T x := by
    have hc := count_Ico_add_count_lt z hx.1 T
    have hcnt : Nat.count (fun n ↦ p n ∧ z n < x) T =
        @Nat.count (fun n ↦ a ≤ z n ∧ z n < x) (fun _ ↦ instDecidableAnd) T := by
      apply natCount_congr
      intro n
      dsimp [p]
      constructor
      · exact fun h ↦ ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, h.2.trans_le hxle⟩, h.2⟩
    rw [hprefixW, hcnt]
    exact hc
  have hprefixR : (prefixCount w K y : ℝ) =
      (prefixCount z T x : ℝ) - prefixCount z T a := by
    have hc : (prefixCount w K y : ℝ) + prefixCount z T a = prefixCount z T x := by
      exact_mod_cast hprefixNat
    linarith
  have hendR : (K : ℝ) = (prefixCount z T b : ℝ) - prefixCount z T a := by
    have hc : (K : ℝ) + prefixCount z T a = prefixCount z T b := by
      exact_mod_cast hendNat
    linarith
  have hdw : discrepancy w K y =
      (discrepancy z T x - discrepancy z T a) -
        (discrepancy z T b - discrepancy z T a) * y := by
    unfold discrepancy
    rw [hprefixR, hendR]
    dsimp [x, L]
    ring
  have hxa := hbound T x hx
  have haa := hbound T a ⟨le_rfl, hab.le⟩
  have hbb := hbound T b ⟨hab.le, le_rfl⟩
  have hyabs : |y| ≤ 1 := (abs_le).2 ⟨by linarith [hy.1], hy.2⟩
  have hfinal : |discrepancy w K y| ≤ 4 * C := calc
    |discrepancy w K y| =
        |(discrepancy z T x - discrepancy z T a) -
          (discrepancy z T b - discrepancy z T a) * y| := congrArg abs hdw
    _ ≤ |discrepancy z T x - discrepancy z T a| +
        |(discrepancy z T b - discrepancy z T a) * y| := abs_sub _ _
    _ = |discrepancy z T x - discrepancy z T a| +
        |discrepancy z T b - discrepancy z T a| * |y| := by rw [abs_mul]
    _ ≤ (|discrepancy z T x| + |discrepancy z T a|) +
        (|discrepancy z T b| + |discrepancy z T a|) := by
      gcongr
      · exact abs_sub _ _
      · calc
          |discrepancy z T b - discrepancy z T a| * |y|
              ≤ |discrepancy z T b - discrepancy z T a| * 1 := by gcongr
          _ ≤ |discrepancy z T b| + |discrepancy z T a| := by
            simpa using abs_sub (discrepancy z T b) (discrepancy z T a)
    _ ≤ 4 * C := by linarith
  exact (not_lt_of_ge hfinal) hbad

theorem exists_unbounded_prefix_discrepancy
    (hstar : NoUniformStarDiscrepancy) (z : ℕ → ℝ) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ¬ BddAbove (Set.range (fun N ↦ |discrepancy z N x|)) := by
  by_contra h
  push Not at h
  let _ : BaireSpace (regularDomain z) :=
    (regularDomain_isGδ z).baireSpace_of_t2Space_locallyCompactSpace
  let _ : Nonempty (regularDomain z) := (regularDomain_nonempty z).to_subtype
  have hcover : ⋃ m : ℕ, boundedLayer z m = Set.univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hb := h (x : ℝ) x.property.1
    rcases hb with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_gt C
    refine ⟨m, ?_⟩
    intro N
    exact (hC ⟨N, rfl⟩).trans hm.le
  obtain ⟨m, x₀, hx₀⟩ :=
    nonempty_interior_of_iUnion_of_closed (boundedLayer_closed z) hcover
  have hnh : interior (boundedLayer z m) ∈ nhds x₀ :=
    isOpen_interior.mem_nhds hx₀
  obtain ⟨u, hu, husub⟩ := (mem_nhds_subtype (regularDomain z) x₀ _).mp hnh
  obtain ⟨l, r, hlr, hlrsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  let A : ℝ := (max l 0 + (x₀ : ℝ)) / 2
  let B : ℝ := ((x₀ : ℝ) + min r 1) / 2
  have hlx : max l 0 < (x₀ : ℝ) := (max_lt_iff).2 ⟨hlr.1, x₀.property.1.1⟩
  have hxr : (x₀ : ℝ) < min r 1 := (lt_min_iff).2 ⟨hlr.2, x₀.property.1.2⟩
  have hA0 : 0 < A := by
    dsimp [A]
    nlinarith [le_max_right l 0, x₀.property.1.1]
  have hlA : l < A := by
    dsimp [A]
    nlinarith [le_max_left l 0, hlx]
  have hAx : A < (x₀ : ℝ) := by dsimp [A]; linarith
  have hxB : (x₀ : ℝ) < B := by dsimp [B]; linarith
  have hBr : B < r := by
    dsimp [B]
    nlinarith [min_le_left r 1, hxr]
  have hB1 : B < 1 := by
    dsimp [B]
    nlinarith [min_le_right r 1, x₀.property.1.2]
  have hboundReg : ∀ x : regularDomain z, (x : ℝ) ∈ Ioo A B →
      ∀ N, |discrepancy z N (x : ℝ)| ≤ m := by
    intro x hxAB
    have hxu : (x : ℝ) ∈ u := hlrsub ⟨hlA.trans hxAB.1, hxAB.2.trans hBr⟩
    exact interior_subset (husub hxu)
  have hall := extend_bound_from_regularDomain z m hA0 hB1 hboundReg
  let c : ℝ := (A + (x₀ : ℝ)) / 2
  let d : ℝ := ((x₀ : ℝ) + B) / 2
  have hcd : c < d := by dsimp [c, d]; linarith
  have hlocal : ∀ N y, y ∈ Icc c d → |discrepancy z N y| ≤ (m : ℝ) := by
    intro N y hy
    apply hall y ?_ N
    constructor
    · have hyl := hy.1
      dsimp [c] at hyl
      linarith [hAx]
    · have hyr := hy.2
      dsimp [d] at hyr
      linarith [hxB]
  exact local_uniform_impossible hstar z hcd hlocal

theorem unbounded_endpoint_of_no_uniform
    (hstar : NoUniformStarDiscrepancy) (z : ℕ → ℝ) :
    ∃ x ∈ Icc (0 : ℝ) 1, ∀ C : ℝ, ∃ N : ℕ,
      C < |discrepancy z N x| := by
  obtain ⟨x, hx, hub⟩ := exists_unbounded_prefix_discrepancy hstar z
  refine ⟨x, ⟨hx.1.le, hx.2.le⟩, ?_⟩
  intro C
  by_contra h
  push Not at h
  apply hub
  refine ⟨C, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact h N

end Erdos255Baire

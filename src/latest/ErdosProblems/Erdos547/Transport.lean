import ErdosProblems.Erdos547.MatchingCompactness

/-!
# Finite fractional transport with prescribed row and column bounds

A direct compactness and augmentation proof is used. No flow theorem is
assumed. The neighbourhood hypothesis below is stronger than Hall's
condition, and is precisely what the greedy allocation lemmas need.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

structure Transport (P : V → V → Prop) (a b : V → ℝ) where
  weight : V → V → ℝ
  nonnegative : ∀ u v, 0 ≤ weight u v
  supported : ∀ u v, ¬ P u v → weight u v = 0
  row_bound : ∀ u, ∑ v, weight u v ≤ a u
  col_bound : ∀ v, ∑ u, weight u v ≤ b v

namespace Transport

def row {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) (u : V) : ℝ :=
  ∑ v, f.weight u v

def col {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) (v : V) : ℝ :=
  ∑ u, f.weight u v

def total {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) : ℝ :=
  ∑ u, f.row u

theorem sum_col {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) :
    (∑ v, f.col v) = f.total := Finset.sum_comm

theorem row_nonneg {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) (u : V) :
    0 ≤ f.row u := Finset.sum_nonneg fun v _ ↦ f.nonnegative u v

theorem col_nonneg {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) (v : V) :
    0 ≤ f.col v := Finset.sum_nonneg fun u _ ↦ f.nonnegative u v

def feasible (P : V → V → Prop) (a b : V → ℝ) : Set (V → V → ℝ) := {f |
  (∀ u v, 0 ≤ f u v) ∧ (∀ u v, ¬ P u v → f u v = 0) ∧
    (∀ u, ∑ v, f u v ≤ a u) ∧ ∀ v, ∑ u, f u v ≤ b v}

theorem isClosed_feasible (P : V → V → Prop) (a b : V → ℝ) : IsClosed (feasible P a b) := by
  have hn : IsClosed {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_le continuous_const (by fun_prop)
  have hs : IsClosed {f : V → V → ℝ | ∀ u v, ¬ P u v → f u v = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) continuous_const
  have hr : IsClosed {f : V → V → ℝ | ∀ u, ∑ v, f u v ≤ a u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_le (by fun_prop) continuous_const
  have hc : IsClosed {f : V → V → ℝ | ∀ v, ∑ u, f u v ≤ b v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v ↦ isClosed_le (by fun_prop) continuous_const
  exact hn.inter (hs.inter (hr.inter hc))

theorem exists_maximum (P : V → V → Prop) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) :
    ∃ f : Transport P a b, ∀ g : Transport P a b, g.total ≤ f.total := by
  have hcompact : IsCompact (feasible P a b) := by
    apply (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : V ↦ (0 : ℝ))
      (fun u _ ↦ a u))).of_isClosed_subset (isClosed_feasible P a b)
    intro f hf
    refine ⟨hf.1, ?_⟩
    intro u v
    exact (Finset.single_le_sum (fun v _ ↦ hf.1 u v) (Finset.mem_univ v)).trans (hf.2.2.1 u)
  have hnonempty : (feasible P a b).Nonempty := by
    refine ⟨fun _ _ ↦ 0, fun _ _ ↦ le_rfl, fun _ _ _ ↦ rfl, ?_, ?_⟩
    · intro u
      simpa only [Finset.sum_const_zero] using ha u
    · intro v
      simpa only [Finset.sum_const_zero] using hb v
  obtain ⟨f, hf, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (show Continuous (fun f : V → V → ℝ ↦ ∑ u, ∑ v, f u v) by fun_prop).continuousOn
  refine ⟨⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩, ?_⟩
  intro g
  exact hmax ⟨g.nonnegative, g.supported, g.row_bound, g.col_bound⟩

open scoped Classical in
def increase {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) {x y : V}
    (hxy : P x y) (t : ℝ) (ht : 0 ≤ t) (hr : f.row x + t ≤ a x)
    (hc : f.col y + t ≤ b y) : Transport P a b where
  weight u v := f.weight u v + if u = x ∧ v = y then t else 0
  nonnegative u v := add_nonneg (f.nonnegative u v) (by split_ifs <;> linarith)
  supported u v huv := by
    rw [f.supported u v huv]
    have hn : ¬ (u = x ∧ v = y) := by rintro ⟨rfl, rfl⟩; exact huv hxy
    rw [if_neg hn, add_zero]
  row_bound u := by
    rw [Finset.sum_add_distrib]
    by_cases hux : u = x
    · subst u
      simpa [row] using hr
    · simpa only [hux, false_and, if_false, Finset.sum_const_zero, add_zero] using f.row_bound u
  col_bound v := by
    rw [Finset.sum_add_distrib]
    by_cases hvy : v = y
    · subst v
      simpa [col] using hc
    · simpa only [hvy, and_false, if_false, Finset.sum_const_zero, add_zero] using f.col_bound v

theorem increase_total {P : V → V → Prop} {a b : V → ℝ} (f : Transport P a b) {x y : V}
    (hxy : P x y) (t : ℝ) (ht : 0 ≤ t) (hr : f.row x + t ≤ a x)
    (hc : f.col y + t ≤ b y) : (f.increase hxy t ht hr hc).total = f.total + t := by
  classical
  have hi (u : V) : (∑ v, if u = x ∧ v = y then t else (0 : ℝ)) =
      if u = x then t else 0 := by
    by_cases hu : u = x <;> simp [hu]
  simp only [total, row, increase, Finset.sum_add_distrib, hi, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem maximum_saturates {P : V → V → Prop} {a b : V → ℝ} {f : Transport P a b}
    (hmax : ∀ g : Transport P a b, g.total ≤ f.total) {x y : V} (hxy : P x y)
    (hx : f.row x < a x) : f.col y = b y := by
  apply le_antisymm (f.col_bound y)
  by_contra hn
  have hy : f.col y < b y := lt_of_not_ge hn
  let t := min (a x - f.row x) (b y - f.col y)
  have ht : 0 < t := lt_min (sub_pos.mpr hx) (sub_pos.mpr hy)
  have hr : f.row x + t ≤ a x := by have := min_le_left (a x - f.row x) (b y - f.col y); linarith
  have hc : f.col y + t ≤ b y := by have := min_le_right (a x - f.row x) (b y - f.col y); linarith
  have hh := hmax (f.increase hxy t ht.le hr hc)
  rw [increase_total] at hh
  linarith

open scoped Classical in
theorem exists_full_rows (P : V → V → Prop) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u)
    (hN : ∀ x, 0 < a x → (∑ u, a u) ≤ ∑ y ∈ Finset.univ.filter (P x), b y) :
    ∃ f : Transport P a b, ∀ u, f.row u = a u := by
  classical
  obtain ⟨f, hmax⟩ := exists_maximum P a b ha hb
  refine ⟨f, ?_⟩
  intro x
  apply le_antisymm (f.row_bound x)
  by_contra hn
  have hx : f.row x < a x := lt_of_not_ge hn
  have hpos : 0 < a x := (f.row_nonneg x).trans_lt hx
  have htotal : f.total < ∑ u, a u := Finset.sum_lt_sum
    (fun u _ ↦ f.row_bound u) ⟨x, Finset.mem_univ _, hx⟩
  have hs : (∑ y ∈ Finset.univ.filter (P x), b y) ≤ f.total := by
    calc
      _ = ∑ y ∈ Finset.univ.filter (P x), f.col y := Finset.sum_congr rfl fun y hy ↦
        (maximum_saturates hmax (Finset.mem_filter.mp hy).2 hx).symm
      _ ≤ ∑ y, f.col y := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun y _ _ ↦ f.col_nonneg y)
      _ = _ := f.sum_col
  exact (not_lt_of_ge ((hN x hpos).trans hs)) htotal

end Transport

end Erdos547.DPRS

#print axioms Erdos547.DPRS.Transport.exists_full_rows

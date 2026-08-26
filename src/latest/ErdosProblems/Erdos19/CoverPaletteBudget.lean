import ErdosProblems.Erdos19.Core

/-! # Palette budgets for coverage refinement and extension -/

namespace Erdos19

theorem cover_denominator_budget (n t s B : ℕ) (hn : 0 < n)
    (ht : 0 < t) (hs : 0 < s) (hB : n ≤ t * B) :
    (n * (n - 1) / (B * (t ^ 2 * s))) * (t * s) ≤ n - 1 := by
  let q := n * (n - 1) / (B * (t ^ 2 * s))
  have hdiv : q * (B * (t ^ 2 * s)) ≤ n * (n - 1) := by
    rw [Nat.mul_comm q]
    exact Nat.mul_div_le (n * (n - 1)) (B * (t ^ 2 * s))
  have hden : n * (t * s) ≤ B * (t ^ 2 * s) := by
    have h := Nat.mul_le_mul_right (t * s) hB
    simpa only [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hmul := Nat.mul_le_mul_left q hden
  have hcancel : n * (q * (t * s)) ≤ n * (n - 1) := by
    nlinarith only [hmul, hdiv]
  exact Nat.le_of_mul_le_mul_left hcancel hn

theorem cover_extension_palette_budget (n t s : ℕ) (hn : 0 < n)
    (ht : 0 < t) (hs : 0 < s) :
    n * (n - 1) / ((8 * (n / t) + 1) * (t ^ 2 * s)) ≤ n / s := by
  have hfloor := Nat.lt_mul_div_succ n ht
  have hB : n ≤ t * (8 * (n / t) + 1) :=
    hfloor.le.trans (Nat.mul_le_mul_left t (by omega))
  have h := cover_denominator_budget n t s (8 * (n / t) + 1) hn ht hs hB
  apply (Nat.le_div_iff_mul_le hs).mpr
  have ht1 : 1 ≤ t := ht
  have hmul := Nat.mul_le_mul_left
    (n * (n - 1) / ((8 * (n / t) + 1) * (t ^ 2 * s)) * s) ht1
  nlinarith only [h, hmul, Nat.sub_le n 1]

theorem cover_refinement_palette_budget (n t s : ℕ) (hn : 0 < n)
    (ht : 0 < t) (hs : 0 < s) :
    (n * (n - 1) / ((16 * (n / t) + 1) * (t ^ 2 * s))) *
      (n / (8 * (n / t) + 1)) ≤ n / s := by
  have hfloor := Nat.lt_mul_div_succ n ht
  have hB : n ≤ t * (16 * (n / t) + 1) :=
    hfloor.le.trans (Nat.mul_le_mul_left t (by omega))
  have h := cover_denominator_budget n t s (16 * (n / t) + 1) hn ht hs hB
  have hsecond : n / (8 * (n / t) + 1) ≤ t := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    exact hfloor.trans_le (Nat.mul_le_mul (Nat.le_succ t) (by omega))
  apply (Nat.le_div_iff_mul_le hs).mpr
  have hmul := Nat.mul_le_mul_right s (Nat.mul_le_mul_left
    (n * (n - 1) / ((16 * (n / t) + 1) * (t ^ 2 * s))) hsecond)
  nlinarith only [h, hmul, Nat.sub_le n 1]

theorem half_saving_palette_budget (n s : ℕ) (hs : 0 < s) :
    n - n / s + n / (2 * s) ≤ n - n / (2 * s) := by
  have hdouble : 2 * (n / (2 * s)) ≤ n / s := by
    apply (Nat.le_div_iff_mul_le hs).mpr
    have h := Nat.mul_div_le n (2 * s)
    nlinarith only [h]
  have hdiv : n / s ≤ n := Nat.div_le_self _ _
  omega

namespace SetHypergraph

variable {V : Type*} [Fintype V]

theorem exists_cover_bounded_coloring_of_palette_card (H : SetHypergraph V)
    {C : Type*} [Fintype C] (color : H.EdgeColoring C) (A n : ℕ)
    (hbounded : H.IsCoverBoundedColoring color A) (hcard : Fintype.card C ≤ n) :
    ∃ color' : H.EdgeColoring (Fin n), H.IsCoverBoundedColoring color' A := by
  classical
  have hcard' : Fintype.card C ≤ Fintype.card (Fin n) := by simpa using hcard
  obtain ⟨embed : C ↪ Fin n⟩ := Function.Embedding.nonempty_of_card_le hcard'
  let color' : H.EdgeColoring (Fin n) :=
    { color := fun e ↦ embed (color e)
      valid := fun {e f} hne hinter heq ↦ color.valid hne hinter (embed.injective heq) }
  refine ⟨color', fun a ↦ ?_⟩
  by_cases hex : ∃ c : C, embed c = a
  · obtain ⟨c, rfl⟩ := hex
    have hclass : ({e : H | color' e = embed c} : Set H) = {e | color e = c} := by
      ext e
      exact embed.injective.eq_iff
    simpa only [hclass] using hbounded c
  · left
    have hclass : ({e : H | color' e = a} : Set H) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hex ⟨color e, he⟩
    simp only [hclass, Set.ncard_empty, Nat.zero_le]

theorem exists_cover_bounded_coloring_of_saving (H : SetHypergraph V)
    (hlinear : H.IsLinear) (n t s : ℕ) (hvertices : Fintype.card V = n)
    (hn : 0 < n) (ht : 0 < t) (hs : 0 < s)
    (hmin : ∀ e : H, t ^ 2 * (2 * s) + 1 ≤ e.1.ncard)
    (hcolor : H.EdgeColorable (n - n / s)) :
    ∃ color : H.EdgeColoring (Fin (n - n / (2 * s))),
      H.IsCoverBoundedColoring color (16 * (n / t)) := by
  obtain ⟨color⟩ := hcolor
  obtain ⟨C, hC, c, hbounded, hcard⟩ := H.exists_cover_bounded_recoloring_card_le_pairBudget
    hlinear color (16 * (n / t)) (t ^ 2 * (2 * s)) (by positivity) hmin
  letI : Fintype C := hC
  have hhalf : 16 * (n / t) / 2 = 8 * (n / t) := by omega
  rw [hvertices, Fintype.card_fin, hhalf] at hcard
  have hbudget := cover_refinement_palette_budget n t (2 * s) hn ht (by omega)
  apply H.exists_cover_bounded_coloring_of_palette_card c _ _ hbounded
  exact hcard.trans ((Nat.add_le_add_left hbudget _).trans (half_saving_palette_budget n s hs))

end SetHypergraph

#print axioms SetHypergraph.exists_cover_bounded_coloring_of_saving

end Erdos19

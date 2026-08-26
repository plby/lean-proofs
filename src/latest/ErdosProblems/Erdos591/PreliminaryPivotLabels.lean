import ErdosProblems.Erdos591.FirstSecondLastLabels

/-!
# Full S labels with two ordered preliminary groups and two shared pivots

The group order is E_T, E_U, beta, F_U, gamma, F_T. The lower label
uses E_T, beta, gamma, F_T; the upper label uses E_U, beta, F_U, gamma.
The requested full cardinalities are preserved, including empty groups.
-/

namespace Erdos591.Positive.Game

structure PreliminaryPivotLabels (H : Set ℕ) (B p q r t : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  beta : ℕ
  gamma : ℕ
  marker : ℕ
  lower_card : lower.card = p
  upper_card : upper.card = q
  beta_lower : beta ∈ lower
  beta_upper : beta ∈ upper
  gamma_lower : gamma ∈ lower
  gamma_upper : gamma ∈ upper
  beta_lt_gamma : beta < gamma
  lower_before : (lower.filter (fun x => x < beta)).card = r
  upper_before : (upper.filter (fun x => x < beta)).card = t
  preliminary_order : ∀ x ∈ lower, x < beta → ∀ y ∈ upper, y < beta → x < y
  lower_gap : ∀ x ∈ lower, x ≤ beta ∨ gamma ≤ x
  upper_le_gamma : ∀ x ∈ upper, x ≤ gamma
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace PreliminaryPivotLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B p q r t : ℕ)
    (hp : r + 2 ≤ p) (hq : t + 2 ≤ q) : Nonempty (PreliminaryPivotLabels H B p q r t) := by
  classical
  obtain ⟨f, hf, hfH, hfB, _⟩ := FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  let E := (Finset.range r).image f
  let F := (Finset.range t).image (fun i => f (r + i))
  let C := f (r + t)
  obtain ⟨L⟩ := FirstSecondLastLabels.exists_of_infinite hH C (p - r) (q - t)
    (by omega) (by omega)
  have hE (x : ℕ) (hx : x ∈ E) : x ∈ H ∧ B < x ∧ x < C := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hfH i, hfB i, hf (by have := Finset.mem_range.mp hi; omega)⟩
  have hF (x : ℕ) (hx : x ∈ F) : x ∈ H ∧ B < x ∧ x < C := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hfH _, hfB _, hf (Nat.add_lt_add_left (Finset.mem_range.mp hi) r)⟩
  have hEcard : E.card = r := by
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_range]
  have hFcard : F.card = t := by
    have hinj : Function.Injective (fun i => f (r + i)) :=
      fun i j h => Nat.add_left_cancel (hf.injective h)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hCfirst : C < L.first := (L.lower_fresh _ L.first_lower).2.1
  have hCmarker : C < L.marker := L.marker_fresh.2
  have hdisE : Disjoint E L.lower := by
    apply Finset.disjoint_left.mpr
    intro x hx hl
    exact not_lt_of_ge ((hE x hx).2.2.le) (L.lower_fresh x hl).2.1
  have hdisF : Disjoint F L.upper := by
    apply Finset.disjoint_left.mpr
    intro x hx hl
    exact not_lt_of_ge ((hF x hx).2.2.le) (L.upper_fresh x hl).2.1
  have hfilterE : (E ∪ L.lower).filter (fun x => x < L.first) = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hx
      · exact (not_lt_of_ge (L.lower_first x hx) hlt).elim
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hx, (hE x hx).2.2.trans hCfirst⟩
  have hfilterF : (F ∪ L.upper).filter (fun x => x < L.first) = F := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hx
      · exact (not_lt_of_ge (L.upper_bounds x hx).1 hlt).elim
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hx, (hF x hx).2.2.trans hCfirst⟩
  refine ⟨⟨E ∪ L.lower, F ∪ L.upper, L.first, L.pivot, L.marker, ?_, ?_,
    Finset.mem_union_right _ L.first_lower, Finset.mem_union_right _ L.first_upper,
    Finset.mem_union_right _ L.pivot_lower, Finset.mem_union_right _ L.pivot_upper,
    L.first_lt_pivot, by rw [hfilterE, hEcard], by rw [hfilterF, hFcard], ?_, ?_, ?_,
    ?_, ?_, ⟨L.marker_fresh.1, (hfB (r + t)).trans hCmarker⟩⟩⟩
  · rw [Finset.card_union_of_disjoint hdisE, hEcard, L.lower_card]
    omega
  · rw [Finset.card_union_of_disjoint hdisF, hFcard, L.upper_card]
    omega
  · intro x hx hxb y hy hyb
    have hxE : x ∈ E := hfilterE ▸ Finset.mem_filter.mpr ⟨hx, hxb⟩
    have hyF : y ∈ F := hfilterF ▸ Finset.mem_filter.mpr ⟨hy, hyb⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxE
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hyF
    exact hf (by have := Finset.mem_range.mp hi; omega)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl ((hE x hx).2.2.trans hCfirst).le
    · rcases L.lower_gap x hx with he | hle
      · exact Or.inl he.le
      · exact Or.inr hle
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ((hF x hx).2.2.trans (hCfirst.trans L.first_lt_pivot)).le
    · exact (L.upper_bounds x hx).2
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨(hE x hx).1, (hE x hx).2.1, (hE x hx).2.2.trans hCmarker⟩
    · have h := L.lower_fresh x hx
      exact ⟨h.1, (hfB (r + t)).trans h.2.1, h.2.2⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨(hF x hx).1, (hF x hx).2.1, (hF x hx).2.2.trans hCmarker⟩
    · have h := L.upper_fresh x hx
      exact ⟨h.1, (hfB (r + t)).trans h.2.1, h.2.2⟩

variable {H : Set ℕ} {B p q r t : ℕ}

theorem gamma_next_lower (L : PreliminaryPivotLabels H B p q r t) (x : ℕ)
    (hx : x ∈ L.lower) (hgt : L.beta < x) : L.gamma ≤ x :=
  (L.lower_gap x hx).resolve_left (not_le_of_gt hgt)

theorem upper_sup (L : PreliminaryPivotLabels H B p q r t) : L.upper.sup id = L.gamma :=
  le_antisymm (Finset.sup_le fun x hx => L.upper_le_gamma x hx)
    (Finset.le_sup (f := id) L.gamma_upper)

#print axioms exists_of_infinite
#print axioms gamma_next_lower
#print axioms upper_sup

end PreliminaryPivotLabels

end Erdos591.Positive.Game

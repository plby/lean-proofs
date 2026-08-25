import StackExchange.Puzzling139335.JordanRegion
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Basic

/-!
# Actual bottom-edge coverage from finite contacts

A closed piece owns a whole bottom interval when the other substantial
piece is excluded from its open part and the two remaining pieces have
only finitely many bottom-line contacts. The proof removes those finite
exceptions in the real parameter interval and then uses closedness. No
convex-hull replacement or boundary regularity is involved.
-/

open Set

namespace Puzzling139335.N4Midline

noncomputable section

/-- A continuous map lands in a closed set on a closed real interval if
it does so throughout the open interval except at finitely many points. -/
theorem mapsTo_Icc_of_finite_exceptions {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} (hf : Continuous f) {P : Set X} (hP : IsClosed P)
    {a b : ℝ} (hab : a < b) {bad : Set ℝ} (hbad : bad.Finite)
    (hgood : ∀ x ∈ Ioo a b, x ∉ bad → f x ∈ P) :
    MapsTo f (Icc a b) P := by
  have hdense : Dense badᶜ := by
    simpa only [sdiff_eq, univ_inter] using
      (dense_univ : Dense (univ : Set ℝ)).sdiff_finite hbad
  have hsub : Ioo a b ∩ badᶜ ⊆ f ⁻¹' P := by
    intro x hx
    exact hgood x hx.1 hx.2
  have hopen : Ioo a b ⊆ f ⁻¹' P :=
    (hdense.open_subset_closure_inter isOpen_Ioo).trans
      (closure_minimal hsub (hP.preimage hf))
  have hclosed := closure_minimal hopen (hP.preimage hf)
  rw [closure_Ioo hab.ne] at hclosed
  exact hclosed

/-- Generic four-set coverage lemma for an actual bottom-edge interval. -/
theorem bottom_interval_subset_of_finite_contacts
    {P Q R S : Set Plane} (hP : IsClosed P)
    (hcover : ∀ p ∈ unitSquare, p ∈ P ∨ p ∈ Q ∨ p ∈ R ∨ p ∈ S)
    {a b : ℝ} (hab : a < b) (hinterval : Icc a b ⊆ Icc (0 : ℝ) 1)
    (hQ : ∀ p ∈ Q, p 1 = 0 → p 0 ∉ Ioo a b)
    (hR : (R ∩ {p : Plane | p 1 = 0}).Finite)
    (hS : (S ∩ {p : Plane | p 1 = 0}).Finite) :
    {p : Plane | p 0 ∈ Icc a b ∧ p 1 = 0} ⊆ P := by
  let f : ℝ → Plane := fun x => !₂[x, 0]
  have hf : Continuous f := by dsimp [f]; fun_prop
  let bad : Set ℝ :=
    (fun p : Plane => p 0) '' (R ∩ {p : Plane | p 1 = 0}) ∪
      (fun p : Plane => p 0) '' (S ∩ {p : Plane | p 1 = 0})
  have hbad : bad.Finite := (hR.image _).union (hS.image _)
  have hgood : ∀ x ∈ Ioo a b, x ∉ bad → f x ∈ P := by
    intro x hx hxnot
    have hxsq : f x ∈ unitSquare := by
      exact ⟨hinterval ⟨hx.1.le, hx.2.le⟩, by norm_num [f]⟩
    rcases hcover (f x) hxsq with hp | hq | hr | hs
    · exact hp
    · exact (hQ (f x) hq rfl hx).elim
    · apply False.elim
      apply hxnot
      exact Or.inl ⟨f x, ⟨hr, rfl⟩, rfl⟩
    · apply False.elim
      apply hxnot
      exact Or.inr ⟨f x, ⟨hs, rfl⟩, rfl⟩
  have hmaps := mapsTo_Icc_of_finite_exceptions hf hP hab hbad hgood
  intro p hp
  have hmem : f (p 0) ∈ P := hmaps hp.1
  have heq : f (p 0) = p := by
    ext i
    fin_cases i
    · rfl
    · exact hp.2.symm
  rwa [heq] at hmem

/-- The left half of the actual bottom edge belongs to `P` if `Q` lies
on the right and the two other pieces have finite bottom contacts. -/
theorem bottom_left_subset_of_finite_contacts
    {P Q R S : Set Plane} (hP : IsClosed P)
    (hcover : ∀ p ∈ unitSquare, p ∈ P ∨ p ∈ Q ∨ p ∈ R ∨ p ∈ S)
    (hQ : Q ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 0})
    (hR : (R ∩ {p : Plane | p 1 = 0}).Finite)
    (hS : (S ∩ {p : Plane | p 1 = 0}).Finite) :
    {p : Plane | p 0 ∈ Icc (0 : ℝ) (1 / 2) ∧ p 1 = 0} ⊆ P := by
  apply bottom_interval_subset_of_finite_contacts hP hcover (by norm_num) ?_ ?_ hR hS
  · intro x hx
    exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩
  · intro p hp _ hx
    have hr := hQ hp
    exact (not_lt_of_ge hr) hx.2

/-- The right half of the actual bottom edge belongs to `Q` if `P` lies
on the left and the two other pieces have finite bottom contacts. -/
theorem bottom_right_subset_of_finite_contacts
    {P Q R S : Set Plane} (hQ : IsClosed Q)
    (hcover : ∀ p ∈ unitSquare, p ∈ P ∨ p ∈ Q ∨ p ∈ R ∨ p ∈ S)
    (hP : P ⊆ {p : Plane | p 0 ≤ (1 / 2 : ℝ)})
    (hR : (R ∩ {p : Plane | p 1 = 0}).Finite)
    (hS : (S ∩ {p : Plane | p 1 = 0}).Finite) :
    {p : Plane | p 0 ∈ Icc (1 / 2 : ℝ) 1 ∧ p 1 = 0} ⊆ Q := by
  have hcover' : ∀ p ∈ unitSquare, p ∈ Q ∨ p ∈ P ∨ p ∈ R ∨ p ∈ S := by
    intro p hp
    rcases hcover p hp with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  apply bottom_interval_subset_of_finite_contacts hQ hcover' (by norm_num) ?_ ?_ hR hS
  · intro x hx
    exact ⟨le_trans (by norm_num) hx.1, hx.2⟩
  · intro p hp _ hx
    have hl := hP hp
    exact (not_lt_of_ge hl) hx.1

end

end Puzzling139335.N4Midline

namespace Puzzling139335.SquareDissection

/-- Four named indices covering all indices give the corresponding
four-way actual-piece coverage. Distinctness is unnecessary here. -/
theorem four_piece_coverage (d : SquareDissection) (i j k l : Fin 4)
    (henum : ∀ m : Fin 4, m = i ∨ m = j ∨ m = k ∨ m = l) :
    ∀ p ∈ unitSquare,
      p ∈ d.piece i ∨ p ∈ d.piece j ∨ p ∈ d.piece k ∨ p ∈ d.piece l := by
  intro p hp
  obtain ⟨m, hm⟩ := d.exists_piece_mem hp
  rcases henum m with rfl | rfl | rfl | rfl
  · exact Or.inl hm
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (Or.inl hm))
  · exact Or.inr (Or.inr (Or.inr hm))

theorem bottom_left_subset_piece_of_finite_contacts (d : SquareDissection)
    (i j k l : Fin 4) (henum : ∀ m : Fin 4, m = i ∨ m = j ∨ m = k ∨ m = l)
    (hj : d.piece j ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 0})
    (hk : (d.piece k ∩ {p : Plane | p 1 = 0}).Finite)
    (hl : (d.piece l ∩ {p : Plane | p 1 = 0}).Finite) :
    {p : Plane | p 0 ∈ Icc (0 : ℝ) (1 / 2) ∧ p 1 = 0} ⊆ d.piece i :=
  N4Midline.bottom_left_subset_of_finite_contacts (d.jordan i).isClosed
    (d.four_piece_coverage i j k l henum) hj hk hl

theorem bottom_right_subset_piece_of_finite_contacts (d : SquareDissection)
    (i j k l : Fin 4) (henum : ∀ m : Fin 4, m = i ∨ m = j ∨ m = k ∨ m = l)
    (hi : d.piece i ⊆ {p : Plane | p 0 ≤ (1 / 2 : ℝ)})
    (hk : (d.piece k ∩ {p : Plane | p 1 = 0}).Finite)
    (hl : (d.piece l ∩ {p : Plane | p 1 = 0}).Finite) :
    {p : Plane | p 0 ∈ Icc (1 / 2 : ℝ) 1 ∧ p 1 = 0} ⊆ d.piece j :=
  N4Midline.bottom_right_subset_of_finite_contacts (d.jordan j).isClosed
    (d.four_piece_coverage i j k l henum) hi hk hl

end Puzzling139335.SquareDissection

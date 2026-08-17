import Mathlib

open scoped BigOperators
open Filter Finset Asymptotics

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos735

abbrev Point := EuclideanSpace ℝ (Fin 2)

def orientationDet (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

def Collinear3 (p q r : Point) : Prop := orientationDet p q r = 0

def OrdinaryPair (S : Finset Point) (p q : Point) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧
    ∀ r ∈ S, Collinear3 p q r → r = p ∨ r = q

lemma orientationDet_swap (p q r : Point) :
    orientationDet q p r = -orientationDet p q r := by
  simp [orientationDet]
  ring

lemma collinear3_swap (p q r : Point) : Collinear3 q p r ↔ Collinear3 p q r := by
  unfold Collinear3
  rw [orientationDet_swap]
  constructor
  · exact neg_eq_zero.mp
  · exact neg_eq_zero.mpr

lemma ordinaryPair_symm {S : Finset Point} {p q : Point} :
    OrdinaryPair S p q ↔ OrdinaryPair S q p := by
  constructor
  · rintro ⟨hp, hq, hpq, hline⟩
    refine ⟨hq, hp, hpq.symm, ?_⟩
    intro r hr hcol
    rcases hline r hr ((collinear3_swap p q r).mp hcol) with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro ⟨hq, hp, hqp, hline⟩
    refine ⟨hp, hq, hqp.symm, ?_⟩
    intro r hr hcol
    rcases hline r hr ((collinear3_swap q p r).mp hcol) with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

def ordinaryGraph (S : Finset Point) : SimpleGraph {x // x ∈ S} where
  Adj p q := OrdinaryPair S p.1 q.1
  symm := ⟨fun p q h ↦
    (ordinaryPair_symm (S := S) (p := p.1) (q := q.1)).mp h⟩
  loopless := ⟨fun _ h ↦ h.2.2.1 rfl⟩

noncomputable def ordinaryLineCount (S : Finset Point) : ℕ := by
  classical
  exact (ordinaryGraph S).edgeFinset.card

end Erdos735

open Erdos735

namespace Erdos960

abbrev Point := Erdos735.Point

end Erdos960

namespace Erdos960

def NoKCollinear (A : Finset Point) (k : ℕ) : Prop :=
  ∀ B : Finset Point, B ⊆ A → B.card = k → ¬ Collinear ℝ (B : Set Point)

end Erdos960

namespace Erdos960

def HasOrdinaryClique (A : Finset Point) (r : ℕ) : Prop :=
  ∃ B : Finset Point, B ⊆ A ∧ B.card = r ∧
    ∀ p ∈ B, ∀ q ∈ B, p ≠ q → OrdinaryPair A p q

end Erdos960

namespace Erdos960

def ForcesOrdinaryClique (r k n t : ℕ) : Prop :=
  ∀ A : Finset Point, A.card = n → NoKCollinear A k →
    t ≤ ordinaryLineCount A → HasOrdinaryClique A r

end Erdos960

namespace Erdos960

noncomputable def f (r k n : ℕ) : ℕ :=
  sInf {t : ℕ | ForcesOrdinaryClique r k n t}

end Erdos960

namespace Erdos960

theorem erdos960_resolution {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) :
    (∀ n : ℕ, 72 ≤ n →
      (n : ℝ) ^ 2 / 12 - (10 / 3 : ℝ) * n + 1 ≤ (f r k n : ℝ) ∧
      (f r k n : ℝ) ≤
        (1 - 1 / ((r - 1 : ℕ) : ℝ)) * (n : ℝ) ^ 2 / 2 + 1) ∧
    ¬ Asymptotics.IsLittleO atTop (fun n : ℕ ↦ (f r k n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ 2) ∧
    ¬ Asymptotics.IsBigO atTop (fun n : ℕ ↦ (f r k n : ℝ))
      (fun n : ℕ ↦ (n : ℝ)) := by
  sorry

end Erdos960

end

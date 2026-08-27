import Arxiv.Arxiv2411_18291.FiniteHistoryProbability

/-! # Agreement of trajectory measures on events determined by a finite prefix -/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

def extendHistory (start : S) {n : ℕ} (h : History S n) (i : ℕ) : S :=
  if hi : i ≤ n then h ⟨i, mem_Iic.mpr hi⟩ else start

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem frestrictLe_extendHistory (start : S) {n : ℕ} (h : History S n) :
    frestrictLe n (extendHistory start h) = h := by
  funext i
  simp only [frestrictLe_apply, extendHistory, dif_pos (mem_Iic.mp i.property)]

theorem probability_event_eq_of_prefix_agreement (start : S)
    (p q : (n : ℕ) → History S n → PMF S) (n : ℕ) (Q : (ℕ → S) → Prop)
    (hQ : ∀ ω ω', frestrictLe n ω = frestrictLe n ω' → (Q ω ↔ Q ω'))
    (hpq : ∀ ω, Q ω → ∀ i < n, p i (frestrictLe i ω) = q i (frestrictLe i ω)) :
    probability start p {ω | Q ω} = probability start q {ω | Q ω} := by
  let E : Set (History S n) := {h | Q (extendHistory start h)}
  have hevent : {ω | Q ω} = frestrictLe n ⁻¹' E := by
    ext ω
    exact hQ ω (extendHistory start (frestrictLe n ω)) (frestrictLe_extendHistory _ _).symm
  rw [hevent]
  apply history_event_probability_eq_of_transitions start p q n E
  intro h hh i hi
  have heq : frestrictLe i (extendHistory start h) =
      frestrictLe₂ (π := fun _ => S) hi.le h := by
    calc
      _ = frestrictLe₂ (π := fun _ => S) hi.le
          (frestrictLe n (extendHistory start h)) := rfl
      _ = _ := by rw [frestrictLe_extendHistory]
  simpa only [heq] using hpq (extendHistory start h) hh i hi

end Arxiv2411_18291.FiniteHistoryProcess

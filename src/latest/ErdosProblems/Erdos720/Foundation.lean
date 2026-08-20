import Util.Ramsey

/-! Foundational size-Ramsey definitions for Erdős Problem 720. -/

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos720

open SimpleGraph

/-- A host graph arrows a target graph if every red/blue edge-colouring
of the host contains a monochromatic copy of the target. -/
def Arrows {V W : Type*} (H : SimpleGraph V) (F : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph V, R ≤ H → F ⊑ R ∨ F ⊑ H \ R

/-- There is a finite host with exactly `m` edges which arrows `F`. -/
def IsSizeRamseyWitness {W : Type*} (F : SimpleGraph W) (m : ℕ) : Prop :=
  ∃ N : ℕ, ∃ H : SimpleGraph (Fin N), Nat.card H.edgeSet = m ∧ Arrows H F

lemma exists_sizeRamseyWitness {W : Type*} [Fintype W] (F : SimpleGraph W) :
    ∃ m, IsSizeRamseyWitness F m := by
  classical
  let k := Fintype.card W
  let N := Ramsey.ramseyNumber k k
  let H : SimpleGraph (Fin N) := ⊤
  have hFtop : F ⊑ (⊤ : SimpleGraph (Fin k)) := by
    let e : W ≃ Fin k := Fintype.equivFin W
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    intro a b hab
    simpa using hab.ne
  refine ⟨Nat.card H.edgeSet, N, H, rfl, ?_⟩
  intro R hRH
  have hRamsey : ¬ (R.CliqueFree k ∧ R.IndepSetFree k) :=
    Ramsey.ramseyNumber_spec k k R
  rcases not_and_or.mp hRamsey with hClique | hIndep
  · left
    have htop : (⊤ : SimpleGraph (Fin k)) ⊑ R := by
      rw [SimpleGraph.cliqueFree_iff] at hClique
      exact not_isEmpty_iff.mp hClique
    exact hFtop.trans htop
  · right
    have htop : (⊤ : SimpleGraph (Fin k)) ⊑ Rᶜ := by
      rw [← SimpleGraph.cliqueFree_compl, SimpleGraph.cliqueFree_iff] at hIndep
      exact not_isEmpty_iff.mp hIndep
    have hF : F ⊑ Rᶜ := hFtop.trans htop
    simpa [H] using hF

/-- The size Ramsey number of a finite simple graph. -/
def sizeRamsey {W : Type*} [Fintype W] (F : SimpleGraph W) : ℕ :=
  by
    classical
    exact Nat.find (exists_sizeRamseyWitness F)

lemma sizeRamsey_spec {W : Type*} [Fintype W] (F : SimpleGraph W) :
    IsSizeRamseyWitness F (sizeRamsey F) := by
  classical
  exact Nat.find_spec (exists_sizeRamseyWitness F)

lemma sizeRamsey_le_of_witness {W : Type*} [Fintype W] {F : SimpleGraph W} {m : ℕ}
    (h : IsSizeRamseyWitness F m) : sizeRamsey F ≤ m := by
  classical
  exact Nat.find_min' (exists_sizeRamseyWitness F) h

end Erdos720

import ErdosProblems.Erdos547.ShrubIndex
import ErdosProblems.Erdos547.ShrubPartSizes

/-!
# The canonical shrub indices have the prescribed four part totals
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

theorem shrubColour_eq_iff (S : ↥P.shrubs) (c : Fin 2) :
    P.shrubColour S = c ↔ S.val ∈ P.shrubsOfColour c := by
  constructor
  · intro h
    rw [← h]
    exact P.mem_shrubsOfColour S
  · intro h
    exact ((P.exists_unique_shrub_colour S.property).choose_spec.2 c h).symm

def indexOfColour (c : Fin 2) (S : ↥(P.shrubsOfColour c)) : ↥P.shrubs :=
  ⟨S.val, (Finset.mem_filter.mp S.property).1⟩

open scoped Classical in
theorem sum_indexed_colour {M : Type*} [AddCommMonoid M] (c : Fin 2) (f : ↥P.shrubs → M) :
    (∑ S : ↥(P.shrubsOfColour c), f (P.indexOfColour c S)) =
      ∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter (fun S ↦ P.shrubColour S = c), f S := by
  classical
  apply Finset.sum_bij (fun S _ ↦ P.indexOfColour c S)
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (P.shrubColour_eq_iff _ c).mpr S.property⟩
  · intro S _ A _ he
    exact Subtype.ext (congrArg (fun z : ↥P.shrubs ↦ z.val) he)
  · intro S hS
    have hc := (P.shrubColour_eq_iff S c).mp (Finset.mem_filter.mp hS).2
    exact ⟨⟨S.val, hc⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    rfl

open scoped Classical in
theorem sum_nearPart_colour (c : Fin 2) :
    (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter (fun S ↦ P.shrubColour S = c),
      (P.nearPart S).card) = (P.nearVertices c).card := by
  rw [← P.sum_indexed_colour c (fun S ↦ (P.nearPart S).card)]
  calc
    _ = ∑ S : ↥(P.shrubsOfColour c), (S.val.filter (fun v ↦ col v ≠ c)).card := by
      apply Finset.sum_congr rfl
      intro S _
      have hc := (P.shrubColour_eq_iff (P.indexOfColour c S) c).mpr S.property
      simp only [indexOfColour] at hc
      simp only [nearPart, indexOfColour, hc]
    _ = _ := P.sum_near_shrub_sizes c

open scoped Classical in
theorem sum_farPart_colour (c : Fin 2) :
    (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter (fun S ↦ P.shrubColour S = c),
      (P.farPart S).card) = (P.farVertices c).card := by
  rw [← P.sum_indexed_colour c (fun S ↦ (P.farPart S).card)]
  calc
    _ = ∑ S : ↥(P.shrubsOfColour c), (S.val.filter (fun v ↦ col v = c)).card := by
      apply Finset.sum_congr rfl
      intro S _
      have hc := (P.shrubColour_eq_iff (P.indexOfColour c S) c).mpr S.property
      simp only [indexOfColour] at hc
      simp only [farPart, indexOfColour, hc]
    _ = _ := P.sum_far_shrub_sizes c

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.sum_nearPart_colour
#print axioms Erdos547.FineTreePartition.sum_farPart_colour

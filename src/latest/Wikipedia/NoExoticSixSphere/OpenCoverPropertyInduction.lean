import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite-union induction with overlap hypotheses

A property which glues across a binary union when it holds on both
pieces and their intersection holds on finite unions of a collection
closed under binary intersections. The induction also applies to the
intersections with the next piece; no union-intersection hypothesis is
silently omitted.
-/

namespace NoExoticSixSphere.OpenCoverProperty

variable {L : Type*} [DistribLattice L] [OrderBot L]
  (P B : L → Prop) (hbot : P ⊥) (hbasic : ∀ U, B U → P U)
  (hinter : ∀ U V, B U → B V → B (U ⊓ V))
  (hunion : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))

include hbot hbasic hinter hunion

/-- Finite unions are proved by induction simultaneously for every family of basic opens. -/
theorem finite_sup {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, B (f i)) :
    P (s.sup f) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simpa only [Finset.sup_empty] using hbot
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs (j : ι) (hj : j ∈ s) : B (f j) := hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sup_insert]
    apply hunion (f i) (s.sup f) (hbasic _ hfi) (ih f hfs)
    rw [Finset.sup_inf_distrib_left]
    exact ih (fun j => f i ⊓ f j) (fun j hj => hinter _ _ hfi (hfs j hj))

end NoExoticSixSphere.OpenCoverProperty

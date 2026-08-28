import ErdosProblems.Erdos577.Basic

/-! Injective finite vertex tuples and their disjoint concatenation. -/

namespace Erdos577

open Finset Function

variable {V : Type*} [DecidableEq V] {m n : ℕ}

def tupleSupport (e : Fin n ↪ V) : Finset V := univ.image e

@[simp] lemma mem_tupleSupport (e : Fin n ↪ V) (v : V) :
    v ∈ tupleSupport e ↔ ∃ i, e i = v := by simp [tupleSupport]

@[simp] lemma card_tupleSupport (e : Fin n ↪ V) : (tupleSupport e).card = n := by
  rw [tupleSupport, card_image_of_injective _ e.injective]
  simp

/-- Concatenation retains injectivity because the two actual supports are disjoint. -/
def joinTuples (a : Fin m ↪ V) (b : Fin n ↪ V)
    (h : Disjoint (tupleSupport a) (tupleSupport b)) : Fin (m + n) ↪ V :=
  finSumFinEquiv.symm.toEmbedding.trans {
    toFun := Sum.elim a b
    inj' := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact congrArg Sum.inl (a.injective hij)
        | inr j =>
          exact False.elim ((disjoint_left.mp h)
            ((mem_tupleSupport a _).mpr ⟨i, rfl⟩)
            ((mem_tupleSupport b _).mpr ⟨j, hij.symm⟩))
      | inr i =>
        cases j with
        | inl j =>
          exact False.elim ((disjoint_left.mp h)
            ((mem_tupleSupport a _).mpr ⟨j, hij.symm⟩)
            ((mem_tupleSupport b _).mpr ⟨i, rfl⟩))
        | inr j => exact congrArg Sum.inr (b.injective hij) }

@[simp] lemma joinTuples_left (a : Fin m ↪ V) (b : Fin n ↪ V)
    (h : Disjoint (tupleSupport a) (tupleSupport b)) (i : Fin m) :
    joinTuples a b h (Fin.castAdd n i) = a i := by
  change Sum.elim a b (finSumFinEquiv.symm (Fin.castAdd n i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] lemma joinTuples_right (a : Fin m ↪ V) (b : Fin n ↪ V)
    (h : Disjoint (tupleSupport a) (tupleSupport b)) (i : Fin n) :
    joinTuples a b h (Fin.natAdd m i) = b i := by
  change Sum.elim a b (finSumFinEquiv.symm (Fin.natAdd m i)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

lemma tupleSupport_joinTuples (a : Fin m ↪ V) (b : Fin n ↪ V)
    (h : Disjoint (tupleSupport a) (tupleSupport b)) :
    tupleSupport (joinTuples a b h) = tupleSupport a ∪ tupleSupport b := by
  ext v
  simp only [mem_tupleSupport, mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := m) (n := n)).surjective i
    cases j with
    | inl j => exact Or.inl ⟨j, (joinTuples_left a b h j).symm⟩
    | inr j => exact Or.inr ⟨j, (joinTuples_right a b h j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, joinTuples_left a b h i⟩
    · exact ⟨Fin.natAdd m i, joinTuples_right a b h i⟩

def singletonTuple (v : V) : Fin 1 ↪ V where
  toFun := fun _ ↦ v
  inj' := fun _ _ _ ↦ Subsingleton.elim _ _

@[simp] lemma tupleSupport_singleton (v : V) : tupleSupport (singletonTuple v) = {v} := by
  change univ.image (fun _ : Fin 1 ↦ v) = {v}
  simp

end Erdos577

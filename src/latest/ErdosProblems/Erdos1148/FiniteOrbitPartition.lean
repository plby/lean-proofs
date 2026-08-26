import ErdosProblems.Erdos1148.FinitePartitionEntropy
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Finite measurable orbit partitions -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

structure FiniteMeasurablePartition (X ι : Type*) [MeasurableSpace X] where
  atom : ι → Set X
  measurable_atom : ∀ i, MeasurableSet (atom i)
  disjoint_atom : Pairwise (Disjoint on atom)
  iUnion_atom : (⋃ i, atom i) = Set.univ

namespace FiniteMeasurablePartition

variable {X ι : Type*} [MeasurableSpace X]

def orbitAtom (P : FiniteMeasurablePartition X ι) (f : X → X)
    (n : ℕ) (w : Fin n → ι) : Set X :=
  {x | ∀ j : Fin n, f^[j.val] x ∈ P.atom (w j)}

lemma orbitAtom_eq_iInter (P : FiniteMeasurablePartition X ι) (f : X → X)
    (n : ℕ) (w : Fin n → ι) :
    P.orbitAtom f n w = ⋂ j : Fin n, f^[j.val] ⁻¹' P.atom (w j) := by
  ext x
  simp only [orbitAtom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]

lemma measurableSet_orbitAtom (P : FiniteMeasurablePartition X ι)
    {f : X → X} (hf : Measurable f) (n : ℕ) (w : Fin n → ι) :
    MeasurableSet (P.orbitAtom f n w) := by
  simpa only [orbitAtom, Set.setOf_forall, Set.preimage] using
    MeasurableSet.iInter (fun j => (P.measurable_atom (w j)).preimage (hf.iterate j.val))

lemma pairwise_disjoint_orbitAtom (P : FiniteMeasurablePartition X ι)
    (f : X → X) (n : ℕ) : Pairwise (Disjoint on P.orbitAtom f n) := by
  intro v w hvw
  apply Set.disjoint_left.mpr
  intro x hxv hxw
  have heq : v = w := by
    funext j
    by_contra hne
    exact Set.disjoint_left.mp (P.disjoint_atom hne) (hxv j) (hxw j)
  exact hvw heq

lemma iUnion_orbitAtom (P : FiniteMeasurablePartition X ι)
    (f : X → X) (n : ℕ) : (⋃ w : Fin n → ι, P.orbitAtom f n w) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hlabel (j : Fin n) : ∃ a, f^[j.val] x ∈ P.atom a := by
    apply Set.mem_iUnion.mp
    rw [P.iUnion_atom]
    exact Set.mem_univ _
  choose w hw using hlabel
  exact Set.mem_iUnion.mpr ⟨w, hw⟩

def orbitPartition (P : FiniteMeasurablePartition X ι)
    {f : X → X} (hf : Measurable f) (n : ℕ) :
    FiniteMeasurablePartition X (Fin n → ι) where
  atom := P.orbitAtom f n
  measurable_atom := P.measurableSet_orbitAtom hf n
  disjoint_atom := P.pairwise_disjoint_orbitAtom f n
  iUnion_atom := P.iUnion_orbitAtom f n

lemma orbitAtom_append (P : FiniteMeasurablePartition X ι) (f : X → X)
    {n m : ℕ} (v : Fin n → ι) (w : Fin m → ι) :
    P.orbitAtom f (n + m) (Fin.append v w) =
      P.orbitAtom f n v ∩ f^[n] ⁻¹' P.orbitAtom f m w := by
  ext x
  change (∀ j : Fin (n + m), f^[j.val] x ∈ P.atom (Fin.append v w j)) ↔
    (∀ j : Fin n, f^[j.val] x ∈ P.atom (v j)) ∧
      (∀ j : Fin m, f^[j.val] (f^[n] x) ∈ P.atom (w j))
  constructor
  · intro h
    constructor
    · intro j
      simpa only [Fin.val_castAdd, Fin.append_left] using h (Fin.castAdd m j)
    · intro j
      simpa only [Fin.val_natAdd, Fin.append_right, Nat.add_comm n j.val,
        Function.iterate_add_apply] using h (Fin.natAdd n j)
  · rintro ⟨hv, hw⟩ j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simpa only [Fin.val_castAdd, Fin.append_left] using hv k
    · intro k
      simpa only [Fin.val_natAdd, Fin.append_right, Nat.add_comm n k.val,
        Function.iterate_add_apply] using hw k

end FiniteMeasurablePartition

theorem finitePartitionEntropy_reindex {X ι κ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (μ : Measure X) (s : κ → Set X) (e : ι ≃ κ) :
    finitePartitionEntropy μ (fun i => s (e i)) = finitePartitionEntropy μ s := by
  exact e.sum_comp (fun k => Real.negMulLog (μ.real (s k)))

end Erdos1148.DukeArithmetic

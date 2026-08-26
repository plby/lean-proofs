/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingBranchStep

/-!
# Consecutive pending branches with one newly chosen outer root

The threshold orientation is indexed by the literal branch order. This
file iterates a sequential step over an interval of that order, without
re-enumerating a selected finset. The external parent is fixed throughout
the interval, and every earlier component copy is preserved exactly.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingInterval

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58OnlineOwnerReparent

/-- Literal initial segment, also defined at the empty and full cutoffs. -/
def branchPrefix {b : ℕ} (n : ℕ) : Finset (Fin b) :=
  Finset.univ.filter fun i => i.val < n

@[simp] theorem mem_branchPrefix {b n : ℕ} (i : Fin b) :
    i ∈ branchPrefix n ↔ i.val < n := by
  simp [branchPrefix]

theorem branchPrefix_mono {b a c : ℕ} (h : a ≤ c) :
    (branchPrefix a : Finset (Fin b)) ⊆ branchPrefix c := by
  intro i hi
  exact mem_branchPrefix i |>.mpr ((mem_branchPrefix i |>.mp hi).trans_le h)

@[simp] theorem branchPrefix_zero (b : ℕ) :
    (branchPrefix 0 : Finset (Fin b)) = ∅ := by
  ext i
  simp

@[simp] theorem branchPrefix_full (b : ℕ) :
    (branchPrefix b : Finset (Fin b)) = Finset.univ := by
  ext i
  simp [i.isLt]

theorem branchPrefix_eq_Iio {b : ℕ} (i : Fin b) :
    branchPrefix i.val = Finset.Iio i := by
  ext j
  simp

theorem branchPrefix_succ {b : ℕ} (i : Fin b) :
    branchPrefix (i.val + 1) = Finset.Iio i ∪ {i} := by
  ext j
  simp only [mem_branchPrefix, Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton]
  constructor
  · intro h
    by_cases hlt : j.val < i.val
    · exact Or.inl hlt
    · exact Or.inr (Fin.ext (by omega))
  · rintro (h | rfl)
    · exact Nat.lt_succ_of_lt h
    · exact Nat.lt_succ_self _

variable {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (F : OrderedRootedForest b) (H : SimpleGraph V)
variable (parent : Fin b → V) (orient : Fin b → Fin 2 ≃ Fin 2)
variable (available : Fin 2 → Finset V)

/-- Change only the proof of the selected set. The component copy is
literally the old component copy, with a transported membership proof. -/
def castPartialSelected {s t : Finset (Fin b)} (hst : s = t)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available s) :
    PartialDynamicAttachedForestEmbedding F H parent orient available t where
  forestCopy := {
    componentCopy := fun i hi => E.forestCopy.componentCopy i (hst.symm ▸ hi)
    disjoint_ranges := fun i hi j hj hne => E.forestCopy.disjoint_ranges i
      (hst.symm ▸ hi) j (hst.symm ▸ hj) hne }
  attach := fun i hi => E.attach i (hst.symm ▸ hi)
  map_side := fun i hi a => E.map_side i (hst.symm ▸ hi) a

@[simp] theorem castPartialSelected_componentCopy {s t : Finset (Fin b)} (hst : s = t)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available s)
    (i : Fin b) (hi : i ∈ t) :
    (castPartialSelected F H parent orient available hst E).forestCopy.componentCopy i hi =
      E.forestCopy.componentCopy i (hst.symm ▸ hi) := rfl

/-- A local branch-step certificate for a single chosen root. It is an
internal induction interface, not a replacement for proving root access. -/
def BranchStepAccess (z : V) : Prop :=
  ∀ (i : Fin b) (p : Fin b → V)
    (E : PartialDynamicAttachedForestEmbedding F H p orient available (Finset.Iio i)),
    ∃ E' : PartialDynamicAttachedForestEmbedding F H (Function.update p i z) orient available
        (Finset.Iio i ∪ {i}),
      ∀ j hj, E'.forestCopy.componentCopy j (Finset.mem_union_left _ hj) =
        E.forestCopy.componentCopy j hj

/-- Extend a consecutive branch interval whose outer root has just been
chosen. Empty intervals are allowed. Only this root's step certificate is
needed, and the maps of all branches before the interval remain unchanged. -/
theorem exists_interval_extension (z : V)
    (hstep : BranchStepAccess F H orient available z)
    (lo hi : ℕ) (hle : lo ≤ hi) (hhi : hi ≤ b)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available (branchPrefix lo))
    (hparent : ∀ i : Fin b, lo ≤ i.val → i.val < hi → parent i = z) :
    ∃ E' : PartialDynamicAttachedForestEmbedding F H parent orient available (branchPrefix hi),
      ∀ j hj, E'.forestCopy.componentCopy j (branchPrefix_mono hle hj) =
        E.forestCopy.componentCopy j hj := by
  induction hi with
  | zero =>
      have hlo : lo = 0 := Nat.eq_zero_of_le_zero hle
      subst lo
      exact ⟨E, fun _ _ => rfl⟩
  | succ k ih =>
      by_cases heq : lo = k + 1
      · subst lo
        exact ⟨E, fun _ _ => rfl⟩
      have hlok : lo ≤ k := by omega
      have hk : k < b := by omega
      obtain ⟨Ek, hEk⟩ := ih hlok (by omega)
        (fun i hli hik => hparent i hli (Nat.lt_succ_of_lt hik))
      let i : Fin b := ⟨k, hk⟩
      have hpk : branchPrefix k = Finset.Iio i := branchPrefix_eq_Iio i
      let Ei := castPartialSelected F H parent orient available hpk Ek
      obtain ⟨Enew, hnew⟩ := hstep i parent Ei
      have hpi : parent i = z := hparent i hlok (Nat.lt_succ_self k)
      have hup : ∀ j, Function.update parent i z j = parent j := by
        intro j
        rw [← hpi, Function.update_eq_self]
      let Eback := partialReparent F H (Function.update parent i z) parent orient available
        (Finset.Iio i ∪ {i}) Enew (fun j _ => (hup j).symm)
      let Eout := castPartialSelected F H parent orient available
        (branchPrefix_succ i).symm Eback
      refine ⟨Eout, ?_⟩
      intro j hj
      have hjk : j ∈ branchPrefix k := branchPrefix_mono hlok hj
      have hji : j ∈ Finset.Iio i := hpk ▸ hjk
      change Enew.forestCopy.componentCopy j _ = E.forestCopy.componentCopy j hj
      exact (hnew j hji).trans (hEk j hj)

end Erdos547b.ZhaoSourcePendingInterval

#print axioms Erdos547b.ZhaoSourcePendingInterval.castPartialSelected
#print axioms Erdos547b.ZhaoSourcePendingInterval.exists_interval_extension

import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Boolean presentation of a whole matching-edge split

`false` is assigned the selected family `K₀` and head `X`; `true` is assigned
its complement and head `Y`.  These definitions are deliberately tiny, but
their simp lemmas remove all owner/head case splits from the final embedding
assembly.
-/

open Finset

namespace Erdos550

noncomputable def offTuranBoolHead
    {ι : Type*} (X Y : ι) (b : Bool) : ι :=
  if b then Y else X

noncomputable def offTuranBoolOtherHead
    {ι : Type*} (X Y : ι) (b : Bool) : ι :=
  if b then X else Y

noncomputable def offTuranBoolEdges
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) (b : Bool) : Finset κ :=
  if b then Finset.univ \ K₀ else K₀

noncomputable def offTuranAssignedHead
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) (X Y : ι) (k : κ) : ι :=
  if k ∈ K₀ then X else Y

noncomputable def offTuranAssignedBool
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) (k : κ) : Bool :=
  if k ∈ K₀ then false else true

@[simp] lemma offTuranBoolHead_false
    {ι : Type*} (X Y : ι) :
    offTuranBoolHead X Y false = X := by
  simp [offTuranBoolHead]

@[simp] lemma offTuranBoolHead_true
    {ι : Type*} (X Y : ι) :
    offTuranBoolHead X Y true = Y := by
  simp [offTuranBoolHead]

@[simp] lemma offTuranBoolOtherHead_false
    {ι : Type*} (X Y : ι) :
    offTuranBoolOtherHead X Y false = Y := by
  simp [offTuranBoolOtherHead]

@[simp] lemma offTuranBoolOtherHead_true
    {ι : Type*} (X Y : ι) :
    offTuranBoolOtherHead X Y true = X := by
  simp [offTuranBoolOtherHead]

@[simp] lemma offTuranBoolEdges_false
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) :
    offTuranBoolEdges K₀ false = K₀ := by
  simp [offTuranBoolEdges]

@[simp] lemma offTuranBoolEdges_true
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) :
    offTuranBoolEdges K₀ true = Finset.univ \ K₀ := by
  simp [offTuranBoolEdges]

lemma offTuranBoolEdges_disjoint
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) :
    Disjoint (offTuranBoolEdges K₀ false)
      (offTuranBoolEdges K₀ true) := by
  simpa using! (Finset.disjoint_sdiff : Disjoint K₀ (Finset.univ \ K₀))

lemma offTuranBoolEdges_union
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) :
    offTuranBoolEdges K₀ false ∪ offTuranBoolEdges K₀ true =
      Finset.univ := by
  simp

lemma offTuranAssignedHead_of_mem
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) (X Y : ι) (b : Bool) {k : κ}
    (hk : k ∈ offTuranBoolEdges K₀ b) :
    offTuranAssignedHead K₀ X Y k = offTuranBoolHead X Y b := by
  cases b
  · simp only [offTuranBoolEdges_false] at hk
    simp [offTuranAssignedHead, hk]
  · have hkNot : k ∉ K₀ := (Finset.mem_sdiff.mp hk).2
    simp [offTuranAssignedHead, hkNot]

lemma offTuranAssignedBool_of_mem
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) (b : Bool) {k : κ}
    (hk : k ∈ offTuranBoolEdges K₀ b) :
    offTuranAssignedBool K₀ k = b := by
  cases b
  · simp only [offTuranBoolEdges_false] at hk
    simp [offTuranAssignedBool, hk]
  · have hkNot : k ∉ K₀ := (Finset.mem_sdiff.mp hk).2
    simp [offTuranAssignedBool, hkNot]

lemma offTuranAssignedHead_eq_boolHead
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (K₀ : Finset κ) (X Y : ι) (k : κ) :
    offTuranAssignedHead K₀ X Y k =
      offTuranBoolHead X Y (offTuranAssignedBool K₀ k) := by
  by_cases hk : k ∈ K₀ <;>
    simp [offTuranAssignedHead, offTuranAssignedBool, hk]

lemma offTuranBoolHead_ne_other
    {ι : Type*} (X Y : ι) (hXY : X ≠ Y) (b : Bool) :
    offTuranBoolHead X Y b ≠ offTuranBoolOtherHead X Y b := by
  cases b <;> simp [hXY, hXY.symm]

lemma offTuranBoolOtherHead_eq_of_ne
    {ι : Type*} (X Y : ι) (b c : Bool) (hbc : b ≠ c) :
    offTuranBoolHead X Y c = offTuranBoolOtherHead X Y b := by
  cases b <;> cases c <;> simp_all

end Erdos550

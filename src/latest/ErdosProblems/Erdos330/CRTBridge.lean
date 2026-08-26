/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib.Data.ZMod.QuotientRing
import ErdosProblems.Erdos330.SafePairs

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# CRT bridge lemmas for Erdős Problem 330

This file records the thin interface needed to pull product-coordinate sumset
identities back through the Chinese remainder equivalence.
-/

namespace Erdos330

open scoped Pointwise

theorem addEquiv_preimage_add {α β : Type*} [Add α] [Add β]
    (φ : α ≃+ β) (A B : Set β) :
    {x | φ x ∈ A + B} = {x | φ x ∈ A} + {x | φ x ∈ B} := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨φ.symm a, ?_, φ.symm b, ?_, ?_⟩
    · simpa using ha
    · simpa using hb
    · apply φ.injective
      have hab' : a + b = φ z := by simpa using hab
      calc
        φ (φ.symm a + φ.symm b) = a + b := by simp [φ.map_add]
        _ = φ z := hab'
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨φ x, hx, φ y, hy, ?_⟩
    have hxy' : x + y = z := by simpa using hxy
    calc
      φ x + φ y = φ (x + y) := (φ.map_add x y).symm
      _ = φ z := by rw [hxy']

noncomputable def addEquivPreimageFinset {α β : Type*} [Fintype α] [Add α] [Add β]
    (φ : α ≃+ β) (S : Set β) : Finset α := by
  classical
  exact Finset.univ.filter fun x => φ x ∈ S

noncomputable def addEquivTranslatePreimageFinset {α β : Type*} [Fintype α]
    [Add α] [Add β] (a : α) (φ : α ≃+ β) (S : Set β) : Finset α := by
  classical
  exact Finset.univ.filter fun x => φ (a + x) ∈ S

noncomputable def setFiniteFinset {α : Type*} [Fintype α] (S : Set α) : Finset α := by
  classical
  exact Finset.univ.filter fun x => x ∈ S

theorem coe_addEquivPreimageFinset {α β : Type*} [Fintype α] [Add α] [Add β]
    (φ : α ≃+ β) (S : Set β) :
    (addEquivPreimageFinset φ S : Set α) = {x | φ x ∈ S} := by
  classical
  ext x
  simp [addEquivPreimageFinset]

theorem coe_addEquivTranslatePreimageFinset {α β : Type*} [Fintype α]
    [Add α] [Add β] (a : α) (φ : α ≃+ β) (S : Set β) :
    (addEquivTranslatePreimageFinset a φ S : Set α) = {x | φ (a + x) ∈ S} := by
  classical
  ext x
  simp [addEquivTranslatePreimageFinset]

theorem mem_setFiniteFinset {α : Type*} [Fintype α] (S : Set α) (x : α) :
    x ∈ setFiniteFinset S ↔ x ∈ S := by
  classical
  simp [setFiniteFinset]

theorem addEquiv_preimage_add_eq_compl {α β : Type*} [Add α] [Add β]
    (φ : α ≃+ β) (A B P : Set β) (hAB : A + B = Set.univ \ P) :
    {x | φ x ∈ A} + {x | φ x ∈ B} = Set.univ \ {x | φ x ∈ P} := by
  rw [← addEquiv_preimage_add φ A B, hAB]
  ext x
  simp

theorem addEquiv_preimage_add_eq_univ {α β : Type*} [Add α] [Add β]
    (φ : α ≃+ β) (A B : Set β) (hAB : A + B = Set.univ) :
    {x | φ x ∈ A} + {x | φ x ∈ B} = Set.univ := by
  rw [← addEquiv_preimage_add φ A B, hAB]
  ext x
  simp

theorem addEquiv_translate_image_preimage {α β : Type*}
    [AddGroup α] [Add β] (φ : α ≃+ β) (a : α) (P : Set β) :
    ((fun x : α => a + x) '' {x | φ (a + x) ∈ P}) = {x | φ x ∈ P} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    refine ⟨-a + z, ?_, ?_⟩
    · change φ (a + (-a + z)) ∈ P
      have hsum : a + (-a + z) = z := by simp
      rwa [hsum]
    · simp

theorem addEquiv_preimage_add_translate_eq_compl_image {α β : Type*}
    [AddGroup α] [Add β] (φ : α ≃+ β) (a : α) (A B P : Set β)
    (hAB : A + B = Set.univ \ P) :
    {x | φ x ∈ A} + {x | φ x ∈ B} =
      Set.univ \ ((fun x : α => a + x) '' {x | φ (a + x) ∈ P}) := by
  rw [addEquiv_translate_image_preimage φ a P]
  exact addEquiv_preimage_add_eq_compl φ A B P hAB

theorem addEquivPreimageFinset_add_eq_compl_translate_image {α β : Type*}
    [Fintype α] [AddGroup α] [Add β]
    (φ : α ≃+ β) (a : α) (A B P : Set β) (hAB : A + B = Set.univ \ P) :
    ((addEquivPreimageFinset φ A : Set α) + (addEquivPreimageFinset φ B : Set α)) =
      Set.univ \ ((fun x : α => a + x) ''
        (addEquivTranslatePreimageFinset a φ P : Set α)) := by
  rw [coe_addEquivPreimageFinset, coe_addEquivPreimageFinset,
    coe_addEquivTranslatePreimageFinset]
  exact addEquiv_preimage_add_translate_eq_compl_image φ a A B P hAB

theorem addEquivPreimageFinset_add_eq_univ {α β : Type*}
    [Fintype α] [Add α] [Add β]
    (φ : α ≃+ β) (A B : Set β) (hAB : A + B = Set.univ) :
    ((addEquivPreimageFinset φ A : Set α) + (addEquivPreimageFinset φ B : Set α)) =
      Set.univ := by
  rw [coe_addEquivPreimageFinset, coe_addEquivPreimageFinset]
  exact addEquiv_preimage_add_eq_univ φ A B hAB

theorem addEquivPreimageFinset_subset {α β : Type*} [Fintype α] [Add α] [Add β]
    {φ : α ≃+ β} {A B : Set β} (hAB : A ⊆ B) :
    addEquivPreimageFinset φ A ⊆ addEquivPreimageFinset φ B := by
  classical
  intro x hx
  simp [addEquivPreimageFinset] at hx ⊢
  exact hAB hx

theorem addEquivPreimageFinset_card_eq {α β : Type*}
    [Fintype α] [Fintype β] [Add α] [Add β]
    (φ : α ≃+ β) (S : Set β) :
    (addEquivPreimageFinset φ S).card = (setFiniteFinset S).card := by
  classical
  refine Finset.card_bij (fun x _ => φ x) ?_ ?_ ?_
  · intro x hx
    rw [mem_setFiniteFinset]
    simp [addEquivPreimageFinset] at hx
    exact hx
  · intro x _ y _ hxy
    exact φ.injective hxy
  · intro y hy
    refine ⟨φ.symm y, ?_, ?_⟩
    · simp [addEquivPreimageFinset]
      rwa [mem_setFiniteFinset] at hy
    · simp

theorem addEquivTranslatePreimageFinset_card_eq_preimage {α β : Type*}
    [Fintype α] [AddGroup α] [Add β]
    (a : α) (φ : α ≃+ β) (S : Set β) :
    (addEquivTranslatePreimageFinset a φ S).card = (addEquivPreimageFinset φ S).card := by
  classical
  refine Finset.card_bij (fun x _ => a + x) ?_ ?_ ?_
  · intro x hx
    simp [addEquivTranslatePreimageFinset, addEquivPreimageFinset] at hx ⊢
    exact hx
  · intro x _ y _ hxy
    exact add_left_cancel hxy
  · intro y hy
    refine ⟨-a + y, ?_, ?_⟩
    · simp [addEquivTranslatePreimageFinset, addEquivPreimageFinset] at hy ⊢
      have hsum : a + (-a + y) = y := by simp
      have hEq : φ a + (φ (-a) + φ y) = φ y := by
        calc
          φ a + (φ (-a) + φ y) = φ (a + (-a + y)) := by
            rw [← φ.map_add (-a) y, ← φ.map_add a (-a + y)]
          _ = φ y := by rw [hsum]
      rwa [hEq]
    · simp

theorem setFiniteFinset_prod_singleton_card {α β : Type*}
    [Fintype α] [Fintype β] (a : α) (S : Set β) :
    (setFiniteFinset ({x : α × β | x.1 = a ∧ x.2 ∈ S})).card =
      (setFiniteFinset S).card := by
  classical
  refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
  · intro x hx
    rw [mem_setFiniteFinset]
    rw [mem_setFiniteFinset] at hx
    exact hx.2
  · intro x hx y hy hxy
    rw [mem_setFiniteFinset] at hx hy
    ext
    · rw [hx.1, hy.1]
    · exact hxy
  · intro y hy
    refine ⟨(a, y), ?_, ?_⟩
    · rw [mem_setFiniteFinset]
      rw [mem_setFiniteFinset] at hy
      exact ⟨rfl, hy⟩
    · rfl

noncomputable def zmodProdEquivPi {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hcoprime : Pairwise fun i j => Nat.Coprime (m i) (m j)) :
    ZMod (∏ i, m i) ≃+* ∀ i, ZMod (m i) :=
  ZMod.prodEquivPi m hcoprime

theorem crt_safePair_sum_union_eq_coordinateTarget_preimage {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (hcoprime : Pairwise fun i j => Nat.Coprime (p i) (p j))
    (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    let φ : ZMod (∏ i, p i) ≃+ ∀ i, ZMod (p i) :=
      (zmodProdEquivPi p hcoprime).toAddEquiv
    (({x | φ x ∈ leftSafeSet p e data true (safeLeftThreshold ι)} +
        {x | φ x ∈ rightSafeSet p e data true (safeRightThreshold ι)}) ∪
      ({x | φ x ∈ leftSafeSet p e data false (safeLeftThreshold ι)} +
        {x | φ x ∈ rightSafeSet p e data false (safeRightThreshold ι)})) =
      {x | φ x ∈ coordinateTarget p e} := by
  intro φ
  rw [← addEquiv_preimage_add φ, ← addEquiv_preimage_add φ]
  ext x
  change (φ x ∈ leftSafeSet p e data true (safeLeftThreshold ι) +
        rightSafeSet p e data true (safeRightThreshold ι) ∨
      φ x ∈ leftSafeSet p e data false (safeLeftThreshold ι) +
        rightSafeSet p e data false (safeRightThreshold ι)) ↔
    φ x ∈ coordinateTarget p e
  rw [← Set.mem_union]
  rw [safePair_sum_union_eq_coordinateTarget p hp7 e data]

end Erdos330

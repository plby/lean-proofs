import Mathlib.Data.Set.PowersetCard

/-!
# A local upward-LYM double count

This is the finite double count needed to compare consecutive uniform
subset layers.  It is kept local so the Erdős 746 development does not need
to import the much broader Erdős 543 module that originally used the same
argument.
-/

namespace Erdos746.LocalLYM

attribute [local instance] Classical.propDecidable

/-- Members of the `k`th Boolean-lattice layer satisfying `P`. -/
noncomputable def goodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset (Finset α) :=
  (U.powersetCard k).filter P

/-- A good `k`-set together with a new point. -/
noncomputable def extensionPairs {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset ((_A : Finset α) × α) :=
  (goodSets U P k).sigma fun A ↦ U \ A

/-- A good `(k+1)`-set together with a marked point. -/
noncomputable def markedGoodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset ((_B : Finset α) × α) :=
  (goodSets U P (k + 1)).sigma fun B ↦ B

lemma card_extensionPairs {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) :
    (extensionPairs U P k).card = (goodSets U P k).card * (U.card - k) := by
  rw [extensionPairs, Finset.card_sigma]
  apply Finset.sum_const_nat
  intro A hA
  have hlevel : A ∈ U.powersetCard k := (Finset.mem_filter.mp hA).1
  have hAU : A ⊆ U := (Finset.mem_powersetCard.mp hlevel).1
  have hcard : A.card = k := (Finset.mem_powersetCard.mp hlevel).2
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAU, hcard]

lemma card_markedGoodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) :
    (markedGoodSets U P k).card = (goodSets U P (k + 1)).card * (k + 1) := by
  rw [markedGoodSets, Finset.card_sigma]
  apply Finset.sum_const_nat
  intro B hB
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1).2

/-- Adjoin the marked point while retaining it as the mark. -/
def extendPair {α : Type*} [DecidableEq α] :
    ((_A : Finset α) × α) → ((_B : Finset α) × α)
  | ⟨A, x⟩ => ⟨insert x A, x⟩

lemma extendPair_injective_on_extensions {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) :
    Set.InjOn extendPair
      (↑(extensionPairs U P k) : Set ((_A : Finset α) × α)) := by
  rintro ⟨A, x⟩ hAx ⟨B, y⟩ hBy hEq
  have hxA : x ∉ A :=
    (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hAx).2).2
  have hyB : y ∉ B :=
    (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hBy).2).2
  have hfirst : insert x A = insert y B := congrArg Sigma.fst hEq
  have hxy : x = y := by
    have hHEq : HEq x y := (Sigma.mk.inj_iff.mp hEq).2
    exact eq_of_heq hHEq
  subst y
  have hAB : A = B := by
    simpa only [Finset.erase_insert hxA, Finset.erase_insert hyB] using
      congrArg (fun S : Finset α ↦ S.erase x) hfirst
  subst B
  rfl

lemma extensionPairs_mapsTo_markedGoodSets {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B) :
    Set.MapsTo extendPair
      (↑(extensionPairs U P k) : Set ((_A : Finset α) × α))
      (↑(markedGoodSets U P k) : Set ((_B : Finset α) × α)) := by
  rintro ⟨A, x⟩ hAx
  change ⟨A, x⟩ ∈ (goodSets U P k).sigma (fun A ↦ U \ A) at hAx
  change ⟨insert x A, x⟩ ∈
    (goodSets U P (k + 1)).sigma (fun B ↦ B)
  rw [Finset.mem_sigma] at hAx ⊢
  rcases hAx with ⟨hA, hx⟩
  rw [goodSets, Finset.mem_filter] at hA ⊢
  rcases hA with ⟨hAlevel, hPA⟩
  rcases Finset.mem_powersetCard.mp hAlevel with ⟨hAU, hcardA⟩
  rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxA⟩
  constructor
  · constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.insert_subset hxU hAU,
        by simp [Finset.card_insert_of_notMem hxA, hcardA]⟩
    · exact hP (Finset.subset_insert x A) hPA
  · exact Finset.mem_insert_self x A

/-- The upward local-LYM double count. -/
lemma extension_count_le_marked_count {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B) :
    (goodSets U P k).card * (U.card - k) ≤
      (goodSets U P (k + 1)).card * (k + 1) := by
  rw [← card_extensionPairs, ← card_markedGoodSets]
  exact Finset.card_le_card_of_injOn extendPair
    (extensionPairs_mapsTo_markedGoodSets U P k hP)
    (extendPair_injective_on_extensions U P k)

end Erdos746.LocalLYM

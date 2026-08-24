/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 362.
https://www.erdosproblems.com/forum/thread/362

Informal authors:
- András Sárközy
- Endre Szemerédi
- Gábor Halász

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos362.md
-/
/-
This is a Lean formalization of the affirmative resolution of Erdős Problem 362.
https://www.erdosproblems.com/362

Informal authors:
- András Sárközy
- Endre Szemerédi
- Gábor Halász

The first estimate is the Sárközy--Szemerédi refinement of the
Littlewood--Offord inequality.  The fixed-cardinality estimate is due to Halász.

References:
- A. Sárközy and E. Szemerédi, Über ein Problem von Erdős und Moser,
  Acta Arith. 11 (1965), 205--208.
- G. Halász, Estimates for the concentration function of combinatorial number
  theory and probability, Period. Math. Hungar. 8 (1977), 197--211.
- B. Gunby, X. He, B. Narayanan, and S. Spiro, Antichain codes,
  Bull. Lond. Math. Soc. 55 (2023), 3053--3062.
-/

import Mathlib
import ErdosProblems.Erdos487

namespace Erdos362

open scoped BigOperators
open Finset

/-- The subsets of `A` whose elements sum to `t`. -/
def subsetSumFiber (A : Finset ℕ) (t : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter fun S ↦ ∑ a ∈ S, a = t

/-- The `l`-element subsets of `A` whose elements sum to `t`. -/
def fixedCardSubsetSumFiber (A : Finset ℕ) (l t : ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard l).filter fun S ↦ ∑ a ∈ S, a = t

@[simp] lemma mem_subsetSumFiber {A S : Finset ℕ} {t : ℕ} :
    S ∈ subsetSumFiber A t ↔ S ⊆ A ∧ ∑ a ∈ S, a = t := by
  simp [subsetSumFiber]

@[simp] lemma mem_fixedCardSubsetSumFiber {A S : Finset ℕ} {l t : ℕ} :
    S ∈ fixedCardSubsetSumFiber A l t ↔
      S ⊆ A ∧ S.card = l ∧ ∑ a ∈ S, a = t := by
  simp [fixedCardSubsetSumFiber, and_assoc]

lemma subsetSumFiber_card_le (A : Finset ℕ) (t : ℕ) :
    (subsetSumFiber A t).card ≤ 2 ^ A.card := by
  calc
    (subsetSumFiber A t).card ≤ A.powerset.card := card_filter_le _ _
    _ = 2 ^ A.card := card_powerset A

lemma fixedCardSubsetSumFiber_card_le (A : Finset ℕ) (l t : ℕ) :
    (fixedCardSubsetSumFiber A l t).card ≤ A.card.choose l := by
  calc
    (fixedCardSubsetSumFiber A l t).card ≤ (A.powersetCard l).card := card_filter_le _ _
    _ = A.card.choose l := card_powersetCard l A

/-- The indexed version of a subset-sum fiber. -/
def indexedSubsetSumFiber {n : ℕ} (a : Fin n → ℕ) (t : ℕ) :
    Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter fun S ↦ ∑ i ∈ S, a i = t

/-- The indexed fixed-cardinality subset-sum fiber. -/
def indexedFixedCardSubsetSumFiber {n : ℕ} (a : Fin n → ℕ) (l t : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard l).filter fun S ↦ ∑ i ∈ S, a i = t

@[simp] lemma mem_indexedSubsetSumFiber {n : ℕ} {a : Fin n → ℕ}
    {S : Finset (Fin n)} {t : ℕ} :
    S ∈ indexedSubsetSumFiber a t ↔ ∑ i ∈ S, a i = t := by
  simp [indexedSubsetSumFiber]

@[simp] lemma mem_indexedFixedCardSubsetSumFiber {n : ℕ} {a : Fin n → ℕ}
    {S : Finset (Fin n)} {l t : ℕ} :
    S ∈ indexedFixedCardSubsetSumFiber a l t ↔
      S.card = l ∧ ∑ i ∈ S, a i = t := by
  simp [indexedFixedCardSubsetSumFiber]

/-- Hamming distance between two finite subsets. -/
def finsetDistance {α : Type*} [DecidableEq α] (S T : Finset α) : ℕ :=
  (S \ T).card + (T \ S).card

lemma finsetDistance_eq_card_symmDiff {α : Type*} [DecidableEq α]
    (S T : Finset α) : finsetDistance S T = (symmDiff S T).card := by
  rw [finsetDistance, symmDiff_def]
  symm
  apply card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro a haS haT
  simp only [mem_sdiff] at haS haT
  exact haS.2 haT.1

/-- A family of finite subsets is an antichain for inclusion. -/
def IsFinsetAntichain {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒜 → ∀ ⦃T⦄, T ∈ 𝒜 → S ⊆ T → S = T

/-- A family is a Hamming-distance-three code. -/
def IsDistanceThreeCode {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃S⦄, S ∈ 𝒜 → ∀ ⦃T⦄, T ∈ 𝒜 → S ≠ T → 3 ≤ finsetDistance S T

/-- A family contains no strictly increasing chain of three members. -/
def ThreeChainFree {α : Type*} [DecidableEq α]
    (𝒢 : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C : Finset α⦄, A ∈ 𝒢 → B ∈ 𝒢 → C ∈ 𝒢 → A ⊂ B → B ⊂ C → False

/-- The members having no strictly smaller member in the family. -/
def minimalPart {α : Type*} [DecidableEq α]
    (𝒢 : Finset (Finset α)) : Finset (Finset α) :=
  𝒢.filter fun A ↦ ¬ ∃ B ∈ 𝒢, B ⊂ A

lemma minimalPart_subset {α : Type*} [DecidableEq α]
    (𝒢 : Finset (Finset α)) : minimalPart 𝒢 ⊆ 𝒢 := by
  intro A hA
  exact (mem_filter.mp hA).1

lemma minimalPart_isAntichain {α : Type*} [Fintype α] [DecidableEq α]
    (𝒢 : Finset (Finset α)) :
    IsAntichain (· ⊆ ·) (minimalPart 𝒢 : Set (Finset α)) := by
  intro A hA B hB hAB hle
  have hA𝒢 : A ∈ 𝒢 := (mem_filter.mp hA).1
  have hBmin : ¬ ∃ C ∈ 𝒢, C ⊂ B := (mem_filter.mp hB).2
  exact hBmin ⟨A, hA𝒢, hle.ssubset_of_ne hAB⟩

lemma nonminimalPart_isAntichain {α : Type*} [Fintype α] [DecidableEq α]
    (𝒢 : Finset (Finset α)) (h𝒢 : ThreeChainFree 𝒢) :
    IsAntichain (· ⊆ ·) ((𝒢 \ minimalPart 𝒢 : Finset (Finset α)) : Set (Finset α)) := by
  intro A hA B hB hAB hle
  have hA' : A ∈ 𝒢 \ minimalPart 𝒢 := hA
  have hB' : B ∈ 𝒢 \ minimalPart 𝒢 := hB
  have hA𝒢 : A ∈ 𝒢 := (mem_sdiff.mp hA').1
  have hB𝒢 : B ∈ 𝒢 := (mem_sdiff.mp hB').1
  have hAnot : A ∉ minimalPart 𝒢 := (mem_sdiff.mp hA').2
  have hAhas : ∃ C ∈ 𝒢, C ⊂ A := by
    simpa [minimalPart, hA𝒢] using hAnot
  obtain ⟨C, hC𝒢, hCA⟩ := hAhas
  exact h𝒢 hC𝒢 hA𝒢 hB𝒢 hCA (hle.ssubset_of_ne hAB)

/-- Erdős's two-Sperner bound, in the slightly weaker form sufficient here. -/
theorem threeChainFree_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (𝒢 : Finset (Finset α)) (h𝒢 : ThreeChainFree 𝒢) :
    𝒢.card ≤ 2 * (Fintype.card α).choose (Fintype.card α / 2) := by
  have hmin := (minimalPart_isAntichain 𝒢).sperner
  have hrest := (nonminimalPart_isAntichain 𝒢 h𝒢).sperner
  have hpart : (𝒢 \ minimalPart 𝒢).card + (minimalPart 𝒢).card = 𝒢.card :=
    card_sdiff_add_card_eq_card (minimalPart_subset 𝒢)
  omega

/-- Toggle membership of one coordinate. -/
def toggle {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) : Finset ι :=
  if i ∈ S then S.erase i else insert i S

@[simp] lemma toggle_of_mem {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {i : ι} (hi : i ∈ S) : toggle S i = S.erase i := by
  simp [toggle, hi]

@[simp] lemma toggle_of_not_mem {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {i : ι} (hi : i ∉ S) : toggle S i = insert i S := by
  simp [toggle, hi]

@[simp] lemma toggle_toggle {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) :
    toggle (toggle S i) i = S := by
  by_cases hi : i ∈ S
  · simp [toggle, hi, insert_erase hi]
  · simp [toggle, hi]

lemma sum_toggle {ι : Type*} [DecidableEq ι] (a : ι → ℤ) (S : Finset ι) (i : ι) :
    ∑ x ∈ toggle S i, a x =
      ∑ x ∈ S, a x + if i ∈ S then -a i else a i := by
  by_cases hi : i ∈ S
  · simp only [toggle_of_mem hi, hi, if_pos]
    have h := sum_erase_add (s := S) (f := a) hi
    omega
  · simp [toggle_of_not_mem hi, hi, add_comm]

lemma toggle_eq_of_equal_sums {ι : Type*} [DecidableEq ι]
    (a : ι → ℤ) (ha_pos : ∀ i, 0 < a i) (ha_inj : Function.Injective a)
    {S T : Finset ι} {i j : ι}
    (hsum : (∑ x ∈ S, a x) = ∑ x ∈ T, a x)
    (htog : toggle S i = toggle T j) : S = T ∧ i = j := by
  have hS := sum_toggle a S i
  have hT := sum_toggle a T j
  rw [htog] at hS
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ T
  · have haij : a i = a j := by simp [hi, hj] at hS hT; omega
    have hij : i = j := ha_inj haij
    subst j
    exact ⟨by simpa only [toggle_toggle] using congrArg (toggle · i) htog, rfl⟩
  · simp [hi, hj] at hS hT
    have := ha_pos i
    have := ha_pos j
    omega
  · simp [hi, hj] at hS hT
    have := ha_pos i
    have := ha_pos j
    omega
  · have haij : a i = a j := by simp [hi, hj] at hS hT; omega
    have hij : i = j := ha_inj haij
    subst j
    exact ⟨by simpa only [toggle_toggle] using congrArg (toggle · i) htog, rfl⟩

/-- The section over `c` of an embedding into a product. -/
def sectionSubtype {α β γ : Type*} [DecidableEq α]
    (e : β ↪ γ × Finset α) (c : γ) := {b : β // (e b).1 = c}

noncomputable instance sectionSubtypeFintype {α β γ : Type*} [DecidableEq α]
    [Fintype β] (e : β ↪ γ × Finset α) (c : γ) : Fintype (sectionSubtype e c) :=
  Fintype.ofInjective (fun b : sectionSubtype e c ↦ b.1) Subtype.val_injective

def sectionEmbedding {α β γ : Type*} [DecidableEq α]
    (e : β ↪ γ × Finset α) (c : γ) : sectionSubtype e c ↪ Finset α where
  toFun b := (e b.1).2
  inj' := by
    intro b₁ b₂ h
    apply Subtype.ext
    apply e.injective
    exact Prod.ext (b₁.2.trans b₂.2.symm) h

noncomputable def sectionFamily {α β γ : Type*} [Fintype β] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ]
    (e : β ↪ γ × Finset α) (c : γ) : Finset (Finset α) := by
  classical
  exact Finset.univ.map (sectionEmbedding e c)

def sectionSigmaEquiv {α β γ : Type*} [DecidableEq α]
    (e : β ↪ γ × Finset α) : (Σ c : γ, sectionSubtype e c) ≃ β where
  toFun z := z.2.1
  invFun b := ⟨(e b).1, ⟨b, rfl⟩⟩
  left_inv := by rintro ⟨c, b, hb⟩; simp only; subst c; rfl
  right_inv _ := rfl

lemma sum_card_sections {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : β ↪ γ × Finset α) :
    ∑ c : γ, (sectionFamily e c).card = Fintype.card β := by
  classical
  simp only [sectionFamily, card_map, card_univ]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (sectionSigmaEquiv e)

theorem card_le_of_embedding_sections {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : β ↪ γ × Finset α) (hsec : ∀ c, ThreeChainFree (sectionFamily e c)) :
    Fintype.card β ≤
      Fintype.card γ * (2 * (Fintype.card α).choose (Fintype.card α / 2)) := by
  classical
  rw [← sum_card_sections e]
  calc
    ∑ c : γ, (sectionFamily e c).card ≤
        ∑ _c : γ, 2 * (Fintype.card α).choose (Fintype.card α / 2) :=
      sum_le_sum fun c _ ↦ threeChainFree_card_le _ (hsec c)
    _ = Fintype.card γ * (2 * (Fintype.card α).choose
        (Fintype.card α / 2)) := by simp

/-- A generic indexed subset-sum fiber on a finite type. -/
def sumFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (t : ℕ) : Finset (Finset ι) :=
  Finset.univ.powerset.filter fun S ↦ ∑ i ∈ S, a i = t

@[simp] lemma mem_sumFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ι → ℕ} {t : ℕ} {S : Finset ι} :
    S ∈ sumFiber a t ↔ ∑ i ∈ S, a i = t := by
  simp [sumFiber]

@[simp] lemma toLeft_toggle_inl {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset (ι ⊕ κ)) (i : ι) :
    (toggle S (Sum.inl i)).toLeft = toggle S.toLeft i := by
  ext x
  by_cases hi : Sum.inl i ∈ S <;> simp [toggle, hi]

@[simp] lemma toRight_toggle_inl {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset (ι ⊕ κ)) (i : ι) :
    (toggle S (Sum.inl i)).toRight = S.toRight := by
  ext x
  by_cases hi : Sum.inl i ∈ S <;> simp [toggle, hi]

lemma sum_sumType {ι κ M : Type*} [DecidableEq ι] [DecidableEq κ]
    [AddCommMonoid M] (a : ι ⊕ κ → M) (S : Finset (ι ⊕ κ)) :
    ∑ x ∈ S, a x =
      (∑ i ∈ S.toLeft, a (Sum.inl i)) + ∑ j ∈ S.toRight, a (Sum.inr j) := by
  conv_lhs => rw [← S.toLeft_disjSum_toRight]
  simp

/-- The domain of the low-coordinate flip map. -/
def flipDomain {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (a : ι ⊕ κ → ℕ) (t : ℕ) :=
  ↥((sumFiber a t).product (Finset.univ : Finset ι))

noncomputable instance flipDomainFintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (a : ι ⊕ κ → ℕ) (t : ℕ) :
    Fintype (flipDomain a t) := by
  dsimp [flipDomain]
  infer_instance

noncomputable instance flipDomainDecidableEq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (a : ι ⊕ κ → ℕ) (t : ℕ) :
    DecidableEq (flipDomain a t) := Classical.decEq _

noncomputable def flipEmbedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (a : ι ⊕ κ → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha_inj : Function.Injective a) (t : ℕ) :
    flipDomain a t ↪ Finset ι × Finset κ where
  toFun p := ((toggle p.1.1 (Sum.inl p.1.2)).toLeft,
    (toggle p.1.1 (Sum.inl p.1.2)).toRight)
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · have htog : toggle p.1.1 (Sum.inl p.1.2) =
          toggle q.1.1 (Sum.inl q.1.2) := by
        have := congrArg (fun z : Finset ι × Finset κ ↦ z.1.disjSum z.2) hpq
        simpa only [Finset.toLeft_disjSum_toRight] using this
      have hsumNat : (∑ x ∈ p.1.1, a x) = ∑ x ∈ q.1.1, a x := by
        have hp := (mem_product.mp p.2).1
        have hq := (mem_product.mp q.2).1
        rw [mem_sumFiber] at hp hq
        omega
      have hsum : (∑ x ∈ p.1.1, (a x : ℤ)) =
          ∑ x ∈ q.1.1, (a x : ℤ) := by exact_mod_cast hsumNat
      exact (toggle_eq_of_equal_sums (fun x ↦ (a x : ℤ))
        (fun x ↦ by exact_mod_cast ha_pos x)
        (fun x y h ↦ ha_inj (by simpa using h)) hsum htog).1
    · have htog : toggle p.1.1 (Sum.inl p.1.2) =
          toggle q.1.1 (Sum.inl q.1.2) := by
        have := congrArg (fun z : Finset ι × Finset κ ↦ z.1.disjSum z.2) hpq
        simpa only [Finset.toLeft_disjSum_toRight] using this
      have hsumNat : (∑ x ∈ p.1.1, a x) = ∑ x ∈ q.1.1, a x := by
        have hp := (mem_product.mp p.2).1
        have hq := (mem_product.mp q.2).1
        rw [mem_sumFiber] at hp hq
        omega
      have hsum : (∑ x ∈ p.1.1, (a x : ℤ)) =
          ∑ x ∈ q.1.1, (a x : ℤ) := by exact_mod_cast hsumNat
      have hij := (toggle_eq_of_equal_sums (fun x ↦ (a x : ℤ))
        (fun x ↦ by exact_mod_cast ha_pos x)
        (fun x y h ↦ ha_inj (by simpa using h)) hsum htog).2
      exact Sum.inl_injective hij

lemma flipSection_threeChainFree {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (a : ι ⊕ κ → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha_inj : Function.Injective a)
    (hsep : ∀ i j, a (Sum.inl i) < a (Sum.inr j)) (t : ℕ) (c : Finset ι) :
    ThreeChainFree (sectionFamily (flipEmbedding a ha_pos ha_inj t) c) := by
  classical
  let e := flipEmbedding a ha_pos ha_inj t
  have source : ∀ {U : Finset κ}, U ∈ sectionFamily e c →
      ∃ S : Finset (ι ⊕ κ), ∃ i : ι,
        S ∈ sumFiber a t ∧ (toggle S (Sum.inl i)).toLeft = c ∧ S.toRight = U := by
    intro U hU
    change U ∈ Finset.univ.map (sectionEmbedding e c) at hU
    rw [mem_map] at hU
    obtain ⟨b, hb, hbe⟩ := hU
    refine ⟨b.1.1.1, b.1.1.2, (mem_product.mp b.1.2).1, ?_, ?_⟩
    · have hb2 := b.2
      change (toggle b.1.1.1 (Sum.inl b.1.1.2)).toLeft = c at hb2
      exact hb2
    · have hbe' := hbe
      change (toggle b.1.1.1 (Sum.inl b.1.1.2)).toRight = U at hbe'
      rw [toRight_toggle_inl] at hbe'
      exact hbe'
  intro U V W hU hV hW hUV hVW
  obtain ⟨S, i, hSf, hSi, hSU⟩ := source hU
  obtain ⟨T, j, hTf, hTj, hTW⟩ := source hW
  have hSi' : toggle S.toLeft i = c := by simpa using hSi
  have hTj' : toggle T.toLeft j = c := by simpa using hTj
  have hSlow : S.toLeft = toggle c i := by
    have := congrArg (toggle · i) hSi'
    simpa using this
  have hTlow : T.toLeft = toggle c j := by
    have := congrArg (toggle · j) hTj'
    simpa using this
  have hxex : ∃ x, x ∈ V ∧ x ∉ U := by
    by_contra h
    push_neg at h
    exact hUV.not_subset h
  have hyex : ∃ y, y ∈ W ∧ y ∉ V := by
    by_contra h
    push_neg at h
    exact hVW.not_subset h
  obtain ⟨x, hxV, hxU⟩ := hxex
  obtain ⟨y, hyW, hyV⟩ := hyex
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hyV hxV
  have hxW : x ∈ W := hVW.subset hxV
  have hyU : y ∉ U := fun hy ↦ hyV (hUV.subset hy)
  have hpair : ({x, y} : Finset κ) ⊆ W \ U := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_sdiff.mpr ⟨hxW, hxU⟩
    · exact mem_sdiff.mpr ⟨hyW, hyU⟩
  let lowWeight : ι → ℤ := fun z ↦ a (Sum.inl z)
  let highWeight : κ → ℤ := fun z ↦ a (Sum.inr z)
  have hpairSum : highWeight x + highWeight y ≤ ∑ z ∈ W \ U, highWeight z := by
    have hle : (∑ z ∈ ({x, y} : Finset κ), highWeight z) ≤
        ∑ z ∈ W \ U, highWeight z := by
      apply sum_le_sum_of_subset_of_nonneg hpair
      intro z _ _
      change 0 ≤ (a (Sum.inr z) : ℤ)
      positivity
    simpa [hxy] using hle
  have hUW : U ⊂ W := hUV.trans hVW
  have hWdecomp : (∑ z ∈ W \ U, highWeight z) + ∑ z ∈ U, highWeight z =
      ∑ z ∈ W, highWeight z := sum_sdiff hUW.subset
  have hsepI : lowWeight i < highWeight x := by
    change (a (Sum.inl i) : ℤ) < (a (Sum.inr x) : ℤ)
    exact_mod_cast hsep i x
  have hsepJ : lowWeight j < highWeight y := by
    change (a (Sum.inl j) : ℤ) < (a (Sum.inr y) : ℤ)
    exact_mod_cast hsep j y
  have hhigh : (∑ z ∈ U, highWeight z) + lowWeight i + lowWeight j <
      ∑ z ∈ W, highWeight z := by omega
  have hsumS : (∑ z ∈ S, (a z : ℤ)) = t := by
    exact_mod_cast (mem_sumFiber.mp hSf)
  have hsumT : (∑ z ∈ T, (a z : ℤ)) = t := by
    exact_mod_cast (mem_sumFiber.mp hTf)
  rw [sum_sumType (fun z ↦ (a z : ℤ)) S, hSlow, hSU] at hsumS
  rw [sum_sumType (fun z ↦ (a z : ℤ)) T, hTlow, hTW] at hsumT
  have hlowI := sum_toggle lowWeight c i
  have hlowJ := sum_toggle lowWeight c j
  dsimp [lowWeight, highWeight] at hsumS hsumT hlowI hlowJ hhigh
  split at hlowI <;> split at hlowJ <;> omega

/-- Exact finite form of the Sárközy--Szemerédi estimate. -/
theorem sarkozy_szemeredi_finite {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (a : ι ⊕ κ → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha_inj : Function.Injective a)
    (hsep : ∀ i j, a (Sum.inl i) < a (Sum.inr j)) (t : ℕ) :
    (sumFiber a t).card * Fintype.card ι ≤
      2 ^ Fintype.card ι *
        (2 * (Fintype.card κ).choose (Fintype.card κ / 2)) := by
  classical
  have h := card_le_of_embedding_sections (flipEmbedding a ha_pos ha_inj t)
    (flipSection_threeChainFree a ha_pos ha_inj hsep t)
  have hcard : Fintype.card (flipDomain a t) =
      ((sumFiber a t).product (Finset.univ : Finset ι)).card := by
    calc
      Fintype.card (flipDomain a t) =
          Fintype.card ↥((sumFiber a t).product (Finset.univ : Finset ι)) :=
        Fintype.card_congr (Equiv.refl _)
      _ = ((sumFiber a t).product (Finset.univ : Finset ι)).card := Fintype.card_coe _
  calc
    (sumFiber a t).card * Fintype.card ι = Fintype.card (flipDomain a t) := by
      rw [hcard]
      simp [card_product]
    _ ≤ Fintype.card (Finset ι) *
        (2 * (Fintype.card κ).choose (Fintype.card κ / 2)) := h
    _ = 2 ^ Fintype.card ι *
        (2 * (Fintype.card κ).choose (Fintype.card κ / 2)) := by
      simp [Fintype.card_finset]

lemma sum_pos_of_ssubset_of_pos {α : Type*} [DecidableEq α]
    (a : α → ℕ) (ha : ∀ i, 0 < a i) {S T : Finset α} (hST : S ⊂ T) :
    ∑ i ∈ S, a i < ∑ i ∈ T, a i := by
  have hne : T \ S ≠ ∅ := by
    simpa [sdiff_eq_empty_iff_subset] using hST.not_subset
  have hpos : 0 < ∑ i ∈ T \ S, a i := by
    exact sum_pos (fun i hi ↦ ha i) (Finset.nonempty_iff_ne_empty.mpr hne)
  calc
    ∑ i ∈ S, a i < (∑ i ∈ T \ S, a i) + ∑ i ∈ S, a i := by omega
    _ = ∑ i ∈ T, a i := sum_sdiff hST.subset

lemma indexedSubsetSumFiber_isAntichain {n : ℕ} (a : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (t : ℕ) :
    IsFinsetAntichain (indexedSubsetSumFiber a t) := by
  intro S hS T hT hST
  by_contra hne
  have hss : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, hne⟩
  have hlt := sum_pos_of_ssubset_of_pos a ha hss
  rw [(mem_indexedSubsetSumFiber.mp hS), (mem_indexedSubsetSumFiber.mp hT)] at hlt
  exact (Nat.lt_irrefl t) hlt

lemma indexedSubsetSumFiber_isDistanceThree {n : ℕ} (a : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (ha_inj : Function.Injective a) (t : ℕ) :
    IsDistanceThreeCode (indexedSubsetSumFiber a t) := by
  have hanti := indexedSubsetSumFiber_isAntichain a ha_pos t
  intro S hS T hT hne
  have hST : ¬S ⊆ T := fun h ↦ hne (hanti hS hT h)
  have hTS : ¬T ⊆ S := fun h ↦ Ne.symm hne (hanti hT hS h)
  have hSdiff : 0 < (S \ T).card := by
    rw [card_pos]
    exact Finset.nonempty_iff_ne_empty.mpr (by
      simpa [sdiff_eq_empty_iff_subset] using hST)
  have hTdiff : 0 < (T \ S).card := by
    rw [card_pos]
    exact Finset.nonempty_iff_ne_empty.mpr (by
      simpa [sdiff_eq_empty_iff_subset] using hTS)
  by_contra hnot
  have hle : finsetDistance S T ≤ 2 := by omega
  have htwo : finsetDistance S T = 2 := by
    simp only [finsetDistance] at hle ⊢
    omega
  have hScard : (S \ T).card = 1 := by
    simp only [finsetDistance] at htwo
    omega
  have hTcard : (T \ S).card = 1 := by
    simp only [finsetDistance] at htwo
    omega
  rcases card_eq_one.mp hScard with ⟨i, hi⟩
  rcases card_eq_one.mp hTcard with ⟨j, hj⟩
  have hsum := (mem_indexedSubsetSumFiber.mp hS).trans
    (mem_indexedSubsetSumFiber.mp hT).symm
  rw [← sum_sdiff (inter_subset_left : S ∩ T ⊆ S),
    ← sum_sdiff (inter_subset_right : S ∩ T ⊆ T)] at hsum
  have hSdecomp : S \ (S ∩ T) = S \ T := by ext x; simp [and_assoc]
  have hTdecomp : T \ (S ∩ T) = T \ S := by ext x; simp [and_assoc, and_left_comm]
  rw [hSdecomp, hTdecomp, hi, hj] at hsum
  simp only [sum_singleton] at hsum
  have hij : i = j := ha_inj (Nat.add_right_cancel hsum)
  have hiST : i ∈ S \ T := by simp [hi]
  have hjTS : j ∈ T \ S := by simp [hj]
  subst j
  simp only [mem_sdiff] at hiST hjTS
  exact hiST.2 hjTS.1

lemma sqrt_sq_nat (n : ℕ) :
    Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := by
  simpa only [pow_two] using Real.mul_self_sqrt (Nat.cast_nonneg n)

lemma sqrt_four_nat (n : ℕ) :
    Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sqrt_sq_nat]

lemma sqrt_ne_zero_nat {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt hn)))

lemma sqrt_cube_comparison {n r : ℕ} (hnr : n ≤ 8 * r) :
    Real.sqrt (n : ℝ) ^ 3 ≤ 27 * Real.sqrt (r : ℝ) ^ 3 := by
  have hcast : (n : ℝ) ≤ 9 * (r : ℝ) := by
    exact_mod_cast (hnr.trans (by omega : 8 * r ≤ 9 * r))
  have hsqrt : Real.sqrt (n : ℝ) ≤ 3 * Real.sqrt (r : ℝ) := by
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt (9 * (r : ℝ)) :=
        Real.sqrt_le_sqrt hcast
      _ = 3 * Real.sqrt (r : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num
  have hfactor :
      0 ≤ (3 * Real.sqrt (r : ℝ) - Real.sqrt (n : ℝ)) *
        (9 * Real.sqrt (r : ℝ) ^ 2 +
          3 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) +
          Real.sqrt (n : ℝ) ^ 2) := by
    positivity
  nlinarith

lemma div_sqrt_mul_div_sqrt_cube_le {a : ℝ} {n r : ℕ}
    (ha : 0 ≤ a) (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : n ≤ 8 * r) :
    (a / Real.sqrt (n : ℝ)) / Real.sqrt (r : ℝ) ^ 3 ≤
      27 * a / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hr0
  have hcomp := sqrt_cube_comparison hnr
  rw [div_div]
  rw [div_le_iff₀ (mul_pos hsn (pow_pos hsr 3))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (sq_pos_of_pos hn0)]
  rw [← sqrt_four_nat n]
  calc
    a * Real.sqrt (n : ℝ) ^ 4 =
        a * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ^ 3 := by ring
    _ ≤ a * Real.sqrt (n : ℝ) *
        (27 * Real.sqrt (r : ℝ) ^ 3) := by
      gcongr
    _ = 27 * a * (Real.sqrt (n : ℝ) * Real.sqrt (r : ℝ) ^ 3) := by ring

lemma central_choose_div_sqrt_cube_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n r : ℕ, 1 ≤ n → 1 ≤ r → n ≤ 8 * r →
      (Nat.choose n (n / 2) : ℝ) / Real.sqrt (r : ℝ) ^ 3 ≤
        C * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := Erdos487.central_binom_bound
  have hC₀_nonneg : 0 ≤ C₀ := by
    have h := hC₀ 1 (by omega)
    norm_num at h
    linarith
  refine ⟨27 * (C₀ + 1), by positivity, ?_⟩
  intro n r hn hr hnr
  have hcentral := hC₀ n hn
  calc
    (Nat.choose n (n / 2) : ℝ) / Real.sqrt (r : ℝ) ^ 3 ≤
        (C₀ * ((2 : ℝ) ^ n / Real.sqrt (n : ℝ))) /
          Real.sqrt (r : ℝ) ^ 3 := by
      gcongr
    _ = C₀ *
        (((2 : ℝ) ^ n / Real.sqrt (n : ℝ)) /
          Real.sqrt (r : ℝ) ^ 3) := by ring
    _ ≤ C₀ * (27 * (2 : ℝ) ^ n / (n : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (div_sqrt_mul_div_sqrt_cube_le (a := (2 : ℝ) ^ n)
          (by positivity) hn hr hnr)
        hC₀_nonneg
    _ ≤ (27 * (C₀ + 1)) * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      rw [show C₀ * (27 * (2 : ℝ) ^ n / (n : ℝ) ^ 2) =
        (C₀ * 27 * (2 : ℝ) ^ n) / (n : ℝ) ^ 2 by ring]
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hn0)).2
      nlinarith [show 0 ≤ (2 : ℝ) ^ n by positivity]
lemma choose_mul_seven_pow_le (n r : ℕ) (hr : r ≤ n) :
    n.choose r * 7 ^ (n - r) ≤ 8 ^ n := by
  rw [show 8 ^ n = (1 + 7 : ℕ) ^ n by norm_num, add_pow]
  have hrange : r ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  calc
    n.choose r * 7 ^ (n - r) =
        1 ^ r * 7 ^ (n - r) * n.choose r := by simp [Nat.mul_comm]
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        1 ^ m * 7 ^ (n - m) * n.choose m := by
      exact Finset.single_le_sum
        (s := Finset.range (n + 1))
        (f := fun m => 1 ^ m * 7 ^ (n - m) * n.choose m)
        (fun m _ => Nat.zero_le _) hrange

lemma poly_four_pow_le (n : ℕ) :
    n ^ 2 * 4 ^ n ≤ 8 * 7 ^ (n - n / 8) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 12
      · interval_cases n <;> norm_num
      · have hn12 : 12 ≤ n := by omega
        have hn8lt : n - 8 < n := by omega
        have hi := ih (n - 8) hn8lt
        have hn3 : n ≤ 3 * (n - 8) := by omega
        have hnum : 9 * 4 ^ 8 ≤ 7 ^ 7 := by norm_num
        have hpow4 : 4 ^ n = 4 ^ (n - 8) * 4 ^ 8 := by
          rw [← pow_add]
          congr 1
          omega
        have hdiv : (n - 8) - (n - 8) / 8 + 7 = n - n / 8 := by omega
        calc
          n ^ 2 * 4 ^ n
              ≤ (3 * (n - 8)) ^ 2 * 4 ^ n := by
                exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn3 2)
          _ = 9 * 4 ^ 8 * ((n - 8) ^ 2 * 4 ^ (n - 8)) := by
                rw [hpow4]
                ring
          _ ≤ 9 * 4 ^ 8 * (8 * 7 ^ ((n - 8) - (n - 8) / 8)) := by
                exact Nat.mul_le_mul_left _ hi
          _ ≤ 7 ^ 7 * (8 * 7 ^ ((n - 8) - (n - 8) / 8)) := by
                exact Nat.mul_le_mul_right _ hnum
          _ = 8 * 7 ^ (n - n / 8) := by
                rw [← hdiv, pow_add]
                ring

lemma small_choose_bound (n r : ℕ) (hr : 8 * r < n) :
    n ^ 2 * n.choose r ≤ 8 * 2 ^ n := by
  have hrn : r ≤ n := by omega
  have hweight := choose_mul_seven_pow_le n r hrn
  have hrdiv : r ≤ n / 8 := by omega
  have hseven : 7 ^ (n - n / 8) ≤ 7 ^ (n - r) := by
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hrdiv n)
  have hpoly := poly_four_pow_le n
  have hmul : n ^ 2 * n.choose r * 7 ^ (n - r) ≤
      (8 * 7 ^ (n - r)) * 2 ^ n := by
    calc
      n ^ 2 * n.choose r * 7 ^ (n - r)
          = n ^ 2 * (n.choose r * 7 ^ (n - r)) := by ring
      _ ≤ n ^ 2 * 8 ^ n := Nat.mul_le_mul_left _ hweight
      _ = n ^ 2 * 4 ^ n * 2 ^ n := by
        rw [show (8 : ℕ) = 4 * 2 by norm_num, mul_pow]
        ring
      _ ≤ (8 * 7 ^ (n - n / 8)) * 2 ^ n :=
        Nat.mul_le_mul_right _ hpoly
      _ ≤ (8 * 7 ^ (n - r)) * 2 ^ n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hseven)
  exact Nat.le_of_mul_le_mul_right (by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
    (by positivity : 0 < 7 ^ (n - r))

lemma small_choose_bound_real (n r : ℕ) (hr : 8 * r < n) :
    (n.choose r : ℝ) ≤ 8 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
  have hn : 0 < n := by omega
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  have hnat : n.choose r * n ^ 2 ≤ 8 * 2 ^ n := by
    simpa [Nat.mul_comm] using small_choose_bound n r hr
  exact_mod_cast hnat


/-- The canonical increasing enumeration of a finite set of naturals. -/
noncomputable def orderedEnumerate (A : Finset ℕ) : Fin A.card → ℕ :=
  A.orderEmbOfFin rfl

theorem orderedEnumerate_strictMono (A : Finset ℕ) :
    StrictMono (orderedEnumerate A) :=
  (A.orderEmbOfFin rfl).strictMono

theorem orderedEnumerate_injective (A : Finset ℕ) :
    Function.Injective (orderedEnumerate A) :=
  (orderedEnumerate_strictMono A).injective

@[simp] theorem orderedEnumerate_mem (A : Finset ℕ) (i : Fin A.card) :
    orderedEnumerate A i ∈ A :=
  A.orderEmbOfFin_mem rfl i

@[simp] theorem map_orderedEnumerate_univ (A : Finset ℕ) :
    Finset.univ.map (A.orderEmbOfFin rfl).toEmbedding = A :=
  A.map_orderEmbOfFin_univ rfl

noncomputable def orderedIndexSubsetEmbedding (A : Finset ℕ) :
    Finset (Fin A.card) ↪ Finset ℕ :=
  (Finset.mapEmbedding (A.orderEmbOfFin rfl).toEmbedding).toEmbedding

@[simp] theorem card_orderedIndexSubsetEmbedding (A : Finset ℕ)
    (I : Finset (Fin A.card)) :
    (orderedIndexSubsetEmbedding A I).card = I.card := by
  simp [orderedIndexSubsetEmbedding]

@[simp] theorem sum_orderedIndexSubsetEmbedding (A : Finset ℕ)
    (I : Finset (Fin A.card)) :
    ∑ x ∈ orderedIndexSubsetEmbedding A I, x =
      ∑ i ∈ I, orderedEnumerate A i := by
  simp [orderedIndexSubsetEmbedding, orderedEnumerate]

theorem map_indexedSubsetSumFiber_orderedEnumerate (A : Finset ℕ) (t : ℕ) :
    (indexedSubsetSumFiber (orderedEnumerate A) t).map
        (orderedIndexSubsetEmbedding A) = subsetSumFiber A t := by
  ext S
  constructor
  · simp only [mem_map, mem_indexedSubsetSumFiber, mem_subsetSumFiber]
    rintro ⟨I, hsum, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      change x ∈ I.map (A.orderEmbOfFin rfl).toEmbedding at hx
      rw [mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact orderedEnumerate_mem A i
    · simpa using hsum
  · intro hS
    have hS' := mem_subsetSumFiber.mp hS
    let I : Finset (Fin A.card) :=
      Finset.univ.filter fun i => orderedEnumerate A i ∈ S
    have hmap : orderedIndexSubsetEmbedding A I = S := by
      ext x
      constructor
      · intro hx
        change x ∈ I.map (A.orderEmbOfFin rfl).toEmbedding at hx
        rw [mem_map] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        change orderedEnumerate A i ∈ S
        simpa [I] using hi
      · intro hx
        have hxA : x ∈ A := hS'.1 hx
        let y : A := ⟨x, hxA⟩
        let i : Fin A.card := (A.orderIsoOfFin rfl).symm y
        change x ∈ I.map (A.orderEmbOfFin rfl).toEmbedding
        rw [mem_map]
        have hienum : orderedEnumerate A i = x := by
          change A.orderEmbOfFin rfl i = x
          rw [← Finset.coe_orderIsoOfFin_apply A rfl i]
          change ((A.orderIsoOfFin rfl i : A) : ℕ) = x
          rw [show i = (A.orderIsoOfFin rfl).symm y from rfl,
            (A.orderIsoOfFin rfl).apply_symm_apply y]
        refine ⟨i, ?_, hienum⟩
        simp only [I, mem_filter, mem_univ, true_and]
        rw [hienum]
        exact hx
    rw [← hmap] at hS' ⊢
    simp only [mem_map]
    refine ⟨I, ?_, rfl⟩
    simpa using hS'.2

theorem card_indexedSubsetSumFiber_orderedEnumerate (A : Finset ℕ) (t : ℕ) :
    (indexedSubsetSumFiber (orderedEnumerate A) t).card =
      (subsetSumFiber A t).card := by
  rw [← map_indexedSubsetSumFiber_orderedEnumerate A t, card_map]

theorem map_indexedFixedCardSubsetSumFiber_orderedEnumerate
    (A : Finset ℕ) (l t : ℕ) :
    (indexedFixedCardSubsetSumFiber (orderedEnumerate A) l t).map
        (orderedIndexSubsetEmbedding A) = fixedCardSubsetSumFiber A l t := by
  ext S
  constructor
  · simp only [mem_map, mem_indexedFixedCardSubsetSumFiber,
      mem_fixedCardSubsetSumFiber]
    rintro ⟨I, ⟨hcard, hsum⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change x ∈ I.map (A.orderEmbOfFin rfl).toEmbedding at hx
      rw [mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact orderedEnumerate_mem A i
    · simpa using hcard
    · simpa using hsum
  · intro hS
    have hS' := mem_fixedCardSubsetSumFiber.mp hS
    let I : Finset (Fin A.card) :=
      Finset.univ.filter fun i => orderedEnumerate A i ∈ S
    have hmap : orderedIndexSubsetEmbedding A I = S := by
      ext x
      constructor
      · intro hx
        change x ∈ I.map (A.orderEmbOfFin rfl).toEmbedding at hx
        rw [mem_map] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        change orderedEnumerate A i ∈ S
        simpa [I] using hi
      · intro hx
        have hxA : x ∈ A := hS'.1 hx
        let y : A := ⟨x, hxA⟩
        let i : Fin A.card := (A.orderIsoOfFin rfl).symm y
        change x ∈ I.map (A.orderEmbOfFin rfl).toEmbedding
        rw [mem_map]
        have hienum : orderedEnumerate A i = x := by
          change A.orderEmbOfFin rfl i = x
          rw [← Finset.coe_orderIsoOfFin_apply A rfl i]
          change ((A.orderIsoOfFin rfl i : A) : ℕ) = x
          rw [show i = (A.orderIsoOfFin rfl).symm y from rfl,
            (A.orderIsoOfFin rfl).apply_symm_apply y]
        refine ⟨i, ?_, hienum⟩
        simp only [I, mem_filter, mem_univ, true_and]
        rw [hienum]
        exact hx
    rw [← hmap] at hS' ⊢
    simp only [mem_map]
    refine ⟨I, ?_, rfl⟩
    rw [mem_indexedFixedCardSubsetSumFiber]
    exact ⟨by simpa using hS'.2.1, by simpa using hS'.2.2⟩

theorem card_indexedFixedCardSubsetSumFiber_orderedEnumerate
    (A : Finset ℕ) (l t : ℕ) :
    (indexedFixedCardSubsetSumFiber (orderedEnumerate A) l t).card =
      (fixedCardSubsetSumFiber A l t).card := by
  rw [← map_indexedFixedCardSubsetSumFiber_orderedEnumerate A l t, card_map]

/-- Transfer any natural-valued uniform bound from strictly increasing indexed families. -/
theorem subsetSumFiber_card_le_of_ordered
    (B : ℕ → ℕ)
    (h : ∀ (n : ℕ) (a : Fin n → ℕ), StrictMono a → ∀ t : ℕ,
      (indexedSubsetSumFiber a t).card ≤ B n) :
    ∀ (A : Finset ℕ) (t : ℕ), (subsetSumFiber A t).card ≤ B A.card := by
  intro A t
  rw [← card_indexedSubsetSumFiber_orderedEnumerate A t]
  exact h A.card (orderedEnumerate A) (orderedEnumerate_strictMono A) t

/-- Transfer a fixed-layer uniform bound from strictly increasing indexed families. -/
theorem fixedCardSubsetSumFiber_card_le_of_ordered
    (B : ℕ → ℕ)
    (h : ∀ (n : ℕ) (a : Fin n → ℕ), StrictMono a → ∀ l t : ℕ,
      (indexedFixedCardSubsetSumFiber a l t).card ≤ B n) :
    ∀ (A : Finset ℕ) (l t : ℕ),
      (fixedCardSubsetSumFiber A l t).card ≤ B A.card := by
  intro A l t
  rw [← card_indexedFixedCardSubsetSumFiber_orderedEnumerate A l t]
  exact h A.card (orderedEnumerate A) (orderedEnumerate_strictMono A) l t


def lowerIndex (p : ℕ) (i : Fin p) : Fin (2 * p) :=
  ⟨i, by omega⟩

def upperIndex (p : ℕ) (i : Fin p) : Fin (2 * p) :=
  ⟨2 * p - 1 - i, by omega⟩

lemma lowerIndex_lt_upperIndex {p : ℕ} (i : Fin p) :
    lowerIndex p i < upperIndex p i := by
  simp only [lowerIndex, upperIndex, Fin.mk_lt_mk]
  omega

lemma upperIndex_strictAnti (p : ℕ) : StrictAnti (upperIndex p) := by
  intro i j hij
  simp only [upperIndex, Fin.mk_lt_mk]
  omega

def pairDiff {p : ℕ} (x : Fin (2 * p) → ℕ) (i : Fin p) : ℕ :=
  x (upperIndex p i) - x (lowerIndex p i)

lemma pairDiff_pos {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x) (i : Fin p) :
    0 < pairDiff x i := by
  rw [pairDiff]
  exact Nat.sub_pos_of_lt (hx (lowerIndex_lt_upperIndex i))

lemma pairDiff_strictAnti {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x) :
    StrictAnti (pairDiff x) := by
  intro i j hij
  have hlo : x (lowerIndex p i) < x (lowerIndex p j) := hx (by simpa [lowerIndex])
  have hup : x (upperIndex p j) < x (upperIndex p i) := hx (upperIndex_strictAnti p hij)
  have hip := pairDiff_pos hx i
  have hjp := pairDiff_pos hx j
  simp only [pairDiff] at hip hjp ⊢
  omega

lemma pairDiff_injective {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x) :
    Function.Injective (pairDiff x) :=
  (pairDiff_strictAnti hx).injective

section PairEncoding

variable (p : ℕ)

def singletonPairs (S : Finset (Fin p × Bool)) : Finset (Fin p) :=
  Finset.univ.filter fun i ↦
    (((i, false) ∈ S) ∧ (i, true) ∉ S) ∨ (((i, false) ∉ S) ∧ (i, true) ∈ S)

def upperBits (S : Finset (Fin p × Bool)) : Fin p → Bool :=
  fun i ↦ decide ((i, true) ∈ S)

def subsetOfPairData (d : Finset (Fin p) × (Fin p → Bool)) : Finset (Fin p × Bool) :=
  Finset.univ.filter fun ib ↦
    if ib.2 then d.2 ib.1 = true
    else if ib.1 ∈ d.1 then d.2 ib.1 = false else d.2 ib.1 = true

lemma mem_subsetOfPairData_false (d : Finset (Fin p) × (Fin p → Bool)) (i : Fin p) :
    (i, false) ∈ subsetOfPairData p d ↔
      (if i ∈ d.1 then d.2 i = false else d.2 i = true) := by
  simp [subsetOfPairData]

lemma mem_subsetOfPairData_true (d : Finset (Fin p) × (Fin p → Bool)) (i : Fin p) :
    (i, true) ∈ subsetOfPairData p d ↔ d.2 i := by
  simp [subsetOfPairData]

def pairDataEquiv : Finset (Fin p × Bool) ≃ Finset (Fin p) × (Fin p → Bool) where
  toFun S := (singletonPairs p S, upperBits p S)
  invFun := subsetOfPairData p
  left_inv S := by
    ext ⟨i, b⟩
    cases b <;> simp only [subsetOfPairData, singletonPairs, upperBits, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.false_eq_true, ↓reduceIte]
    · by_cases hlo : (i, false) ∈ S <;> by_cases hup : (i, true) ∈ S <;> simp [hlo, hup]
    · simp
  right_inv d := by
    apply Prod.ext
    · ext i
      by_cases hi : i ∈ d.1 <;> cases hq : d.2 i <;>
        simp [singletonPairs, subsetOfPairData, upperBits, hi, hq]
    · apply funext
      intro i
      change decide ((i, true) ∈ subsetOfPairData p (d.1, d.2)) = d.2 i
      cases hq : d.2 i <;> simp [subsetOfPairData, hq]

@[simp] lemma pairDataEquiv_fst (S : Finset (Fin p × Bool)) :
    (pairDataEquiv p S).1 = singletonPairs p S := rfl

@[simp] lemma pairDataEquiv_snd (S : Finset (Fin p × Bool)) :
    (pairDataEquiv p S).2 = upperBits p S := rfl

def singletonCountEquiv (m : ℕ) :
    {S : Finset (Fin p × Bool) // (singletonPairs p S).card = m} ≃
      {U : Finset (Fin p) // U.card = m} × (Fin p → Bool) where
  toFun S := (⟨singletonPairs p S, S.property⟩, upperBits p S)
  invFun d := ⟨(pairDataEquiv p).symm (d.1.1, d.2), by
    change (((pairDataEquiv p) ((pairDataEquiv p).symm (d.1.1, d.2))).1).card = m
    rw [(pairDataEquiv p).apply_symm_apply]
    exact d.1.2⟩
  left_inv S := by
    apply Subtype.ext
    exact (pairDataEquiv p).symm_apply_apply S
  right_inv d := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((pairDataEquiv p).apply_symm_apply (d.1.1, d.2))
    · apply funext
      intro i
      change decide ((i, true) ∈ subsetOfPairData p (d.1.1, d.2)) = d.2 i
      cases hq : d.2 i <;> simp [subsetOfPairData, hq]

lemma card_singletonCount (m : ℕ) :
    Fintype.card {S : Finset (Fin p × Bool) // (singletonPairs p S).card = m} =
      p.choose m * 2 ^ p := by
  rw [Fintype.card_congr (singletonCountEquiv p m), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  congr 1
  simpa using (@Fintype.card_finset_len (Fin p) _ m)

end PairEncoding

section PairSums


def doublePairs {p : ℕ} (S : Finset (Fin p × Bool)) : Finset (Fin p) :=
  Finset.univ.filter fun i ↦ (i, false) ∈ S ∧ (i, true) ∈ S

def upperSingletonPairs {p : ℕ} (S : Finset (Fin p × Bool)) : Finset (Fin p) :=
  Finset.univ.filter fun i ↦ (i, false) ∉ S ∧ (i, true) ∈ S

@[simp] lemma mem_singletonPairs {p : ℕ} {S : Finset (Fin p × Bool)} {i : Fin p} :
    i ∈ singletonPairs p S ↔
      (((i, false) ∈ S) ∧ (i, true) ∉ S) ∨ (((i, false) ∉ S) ∧ (i, true) ∈ S) := by
  simp [singletonPairs]

@[simp] lemma mem_doublePairs {p : ℕ} {S : Finset (Fin p × Bool)} {i : Fin p} :
    i ∈ doublePairs S ↔ (i, false) ∈ S ∧ (i, true) ∈ S := by
  simp [doublePairs]

@[simp] lemma mem_upperSingletonPairs {p : ℕ} {S : Finset (Fin p × Bool)} {i : Fin p} :
    i ∈ upperSingletonPairs S ↔ (i, false) ∉ S ∧ (i, true) ∈ S := by
  simp [upperSingletonPairs]

def pairWeight {p : ℕ} (x : Fin (2 * p) → ℕ) (ib : Fin p × Bool) : ℕ :=
  if ib.2 then x (upperIndex p ib.1) else x (lowerIndex p ib.1)

def subsetWeight {p : ℕ} (x : Fin (2 * p) → ℕ) (S : Finset (Fin p × Bool)) : ℕ :=
  ∑ ib ∈ S, pairWeight x ib

def statusBase {p : ℕ} (x : Fin (2 * p) → ℕ) (U B : Finset (Fin p)) : ℕ :=
  (∑ i ∈ U, x (lowerIndex p i)) +
    ∑ i ∈ B, (x (lowerIndex p i) + x (upperIndex p i))

def orientationWeight {p : ℕ} (x : Fin (2 * p) → ℕ) (R : Finset (Fin p)) : ℕ :=
  ∑ i ∈ R, pairDiff x i

lemma subsetWeight_eq_sum_pairContribution {p : ℕ} (x : Fin (2 * p) → ℕ)
    (S : Finset (Fin p × Bool)) :
    subsetWeight x S = ∑ i : Fin p, (
      (if (i, false) ∈ S then x (lowerIndex p i) else 0) +
      (if (i, true) ∈ S then x (upperIndex p i) else 0)) := by
  classical
  rw [subsetWeight]
  calc
    ∑ ib ∈ S, pairWeight x ib =
        ∑ ib ∈ (Finset.univ.filter fun ib : Fin p × Bool ↦ ib ∈ S), pairWeight x ib := by
          congr 1
          ext ib
          simp
    _ = ∑ ib : Fin p × Bool, if ib ∈ S then pairWeight x ib else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ i : Fin p, (
        (if (i, false) ∈ S then x (lowerIndex p i) else 0) +
        (if (i, true) ∈ S then x (upperIndex p i) else 0)) := by
          rw [Fintype.sum_prod_type]
          simp [pairWeight, add_comm]

lemma pairContribution_eq_status {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (S : Finset (Fin p × Bool)) (i : Fin p) :
    (if (i, false) ∈ S then x (lowerIndex p i) else 0) +
        (if (i, true) ∈ S then x (upperIndex p i) else 0) =
      (if i ∈ singletonPairs p S then x (lowerIndex p i) else 0) +
      (if i ∈ doublePairs S then x (lowerIndex p i) + x (upperIndex p i) else 0) +
      (if i ∈ upperSingletonPairs S then pairDiff x i else 0) := by
  have hle : x (lowerIndex p i) ≤ x (upperIndex p i) :=
    (hx (lowerIndex_lt_upperIndex i)).le
  by_cases hlo : (i, false) ∈ S <;> by_cases hup : (i, true) ∈ S <;>
    simp [hlo, hup, pairDiff, hle]

lemma subsetWeight_decomposition {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (S : Finset (Fin p × Bool)) :
    subsetWeight x S =
      statusBase x (singletonPairs p S) (doublePairs S) +
        orientationWeight x (upperSingletonPairs S) := by
  classical
  rw [subsetWeight_eq_sum_pairContribution]
  simp only [statusBase, orientationWeight]
  simp_rw [pairContribution_eq_status hx S]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_filter]
  simp [singletonPairs, doublePairs, upperSingletonPairs]

lemma subsetCard_decomposition {p : ℕ} (S : Finset (Fin p × Bool)) :
    S.card = (singletonPairs p S).card + 2 * (doublePairs S).card := by
  classical
  have hlocal (i : Fin p) :
      (if (i, false) ∈ S then 1 else 0) + (if (i, true) ∈ S then 1 else 0) =
        (if i ∈ singletonPairs p S then 1 else 0) +
          2 * (if i ∈ doublePairs S then 1 else 0) := by
    by_cases hlo : (i, false) ∈ S <;> by_cases hup : (i, true) ∈ S <;>
      simp [hlo, hup]
  calc
    S.card = ∑ _ib ∈ S, 1 := by simp
    _ = ∑ i : Fin p, (
        (if (i, false) ∈ S then 1 else 0) + (if (i, true) ∈ S then 1 else 0)) := by
      calc
        ∑ _ib ∈ S, 1 =
            ∑ ib ∈ (Finset.univ.filter fun ib : Fin p × Bool ↦ ib ∈ S), 1 := by
              congr 1
              ext ib
              simp
        _ = ∑ ib : Fin p × Bool, if ib ∈ S then 1 else 0 := by rw [Finset.sum_filter]
        _ = _ := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          rw [Fintype.sum_bool]
          simp [add_comm]
    _ = ∑ i : Fin p, (
        (if i ∈ singletonPairs p S then 1 else 0) +
          2 * (if i ∈ doublePairs S then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hlocal i
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [← Finset.sum_filter]
      simp [singletonPairs, doublePairs]

lemma upperSingletonPairs_subset_singletonPairs {p : ℕ} (S : Finset (Fin p × Bool)) :
    upperSingletonPairs S ⊆ singletonPairs p S := by
  intro i hi
  simp only [mem_upperSingletonPairs] at hi
  simp [hi.1, hi.2]

lemma pairSubset_ext_of_status {p : ℕ} {S T : Finset (Fin p × Bool)}
    (hU : singletonPairs p S = singletonPairs p T)
    (hB : doublePairs S = doublePairs T)
    (hR : upperSingletonPairs S = upperSingletonPairs T) : S = T := by
  ext ⟨i, b⟩
  have hu := Finset.ext_iff.mp hU i
  have hb := Finset.ext_iff.mp hB i
  have hr := Finset.ext_iff.mp hR i
  simp only [mem_singletonPairs] at hu
  simp only [mem_doublePairs] at hb
  simp only [mem_upperSingletonPairs] at hr
  cases b <;> tauto

def orientationIn {p : ℕ} (U : Finset (Fin p)) (S : Finset (Fin p × Bool)) : Finset U :=
  U.attach.filter fun i ↦ (i : Fin p) ∈ upperSingletonPairs S

@[simp] lemma mem_orientationIn {p : ℕ} {U : Finset (Fin p)} {S : Finset (Fin p × Bool)}
    {i : U} : i ∈ orientationIn U S ↔ (i : Fin p) ∈ upperSingletonPairs S := by
  simp [orientationIn]

lemma orientationIn_map_val {p : ℕ} {U : Finset (Fin p)} {S : Finset (Fin p × Bool)}
    (hU : singletonPairs p S = U) :
    (orientationIn U S).map ⟨Subtype.val, Subtype.val_injective⟩ = upperSingletonPairs S := by
  ext i
  constructor
  · simp only [Finset.mem_map, mem_orientationIn]
    rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    have hiU : i ∈ U := by
      rw [← hU]
      exact upperSingletonPairs_subset_singletonPairs S hi
    simp only [Finset.mem_map, mem_orientationIn]
    exact ⟨⟨i, hiU⟩, hi, rfl⟩

lemma orientationIn_sum {p : ℕ} {x : Fin (2 * p) → ℕ} {U : Finset (Fin p)}
    {S : Finset (Fin p × Bool)} (hU : singletonPairs p S = U) :
    (∑ i ∈ orientationIn U S, pairDiff x (i : Fin p)) =
      orientationWeight x (upperSingletonPairs S) := by
  classical
  rw [orientationWeight, ← orientationIn_map_val hU]
  simpa using Finset.sum_map (orientationIn U S) ⟨Subtype.val, Subtype.val_injective⟩
    (fun i : Fin p ↦ pairDiff x i)

lemma orientationIn_injective_on_status {p : ℕ} (U B : Finset (Fin p)) :
    Set.InjOn (orientationIn U)
      {S : Finset (Fin p × Bool) | singletonPairs p S = U ∧ doublePairs S = B} := by
  intro S hS T hT hO
  apply pairSubset_ext_of_status (hS.1.trans hT.1.symm) (hS.2.trans hT.2.symm)
  ext i
  by_cases hi : i ∈ U
  · have hm := Finset.ext_iff.mp hO ⟨i, hi⟩
    simpa only [mem_orientationIn] using hm
  · have hSi : i ∉ upperSingletonPairs S := fun h ↦
      hi (hS.1 ▸ upperSingletonPairs_subset_singletonPairs S h)
    have hTi : i ∉ upperSingletonPairs T := fun h ↦
      hi (hT.1 ▸ upperSingletonPairs_subset_singletonPairs T h)
    simp [hSi, hTi]

end PairSums

section StatusFibers

def fixedPairFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (l t : ℕ) :
    Finset (Finset (Fin p × Bool)) :=
  Finset.univ.filter fun S ↦ S.card = l ∧ subsetWeight x S = t

def fixedStatusFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (l t : ℕ)
    (U B : Finset (Fin p)) : Finset (Finset (Fin p × Bool)) :=
  (fixedPairFiber x l t).filter fun S ↦ singletonPairs p S = U ∧ doublePairs S = B

def orientationFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (t : ℕ)
    (U B : Finset (Fin p)) : Finset (Finset U) :=
  U.attach.powerset.filter fun R ↦
    statusBase x U B + ∑ i ∈ R, pairDiff x (i : Fin p) = t

lemma orientationIn_mem_orientationFiber {p : ℕ} {x : Fin (2 * p) → ℕ}
    (hx : StrictMono x) {l t : ℕ} {U B : Finset (Fin p)}
    {S : Finset (Fin p × Bool)} (hS : S ∈ fixedStatusFiber x l t U B) :
    orientationIn U S ∈ orientationFiber x t U B := by
  rcases Finset.mem_filter.mp hS with ⟨hSol, hU, hB⟩
  rcases Finset.mem_filter.mp hSol with ⟨-, -, hwt⟩
  rw [orientationFiber, Finset.mem_filter]
  constructor
  · exact Finset.mem_powerset.mpr (by intro i _; simpa using i.2)
  · rw [orientationIn_sum hU]
    rw [← hU, ← hB, ← subsetWeight_decomposition hx S]
    exact hwt

lemma fixedStatusFiber_card_le_orientationFiber_card {p : ℕ} {x : Fin (2 * p) → ℕ}
    (hx : StrictMono x) (l t : ℕ) (U B : Finset (Fin p)) :
    (fixedStatusFiber x l t U B).card ≤ (orientationFiber x t U B).card := by
  let f : {S // S ∈ fixedStatusFiber x l t U B} → {R // R ∈ orientationFiber x t U B} :=
    fun S ↦ ⟨orientationIn U S, orientationIn_mem_orientationFiber hx S.2⟩
  have hf : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply orientationIn_injective_on_status U B
    · rcases Finset.mem_filter.mp S.2 with ⟨-, hU, hB⟩
      exact ⟨hU, hB⟩
    · rcases Finset.mem_filter.mp T.2 with ⟨-, hU, hB⟩
      exact ⟨hU, hB⟩
    · exact congrArg Subtype.val h
  simpa using Fintype.card_le_of_injective f hf

def IndexedScalarBound (C : ℝ) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (w : α → ℕ), Function.Injective w →
    (∀ i, 0 < w i) → 1 ≤ Fintype.card α → ∀ b t : ℕ,
      (((Finset.univ.powerset.filter fun R ↦ b + ∑ i ∈ R, w i = t).card : ℝ) ≤
        C * (2 : ℝ) ^ Fintype.card α / Real.sqrt (Fintype.card α) ^ 3)

lemma orientationFiber_real_card_le {C : ℝ} (hscalar : IndexedScalarBound C)
    {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (t : ℕ) (U B : Finset (Fin p)) (hU : 1 ≤ U.card) :
    ((orientationFiber x t U B).card : ℝ) ≤
      C * (2 : ℝ) ^ U.card / Real.sqrt U.card ^ 3 := by
  let w : U → ℕ := fun i ↦ pairDiff x (i : Fin p)
  have hwi : Function.Injective w := (pairDiff_injective hx).comp Subtype.val_injective
  have hwp : ∀ i, 0 < w i := fun i ↦ pairDiff_pos hx _
  have hs := hscalar w hwi hwp (by simpa using hU) (statusBase x U B) t
  simpa [orientationFiber, w] using hs

lemma fixedStatusFiber_real_card_le {C : ℝ} (hscalar : IndexedScalarBound C)
    {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (l t : ℕ) (U B : Finset (Fin p)) (hU : 1 ≤ U.card) :
    ((fixedStatusFiber x l t U B).card : ℝ) ≤
      C * (2 : ℝ) ^ U.card / Real.sqrt U.card ^ 3 := by
  calc
    ((fixedStatusFiber x l t U B).card : ℝ) ≤
        ((orientationFiber x t U B).card : ℝ) := by
      exact_mod_cast fixedStatusFiber_card_le_orientationFiber_card hx l t U B
    _ ≤ _ := orientationFiber_real_card_le hscalar hx t U B hU

end StatusFibers

section Aggregation

@[simp] lemma singletonPairs_subsetOfPairData (p : ℕ) (U : Finset (Fin p)) (q : Fin p → Bool) :
    singletonPairs p (subsetOfPairData p (U, q)) = U := by
  have h := congrArg Prod.fst ((pairDataEquiv p).apply_symm_apply (U, q))
  exact h

lemma doublePairs_subsetOfPairData (p : ℕ) (U : Finset (Fin p)) (q : Fin p → Bool) :
    doublePairs (subsetOfPairData p (U, q)) =
      Finset.univ.filter fun i ↦ i ∉ U ∧ q i = true := by
  ext i
  by_cases hi : i ∈ U <;> cases hq : q i <;>
    simp [doublePairs, subsetOfPairData, hi, hq]

lemma upperSingletonPairs_subsetOfPairData (p : ℕ) (U : Finset (Fin p)) (q : Fin p → Bool) :
    upperSingletonPairs (subsetOfPairData p (U, q)) =
      U.filter fun i ↦ q i = true := by
  ext i
  by_cases hi : i ∈ U <;> cases hq : q i <;>
    simp [upperSingletonPairs, subsetOfPairData, hi, hq]

def statusBits {p : ℕ} (U B : Finset (Fin p)) (R : Finset U) : Fin p → Bool :=
  fun i ↦ if hi : i ∈ U then decide (⟨i, hi⟩ ∈ R) else decide (i ∈ B)

lemma statusBits_outside {p : ℕ} {U B : Finset (Fin p)} (R : Finset U)
    {i : Fin p} (hi : i ∉ U) : statusBits U B R i = decide (i ∈ B) := by
  simp [statusBits, hi]

lemma doublePairs_statusBits {p : ℕ} {U B : Finset (Fin p)} (hUB : Disjoint U B)
    (R : Finset U) :
    doublePairs (subsetOfPairData p (U, statusBits U B R)) = B := by
  rw [doublePairs_subsetOfPairData]
  ext i
  by_cases hi : i ∈ U
  · have hiB : i ∉ B := Finset.disjoint_left.mp hUB hi
    simp [hi, hiB]
  · rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [statusBits_outside R hi]
    simp [hi]

lemma orientationIn_statusBits {p : ℕ} (U B : Finset (Fin p)) (R : Finset U) :
    orientationIn U (subsetOfPairData p (U, statusBits U B R)) = R := by
  rw [orientationIn]
  ext i
  rw [Finset.mem_filter]
  simp only [Finset.mem_attach, true_and]
  rw [upperSingletonPairs_subsetOfPairData, Finset.mem_filter]
  simp only [i.2, true_and]
  have hb : statusBits U B R i = decide (i ∈ R) := by simp [statusBits, i.2]
  rw [hb]
  simp [i.2]

def statusOrientationEquiv {p : ℕ} (U B : Finset (Fin p)) (hUB : Disjoint U B) :
    {S : Finset (Fin p × Bool) // singletonPairs p S = U ∧ doublePairs S = B} ≃ Finset U where
  toFun S := orientationIn U S
  invFun R := ⟨subsetOfPairData p (U, statusBits U B R), by
    exact ⟨singletonPairs_subsetOfPairData p U _, doublePairs_statusBits hUB R⟩⟩
  left_inv S := by
    apply Subtype.ext
    apply orientationIn_injective_on_status U B
      ⟨singletonPairs_subsetOfPairData p U _, doublePairs_statusBits hUB _⟩ S.2
    exact orientationIn_statusBits U B _
  right_inv R := orientationIn_statusBits U B R

lemma card_eq_sum_card_filter_fiber {α β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card = ∑ b : β, (s.filter fun a ↦ f a = b).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, ih]
      simp only [Finset.filter_insert]
      calc
        (∑ b : β, (s.filter fun z ↦ f z = b).card) + 1 =
            (∑ b : β, (s.filter fun z ↦ f z = b).card) +
              ∑ b : β, if f a = b then 1 else 0 := by simp
        _ = ∑ b : β, ((s.filter fun z ↦ f z = b).card +
              (if f a = b then 1 else 0)) := by rw [Finset.sum_add_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases h : f a = b
          · simp [h, ha]
          · simp [h]

lemma card_filter_univ_eq_card_subtype {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card = Fintype.card {a : α // P a} := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun a ↦ ⟨a, (Finset.mem_filter.mp a.2).2⟩
      invFun := fun a ↦ ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

lemma fixedPairFiber_card_eq_sum_status {p : ℕ} (x : Fin (2 * p) → ℕ) (l t : ℕ) :
    (fixedPairFiber x l t).card =
      ∑ st : Finset (Fin p) × Finset (Fin p),
        (fixedStatusFiber x l t st.1 st.2).card := by
  simpa [fixedStatusFiber, Prod.ext_iff] using
    card_eq_sum_card_filter_fiber (fixedPairFiber x l t)
      (fun S ↦ (singletonPairs p S, doublePairs S))

def fixedCardPairFiber (p l : ℕ) : Finset (Finset (Fin p × Bool)) :=
  Finset.univ.filter fun S ↦ S.card = l

def fixedCardStatusFiber (p l : ℕ) (U B : Finset (Fin p)) :
    Finset (Finset (Fin p × Bool)) :=
  (fixedCardPairFiber p l).filter fun S ↦ singletonPairs p S = U ∧ doublePairs S = B

lemma fixedCardPairFiber_card (p l : ℕ) :
    (fixedCardPairFiber p l).card = (2 * p).choose l := by
  have heq : fixedCardPairFiber p l = (Finset.univ : Finset (Fin p × Bool)).powersetCard l := by
    ext S
    simp [fixedCardPairFiber]
  rw [heq, Finset.card_powersetCard]
  simp [Fintype.card_prod, Nat.mul_comm]

lemma fixedCardPairFiber_card_eq_sum_status (p l : ℕ) :
    (fixedCardPairFiber p l).card =
      ∑ st : Finset (Fin p) × Finset (Fin p),
        (fixedCardStatusFiber p l st.1 st.2).card := by
  simpa [fixedCardStatusFiber, Prod.ext_iff] using
    card_eq_sum_card_filter_fiber (fixedCardPairFiber p l)
      (fun S ↦ (singletonPairs p S, doublePairs S))

lemma singletonPairs_disjoint_doublePairs {p : ℕ} (S : Finset (Fin p × Bool)) :
    Disjoint (singletonPairs p S) (doublePairs S) := by
  rw [Finset.disjoint_left]
  intro i hiU hiB
  simp only [mem_singletonPairs] at hiU
  simp only [mem_doublePairs] at hiB
  tauto

lemma fixedCardStatusFiber_card_of_feasible {p l : ℕ} {U B : Finset (Fin p)}
    (hUB : Disjoint U B) (hcard : U.card + 2 * B.card = l) :
    (fixedCardStatusFiber p l U B).card = 2 ^ U.card := by
  have heq : fixedCardStatusFiber p l U B =
      Finset.univ.filter fun S : Finset (Fin p × Bool) ↦
        singletonPairs p S = U ∧ doublePairs S = B := by
    ext S
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
    · intro h
      have hs := (Finset.mem_filter.mp h).2
      have hc := subsetCard_decomposition S
      rw [hs.1, hs.2, hcard] at hc
      simpa [fixedCardStatusFiber, fixedCardPairFiber, hc] using h
  rw [heq]
  calc
    (Finset.univ.filter fun S : Finset (Fin p × Bool) ↦
        singletonPairs p S = U ∧ doublePairs S = B).card =
        Fintype.card {S : Finset (Fin p × Bool) //
          singletonPairs p S = U ∧ doublePairs S = B} :=
      card_filter_univ_eq_card_subtype _
    _ = Fintype.card (Finset U) := Fintype.card_congr (statusOrientationEquiv U B hUB)
    _ = 2 ^ U.card := by simpa using (Fintype.card_finset (U : Type))

lemma fixedStatusFiber_feasible {p : ℕ} {x : Fin (2 * p) → ℕ} {l t : ℕ}
    {U B : Finset (Fin p)} (hne : (fixedStatusFiber x l t U B).Nonempty) :
    Disjoint U B ∧ U.card + 2 * B.card = l := by
  rcases hne with ⟨S, hS⟩
  rcases Finset.mem_filter.mp hS with ⟨hSol, hU, hB⟩
  rcases Finset.mem_filter.mp hSol with ⟨-, hcard, -⟩
  constructor
  · rw [← hU, ← hB]
    exact singletonPairs_disjoint_doublePairs S
  · rw [← hU, ← hB, ← subsetCard_decomposition S]
    exact hcard

def activeStatusMass {p : ℕ} (x : Fin (2 * p) → ℕ) (l t q : ℕ) : ℕ :=
  ∑ st : Finset (Fin p) × Finset (Fin p),
    if (fixedStatusFiber x l t st.1 st.2).Nonempty ∧ q ≤ st.1.card
    then 2 ^ st.1.card else 0

lemma activeStatusMass_le_choose {p : ℕ} (x : Fin (2 * p) → ℕ) (l t q : ℕ) :
    activeStatusMass x l t q ≤ (2 * p).choose l := by
  rw [← fixedCardPairFiber_card p l, fixedCardPairFiber_card_eq_sum_status]
  apply Finset.sum_le_sum
  intro st _
  by_cases h : (fixedStatusFiber x l t st.1 st.2).Nonempty ∧ q ≤ st.1.card
  · rw [if_pos h]
    exact (fixedCardStatusFiber_card_of_feasible
      (fixedStatusFiber_feasible h.1).1 (fixedStatusFiber_feasible h.1).2).ge
  · simp [h]

def lowPairFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (l t q : ℕ) :
    Finset (Finset (Fin p × Bool)) :=
  (fixedPairFiber x l t).filter fun S ↦ (singletonPairs p S).card < q

def highPairFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (l t q : ℕ) :
    Finset (Finset (Fin p × Bool)) :=
  (fixedPairFiber x l t).filter fun S ↦ q ≤ (singletonPairs p S).card

def highStatusFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (l t q : ℕ)
    (U B : Finset (Fin p)) : Finset (Finset (Fin p × Bool)) :=
  (highPairFiber x l t q).filter fun S ↦ singletonPairs p S = U ∧ doublePairs S = B

lemma fixedPairFiber_card_eq_low_add_high {p : ℕ} (x : Fin (2 * p) → ℕ)
    (l t q : ℕ) :
    (fixedPairFiber x l t).card =
      (lowPairFiber x l t q).card + (highPairFiber x l t q).card := by
  rw [← Finset.card_filter_add_card_filter_not
    (fun S : Finset (Fin p × Bool) ↦ (singletonPairs p S).card < q)]
  congr 2
  ext S
  simp [lowPairFiber, highPairFiber]

lemma highPairFiber_card_eq_sum_status {p : ℕ} (x : Fin (2 * p) → ℕ)
    (l t q : ℕ) :
    (highPairFiber x l t q).card =
      ∑ st : Finset (Fin p) × Finset (Fin p),
        (highStatusFiber x l t q st.1 st.2).card := by
  simpa [highStatusFiber, Prod.ext_iff] using
    card_eq_sum_card_filter_fiber (highPairFiber x l t q)
      (fun S ↦ (singletonPairs p S, doublePairs S))

lemma highStatusFiber_eq_fixedStatusFiber {p : ℕ} {x : Fin (2 * p) → ℕ}
    {l t q : ℕ} {U B : Finset (Fin p)} (hq : q ≤ U.card) :
    highStatusFiber x l t q U B = fixedStatusFiber x l t U B := by
  ext S
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hHigh, hU, hB⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hHigh).1, hU, hB⟩
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hFixed, hU, hB⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hFixed, by simpa [hU] using hq⟩, hU, hB⟩

lemma highPairFiber_real_card_le {C D : ℝ} (hscalar : IndexedScalarBound C)
    (hD : 0 ≤ D) {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (l t q : ℕ) (hq1 : 1 ≤ q)
    (hscale : ∀ m : ℕ, q ≤ m →
      C * (2 : ℝ) ^ m / Real.sqrt m ^ 3 ≤ D * (2 : ℝ) ^ m) :
    ((highPairFiber x l t q).card : ℝ) ≤ D * (2 * p).choose l := by
  rw [highPairFiber_card_eq_sum_status]
  push_cast
  calc
    ∑ st : Finset (Fin p) × Finset (Fin p),
        ((highStatusFiber x l t q st.1 st.2).card : ℝ) ≤
      ∑ st : Finset (Fin p) × Finset (Fin p),
        D * (if (fixedStatusFiber x l t st.1 st.2).Nonempty ∧ q ≤ st.1.card
          then (2 : ℝ) ^ st.1.card else 0) := by
      apply Finset.sum_le_sum
      intro st _
      by_cases hne : (highStatusFiber x l t q st.1 st.2).Nonempty
      · rcases hne with ⟨S, hS⟩
        rcases Finset.mem_filter.mp hS with ⟨hHigh, hU, hB⟩
        rcases Finset.mem_filter.mp hHigh with ⟨hFixed, hq⟩
        have hfix : (fixedStatusFiber x l t st.1 st.2).Nonempty :=
          ⟨S, Finset.mem_filter.mpr ⟨hFixed, hU, hB⟩⟩
        rw [if_pos ⟨hfix, by simpa [hU] using hq⟩]
        rw [highStatusFiber_eq_fixedStatusFiber (by simpa [hU] using hq)]
        exact (fixedStatusFiber_real_card_le hscalar hx l t st.1 st.2
          (hq1.trans (by simpa [hU] using hq))).trans (hscale _ (by simpa [hU] using hq))
      · have hz : (highStatusFiber x l t q st.1 st.2).card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
        have hnact : ¬ ((fixedStatusFiber x l t st.1 st.2).Nonempty ∧ q ≤ st.1.card) := by
          intro h
          apply hne
          rw [highStatusFiber_eq_fixedStatusFiber h.2]
          exact h.1
        rw [hz, if_neg hnact]
        simp
    _ = D * (activeStatusMass x l t q : ℝ) := by
      rw [activeStatusMass, Nat.cast_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro st _
      by_cases h : (fixedStatusFiber x l t st.1 st.2).Nonempty ∧ q ≤ st.1.card <;>
        simp [h]
    _ ≤ D * (2 * p).choose l := by
      gcongr
      exact_mod_cast activeStatusMass_le_choose x l t q

theorem fixedPairFiber_real_card_le_low_add {C D : ℝ} (hscalar : IndexedScalarBound C)
    (hD : 0 ≤ D) {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (l t q : ℕ) (hq1 : 1 ≤ q)
    (hscale : ∀ m : ℕ, q ≤ m →
      C * (2 : ℝ) ^ m / Real.sqrt m ^ 3 ≤ D * (2 : ℝ) ^ m) :
    ((fixedPairFiber x l t).card : ℝ) ≤
      (lowPairFiber x l t q).card + D * (2 * p).choose l := by
  rw [fixedPairFiber_card_eq_low_add_high]
  push_cast
  gcongr
  exact highPairFiber_real_card_le hscalar hD hx l t q hq1 hscale

def lowSingletonEquiv (p q : ℕ) :
    {S : Finset (Fin p × Bool) // (singletonPairs p S).card < q} ≃
      {U : Finset (Fin p) // U.card < q} × (Fin p → Bool) where
  toFun S := (⟨singletonPairs p S, S.property⟩, upperBits p S)
  invFun d := ⟨subsetOfPairData p (d.1.1, d.2), by
    rw [singletonPairs_subsetOfPairData]
    exact d.1.2⟩
  left_inv S := by
    apply Subtype.ext
    exact (pairDataEquiv p).symm_apply_apply S
  right_inv d := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((pairDataEquiv p).apply_symm_apply (d.1.1, d.2))
    · apply funext
      intro i
      change decide ((i, true) ∈ subsetOfPairData p (d.1.1, d.2)) = d.2 i
      cases hq : d.2 i <;> simp [subsetOfPairData, hq]

lemma card_all_low_singletons (p q : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin p × Bool) ↦
      (singletonPairs p S).card < q).card =
      Fintype.card {U : Finset (Fin p) // U.card < q} * 2 ^ p := by
  calc
    _ = Fintype.card {S : Finset (Fin p × Bool) // (singletonPairs p S).card < q} :=
      card_filter_univ_eq_card_subtype _
    _ = Fintype.card ({U : Finset (Fin p) // U.card < q} × (Fin p → Bool)) :=
      Fintype.card_congr (lowSingletonEquiv p q)
    _ = _ := by simp [Fintype.card_prod, Fintype.card_fun]

lemma lowPairFiber_card_le (p : ℕ) (x : Fin (2 * p) → ℕ) (l t q : ℕ) :
    (lowPairFiber x l t q).card ≤
      Fintype.card {U : Finset (Fin p) // U.card < q} * 2 ^ p := by
  rw [← card_all_low_singletons p q]
  apply Finset.card_le_card
  intro S hS
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2⟩

theorem fixedPairFiber_real_card_le_of_numerical {C D E F : ℝ}
    (hscalar : IndexedScalarBound C) (hD : 0 ≤ D)
    {p : ℕ} {x : Fin (2 * p) → ℕ} (hx : StrictMono x)
    (l t q : ℕ) (hq1 : 1 ≤ q)
    (hscale : ∀ m : ℕ, q ≤ m →
      C * (2 : ℝ) ^ m / Real.sqrt m ^ 3 ≤ D * (2 : ℝ) ^ m)
    (hlow : (Fintype.card {U : Finset (Fin p) // U.card < q} : ℝ) * (2 : ℝ) ^ p ≤
      E * (4 : ℝ) ^ p / (p : ℝ) ^ 2)
    (hhigh : D * ((2 * p).choose l : ℝ) ≤
      F * (4 : ℝ) ^ p / (p : ℝ) ^ 2) :
    ((fixedPairFiber x l t).card : ℝ) ≤
      (E + F) * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  calc
    ((fixedPairFiber x l t).card : ℝ) ≤
        (lowPairFiber x l t q).card + D * (2 * p).choose l :=
      fixedPairFiber_real_card_le_low_add hscalar hD hx l t q hq1 hscale
    _ ≤ (Fintype.card {U : Finset (Fin p) // U.card < q} : ℝ) * (2 : ℝ) ^ p +
        D * ((2 * p).choose l : ℝ) := by
      gcongr
      exact_mod_cast lowPairFiber_card_le p x l t q
    _ ≤ E * (4 : ℝ) ^ p / (p : ℝ) ^ 2 +
        F * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := add_le_add hlow hhigh
    _ = _ := by ring

def oddPairFiber {p : ℕ} (x : Fin (2 * p) → ℕ) (z l t : ℕ) :
    Finset (Finset (Fin p × Bool) × Bool) :=
  Finset.univ.filter fun d ↦
    d.1.card + (if d.2 then 1 else 0) = l ∧
      subsetWeight x d.1 + (if d.2 then z else 0) = t

lemma oddPairFiber_card_le_two_even {p : ℕ} (x : Fin (2 * p) → ℕ) (z l t : ℕ) :
    (oddPairFiber x z l t).card ≤
      (fixedPairFiber x l t).card + (fixedPairFiber x (l - 1) (t - z)).card := by
  let f : {d // d ∈ oddPairFiber x z l t} →
      {S // S ∈ fixedPairFiber x l t} ⊕ {S // S ∈ fixedPairFiber x (l - 1) (t - z)} :=
    fun d ↦ if hb : d.1.2 = false then
      Sum.inl ⟨d.1.1, by
        rcases Finset.mem_filter.mp d.2 with ⟨-, hc, hs⟩
        rw [fixedPairFiber, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        simpa [hb] using And.intro hc hs⟩
    else
      Sum.inr ⟨d.1.1, by
        rcases Finset.mem_filter.mp d.2 with ⟨-, hc, hs⟩
        have hb' : d.1.2 = true := Bool.eq_true_of_not_eq_false hb
        rw [fixedPairFiber, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        constructor <;> simp [hb'] at hc hs ⊢ <;> omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rcases a with ⟨⟨Sa, ba⟩, ha⟩
    rcases b with ⟨⟨Sb, bb⟩, hb⟩
    change (⟨Sa, ba⟩ : Finset (Fin p × Bool) × Bool) = ⟨Sb, bb⟩
    cases hba : ba <;> cases hbb : bb <;> simp [f, hba, hbb] at hab ⊢
    all_goals exact hab
  simpa [Fintype.card_sum] using Fintype.card_le_of_injective f hf

lemma oddPairFiber_real_card_le_of_even
    {p : ℕ} (x : Fin (2 * p) → ℕ) (z l t K : ℕ)
    (h₀ : (fixedPairFiber x l t).card ≤ K)
    (h₁ : (fixedPairFiber x (l - 1) (t - z)).card ≤ K) :
    (oddPairFiber x z l t).card ≤ 2 * K := by
  exact (oddPairFiber_card_le_two_even x z l t).trans (by omega)

end Aggregation


def cutoff (p : ℕ) : ℕ := (p + 7) / 8

lemma cutoff_pos {p : ℕ} (hp : 1 ≤ p) : 1 ≤ cutoff p := by
  simp only [cutoff]
  omega

lemma eight_mul_lt_of_lt_cutoff {p m : ℕ} (hm : m < cutoff p) : 8 * m < p := by
  simp only [cutoff] at hm
  omega

lemma p_le_eight_mul_cutoff (p : ℕ) : p ≤ 8 * cutoff p := by
  simp only [cutoff]
  omega

lemma cutoff_le {p : ℕ} (hp : 1 ≤ p) : cutoff p ≤ p := by
  simp only [cutoff]
  omega

lemma poly_cube_four_pow_le (n : ℕ) :
    n ^ 3 * 4 ^ n ≤ 64 * 7 ^ (n - n / 8) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 16
      · interval_cases n <;> norm_num
      · have hn16 : 16 ≤ n := by omega
        have hn8lt : n - 8 < n := by omega
        have hi := ih (n - 8) hn8lt
        have hn2 : n ≤ 2 * (n - 8) := by omega
        have hnum : 8 * 4 ^ 8 ≤ 7 ^ 7 := by norm_num
        have hpow4 : 4 ^ n = 4 ^ (n - 8) * 4 ^ 8 := by
          rw [← pow_add]
          congr 1
          omega
        have hdiv : (n - 8) - (n - 8) / 8 + 7 = n - n / 8 := by omega
        calc
          n ^ 3 * 4 ^ n ≤ (2 * (n - 8)) ^ 3 * 4 ^ n := by
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn2 3)
          _ = 8 * 4 ^ 8 * ((n - 8) ^ 3 * 4 ^ (n - 8)) := by
            rw [hpow4]
            ring
          _ ≤ 8 * 4 ^ 8 * (64 * 7 ^ ((n - 8) - (n - 8) / 8)) := by
            exact Nat.mul_le_mul_left _ hi
          _ ≤ 7 ^ 7 * (64 * 7 ^ ((n - 8) - (n - 8) / 8)) := by
            exact Nat.mul_le_mul_right _ hnum
          _ = 64 * 7 ^ (n - n / 8) := by
            rw [← hdiv, pow_add]
            ring

lemma small_choose_bound_cube (n r : ℕ) (hr : 8 * r < n) :
    n ^ 3 * n.choose r ≤ 64 * 2 ^ n := by
  have hrn : r ≤ n := by omega
  have hweight := choose_mul_seven_pow_le n r hrn
  have hrdiv : r ≤ n / 8 := by omega
  have hseven : 7 ^ (n - n / 8) ≤ 7 ^ (n - r) := by
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hrdiv n)
  have hpoly := poly_cube_four_pow_le n
  have hmul : n ^ 3 * n.choose r * 7 ^ (n - r) ≤
      (64 * 7 ^ (n - r)) * 2 ^ n := by
    calc
      n ^ 3 * n.choose r * 7 ^ (n - r)
          = n ^ 3 * (n.choose r * 7 ^ (n - r)) := by ring
      _ ≤ n ^ 3 * 8 ^ n := Nat.mul_le_mul_left _ hweight
      _ = n ^ 3 * 4 ^ n * 2 ^ n := by
        rw [show (8 : ℕ) = 4 * 2 by norm_num, mul_pow]
        ring
      _ ≤ (64 * 7 ^ (n - n / 8)) * 2 ^ n :=
        Nat.mul_le_mul_right _ hpoly
      _ ≤ (64 * 7 ^ (n - r)) * 2 ^ n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 hseven)
  exact Nat.le_of_mul_le_mul_right (by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
    (by positivity : 0 < 7 ^ (n - r))

lemma low_choose_sum_bound (p : ℕ) (hp : 1 ≤ p) :
    p ^ 2 * (∑ m ∈ Finset.range (cutoff p), p.choose m) ≤ 64 * 2 ^ p := by
  have heach (m : ℕ) (hm : m ∈ Finset.range (cutoff p)) :
      p ^ 3 * p.choose m ≤ 64 * 2 ^ p :=
    small_choose_bound_cube p m (eight_mul_lt_of_lt_cutoff (Finset.mem_range.mp hm))
  have hsum :
      ∑ m ∈ Finset.range (cutoff p), p ^ 3 * p.choose m ≤
        ∑ _m ∈ Finset.range (cutoff p), 64 * 2 ^ p :=
    Finset.sum_le_sum heach
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hscaled :
      p ^ 3 * (∑ m ∈ Finset.range (cutoff p), p.choose m) ≤ p * (64 * 2 ^ p) :=
    hsum.trans (Nat.mul_le_mul_right _ (cutoff_le hp))
  apply Nat.le_of_mul_le_mul_left (c := p) _ (by omega)
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled

lemma low_subtype_card_eq_sum_choose (p q : ℕ) :
    Fintype.card {U : Finset (Fin p) // U.card < q} =
      ∑ m ∈ Finset.range q, p.choose m := by
  let s := (Finset.univ : Finset (Finset (Fin p))).filter fun U ↦ U.card < q
  have hmaps : (s : Set (Finset (Fin p))).MapsTo Finset.card (Finset.range q) := by
    intro U hU
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hU).2
  rw [← card_filter_univ_eq_card_subtype (fun U : Finset (Fin p) ↦ U.card < q)]
  change s.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m < q := Finset.mem_range.mp hm
  have heq : (s.filter fun U ↦ U.card = m) =
      (Finset.univ : Finset (Fin p)).powersetCard m := by
    ext U
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ]
    omega
  rw [heq, Finset.card_powersetCard]
  simp

lemma low_subtype_card_bound_nat (p : ℕ) (hp : 1 ≤ p) :
    p ^ 2 * Fintype.card {U : Finset (Fin p) // U.card < cutoff p} ≤
      64 * 2 ^ p := by
  rw [low_subtype_card_eq_sum_choose]
  exact low_choose_sum_bound p hp

lemma low_subtype_scaled_bound (p : ℕ) (hp : 1 ≤ p) :
    (Fintype.card {U : Finset (Fin p) // U.card < cutoff p} : ℝ) * (2 : ℝ) ^ p ≤
      64 * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
  have hnat := Nat.mul_le_mul_right (2 ^ p) (low_subtype_card_bound_nat p hp)
  have hnat' :
      Fintype.card {U : Finset (Fin p) // U.card < cutoff p} * 2 ^ p * p ^ 2 ≤
        64 * 4 ^ p := by
    calc
      Fintype.card {U : Finset (Fin p) // U.card < cutoff p} * 2 ^ p * p ^ 2 =
          (p ^ 2 * Fintype.card {U : Finset (Fin p) // U.card < cutoff p}) * 2 ^ p := by
            ring
      _ ≤ (64 * 2 ^ p) * 2 ^ p := hnat
      _ = 64 * 4 ^ p := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
        ring
  exact_mod_cast hnat'

lemma sqrt_cube_comparison_sixteen {n r : ℕ} (hnr : n ≤ 16 * r) :
    Real.sqrt (n : ℝ) ^ 3 ≤ 64 * Real.sqrt (r : ℝ) ^ 3 := by
  have hcast : (n : ℝ) ≤ 16 * (r : ℝ) := by exact_mod_cast hnr
  have hsqrt : Real.sqrt (n : ℝ) ≤ 4 * Real.sqrt (r : ℝ) := by
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt (16 * (r : ℝ)) := Real.sqrt_le_sqrt hcast
      _ = 4 * Real.sqrt (r : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have hfactor :
      0 ≤ (4 * Real.sqrt (r : ℝ) - Real.sqrt (n : ℝ)) *
        (16 * Real.sqrt (r : ℝ) ^ 2 +
          4 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) +
          Real.sqrt (n : ℝ) ^ 2) := by positivity
  nlinarith

lemma div_sqrt_mul_div_sqrt_cube_le_sixteen {a : ℝ} {n r : ℕ}
    (ha : 0 ≤ a) (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : n ≤ 16 * r) :
    (a / Real.sqrt (n : ℝ)) / Real.sqrt (r : ℝ) ^ 3 ≤
      64 * a / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hr0
  have hcomp := sqrt_cube_comparison_sixteen hnr
  rw [div_div, div_le_iff₀ (mul_pos hsn (pow_pos hsr 3)), div_mul_eq_mul_div]
  rw [le_div_iff₀ (sq_pos_of_pos hn0), ← sqrt_four_nat n]
  calc
    a * Real.sqrt (n : ℝ) ^ 4 =
        a * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ^ 3 := by ring
    _ ≤ a * Real.sqrt (n : ℝ) * (64 * Real.sqrt (r : ℝ) ^ 3) := by gcongr
    _ = 64 * a * (Real.sqrt (n : ℝ) * Real.sqrt (r : ℝ) ^ 3) := by ring

lemma central_choose_div_sqrt_cube_le_sixteen :
    ∃ K : ℝ, 0 < K ∧ ∀ n r : ℕ, 1 ≤ n → 1 ≤ r → n ≤ 16 * r →
      (Nat.choose n (n / 2) : ℝ) / Real.sqrt (r : ℝ) ^ 3 ≤
        K * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := Erdos487.central_binom_bound
  have hC₀_nonneg : 0 ≤ C₀ := by
    have h := hC₀ 1 (by omega)
    norm_num at h
    linarith
  refine ⟨64 * (C₀ + 1), by positivity, ?_⟩
  intro n r hn hr hnr
  have hcentral := hC₀ n hn
  calc
    (Nat.choose n (n / 2) : ℝ) / Real.sqrt (r : ℝ) ^ 3 ≤
        (C₀ * ((2 : ℝ) ^ n / Real.sqrt (n : ℝ))) /
          Real.sqrt (r : ℝ) ^ 3 := by gcongr
    _ = C₀ * (((2 : ℝ) ^ n / Real.sqrt (n : ℝ)) /
          Real.sqrt (r : ℝ) ^ 3) := by ring
    _ ≤ C₀ * (64 * (2 : ℝ) ^ n / (n : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (div_sqrt_mul_div_sqrt_cube_le_sixteen (a := (2 : ℝ) ^ n)
          (by positivity) hn hr hnr) hC₀_nonneg
    _ ≤ (64 * (C₀ + 1)) * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      rw [show C₀ * (64 * (2 : ℝ) ^ n / (n : ℝ) ^ 2) =
        (C₀ * 64 * (2 : ℝ) ^ n) / (n : ℝ) ^ 2 by ring]
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hn0)).2
      nlinarith [show 0 ≤ (2 : ℝ) ^ n by positivity]

lemma high_scale {C : ℝ} (hC : 0 ≤ C) {p m : ℕ} (hp : 1 ≤ p)
    (hm : cutoff p ≤ m) :
    C * (2 : ℝ) ^ m / Real.sqrt m ^ 3 ≤
      (C / Real.sqrt (cutoff p) ^ 3) * (2 : ℝ) ^ m := by
  have hq : 1 ≤ cutoff p := cutoff_pos hp
  have hq0 : 0 < Real.sqrt (cutoff p : ℝ) := by positivity
  have hm0 : 0 < Real.sqrt (m : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (Nat.zero_lt_of_lt (hq.trans hm))
  have hsqrt : Real.sqrt (cutoff p : ℝ) ≤ Real.sqrt (m : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hm
  have hpow : Real.sqrt (cutoff p : ℝ) ^ 3 ≤ Real.sqrt (m : ℝ) ^ 3 := by gcongr
  have hdiv : C / Real.sqrt (m : ℝ) ^ 3 ≤
      C / Real.sqrt (cutoff p : ℝ) ^ 3 := by
    exact div_le_div_of_nonneg_left hC (pow_pos hq0 3) hpow
  calc
    C * (2 : ℝ) ^ m / Real.sqrt m ^ 3 =
        (C / Real.sqrt m ^ 3) * (2 : ℝ) ^ m := by ring
    _ ≤ (C / Real.sqrt (cutoff p) ^ 3) * (2 : ℝ) ^ m := by gcongr

lemma choose_le_central (n l : ℕ) : n.choose l ≤ n.choose (n / 2) :=
  Nat.choose_le_middle l n

lemma high_central_cutoff_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ p l : ℕ, 1 ≤ p →
      ((2 * p).choose l : ℝ) / Real.sqrt (cutoff p) ^ 3 ≤
        K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  obtain ⟨K, hK, hcentral⟩ := central_choose_div_sqrt_cube_le_sixteen
  refine ⟨K, hK, ?_⟩
  intro p l hp
  have hq := cutoff_pos hp
  have hcond : 2 * p ≤ 16 * cutoff p := by
    have := p_le_eight_mul_cutoff p
    omega
  have hc := hcentral (2 * p) (cutoff p) (by omega) hq hcond
  have hchoose : ((2 * p).choose l : ℝ) ≤ ((2 * p).choose ((2 * p) / 2) : ℝ) := by
    exact_mod_cast choose_le_central (2 * p) l
  have hden : 0 < Real.sqrt (cutoff p : ℝ) ^ 3 := by positivity
  calc
    ((2 * p).choose l : ℝ) / Real.sqrt (cutoff p) ^ 3 ≤
        ((2 * p).choose ((2 * p) / 2) : ℝ) /
          Real.sqrt (cutoff p) ^ 3 := div_le_div_of_nonneg_right hchoose hden.le
    _ ≤ K * (2 : ℝ) ^ (2 * p) / (2 * p : ℕ) ^ 2 := hc
    _ ≤ K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
      have hK0 : 0 ≤ K := hK.le
      rw [show (2 : ℝ) ^ (2 * p) = (4 : ℝ) ^ p by rw [pow_mul]; norm_num]
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hp0)
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith [sq_nonneg (p : ℝ)]

lemma high_scaled_central_cutoff_bound {C K : ℝ} (hC : 0 ≤ C) (_hK : 0 ≤ K)
    (hcentral : ∀ p l : ℕ, 1 ≤ p →
      ((2 * p).choose l : ℝ) / Real.sqrt (cutoff p) ^ 3 ≤
        K * (4 : ℝ) ^ p / (p : ℝ) ^ 2)
    {p l : ℕ} (hp : 1 ≤ p) :
    (C / Real.sqrt (cutoff p) ^ 3) * ((2 * p).choose l : ℝ) ≤
      (C * K) * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  calc
    (C / Real.sqrt (cutoff p) ^ 3) * ((2 * p).choose l : ℝ) =
        C * (((2 * p).choose l : ℝ) / Real.sqrt (cutoff p) ^ 3) := by ring
    _ ≤ C * (K * (4 : ℝ) ^ p / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hcentral p l hp) hC
    _ = (C * K) * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by ring


theorem exists_fixed_reduction_numerics {C : ℝ} (hC : 0 < C) :
    ∃ Ktotal : ℝ, 0 < Ktotal ∧ ∀ p : ℕ, 1 ≤ p →
      let q := cutoff p
      let D := C / Real.sqrt q ^ 3
      0 ≤ D ∧ 1 ≤ q ∧
      (∀ m : ℕ, q ≤ m →
        C * (2 : ℝ) ^ m / Real.sqrt m ^ 3 ≤ D * (2 : ℝ) ^ m) ∧
      (Fintype.card {U : Finset (Fin p) // U.card < q} : ℝ) * (2 : ℝ) ^ p ≤
        64 * (4 : ℝ) ^ p / (p : ℝ) ^ 2 ∧
      ∃ F : ℝ, 0 ≤ F ∧ 64 + F = Ktotal ∧ ∀ l : ℕ,
        D * ((2 * p).choose l : ℝ) ≤
          F * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  obtain ⟨K₀, hK₀, hcentral⟩ := high_central_cutoff_bound
  refine ⟨64 + C * K₀, by positivity, ?_⟩
  intro p hp
  dsimp only
  refine ⟨by positivity, cutoff_pos hp, ?_, low_subtype_scaled_bound p hp,
    C * K₀, by positivity, rfl, ?_⟩
  · intro m hm
    exact high_scale hC.le hp hm
  · intro l
    exact high_scaled_central_cutoff_bound hC.le hK₀.le hcentral hp


lemma sum_finsetCongr {A B M : Type*} [DecidableEq A] [DecidableEq B]
    [AddCommMonoid M] (e : A ≃ B) (f : B → M) (S : Finset A) :
    ∑ y ∈ e.finsetCongr S, f y = ∑ x ∈ S, f (e x) := by
  simp [Equiv.finsetCongr_apply]

def sumFiberEquiv {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (f : B → ℕ) (t : ℕ) :
    {S // S ∈ sumFiber (f ∘ e) t} ≃ {T // T ∈ sumFiber f t} where
  toFun S := ⟨e.finsetCongr S.1, by
    rw [mem_sumFiber, sum_finsetCongr]
    exact mem_sumFiber.mp S.2⟩
  invFun T := ⟨e.symm.finsetCongr T.1, by
    rw [mem_sumFiber, sum_finsetCongr]
    simpa only [Function.comp_apply, e.apply_symm_apply] using mem_sumFiber.mp T.2⟩
  left_inv S := by
    apply Subtype.ext
    simpa only [Equiv.finsetCongr_symm] using e.finsetCongr.symm_apply_apply S.1
  right_inv T := by
    apply Subtype.ext
    simpa only [Equiv.finsetCongr_symm] using e.finsetCongr.apply_symm_apply T.1

lemma card_sumFiber_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (f : B → ℕ) (t : ℕ) :
    (sumFiber (f ∘ e) t).card = (sumFiber f t).card := by
  calc
    (sumFiber (f ∘ e) t).card =
        Fintype.card {S // S ∈ sumFiber (f ∘ e) t} := (Fintype.card_coe _).symm
    _ = Fintype.card {T // T ∈ sumFiber f t} :=
      Fintype.card_congr (sumFiberEquiv e f t)
    _ = (sumFiber f t).card := Fintype.card_coe _

lemma arbitrary_scalar_exact {A : Type*} [Fintype A] [DecidableEq A]
    (w : A → ℕ) (hw_inj : Function.Injective w) (hw_pos : ∀ i, 0 < w i)
    (t : ℕ) :
    let n := Fintype.card A
    let q := n / 2
    let r := n - q
    (sumFiber w t).card * q ≤ 2 ^ q * (2 * r.choose (r / 2)) := by
  classical
  let n := Fintype.card A
  let q := n / 2
  let r := n - q
  let e0 : Fin n ≃ A := (Fintype.equivFin A).symm
  let f : Fin n → ℕ := w ∘ e0
  let σ : Equiv.Perm (Fin n) := Tuple.sort f
  let x : Fin n → ℕ := f ∘ σ
  have hx_mono : Monotone x := Tuple.monotone_sort f
  have hx_inj : Function.Injective x :=
    (hw_inj.comp e0.injective).comp σ.injective
  have hx : StrictMono x := hx_mono.strictMono_of_injective hx_inj
  have hqn : q ≤ n := Nat.div_le_self _ _
  have hqr : q + r = n := Nat.add_sub_of_le hqn
  let es : Fin q ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr hqr)
  let e : Fin q ⊕ Fin r ≃ A := es.trans (σ.trans e0)
  let a : Fin q ⊕ Fin r → ℕ := w ∘ e
  have ha_pos : ∀ z, 0 < a z := fun z ↦ hw_pos _
  have ha_inj : Function.Injective a := hw_inj.comp e.injective
  have ha_sep : ∀ i j, a (Sum.inl i) < a (Sum.inr j) := by
    intro i j
    apply hx
    simp only [es, Equiv.trans_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply]
    change (Fin.castAdd r i : Fin (q + r)) < Fin.natAdd q j
    change i.val < q + j.val
    omega
  have hs := sarkozy_szemeredi_finite a ha_pos ha_inj ha_sep t
  have hc := card_sumFiber_comp_equiv e w t
  change (sumFiber w t).card * q ≤ _
  rw [← hc]
  simpa [a] using hs

theorem exists_indexedScalarBound : ∃ C > 0, IndexedScalarBound C := by
  obtain ⟨C₀, hC₀⟩ := Erdos487.central_binom_bound
  have hC₀one := hC₀ 1 (by omega)
  norm_num at hC₀one
  have hC₀pos : 0 < C₀ := by nlinarith
  refine ⟨12 * C₀, by positivity, ?_⟩
  intro A _ _ w hw_inj hw_pos hn b t
  by_cases htb : t < b
  · have hempty :
        (Finset.univ.powerset.filter fun R : Finset A ↦ b + ∑ i ∈ R, w i = t) = ∅ := by
      ext R
      simp
      omega
    rw [hempty]
    simp
    positivity
  · have hbase :
        (Finset.univ.powerset.filter fun R : Finset A ↦ b + ∑ i ∈ R, w i = t) =
          sumFiber w (t - b) := by
      ext R
      simp [sumFiber]
      omega
    rw [hbase]
    let n := Fintype.card A
    let q := n / 2
    let r := n - q
    have hnpos : 0 < n := by dsimp [n]; omega
    by_cases hnsmall : n = 1
    · have htriv : (sumFiber w (t - b)).card ≤ 2 ^ n := by
        calc
          (sumFiber w (t - b)).card ≤ Finset.univ.powerset.card := card_filter_le _ _
          _ = 2 ^ n := by simp [n]
      have htrivR : ((sumFiber w (t - b)).card : ℝ) ≤ 2 ^ n := by
        exact_mod_cast htriv
      change ((sumFiber w (t - b)).card : ℝ) ≤
        12 * C₀ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ^ 3
      rw [hnsmall] at htrivR ⊢
      norm_num at htrivR ⊢
      calc
        ((sumFiber w (t - b)).card : ℝ) ≤ 2 := by exact_mod_cast htrivR
        _ ≤ 12 * C₀ * 2 := by nlinarith [hC₀one]
    · have hnlarge : 2 ≤ n := by omega
      have hqpos : 0 < q := by dsimp [q]; omega
      have hrpos : 0 < r := by dsimp [r, q]; omega
      have hqn : q ≤ n := by dsimp [q]; omega
      have hqr : q + r = n := by dsimp [r]; omega
      have hex := arbitrary_scalar_exact w hw_inj hw_pos (t - b)
      have hex' : (sumFiber w (t - b)).card * q ≤
          2 ^ q * (2 * r.choose (r / 2)) := by
        simpa only [n, q, r] using hex
      have hexR : ((sumFiber w (t - b)).card : ℝ) * q ≤
          (2 : ℝ) ^ q * (2 * (r.choose (r / 2) : ℝ)) := by
        exact_mod_cast hex'
      have hcent := hC₀ r hrpos
      have hsqrtrpos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hcent' : (r.choose (r / 2) : ℝ) * Real.sqrt r ≤
          C₀ * (2 : ℝ) ^ r := by
        calc
          (r.choose (r / 2) : ℝ) * Real.sqrt r ≤
              (C₀ * ((2 : ℝ) ^ r / Real.sqrt r)) * Real.sqrt r :=
            mul_le_mul_of_nonneg_right hcent (Real.sqrt_nonneg _)
          _ = C₀ * (2 : ℝ) ^ r := by field_simp
      have hprod : ((sumFiber w (t - b)).card : ℝ) * q * Real.sqrt r ≤
          2 * C₀ * (2 : ℝ) ^ n := by
        calc
          ((sumFiber w (t - b)).card : ℝ) * q * Real.sqrt r ≤
              ((2 : ℝ) ^ q * (2 * (r.choose (r / 2) : ℝ))) * Real.sqrt r :=
            mul_le_mul_of_nonneg_right hexR (Real.sqrt_nonneg _)
          _ = (2 * (2 : ℝ) ^ q) *
              ((r.choose (r / 2) : ℝ) * Real.sqrt r) := by ring
          _ ≤ (2 * (2 : ℝ) ^ q) * (C₀ * (2 : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left hcent' (by positivity)
          _ = 2 * C₀ * ((2 : ℝ) ^ q * (2 : ℝ) ^ r) := by ring
          _ = 2 * C₀ * (2 : ℝ) ^ n := by rw [← pow_add, hqr]
      have hnq : n ≤ 3 * q := by dsimp [q]; omega
      have hnr : n ≤ 4 * r := by dsimp [r, q]; omega
      have hnqR : (n : ℝ) ≤ 3 * q := by exact_mod_cast hnq
      have hnrR : (n : ℝ) ≤ 4 * r := by exact_mod_cast hnr
      have hnRpos : 0 < (n : ℝ) := by positivity
      have hsqrtnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnRpos
      have hsqrtn : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity),
          Real.sq_sqrt (show 0 ≤ (r : ℝ) by positivity)]
      have hcub : Real.sqrt (n : ℝ) ^ 3 ≤
          6 * (q : ℝ) * Real.sqrt (r : ℝ) := by
        calc
          Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
            nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
          _ ≤ (3 * (q : ℝ)) * (2 * Real.sqrt (r : ℝ)) :=
            mul_le_mul hnqR hsqrtn (Real.sqrt_nonneg _) (by positivity)
          _ = 6 * (q : ℝ) * Real.sqrt (r : ℝ) := by ring
      apply (le_div_iff₀ (pow_pos hsqrtnpos 3)).2
      calc
        ((sumFiber w (t - b)).card : ℝ) * Real.sqrt (n : ℝ) ^ 3 ≤
            ((sumFiber w (t - b)).card : ℝ) *
              (6 * (q : ℝ) * Real.sqrt (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hcub (by positivity)
        _ = 6 * (((sumFiber w (t - b)).card : ℝ) * q * Real.sqrt r) := by ring
        _ ≤ 6 * (2 * C₀ * (2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 12 * C₀ * (2 : ℝ) ^ n := by ring


def eraseZeroEmbedding : Finset ℕ ↪ Finset ℕ × Bool where
  toFun S := (S.erase 0, decide (0 ∈ S))
  inj' := by
    intro S T h
    have he : S.erase 0 = T.erase 0 := congrArg Prod.fst h
    have hb : decide (0 ∈ S) = decide (0 ∈ T) := congrArg Prod.snd h
    by_cases hS : 0 ∈ S <;> by_cases hT : 0 ∈ T
    · rw [← insert_erase hS, ← insert_erase hT, he]
    · simp [hS, hT] at hb
    · simp [hS, hT] at hb
    · simpa [erase_eq_of_notMem hS, erase_eq_of_notMem hT] using he

theorem sum_erase_zero (S : Finset ℕ) :
    ∑ x ∈ S.erase 0, x = ∑ x ∈ S, x := by
  simpa using
    (Finset.sum_erase S (f := fun x : ℕ => x) (a := 0) (by rfl))

/-- Deleting a possible zero costs at most a factor two in the unrestricted fiber. -/
theorem card_subsetSumFiber_le_two_mul_erase_zero (A : Finset ℕ) (t : ℕ) :
    (subsetSumFiber A t).card ≤ 2 * (subsetSumFiber (A.erase 0) t).card := by
  have himage :
      (subsetSumFiber A t).map eraseZeroEmbedding ⊆
        subsetSumFiber (A.erase 0) t ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    rw [mem_map] at hp
    obtain ⟨S, hS, rfl⟩ := hp
    rw [mem_product]
    refine ⟨?_, mem_univ _⟩
    change S.erase 0 ∈ subsetSumFiber (A.erase 0) t
    rw [mem_subsetSumFiber] at hS ⊢
    exact ⟨erase_subset_erase 0 hS.1, (sum_erase_zero S).trans hS.2⟩
  rw [← card_map eraseZeroEmbedding]
  refine (card_le_card himage).trans_eq ?_
  simp [Nat.mul_comm]

/-- A set is recovered from deletion of one element and its membership bit. -/
def eraseElementEmbedding (a : ℕ) : Finset ℕ ↪ Finset ℕ × Bool where
  toFun S := (S.erase a, decide (a ∈ S))
  inj' := by
    intro S T h
    have he : S.erase a = T.erase a := congrArg Prod.fst h
    have hb : decide (a ∈ S) = decide (a ∈ T) := congrArg Prod.snd h
    by_cases hS : a ∈ S <;> by_cases hT : a ∈ T
    · rw [← insert_erase hS, ← insert_erase hT, he]
    · simp [hS, hT] at hb
    · simp [hS, hT] at hb
    · simpa [erase_eq_of_notMem hS, erase_eq_of_notMem hT] using he

/-- Deleting a specified element splits a fixed layer into two fixed layers. -/
theorem card_fixedCardSubsetSumFiber_le_erase (A : Finset ℕ) (a l t : ℕ) :
    (fixedCardSubsetSumFiber A l t).card ≤
      2 * ((fixedCardSubsetSumFiber (A.erase a) l t).card +
        (fixedCardSubsetSumFiber (A.erase a) (l - 1) (t - a)).card) := by
  let U := fixedCardSubsetSumFiber (A.erase a) l t ∪
    fixedCardSubsetSumFiber (A.erase a) (l - 1) (t - a)
  have himage :
      (fixedCardSubsetSumFiber A l t).map (eraseElementEmbedding a) ⊆
        U ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    rw [mem_map] at hp
    obtain ⟨S, hS, rfl⟩ := hp
    rw [mem_product]
    refine ⟨?_, mem_univ _⟩
    change S.erase a ∈ U
    rw [mem_union]
    rw [mem_fixedCardSubsetSumFiber] at hS
    by_cases ha : a ∈ S
    · right
      rw [mem_fixedCardSubsetSumFiber]
      refine ⟨erase_subset_erase a hS.1, ?_, ?_⟩
      · simp [card_erase_of_mem ha, hS.2.1]
      · have hsum := Finset.sum_erase_add (s := S) (f := fun x : ℕ ↦ x) ha
        rw [hS.2.2] at hsum
        omega
    · left
      rw [mem_fixedCardSubsetSumFiber]
      rw [erase_eq_of_notMem ha]
      exact ⟨subset_erase.mpr ⟨hS.1, ha⟩, hS.2⟩
  rw [← card_map (eraseElementEmbedding a)]
  refine (card_le_card himage).trans ?_
  calc
    (U ×ˢ (Finset.univ : Finset Bool)).card = 2 * U.card := by simp [Nat.mul_comm]
    _ ≤ 2 * ((fixedCardSubsetSumFiber (A.erase a) l t).card +
        (fixedCardSubsetSumFiber (A.erase a) (l - 1) (t - a)).card) := by
      exact Nat.mul_le_mul_left 2 (card_union_le _ _)

/-- The paired reduction plus the numerical estimates give a uniform bound for even families. -/
theorem exists_fixedPairFiber_bound {C : ℝ} (hC : 0 < C)
    (hscalar : IndexedScalarBound C) :
    ∃ K : ℝ, 0 < K ∧ ∀ {p : ℕ}, 1 ≤ p → ∀ (x : Fin (2 * p) → ℕ),
      StrictMono x → ∀ l t : ℕ,
        ((fixedPairFiber x l t).card : ℝ) ≤
          K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  obtain ⟨K, hK, hnum⟩ := exists_fixed_reduction_numerics hC
  refine ⟨K, hK, ?_⟩
  intro p hp x hx l t
  obtain ⟨hD, hq, hscale, hlow, F, hF, hKF, hhigh⟩ := hnum p hp
  have h := fixedPairFiber_real_card_le_of_numerical hscalar hD hx l t
    (cutoff p) hq hscale hlow (hhigh l)
  simpa [hKF] using h

/-- Choose the lower member of a pair for `false` and the reversed upper member for `true`. -/
def pairSumEquiv (p : ℕ) : Fin p × Bool ≃ Fin p ⊕ Fin p where
  toFun ib := if ib.2 then Sum.inr ib.1.rev else Sum.inl ib.1
  invFun s := match s with
    | Sum.inl i => (i, false)
    | Sum.inr i => (i.rev, true)
  left_inv ib := by
    rcases ib with ⟨i, b⟩
    cases b <;> simp
  right_inv s := by
    rcases s with i | i <;> simp

/-- The pair coordinates reindex the first and last, second and penultimate, and so on. -/
def pairIndexEquiv (p : ℕ) : Fin p × Bool ≃ Fin (2 * p) :=
  (pairSumEquiv p).trans (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] lemma pairIndexEquiv_false (p : ℕ) (i : Fin p) :
    pairIndexEquiv p (i, false) = lowerIndex p i := by
  apply Fin.ext
  simp [pairIndexEquiv, pairSumEquiv, lowerIndex]

@[simp] lemma pairIndexEquiv_true (p : ℕ) (i : Fin p) :
    pairIndexEquiv p (i, true) = upperIndex p i := by
  apply Fin.ext
  simp [pairIndexEquiv, pairSumEquiv, upperIndex]
  omega

@[simp] lemma pairWeight_eq_pairIndex {p : ℕ} (x : Fin (2 * p) → ℕ)
    (ib : Fin p × Bool) : pairWeight x ib = x (pairIndexEquiv p ib) := by
  rcases ib with ⟨i, b⟩
  cases b <;> simp [pairWeight]

/-- Reindexing by the extreme-pair equivalence preserves the complete fixed fiber. -/
noncomputable def fixedPairFiberEquiv {p : ℕ} (x : Fin (2 * p) → ℕ) (l t : ℕ) :
    {S // S ∈ fixedPairFiber x l t} ≃
      {T // T ∈ indexedFixedCardSubsetSumFiber x l t} where
  toFun S := ⟨(pairIndexEquiv p).finsetCongr S.1, by
    rcases Finset.mem_filter.mp S.2 with ⟨_, hcard, hsum⟩
    rw [mem_indexedFixedCardSubsetSumFiber]
    refine ⟨by simpa using hcard, ?_⟩
    rw [sum_finsetCongr]
    simpa [subsetWeight] using hsum⟩
  invFun T := ⟨(pairIndexEquiv p).symm.finsetCongr T.1, by
    rw [fixedPairFiber, Finset.mem_filter]
    rcases mem_indexedFixedCardSubsetSumFiber.mp T.2 with ⟨hcard, hsum⟩
    refine ⟨Finset.mem_univ _, by simpa using hcard, ?_⟩
    rw [subsetWeight, sum_finsetCongr]
    simpa using hsum⟩
  left_inv S := by
    apply Subtype.ext
    simpa only [Equiv.finsetCongr_symm] using
      (pairIndexEquiv p).finsetCongr.symm_apply_apply S.1
  right_inv T := by
    apply Subtype.ext
    simpa only [Equiv.finsetCongr_symm] using
      (pairIndexEquiv p).finsetCongr.apply_symm_apply T.1

theorem card_fixedPairFiber_eq_indexed {p : ℕ} (x : Fin (2 * p) → ℕ) (l t : ℕ) :
    (fixedPairFiber x l t).card = (indexedFixedCardSubsetSumFiber x l t).card := by
  calc
    (fixedPairFiber x l t).card = Fintype.card {S // S ∈ fixedPairFiber x l t} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {T // T ∈ indexedFixedCardSubsetSumFiber x l t} :=
      Fintype.card_congr (fixedPairFiberEquiv x l t)
    _ = (indexedFixedCardSubsetSumFiber x l t).card := Fintype.card_coe _

/-- Fixed-cardinality fibers are invariant under a permutation of their coordinates. -/
noncomputable def indexedFixedFiberEquiv {m n : ℕ} (e : Fin m ≃ Fin n)
    (a : Fin n → ℕ) (l t : ℕ) :
    {S // S ∈ indexedFixedCardSubsetSumFiber (a ∘ e) l t} ≃
      {T // T ∈ indexedFixedCardSubsetSumFiber a l t} where
  toFun S := ⟨e.finsetCongr S.1, by
    rcases mem_indexedFixedCardSubsetSumFiber.mp S.2 with ⟨hcard, hsum⟩
    rw [mem_indexedFixedCardSubsetSumFiber]
    refine ⟨by simpa using hcard, ?_⟩
    rw [sum_finsetCongr]
    exact hsum⟩
  invFun T := ⟨e.symm.finsetCongr T.1, by
    rcases mem_indexedFixedCardSubsetSumFiber.mp T.2 with ⟨hcard, hsum⟩
    rw [mem_indexedFixedCardSubsetSumFiber]
    refine ⟨by simpa using hcard, ?_⟩
    rw [sum_finsetCongr]
    simpa only [Function.comp_apply, e.apply_symm_apply] using hsum⟩
  left_inv S := by
    apply Subtype.ext
    simpa only [Equiv.finsetCongr_symm] using e.finsetCongr.symm_apply_apply S.1
  right_inv T := by
    apply Subtype.ext
    simpa only [Equiv.finsetCongr_symm] using e.finsetCongr.apply_symm_apply T.1

theorem card_indexedFixed_comp_equiv {m n : ℕ} (e : Fin m ≃ Fin n)
    (a : Fin n → ℕ) (l t : ℕ) :
    (indexedFixedCardSubsetSumFiber (a ∘ e) l t).card =
      (indexedFixedCardSubsetSumFiber a l t).card := by
  calc
    _ = Fintype.card {S // S ∈ indexedFixedCardSubsetSumFiber (a ∘ e) l t} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {T // T ∈ indexedFixedCardSubsetSumFiber a l t} :=
      Fintype.card_congr (indexedFixedFiberEquiv e a l t)
    _ = _ := Fintype.card_coe _

theorem fixedCardSubsetSumFiber_even_bound {K : ℝ}
    (hpair : ∀ {p : ℕ}, 1 ≤ p → ∀ (x : Fin (2 * p) → ℕ),
      StrictMono x → ∀ l t : ℕ,
        ((fixedPairFiber x l t).card : ℝ) ≤ K * (4 : ℝ) ^ p / (p : ℝ) ^ 2)
    (A : Finset ℕ) {p : ℕ} (hp : 1 ≤ p) (hcard : A.card = 2 * p) (l t : ℕ) :
    ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
      K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
  let e : Fin (2 * p) ≃ Fin A.card := finCongr hcard.symm
  let x : Fin (2 * p) → ℕ := orderedEnumerate A ∘ e
  have hx : StrictMono x := by
    intro i j hij
    apply orderedEnumerate_strictMono A
    simpa [x, e, finCongr_apply] using hij
  calc
    ((fixedCardSubsetSumFiber A l t).card : ℝ) =
        (indexedFixedCardSubsetSumFiber (orderedEnumerate A) l t).card := by
          rw [card_indexedFixedCardSubsetSumFiber_orderedEnumerate]
    _ = (indexedFixedCardSubsetSumFiber x l t).card := by
          rw [card_indexedFixed_comp_equiv e (orderedEnumerate A) l t]
    _ = (fixedPairFiber x l t).card := by
          rw [card_fixedPairFiber_eq_indexed]
    _ ≤ K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := hpair hp x hx l t

/-- The scalar Sárközy--Szemerédi bound for arbitrary nonempty finite sets of
naturals.  A possible zero is deleted at a cost of at most two. -/
theorem exists_subsetSumFiber_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ t : ℕ,
      ((subsetSumFiber A t).card : ℝ) ≤
        C * (2 : ℝ) ^ A.card / Real.sqrt (A.card : ℝ) ^ 3 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_indexedScalarBound
  refine ⟨16 * (C₀ + 1), by positivity, ?_⟩
  intro A hA t
  let B := A.erase 0
  by_cases hB : B.Nonempty
  · have hBcard : 1 ≤ B.card := hB.card_pos
    have hwpos : ∀ i, 0 < orderedEnumerate B i := by
      intro i
      have hi := orderedEnumerate_mem B i
      change orderedEnumerate B i ∈ A.erase 0 at hi
      exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1
    have hs := hC₀ (orderedEnumerate B) (orderedEnumerate_injective B)
      hwpos (by simpa using hBcard) 0 t
    have hs' : ((subsetSumFiber B t).card : ℝ) ≤
        C₀ * (2 : ℝ) ^ B.card / Real.sqrt (B.card : ℝ) ^ 3 := by
      rw [← card_indexedSubsetSumFiber_orderedEnumerate B t]
      simpa [indexedSubsetSumFiber] using hs
    have herase : ((subsetSumFiber A t).card : ℝ) ≤
        2 * ((subsetSumFiber B t).card : ℝ) := by
      exact_mod_cast card_subsetSumFiber_le_two_mul_erase_zero A t
    have hBA : B.card ≤ A.card := by
      apply card_le_card
      exact erase_subset _ _
    have hAB : A.card ≤ 2 * B.card := by
      by_cases hz : 0 ∈ A
      · have he : B.card + 1 = A.card := by
          simpa [B] using card_erase_add_one hz
        omega
      · simp [B, erase_eq_of_notMem hz]
        omega
    have hpow : (2 : ℝ) ^ B.card ≤ (2 : ℝ) ^ A.card :=
      pow_le_pow_right₀ (by norm_num) hBA
    have hAcardpos : 0 < (A.card : ℝ) := by
      exact_mod_cast hA.card_pos
    have hBcardpos : 0 < (B.card : ℝ) := by
      exact_mod_cast hB.card_pos
    have hsqrtApos : 0 < Real.sqrt (A.card : ℝ) := Real.sqrt_pos.2 hAcardpos
    have hsqrtBpos : 0 < Real.sqrt (B.card : ℝ) := Real.sqrt_pos.2 hBcardpos
    have hABR : (A.card : ℝ) ≤ 4 * (B.card : ℝ) := by
      exact_mod_cast hAB.trans (by omega : 2 * B.card ≤ 4 * B.card)
    have hsqrt : Real.sqrt (A.card : ℝ) ≤ 2 * Real.sqrt (B.card : ℝ) := by
      calc
        Real.sqrt (A.card : ℝ) ≤ Real.sqrt (4 * (B.card : ℝ)) :=
          Real.sqrt_le_sqrt hABR
        _ = 2 * Real.sqrt (B.card : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    have hcub : Real.sqrt (A.card : ℝ) ^ 3 ≤
        8 * Real.sqrt (B.card : ℝ) ^ 3 := by
      calc
        Real.sqrt (A.card : ℝ) ^ 3 ≤
            (2 * Real.sqrt (B.card : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 3
        _ = 8 * Real.sqrt (B.card : ℝ) ^ 3 := by ring
    apply (le_div_iff₀ (pow_pos hsqrtApos 3)).2
    calc
      ((subsetSumFiber A t).card : ℝ) * Real.sqrt (A.card : ℝ) ^ 3 ≤
          (2 * ((subsetSumFiber B t).card : ℝ)) *
            Real.sqrt (A.card : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right herase (by positivity)
      _ ≤ (2 * (C₀ * (2 : ℝ) ^ B.card /
            Real.sqrt (B.card : ℝ) ^ 3)) * Real.sqrt (A.card : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs' (by norm_num)) (by positivity)
      _ ≤ (2 * (C₀ * (2 : ℝ) ^ B.card /
            Real.sqrt (B.card : ℝ) ^ 3)) *
            (8 * Real.sqrt (B.card : ℝ) ^ 3) := by
        gcongr
      _ = 16 * C₀ * (2 : ℝ) ^ B.card := by
        field_simp [ne_of_gt hsqrtBpos]
        ring
      _ ≤ 16 * C₀ * (2 : ℝ) ^ A.card := by
        gcongr
      _ ≤ 16 * (C₀ + 1) * (2 : ℝ) ^ A.card := by
        nlinarith [show 0 ≤ (2 : ℝ) ^ A.card by positivity]
  · have hBempty : B = ∅ := not_nonempty_iff_eq_empty.mp hB
    have hAsub : A ⊆ {0} := by
      intro x hx
      by_contra hx0
      have hxB : x ∈ B := by
        change x ∈ A.erase 0
        exact Finset.mem_erase.mpr ⟨by simpa using hx0, hx⟩
      simpa [hBempty] using hxB
    have hAcard : A.card = 1 := by
      have hle := card_le_card hAsub
      have hpos := hA.card_pos
      simp only [card_singleton] at hle
      omega
    have htriv := subsetSumFiber_card_le A t
    have htrivR : ((subsetSumFiber A t).card : ℝ) ≤ (2 : ℝ) ^ A.card := by
      exact_mod_cast htriv
    rw [hAcard] at htrivR ⊢
    norm_num at htrivR ⊢
    calc
      ((subsetSumFiber A t).card : ℝ) ≤ 2 := by exact_mod_cast htrivR
      _ ≤ 16 * (C₀ + 1) * 2 := by nlinarith [hC₀pos]

/-- The Halász fixed-layer estimate, packaged for arbitrary finite subsets of `ℕ`. -/
theorem exists_fixedCardSubsetSumFiber_bound {C : ℝ} (hC : 0 < C)
    (hscalar : IndexedScalarBound C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset ℕ), 1 ≤ A.card → ∀ l t : ℕ,
      ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
        K * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2 := by
  obtain ⟨K, hK, hpair⟩ := exists_fixedPairFiber_bound hC hscalar
  refine ⟨32 * (K + 1), by positivity, ?_⟩
  intro A hA l t
  obtain ⟨p, heven | hodd⟩ := Nat.even_or_odd' A.card
  · have hp : 1 ≤ p := by omega
    have hmain := fixedCardSubsetSumFiber_even_bound hpair A hp heven l t
    calc
      ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
          K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := hmain
      _ ≤ 8 * (K + 1) * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
        gcongr
        nlinarith
      _ = 32 * (K + 1) * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2 := by
        rw [heven]
        push_cast
        rw [pow_mul]
        norm_num
        field_simp
        <;> ring
  · by_cases hp0 : p = 0
    · have hcardA : A.card = 1 := by omega
      have hnat : (fixedCardSubsetSumFiber A l t).card ≤ 2 ^ A.card :=
        (fixedCardSubsetSumFiber_card_le A l t).trans (Nat.choose_le_two_pow _ _)
      have hreal : ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
          (2 : ℝ) ^ A.card := by exact_mod_cast hnat
      calc
        ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤ (2 : ℝ) ^ A.card := hreal
        _ ≤ 32 * (K + 1) * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2 := by
          rw [hcardA]
          norm_num
          nlinarith
    · have hp : 1 ≤ p := by omega
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hAne
      have heraseCard : (A.erase a).card = 2 * p := by
        rw [Finset.card_erase_of_mem ha, hodd]
        omega
      have hzero := fixedCardSubsetSumFiber_even_bound hpair (A.erase a) hp
        heraseCard l t
      have hone := fixedCardSubsetSumFiber_even_bound hpair (A.erase a) hp
        heraseCard (l - 1) (t - a)
      have heraseNat := card_fixedCardSubsetSumFiber_le_erase A a l t
      have heraseReal : ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
          2 * (((fixedCardSubsetSumFiber (A.erase a) l t).card : ℝ) +
            ((fixedCardSubsetSumFiber (A.erase a) (l - 1) (t - a)).card : ℝ)) := by
        exact_mod_cast heraseNat
      have hpR : 0 < (p : ℝ) := by positivity
      have hcardR : 0 < ((2 * p + 1 : ℕ) : ℝ) := by positivity
      have hratio : (4 : ℝ) / (p : ℝ) ^ 2 ≤
          64 / ((2 * p + 1 : ℕ) : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hpR) (sq_pos_of_pos hcardR)).2
        push_cast
        nlinarith [show (1 : ℝ) ≤ p by exact_mod_cast hp]
      calc
        ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
            2 * (((fixedCardSubsetSumFiber (A.erase a) l t).card : ℝ) +
              ((fixedCardSubsetSumFiber (A.erase a) (l - 1) (t - a)).card : ℝ)) :=
          heraseReal
        _ ≤ 2 * (K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 +
            K * (4 : ℝ) ^ p / (p : ℝ) ^ 2) := by gcongr
        _ = 4 * K * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by ring
        _ ≤ 4 * (K + 1) * (4 : ℝ) ^ p / (p : ℝ) ^ 2 := by
          gcongr
          nlinarith
        _ = ((K + 1) * (4 : ℝ) ^ p) * (4 / (p : ℝ) ^ 2) := by ring
        _ ≤ ((K + 1) * (4 : ℝ) ^ p) *
            (64 / ((2 * p + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 32 * (K + 1) * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2 := by
          have hpow : (2 : ℝ) ^ (2 * p + 1) = 2 * (4 : ℝ) ^ p := by
            calc
              (2 : ℝ) ^ (2 * p + 1) = (2 : ℝ) ^ (p + p + 1) := by
                congr 1
                omega
              _ = (2 : ℝ) ^ (p + p) * 2 := by rw [pow_succ]
              _ = ((2 : ℝ) ^ p * (2 : ℝ) ^ p) * 2 := by rw [pow_add]
              _ = 2 * (4 : ℝ) ^ p := by
                rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
                ring
          rw [hodd, hpow]
          ring

/-- The exact uniform interpretation of the two assertions in Erdős Problem 362. -/
def Erdos362Statement : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ t : ℕ,
      ((subsetSumFiber A t).card : ℝ) ≤
        C * (2 : ℝ) ^ A.card / Real.sqrt (A.card : ℝ) ^ 3) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ l t : ℕ,
      ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
        C * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2)

/-- Erdős Problem 362: both subset-sum concentration estimates hold uniformly. -/
theorem erdos_362 :
    (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ t : ℕ,
        ((subsetSumFiber A t).card : ℝ) ≤
          C * (2 : ℝ) ^ A.card / Real.sqrt (A.card : ℝ) ^ 3) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ l t : ℕ,
        ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
          C * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2) := by
  constructor
  · exact exists_subsetSumFiber_real_bound
  · obtain ⟨C, hC, hscalar⟩ := exists_indexedScalarBound
    obtain ⟨K, hK, hfixed⟩ := exists_fixedCardSubsetSumFiber_bound hC hscalar
    refine ⟨K, hK, ?_⟩
    intro A hA l t
    exact hfixed A hA.card_pos l t


end Erdos362

#print axioms Erdos362.erdos_362

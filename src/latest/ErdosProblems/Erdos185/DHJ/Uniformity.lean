/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos185.DHJ.BinaryMulti

/-!
# Uniform sections for the ternary density Hales--Jewett argument

This file formalizes the elementary stopping argument of Dodos--Kanellopoulos--
Tyros.  A cube is exposed one block at a time.  If one section is too small,
averaging supplies another section whose density has increased by a fixed
amount.  Since density is at most one, after finitely many blocks one exposed
block has all of its sections close to the original density.

The recursive `Tower` representation below keeps the stopping argument free of
coordinate arithmetic.  At the public interface the tower is reindexed by a
finite equivalence, so the resulting subspace has the usual `Fin N` ambient
coordinates.
-/

open scoped BigOperators

namespace Erdos185.DHJ

open Combinatorics

universe u

/-! ## Towers of equal finite blocks -/

/-- `Tower X Y b` consists of `b` successive `X`-blocks followed by a tail
of type `Y`. -/
def Tower (X Y : Type u) : ℕ → Type u
  | 0 => Y
  | b + 1 => X × Tower X Y b

attribute [reducible] Tower

noncomputable instance towerFintype (X Y : Type u) [Fintype X] [Fintype Y] :
    (b : ℕ) → Fintype (Tower X Y b)
  | 0 => inferInstanceAs (Fintype Y)
  | b + 1 => by
      letI := towerFintype X Y b
      exact inferInstanceAs (Fintype (X × Tower X Y b))

instance towerNonempty (X Y : Type u) [Nonempty X] [Nonempty Y] :
    (b : ℕ) → Nonempty (Tower X Y b)
  | 0 => inferInstanceAs (Nonempty Y)
  | b + 1 => by
      letI := towerNonempty X Y b
      exact inferInstanceAs (Nonempty (X × Tower X Y b))

/-- A hole records one distinguished block in a tower and the values frozen
in all blocks preceding it. -/
inductive BlockHole (X Y : Type u) : ℕ → Type u
  | here (b : ℕ) : BlockHole X Y (b + 1)
  | later {b : ℕ} (x : X) (h : BlockHole X Y b) : BlockHole X Y (b + 1)

namespace BlockHole

/-- The still-unfrozen tail following the distinguished block. -/
def Tail {X Y : Type u} : {b : ℕ} → BlockHole X Y b → Type u
  | _, .here b => Tower X Y b
  | _, .later _ h => h.Tail

attribute [reducible] Tail

noncomputable def tailFintype {X Y : Type u} [Fintype X] [Fintype Y] :
    {b : ℕ} → (h : BlockHole X Y b) → Fintype h.Tail
  | _, .here b => towerFintype X Y b
  | _, .later _ h => h.tailFintype

def tailNonempty {X Y : Type u} [Nonempty X] [Nonempty Y] :
    {b : ℕ} → (h : BlockHole X Y b) → Nonempty h.Tail
  | _, .here b => towerNonempty X Y b
  | _, .later _ h => h.tailNonempty

noncomputable instance instTailFintype {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (h : BlockHole X Y b) : Fintype h.Tail :=
  h.tailFintype

instance instTailNonempty {X Y : Type u} [Nonempty X] [Nonempty Y]
    {b : ℕ} (h : BlockHole X Y b) : Nonempty h.Tail :=
  h.tailNonempty

/-- Fill the distinguished block and the remaining tail of a hole. -/
def fill {X Y : Type u} : {b : ℕ} → (h : BlockHole X Y b) →
    X → h.Tail → Tower X Y b
  | _, .here _, x, z => (x, z)
  | _, .later p h, x, z => (p, h.fill x z)

/-- The section obtained by filling a hole's distinguished block with `x`. -/
noncomputable def holeSection {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y b)) (h : BlockHole X Y b) (x : X) :
    Finset h.Tail := by
  classical
  letI := h.tailFintype
  exact Finset.univ.filter fun z ↦ h.fill x z ∈ A

@[simp] theorem mem_section {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y b)) (h : BlockHole X Y b)
    (x : X) (z : h.Tail) :
    z ∈ h.holeSection A x ↔ h.fill x z ∈ A := by
  classical
  letI := h.tailFintype
  simp [holeSection]

@[simp] theorem section_here {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y (b + 1))) (x : X) :
    (BlockHole.here b).holeSection A x = fiber A x := by
  classical
  ext z
  rw [mem_section, mem_fiber]
  rfl

@[simp] theorem section_later {X Y : Type u} [Fintype X] [Fintype Y]
    {b : ℕ} (A : Finset (Tower X Y (b + 1))) (p x : X)
    (h : BlockHole X Y b) :
    (BlockHole.later p h).holeSection A x = h.holeSection (fiber A p) x := by
  classical
  letI := h.tailFintype
  ext z
  rw [mem_section, mem_section, mem_fiber]
  rfl

end BlockHole

/-! ## The finite stopping argument -/

/-- If one value lies `eps` below a finite average, another value lies more
than `rho` above it, provided `(card X - 1) * rho ≤ eps`. -/
theorem exists_gt_average_add_of_exists_lt_average_sub
    {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ)
    {eps rho : ℝ} (hrho : 0 < rho)
    (hspread : ((Fintype.card X : ℝ) - 1) * rho ≤ eps)
    (x₀ : X) (hx₀ : f x₀ < average f - eps) :
    ∃ x : X, average f + rho < f x := by
  classical
  by_contra! hub
  have hcard : 0 < (Fintype.card X : ℝ) := by positivity
  have hsum_average :
      (∑ x : X, f x) = (Fintype.card X : ℝ) * average f := by
    rw [average_eq_sum_div_card]
    field_simp
  have herase_card :
      ((Finset.univ.erase x₀).card : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (by simp), Finset.card_univ]
    have hcNat : Fintype.card X - 1 + 1 = Fintype.card X :=
      Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)
    have hcReal : ((Fintype.card X - 1 : ℕ) : ℝ) + 1 = Fintype.card X := by
      exact_mod_cast hcNat
    linarith
  have herase :
      (∑ x ∈ Finset.univ.erase x₀, f x) ≤
        ∑ _x ∈ Finset.univ.erase x₀, (average f + rho) := by
    exact Finset.sum_le_sum fun x _ ↦ hub x
  have hlt :
      (∑ x : X, f x) < (Fintype.card X : ℝ) * average f := by
    calc
      (∑ x : X, f x) =
          (∑ x ∈ Finset.univ.erase x₀, f x) + f x₀ := by
            exact (Finset.sum_erase_add _ _
              (by simp : x₀ ∈ (Finset.univ : Finset X))).symm
      _ = f x₀ + ∑ x ∈ Finset.univ.erase x₀, f x := by
            ac_rfl
      _
          < (average f - eps) +
              ∑ _x ∈ Finset.univ.erase x₀, (average f + rho) :=
            add_lt_add_of_lt_of_le hx₀ herase
      _ = (average f - eps) +
            ((Fintype.card X : ℝ) - 1) * (average f + rho) := by
              rw [Finset.sum_const, nsmul_eq_mul, herase_card]
      _ ≤ (Fintype.card X : ℝ) * average f := by
            nlinarith
  linarith

/-- Stopping lemma with an explicit density budget.  The hypothesis says that
there are enough unexposed blocks for repeated increments of size `rho` to
cross the a priori upper bound one. -/
theorem tower_uniform_sections_aux
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    {eps rho : ℝ} (hrho : 0 < rho)
    (hspread : ((Fintype.card X : ℝ) - 1) * rho ≤ eps) :
    ∀ (b : ℕ) (A : Finset (Tower X Y b)),
      1 < density A + (b : ℝ) * rho →
      ∃ h : BlockHole X Y b, ∀ x : X,
        density A - eps ≤ density (h.holeSection A x) := by
  intro b
  induction b with
  | zero =>
      intro A hbudget
      have hle := density_le_one A
      norm_num only [Nat.cast_zero, zero_mul, add_zero] at hbudget
      exact (not_lt_of_ge hle hbudget).elim
  | succ b ih =>
      intro A hbudget
      by_cases huniform : ∀ x : X,
          density A - eps ≤ density (fiber A x)
      · refine ⟨BlockHole.here b, ?_⟩
        intro x
        rw [BlockHole.section_here]
        exact huniform x
      · push_neg at huniform
        obtain ⟨x₀, hx₀⟩ := huniform
        have havg : density A = average fun x : X ↦ density (fiber A x) :=
          density_eq_average_fiber A
        obtain ⟨p, hp⟩ :=
          exists_gt_average_add_of_exists_lt_average_sub
            (fun x : X ↦ density (fiber A x)) hrho hspread x₀ (by
              rw [← havg]
              exact hx₀)
        have hnext : 1 < density (fiber A p) + (b : ℝ) * rho := by
          rw [← havg] at hp
          norm_num only [Nat.cast_add, Nat.cast_one] at hbudget
          linarith
        obtain ⟨h, hh⟩ := ih (fiber A p) hnext
        refine ⟨BlockHole.later p h, ?_⟩
        intro x
        have hbase : density A - eps ≤ density (fiber A p) - eps := by
          linarith
        rw [BlockHole.section_later]
        exact hbase.trans (hh x)

/-- Uniform sections, in a dimension chosen solely from the block type and
the error. -/
theorem exists_tower_uniform_sections
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (hX : 1 < Fintype.card X) (eps : ℝ) (heps : 0 < eps) :
    ∃ b : ℕ, ∀ A : Finset (Tower X Y b),
      ∃ h : BlockHole X Y b, ∀ x : X,
        density A - eps ≤ density (h.holeSection A x) := by
  let rho : ℝ := eps / ((Fintype.card X : ℝ) - 1)
  have hden : 0 < (Fintype.card X : ℝ) - 1 := by
    have : (1 : ℝ) < Fintype.card X := by exact_mod_cast hX
    linarith
  have hrho : 0 < rho := div_pos heps hden
  obtain ⟨b, hb⟩ : ∃ b : ℕ, rho⁻¹ < b := exists_nat_gt rho⁻¹
  refine ⟨b, ?_⟩
  intro A
  apply tower_uniform_sections_aux hrho
  · dsimp [rho]
    field_simp
    norm_num
  · have hbrho : 1 < (b : ℝ) * rho := by
      have := mul_lt_mul_of_pos_right hb hrho
      have hinv : rho⁻¹ * rho = 1 := inv_mul_cancel₀ hrho.ne'
      linarith
    have hnonneg := density_nonneg A
    linarith

/-! ## Turning a tower hole into an ordinary combinatorial subspace -/

/-- The coordinate type of `b` successive blocks of length `m`. -/
def BlockIndex (m : ℕ) : ℕ → Type
  | 0 => Fin 0
  | b + 1 => Fin m ⊕ BlockIndex m b

noncomputable instance blockIndexFintype (m : ℕ) :
    (b : ℕ) → Fintype (BlockIndex m b)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | b + 1 => by
      letI := blockIndexFintype m b
      exact inferInstanceAs (Fintype (Fin m ⊕ BlockIndex m b))

/-- Flatten a tower of word-blocks to a word on `BlockIndex`. -/
def towerWord {q m : ℕ} :
    (b : ℕ) → Tower (Word q m) PUnit b → BlockIndex m b → Fin q
  | 0, _, i => Fin.elim0 i
  | _ + 1, (x, _), Sum.inl i => x i
  | b + 1, (_, z), Sum.inr i => towerWord b z i

/-- Unflatten a word on `BlockIndex` into a tower of word-blocks. -/
def wordTower {q m : ℕ} :
    (b : ℕ) → (BlockIndex m b → Fin q) → Tower (Word q m) PUnit b
  | 0, _ => PUnit.unit
  | b + 1, x => (fun i ↦ x (Sum.inl i), wordTower b fun i ↦ x (Sum.inr i))

@[simp] theorem wordTower_towerWord {q m : ℕ} :
    ∀ (b : ℕ) (z : Tower (Word q m) PUnit b),
      wordTower b (towerWord b z) = z := by
  intro b
  induction b with
  | zero => intro z; cases z; rfl
  | succ b ih =>
      rintro ⟨x, z⟩
      change (x, wordTower b (towerWord b z)) = (x, z)
      rw [ih]

@[simp] theorem towerWord_wordTower {q m : ℕ} :
    ∀ (b : ℕ) (x : BlockIndex m b → Fin q),
      towerWord b (wordTower b x) = x := by
  intro b
  induction b with
  | zero =>
      intro x
      funext i
      exact Fin.elim0 i
  | succ b ih =>
      intro x
      funext i
      cases i with
      | inl j =>
          change (fun i ↦ x (Sum.inl i)) j = x (Sum.inl j)
          rfl
      | inr j =>
          change towerWord b (wordTower b (fun i ↦ x (Sum.inr i))) j = x (Sum.inr j)
          rw [ih]

/-- Towers of `m`-letter blocks are equivalent to words on their flattened
coordinate type. -/
def towerWordEquiv (q m b : ℕ) :
    Tower (Word q m) PUnit b ≃ (BlockIndex m b → Fin q) where
  toFun := towerWord b
  invFun := wordTower b
  left_inv := wordTower_towerWord b
  right_inv := towerWord_wordTower b

/-- Reindex the flattened coordinate type by `Fin`. -/
noncomputable def towerFinEquiv (q m b : ℕ) :
    Tower (Word q m) PUnit b ≃ Word q (Fintype.card (BlockIndex m b)) :=
  (towerWordEquiv q m b).trans
    ((Fintype.equivFin (BlockIndex m b)).arrowCongr (Equiv.refl (Fin q)))

namespace BlockHole

/-- The subspace obtained by fixing a hole's frozen prefix and remaining tail,
while retaining the distinguished word-block as its parameter cube. -/
def subspace {q m : ℕ} :
    {b : ℕ} → (h : BlockHole (Word q m) PUnit b) → h.Tail →
      Subspace (Fin m) (Fin q) (BlockIndex m b)
  | _, .here b, z =>
      { idxFun := fun
          | Sum.inl i => Sum.inr i
          | Sum.inr j => Sum.inl (towerWord b z j)
        proper := fun e ↦ ⟨Sum.inl e, rfl⟩ }
  | _, .later p h, z =>
      { idxFun := fun
          | Sum.inl i => Sum.inl (p i)
          | Sum.inr j => (h.subspace z).idxFun j
        proper := by
          intro e
          obtain ⟨j, hj⟩ := (h.subspace z).proper e
          exact ⟨Sum.inr j, hj⟩ }

@[simp] theorem subspace_apply {q m : ℕ} :
    ∀ {b : ℕ} (h : BlockHole (Word q m) PUnit b) (z : h.Tail)
      (x : Word q m),
      h.subspace z x = towerWord b (h.fill x z) := by
  intro b h
  induction h with
  | here b =>
      intro z x
      funext i
      cases i <;> rfl
  | later p h ih =>
      intro z x
      funext i
      cases i with
      | inl j => rfl
      | inr j =>
          change h.subspace z x j = towerWord _ (h.fill x z) j
          exact congrFun (ih z x) j

end BlockHole

/-- Extend the fixed letters of a binary subspace to the ternary alphabet.
Its variable blocks remain variable, now over all three letters. -/
def extendBinarySubspace {d m : ℕ}
    (U : Subspace (Fin d) (Fin 2) (Fin m)) :
    Subspace (Fin d) (Fin 3) (Fin m) where
  idxFun i := (U.idxFun i).map Fin.castSucc id
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨i, by simp [hi]⟩

@[simp] theorem extendBinarySubspace_apply_restrictWord {d m : ℕ}
    (U : Subspace (Fin d) (Fin 2) (Fin m)) (x : Word 2 d) :
    extendBinarySubspace U (Erdos171.restrictWord x) =
      Erdos171.restrictWord (U x) := by
  funext i
  cases hi : U.idxFun i with
  | inl a =>
      simp [extendBinarySubspace, Erdos171.restrictWord,
        Subspace.coe_apply, hi]
  | inr e =>
      simp [extendBinarySubspace, Erdos171.restrictWord,
        Subspace.coe_apply, hi]

/-- Append a fixed coordinate block to a subspace. -/
def appendFixedTailSubspace {q d M r : ℕ}
    (U : Subspace (Fin d) (Fin q) (Fin M)) (y : Word q r) :
    Subspace (Fin d) (Fin q) (Fin (M + r)) where
  idxFun i := match finSumFinEquiv.symm i with
    | Sum.inl j => U.idxFun j
    | Sum.inr j => Sum.inl (y j)
  proper e := by
    obtain ⟨i, hi⟩ := U.proper e
    exact ⟨Fin.castAdd r i, by simp [hi]⟩

@[simp] theorem wordSplitEquiv_appendFixedTailSubspace_apply
    {q d M r : ℕ} (U : Subspace (Fin d) (Fin q) (Fin M))
    (y : Word q r) (x : Word q d) :
    wordSplitEquiv q M r (appendFixedTailSubspace U y x) = (U x, y) := by
  apply Prod.ext
  · funext i
    simp [appendFixedTailSubspace, wordSplitEquiv,
      Subspace.coe_apply]
  · funext i
    simp [appendFixedTailSubspace, wordSplitEquiv,
      Subspace.coe_apply]

/-! ## The restricted-subspace corollary -/

/-- Incidences between embedded binary points in the distinguished block and
the common tails of their sections. -/
noncomputable def binaryHoleIncidence {M b : ℕ}
    (A : Finset (Tower (Word 3 M) PUnit b))
    (h : BlockHole (Word 3 M) PUnit b) :
    Finset (Word 2 M × h.Tail) := by
  classical
  letI := h.tailFintype
  exact Finset.univ.filter fun p ↦
    h.fill (Erdos171.restrictWord p.1) p.2 ∈ A

@[simp] theorem mem_binaryHoleIncidence {M b : ℕ}
    (A : Finset (Tower (Word 3 M) PUnit b))
    (h : BlockHole (Word 3 M) PUnit b) (x : Word 2 M) (z : h.Tail) :
    (x, z) ∈ binaryHoleIncidence A h ↔
      h.fill (Erdos171.restrictWord x) z ∈ A := by
  classical
  letI := h.tailFintype
  simp [binaryHoleIncidence]

@[simp] theorem fiber_binaryHoleIncidence {M b : ℕ}
    (A : Finset (Tower (Word 3 M) PUnit b))
    (h : BlockHole (Word 3 M) PUnit b) (x : Word 2 M) :
    fiber (binaryHoleIncidence A h) x =
      h.holeSection A (Erdos171.restrictWord x) := by
  classical
  letI := h.tailFintype
  ext z
  simp

/-- Transpose a finite binary relation. -/
noncomputable def transposeFinset {X Y : Type*}
    (A : Finset (X × Y)) : Finset (Y × X) := by
  classical
  exact A.map (Equiv.prodComm X Y).toEmbedding

@[simp] theorem mem_transposeFinset {X Y : Type*}
    (A : Finset (X × Y)) (y : Y) (x : X) :
    (y, x) ∈ transposeFinset A ↔ (x, y) ∈ A := by
  classical
  simp [transposeFinset]

@[simp] theorem density_transposeFinset {X Y : Type*}
    [Fintype X] [Fintype Y] (A : Finset (X × Y)) :
    density (transposeFinset A) = density A := by
  simpa [transposeFinset] using density_map_equiv (Equiv.prodComm X Y) A

/-- Evaluation of a reindexed hole subspace agrees with the tower-to-`Fin`
equivalence. -/
theorem reindex_hole_comp_apply {q m d b : ℕ}
    (h : BlockHole (Word q m) PUnit b) (z : h.Tail)
    (V : Subspace (Fin d) (Fin q) (Fin m)) (x : Word q d) :
    ((h.subspace z).comp V).reindex (Equiv.refl _) (Equiv.refl _)
        (Fintype.equivFin (BlockIndex m b)) x =
      towerFinEquiv q m b (h.fill (V x) z) := by
  funext i
  simp only [Subspace.reindex_apply, Equiv.refl_apply, Equiv.refl_symm,
    Function.comp_apply, Subspace.comp_apply, BlockHole.subspace_apply]
  rfl

/-- A dense ternary cube contains a ternary subspace all of whose binary
parameter points lie in the dense set.  This is Corollary 5 of the specialized
DKT argument. -/
theorem restricted_binary_subspace (m : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ A : Finset (Word 3 N), delta ≤ density A →
      ∃ U : Subspace (Fin m) (Fin 3) (Fin N), RestrictedPartContained U A := by
  obtain ⟨M, hM⟩ := binary_multidimensional m (delta / 2) (by linarith)
  let K := M + 1
  have hKpos : 0 < K := by simp [K]
  have hblock : 1 < Fintype.card (Word 3 K) := by
    rw [Erdos171.card_word]
    exact Nat.one_lt_pow hKpos.ne' (by norm_num)
  obtain ⟨b, hb⟩ := exists_tower_uniform_sections
    (X := Word 3 K) (Y := PUnit) hblock (delta / 2) (by linarith)
  let N := Fintype.card (BlockIndex K b)
  let e : Tower (Word 3 K) PUnit b ≃ Word 3 N := towerFinEquiv 3 K b
  refine ⟨N, ?_⟩
  intro A hA
  classical
  let AT : Finset (Tower (Word 3 K) PUnit b) := A.map e.symm.toEmbedding
  have hAT : density AT = density A := by
    simpa [AT] using density_map_equiv e.symm A
  obtain ⟨h, hh⟩ := hb AT
  letI := h.tailFintype
  letI := h.tailNonempty
  let R := binaryHoleIncidence AT h
  have hsections : ∀ x : Word 2 K,
      delta / 2 ≤ density (fiber R x) := by
    intro x
    rw [show fiber R x = h.holeSection AT (Erdos171.restrictWord x) by
      simp [R]]
    have := hh (Erdos171.restrictWord x)
    rw [hAT] at this
    linarith
  have hR : delta / 2 ≤ density R := by
    rw [density_eq_average_fiber]
    exact const_le_average hsections
  let RT := transposeFinset R
  have hRT : delta / 2 ≤ density RT :=
    hR.trans_eq (density_transposeFinset R).symm
  obtain ⟨z, hz⟩ := exists_fiber_density_ge RT
  let Cfull : Finset (Word 2 K) := fiber RT z
  have hCfull : delta / 2 ≤ density Cfull := hRT.trans hz
  have hKeq : K = M + 1 := rfl
  let Csplit : Finset (Word 2 M × Word 2 1) := by
    rw [hKeq] at Cfull
    exact splitFinset Cfull
  have hCsplit : density Csplit = density Cfull := by
    simpa [Csplit, K] using
      (density_map_equiv (wordSplitEquiv 2 M 1) Cfull)
  let Cswap := transposeFinset Csplit
  have hCswap : delta / 2 ≤ density Cswap := by
    rw [density_transposeFinset, hCsplit]
    exact hCfull
  obtain ⟨y, hy⟩ := exists_fiber_density_ge Cswap
  let C : Finset (Word 2 M) := fiber Cswap y
  have hC : delta / 2 ≤ density C := hCswap.trans hy
  obtain ⟨U₂, hU₂⟩ := hM C hC
  let UK : Subspace (Fin m) (Fin 2) (Fin K) :=
    appendFixedTailSubspace U₂ y
  let V : Subspace (Fin m) (Fin 3) (Fin K) := extendBinarySubspace UK
  let W : Subspace (Fin m) (Fin 3) (Fin N) :=
    ((h.subspace z).comp V).reindex (Equiv.refl _) (Equiv.refl _)
      (Fintype.equivFin (BlockIndex K b))
  refine ⟨W, ?_⟩
  intro x
  have hxC : U₂ x ∈ C := hU₂ x
  have hxCswap : (y, U₂ x) ∈ Cswap := (mem_fiber Cswap y (U₂ x)).1 hxC
  have hxCsplit : (U₂ x, y) ∈ Csplit := by
    simpa [Cswap] using hxCswap
  have hxCfull : UK x ∈ Cfull := by
    have hmem : (wordSplitEquiv 2 M 1).symm (U₂ x, y) ∈ Cfull := by
      simpa [Csplit] using hxCsplit
    have hUKsplit : wordSplitEquiv 2 M 1 (UK x) = (U₂ x, y) := by
      simpa only [UK] using
        wordSplitEquiv_appendFixedTailSubspace_apply U₂ y x
    rw [← hUKsplit] at hmem
    simpa using hmem
  have hxR : (UK x, z) ∈ R := by
    have hxRT : (z, UK x) ∈ RT := (mem_fiber RT z (UK x)).1 hxCfull
    simpa [RT] using hxRT
  have hxAT : h.fill (Erdos171.restrictWord (UK x)) z ∈ AT := by
    simpa [R] using hxR
  have hxe : e (h.fill (Erdos171.restrictWord (UK x)) z) ∈ A := by
    simpa [AT] using hxAT
  have hW : W (Erdos171.restrictWord x) =
      e (h.fill (Erdos171.restrictWord (UK x)) z) := by
    rw [show W (Erdos171.restrictWord x) =
        towerFinEquiv 3 K b (h.fill (V (Erdos171.restrictWord x)) z) by
      exact reindex_hole_comp_apply h z V (Erdos171.restrictWord x)]
    simp [V]
    rfl
  rw [hW]
  exact hxe

end Erdos185.DHJ

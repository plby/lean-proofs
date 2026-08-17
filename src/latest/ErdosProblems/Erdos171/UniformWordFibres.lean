/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.SubspaceOps
import ErdosProblems.Erdos171.UniformFibres

/-!
# Uniform fibres in ordinary finite word cubes

`UniformFibres.exists_uniform_frozenPrefix_real` is proved on a recursively
nested product of word blocks.  This file transports that result through
`BlockTower.wordEquiv`, so its conclusion can be consumed without leaving the
usual model `Word t n = Fin n → Fin t`.
-/

namespace Erdos171

open BlockTower
open UniformFibres

namespace UniformWordFibres

/-- The subspace obtained by letting the first block vary and fixing the
flattened remainder of a block tower. -/
def towerHeadSubspace {t m s r : ℕ}
    (z : BlockTower (Word t m) (Word t s) r) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin ((r + 1) * m + s)) :=
  ((default : Combinatorics.Subspace (Fin m) (Fin t) (Fin m)).extendRightWord
      (wordEquiv t m s r z)).reindex (Equiv.refl _) (Equiv.refl _) <|
    finSumFinEquiv.trans (finCongr (by
      simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]))

@[simp] theorem towerHeadSubspace_apply {t m s r : ℕ}
    (z : BlockTower (Word t m) (Word t s) r) (x : Word t m) :
    towerHeadSubspace z x = wordEquiv t m s (r + 1) (x, z) := by
  funext i
  simp [towerHeadSubspace, BlockTower.wordEquiv, BlockTower.wordAddEquiv,
    Combinatorics.Subspace.reindex_apply,
    Combinatorics.Subspace.extendRightWord_apply,
    Combinatorics.Subspace.sumWord, Equiv.piCongrLeft_apply]
  cases h : finSumFinEquiv.symm (Fin.cast _ i) <;> rfl

/-- Add one fixed word block in front of a subspace which already describes
the remaining block tower. -/
def towerPrependSubspace {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * m + s))) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin ((r + 1) * m + s)) :=
  (U.extendRightWord a).reindex (Equiv.refl _) (Equiv.refl _) <|
    (((Equiv.sumComm (Fin (r * m + s)) (Fin m)).trans finSumFinEquiv).trans
      (finCongr (by
        simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])))

@[simp] theorem towerPrependSubspace_apply {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * m + s)))
    (x : Word t m) :
    towerPrependSubspace a U x =
      wordEquiv t m s (r + 1) (a, (wordEquiv t m s r).symm (U x)) := by
  funext i
  simp [towerPrependSubspace, BlockTower.wordEquiv, BlockTower.wordAddEquiv,
    Combinatorics.Subspace.reindex_apply,
    Combinatorics.Subspace.extendRightWord_apply,
    Combinatorics.Subspace.sumWord, Equiv.piCongrLeft_apply]
  cases h : finSumFinEquiv.symm (Fin.cast _ i) <;> rfl

/-- Generic version of `towerPrependSubspace`: the parameter type is
arbitrary, so the subspace may involve any collection of directions in all
remaining tower coordinates. -/
def towerPrependSubspaceGeneric {η : Type*} {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace η (Fin t) (Fin (r * m + s))) :
    Combinatorics.Subspace η (Fin t) (Fin ((r + 1) * m + s)) :=
  (U.extendRightWord a).reindex (Equiv.refl _) (Equiv.refl _) <|
    (((Equiv.sumComm (Fin (r * m + s)) (Fin m)).trans finSumFinEquiv).trans
      (finCongr (by
        simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])))

@[simp] theorem towerPrependSubspaceGeneric_apply {η : Type*}
    {t m s r : ℕ} (a : Word t m)
    (U : Combinatorics.Subspace η (Fin t) (Fin (r * m + s)))
    (x : η → Fin t) :
    towerPrependSubspaceGeneric a U x =
      wordEquiv t m s (r + 1) (a, (wordEquiv t m s r).symm (U x)) := by
  funext i
  simp [towerPrependSubspaceGeneric, BlockTower.wordEquiv,
    BlockTower.wordAddEquiv, Combinatorics.Subspace.reindex_apply,
    Combinatorics.Subspace.extendRightWord_apply,
    Combinatorics.Subspace.sumWord, Equiv.piCongrLeft_apply]
  cases h : finSumFinEquiv.symm (Fin.cast _ i) <;> rfl

/-- Recursively insert an arbitrary subspace on all remaining flattened tower
coordinates behind a frozen prefix. -/
def frozenPrefixSubspaceGeneric {η : Type*} {t m s : ℕ} : {r q : ℕ} →
    (p : FrozenPrefix (Word t m) r q) →
    Combinatorics.Subspace η (Fin t) (Fin (q * m + s)) →
      Combinatorics.Subspace η (Fin t) (Fin (r * m + s))
  | _, _, .nil _, U => U
  | _, _, .cons a p, U =>
      towerPrependSubspaceGeneric a (frozenPrefixSubspaceGeneric p U)

@[simp] theorem frozenPrefixSubspaceGeneric_apply {η : Type*}
    {t m s : ℕ} : ∀ {r q : ℕ}
    (p : FrozenPrefix (Word t m) r q)
    (U : Combinatorics.Subspace η (Fin t) (Fin (q * m + s)))
    (x : η → Fin t),
    frozenPrefixSubspaceGeneric p U x =
      wordEquiv t m s r
        (p.prepend ((wordEquiv t m s q).symm (U x)))
  | _, _, .nil _, U, x => by
      simp [frozenPrefixSubspaceGeneric, FrozenPrefix.prepend]
  | _, _, .cons a p, U, x => by
      rw [frozenPrefixSubspaceGeneric, towerPrependSubspaceGeneric_apply,
        frozenPrefixSubspaceGeneric_apply]
      simp [FrozenPrefix.prepend]

/-- The concrete `m`-dimensional subspace selected by a frozen prefix, after
also fixing one word in the surviving suffix cube. -/
def frozenPrefixSubspace {t m s : ℕ} : {r q : ℕ} →
    (p : FrozenPrefix (Word t m) r (q + 1)) →
    BlockTower (Word t m) (Word t s) q →
      Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * m + s))
  | _, _, .nil _, z => towerHeadSubspace z
  | _, _, .cons a p, z => towerPrependSubspace a (frozenPrefixSubspace p z)

@[simp] theorem frozenPrefixSubspace_apply {t m s : ℕ} : ∀ {r q : ℕ}
    (p : FrozenPrefix (Word t m) r (q + 1))
    (z : BlockTower (Word t m) (Word t s) q) (x : Word t m),
    frozenPrefixSubspace p z x =
      wordEquiv t m s r (p.prepend (x, z))
  | _, _, .nil _, z, x => towerHeadSubspace_apply z x
  | _, _, .cons a p, z, x => by
      rw [frozenPrefixSubspace, towerPrependSubspace_apply,
        frozenPrefixSubspace_apply]
      simp [FrozenPrefix.prepend]

/-- Pull a finite set of ordinary words back to the corresponding block tower. -/
noncomputable def towerPullback (t m s r : ℕ)
    (A : Finset (Word t (r * m + s))) :
    Finset (BlockTower (Word t m) (Word t s) r) :=
  A.map (wordEquiv t m s r).symm.toEmbedding

@[simp] theorem dens_towerPullback (t m s r : ℕ)
    (A : Finset (Word t (r * m + s))) :
    (towerPullback t m s r A).dens = A.dens := by
  simp [towerPullback]

/-- After freezing `p`, flatten all remaining tower coordinates back to one
ordinary word cube. -/
noncomputable def frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q) :
    Finset (Word t (q * m + s)) :=
  (p.iterFibre (towerPullback t m s r A)).map
    (wordEquiv t m s q).toEmbedding

@[simp] theorem dens_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q) :
    (frozenPrefixWordPullback A p).dens =
      (p.iterFibre (towerPullback t m s r A)).dens := by
  simp [frozenPrefixWordPullback]

@[simp] theorem mem_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q) (z : Word t (q * m + s)) :
    z ∈ frozenPrefixWordPullback A p ↔
      wordEquiv t m s r
        (p.prepend ((wordEquiv t m s q).symm z)) ∈ A := by
  simp [frozenPrefixWordPullback]
  simp [towerPullback]

/-- Pulling the frozen-prefix word set back along an arbitrary remaining
subspace is exactly the same membership test as evaluating its realization
in the original cube. -/
@[simp] theorem mem_frozenPrefixWordPullback_subspace {η : Type*}
    {t m s r q : ℕ} (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (U : Combinatorics.Subspace η (Fin t) (Fin (q * m + s)))
    (x : η → Fin t) :
    U x ∈ frozenPrefixWordPullback A p ↔
      frozenPrefixSubspaceGeneric p U x ∈ A := by
  rw [mem_frozenPrefixWordPullback, frozenPrefixSubspaceGeneric_apply]

theorem frozenPrefixSubspaceGeneric_mem_iff {η : Type*}
    {t m s r q : ℕ} (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (U : Combinatorics.Subspace η (Fin t) (Fin (q * m + s)))
    (x : η → Fin t) :
    frozenPrefixSubspaceGeneric p U x ∈ A ↔
      U x ∈ frozenPrefixWordPullback A p :=
  (mem_frozenPrefixWordPullback_subspace A p U x).symm

/-- A line in the remaining word pullback maps to a line in the original set. -/
theorem containsLine_of_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (h : ContainsLine
      (frozenPrefixWordPullback A p : Set (Word t (q * m + s)))) :
    ContainsLine (A : Set (Word t (r * m + s))) := by
  obtain ⟨l, hl⟩ := h
  let I : Combinatorics.Subspace (Fin (q * m + s)) (Fin t)
      (Fin (q * m + s)) := default
  let U := frozenPrefixSubspaceGeneric p I
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Combinatorics.Subspace.lineMap_apply]
  apply (mem_frozenPrefixWordPullback_subspace A p I (l a)).1
  change l a ∈ frozenPrefixWordPullback A p
  exact hl ⟨a, rfl⟩

theorem not_containsLine_frozenPrefixWordPullback {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r q)
    (hA : ¬ ContainsLine (A : Set (Word t (r * m + s)))) :
    ¬ ContainsLine
      (frozenPrefixWordPullback A p : Set (Word t (q * m + s))) :=
  fun h ↦ hA (containsLine_of_frozenPrefixWordPullback A p h)

/-- The suffix fibre, expressed again as an ordinary word cube, after freezing
the prefix recorded by `p` and assigning `x` to the selected `m`-letter block. -/
noncomputable def wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1)) (x : Word t m) :
    Finset (Word t (q * m + s)) :=
  (BlockTower.fibre (p.iterFibre (towerPullback t m s r A)) x).map
    (wordEquiv t m s q).toEmbedding

@[simp] theorem dens_wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1)) (x : Word t m) :
    (wordFibre A p x).dens =
      (BlockTower.fibre (p.iterFibre (towerPullback t m s r A)) x).dens := by
  simp [wordFibre]

@[simp] theorem mem_wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1))
    (x : Word t m) (z : Word t (q * m + s)) :
    z ∈ wordFibre A p x ↔
      wordEquiv t m s r
        (p.prepend (x, (wordEquiv t m s q).symm z)) ∈ A := by
  simp [wordFibre]
  rw [FrozenPrefix.mem_iterFibre]
  simp [towerPullback]

/-- Membership in a suffix fibre is the same as membership of the
corresponding point of the concrete selected block subspace. -/
@[simp] theorem frozenPrefixSubspace_mem_iff_wordFibre {t m s r q : ℕ}
    (A : Finset (Word t (r * m + s)))
    (p : FrozenPrefix (Word t m) r (q + 1))
    (x : Word t m) (z : Word t (q * m + s)) :
    frozenPrefixSubspace p ((wordEquiv t m s q).symm z) x ∈ A ↔
      z ∈ wordFibre A p x := by
  simpa only [frozenPrefixSubspace_apply] using (mem_wordFibre A p x z).symm

/-- Ordinary-word version of the uniform-fibres lemma, with an arbitrary
terminal suffix length `s`.  The total dimension is `(R+1)m+s`; after a
frozen prefix, every assignment to the next `m`-letter block leaves a suffix
fibre of density at least the original density minus `e`. -/
theorem exists_uniform_wordFibres (t m s : ℕ) (ht : 2 ≤ t) (hm : 0 < m)
    (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (Word t ((R + 1) * m + s)),
      ∃ q : ℕ, ∃ p : FrozenPrefix (Word t m) (R + 1) (q + 1),
        ∀ x : Word t m,
          (A.dens : ℝ) - e ≤ (wordFibre A p x).dens := by
  let _ : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  let _ : Nonempty (Word t m) := Pi.instNonempty
  have hcard : 1 < Fintype.card (Word t m) := by
    rw [card_word]
    exact one_lt_pow₀ (by omega) (Nat.ne_of_gt hm)
  obtain ⟨R, hR⟩ :=
    exists_uniform_frozenPrefix_real
      (X := Word t m) (Y := Word t s) hcard e he
  refine ⟨R, fun A ↦ ?_⟩
  obtain ⟨q, p, hp⟩ := hR (towerPullback t m s (R + 1) A)
  refine ⟨q, p, fun x ↦ ?_⟩
  have hA : ((towerPullback t m s (R + 1) A).dens : ℝ) = (A.dens : ℝ) := by
    exact_mod_cast dens_towerPullback t m s (R + 1) A
  have hF : ((wordFibre A p x).dens : ℝ) =
      ((BlockTower.fibre
        (p.iterFibre (towerPullback t m s (R + 1) A)) x).dens : ℝ) := by
    exact_mod_cast dens_wordFibre A p x
  rw [hF, ← hA]
  exact hp x

/-- A version with no terminal coordinates.  Thus one may choose the total
dimension to be a positive multiple `(R+1)m` of the target block size. -/
theorem exists_uniform_wordFibres_zeroSuffix (t m : ℕ) (ht : 2 ≤ t)
    (hm : 0 < m) (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (Word t ((R + 1) * m)),
      ∃ q : ℕ, ∃ p : FrozenPrefix (Word t m) (R + 1) (q + 1),
        ∀ x : Word t m,
          (A.dens : ℝ) - e ≤ (wordFibre (s := 0) A p x).dens := by
  simpa using exists_uniform_wordFibres t m 0 ht hm e he

/-- Packaged form exposing both the uniform density estimate and the concrete
subspace whose points realize the suffix fibres. -/
theorem exists_uniform_wordFibres_with_subspaces (t m s : ℕ)
    (ht : 2 ≤ t) (hm : 0 < m) (e : ℝ) (he : 0 < e) :
    ∃ R : ℕ, ∀ A : Finset (Word t ((R + 1) * m + s)),
      ∃ q : ℕ, ∃ p : FrozenPrefix (Word t m) (R + 1) (q + 1),
        (∀ x : Word t m,
          (A.dens : ℝ) - e ≤ (wordFibre A p x).dens) ∧
        ∀ (x : Word t m) (z : Word t (q * m + s)),
          frozenPrefixSubspace p ((wordEquiv t m s q).symm z) x ∈ A ↔
            z ∈ wordFibre A p x := by
  obtain ⟨R, hR⟩ := exists_uniform_wordFibres t m s ht hm e he
  refine ⟨R, fun A ↦ ?_⟩
  obtain ⟨q, p, hp⟩ := hR A
  exact ⟨q, p, hp, fun x z ↦ frozenPrefixSubspace_mem_iff_wordFibre A p x z⟩

end UniformWordFibres

end Erdos171

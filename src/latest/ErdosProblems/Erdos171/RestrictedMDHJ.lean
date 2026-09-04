/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Framework
import ErdosProblems.Erdos171.SubspaceOps
import ErdosProblems.Erdos171.UniformFibres

/-!
# Restricted multidimensional density Hales--Jewett

This file formalizes Corollary 5 of Dodos--Kanellopoulos--Tyros.  Assuming
density Hales--Jewett for the alphabet `Fin k`, every dense subset of a large
cube over `Fin (k + 1)` contains the old-alphabet face of an arbitrarily
high-dimensional combinatorial subspace.
-/

namespace Erdos171


/-- The nested coordinate type corresponding to a tower of word blocks. -/
abbrev BlockCoord (M s : ℕ) : ℕ → Type
  | 0 => Fin s
  | r + 1 => Fin M ⊕ BlockCoord M s r

namespace BlockCoord

/-- Flatten the nested coordinate type of a block tower. -/
def equivFin (M s : ℕ) : ∀ r : ℕ, BlockCoord M s r ≃ Fin (r * M + s)
  | 0 => finCongr (by simp)
  | r + 1 =>
      ((Equiv.refl (Fin M)).sumCongr (equivFin M s r)).trans <|
        finSumFinEquiv.trans <| finCongr (by
          simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm])

end BlockCoord

namespace BlockTower

universe u

theorem nonempty {X Y : Type u} [Nonempty X] [Nonempty Y] :
    ∀ r : ℕ, Nonempty (BlockTower X Y r)
  | 0 => inferInstance
  | r + 1 => by
      let : Nonempty (BlockTower X Y r) :=
        nonempty (X := X) (Y := Y) r
      infer_instance

/-- View a tower of word blocks as a word on the corresponding nested
coordinate type. -/
def functionEquiv (t M s : ℕ) : ∀ r : ℕ,
    BlockTower (Word t M) (Word t s) r ≃ (BlockCoord M s r → Fin t)
  | 0 => Equiv.refl _
  | r + 1 =>
      ((Equiv.refl (Word t M)).prodCongr (functionEquiv t M s r)).trans
        (Equiv.sumArrowEquivProdArrow (Fin M) (BlockCoord M s r) (Fin t)).symm

@[simp] theorem functionEquiv_zero_apply (t M s : ℕ) (z : Word t s) :
    functionEquiv t M s 0 z = z := rfl

@[simp] theorem functionEquiv_succ_apply (t M s r : ℕ)
    (z : Word t M) (y : BlockTower (Word t M) (Word t s) r) :
    functionEquiv t M s (r + 1) (z, y) =
      Sum.elim z (functionEquiv t M s r y) := by
  rfl

/-- A block-tower/ordinary-word equivalence factored through its explicit
coordinate equivalence. -/
def coordinateWordEquiv (t M s r : ℕ) :
    BlockTower (Word t M) (Word t s) r ≃ Word t (r * M + s) :=
  (functionEquiv t M s r).trans <|
    Equiv.piCongrLeft (fun _ : Fin (r * M + s) ↦ Fin t) (BlockCoord.equivFin M s r)

@[simp] theorem coordinateWordEquiv_apply (t M s r : ℕ)
    (z : BlockTower (Word t M) (Word t s) r) (i : Fin (r * M + s)) :
    coordinateWordEquiv t M s r z i =
      functionEquiv t M s r z ((BlockCoord.equivFin M s r).symm i) := by
  simp only [coordinateWordEquiv, Equiv.trans_apply]
  rw [Equiv.piCongrLeft_apply]
  simp

end BlockTower

/-- Prepend a fixed coordinate block without changing the parameter
directions of a subspace. -/
def fixedLeft {eta alpha iota kappa : Type*} (z : kappa → alpha)
    (U : Combinatorics.Subspace eta alpha iota) :
    Combinatorics.Subspace eta alpha (kappa ⊕ iota) where
  idxFun
    | Sum.inl i => Sum.inl (z i)
    | Sum.inr j => U.idxFun j
  proper e := by
    obtain ⟨j, hj⟩ := U.proper e
    exact ⟨Sum.inr j, hj⟩

@[simp] theorem fixedLeft_apply {eta alpha iota kappa : Type*}
    (z : kappa → alpha) (U : Combinatorics.Subspace eta alpha iota)
    (x : eta → alpha) :
    fixedLeft z U x = Sum.elim z (U x) := by
  funext i
  cases i <;> simp [fixedLeft, Combinatorics.Subspace.coe_apply]

namespace UniformFibres.FrozenPrefix

open BlockTower

/-- Realize a frozen prefix, a subspace in the next block, and a fixed
remaining suffix as a subspace in the original flattened word cube. -/
def realizeNested {t M s m q : ℕ} : ∀ {r : ℕ},
    FrozenPrefix (Word t M) r (q + 1) →
      Combinatorics.Subspace (Fin m) (Fin t) (Fin M) →
      BlockTower (Word t M) (Word t s) q →
      Combinatorics.Subspace (Fin m) (Fin t) (BlockCoord M s r)
  | _, .nil _, V, y =>
      V.extendRightWord (BlockTower.functionEquiv t M s q y)
  | _, .cons z p, V, y =>
      fixedLeft z (realizeNested p V y)

@[simp] theorem realizeNested_apply {t M s m : ℕ} : ∀ {q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) (x : Word t m),
    realizeNested p V y x =
      BlockTower.functionEquiv t M s r (p.prepend (V x, y))
  | q, _, .nil _, V, y, x => by
      rw [show realizeNested (.nil (q + 1)) V y x =
          Sum.elim (V x) (BlockTower.functionEquiv t M s q y) by
        simp [realizeNested, Combinatorics.Subspace.extendRightWord_apply,
          Combinatorics.Subspace.sumWord]]
      exact (BlockTower.functionEquiv_succ_apply t M s q (V x) y).symm
  | q, _, .cons z p, V, y, x => by
      rw [show realizeNested (.cons z p) V y x =
          Sum.elim z (realizeNested p V y x) by
        simp [realizeNested]]
      rw [realizeNested_apply p V y x]
      exact (BlockTower.functionEquiv_succ_apply t M s _ z
        (p.prepend (V x, y))).symm

/-- Flatten `realizeNested` to an ordinary `Fin`-indexed word cube. -/
def realize {t M s m q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) :
    Combinatorics.Subspace (Fin m) (Fin t) (Fin (r * M + s)) :=
  (realizeNested p V y).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem realize_apply {t M s m q r : ℕ}
    (p : FrozenPrefix (Word t M) r (q + 1))
    (V : Combinatorics.Subspace (Fin m) (Fin t) (Fin M))
    (y : BlockTower (Word t M) (Word t s) q) (x : Word t m) :
    realize p V y x =
      BlockTower.coordinateWordEquiv t M s r (p.prepend (V x, y)) := by
  funext i
  simp [realize,
    Combinatorics.Subspace.reindex_apply]

end UniformFibres.FrozenPrefix

/-- A set in a cube over `Fin (k + 1)` contains the restriction to the old
alphabet `Fin k` of an `m`-dimensional combinatorial subspace. -/
def ContainsRestrictedSubspace (m : ℕ) {k n : ℕ}
    (A : Set (Word (k + 1) n)) : Prop :=
  ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
    Set.range (fun x : Word k m ↦ U (liftWord x)) ⊆ A

theorem containsRestrictedSubspace_iff (m : ℕ) {k n : ℕ}
    {A : Set (Word (k + 1) n)} :
    ContainsRestrictedSubspace m A ↔
      ∃ U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∀ x : Word k m, U (liftWord x) ∈ A := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, fun x ↦ hU ⟨x, rfl⟩⟩
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hU x

theorem ContainsRestrictedSubspace.mono {m k n : ℕ}
    {A B : Set (Word (k + 1) n)}
    (hA : ContainsRestrictedSubspace m A) (hAB : A ⊆ B) :
    ContainsRestrictedSubspace m B := by
  obtain ⟨U, hU⟩ := hA
  exact ⟨U, hU.trans hAB⟩

/-- One-witness form of the restricted multidimensional density theorem. -/
def FiniteRestrictedMDHJ (k m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n))

/-- Eventual form of the restricted multidimensional density theorem. -/
def EventualRestrictedMDHJ (k m : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n))

/-- Dodos--Kanellopoulos--Tyros, Corollary 5: density Hales--Jewett on the
old alphabet gives arbitrarily high-dimensional restricted subspaces in a
dense cube over the alphabet with one new letter. -/
theorem FiniteDensityHJ.finiteRestrictedMDHJ {k : ℕ} (h : FiniteDensityHJ k)
    (hk : 0 < k) (m : ℕ) : FiniteRestrictedMDHJ k m := by
  intro δ hδ
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let : Nonempty (Fin (k + 1)) := Fin.pos_iff_nonempty.mp (by omega)
  have hMD := (h.finiteDensityMDHJ hk m).eventual hk
  obtain ⟨M₀, hM₀⟩ := hMD (δ / 2) (half_pos hδ)
  let M : ℕ := max M₀ 1
  have hM₀M : M₀ ≤ M := Nat.le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  have hM := hM₀ M hM₀M
  let X := Word (k + 1) M
  let Y := Word (k + 1) 0
  have hXcard : 1 < Fintype.card X := by
    rw [show Fintype.card X = (k + 1) ^ M by simp [X, Word]]
    exact one_lt_pow' (by omega) hMpos.ne'
  obtain ⟨R, hR⟩ := UniformFibres.exists_uniform_frozenPrefix_real
    (X := X) (Y := Y) hXcard (δ / 2) (half_pos hδ)
  refine ⟨(R + 1) * M + 0, ?_⟩
  intro A hA
  classical
  let e := BlockTower.coordinateWordEquiv (k + 1) M 0 (R + 1)
  let AT : Finset (BlockTower X Y (R + 1)) := A.map e.symm.toEmbedding
  have hATdens : density AT = density A := by
    simpa [AT, e, X, Y] using density_map_equiv e.symm A
  obtain ⟨q, p, hp⟩ := hR AT
  let Aₚ : Finset (BlockTower X Y (q + 1)) := p.iterFibre AT
  have hrow (x : Word k M) :
      δ / 2 ≤ density (BlockTower.fibre Aₚ (liftWord x)) := by
    have hpx : density AT - δ / 2 ≤
        density (BlockTower.fibre Aₚ (liftWord x)) := by
      simpa only [density_eq_coe_dens, Aₚ] using hp (liftWord x)
    have hbase : δ / 2 ≤ density AT - δ / 2 := by
      rw [hATdens]
      linarith
    exact hbase.trans hpx
  let C : Finset (Word k M × BlockTower X Y q) :=
    Finset.univ.filter fun z ↦ (liftWord z.1, z.2) ∈ Aₚ
  have hCfiber (x : Word k M) :
      fiber C x = BlockTower.fibre Aₚ (liftWord x) := by
    ext y
    simp [C]
  have hCdense : δ / 2 ≤ density C := by
    rw [density_eq_average_fiber]
    apply const_le_average
    intro x
    rw [hCfiber]
    exact hrow x
  let : Nonempty (BlockTower X Y q) := BlockTower.nonempty q
  have hCcolumns :
      δ / 2 ≤ average fun y : BlockTower X Y q ↦ density (columnFiber C y) := by
    rwa [← density_eq_average_columnFiber]
  obtain ⟨y, hy⟩ := exists_ge_of_le_average hCcolumns
  let B : Finset (Word k M) := columnFiber C y
  have hBdense : δ / 2 ≤ density B := by
    simpa [B] using hy
  obtain ⟨V, hV⟩ := hM B hBdense
  refine ⟨p.realize V.finLift y, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hxB : V x ∈ B := hV ⟨x, rfl⟩
  have hxAₚ : (liftWord (V x), y) ∈ Aₚ := by
    simpa [B, C] using hxB
  have hxAT : p.prepend (liftWord (V x), y) ∈ AT := by
    exact (UniformFibres.FrozenPrefix.mem_iterFibre p AT _).1 hxAₚ
  have hxA : e (p.prepend (liftWord (V x), y)) ∈ A := by
    simpa [AT, e] using hxAT
  simpa only [UniformFibres.FrozenPrefix.realize_apply,
    Combinatorics.Subspace.finLift_apply, e, Finset.mem_coe] using hxA

/-- A witnessing dimension for the restricted theorem works in every larger
ambient dimension, by restricting to a dense fibre and fixing the added
coordinates. -/
theorem FiniteRestrictedMDHJ.eventual {k m : ℕ} (h : FiniteRestrictedMDHJ k m) :
    EventualRestrictedMDHJ k m := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn A hA
  let : Nonempty (Fin (k + 1)) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  classical
  let e := wordFiberEquiv (k + 1) n₀ r
  let B : Finset (Word (k + 1) r × Word (k + 1) n₀) := A.map e.toEmbedding
  have hB : δ ≤ density B := by
    change δ ≤ density (A.map e.toEmbedding)
    rw [density_map_equiv]
    exact hA
  obtain ⟨z, hz⟩ := exists_fiber_density_ge B
  obtain ⟨U, hU⟩ := hn₀ (fiber B z) (hB.trans hz)
  refine ⟨extendSubspaceRight U z, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hmemB : (z, U (liftWord x)) ∈ B :=
    (mem_fiber B z (U (liftWord x))).1 (hU ⟨x, rfl⟩)
  have hmemA : e.symm (z, U (liftWord x)) ∈ A := by
    simpa [B] using hmemB
  have heq : e.symm (z, U (liftWord x)) =
      extendSubspaceRight U z (liftWord x) := by
    apply e.injective
    simp [e]
  simpa [heq] using hmemA

/-- Positive-dimension witness form, convenient when the ambient cube will
later be repeated in blocks. -/
theorem FiniteRestrictedMDHJ.positiveWitness {k m : ℕ}
    (h : FiniteRestrictedMDHJ k m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ A : Finset (Word (k + 1) n),
      δ ≤ density A → ContainsRestrictedSubspace m (A : Set (Word (k + 1) n)) := by
  obtain ⟨n₀, hn₀⟩ := h.eventual δ hδ
  refine ⟨max n₀ 1, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _), ?_⟩
  exact hn₀ _ (Nat.le_max_left _ _)

end Erdos171

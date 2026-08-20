/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file develops the lower-bound side of the Anderson--Keisler
construction.  The central topological input is a Cantor-manifold separator
scheme; everything from that input to the small-inductive-dimension lower
bound is proved here directly from Mathlib's recursive definition.
-/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.SmallInductiveDimension

open Set Topology TopologicalSpace

namespace Erdos909.ContinuumLower

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A nondegenerate continuum, in the sense used by Anderson--Keisler. -/
def IsNondegenerateContinuum (C : Set X) : Prop :=
  IsCompact C ∧ IsConnected C ∧ ¬ C.Subsingleton

/-- A set meets every nondegenerate continuum in the ambient space. -/
def MeetsEveryNondegenerateContinuum (K : Set X) : Prop :=
  ∀ C : Set X, IsNondegenerateContinuum C → (K ∩ C).Nonempty

theorem MeetsEveryNondegenerateContinuum.inter_nonempty
    {K C : Set X} (hK : MeetsEveryNondegenerateContinuum K)
    (hC : IsNondegenerateContinuum C) : (K ∩ C).Nonempty :=
  hK C hC

/-- The Mazurkiewicz avoidance conclusion at dimension level `n`: every
subspace of strict small inductive dimension `< n` misses a nondegenerate
continuum of the ambient space.  Engelking's Theorem 1.8.19 establishes this
for Euclidean `m`-space with `n = m - 1`. -/
def HasMazurkiewiczAvoidance (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ M : Set X, HasSmallInductiveDimensionLT M n →
    ∃ C : Set X, IsNondegenerateContinuum C ∧ Disjoint C M

/-- The two-prescribed-point form of Mazurkiewicz avoidance.  This is the
form used in the final Anderson--Keisler selector: the two points can be put
into the unary forbidden set before the continuum-hitting set is chosen. -/
def HasMazurkiewiczBetween (X : Type*) [TopologicalSpace X]
    (n : ℕ) (p q : X) : Prop :=
  ∀ M : Set X, HasSmallInductiveDimensionLT M n →
    p ∉ M → q ∉ M → p ≠ q →
      ∃ C : Set X, IsNondegenerateContinuum C ∧ Disjoint C M

/-- A continuum hitter omitting the prescribed endpoints cannot satisfy the
strict dimension bound occurring in `HasMazurkiewiczBetween`. -/
theorem not_hasSmallInductiveDimensionLT_of_hitter_of_mazurkiewiczBetween
    {K : Set X} {n : ℕ} {p q : X}
    (hK : MeetsEveryNondegenerateContinuum K)
    (hp : p ∉ K) (hq : q ∉ K) (hpq : p ≠ q)
    (hX : HasMazurkiewiczBetween X n p q) :
    ¬ HasSmallInductiveDimensionLT K n := by
  intro hdim
  obtain ⟨C, hC, hCK⟩ := hX K hdim hp hq hpq
  obtain ⟨x, hxK, hxC⟩ := hK C hC
  exact Set.disjoint_left.1 hCK hxC hxK

/-- Numerical lower bound from the prescribed-endpoint Mazurkiewicz form. -/
theorem smallInductiveDimension_ge_of_hitter_of_mazurkiewiczBetween
    {K : Set X} {n : ℕ} {p q : X}
    (hK : MeetsEveryNondegenerateContinuum K)
    (hp : p ∉ K) (hq : q ∉ K) (hpq : p ≠ q)
    (hX : HasMazurkiewiczBetween X n p q) :
    (n : WithBot ℕ∞) ≤ smallInductiveDimension K := by
  rw [← not_lt, smallInductiveDimension_lt_iff]
  exact not_hasSmallInductiveDimensionLT_of_hitter_of_mazurkiewiczBetween
    hK hp hq hpq hX

/-- Mazurkiewicz avoidance immediately contradicts continuum hitting. -/
theorem not_hasSmallInductiveDimensionLT_of_hitter_of_mazurkiewicz
    {K : Set X} {n : ℕ} (hK : MeetsEveryNondegenerateContinuum K)
    (hX : HasMazurkiewiczAvoidance X n) :
    ¬ HasSmallInductiveDimensionLT K n := by
  intro hdim
  obtain ⟨C, hC, hCK⟩ := hX K hdim
  obtain ⟨x, hxK, hxC⟩ := hK C hC
  exact Set.disjoint_left.1 hCK hxC hxK

/-- Numerical form of the direct Mazurkiewicz lower-bound route. -/
theorem smallInductiveDimension_ge_of_hitter_of_mazurkiewicz
    {K : Set X} {n : ℕ} (hK : MeetsEveryNondegenerateContinuum K)
    (hX : HasMazurkiewiczAvoidance X n) :
    (n : WithBot ℕ∞) ≤ smallInductiveDimension K := by
  rw [← not_lt, smallInductiveDimension_lt_iff]
  exact not_hasSmallInductiveDimensionLT_of_hitter_of_mazurkiewicz hK hX

/-! ### A dual form of the recursive small-inductive-dimension predicate -/

/-- `HasSmallInductiveDimensionGE X n` is the explicit obstruction dual to
`HasSmallInductiveDimensionLT X n`: at level zero the space is nonempty, and
at a successor every topological basis has an element whose frontier carries
an obstruction one level lower. -/
def HasSmallInductiveDimensionGE :
    ∀ (X : Type*) [TopologicalSpace X], ℕ → Prop
  | X, _, 0 => Nonempty X
  | X, _, Nat.succ n =>
      ∀ b : Set (Set X), IsTopologicalBasis b →
        ∃ U ∈ b, HasSmallInductiveDimensionGE (frontier U) n

@[simp]
theorem hasSmallInductiveDimensionGE_zero_iff :
    HasSmallInductiveDimensionGE X 0 ↔ Nonempty X := by
  rfl

theorem hasSmallInductiveDimensionGE_iff_not_lt (n : ℕ) :
    HasSmallInductiveDimensionGE X n ↔
      ¬ HasSmallInductiveDimensionLT X n := by
  classical
  induction n generalizing X with
  | zero =>
      rw [hasSmallInductiveDimensionGE_zero_iff,
        hasSmallInductiveDimensionLT_zero_iff]
      exact not_isEmpty_iff.symm
  | succ n ih =>
      constructor
      · intro hge hlt
        cases hlt with
        | succ _ b hb hfront =>
          obtain ⟨U, hUb, hUge⟩ := hge b hb
          exact (ih.mp hUge) (hfront U hUb)
      · intro hnot b hb
        by_contra hall
        apply hnot
        refine .succ n b hb ?_
        intro U hUb
        by_contra hnotlt
        apply hall
        exact ⟨U, hUb, ih.mpr hnotlt⟩

theorem hasSmallInductiveDimensionGE_iff_smallInductiveDimension_ge
    (n : ℕ) :
    HasSmallInductiveDimensionGE X n ↔
      (n : WithBot ℕ∞) ≤ smallInductiveDimension X := by
  rw [hasSmallInductiveDimensionGE_iff_not_lt, ← smallInductiveDimension_lt_iff,
    not_lt]

/-! ### Pullback and subspace monotonicity -/

theorem inducing_hasSmallInductiveDimensionLT {f : X → Y} (hf : IsInducing f)
    {n : ℕ} (h : HasSmallInductiveDimensionLT Y n) :
    HasSmallInductiveDimensionLT X n := by
  induction h generalizing X with
  | zero =>
      have := Function.isEmpty f
      exact HasSmallInductiveDimensionLT.zero
  | succ n b hb hfront ih =>
      refine .succ n _ (hb.isInducing hf) ?_
      rintro _ ⟨U, hUb, rfl⟩
      apply ih U hUb
      apply (hf.restrictPreimage (frontier U)).comp
      exact (IsEmbedding.inclusion
        (hf.continuous.frontier_preimage_subset U)).isInducing

/-- The prescribed-endpoint Mazurkiewicz property is invariant under
homeomorphism. -/
theorem hasMazurkiewiczBetween_of_homeomorph
    {n : ℕ} {p q : X} (e : X ≃ₜ Y)
    (hY : HasMazurkiewiczBetween Y n (e p) (e q)) :
    HasMazurkiewiczBetween X n p q := by
  intro M hM hp hq hpq
  let M' : Set Y := e '' M
  have hM' : HasSmallInductiveDimensionLT M' n := by
    exact inducing_hasSmallInductiveDimensionLT
      (e.isEmbedding.homeomorphImage M).symm.isInducing hM
  have hep : e p ∉ M' := by
    rintro ⟨x, hxM, hxp⟩
    have hxp' : x = p := e.injective hxp
    exact hp (hxp' ▸ hxM)
  have heq : e q ∉ M' := by
    rintro ⟨x, hxM, hxq⟩
    have hxq' : x = q := e.injective hxq
    exact hq (hxq' ▸ hxM)
  obtain ⟨C, ⟨hCc, hCconn, hCnt⟩, hCM⟩ :=
    hY M' hM' hep heq (fun h ↦ hpq (e.injective h))
  let D : Set X := e.symm '' C
  refine ⟨D, ⟨hCc.image e.symm.continuous,
    hCconn.image e.symm e.symm.continuous.continuousOn, ?_⟩, ?_⟩
  · intro hD
    apply hCnt
    intro x hx y hy
    apply e.symm.injective
    exact hD ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · rw [Set.disjoint_left]
    rintro x ⟨y, hyC, rfl⟩ hxM
    exact Set.disjoint_left.mp hCM hyC
      ⟨e.symm y, hxM, e.apply_symm_apply y⟩

theorem hasMazurkiewiczBetween_homeomorph_iff
    {n : ℕ} {p q : X} (e : X ≃ₜ Y) :
    HasMazurkiewiczBetween X n p q ↔
      HasMazurkiewiczBetween Y n (e p) (e q) := by
  constructor
  · intro h
    have h' : HasMazurkiewiczBetween X n
        (e.symm (e p)) (e.symm (e q)) := by simpa using h
    exact hasMazurkiewiczBetween_of_homeomorph e.symm h'
  · exact hasMazurkiewiczBetween_of_homeomorph e

theorem hasSmallInductiveDimensionGE_of_inducing
    {f : X → Y} (hf : IsInducing f) {n : ℕ}
    (h : HasSmallInductiveDimensionGE X n) :
    HasSmallInductiveDimensionGE Y n := by
  rw [hasSmallInductiveDimensionGE_iff_not_lt] at h ⊢
  exact fun hY ↦ h (inducing_hasSmallInductiveDimensionLT hf hY)

theorem hasSmallInductiveDimensionGE_of_subset
    {s t : Set X} (hst : s ⊆ t) {n : ℕ}
    (h : HasSmallInductiveDimensionGE s n) :
    HasSmallInductiveDimensionGE t n := by
  let f : s → t := fun x ↦ ⟨x, hst x.2⟩
  apply hasSmallInductiveDimensionGE_of_inducing (f := f) _ h
  exact (IsEmbedding.inclusion hst).isInducing

/-! ### The Cantor-manifold separator descent -/

/-- A formal interface for the uniform Cantor-manifold induction in the
Anderson--Keisler lower bound.

`CM r M` says that `M` is a rank-`r` Cantor manifold in the fixed ambient
space.  Rank-one members must be nondegenerate continua.  The second field is
the separator theorem in precisely the form used by the dimension recursion:
for every basis of `K ∩ M`, some basis frontier contains an inducing copy of
`K ∩ N` for a Cantor manifold one rank lower.

The quantifier over *every* basis and *every* higher-rank member is essential.
It is the formal counterpart of the uniform induction emphasized in the
published proof. -/
structure CantorSeparatorScheme (K : Set X)
    (CM : ℕ → Set X → Prop) : Prop where
  rank_one_continuum :
    ∀ {M : Set X}, CM 1 M → IsNondegenerateContinuum M
  basis_frontier_descend :
    ∀ (n : ℕ) {M : Set X}, CM (n + 2) M →
      ∀ (b : Set (Set (↑(K ∩ M : Set X)))), IsTopologicalBasis b →
        ∃ U ∈ b, ∃ N : Set X, CM (n + 1) N ∧
          ∃ f : (↑(K ∩ N : Set X)) → frontier U, IsInducing f

/-- The uniform Cantor-manifold induction.  A continuum-hitting set restricted
to a rank-`n+1` member carries an explicit obstruction to dimension `< n`.
This is the complete logical part of Anderson--Keisler's Lemma 3; the only
remaining geometric input is an instance of `CantorSeparatorScheme`. -/
theorem CantorSeparatorScheme.hasSmallInductiveDimensionGE
    {K : Set X} {CM : ℕ → Set X → Prop}
    (hS : CantorSeparatorScheme K CM)
    (hK : MeetsEveryNondegenerateContinuum K) :
    ∀ (n : ℕ) {M : Set X}, CM (n + 1) M →
      HasSmallInductiveDimensionGE (↑(K ∩ M : Set X)) n := by
  intro n
  induction n with
  | zero =>
      intro M hM
      exact Set.nonempty_coe_sort.mpr
        (hK M (hS.rank_one_continuum (by simpa using hM)))
  | succ n ih =>
      intro M hM b hb
      obtain ⟨U, hUb, N, hN, f, hf⟩ :=
        hS.basis_frontier_descend n (by simpa [Nat.add_assoc] using hM) b hb
      refine ⟨U, hUb, ?_⟩
      exact hasSmallInductiveDimensionGE_of_inducing hf
        (ih (by simpa [Nat.add_assoc] using hN))

/-- The numerical lower bound delivered by a top-rank member of a Cantor
separator scheme. -/
theorem smallInductiveDimension_ge_of_cantorSeparatorScheme
    {K : Set X} {CM : ℕ → Set X → Prop}
    (hS : CantorSeparatorScheme K CM)
    (hK : MeetsEveryNondegenerateContinuum K)
    (n : ℕ) {M : Set X} (hM : CM (n + 1) M) :
    (n : WithBot ℕ∞) ≤ smallInductiveDimension (↑(K ∩ M : Set X)) :=
  (hasSmallInductiveDimensionGE_iff_smallInductiveDimension_ge n).mp
    (hS.hasSmallInductiveDimensionGE hK n hM)

/-- Ambient-space form of the preceding theorem.  Taking `M = univ` turns
the restriction `K ∩ M` definitionally into the original subspace `K`. -/
theorem smallInductiveDimension_ge_of_cantorSeparatorScheme_univ
    {K : Set X} {CM : ℕ → Set X → Prop}
    (hS : CantorSeparatorScheme K CM)
    (hK : MeetsEveryNondegenerateContinuum K)
    (n : ℕ) (hM : CM (n + 1) Set.univ) :
    (n : WithBot ℕ∞) ≤ smallInductiveDimension K := by
  apply (hasSmallInductiveDimensionGE_iff_smallInductiveDimension_ge n).mp
  exact hasSmallInductiveDimensionGE_of_inducing
    (IsEmbedding.inclusion inter_subset_left).isInducing
    (hS.hasSmallInductiveDimensionGE hK n hM)

end Erdos909.ContinuumLower

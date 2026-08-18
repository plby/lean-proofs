/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5CubeGeometry
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Bilu's tube-cube lemma

This file formalizes the geometric object used in Proposition 5.4.  A
`TubeCubeWitness r C S b L` consists of an `r`-cube centred at `b`, with
all its vertices in `S`, together with an explicit subset of `S` contained
in the tube obtained by adding `L`; the subset contains at least a `1/C`
fraction of `S`.

The explicit finite subset is important: it lets the proof retain
cardinality when the induction reflects half of a lower-dimensional tube.
-/

namespace Erdos186.CFP.Bilu.Section5CubeLemma

open Set Module Submodule
open Section5TwoN Section5CubeGeometry

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

/-- A cube point with the indicated coordinates. -/
def cubePoint {r : ℕ} (center : V) (dirs : Fin r → V)
    (t : Fin r → ℝ) : V :=
  center + ∑ i, t i • dirs i

/-- The vertex belonging to a binary sign pattern. -/
def cubeVertex {r : ℕ} (center : V) (dirs : Fin r → V)
    (s : Fin r → Fin 2) : V :=
  cubePoint center dirs (signVector s)

/-- The tube `C + L` around a (possibly degenerate) closed affine cube. -/
def cubeTube {r : ℕ} (center : V) (dirs : Fin r → V)
    (L : Submodule ℝ V) : Set V :=
  {x | ∃ t : Fin r → ℝ,
    (∀ i, -(1 : ℝ) ≤ t i ∧ t i ≤ 1) ∧
    x - cubePoint center dirs t ∈ L}

/-- Symmetry about the geometric centre `center`. -/
def SymmetricAbout (S : Finset V) (center : V) : Prop :=
  ∀ x ∈ S, 2 • center - x ∈ S

/-- The division-free output of Proposition 5.4. -/
structure TubeCubeWitness (r proportionConstant : ℕ)
    (S : Finset V) (center : V) (L : Submodule ℝ V) where
  dirs : Fin r → V
  vertex_mem : ∀ s : Fin r → Fin 2, cubeVertex center dirs s ∈ S
  slice : Finset V
  slice_subset : slice ⊆ S
  slice_mem_tube : ∀ x ∈ slice, x ∈ cubeTube center dirs L
  card_le : S.card ≤ proportionConstant * slice.card

/-- A deliberately generous recursive constant for Proposition 5.4.
Only uniformity in `r` and the doubling constant is used later. -/
def tubeCubeConstant : ℕ → ℕ → ℕ
  | 0, _tau => 1
  | 1, _tau => 1
  | r + 2, tau => max 3 (9 * tau * tubeCubeConstant (r + 1) (9 * tau * tau))

@[simp] theorem tubeCubeConstant_zero (tau : ℕ) :
    tubeCubeConstant 0 tau = 1 := rfl

@[simp] theorem tubeCubeConstant_one (tau : ℕ) :
    tubeCubeConstant 1 tau = 1 := rfl

/-- Reflection about the centre is an involution. -/
theorem reflect_reflect (center x : V) :
    2 • center - (2 • center - x) = x := by
  module

/-- A symmetric finite set contains the reflection of each of its points. -/
theorem SymmetricAbout.reflect_mem {S : Finset V} {center x : V}
    (hS : SymmetricAbout S center) (hx : x ∈ S) :
    2 • center - x ∈ S := hS x hx

/-- A codimension-one subspace is the kernel of a real functional. -/
theorem exists_linearMap_ker_eq_of_codim_one (L : Submodule ℝ V)
    (hcodim : finrank ℝ L + 1 = finrank ℝ V) :
    ∃ f : V →ₗ[ℝ] ℝ, LinearMap.ker f = L := by
  have hquot : finrank ℝ (V ⧸ L) = 1 := by
    have h := L.finrank_quotient_add_finrank
    omega
  let e : (V ⧸ L) ≃ₗ[ℝ] ℝ :=
    LinearEquiv.ofFinrankEq (V ⧸ L) ℝ (by simpa using hquot)
  refine ⟨e.toLinearMap.comp L.mkQ, ?_⟩
  ext x
  simp [LinearMap.mem_ker, e.injective.eq_iff]

/-- In codimension one, choose a point whose functional distance from the
central affine hyperplane is maximal. -/
theorem exists_max_abs_apply (S : Finset V) (hS : S.Nonempty)
    (center : V) (f : V →ₗ[ℝ] ℝ) :
    ∃ a ∈ S, ∀ x ∈ S, |f (x - center)| ≤ |f (a - center)| := by
  let values : Finset ℝ := S.image fun x ↦ |f (x - center)|
  have hvalues : values.Nonempty := hS.image _
  let M : ℝ := values.max' hvalues
  have hMmem : M ∈ values := Finset.max'_mem values hvalues
  obtain ⟨a, ha, haM⟩ := Finset.mem_image.mp hMmem
  refine ⟨a, ha, ?_⟩
  intro x hx
  calc
    |f (x - center)| ≤ M :=
      Finset.le_max' values _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    _ = |f (a - center)| := haM.symm

/-- The base (`r = 1`) case of Proposition 5.4.  The whole symmetric set
lies in the tube around the segment joining a farthest point to its
reflection. -/
theorem exists_tubeCubeWitness_one
    (S : Finset V) (hS : S.Nonempty) (center : V)
    (hsym : SymmetricAbout S center) (L : Submodule ℝ V)
    (hcodim : finrank ℝ L + 1 = finrank ℝ V) :
    Nonempty (TubeCubeWitness 1 1 S center L) := by
  obtain ⟨f, hfker⟩ := exists_linearMap_ker_eq_of_codim_one L hcodim
  obtain ⟨a, haS, hmax⟩ := exists_max_abs_apply S hS center f
  let dirs : Fin 1 → V := fun _ ↦ a - center
  have haReflection : 2 • center - a ∈ S := hsym a haS
  have hvertex : ∀ s : Fin 1 → Fin 2, cubeVertex center dirs s ∈ S := by
    intro s
    have hs : s 0 = 0 ∨ s 0 = 1 := by omega
    rcases hs with hs | hs
    · have hsign : signVector s = fun _ : Fin 1 ↦ -(1 : ℝ) := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [signVector, hs]
      rw [cubeVertex, cubePoint, hsign]
      simp only [Fin.sum_univ_one, dirs]
      convert haReflection using 1 <;> module
    · have hsign : signVector s = fun _ : Fin 1 ↦ (1 : ℝ) := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [signVector, hs]
      rw [cubeVertex, cubePoint, hsign]
      simp only [Fin.sum_univ_one, dirs, one_smul, add_sub_cancel]
      exact haS
  refine ⟨{
    dirs := dirs
    vertex_mem := hvertex
    slice := S
    slice_subset := Finset.Subset.rfl
    slice_mem_tube := ?_
    card_le := by simp }⟩
  intro x hx
  by_cases ha0 : f (a - center) = 0
  · refine ⟨0, by simp, ?_⟩
    have hxabs := hmax x hx
    rw [ha0, abs_zero] at hxabs
    have hxzero : f (x - center) = 0 :=
      abs_eq_zero.mp (le_antisymm hxabs (abs_nonneg _))
    rw [← hfker, LinearMap.mem_ker]
    simpa [cubePoint] using hxzero
  · let t : Fin 1 → ℝ := fun _ ↦ f (x - center) / f (a - center)
    refine ⟨t, ?_, ?_⟩
    · intro i
      have habs : |t i| ≤ 1 := by
        rw [show t i = f (x - center) / f (a - center) from rfl,
          abs_div, div_le_one (abs_pos.mpr ha0)]
        exact hmax x hx
      exact (abs_le.mp habs)
    · rw [← hfker, LinearMap.mem_ker]
      rw [cubePoint]
      simp only [Fin.sum_univ_one, dirs, map_sub, map_add, map_smul]
      rw [show t 0 = f (x - center) / f (a - center) from rfl,
        smul_eq_mul, ← map_sub, div_mul_cancel₀ _ ha0, map_sub]
      ring

/-! ## A generic separating hyperplane -/

/-- Points of `S` lying in the central affine translate of `L`. -/
def centralPart (S : Finset V) (center : V) (L : Submodule ℝ V) : Finset V :=
  S.filter fun x ↦ x - center ∈ L

/-- Points on the positive side of a functional through `center`. -/
def positivePart (S : Finset V) (center : V) (f : V →ₗ[ℝ] ℝ) : Finset V :=
  S.filter fun x ↦ 0 < f (x - center)

/-- Points on the negative side of a functional through `center`. -/
def negativePart (S : Finset V) (center : V) (f : V →ₗ[ℝ] ℝ) : Finset V :=
  S.filter fun x ↦ f (x - center) < 0

@[simp] theorem mem_centralPart {S : Finset V} {center : V}
    {L : Submodule ℝ V} {x : V} :
    x ∈ centralPart S center L ↔ x ∈ S ∧ x - center ∈ L := by
  simp [centralPart]

@[simp] theorem mem_positivePart {S : Finset V} {center : V}
    {f : V →ₗ[ℝ] ℝ} {x : V} :
    x ∈ positivePart S center f ↔ x ∈ S ∧ 0 < f (x - center) := by
  simp [positivePart]

@[simp] theorem mem_negativePart {S : Finset V} {center : V}
    {f : V →ₗ[ℝ] ℝ} {x : V} :
    x ∈ negativePart S center f ↔ x ∈ S ∧ f (x - center) < 0 := by
  simp [negativePart]

/-- A finite collection of vectors outside `L` admits a quotient
functional which is nonzero on every one of them.  Consequently its pullback
has kernel containing `L` and no extra point of the prescribed affine
finite set. -/
theorem exists_separating_functional (S : Finset V) (center : V)
    (L : Submodule ℝ V)
    (houtside : ∃ x ∈ S, x - center ∉ L) :
    ∃ f : V →ₗ[ℝ] ℝ,
      L ≤ LinearMap.ker f ∧ f ≠ 0 ∧
      ∀ x ∈ S, f (x - center) = 0 ↔ x - center ∈ L := by
  let outside : Finset V := S.filter fun x ↦ x - center ∉ L
  have houtsideNonempty : outside.Nonempty := by
    obtain ⟨x, hxS, hxL⟩ := houtside
    exact ⟨x, by simp [outside, hxS, hxL]⟩
  let qv : {x // x ∈ outside} → (V ⧸ L) :=
    fun x ↦ L.mkQ ((x : V) - center)
  have hqv : ∀ x, qv x ≠ 0 := by
    intro x hzero
    have hxnot : (x : V) - center ∉ L :=
      (Finset.mem_filter.mp x.property).2
    apply hxnot
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [qv] using hzero
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℝ) (M := V ⧸ L) qv hqv
  let f : V →ₗ[ℝ] ℝ := g.comp L.mkQ
  have hfL : L ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    change g (L.mkQ x) = 0
    have hqx : L.mkQ x = 0 := by
      change x ∈ LinearMap.ker L.mkQ
      rw [Submodule.ker_mkQ]
      exact hx
    rw [hqx, map_zero]
  have hfne : f ≠ 0 := by
    obtain ⟨x, hx⟩ := houtsideNonempty
    let xo : {x // x ∈ outside} := ⟨x, hx⟩
    intro hfzero
    have happly := LinearMap.congr_fun hfzero ((xo : V) - center)
    exact hg xo (by simpa [f, qv] using happly)
  refine ⟨f, hfL, hfne, ?_⟩
  intro x hxS
  constructor
  · intro hzero
    by_contra hxnot
    let xo : {x // x ∈ outside} :=
      ⟨x, by simp [outside, hxS, hxnot]⟩
    exact hg xo (by simpa [f, qv] using hzero)
  · intro hxL
    exact LinearMap.mem_ker.mp (hfL hxL)

/-- Reflection switches the positive and negative half-parts. -/
theorem image_reflect_positivePart (S : Finset V) (center : V)
    (f : V →ₗ[ℝ] ℝ) (hsym : SymmetricAbout S center) :
    (positivePart S center f).image (fun x ↦ 2 • center - x) =
      negativePart S center f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    have hx' := mem_positivePart.mp hx
    subst y
    apply mem_negativePart.mpr
    refine ⟨hsym x hx'.1, ?_⟩
    rw [show 2 • center - x - center = -(x - center) by module,
      map_neg]
    linarith
  · intro hy
    have hy' := mem_negativePart.mp hy
    refine Finset.mem_image.mpr ⟨2 • center - y, ?_, ?_⟩
    · apply mem_positivePart.mpr
      refine ⟨hsym y hy'.1, ?_⟩
      rw [show 2 • center - y - center = -(y - center) by module,
        map_neg]
      linarith
    · exact reflect_reflect center y

/-- Symmetry makes the two open half-parts equinumerous. -/
theorem card_positivePart_eq_card_negativePart (S : Finset V) (center : V)
    (f : V →ₗ[ℝ] ℝ) (hsym : SymmetricAbout S center) :
    (positivePart S center f).card = (negativePart S center f).card := by
  rw [← image_reflect_positivePart S center f hsym]
  symm
  apply Finset.card_image_of_injOn
  intro x _ y _ hxy
  have h := congrArg (fun z ↦ 2 • center - z) hxy
  simpa [reflect_reflect] using h

/-- If a separator has no extra zeros on `S`, the central part and the two
open half-parts form a disjoint partition. -/
theorem card_central_add_positive_add_negative (S : Finset V) (center : V)
    (L : Submodule ℝ V) (f : V →ₗ[ℝ] ℝ)
    (hexact : ∀ x ∈ S, f (x - center) = 0 ↔ x - center ∈ L) :
    (centralPart S center L).card + (positivePart S center f).card +
      (negativePart S center f).card = S.card := by
  let C := centralPart S center L
  let P := positivePart S center f
  let N := negativePart S center f
  have hCP : Disjoint C P := by
    rw [Finset.disjoint_left]
    intro x hxC hxP
    have hxC' := mem_centralPart.mp hxC
    have hxP' := mem_positivePart.mp hxP
    have hz : f (x - center) = 0 := (hexact x hxC'.1).2 hxC'.2
    linarith
  have hCN : Disjoint C N := by
    rw [Finset.disjoint_left]
    intro x hxC hxN
    have hxC' := mem_centralPart.mp hxC
    have hxN' := mem_negativePart.mp hxN
    have hz : f (x - center) = 0 := (hexact x hxC'.1).2 hxC'.2
    linarith
  have hPN : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    have hxP' := mem_positivePart.mp hxP
    have hxN' := mem_negativePart.mp hxN
    linarith
  have hpartition : (C ∪ P) ∪ N = S := by
    ext x
    simp only [Finset.mem_union, mem_centralPart, mem_positivePart,
      mem_negativePart, C, P, N]
    constructor
    · aesop
    · intro hx
      by_cases hz : f (x - center) = 0
      · exact Or.inl (Or.inl ⟨hx, (hexact x hx).1 hz⟩)
      · by_cases hp : 0 < f (x - center)
        · exact Or.inl (Or.inr ⟨hx, hp⟩)
        · exact Or.inr ⟨hx, lt_of_le_of_ne (not_lt.mp hp) hz⟩
  change C.card + P.card + N.card = S.card
  calc
    C.card + P.card + N.card = ((C ∪ P) ∪ N).card := by
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_union_left.mpr ⟨hCN, hPN⟩),
        Finset.card_union_of_disjoint hCP]
    _ = S.card := congrArg Finset.card hpartition

/-- If fewer than one third of a symmetric set lies in the central plane,
then each open half contains more than one third of the set.  The natural
number form avoids division. -/
theorem card_le_three_mul_card_positivePart (S : Finset V) (center : V)
    (L : Submodule ℝ V) (f : V →ₗ[ℝ] ℝ)
    (hsym : SymmetricAbout S center)
    (hexact : ∀ x ∈ S, f (x - center) = 0 ↔ x - center ∈ L)
    (hcentral : 3 * (centralPart S center L).card < S.card) :
    S.card ≤ 3 * (positivePart S center f).card := by
  have hpartition := card_central_add_positive_add_negative
    S center L f hexact
  have heq := card_positivePart_eq_card_negativePart S center f hsym
  omega

/-! ## The large central-slice branch -/

/-- Enlarge the harmless denominator in a tube-cube witness. -/
def TubeCubeWitness.mono_constant {r C D : ℕ} {S : Finset V}
    {center : V} {L : Submodule ℝ V}
    (W : TubeCubeWitness r C S center L) (hCD : C ≤ D) :
    TubeCubeWitness r D S center L where
  dirs := W.dirs
  vertex_mem := W.vertex_mem
  slice := W.slice
  slice_subset := W.slice_subset
  slice_mem_tube := W.slice_mem_tube
  card_le := W.card_le.trans (Nat.mul_le_mul_right W.slice.card hCD)

/-- If the central affine copy of `L` already contains one third of `S`,
a degenerate cube supported in `L` proves Proposition 5.4.  Degenerate
cubes are explicitly allowed in Bilu's statement. -/
theorem exists_tubeCubeWitness_of_large_central {r : ℕ} (hr : 0 < r)
    (S : Finset V) (hS : S.Nonempty) (center : V)
    (hsym : SymmetricAbout S center) (L : Submodule ℝ V)
    (hcentral : S.card ≤ 3 * (centralPart S center L).card) :
    Nonempty (TubeCubeWitness r 3 S center L) := by
  have hcentralNonempty : (centralPart S center L).Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty.mp hnone] at hcentral
    simp at hcentral
    exact hS.ne_empty hcentral
  obtain ⟨a, ha⟩ := hcentralNonempty
  have ha' := mem_centralPart.mp ha
  let i₀ : Fin r := ⟨0, hr⟩
  let dirs : Fin r → V := fun i ↦ if i = i₀ then a - center else 0
  have hsum (s : Fin r → Fin 2) :
      ∑ i, signVector s i • dirs i = signVector s i₀ • (a - center) := by
    classical
    simp [dirs]
  have hvertex : ∀ s : Fin r → Fin 2, cubeVertex center dirs s ∈ S := by
    intro s
    rw [cubeVertex, cubePoint, hsum]
    by_cases hs : s i₀ = 0
    · rw [show signVector s i₀ = -1 by simp [signVector, hs]]
      convert hsym a ha'.1 using 1 <;> module
    · rw [show signVector s i₀ = 1 by
        simp [signVector, hs]]
      simpa using ha'.1
  refine ⟨{
    dirs := dirs
    vertex_mem := hvertex
    slice := centralPart S center L
    slice_subset := fun _ hx ↦ (mem_centralPart.mp hx).1
    slice_mem_tube := ?_
    card_le := hcentral }⟩
  intro x hx
  refine ⟨0, by simp, ?_⟩
  have hx' := mem_centralPart.mp hx
  simpa [cubePoint] using hx'.2

/-- In every genuinely inductive rank, the recursive constant dominates
the central-slice denominator. -/
theorem three_le_tubeCubeConstant_add_two (r tau : ℕ) :
    3 ≤ tubeCubeConstant (r + 2) tau := by
  simp [tubeCubeConstant]

/-! ## The positive-half symmetric subset -/

/-- Pair sumsets are monotone. -/
theorem pairSumset_mono {A B : Finset V} (hAB : A ⊆ B) :
    Section7FreimanMap.pairSumset A ⊆
      Section7FreimanMap.pairSumset B := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    Section7FreimanMap.mem_pairSumset A z |>.mp hz
  exact Section7FreimanMap.mem_pairSumset B _ |>.mpr
    ⟨x, hAB hx, y, hAB hy, rfl⟩

/-- In the non-central branch, Proposition 5.3 supplies a large symmetric
subset wholly contained in the positive half-space.  This is precisely the
quantitative input used at the next inductive rank in Proposition 5.4. -/
theorem exists_positive_symmetric_subset
    (S : Finset V) (hS : S.Nonempty) (center : V)
    (f : V →ₗ[ℝ] ℝ) (tau : ℕ)
    (hpositive : S.card ≤ 3 * (positivePart S center f).card)
    (hdouble : (Section7FreimanMap.pairSumset S).card ≤ tau * S.card) :
    ∃ b₁ : V, ∃ T : Finset V,
      T.Nonempty ∧ T ⊆ positivePart S center f ∧
      SymmetricAbout T b₁ ∧
      S.card ≤ 9 * tau * T.card ∧
      (Section7FreimanMap.pairSumset T).card ≤
        (9 * tau * tau) * T.card ∧
      0 < f (b₁ - center) := by
  let P := positivePart S center f
  change S.card ≤ 3 * P.card at hpositive
  have hP : P.Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty.mp hnone] at hpositive
    simp at hpositive
    exact hS.ne_empty hpositive
  have hPS : P ⊆ S := fun _ hx ↦ (mem_positivePart.mp hx).1
  have hPdouble :
      (Section7FreimanMap.pairSumset P).card ≤ (3 * tau) * P.card := by
    calc
      (Section7FreimanMap.pairSumset P).card ≤
          (Section7FreimanMap.pairSumset S).card :=
        Finset.card_le_card (pairSumset_mono hPS)
      _ ≤ tau * S.card := hdouble
      _ ≤ tau * (3 * P.card) := Nat.mul_le_mul_left tau hpositive
      _ = (3 * tau) * P.card := by ring
  obtain ⟨sumCenter, T, _hTeq, hTP, hreflect, hPT⟩ :=
    exists_large_symmetricFiber P hP (3 * tau) hPdouble
  let b₁ : V := (1 / 2 : ℝ) • sumCenter
  have hT : T.Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty.mp hnone] at hPT
    simp at hPT
    exact hP.ne_empty hPT
  have hTS : T ⊆ S := fun _ hx ↦ hPS (hTP hx)
  have hsym : SymmetricAbout T b₁ := by
    intro x hx
    convert hreflect x hx using 1
    dsimp [b₁]
    module
  have hST : S.card ≤ 9 * tau * T.card := by
    calc
      S.card ≤ 3 * P.card := hpositive
      _ ≤ 3 * ((3 * tau) * T.card) := Nat.mul_le_mul_left 3 hPT
      _ = 9 * tau * T.card := by ring
  have hTdouble :
      (Section7FreimanMap.pairSumset T).card ≤
        (9 * tau * tau) * T.card := by
    calc
      (Section7FreimanMap.pairSumset T).card ≤
          (Section7FreimanMap.pairSumset S).card :=
        Finset.card_le_card (pairSumset_mono hTS)
      _ ≤ tau * S.card := hdouble
      _ ≤ tau * (9 * tau * T.card) := Nat.mul_le_mul_left tau hST
      _ = (9 * tau * tau) * T.card := by ring
  obtain ⟨x, hxT⟩ := hT
  have hxP := mem_positivePart.mp (hTP hxT)
  have hrefT : sumCenter - x ∈ T := hreflect x hxT
  have hrefP := mem_positivePart.mp (hTP hrefT)
  have hbpos : 0 < f (b₁ - center) := by
    have hidentity :
        f (x - center) + f (sumCenter - x - center) =
          2 * f (b₁ - center) := by
      dsimp [b₁]
      simp only [map_sub, map_smul]
      ring
    nlinarith [hxP.2, hrefP.2]
  exact ⟨b₁, T, ⟨x, hxT⟩, hTP, hsym, hST, hTdouble, hbpos⟩

/-- Enlarging `L` by the new positive direction lowers its codimension by
one, the dimension transition used in the induction. -/
theorem finrank_sup_span_add_succ_of_codim
    {r : ℕ} (L : Submodule ℝ V) (a : V) (ha : a ∉ L)
    (hcodim : finrank ℝ L + (r + 1) = finrank ℝ V) :
    finrank ℝ (L ⊔ Submodule.span ℝ {a} : Submodule ℝ V) + r =
      finrank ℝ V := by
  rw [Submodule.finrank_sup_span_singleton ha]
  omega

/-! ## Folding a lower-dimensional tube -/

/-- A linear functional which is positive at every cube vertex is positive
throughout the closed cube.  This is the elementary convexity estimate
used in the folding step of Proposition 5.4. -/
theorem linear_positive_on_cubePoint_of_vertices {r : ℕ}
    (f : V →ₗ[ℝ] ℝ) (origin center : V) (dirs : Fin r → V)
    (hvertices : ∀ s : Fin r → Fin 2,
      0 < f (cubeVertex center dirs s - origin))
    (t : Fin r → ℝ) (ht : ∀ i, -(1 : ℝ) ≤ t i ∧ t i ≤ 1) :
    0 < f (cubePoint center dirs t - origin) := by
  let c : Fin r → ℝ := fun i ↦ f (dirs i)
  let s : Fin r → Fin 2 := fun i ↦ if 0 ≤ c i then 0 else 1
  have hsign (i : Fin r) : signVector s i * c i = -|c i| := by
    by_cases hi : 0 ≤ c i
    · have hs : s i = 0 := by simp [s, hi]
      rw [signVector, if_pos hs, abs_of_nonneg hi]
      ring
    · have hc : c i < 0 := lt_of_not_ge hi
      have hs : s i = 1 := by simp [s, hi]
      rw [signVector, if_neg (by omega : s i ≠ 0), abs_of_neg hc]
      ring
  have hvertex := hvertices s
  have hvertexFormula :
      f (cubeVertex center dirs s - origin) =
        f (center - origin) + ∑ i, signVector s i * c i := by
    simp only [cubeVertex, cubePoint, map_sub, map_add, map_sum,
      map_smul, smul_eq_mul, c]
    ring
  rw [hvertexFormula] at hvertex
  simp_rw [hsign] at hvertex
  have hterm (i : Fin r) : -|c i| ≤ t i * c i := by
    have hti := ht i
    by_cases hi : 0 ≤ c i
    · rw [abs_of_nonneg hi]
      nlinarith
    · have hc : c i < 0 := lt_of_not_ge hi
      rw [abs_of_neg hc]
      nlinarith
  have hsum : ∑ i, -|c i| ≤ ∑ i, t i * c i :=
    Finset.sum_le_sum fun i _ ↦ hterm i
  have hpointFormula :
      f (cubePoint center dirs t - origin) =
        f (center - origin) + ∑ i, t i * c i := by
    simp only [cubePoint, map_sub, map_add, map_sum, map_smul,
      smul_eq_mul, c]
    ring
  rw [hpointFormula]
  linarith

/-- The closed cube is centrally symmetric. -/
theorem cubePoint_reflection {r : ℕ} (center : V) (dirs : Fin r → V)
    (t : Fin r → ℝ) :
    cubePoint center dirs (-t) = 2 • center - cubePoint center dirs t := by
  simp only [cubePoint, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  module

/-- A vector in `L + span a` can be reduced to `L` by subtracting the
coefficient detected by a functional which vanishes on `L`. -/
theorem sub_div_apply_smul_mem_of_mem_sup_span
    (f : V →ₗ[ℝ] ℝ) (L : Submodule ℝ V) (hfL : L ≤ LinearMap.ker f)
    (a d : V) (hfa : f a ≠ 0)
    (hd : d ∈ (L ⊔ Submodule.span ℝ {a} : Submodule ℝ V)) :
    d - (f d / f a) • a ∈ L := by
  obtain ⟨l, hl, z, hz, hld⟩ := Submodule.mem_sup.mp hd
  obtain ⟨q, rfl⟩ := (Submodule.mem_span_singleton.mp hz)
  rw [← hld]
  have hfl : f l = 0 := LinearMap.mem_ker.mp (hfL hl)
  simp only [map_add, map_smul, hfl, zero_add, smul_eq_mul]
  rw [mul_div_cancel_right₀ q hfa]
  simpa using hl

/-- Flip all binary signs. -/
def flipPattern {r : ℕ} (s : Fin r → Fin 2) : Fin r → Fin 2 :=
  fun i ↦ if s i = 0 then 1 else 0

@[simp] theorem signVector_flipPattern {r : ℕ} (s : Fin r → Fin 2) (i : Fin r) :
    signVector (flipPattern s) i = -signVector s i := by
  by_cases hi : s i = 0
  · simp [flipPattern, signVector, hi]
  · have hs1 : s i = 1 := Fin.eq_one_of_ne_zero _ hi
    simp [flipPattern, signVector, hi, hs1]

/-- Add a new leading cube direction. -/
def extendDirs {r : ℕ} (a : V) (dirs : Fin r → V) : Fin (r + 1) → V :=
  Fin.cons a dirs

theorem cubePoint_extend {r : ℕ} (center a : V) (dirs : Fin r → V)
    (t : Fin (r + 1) → ℝ) :
    cubePoint center (extendDirs a dirs) t =
      center + t 0 • a + ∑ i, t i.succ • dirs i := by
  simp [cubePoint, extendDirs, Fin.sum_univ_succ, add_assoc]

/-- A positive-leading vertex of the extended cube is a vertex of the
lower cube. -/
theorem cubeVertex_extend_zero {r : ℕ} (center b₁ a : V)
    (hb₁ : b₁ = center + a) (dirs : Fin r → V)
    (s : Fin (r + 1) → Fin 2) (hs : s 0 ≠ 0) :
    cubeVertex center (extendDirs a dirs) s =
      cubeVertex b₁ dirs (Fin.tail s) := by
  rw [cubeVertex, cubePoint_extend, cubeVertex, cubePoint]
  have hs0 : signVector s 0 = 1 := by simp [signVector, hs]
  rw [hs0, one_smul, hb₁]
  congr 1

/-- A negative-leading vertex of the extended cube is the reflection,
about the old centre, of the opposite lower-cube vertex. -/
theorem cubeVertex_extend_zero_reflection {r : ℕ} (center b₁ a : V)
    (hb₁ : b₁ = center + a) (dirs : Fin r → V)
    (s : Fin (r + 1) → Fin 2) (hs : s 0 = 0) :
    cubeVertex center (extendDirs a dirs) s =
      2 • center - cubeVertex b₁ dirs (flipPattern (Fin.tail s)) := by
  rw [cubeVertex, cubePoint_extend, cubeVertex, cubePoint]
  have hs0 : signVector s 0 = -1 := by simp [signVector, hs]
  have hsum :
      ∑ i, signVector (flipPattern (Fin.tail s)) i • dirs i =
        -(∑ i, signVector (Fin.tail s) i • dirs i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [signVector_flipPattern, neg_smul]
  rw [hs0, neg_one_smul, hsum, hb₁]
  abel

/-- The source's folding construction: a lower-dimensional tube inside a
positive symmetric subset is folded across the two centres into a tube one
dimension higher.  The fold is injective because its two branches lie in
opposite open half-spaces. -/
theorem exists_folded_tubeCubeWitness {r C D : ℕ}
    (S : Finset V) (center : V) (hsymS : SymmetricAbout S center)
    (f : V →ₗ[ℝ] ℝ) (L : Submodule ℝ V)
    (hfL : L ≤ LinearMap.ker f)
    (b₁ a : V) (hb₁ : b₁ = center + a) (hfa : 0 < f a)
    (T : Finset V) (hTpositive : T ⊆ positivePart S center f)
    (hsymT : SymmetricAbout T b₁) (hST : S.card ≤ D * T.card)
    (W : TubeCubeWitness r C T b₁
      (L ⊔ Submodule.span ℝ {a} : Submodule ℝ V)) :
    Nonempty (TubeCubeWitness (r + 1) (D * C) S center L) := by
  let coeff : V → (Fin r → ℝ) := fun x ↦
    if hx : x ∈ W.slice then
      (W.slice_mem_tube x hx).choose
    else 0
  have hcoeffBounds (x : V) (hx : x ∈ W.slice) :
      ∀ i, -(1 : ℝ) ≤ coeff x i ∧ coeff x i ≤ 1 := by
    have hs := (W.slice_mem_tube x hx).choose_spec.1
    simpa [coeff, hx] using hs
  have hcoeffMem (x : V) (hx : x ∈ W.slice) :
      x - cubePoint b₁ W.dirs (coeff x) ∈
        (L ⊔ Submodule.span ℝ {a} : Submodule ℝ V) := by
    have hs := (W.slice_mem_tube x hx).choose_spec.2
    simpa [coeff, hx] using hs
  let q : V → ℝ := fun x ↦
    f (x - cubePoint b₁ W.dirs (coeff x)) / f a
  have hfa0 : f a ≠ 0 := ne_of_gt hfa
  have hqBounds (x : V) (hx : x ∈ W.slice) :
      -(2 : ℝ) < q x ∧ q x < 2 := by
    have hxT : x ∈ T := W.slice_subset hx
    have hxPositive := mem_positivePart.mp (hTpositive hxT)
    have hxReflectT : 2 • b₁ - x ∈ T := hsymT x hxT
    have hxReflectPositive := mem_positivePart.mp (hTpositive hxReflectT)
    have hvertexPositive : ∀ s : Fin r → Fin 2,
        0 < f (cubeVertex b₁ W.dirs s - center) := by
      intro s
      exact (mem_positivePart.mp (hTpositive (W.vertex_mem s))).2
    have hpPositive :
        0 < f (cubePoint b₁ W.dirs (coeff x) - center) :=
      linear_positive_on_cubePoint_of_vertices f center b₁ W.dirs
        hvertexPositive (coeff x) (hcoeffBounds x hx)
    have hnegBounds : ∀ i, -(1 : ℝ) ≤ (-coeff x) i ∧ (-coeff x) i ≤ 1 := by
      intro i
      have hi := hcoeffBounds x hx i
      constructor <;> simp only [Pi.neg_apply] <;> linarith
    have hpReflectPositive :
        0 < f (cubePoint b₁ W.dirs (-coeff x) - center) :=
      linear_positive_on_cubePoint_of_vertices f center b₁ W.dirs
        hvertexPositive (-coeff x) hnegBounds
    have hcenterEval : f (b₁ - center) = f a := by
      rw [hb₁]
      simp
    have hxSum :
        f (x - center) + f ((2 • b₁ - x) - center) = 2 * f a := by
      rw [← hcenterEval]
      simp only [map_sub, map_nsmul]
      ring
    have hpSum :
        f (cubePoint b₁ W.dirs (coeff x) - center) +
          f (cubePoint b₁ W.dirs (-coeff x) - center) = 2 * f a := by
      rw [cubePoint_reflection]
      rw [← hcenterEval]
      simp only [map_sub, map_nsmul]
      ring
    have hqMul :
        q x * f a = f (x - center) -
          f (cubePoint b₁ W.dirs (coeff x) - center) := by
      dsimp [q]
      rw [div_mul_cancel₀ _ hfa0]
      simp only [map_sub]
      ring
    constructor <;> nlinarith [hxPositive.2, hxReflectPositive.2,
      hpPositive, hpReflectPositive]
  let fold : V → V := fun x ↦
    if q x < 0 then x else x - 2 • a
  have hfoldSubset : ∀ x ∈ W.slice, fold x ∈ S := by
    intro x hx
    have hxT : x ∈ T := W.slice_subset hx
    by_cases hqx : q x < 0
    · simp only [fold, if_pos hqx]
      exact (mem_positivePart.mp (hTpositive hxT)).1
    · simp only [fold, if_neg hqx]
      have hrefT : 2 • b₁ - x ∈ T := hsymT x hxT
      have hrefS : 2 • b₁ - x ∈ S :=
        (mem_positivePart.mp (hTpositive hrefT)).1
      have hreflected := hsymS (2 • b₁ - x) hrefS
      convert hreflected using 1
      rw [hb₁]
      module
  have hfoldTube : ∀ x ∈ W.slice,
      fold x ∈ cubeTube center (extendDirs a W.dirs) L := by
    intro x hx
    have hresidual :
        (x - cubePoint b₁ W.dirs (coeff x)) - q x • a ∈ L := by
      exact sub_div_apply_smul_mem_of_mem_sup_span f L hfL a
        (x - cubePoint b₁ W.dirs (coeff x)) hfa0 (hcoeffMem x hx)
    have hqb := hqBounds x hx
    by_cases hqx : q x < 0
    · let extCoeff : Fin (r + 1) → ℝ := Fin.cons (1 + q x) (coeff x)
      refine ⟨extCoeff, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change -(1 : ℝ) ≤ 1 + q x ∧ 1 + q x ≤ 1
          constructor <;> linarith
        · simpa [extCoeff] using hcoeffBounds x hx j
      · simp only [fold, if_pos hqx]
        have heq :
            x - cubePoint center (extendDirs a W.dirs) extCoeff =
              (x - cubePoint b₁ W.dirs (coeff x)) - q x • a := by
          rw [cubePoint_extend]
          simp only [extCoeff, Fin.cons_zero, Fin.cons_succ]
          rw [cubePoint]
          have hbEq :
              b₁ + ∑ i, coeff x i • W.dirs i =
                center + a + ∑ i, coeff x i • W.dirs i := by
            exact congrArg (fun z ↦ z + ∑ i, coeff x i • W.dirs i) hb₁
          rw [hbEq]
          module
        rw [heq]
        exact hresidual
    · let extCoeff : Fin (r + 1) → ℝ := Fin.cons (q x - 1) (coeff x)
      refine ⟨extCoeff, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change -(1 : ℝ) ≤ q x - 1 ∧ q x - 1 ≤ 1
          constructor <;> linarith [not_lt.mp hqx]
        · simpa [extCoeff] using hcoeffBounds x hx j
      · simp only [fold, if_neg hqx]
        have heq :
            (x - 2 • a) - cubePoint center (extendDirs a W.dirs) extCoeff =
              (x - cubePoint b₁ W.dirs (coeff x)) - q x • a := by
          rw [cubePoint_extend]
          simp only [extCoeff, Fin.cons_zero, Fin.cons_succ]
          rw [cubePoint]
          have hbEq :
              b₁ + ∑ i, coeff x i • W.dirs i =
                center + a + ∑ i, coeff x i • W.dirs i := by
            exact congrArg (fun z ↦ z + ∑ i, coeff x i • W.dirs i) hb₁
          rw [hbEq]
          module
        rw [heq]
        exact hresidual
  have hfoldInj : Set.InjOn fold (W.slice : Set V) := by
    intro x hx y hy hxy
    by_cases hxq : q x < 0
    · by_cases hyq : q y < 0
      · simpa [fold, hxq, hyq] using hxy
      · have hxPositive := mem_positivePart.mp
          (hTpositive (W.slice_subset hx))
        have hyReflectT : 2 • b₁ - y ∈ T :=
          hsymT y (W.slice_subset hy)
        have hyReflectPositive := mem_positivePart.mp (hTpositive hyReflectT)
        have hfoldx : fold x = x := by simp [fold, hxq]
        have hfoldy : fold y = 2 • center - (2 • b₁ - y) := by
          simp only [fold, if_neg hyq]
          rw [hb₁]
          module
        have hyNegative :
            f ((2 • center - (2 • b₁ - y)) - center) < 0 := by
          rw [show (2 • center - (2 • b₁ - y)) - center =
              -((2 • b₁ - y) - center) by module,
            map_neg]
          linarith [hyReflectPositive.2]
        have hfEq := congrArg (fun z ↦ f (z - center)) hxy
        rw [hfoldx, hfoldy] at hfEq
        linarith [hxPositive.2, hyNegative]
    · by_cases hyq : q y < 0
      · have hyPositive := mem_positivePart.mp
          (hTpositive (W.slice_subset hy))
        have hxReflectT : 2 • b₁ - x ∈ T :=
          hsymT x (W.slice_subset hx)
        have hxReflectPositive := mem_positivePart.mp (hTpositive hxReflectT)
        have hfoldy : fold y = y := by simp [fold, hyq]
        have hfoldx : fold x = 2 • center - (2 • b₁ - x) := by
          simp only [fold, if_neg hxq]
          rw [hb₁]
          module
        have hxNegative :
            f ((2 • center - (2 • b₁ - x)) - center) < 0 := by
          rw [show (2 • center - (2 • b₁ - x)) - center =
              -((2 • b₁ - x) - center) by module,
            map_neg]
          linarith [hxReflectPositive.2]
        have hfEq := congrArg (fun z ↦ f (z - center)) hxy
        rw [hfoldx, hfoldy] at hfEq
        linarith [hyPositive.2, hxNegative]
      · simp only [fold, if_neg hxq, if_neg hyq] at hxy
        exact sub_left_inj.mp hxy
  have hvertex : ∀ s : Fin (r + 1) → Fin 2,
      cubeVertex center (extendDirs a W.dirs) s ∈ S := by
    intro s
    by_cases hs : s 0 = 0
    · rw [cubeVertex_extend_zero_reflection center b₁ a hb₁ W.dirs s hs]
      have hvT := W.vertex_mem (flipPattern (Fin.tail s))
      have hvS := (mem_positivePart.mp (hTpositive hvT)).1
      exact hsymS _ hvS
    · rw [cubeVertex_extend_zero center b₁ a hb₁ W.dirs s hs]
      exact (mem_positivePart.mp
        (hTpositive (W.vertex_mem (Fin.tail s)))).1
  refine ⟨{
    dirs := extendDirs a W.dirs
    vertex_mem := hvertex
    slice := W.slice.image fold
    slice_subset := ?_
    slice_mem_tube := ?_
    card_le := ?_ }⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hfoldSubset x hx
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hfoldTube x hx
  · rw [Finset.card_image_of_injOn hfoldInj]
    calc
      S.card ≤ D * T.card := hST
      _ ≤ D * (C * W.slice.card) := Nat.mul_le_mul_left D W.card_le
      _ = (D * C) * W.slice.card := by ring

/-! ## Proposition 5.4 -/

/-- Bilu Proposition 5.4, in uniform division-free form.  If `L` has
codimension `r` and `S` is symmetric with doubling at most `tau`, there is
an `r`-cube with vertices in `S` whose `L`-tube contains a fixed positive
fraction of `S`. -/
theorem exists_tubeCubeWitness {r : ℕ} (hr : 0 < r)
    (S : Finset V) (hS : S.Nonempty) (center : V)
    (hsym : SymmetricAbout S center) (L : Submodule ℝ V)
    (hcodim : finrank ℝ L + r = finrank ℝ V) (tau : ℕ)
    (hdouble : (Section7FreimanMap.pairSumset S).card ≤ tau * S.card) :
    Nonempty (TubeCubeWitness r (tubeCubeConstant r tau) S center L) := by
  induction r using Nat.strong_induction_on generalizing S center L tau with
  | h r ih =>
      match r with
      | 0 => exact (Nat.not_lt_zero 0 hr).elim
      | 1 =>
          simpa using exists_tubeCubeWitness_one S hS center hsym L hcodim
      | Nat.succ (Nat.succ k) =>
          by_cases hlarge :
              S.card ≤ 3 * (centralPart S center L).card
          · obtain ⟨W⟩ := exists_tubeCubeWitness_of_large_central
              (r := k + 2) (by omega) S hS center hsym L hlarge
            exact ⟨W.mono_constant (three_le_tubeCubeConstant_add_two k tau)⟩
          · have hcentral :
                3 * (centralPart S center L).card < S.card := by omega
            have houtside : ∃ x ∈ S, x - center ∉ L := by
              by_contra hnone
              push_neg at hnone
              have hcentralEq : centralPart S center L = S := by
                ext x
                constructor
                · intro hx
                  exact (mem_centralPart.mp hx).1
                · intro hx
                  exact mem_centralPart.mpr ⟨hx, hnone x hx⟩
              rw [hcentralEq] at hcentral
              omega
            obtain ⟨f, hfL, _hfne, hfexact⟩ :=
              exists_separating_functional S center L houtside
            have hpositive :
                S.card ≤ 3 * (positivePart S center f).card :=
              card_le_three_mul_card_positivePart S center L f hsym
                hfexact hcentral
            obtain ⟨b₁, T, hT, hTpositive, hsymT, hST,
                hTdouble, hb₁Positive⟩ :=
              exists_positive_symmetric_subset S hS center f tau
                hpositive hdouble
            let a : V := b₁ - center
            have hb₁ : b₁ = center + a := by
              simp [a]
            have hfa : 0 < f a := by
              simpa [a] using hb₁Positive
            have haL : a ∉ L := by
              intro ha
              have hz : f a = 0 := LinearMap.mem_ker.mp (hfL ha)
              linarith
            let L₁ : Submodule ℝ V :=
              L ⊔ Submodule.span ℝ {a}
            have hL₁codim :
                finrank ℝ L₁ + (k + 1) = finrank ℝ V := by
              dsimp [L₁]
              apply finrank_sup_span_add_succ_of_codim L a haL
              simpa [Nat.add_assoc] using hcodim
            have hlower := ih (k + 1) (by omega) (by omega)
              T hT b₁ hsymT L₁ hL₁codim (9 * tau * tau) hTdouble
            obtain ⟨Wlower⟩ := hlower
            have hfold := exists_folded_tubeCubeWitness
              S center hsym f L hfL b₁ a hb₁ hfa T hTpositive hsymT hST Wlower
            obtain ⟨Wfold⟩ := hfold
            have Wfinal := Wfold.mono_constant
              (Nat.le_max_right 3
                (9 * tau * tubeCubeConstant (k + 1) (9 * tau * tau)))
            simpa [tubeCubeConstant, L₁] using
              (show Nonempty (TubeCubeWitness (k + 2)
                (max 3 (9 * tau * tubeCubeConstant (k + 1) (9 * tau * tau)))
                S center L) from ⟨Wfinal⟩)

/-! ## Cube Lemma 5.2 -/

/-- Uniform denominator in the Cube Lemma obtained from Proposition 5.3
and Proposition 5.4. -/
def cubeLemmaConstant (n tau : ℕ) : ℕ :=
  tau * tubeCubeConstant n (tau * tau)

/-- Bilu's Cube Lemma 5.2.  The witness is packaged as a tube over the zero
subspace, which is exactly the closed affine cube itself. -/
theorem exists_cubeLemmaWitness {n : ℕ} (hn : 0 < n)
    (S : Finset V) (hS : S.Nonempty) (hfinrank : finrank ℝ V = n)
    (tau : ℕ)
    (hdouble : (Section7FreimanMap.pairSumset S).card ≤ tau * S.card) :
    ∃ center : V,
      Nonempty (TubeCubeWitness n (cubeLemmaConstant n tau)
        S center (⊥ : Submodule ℝ V)) := by
  obtain ⟨sumCenter, T, _hTeq, hTS, hreflect, hST⟩ :=
    exists_large_symmetricFiber S hS tau hdouble
  have hT : T.Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty.mp hnone] at hST
    simp at hST
    exact hS.ne_empty hST
  let center : V := (1 / 2 : ℝ) • sumCenter
  have hsymT : SymmetricAbout T center := by
    intro x hx
    convert hreflect x hx using 1
    dsimp [center]
    module
  have hTdouble :
      (Section7FreimanMap.pairSumset T).card ≤
        (tau * tau) * T.card := by
    calc
      (Section7FreimanMap.pairSumset T).card ≤
          (Section7FreimanMap.pairSumset S).card :=
        Finset.card_le_card (pairSumset_mono hTS)
      _ ≤ tau * S.card := hdouble
      _ ≤ tau * (tau * T.card) := Nat.mul_le_mul_left tau hST
      _ = (tau * tau) * T.card := by ring
  have hbotCodim :
      finrank ℝ (⊥ : Submodule ℝ V) + n = finrank ℝ V := by
    simp [hfinrank]
  obtain ⟨W⟩ := exists_tubeCubeWitness hn T hT center hsymT
    (⊥ : Submodule ℝ V) hbotCodim (tau * tau) hTdouble
  refine ⟨center, ⟨{
    dirs := W.dirs
    vertex_mem := fun s ↦ hTS (W.vertex_mem s)
    slice := W.slice
    slice_subset := fun _ hx ↦ hTS (W.slice_subset hx)
    slice_mem_tube := W.slice_mem_tube
    card_le := ?_ }⟩⟩
  calc
    S.card ≤ tau * T.card := hST
    _ ≤ tau * (tubeCubeConstant n (tau * tau) * W.slice.card) :=
      Nat.mul_le_mul_left tau W.card_le
    _ = cubeLemmaConstant n tau * W.slice.card := by
      simp [cubeLemmaConstant]
      ring

end

end Erdos186.CFP.Bilu.Section5CubeLemma

#print axioms Erdos186.CFP.Bilu.Section5CubeLemma.exists_tubeCubeWitness_one
#print axioms Erdos186.CFP.Bilu.Section5CubeLemma.exists_tubeCubeWitness
#print axioms Erdos186.CFP.Bilu.Section5CubeLemma.exists_cubeLemmaWitness

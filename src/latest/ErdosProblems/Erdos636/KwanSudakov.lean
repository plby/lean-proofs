/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.Augmentation
import ErdosProblems.Erdos636.AugmentationIntegration
import ErdosProblems.Erdos636.OuterSwitching
import ErdosProblems.Erdos636.RichnessBridge
import ErdosProblems.Erdos636.StructuralIntegration

/-!
# The Kwan--Sudakov assembly for Erdős Problem 636

This file joins the rich-graph structural theorem, balanced augmentation,
and the exact rounded outer parameters.  The small adapter below isolates
the dependent finite choice which selects the structural value `k` and the
successful one-copy/two-copy branch separately for every outer parameter.
-/

open Classical SimpleGraph

namespace Erdos636.KwanSudakov

open OuterAssembly RoundedParameters

universe u

noncomputable section

/-- Choose the Boolean structural branch from the one-copy/two-copy size
alternative. -/
lemma exists_branchScale_eq_of_eq_or_eq_two_mul {u ell : ℕ}
    (h : u = ell ∨ u = 2 * ell) :
    ∃ branch : Bool, u = branchScale branch ell := by
  rcases h with h | h
  · exact ⟨false, by simpa using h⟩
  · exact ⟨true, by simpa using h⟩

/-- The selected affine order is the literal cardinality left after deleting
the corresponding one-copy/two-copy reservoir and adjoining the fixed base
and `k * nZ` augmentation vertices. -/
lemma selectedOffsetOrder_eq_branchScale_sub_add
    (f nW nZ k ell : ℕ) (branch : Bool) (hf : f ≤ ell) :
    ProfileReduction.selectedOffsetOrder f
        (fun _ ↦ nW + k * nZ) (fun _ ↦ branch) ell =
      branchScale branch ell - branchScale branch f + (nW + k * nZ) := by
  cases branch
  · simp [ProfileReduction.selectedOffsetOrder,
      ProfileReduction.offsetAffineOrder, ProfileReduction.firstAffineOrder,
      branchScale]
  · simp [ProfileReduction.selectedOffsetOrder,
      ProfileReduction.offsetAffineOrder,
      ProfileReduction.secondAffineOrder, branchScale]
    omega

lemma selectedAssemblyOrder_eq_branchScale_sub_add
    (cW c₀ δ₀ : ℝ) (n k ell : ℕ) (branch : Bool)
    (hf : deletionSize c₀ n ≤ ell) :
    ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
        (fun _ ↦ assemblyOffset cW c₀ δ₀ n k)
        (fun _ ↦ branch) ell =
      branchScale branch ell - branchScale branch (deletionSize c₀ n) +
        (deletionSize cW n +
          k * augmentationSize δ₀ (deletionSize c₀ n) k) := by
  simpa [assemblyOffset, deletionSize] using
    selectedOffsetOrder_eq_branchScale_sub_add
      (deletionSize c₀ n) (deletionSize cW n)
        (augmentationSize δ₀ (deletionSize c₀ n) k) k ell branch hf

/-- The canonical augmentation order attached to a structural witness is
literally the rounded affine order used by the outer assembly.  This closes
the one-copy/two-copy, base-cardinality, and `k * nZ` bookkeeping in one
place. -/
lemma augmentationOrder_structuralBase_eq_selectedAssemblyOrder
    {n nW ell K : ℕ} {alpha aDisc aDiv b cW c₀ δ₀ : ℝ}
    {G : SimpleGraph (Fin n)}
    (S : StructuralWitness G n nW ell K alpha aDisc aDiv b)
    (branch : Bool)
    (hU0 : S.U0.card = branchScale branch ell)
    (hnW : nW = deletionSize cW n)
    (nD nZ : ℕ)
    (hnD : nD = branchScale branch (deletionSize c₀ n))
    (hnZ : nZ = augmentationSize δ₀ (deletionSize c₀ n) S.k)
    (hf : deletionSize c₀ n ≤ ell) :
    Augmentation.augmentationOrder (Augmentation.structuralBase S branch)
        S.U0 nD nZ S.k =
      ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
        (fun _ ↦ assemblyOffset cW c₀ δ₀ n S.k)
        (fun _ ↦ branch) ell := by
  rw [selectedAssemblyOrder_eq_branchScale_sub_add cW c₀ δ₀ n S.k ell
    branch hf]
  have hbase :
      (Augmentation.structuralBase S branch).card = nW := by
    cases branch <;>
      simp [Augmentation.structuralBase, S.card_Wminus, S.card_Wplus]
  rw [Augmentation.augmentationOrder, hbase, hU0, hnD, hnZ]
  have hbranch := branchScale_mono (double := branch) hf
  have hmul :
      augmentationSize δ₀ (deletionSize c₀ n) S.k * S.k =
        S.k * augmentationSize δ₀ (deletionSize c₀ n) S.k :=
    Nat.mul_comm _ _
  rw [hmul]
  omega

/-- Package pointwise successful fixed-order spectra into the exact rounded
outer-assembly record.  The witness may choose a different `k` and branch
at every outer parameter; bounded multiplicity is recovered later by the
finite offset set in `OuterAssembly`. -/
theorem nonempty_roundedAssemblyInput_of_pointwise
    {E : Type u} {n K : ℕ} {cW c c₀ δ₀ δZ a : ℝ}
    {spectra : ℕ → Finset E}
    (B : Bounds c c₀ δ₀ δZ K n)
    (hpoint : ∀ ell ∈ outerParameterInterval c n,
      ∃ k : ℕ, ∃ branch : Bool,
        1 ≤ k ∧ k ≤ K ∧
          a * n * Real.sqrt n ≤
            ((spectra (ProfileReduction.selectedOffsetOrder
              (deletionSize c₀ n)
              (fun _ell ↦ assemblyOffset cW c₀ δ₀ n k)
              (fun _ell ↦ branch) ell)).card : ℝ)) :
    Nonempty (RoundedAssemblyInput n K cW c₀ δ₀ (c / 2) a spectra) := by
  let P : ℕ → ℕ × Bool → Prop := fun ell p ↦
    ell ∈ outerParameterInterval c n →
      1 ≤ p.1 ∧ p.1 ≤ K ∧
        a * n * Real.sqrt n ≤
          ((spectra (ProfileReduction.selectedOffsetOrder
            (deletionSize c₀ n)
            (fun _ell ↦ assemblyOffset cW c₀ δ₀ n p.1)
            (fun _ell ↦ p.2) ell)).card : ℝ)
  have hex : ∀ ell, ∃ p, P ell p := by
    intro ell
    by_cases hell : ell ∈ outerParameterInterval c n
    · obtain ⟨k, branch, hk1, hkK, hlarge⟩ := hpoint ell hell
      exact ⟨(k, branch), fun _ ↦ ⟨hk1, hkK, hlarge⟩⟩
    · exact ⟨(1, false), fun h ↦ (hell h).elim⟩
  let choice : ℕ → ℕ × Bool := fun ell ↦ Classical.choose (hex ell)
  have hchoice : ∀ ell, P ell (choice ell) := fun ell ↦
    Classical.choose_spec (hex ell)
  refine ⟨{
    parameter := outerParameterInterval c n
    k := fun ell ↦ (choice ell).1
    branch := fun ell ↦ (choice ell).2
    linear_card := B.parameter_linear
    deletion_le := ?_
    k_pos := ?_
    k_le := ?_
    large := ?_ }⟩
  · intro ell hell
    have hthree := B.reservoir_large false ell hell
    have hthree' : 3 * deletionSize c₀ n ≤ ell := by
      simpa [branchScale] using hthree
    omega
  · intro ell hell
    exact (hchoice ell hell).1
  · intro ell hell
    exact (hchoice ell hell).2.1
  · intro ell hell
    simpa only [ProfileReduction.selectedOffsetOrder] using
      (hchoice ell hell).2.2

/-- Uniform form of `nonempty_roundedAssemblyInput_of_pointwise`.

This theorem is the boundary between the graph/probability argument and the
purely finite profile reduction.  It deliberately asks only for the
pointwise conclusion of the Kwan--Sudakov switching construction.  All
rounding estimates and all parameter-dependent choices are discharged here.
-/
theorem hasRoundedAssembly_of_pointwise
    {Ambient : ℕ → Type u}
    {Good : (n : ℕ) → Ambient n → Prop}
    {spectra : (n : ℕ) → Ambient n → ℕ → Finset ℕ}
    {cW c c₀ δ₀ δZ a : ℝ} {K : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ)
    (ha : 0 < a) (hK : 0 < K)
    (hpoint : ∃ N : ℕ, ∀ n ≥ N, ∀ G : Ambient n, Good n G →
      ∀ ell ∈ outerParameterInterval c n,
        ∃ k : ℕ, ∃ branch : Bool,
          1 ≤ k ∧ k ≤ K ∧
            a * n * Real.sqrt n ≤
              (((spectra n G)
                (ProfileReduction.selectedOffsetOrder
                  (deletionSize c₀ n)
                  (fun _ell ↦ assemblyOffset cW c₀ δ₀ n k)
                  (fun _ell ↦ branch) ell)).card : ℝ)) :
    HasRoundedAssembly Good spectra := by
  obtain ⟨Nround, hround⟩ :=
    exists_uniform_rounding_threshold hc hc₀ hsmall hδ₀ hδZ hK
  obtain ⟨Npoint, hpoint⟩ := hpoint
  refine ⟨cW, c₀, δ₀, c / 2, a, hc₀, hδ₀, by positivity, ha,
    K, hK, max Nround Npoint, ?_⟩
  intro n hn G hG
  apply nonempty_roundedAssemblyInput_of_pointwise
    (hround n ((le_max_left _ _).trans hn))
  exact hpoint n ((le_max_right _ _).trans hn) G hG

/-- Uniform pointwise-window form of the Kwan--Sudakov assembly.

This is the exact interface consumed by the graph-specific structural,
crowd, and balanced-augmentation argument.  Each outer parameter may choose
its own structural uniformity `k` and one-copy/two-copy branch.  The
separated-window count supplies the product constant `b * d`, while the
rounded parameter estimates and the bounded order multiplicity are handled
by `hasRoundedAssembly_of_pointwise`. -/
theorem hasRoundedAssembly_of_pointwiseWindows
    {Ambient : ℕ → Type u}
    {Good : (n : ℕ) → Ambient n → Prop}
    {spectra : (n : ℕ) → Ambient n → ℕ → Finset ℕ}
    {cW c c₀ δ₀ δZ b d : ℝ} {K : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ)
    (hb : 0 < b) (hd : 0 < d) (hK : 0 < K)
    (hpoint : ∃ N : ℕ, ∀ n ≥ N, ∀ G : Ambient n, Good n G →
      ∀ ell ∈ outerParameterInterval c n,
        Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ δ₀ b d
          (spectra n G) ell)) :
    HasRoundedAssembly Good spectra := by
  apply hasRoundedAssembly_of_pointwise hc hc₀ hsmall hδ₀ hδZ
    (mul_pos hb hd) hK
  obtain ⟨N, hN⟩ := hpoint
  refine ⟨N, ?_⟩
  intro n hn G hG ell hell
  let P := Classical.choice (hN n hn G hG ell hell)
  refine ⟨P.k, P.branch, P.k_pos, P.k_le, ?_⟩
  exact P.windows.large_spectrum n b d hb.le hd.le P.index_large P.piece_large

/-- The precise eventual graph-specific assertion left by the structural,
crowd, and balanced-augmentation construction.  Keeping it as a named
predicate makes the final integration insensitive to the internal choice of
constants while preserving all rounding and fixed-order data literally. -/
def RamseyFreePointwiseWindows (C : ℝ) : Prop :=
  ∃ cW c c₀ δ₀ δZ b d : ℝ, ∃ K : ℕ,
    0 < c ∧ 0 < c₀ ∧ 6 * c₀ ≤ c ∧
    0 < δ₀ ∧ δ₀ ≤ δZ ∧ 0 < b ∧ 0 < d ∧ 0 < K ∧
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      Erdos88.RamseyFree C G →
      ∀ ell ∈ outerParameterInterval c n,
        Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ δ₀ b d
          (Augmentation.fixedOrderEdgeValues G) ell)

/-- Compose the two eventual graph-facing inputs without changing the public
boundary: first construct the structural witness at the rounded deletion
density, then feed that witness to the balanced augmentation and switching
theorem. -/
theorem ramseyFreePointwiseWindows_of_structural_augmentation
    {C cW c c₀ δ₀ δZ bIndex dPiece aDisc aDiv bStruct : ℝ} {K : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ)
    (hbIndex : 0 < bIndex) (hdPiece : 0 < dPiece) (hK : 0 < K)
    (hstruct : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      Erdos88.RamseyFree C G →
      ∀ ell ∈ outerParameterInterval c n,
        Nonempty (StructuralWitness G n (deletionSize cW n) ell K
          (1 - (deletionSize c₀ n : ℝ) / ell) aDisc aDiv bStruct))
    (haugment : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      ∀ ell ∈ outerParameterInterval c n,
        Nonempty (StructuralWitness G n (deletionSize cW n) ell K
          (1 - (deletionSize c₀ n : ℝ) / ell) aDisc aDiv bStruct) →
        Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ δ₀
          bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell)) :
    RamseyFreePointwiseWindows C := by
  obtain ⟨Nstruct, hstruct⟩ := hstruct
  obtain ⟨Naugment, haugment⟩ := haugment
  refine ⟨cW, c, c₀, δ₀, δZ, bIndex, dPiece, K,
    hc, hc₀, hsmall, hδ₀, hδZ, hbIndex, hdPiece, hK,
    max Nstruct Naugment, ?_⟩
  intro n hn G hG ell hell
  apply haugment n ((le_max_right Nstruct Naugment).trans hn) G ell hell
  exact hstruct n ((le_max_left Nstruct Naugment).trans hn) G hG ell hell

/-- Rounded-parameter adapter for a structural theorem uniform in
`alpha \in [1/2,1]`.  This is the exact form supplied after lifting the
fixed-ambient rich-graph construction back to the original Ramsey graph.
The only additional threshold chosen here is the elementary simultaneous
rounding threshold from `RoundedParameters`. -/
theorem ramseyFreePointwiseWindows_of_uniform_structural_augmentation
    {C cW c c₀ δ₀ δZ bIndex dPiece aDisc aDiv bStruct : ℝ} {K : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ)
    (hbIndex : 0 < bIndex) (hdPiece : 0 < dPiece) (hK : 0 < K)
    (hstruct : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      Erdos88.RamseyFree C G →
      ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha ≤ 1 →
      ∀ ell : ℕ, c * n ≤ ell → (ell : ℝ) ≤ 2 * c * n →
        Nonempty (StructuralWitness G n (deletionSize cW n) ell K
          alpha aDisc aDiv bStruct))
    (haugment : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      ∀ ell ∈ outerParameterInterval c n,
        Nonempty (StructuralWitness G n (deletionSize cW n) ell K
          (1 - (deletionSize c₀ n : ℝ) / ell) aDisc aDiv bStruct) →
        Nonempty (OuterSwitching.PointwiseWindows n K cW c₀ δ₀
          bIndex dPiece (Augmentation.fixedOrderEdgeValues G) ell)) :
    RamseyFreePointwiseWindows C := by
  obtain ⟨Nstruct, hstruct⟩ := hstruct
  obtain ⟨Nround, hround⟩ :=
    exists_uniform_rounding_threshold hc hc₀ hsmall hδ₀ hδZ hK
  apply ramseyFreePointwiseWindows_of_structural_augmentation hc hc₀ hsmall
    hδ₀ hδZ hbIndex hdPiece hK
  · refine ⟨max Nstruct Nround, ?_⟩
    intro n hn G hG ell hell
    have B := hround n ((le_max_right Nstruct Nround).trans hn)
    have halpha := B.alpha_bounds ell hell
    have hell' := (mem_outerParameterInterval hc.le).mp hell
    exact hstruct n ((le_max_left Nstruct Nround).trans hn) G hG
      (1 - (deletionSize c₀ n : ℝ) / ell) halpha.1 halpha.2
      ell hell'.1 hell'.2
  · exact haugment

/-- Lift an eventual fixed-ambient structural theorem from the rich induced
subgraph supplied by the Kwan--Sudakov richness reduction back to the
original Ramsey graph.  The external scale `n`, the rounded base size, and
all quantitative constants are preserved exactly by `liftInduce`. -/
theorem eventually_structuralWitness_ramseyFree_of_linear_rich_induce
    {C cR epsilon cW c aDisc aDiv bStruct : ℝ} {K : ℕ}
    (hcR : 0 < cR)
    (hrich : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      Erdos88.RamseyFree C G →
      ∃ U : Finset (Fin n), cR * n ≤ U.card ∧
        KwanSudakovRich (G.induce (U : Set (Fin n))) (epsilon ^ K) epsilon)
    (hstruct : ∃ N : ℕ, ∀ n ≥ N,
      ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V],
        cR * n ≤ Fintype.card V →
        (Fintype.card V : ℝ) ≤ n →
        ∀ H : SimpleGraph V, KwanSudakovRich H (epsilon ^ K) epsilon →
        ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha ≤ 1 →
        ∀ ell : ℕ, c * n ≤ ell → (ell : ℝ) ≤ 2 * c * n →
          Nonempty (StructuralWitness H n (deletionSize cW n) ell K
            alpha aDisc aDiv bStruct)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      Erdos88.RamseyFree C G →
      ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha ≤ 1 →
      ∀ ell : ℕ, c * n ≤ ell → (ell : ℝ) ≤ 2 * c * n →
        Nonempty (StructuralWitness G n (deletionSize cW n) ell K
          alpha aDisc aDiv bStruct) := by
  obtain ⟨Nrich, hrich⟩ := hrich
  obtain ⟨Nstruct, hstruct⟩ := hstruct
  refine ⟨max 1 (max Nrich Nstruct), ?_⟩
  intro n hn G hG alpha halpha0 halpha1 ell hell0 hell1
  have hnpos : 0 < n := by
    have : 1 ≤ n := (le_max_left 1 (max Nrich Nstruct)).trans hn
    omega
  have hnrich : Nrich ≤ n :=
    (le_max_left Nrich Nstruct).trans
      ((le_max_right 1 (max Nrich Nstruct)).trans hn)
  have hnstruct : Nstruct ≤ n :=
    (le_max_right Nrich Nstruct).trans
      ((le_max_right 1 (max Nrich Nstruct)).trans hn)
  obtain ⟨U, hUlower, hURich⟩ := hrich n hnrich G hG
  have hUcardPos : 0 < U.card := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have : (0 : ℝ) < U.card :=
      (mul_pos hcR hnreal).trans_le hUlower
    exact_mod_cast this
  have hUne : U.Nonempty := Finset.card_pos.mp hUcardPos
  let : Nonempty ↑(U : Set (Fin n)) :=
    ⟨⟨hUne.choose, by simpa using hUne.choose_spec⟩⟩
  have hUupperNat : U.card ≤ n := by
    simpa using (Finset.card_le_univ U)
  have hUupper : (Fintype.card ↑(U : Set (Fin n)) : ℝ) ≤ n := by
    simpa using (show (U.card : ℝ) ≤ n by exact_mod_cast hUupperNat)
  have hUlower' : cR * n ≤ Fintype.card ↑(U : Set (Fin n)) := by
    simpa using hUlower
  apply nonempty_structuralWitness_liftInduce
  exact hstruct n hnstruct ↑(U : Set (Fin n)) hUlower' hUupper
    (G.induce (U : Set (Fin n))) hURich alpha halpha0 halpha1 ell hell0 hell1

/-- Compose the two unconditional graph-facing endpoint families with the
Kwan--Sudakov rich-induced-subgraph reduction.  The statement exposes no
auxiliary schedule, event, or probability premise: `hfixed` is exactly the
eventual structural theorem for rich graphs, and `haugment` is exactly the
eventual pointwise-window theorem from one structural witness. -/
theorem ramseyFreePointwiseWindows_of_unconditional_endpoints
    (C : ℝ) (hC : 0 < C)
    (hfixed : ∀ {cR epsilon : ℝ}, 0 < cR → cR ≤ 1 →
      0 < epsilon → epsilon < 1 →
      ∃ cW c aDisc aDiv bStruct : ℝ,
        0 < cW ∧ 0 < c ∧ 0 < aDisc ∧ 0 < aDiv ∧ 0 < bStruct ∧
        ∃ N : ℕ, ∀ n ≥ N,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V],
            cR * n ≤ Fintype.card V →
            (Fintype.card V : ℝ) ≤ n →
            ∀ G : SimpleGraph V,
              KwanSudakovRich G (epsilon ^ structuralUniformity) epsilon →
              ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha ≤ 1 →
              ∀ ell : ℕ, c * n ≤ ell → (ell : ℝ) ≤ 2 * c * n →
                Nonempty (StructuralWitness G n ⌊cW * n⌋₊ ell
                  structuralUniformity alpha aDisc aDiv bStruct))
    (haugment : ∀ {cW c aDisc aDiv bStruct : ℝ},
      0 < cW → 0 < c → 0 < aDisc → 0 < aDiv → 0 < bStruct →
      ∃ c₀ δ₀ δZ bIndex dPiece : ℝ,
        0 < c₀ ∧ 6 * c₀ ≤ c ∧ 0 < δ₀ ∧ δ₀ ≤ δZ ∧
        0 < bIndex ∧ 0 < dPiece ∧
        ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
          ∀ ell ∈ outerParameterInterval c n,
            Nonempty (StructuralWitness G n (deletionSize cW n) ell
              structuralUniformity
              (1 - (deletionSize c₀ n : ℝ) / ell)
              aDisc aDiv bStruct) →
            Nonempty (OuterSwitching.PointwiseWindows n structuralUniformity
              cW c₀ δ₀ bIndex dPiece
              (Augmentation.fixedOrderEdgeValues G) ell)) :
    RamseyFreePointwiseWindows C := by
  obtain ⟨epsilon, cRich, hepsilon, hepsilonOne, hcRich,
      Nrich, hrich⟩ :=
    exists_linear_ksRich_induce_pow C structuralUniformity hC
      (by simp [structuralUniformity])
  let cR : ℝ := min cRich 1
  have hcR : 0 < cR := by
    dsimp only [cR]
    exact lt_min hcRich zero_lt_one
  have hcROne : cR ≤ 1 := by
    dsimp only [cR]
    exact min_le_right _ _
  obtain ⟨cW, c, aDisc, aDiv, bStruct,
      hcW, hc, haDisc, haDiv, hbStruct, Nfixed, hfixed⟩ :=
    hfixed hcR hcROne hepsilon hepsilonOne
  have hrichAtScale : ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        ∃ U : Finset (Fin n), cR * n ≤ U.card ∧
          KwanSudakovRich (G.induce (U : Set (Fin n)))
            (epsilon ^ structuralUniformity) epsilon := by
    refine ⟨Nrich, ?_⟩
    intro n hn G hG
    obtain ⟨U, hUlower, hURich⟩ := hrich n hn G hG
    refine ⟨U, ?_, hURich⟩
    exact (mul_le_mul_of_nonneg_right (min_le_left cRich 1)
      (Nat.cast_nonneg n)).trans hUlower
  have hfixedRounded : ∃ N : ℕ, ∀ n ≥ N,
      ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V],
        cR * n ≤ Fintype.card V →
        (Fintype.card V : ℝ) ≤ n →
        ∀ G : SimpleGraph V,
          KwanSudakovRich G (epsilon ^ structuralUniformity) epsilon →
          ∀ alpha : ℝ, 1 / 2 ≤ alpha → alpha ≤ 1 →
          ∀ ell : ℕ, c * n ≤ ell → (ell : ℝ) ≤ 2 * c * n →
            Nonempty (StructuralWitness G n (deletionSize cW n) ell
              structuralUniformity alpha aDisc aDiv bStruct) := by
    refine ⟨Nfixed, ?_⟩
    intro n hn V _instFintype _instDecidableEq _instNonempty
      hVlower hVupper G hG alpha halpha0 halpha1 ell hell0 hell1
    simpa only [deletionSize] using
      hfixed n hn V hVlower hVupper G hG alpha halpha0 halpha1 ell hell0 hell1
  obtain ⟨Nstruct, hstruct⟩ :=
    eventually_structuralWitness_ramseyFree_of_linear_rich_induce
      hcR hrichAtScale hfixedRounded
  obtain ⟨c₀, δ₀, δZ, bIndex, dPiece,
      hc₀, hsmall, hδ₀, hδZ, hbIndex, hdPiece, Naugment, haugment⟩ :=
    haugment hcW hc haDisc haDiv hbStruct
  apply ramseyFreePointwiseWindows_of_uniform_structural_augmentation
    (C := C) (cW := cW) (c := c) (c₀ := c₀) (δ₀ := δ₀) (δZ := δZ)
    (bIndex := bIndex) (dPiece := dPiece) (aDisc := aDisc)
    (aDiv := aDiv) (bStruct := bStruct) (K := structuralUniformity)
    hc hc₀ hsmall hδ₀ hδZ hbIndex hdPiece
    (by norm_num [structuralUniformity])
  · exact ⟨Nstruct, hstruct⟩
  · exact ⟨Naugment, haugment⟩

/-- The final, assumption-free rounding integration once the graph-specific
Kwan--Sudakov pointwise-window theorem has been established. -/
theorem hasRoundedAssembly_ramseyFree_of_pointwiseWindows
    {C : ℝ} (h : RamseyFreePointwiseWindows C) :
    HasRoundedAssembly
      (Ambient := fun n ↦ SimpleGraph (Fin n))
      (fun _n G ↦ Erdos88.RamseyFree C G)
      (fun _n G ↦ Augmentation.fixedOrderEdgeValues G) := by
  rcases h with ⟨cW, c, c₀, δ₀, δZ, b, d, K,
    hc, hc₀, hsmall, hδ₀, hδZ, hb, hd, hK, hpoint⟩
  exact hasRoundedAssembly_of_pointwiseWindows hc hc₀ hsmall hδ₀ hδZ
    hb hd hK hpoint

/-- The unconditional Kwan--Sudakov pointwise-window theorem.  Ramsey
freeness first supplies a linear rich induced subgraph; the structural
endpoint constructs the fixed-ambient witness there and lifts it back; the
balanced augmentation endpoint then supplies the exact fixed-order windows.
All schedules, exposure events, and numerical inequalities are internal to
the two endpoint theorems used below. -/
theorem ramseyFreePointwiseWindows (C : ℝ) (hC : 0 < C) :
    RamseyFreePointwiseWindows C := by
  apply ramseyFreePointwiseWindows_of_unconditional_endpoints C hC
  · intro cR epsilon hcR hcROne hepsilon hepsilonOne
    exact
      StructuralIntegration.eventually_nonempty_structuralWitness_of_ksRich_fixedAmbient
        hcR hcROne hepsilon hepsilonOne
  · intro cW c aDisc aDiv bStruct hcW hc haDisc haDiv hbStruct
    exact
      AugmentationIntegration.exists_eventual_pointwiseWindows_of_structuralWitness
        (K := structuralUniformity) (by norm_num [structuralUniformity])
        hcW hc haDisc haDiv hbStruct

/-- Exact rounded-assembly form of the unconditional Kwan--Sudakov theorem,
specialized to Ramsey-free graphs and their fixed-order induced-edge
spectra. -/
theorem hasRoundedAssembly_ramseyFree (C : ℝ) (hC : 0 < C) :
    HasRoundedAssembly
      (Ambient := fun n ↦ SimpleGraph (Fin n))
      (fun _n G ↦ Erdos88.RamseyFree C G)
      (fun _n G ↦ Augmentation.fixedOrderEdgeValues G) :=
  hasRoundedAssembly_ramseyFree_of_pointwiseWindows
    (ramseyFreePointwiseWindows C hC)

end

end Erdos636.KwanSudakov

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 909.
https://www.erdosproblems.com/forum/thread/909

Informal authors:
- R. D. Anderson
- J. E. Keisler

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos909.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 909.
https://www.erdosproblems.com/909

Informal authors:
- R. D. Anderson
- J. E. Keisler

Formal author:
- OpenAI Codex

Primary reference:
- R. D. Anderson and J. E. Keisler, "An example in dimension theory",
  Proc. Amer. Math. Soc. 18 (1967), 709--713.
-/

import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.SmallInductiveDimension
import ErdosProblems.Erdos909.MazurkiewiczDoubleCone

/-!
# Erdős Problem 909

For every natural number `n ≥ 2`, there is a topological space `S` whose
small inductive dimension is `n` and whose Cartesian square has the same
dimension.

The mathematical proof and a detailed formalization guide are in `tex/909.tex`.
-/

open Set Topology TopologicalSpace

namespace Erdos909

section DimensionInvariance

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Small inductive dimension does not increase when a topology is induced
from another space. -/
theorem inducing_hasSmallInductiveDimensionLT {f : X → Y} (hf : IsInducing f)
    {n : ℕ} (h : HasSmallInductiveDimensionLT Y n) :
    HasSmallInductiveDimensionLT X n := by
  induction h generalizing X with
  | zero =>
      have := Function.isEmpty f
      exact HasSmallInductiveDimensionLT.zero
  | succ n s hs h ih =>
      refine .succ n _ (hs.isInducing hf) ?_
      rintro _ ⟨U, hU, rfl⟩
      apply ih U hU
      apply (hf.restrictPreimage (frontier U)).comp
      exact (IsEmbedding.inclusion (hf.continuous.frontier_preimage_subset U)).isInducing

/-- The class-valued non-strict small-inductive-dimension bound also pulls
back along an inducing map. -/
theorem inducing_hasSmallInductiveDimensionLE {f : X → Y} (hf : IsInducing f)
    {n : ℕ} (h : HasSmallInductiveDimensionLE Y n) :
    HasSmallInductiveDimensionLE X n :=
  inducing_hasSmallInductiveDimensionLT hf h

/-- Small inductive dimension does not increase along an inducing map. -/
theorem inducing_smallInductiveDimension_le {f : X → Y} (hf : IsInducing f) :
    smallInductiveDimension X ≤ smallInductiveDimension Y := by
  apply sInf_le_sInf
  intro m hm i hi
  exact inducing_hasSmallInductiveDimensionLT hf (hm i hi)

/-- A subspace has small inductive dimension at most that of its ambient
space. -/
theorem smallInductiveDimension_subspace_le (s : Set X) :
    smallInductiveDimension s ≤ smallInductiveDimension X :=
  inducing_smallInductiveDimension_le IsInducing.subtypeVal

/-- A convenient interface to the recursive definition: it is enough to
bound each basis frontier by a (possibly larger) subspace of known strict
dimension. -/
theorem hasSmallInductiveDimensionLT_of_basis_frontier_subset
    (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (F : Set X → Set X)
    (hsub : ∀ U ∈ b, frontier U ⊆ F U)
    (hdim : ∀ U ∈ b, HasSmallInductiveDimensionLT (F U) n) :
    HasSmallInductiveDimensionLT X (n + 1) := by
  refine .succ n b hb ?_
  intro U hU
  exact inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion (hsub U hU)).isInducing (hdim U hU)

/-- Intersecting an ambient basis with a subspace gives a dimension bound when
the intersections with all ambient frontiers have the preceding strict
dimension bound.  This is the recursive step used by the sphere-cutting
argument of Anderson--Keisler. -/
theorem subtype_hasSmallInductiveDimensionLT_of_basis
    (s : Set X) (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (hdim : ∀ U ∈ b,
      HasSmallInductiveDimensionLT (Subtype.val ⁻¹' frontier U : Set s) n) :
    HasSmallInductiveDimensionLT s (n + 1) := by
  refine .succ n _ (hb.isInducing IsInducing.subtypeVal) ?_
  rintro _ ⟨U, hU, rfl⟩
  exact inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion
      (continuous_subtype_val.frontier_preimage_subset U)).isInducing
    (hdim U hU)

/-- An ambient open lift has exactly the desired relative frontier once both
its trace and its closure trace agree with those of the subspace-open set.
The nontrivial metric-space step in the continuum-hitter argument is to
construct lifts satisfying the two displayed hypotheses. -/
theorem preimage_frontier_eq_of_isOpen_of_closure_preimage_eq
    {f : X → Y} {V : Set Y} {B : Set X}
    (hV : IsOpen V) (hB : IsOpen B)
    (hpre : f ⁻¹' V = B) (hclosure : f ⁻¹' closure V = closure B) :
    f ⁻¹' frontier V = frontier B := by
  rw [hV.frontier_eq, hB.frontier_eq, preimage_sdiff, hclosure, hpre]

/-- A nontrivial open set of a metrizable subspace has an ambient open lift
whose trace and closure trace are the prescribed set and its relative closure.
Together with `preimage_frontier_eq_of_isOpen_of_closure_preimage_eq`, this
also makes the frontier trace exact. -/
theorem exists_isOpen_subtype_lift_closure_preimage_eq
    {Z : Type*} [PseudoMetricSpace Z] (s : Set Z) {B : Set s}
    (hB : IsOpen B) (hBn : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    ∃ V : Set Z, IsOpen V ∧
      Subtype.val ⁻¹' V = B ∧
      Subtype.val ⁻¹' closure V = closure B := by
  let A : Set Z := Subtype.val '' B
  let C : Set Z := Subtype.val '' Bᶜ
  let V : Set Z := {x | Metric.infDist x A < Metric.infDist x C}
  have hAn : A.Nonempty := hBn.image Subtype.val
  have hCn : C.Nonempty := hBc.image Subtype.val
  have hVo : IsOpen V :=
    isOpen_lt (Metric.continuous_infDist_pt A) (Metric.continuous_infDist_pt C)
  have htrace : Subtype.val ⁻¹' V = B := by
    ext y
    constructor
    · intro hyV
      by_contra hyB
      have hyC : (y : Z) ∈ C := ⟨y, hyB, rfl⟩
      have hzero : Metric.infDist (y : Z) C = 0 := Metric.infDist_zero_of_mem hyC
      exact (not_lt_of_ge Metric.infDist_nonneg) (by simpa [V, hzero] using hyV)
    · intro hyB
      have hyA : (y : Z) ∈ A := ⟨y, hyB, rfl⟩
      have hzero : Metric.infDist (y : Z) A = 0 := Metric.infDist_zero_of_mem hyA
      have hy_not : (y : Z) ∉ closure C := by
        have hy_not' : y ∉ closure (Bᶜ : Set s) := by
          rw [hB.isClosed_compl.closure_eq]
          simpa only [mem_compl_iff, not_not] using hyB
        simpa [C, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hy_not'
      have hpos : 0 < Metric.infDist (y : Z) C :=
        (Metric.infDist_pos_iff_notMem_closure hCn).1 hy_not
      simpa [V, hzero] using hpos
  refine ⟨V, hVo, htrace, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hycl
    have hy_notA : (y : Z) ∉ closure A := by
      have hy_notA' : y ∉ closure B := hycl
      simpa [A, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hy_notA'
    have hposA : 0 < Metric.infDist (y : Z) A :=
      (Metric.infDist_pos_iff_notMem_closure hAn).1 hy_notA
    have hyBc : y ∈ Bᶜ := by
      simpa using fun hyB : y ∈ B ↦ hycl (subset_closure hyB)
    have hyC : (y : Z) ∈ C := ⟨y, hyBc, rfl⟩
    have hzeroC : Metric.infDist (y : Z) C = 0 := Metric.infDist_zero_of_mem hyC
    let W : Set Z := {x | Metric.infDist x C < Metric.infDist x A}
    have hWo : IsOpen W :=
      isOpen_lt (Metric.continuous_infDist_pt C) (Metric.continuous_infDist_pt A)
    have hyW : (y : Z) ∈ W := by simpa [W, hzeroC] using hposA
    have hWV : W ⊆ Vᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_ofPred_eq, V, W] at hx ⊢
      exact fun h ↦ lt_asymm hx h
    have hyint : (y : Z) ∈ interior Vᶜ :=
      mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset (hWo.mem_nhds hyW) hWV)
    have : (y : Z) ∉ closure V := by
      simpa only [interior_compl, mem_compl_iff] using hyint
    exact this hy
  · intro y hy
    have hyA : (y : Z) ∈ closure A := by
      simpa [A, IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] using hy
    apply closure_mono _ hyA
    intro x hxA
    rcases hxA with ⟨y, hyB, rfl⟩
    change y ∈ Subtype.val ⁻¹' V
    rw [htrace]
    exact hyB

/-- Frontier-preserving form of
`exists_isOpen_subtype_lift_closure_preimage_eq`. -/
theorem exists_isOpen_subtype_lift_frontier_preimage_eq
    {Z : Type*} [PseudoMetricSpace Z] (s : Set Z) {B : Set s}
    (hB : IsOpen B) (hBn : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    ∃ V : Set Z, IsOpen V ∧
      Subtype.val ⁻¹' V = B ∧
      Subtype.val ⁻¹' frontier V = frontier B := by
  obtain ⟨V, hV, htrace, hclosure⟩ :=
    exists_isOpen_subtype_lift_closure_preimage_eq s hB hBn hBc
  exact ⟨V, hV, htrace,
    preimage_frontier_eq_of_isOpen_of_closure_preimage_eq
      hV hB htrace hclosure⟩

/-- Homeomorphisms preserve the class-valued strict bound. -/
theorem Homeomorph.hasSmallInductiveDimensionLT (f : X ≃ₜ Y) (n : ℕ) :
    HasSmallInductiveDimensionLT X n ↔ HasSmallInductiveDimensionLT Y n :=
  ⟨inducing_hasSmallInductiveDimensionLT f.symm.isInducing,
    inducing_hasSmallInductiveDimensionLT f.isInducing⟩

/-- Homeomorphisms preserve the class-valued non-strict bound. -/
theorem Homeomorph.hasSmallInductiveDimensionLE (f : X ≃ₜ Y) (n : ℕ) :
    HasSmallInductiveDimensionLE X n ↔ HasSmallInductiveDimensionLE Y n :=
  Homeomorph.hasSmallInductiveDimensionLT f (n + 1)

/-- Small inductive dimension is a homeomorphism invariant. -/
theorem Homeomorph.smallInductiveDimension_congr (f : X ≃ₜ Y) :
    smallInductiveDimension X = smallInductiveDimension Y := by
  unfold _root_.smallInductiveDimension
  congr! 3
  exact forall₂_congr fun i _ ↦ Homeomorph.hasSmallInductiveDimensionLT f i

end DimensionInvariance

section CountableSelfProduct

variable (A : Type*) [TopologicalSpace A]

/-- A countable product of one space is homeomorphic to its square, by
splitting the coordinates into the even and odd coordinates. -/
noncomputable def piNatProdHomeomorph :
    (ℕ → A) × (ℕ → A) ≃ₜ (ℕ → A) :=
  (Homeomorph.sumPiEquivProdPi ℕ ℕ (fun _ ↦ A)).symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ : ℕ ↦ A) Equiv.natSumNatEquivNat)

/-- The square of a countable product has the same small inductive dimension
as the countable product itself. -/
theorem smallInductiveDimension_piNat_prod :
    smallInductiveDimension ((ℕ → A) × (ℕ → A)) =
      smallInductiveDimension (ℕ → A) :=
  Erdos909.Homeomorph.smallInductiveDimension_congr (piNatProdHomeomorph A)

end CountableSelfProduct

section ReductionToAndersonKeisler

/-- The exact conclusion asked for in Erdős Problem 909, expressed using
Mathlib's Menger--Urysohn small inductive dimension.  The topology on the
Cartesian square is the ordinary product topology inferred by typeclass
search. -/
def HasErdos909Property (n : ℕ) (S : Type*) [TopologicalSpace S] : Prop :=
  smallInductiveDimension S = n ∧
    smallInductiveDimension (S × S) = n

/-- A nonempty space embeds as a coordinate slice of its Cartesian square. -/
theorem smallInductiveDimension_le_square
    (S : Type*) [TopologicalSpace S] [Nonempty S] :
    smallInductiveDimension S ≤ smallInductiveDimension (S × S) :=
  inducing_smallInductiveDimension_le
    (isEmbedding_prodMkLeft (Classical.choice ‹Nonempty S›)).isInducing

/-- To finish the Anderson--Keisler calculation it suffices to prove the
dimension of `S` and the upper bound for its square; the coordinate slice
supplies the reverse bound automatically. -/
theorem hasErdos909Property_of_square_le
    (n : ℕ) (S : Type*) [TopologicalSpace S] [Nonempty S]
    (hS : smallInductiveDimension S = n)
    (hSq : smallInductiveDimension (S × S) ≤ n) :
    HasErdos909Property n S := by
  refine ⟨hS, hSq.antisymm ?_⟩
  rw [← hS]
  exact smallInductiveDimension_le_square S

/-- Anderson--Keisler's countable-power theorem implies the requested
Cartesian-square statement immediately: split the countably many coordinates
into the even and odd coordinates. -/
theorem exists_erdos909Space_of_countablePower
    (n : ℕ) (A : Type) [TopologicalSpace A]
    (hA : smallInductiveDimension (ℕ → A) = n) :
    ∃ (S : Type) (_ : TopologicalSpace S), HasErdos909Property n S := by
  let S := ℕ → A
  refine ⟨S, inferInstance, hA, ?_⟩
  rw [smallInductiveDimension_piNat_prod]
  exact hA

end ReductionToAndersonKeisler

/-! ### Resolution of Erdős Problem 909 -/

/-- **Erdős Problem 909 (Anderson--Keisler).**  For every `n ≥ 2` there
is a topological space of small inductive dimension `n` whose Cartesian
square again has small inductive dimension `n`. -/
theorem erdos_909 (n : ℕ) (hn : 2 ≤ n) :
    ∃ (S : Type) (_ : TopologicalSpace S),
      smallInductiveDimension S = n ∧
      smallInductiveDimension (S × S) = n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hm : 0 < n + 1 := Nat.add_pos_left hnpos 1
  let O := Classical.choice
    (EuclideanObstruction.exists_unaryBinaryObstructions (n + 1) hm)
  let p : EuclideanObstruction.LetterSpace (n + 1) :=
    MazurkiewiczDoubleCone.doubleConeEmbedding n
      (DoubleCone.lowerEndpoint n)
  let q : EuclideanObstruction.LetterSpace (n + 1) :=
    MazurkiewiczDoubleCone.doubleConeEmbedding n
      (DoubleCone.upperEndpoint n)
  have hMaz : AndersonKeislerAssembly.HasMazurkiewiczBetween
      (EuclideanObstruction.LetterSpace (n + 1)) n p q :=
    MazurkiewiczDoubleCone.euclidean_assembly_hasMazurkiewiczBetween n
  obtain ⟨K, hK, hKsq⟩ :=
    AndersonKeislerAssembly.exists_andersonKeisler_witness n O p q hMaz
  exact ⟨K, inferInstance, hK, hKsq⟩

#print axioms erdos_909

end Erdos909

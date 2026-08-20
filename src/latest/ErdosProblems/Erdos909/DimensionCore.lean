/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.SmallInductiveDimension

/-!
# Dimension-theoretic infrastructure for Erdős Problem 909

This file gives two interfaces to the recursive definition of the small
inductive dimension.  The local interface extracts a small-frontier
neighbourhood inside any prescribed open neighbourhood.  The certificate
interface permits each basis frontier to be replaced by a larger subspace;
this is the form used when a cutting sphere controls a relative frontier.
-/

open Set Topology TopologicalSpace

namespace Erdos909.DimensionCore

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem inducing_hasSmallInductiveDimensionLT
    {f : X → Y} (hf : IsInducing f) {n : ℕ}
    (h : HasSmallInductiveDimensionLT Y n) :
    HasSmallInductiveDimensionLT X n := by
  induction h generalizing X with
  | zero =>
      have := Function.isEmpty f
      exact .zero
  | succ n b hb hfront ih =>
      refine .succ n _ (hb.isInducing hf) ?_
      rintro _ ⟨U, hU, rfl⟩
      apply ih U hU
      apply (hf.restrictPreimage (frontier U)).comp
      exact (IsEmbedding.inclusion
        (hf.continuous.frontier_preimage_subset U)).isInducing

/-- The constructor characterization of a successor small-inductive-dimension
bound, exposed as an `iff` for use by dimension-lowering arguments. -/
theorem hasSmallInductiveDimensionLT_succ_iff (n : ℕ) :
    HasSmallInductiveDimensionLT X (n + 1) ↔
      ∃ b : Set (Set X), IsTopologicalBasis b ∧
        ∀ U ∈ b, HasSmallInductiveDimensionLT (frontier U) n := by
  constructor
  · intro h
    cases h with
    | succ _ b hb hfront => exact ⟨b, hb, hfront⟩
  · rintro ⟨b, hb, h⟩
    exact .succ n b hb h

/-- A successor dimension bound supplies a basis neighbourhood whose frontier
has the preceding strict bound. -/
theorem exists_isOpen_mem_subset_frontier_of_hasSmallInductiveDimensionLT
    {n : ℕ} (h : HasSmallInductiveDimensionLT X (n + 1))
    {x : X} {O : Set X} (hx : x ∈ O) (hO : IsOpen O) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      HasSmallInductiveDimensionLT (frontier U) n := by
  obtain ⟨b, hb, hfront⟩ := (hasSmallInductiveDimensionLT_succ_iff n).1 h
  obtain ⟨U, hUb, hxU, hUO⟩ := hb.exists_subset_of_mem_open hx hO
  exact ⟨U, hb.isOpen hUb, hxU, hUO, hfront U hUb⟩

/-- Local-neighbourhood characterization of a successor dimension bound. -/
theorem hasSmallInductiveDimensionLT_succ_iff_local (n : ℕ) :
    HasSmallInductiveDimensionLT X (n + 1) ↔
      ∀ (x : X) (O : Set X), x ∈ O → IsOpen O →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
          HasSmallInductiveDimensionLT (frontier U) n := by
  constructor
  · intro h x O hx hO
    exact exists_isOpen_mem_subset_frontier_of_hasSmallInductiveDimensionLT h hx hO
  · intro h
    let b : Set (Set X) :=
      {U | IsOpen U ∧ HasSmallInductiveDimensionLT (frontier U) n}
    have hb : IsTopologicalBasis b :=
      isTopologicalBasis_of_isOpen_of_nhds
        (fun U hU ↦ hU.1)
        (fun x O hx hO ↦ by
          obtain ⟨U, hUo, hxU, hUO, hUf⟩ := h x O hx hO
          exact ⟨U, ⟨hUo, hUf⟩, hxU, hUO⟩)
    exact .succ n b hb fun U hU ↦ hU.2

/-- In a regular space, the neighbourhood supplied by the dimension basis can
be chosen with closure contained in the prescribed open set. -/
theorem exists_isOpen_mem_closure_subset_frontier_of_hasSmallInductiveDimensionLT
    [RegularSpace X] {n : ℕ} (h : HasSmallInductiveDimensionLT X (n + 1))
    {x : X} {O : Set X} (hx : x ∈ O) (hO : IsOpen O) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ closure U ⊆ O ∧
      HasSmallInductiveDimensionLT (frontier U) n := by
  obtain ⟨W, hWn, hWc, hWO⟩ :=
    exists_mem_nhds_isClosed_subset (hO.mem_nhds hx)
  have hxW : x ∈ interior W := mem_interior_iff_mem_nhds.2 hWn
  obtain ⟨U, hUo, hxU, hUW, hUf⟩ :=
    exists_isOpen_mem_subset_frontier_of_hasSmallInductiveDimensionLT
      h hxW isOpen_interior
  refine ⟨U, hUo, hxU, ?_, hUf⟩
  exact (closure_minimal (hUW.trans interior_subset) hWc).trans hWO

/-- The complement of the frontier of an open set is the union of the set
and the complement of its closure.  These are the two open sides used by the
separator argument. -/
theorem isOpen_compl_frontier_eq_union_compl_closure
    {U : Set X} (hU : IsOpen U) :
    (frontier U)ᶜ = U ∪ (closure U)ᶜ := by
  rw [compl_frontier_eq_union_interior, hU.interior_eq, interior_compl]

/-- An open set and the complement of its closure form disjoint open sides
whose union is the complement of its frontier. -/
theorem isOpen_frontier_open_separation {U : Set X} (hU : IsOpen U) :
    IsOpen U ∧ IsOpen (closure U)ᶜ ∧
      Disjoint U (closure U)ᶜ ∧
      U ∪ (closure U)ᶜ = (frontier U)ᶜ := by
  refine ⟨hU, isClosed_closure.isOpen_compl, ?_,
    (isOpen_compl_frontier_eq_union_compl_closure hU).symm⟩
  exact Set.disjoint_left.2 fun _ hxU hxC ↦ hxC (subset_closure hxU)

/-- If both open sides of a frontier are inhabited, deleting that frontier
disconnects the ambient space. -/
theorem isOpen_not_isPreconnected_compl_frontier
    {U : Set X} (hU : IsOpen U) (hUn : U.Nonempty)
    (hUc : (closure U)ᶜ.Nonempty) :
    ¬ IsPreconnected (frontier U)ᶜ := by
  intro hpre
  have hsep := isOpen_frontier_open_separation hU
  have hsub : (frontier U)ᶜ ⊆ U ∪ (closure U)ᶜ := hsep.2.2.2.symm.subset
  have hleft : ((frontier U)ᶜ ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hUn
    refine ⟨x, ?_, hx⟩
    rw [← hsep.2.2.2]
    exact Or.inl hx
  have hright : ((frontier U)ᶜ ∩ (closure U)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hUc
    refine ⟨x, ?_, hx⟩
    rw [← hsep.2.2.2]
    exact Or.inr hx
  obtain ⟨x, _, hxU, hxC⟩ :=
    hpre U (closure U)ᶜ hsep.1 hsep.2.1 hsub hleft hright
  exact hxC (subset_closure hxU)

/-- A strict dimension bound in a regular space produces, between a point and
the exterior of a prescribed open set, a separator with the preceding strict
dimension bound. -/
theorem exists_low_dimensional_frontier_separator
    [RegularSpace X] {n : ℕ} (h : HasSmallInductiveDimensionLT X (n + 1))
    {x y : X} {O : Set X} (hx : x ∈ O) (hy : y ∉ O) (hO : IsOpen O) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ closure U ⊆ O ∧
      HasSmallInductiveDimensionLT (frontier U) n ∧
      ¬ IsPreconnected (frontier U)ᶜ := by
  obtain ⟨U, hUo, hxU, hUO, hdim⟩ :=
    exists_isOpen_mem_closure_subset_frontier_of_hasSmallInductiveDimensionLT
      h hx hO
  refine ⟨U, hUo, hxU, hUO, hdim,
    isOpen_not_isPreconnected_compl_frontier hUo ⟨x, hxU⟩ ?_⟩
  exact ⟨y, fun hyc ↦ hy (hUO hyc)⟩

/-- Relative basis transfer with an explicit ambient set controlling each
frontier.  The frontier of the trace on `s` need only be contained in the
trace of `F U`; equality is not required. -/
theorem subtype_hasSmallInductiveDimensionLT_of_basis_frontier_subset
    (s : Set X) (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (F : Set X → Set X)
    (hfront : ∀ U ∈ b, frontier U ⊆ F U)
    (hdim : ∀ U ∈ b,
      HasSmallInductiveDimensionLT (Subtype.val ⁻¹' F U : Set s) n) :
    HasSmallInductiveDimensionLT s (n + 1) := by
  refine .succ n _ (hb.isInducing IsInducing.subtypeVal) ?_
  rintro _ ⟨U, hU, rfl⟩
  apply inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion ?_).isInducing (hdim U hU)
  exact (continuous_subtype_val.frontier_preimage_subset U).trans
    (preimage_mono (hfront U hU))

/-- A recursive certificate allowing each basis frontier to be enlarged to a
more convenient controlling subspace.  It is tailored to a finite cutting
tree: terminal controlling spaces are empty, while each nonterminal node has
a basis whose frontiers lie in certified children. -/
inductive FrontierCertificate :
    ∀ (Z : Type u) [TopologicalSpace Z], ℕ → Prop where
  | zero {Z : Type u} [TopologicalSpace Z] [IsEmpty Z] :
      FrontierCertificate Z 0
  | succ {Z : Type u} [TopologicalSpace Z]
      (n : ℕ) (b : Set (Set Z)) (hb : IsTopologicalBasis b)
      (F : Set Z → Set Z)
      (hfront : ∀ (U : Set Z), U ∈ b → frontier U ⊆ F U)
      (hchild : ∀ (U : Set Z) (_hU : U ∈ b),
        FrontierCertificate (F U) n) :
      FrontierCertificate Z (n + 1)

/-- Every frontier certificate proves the corresponding strict dimension
bound. -/
theorem FrontierCertificate.hasSmallInductiveDimensionLT
    {Z : Type u} [TopologicalSpace Z] {n : ℕ}
    (h : FrontierCertificate Z n) : HasSmallInductiveDimensionLT Z n := by
  induction h with
  | zero => exact .zero
  | @succ Z _ n b hb F hfront hchild ih =>
      refine .succ n b hb ?_
      intro U hU
      exact inducing_hasSmallInductiveDimensionLT
        (IsEmbedding.inclusion (hfront U hU)).isInducing (ih U hU)

/-- Variant of `FrontierCertificate.hasSmallInductiveDimensionLT` for a
subspace: an ambient basis controls each relative frontier by a certified
ambient trace. -/
theorem subtype_hasSmallInductiveDimensionLT_of_frontierCertificates
    (s : Set X) (n : ℕ) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (F : Set X → Set X)
    (hfront : ∀ U ∈ b, frontier U ⊆ F U)
    (hcert : ∀ (U : Set X) (_hU : U ∈ b),
      FrontierCertificate (Subtype.val ⁻¹' F U : Set s) n) :
    HasSmallInductiveDimensionLT s (n + 1) := by
  refine .succ n _ (hb.isInducing IsInducing.subtypeVal) ?_
  rintro _ ⟨U, hU, rfl⟩
  apply inducing_hasSmallInductiveDimensionLT
    (IsEmbedding.inclusion ?_).isInducing
    (hcert U hU).hasSmallInductiveDimensionLT
  exact (continuous_subtype_val.frontier_preimage_subset U).trans
    (preimage_mono (hfront U hU))

end Erdos909.DimensionCore

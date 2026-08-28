import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Wikipedia.HopfProblem.CuspPositiveRetractionSublevel

/-!
# Finite patching of local collapses near a compact zero fibre

Each input is an actual global continuous homotopy which fixes the zero
fibre, does not increase the defining function, and collapses an open
set at time one.  Finite composition collapses an open neighborhood of
the entire compact zero fibre.  Restriction to a sufficiently small
compact sublevel then gives an actual strong deformation retraction.

The local homotopies remain explicit inputs to this generic patching
theorem; no global retraction, collar, or CW comparison is assumed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspRetraction.Patching

variable {X : Type*} [TopologicalSpace X]

/-- A constructed local collapse, extended continuously to the ambient
space and fixed on the entire zero fibre. -/
structure LocalCollapse (f : C(X, ℝ)) where
  homotopy : C(unitInterval × X, X)
  map_zero : ∀ x, homotopy (0, x) = x
  fixes_zero : ∀ s x, f x = 0 → homotopy (s, x) = x
  nonincreasing : ∀ s x, f (homotopy (s, x)) ≤ f x
  collapseSet : Set X
  isOpen_collapseSet : IsOpen collapseSet
  map_one_zero : ∀ x ∈ collapseSet, f (homotopy (1, x)) = 0

namespace LocalCollapse

variable {f : C(X, ℝ)}

/-- The neutral homotopy, with no open collapse set yet selected. -/
def identity (f : C(X, ℝ)) : LocalCollapse f where
  homotopy := ⟨Prod.snd, continuous_snd⟩
  map_zero _ := rfl
  fixes_zero _ _ _ := rfl
  nonincreasing _ _ := le_rfl
  collapseSet := ∅
  isOpen_collapseSet := isOpen_empty
  map_one_zero _ h := h.elim

/-- First apply `A` and then `B`, at the same homotopy parameter.
Points already collapsed by `A` are fixed by `B`; points sent by `A` into
the collapse set of `B` are collapsed by its endpoint. -/
def comp (A B : LocalCollapse f) : LocalCollapse f where
  homotopy :=
    ⟨fun p => B.homotopy (p.1, A.homotopy p),
      B.homotopy.continuous.comp (continuous_fst.prodMk A.homotopy.continuous)⟩
  map_zero x := by
    change B.homotopy (0, A.homotopy (0, x)) = x
    rw [A.map_zero, B.map_zero]
  fixes_zero s x hx := by
    change B.homotopy (s, A.homotopy (s, x)) = x
    rw [A.fixes_zero s x hx, B.fixes_zero s x hx]
  nonincreasing s x := (B.nonincreasing s (A.homotopy (s, x))).trans (A.nonincreasing s x)
  collapseSet := A.collapseSet ∪ (fun x => A.homotopy (1, x)) ⁻¹' B.collapseSet
  isOpen_collapseSet := A.isOpen_collapseSet.union
    (B.isOpen_collapseSet.preimage
      (A.homotopy.continuous.comp (continuous_const.prodMk continuous_id)))
  map_one_zero x hx := by
    change f (B.homotopy (1, A.homotopy (1, x))) = 0
    rcases hx with hx | hx
    · rw [B.fixes_zero 1 _ (A.map_one_zero x hx)]
      exact A.map_one_zero x hx
    · exact B.map_one_zero (A.homotopy (1, x)) hx

@[simp] theorem comp_homotopy (A B : LocalCollapse f) (s : unitInterval) (x : X) :
    (A.comp B).homotopy (s, x) = B.homotopy (s, A.homotopy (s, x)) := rfl

/-- On the zero fibre, the new collapse neighborhood contains both old
neighborhoods, even though the homotopies need not preserve them. -/
theorem mem_comp_collapseSet_of_zero (A B : LocalCollapse f) {x : X} (hx : f x = 0)
    (h : x ∈ A.collapseSet ∪ B.collapseSet) : x ∈ (A.comp B).collapseSet := by
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    change A.homotopy (1, x) ∈ B.collapseSet
    rwa [A.fixes_zero 1 x hx]

/-- The stagewise finite composition `Hₙ,s ∘ … ∘ H₁,s`. -/
def combine {ι : Type*} (A : ι → LocalCollapse f) : List ι → LocalCollapse f
  | [] => identity f
  | i :: l => (A i).comp (combine A l)

theorem mem_combine_collapseSet_of_zero {ι : Type*} (A : ι → LocalCollapse f)
    (l : List ι) {x : X} (hx : f x = 0) {i : ι} (hi : i ∈ l)
    (hxi : x ∈ (A i).collapseSet) : x ∈ (combine A l).collapseSet := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inl hxi)
    · exact mem_comp_collapseSet_of_zero (A a) (combine A l) hx (Or.inr (ih hi))

end LocalCollapse

/-- Compactness selects finitely many actual local collapses. Their
stagewise composition collapses an open neighborhood of the zero fibre. -/
theorem exists_localCollapse_covering_zero {f : C(X, ℝ)} {ι : Type*}
    (A : ι → LocalCollapse f) (hcompact : IsCompact {x : X | f x = 0})
    (hcover : {x : X | f x = 0} ⊆ ⋃ i, (A i).collapseSet) :
    ∃ B : LocalCollapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun i => (A i).collapseSet) (fun i => (A i).isOpen_collapseSet) hcover
  refine ⟨LocalCollapse.combine A s.toList, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  exact LocalCollapse.mem_combine_collapseSet_of_zero A s.toList hx
    (by simpa only [Finset.mem_toList] using hi) hxi

/-- The family may be supplied pointwise by genuinely constructed local
homotopies, with each collapse neighborhood containing its chosen point. -/
theorem exists_localCollapse_covering_zero_of_local {f : C(X, ℝ)}
    (hcompact : IsCompact {x : X | f x = 0})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ B : LocalCollapse f, {x : X | f x = 0} ⊆ B.collapseSet := by
  classical
  choose A hA using fun x : {x : X // f x = 0} => hlocal x x.2
  apply exists_localCollapse_covering_zero A hcompact
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x, hx⟩, hA ⟨x, hx⟩⟩

abbrev Sublevel (f : C(X, ℝ)) (η : ℝ) := {x : X // f x ≤ η}

abbrev ZeroSet (f : C(X, ℝ)) := {x : X // f x = 0}

/-- The actual inclusion of the zero fibre into a nonnegative sublevel. -/
def zeroInclusion (f : C(X, ℝ)) (η : ℝ) (hη : 0 ≤ η) : C(ZeroSet f, Sublevel f η) where
  toFun x := ⟨x.1, x.2.symm ▸ hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

namespace LocalCollapse

variable {f : C(X, ℝ)} (A : LocalCollapse f)

/-- Monotonicity keeps every stage inside the actual closed sublevel. -/
def sublevelDeformation (η : ℝ) : C(unitInterval × Sublevel f η, Sublevel f η) where
  toFun p := ⟨A.homotopy (p.1, p.2), (A.nonincreasing p.1 p.2).trans p.2.2⟩
  continuous_toFun := (A.homotopy.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp] theorem sublevelDeformation_coe (η : ℝ) (s : unitInterval) (x : Sublevel f η) :
    (A.sublevelDeformation η (s, x) : X) = A.homotopy (s, x) := rfl

@[simp] theorem sublevelDeformation_zero (η : ℝ) (x : Sublevel f η) :
    A.sublevelDeformation η (0, x) = x := Subtype.ext (A.map_zero x)

theorem sublevelDeformation_fixed (η : ℝ) (s : unitInterval) (x : Sublevel f η)
    (hx : f x = 0) : A.sublevelDeformation η (s, x) = x :=
  Subtype.ext (A.fixes_zero s x hx)

theorem sublevelDeformation_nonincreasing (η : ℝ) (s : unitInterval) (x : Sublevel f η) :
    f (A.sublevelDeformation η (s, x)) ≤ f x := A.nonincreasing s x

/-- Time one with codomain the actual zero fibre, once the sublevel is
contained in the constructed collapse neighborhood. -/
def sublevelRetraction {η : ℝ} (hA : {x : X | f x ≤ η} ⊆ A.collapseSet) :
    C(Sublevel f η, ZeroSet f) where
  toFun x := ⟨A.homotopy (1, x), A.map_one_zero x (hA x.2)⟩
  continuous_toFun := (A.homotopy.continuous.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

@[simp] theorem sublevelRetraction_comp_inclusion {η : ℝ}
    (hA : {x : X | f x ≤ η} ⊆ A.collapseSet) (hη : 0 ≤ η) :
    (A.sublevelRetraction hA).comp (zeroInclusion f η hη) = ContinuousMap.id (ZeroSet f) := by
  apply ContinuousMap.ext
  intro x
  exact Subtype.ext (A.fixes_zero 1 x x.2)

/-- The finite patching yields a genuine strong deformation retraction
in the subspace topology of the closed sublevel. -/
def sublevelStrongDeformationRetraction {η : ℝ}
    (hA : {x : X | f x ≤ η} ⊆ A.collapseSet) (hη : 0 ≤ η) :
    (ContinuousMap.id (Sublevel f η)).HomotopyRel
      ((zeroInclusion f η hη).comp (A.sublevelRetraction hA))
      (range (zeroInclusion f η hη)) where
  toFun p := A.sublevelDeformation η p
  continuous_toFun := (A.sublevelDeformation η).continuous
  map_zero_left := A.sublevelDeformation_zero η
  map_one_left _ := rfl
  prop' s x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact A.sublevelDeformation_fixed η s (zeroInclusion f η hη y) y.2

theorem sublevel_collapse_mono {η δ : ℝ}
    (hA : {x : X | f x ≤ η} ⊆ A.collapseSet) (hδη : δ ≤ η) :
    {x : X | f x ≤ δ} ⊆ A.collapseSet :=
  fun _ hx => hA (hx.trans hδη)

end LocalCollapse

/-- Local collapses near the zero fibre patch to one explicit global
homotopy which collapses an entire positive closed sublevel. Compactness
is required only for one initial positive sublevel. -/
theorem exists_small_sublevel_localCollapse (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
      ∃ A : LocalCollapse f, {x : X | f x ≤ η} ⊆ A.collapseSet := by
  obtain ⟨A, hA⟩ := exists_localCollapse_covering_zero_of_local
    (zeroSet_isCompact f hr hc) hlocal
  obtain ⟨η, hη, hηr, hηA⟩ := exists_positive_sublevel_subset_open f hf hr hc
    A.isOpen_collapseSet hA
  exact ⟨η, hη, hηr, A, hηA⟩

/-- The final local-to-global conclusion includes the actual retraction
and its relative homotopy on the original closed-sublevel subtype. -/
theorem exists_small_sublevel_strongDeformationRetraction (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r})
    (hlocal : ∀ x : X, f x = 0 → ∃ A : LocalCollapse f, x ∈ A.collapseSet) :
    ∃ (η : ℝ) (hη : 0 < η), η ≤ r ∧
      ∃ R : C(Sublevel f η, ZeroSet f),
        R.comp (zeroInclusion f η hη.le) = ContinuousMap.id (ZeroSet f) ∧
          Nonempty ((ContinuousMap.id (Sublevel f η)).HomotopyRel
            ((zeroInclusion f η hη.le).comp R) (range (zeroInclusion f η hη.le))) := by
  obtain ⟨η, hη, hηr, A, hA⟩ := exists_small_sublevel_localCollapse f hf hr hc hlocal
  exact ⟨η, hη, hηr, A.sublevelRetraction hA,
    A.sublevelRetraction_comp_inclusion hA hη.le,
    ⟨A.sublevelStrongDeformationRetraction hA hη.le⟩⟩

end Wikipedia.HopfProblem.CuspRetraction.Patching

import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport
import Mathlib.Topology.Sets.Opens

/-!
# Based paths for a genuine two-open-set cover

For path-connected open sets with path-connected intersection, choose
paths from the common basepoint which lie in both sets whenever their
endpoint does.  These are actual paths in the given topological space.
They allow compatible homomorphisms on the two fundamental groups to
be compared along every path in the overlap.
-/

noncomputable section

open Set TopologicalSpace
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X]

/-- The standard hypotheses of the based two-open-set van Kampen theorem. -/
structure TwoOpenCover (X : Type*) [TopologicalSpace X] where
  U : Opens X
  V : Opens X
  cover : (U : Set X) ∪ V = univ
  pathConnectedU : IsPathConnected (U : Set X)
  pathConnectedV : IsPathConnected (V : Set X)
  pathConnectedIntersection : IsPathConnected ((U : Set X) ∩ V)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

namespace TwoOpenCover

variable (D : TwoOpenCover X)

abbrev chart : Bool → Opens X
  | false => D.U
  | true => D.V

theorem base_mem_chart (i : Bool) : D.base ∈ D.chart i := by
  cases i
  · exact D.baseU
  · exact D.baseV

theorem chart_open (i : Bool) : IsOpen (D.chart i : Set X) := (D.chart i).isOpen

theorem chart_cover : ⋃ i, (D.chart i : Set X) = univ := by
  apply subset_antisymm (subset_univ _)
  intro x _
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨false, hx⟩
  · exact mem_iUnion.mpr ⟨true, hx⟩

theorem mem_U_or_V (x : X) : x ∈ D.U ∨ x ∈ D.V := by
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact hx

def rawPathTo (x : X) : Path D.base x := by
  classical
  exact if h : x ∈ (D.U : Set X) ∩ D.V then
    (D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath
  else if hU : x ∈ D.U then
    (D.pathConnectedU.joinedIn D.base D.baseU x hU).somePath
  else
    (D.pathConnectedV.joinedIn D.base D.baseV x ((D.mem_U_or_V x).resolve_left hU)).somePath

theorem rawPathTo_mem (i : Bool) (x : X) (hx : x ∈ D.chart i) (t : I) :
    D.rawPathTo x t ∈ D.chart i := by
  classical
  cases i with
  | false =>
      change D.rawPathTo x t ∈ D.U
      change x ∈ D.U at hx
      unfold rawPathTo
      by_cases h : x ∈ (D.U : Set X) ∩ D.V
      · rw [dif_pos h]
        exact ((D.pathConnectedIntersection.joinedIn D.base
          ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).1
      · rw [dif_neg h, dif_pos hx]
        exact JoinedIn.somePath_mem _ t
  | true =>
      change D.rawPathTo x t ∈ D.V
      change x ∈ D.V at hx
      unfold rawPathTo
      by_cases h : x ∈ (D.U : Set X) ∩ D.V
      · rw [dif_pos h]
        exact ((D.pathConnectedIntersection.joinedIn D.base
          ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).2
      · have hnU : x ∉ D.U := fun hU => h ⟨hU, hx⟩
        rw [dif_neg h, dif_neg hnU]
        exact JoinedIn.somePath_mem _ t

/-- Coherent based paths, normalized to the constant path at the basepoint. -/
def pathTo (x : X) : Path D.base x := by
  classical
  exact if h : x = D.base then (Path.refl D.base).cast rfl h else D.rawPathTo x

@[simp] theorem pathTo_base : D.pathTo D.base = Path.refl D.base := by
  classical
  simp [pathTo]

theorem pathTo_mem (i : Bool) (x : X) (hx : x ∈ D.chart i) (t : I) :
    D.pathTo x t ∈ D.chart i := by
  classical
  unfold pathTo
  split_ifs
  · exact D.base_mem_chart i
  · exact D.rawPathTo_mem i x hx t

/-- The actual intersection, with the subspace topology. -/
abbrev overlap : Opens X := D.U ⊓ D.V

abbrev baseUPoint : D.U := ⟨D.base, D.baseU⟩
abbrev baseVPoint : D.V := ⟨D.base, D.baseV⟩
abbrev baseOverlapPoint : D.overlap := ⟨D.base, D.baseU, D.baseV⟩
abbrev baseChart (i : Bool) : D.chart i := ⟨D.base, D.base_mem_chart i⟩

abbrev UGroup := FundamentalGroup D.U D.baseUPoint
abbrev VGroup := FundamentalGroup D.V D.baseVPoint
abbrev OverlapGroup := FundamentalGroup D.overlap D.baseOverlapPoint

def overlapToU : C(D.overlap, D.U) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def overlapToV : C(D.overlap, D.V) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def inclusionU : C(D.U, X) := ⟨Subtype.val, continuous_subtype_val⟩
def inclusionV : C(D.V, X) := ⟨Subtype.val, continuous_subtype_val⟩

def overlapHomU : D.OverlapGroup →* D.UGroup :=
  FundamentalGroup.map D.overlapToU D.baseOverlapPoint

def overlapHomV : D.OverlapGroup →* D.VGroup :=
  FundamentalGroup.map D.overlapToV D.baseOverlapPoint

def inclusionHomU : D.UGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionU D.baseUPoint

def inclusionHomV : D.VGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionV D.baseVPoint

/-- The two actual inclusion homomorphisms agree on the intersection. -/
theorem inclusionHom_compatible :
    D.inclusionHomU.comp D.overlapHomU = D.inclusionHomV.comp D.overlapHomV := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- The usual compatibility condition, on actual fundamental groups of the overlap. -/
def Compatible {G : Type*} [Group G] (fU : D.UGroup →* G) (fV : D.VGroup →* G) : Prop :=
  fU.comp D.overlapHomU = fV.comp D.overlapHomV

end TwoOpenCover

end Wikipedia.HopfProblem.FundamentalGroupVanKampen

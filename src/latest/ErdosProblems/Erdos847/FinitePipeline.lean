/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos847.SparseLines
import ErdosProblems.Erdos847.Iteration
import ErdosProblems.Erdos847.Confinement
import ErdosProblems.Erdos847.TriangleAdapter
import ErdosProblems.Erdos847.PictureOutput

/-!
# Finite pipeline for Erdős 847

This module is the integration seam from the sparse Hales--Jewett theorem to
the iterated final picture and then to the encoded integer block.  While the
final sparse-selection and confinement theorems are being completed, the
fully concrete adapters are developed here.
-/

namespace Erdos847FinitePipeline

open Function Set Combinatorics
open Erdos847Pictures Erdos847Iteration
open Erdos847SparseLines
open Erdos847Confinement

set_option autoImplicit false

variable {V : Type} [DecidableEq V]
variable {G : ThreeGraph V}
variable {P C K : Type}

/-! ## Adapting a concrete sparse cube family -/

/-- A concrete sparse Hales--Jewett line system supplies the abstract family
interface used by the focusing layer. -/
theorem sparseFiberLineFamilyOf_nonempty
    (picture : Picture G P C) (x : V) (K : Type)
    [Nontrivial (Fiber picture x)]
    (h : SparseHalesJewett (Fiber picture x) K) :
    Nonempty (SparseFiberLineFamily picture x K) := by
  classical
  rcases h with ⟨N, hN, S, hsparse, hramsey⟩
  let : Fintype N := hN
  let movingSupport : {U // U ∈ S} → Set N := fun U ↦
    (Erdos847SparseLines.movingSet U.1 : Set N)
  refine ⟨{
    Word := N → Fiber picture x
    Index := {U // U ∈ S}
    Move := N
    line := fun U ↦ U.1
    movingSupport := movingSupport
    line_injective := fun U ↦ line_apply_injective U.1
    highChromatic := ?_
    noTripod := ?_
    noTriangle := ?_
  }⟩
  · intro color
    obtain ⟨U, hUS, k, hk⟩ := hramsey color
    exact ⟨⟨U, hUS⟩, k, hk⟩
  · intro htripod
    apply hsparse.1
    rcases htripod with
      ⟨U, W, Z, hUW, hWZ, hZU, ⟨q, hqU, hqW, hqZ⟩, hmove, hdisj⟩
    have hUW' : U.1 ≠ W.1 := fun h ↦ hUW (Subtype.ext h)
    have hWZ' : W.1 ≠ Z.1 := fun h ↦ hWZ (Subtype.ext h)
    have hZU' : Z.1 ≠ U.1 := fun h ↦ hZU (Subtype.ext h)
    have hmove' : Erdos847SparseLines.movingSet U.1 =
        Erdos847SparseLines.movingSet W.1 ∪
          Erdos847SparseLines.movingSet Z.1 := by
      ext s
      have hs := Set.ext_iff.mp hmove s
      simpa [movingSupport] using hs
    have hdisj' : Disjoint (Erdos847SparseLines.movingSet W.1)
        (Erdos847SparseLines.movingSet Z.1) := by
      rw [Finset.disjoint_left]
      intro s hsW hsZ
      exact Set.disjoint_left.mp hdisj
        (by simpa [movingSupport] using hsW)
        (by simpa [movingSupport] using hsZ)
    exact ⟨U.1, U.2, W.1, W.2, Z.1, Z.2,
      hUW', hWZ', hZU', ⟨q, hqU, hqW, hqZ⟩, hmove', hdisj'⟩
  · intro htriangle
    apply hsparse.2
    rcases htriangle with
      ⟨U, W, Z, hUW, hWZ, hZU, hUWmeet, hWZmeet, hZUmeet, hempty⟩
    exact ⟨U.1, U.2, W.1, W.2, Z.1, Z.2,
      (fun h ↦ hUW (Subtype.ext h)),
      (fun h ↦ hWZ (Subtype.ext h)),
      (fun h ↦ hZU (Subtype.ext h)),
      hUWmeet, hWZmeet, hZUmeet, hempty⟩

/-- Choice of the concrete adapter packaged by the preceding propositional
existence theorem. -/
noncomputable def sparseFiberLineFamilyOf
    (picture : Picture G P C) (x : V) (K : Type)
    [Nontrivial (Fiber picture x)]
    (h : SparseHalesJewett (Fiber picture x) K) :
    SparseFiberLineFamily picture x K :=
  Classical.choice (sparseFiberLineFamilyOf_nonempty picture x K h)

/-! ## Translating the finite sparse predicates to raw line systems -/

theorem rawLineSystemHasNoTripod_of_isSparse
    {A N : Type} [Fintype N] (S : Finset (Line A N)) (hS : IsSparse S) :
    RawLineSystemHasNoTripod (S : Set (Line A N)) := by
  classical
  intro U W Z hU hW hZ hraw
  rcases hraw with ⟨hUW, hUZ, hWZ, hcommon, hmoving⟩
  have forbidden (L₀ L₁ L₂ : Line A N)
      (hL₀ : L₀ ∈ S) (hL₁ : L₁ ∈ S) (hL₂ : L₂ ∈ S)
      (h₀₁ : L₀ ≠ L₁) (h₁₂ : L₁ ≠ L₂) (h₂₀ : L₂ ≠ L₀)
      (hc : RawLinesCommonPoint L₀ L₁ L₂)
      (hm : RawMovingDisjointUnion L₀ L₁ L₂) : False := by
    apply hS.1
    rcases hc with ⟨a, b, c, hab, hbc⟩
    have hmove : Erdos847SparseLines.movingSet L₀ =
        Erdos847SparseLines.movingSet L₁ ∪
          Erdos847SparseLines.movingSet L₂ := by
      ext s
      have hs := Set.ext_iff.mp hm.1 s
      simpa [RawMovingSet, Erdos847SparseLines.movingSet] using hs
    have hdisj : Disjoint (Erdos847SparseLines.movingSet L₁)
        (Erdos847SparseLines.movingSet L₂) := by
      rw [Finset.disjoint_left]
      intro s hs₁ hs₂
      exact Set.disjoint_left.mp hm.2
        (by simpa [RawMovingSet, Erdos847SparseLines.movingSet] using hs₁)
        (by simpa [RawMovingSet, Erdos847SparseLines.movingSet] using hs₂)
    exact ⟨L₀, hL₀, L₁, hL₁, L₂, hL₂, h₀₁, h₁₂, h₂₀,
      ⟨L₀ a, ⟨a, rfl⟩, ⟨b, hab.symm⟩, ⟨c, (hab.trans hbc).symm⟩⟩,
      hmove, hdisj⟩
  rcases hmoving with hm | hm | hm
  · exact forbidden U W Z hU hW hZ hUW hWZ (fun h ↦ hUZ h.symm) hcommon hm
  · have hc : RawLinesCommonPoint W U Z := by
      rcases hcommon with ⟨a, b, c, hab, hbc⟩
      exact ⟨b, a, c, hab.symm, hab.trans hbc⟩
    exact forbidden W U Z hW hU hZ (fun h ↦ hUW h.symm) hUZ
      (Ne.symm hWZ) hc hm
  · have hc : RawLinesCommonPoint Z U W := by
      rcases hcommon with ⟨a, b, c, hab, hbc⟩
      exact ⟨c, a, b, (hab.trans hbc).symm, hab⟩
    exact forbidden Z U W hZ hU hW (fun h ↦ hUZ h.symm) hUW hWZ hc hm

theorem rawLineSystemHasNoTriangle_of_isSparse
    {A N : Type} [Fintype N] (S : Finset (Line A N)) (hS : IsSparse S) :
    RawLineSystemHasNoTriangle (S : Set (Line A N)) := by
  classical
  intro U W Z hU hW hZ hraw
  apply hS.2
  rcases hraw with ⟨hUW, hUZ, hWZ, hUWmeet, hUZmeet, hWZmeet, hcommon⟩
  have meet {L M : Line A N} (h : RawLinesIntersect L M) :
      (linePoints L ∩ linePoints M).Nonempty := by
    rcases h with ⟨a, b, hab⟩
    exact ⟨L a, ⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
  have hempty : linePoints U ∩ linePoints W ∩ linePoints Z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩
    apply hcommon
    exact ⟨a, b, c, ha.trans hb.symm, hb.trans hc.symm⟩
  have hZUmeet : RawLinesIntersect Z U := by
    rcases hUZmeet with ⟨a, b, hab⟩
    exact ⟨b, a, hab.symm⟩
  exact ⟨U, hU, W, hW, Z, hZ, hUW, hWZ, (fun h ↦ hUZ h.symm),
    meet hUWmeet, meet hWZmeet, meet hZUmeet, hempty⟩

/-! ## The concrete one-fiber extension, parameterized only by confinement -/

/-- Expanding a cube word over the music fiber into coordinate blocks. -/
def expandFiberWord (source : Picture G P C) (x : V) {N : Type*}
    (w : N → Fiber source x) : N × C → Alphabet :=
  fun sc ↦ source.embed (w sc.1).1 sc.2

/-- On a selected outer line, block expansion is exactly `extendWord` of a
fiber point. -/
theorem expandFiberWord_line (source : Picture G P C) (x : V) {N : Type*}
    (U : Line (Fiber source x) N) (a : Fiber source x) :
    expandFiberWord source x (U a) = extendWord source x U a.1 := by
  funext sc
  simp only [expandFiberWord, extendWord]
  cases hs : U.idxFun sc.1 with
  | none => simp [Line.coe_apply, sectionPoint, hs]
  | some f => simp [Line.coe_apply, sectionPoint, hs]

/-- Build the actual raw partite amalgamation from one concrete sparse line
system.  The difficult incidence theorem appears only as `hconf`; every other
field of `FiberExtension` is discharged here. -/
noncomputable def rawFiberExtensionOfSystem
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    {N : Type} [Fintype N]
    (picture : Picture G P C) (x : V)
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (S : Finset (Line (Fiber picture x) N))
    (hramsey : IsRamseyFamily S K)
    (hconf : EveryQuasilineConfined picture
      (rawAmalgamationData picture x (S : Set (Line (Fiber picture x) N)))) :
    FiberExtension picture x K := by
  classical
  let lineSet : Set (Line (Fiber picture x) N) := S
  let data := rawAmalgamationData picture x lineSet
  let target := amalgamationPicture picture data (by simpa [data, lineSet] using hconf)
  letI : Fintype (RawAmalgamPoint picture x lineSet) := Fintype.ofFinite _
  letI : Fintype (N × C) := inferInstance
  letI : Inhabited K :=
    Classical.inhabited_of_nonempty (inferInstance : Nonempty K)
  have hcopy (U : Line (Fiber picture x) N) (hU : U ∈ S) :
      StandardCopy picture target (standardCopy picture x lineSet U (by simpa [lineSet] using hU)) := by
    refine {
      injective := standardCopy_injective picture x lineSet U _
      proj_copy := ?_
      transports_lines := ?_
    }
    · intro p
      change rawProj picture x lineSet
        (standardCopy picture x lineSet U _ p) = picture.proj p
      exact rawProj_standardCopy picture x lineSet U
        (by simpa [lineSet] using hU) p
    · intro l hl
      change IsCombinatorialLine (rawEmbed picture x lineSet)
        (fun a ↦ standardCopy picture x lineSet U _ (l a))
      exact standardCopy_transports_line picture x lineSet U
        (by simpa [lineSet] using hU) l hl
  have hSne : S.Nonempty := by
    obtain ⟨U, hUS, -⟩ := hramsey (fun _ ↦ default)
    exact ⟨U, hUS⟩
  refine {
    Point := RawAmalgamPoint picture x lineSet
    Coord := N × C
    pointFintype := inferInstance
    coordFintype := inferInstance
    target := target
    targetFiberNontrivial := ?_
    focus := ?_
  }
  · obtain ⟨U₀, hU₀⟩ := hSne
    intro y
    exact (hcopy U₀ hU₀).targetFiberNontrivial sourceFiberNontrivial y
  · intro color
    let cubeColor : (N → Fiber picture x) → K := fun w ↦
      if hw : IsAmalgamWord picture x lineSet (expandFiberWord picture x w)
      then color ⟨expandFiberWord picture x w, hw⟩
      else default
    obtain ⟨U, hUS, k, hk⟩ := hramsey cubeColor
    have hUS' : U ∈ lineSet := by simpa [lineSet] using hUS
    refine ⟨standardCopy picture x lineSet U hUS', hcopy U hUS, k, ?_⟩
    intro p hp
    let a : Fiber picture x := ⟨p, hp⟩
    have hw : IsAmalgamWord picture x lineSet
        (expandFiberWord picture x (U a)) := by
      exact ⟨U, hUS', a.1, expandFiberWord_line picture x U a⟩
    have hpoint :
        (⟨expandFiberWord picture x (U a), hw⟩ :
          RawAmalgamPoint picture x lineSet) =
          standardCopy picture x lineSet U hUS' p := by
      apply Subtype.ext
      exact expandFiberWord_line picture x U a
    have hmono := hk a
    simpa only [cubeColor, dif_pos hw, hpoint] using hmono

/-- Once a confinement theorem is available uniformly for sparse systems,
the sparse Hales--Jewett theorem and the raw constructor produce a one-fiber
extension.  The result is first built under `Nonempty` because the sparse
theorem is proposition-valued. -/
theorem oneFiberExtensionOfConfinement_nonempty
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    (picture : Picture G P C) (x : V)
    [Nontrivial (Fiber picture x)]
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (confinement : ∀ {N : Type} [Fintype N]
      (S : Finset (Line (Fiber picture x) N)), IsSparse S →
        EveryQuasilineConfined picture
          (rawAmalgamationData picture x (S : Set (Line (Fiber picture x) N)))) :
    Nonempty (FiberExtension picture x K) := by
  classical
  rcases sparse_hales_jewett (Fiber picture x) K with
    ⟨N, hN, S, hsparse, hramsey⟩
  let : Fintype N := hN
  exact ⟨rawFiberExtensionOfSystem picture x sourceFiberNontrivial S hramsey
    (confinement S hsparse)⟩

/-- Chosen one-fiber extension supplied by sparse Hales--Jewett and a uniform
confinement theorem. -/
noncomputable def oneFiberExtensionOfConfinement
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    (picture : Picture G P C) (x : V)
    [Nontrivial (Fiber picture x)]
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (confinement : ∀ {N : Type} [Fintype N]
      (S : Finset (Line (Fiber picture x) N)), IsSparse S →
        EveryQuasilineConfined picture
          (rawAmalgamationData picture x (S : Set (Line (Fiber picture x) N)))) :
    FiberExtension picture x K :=
  Classical.choice <| oneFiberExtensionOfConfinement_nonempty picture x
    sourceFiberNontrivial confinement

/-- The actual one-fiber step used by the finite iteration.  The abstract
family parameter is the certificate consumed by the focusing API; the raw
amalgamation selects a concrete sparse Hales--Jewett system and confines it
using linearity of the base together with the sparse tripod/triangle
exclusions. -/
noncomputable def oneFiberAmalgamate
    [Fintype P] [Fintype C] [Fintype K] [Nonempty K]
    (hlinear : G.Linear)
    (picture : Picture G P C)
    (sourceFiberNontrivial : ∀ y : V, Nontrivial (Fiber picture y))
    (x : V) [Nontrivial (Fiber picture x)]
    (_lines : SparseFiberLineFamily picture x K) :
    FiberExtension picture x K :=
  oneFiberExtensionOfConfinement picture x sourceFiberNontrivial <| by
    intro N _ S hS
    exact raw_everyQuasilineConfined_of_sparse_linear picture x
      (S : Set (Line (Fiber picture x) N)) hlinear
      (rawLineSystemHasNoTripod_of_isSparse S hS)
      (rawLineSystemHasNoTriangle_of_isSparse S hS)

/-- Uniform choice of the abstract sparse family required by the iterator. -/
noncomputable def sparseFamily
    [Fintype P] [Fintype C] [Fintype K]
    (picture : Picture G P C) (x : V)
    [Nontrivial (Fiber picture x)] :
    SparseFiberLineFamily picture x K :=
  sparseFiberLineFamilyOf picture x K
    (sparse_hales_jewett (Fiber picture x) K)

/-! ## Initial-picture finite and fiber instances -/

/-- A vertex lying in two distinct base edges has two distinct points in the
corresponding fiber of picture zero. -/
theorem pictureZero_fiber_nontrivial_of_two_incident
    [Fintype V]
    (hincident : ∀ v : V, ∃ e f : G.Edge, e ≠ f ∧ v ∈ e.1 ∧ v ∈ f.1)
    (v : V) :
    Nontrivial (Fiber (pictureZero G) v) := by
  obtain ⟨e, f, hef, hve, hvf⟩ := hincident v
  let a : Alphabet := (G.edgeEquiv e).symm ⟨v, hve⟩
  let b : Alphabet := (G.edgeEquiv f).symm ⟨v, hvf⟩
  let pa : Fiber (pictureZero G) v := ⟨(e, a), by
    simp [pictureZero, zeroProj, a]⟩
  let pb : Fiber (pictureZero G) v := ⟨(f, b), by
    simp [pictureZero, zeroProj, b]⟩
  exact ⟨⟨pa, pb, fun h ↦ hef (congrArg (fun p ↦ p.1.1) h)⟩⟩

/-! ## Complete finite RRS block -/

/-- For every positive finite color count there is a finite integer block
which is Ramsey for nontrivial three-term arithmetic progressions, while
every subset has a three-AP-free subset of at least one third its size. -/
theorem exists_finite_rrs_block (r : ℕ) (hr : 0 < r) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧
          (Z.card : ℝ) ≥ (1 / 3 : ℝ) * Y.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  classical
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨N, hN, hRamsey, hFractional, hlinear⟩ :=
    Erdos847TriangleAdapter.exists_triangleBase_package r
  let base := Erdos847TriangleAdapter.triangleGraph N
  let source := Erdos847TriangleAdapter.doubledPictureZero base
  have hsourceFibers : ∀ x : Erdos847TriangleAdapter.Vertex N,
      Nontrivial (Fiber source x) := by
    intro x
    exact Erdos847TriangleAdapter.doubledTrianglePicture_fiber_nontrivial hN x
  have hrealizes : RealizesEveryEdge source := by
    exact Erdos847TriangleAdapter.doubledPictureZero_realizesEveryEdge base
  obtain ⟨Q, D, hQ, hD, final, hfinalFibers, hfinalRamsey⟩ :=
    exists_ramsey_final_picture source (Fin r) hsourceFibers hrealizes hRamsey
      (fun picture x ↦ sparseFamily picture x)
      (fun picture sourceFibers x _ lines ↦
        oneFiberAmalgamate hlinear picture sourceFibers x lines)
  let : Fintype Q := hQ
  let : Fintype D := hD
  exact Erdos847PictureOutput.exists_encoded_block_one_third_of_finite_coords
    final hr hfinalRamsey hFractional

end Erdos847FinitePipeline

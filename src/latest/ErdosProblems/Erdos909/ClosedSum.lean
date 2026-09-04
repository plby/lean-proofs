/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos909.DimensionCore
import ErdosProblems.Erdos909.MetricSubspaceLift
import ErdosProblems.Erdos909.ZeroDimensionalRefinement
import Mathlib.Topology.Separation.DisjointCover

/-!
# Closed sums for small inductive dimension

This file begins the countable closed-sum argument used in the
Anderson--Keisler lower bound.  The main result proved here is the difficult
base case: a second-countable pseudometrizable space covered by countably many
closed zero-dimensional subspaces is zero-dimensional.  The proof is the
classical recursive separation proof (the base case of `TOPDIM_2:3` in the
Mizar Mathematical Library).
-/

open Set Topology TopologicalSpace

namespace Erdos909.ClosedSum

universe u

variable {X : Type u} [PseudoMetricSpace X]

private theorem exists_open_supersets_disjoint_closure
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      Disjoint (closure U) (closure V) := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hAU₀, hBV₀, hU₀V₀⟩ :=
    normal_separation hA hB hAB
  obtain ⟨U, hU, hAU, hUc⟩ := normal_exists_closure_subset hA hU₀ hAU₀
  obtain ⟨V, hV, hBV, hVc⟩ := normal_exists_closure_subset hB hV₀ hBV₀
  exact ⟨U, V, hU, hV, hAU, hBV, hU₀V₀.mono hUc hVc⟩

/-- A pair of open sets, containing two fixed closed sets, whose closures are
disjoint.  Packaging the invariant makes the countable recursion below
straightforward. -/
private structure SeparationStage (A B : Set X) where
  left : Set X
  right : Set X
  isOpen_left : IsOpen left
  isOpen_right : IsOpen right
  A_subset : A ⊆ left
  B_subset : B ⊆ right
  disjoint_closure : Disjoint (closure left) (closure right)

private theorem exists_initialStage
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) : Nonempty (SeparationStage A B) := by
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    exists_open_supersets_disjoint_closure hA hB hAB
  exact ⟨⟨U, V, hU, hV, hAU, hBV, hUV⟩⟩

private theorem disjoint_four_unions
    {A₀ A₁ B₀ B₁ : Set X}
    (h₀₀ : Disjoint A₀ B₀) (h₀₁ : Disjoint A₀ B₁)
    (h₁₀ : Disjoint A₁ B₀) (h₁₁ : Disjoint A₁ B₁) :
    Disjoint (A₀ ∪ A₁) (B₀ ∪ B₁) := by
  rw [Set.disjoint_left]
  rintro x (hx₀ | hx₁) (hy₀ | hy₁)
  · exact Set.disjoint_left.mp h₀₀ hx₀ hy₀
  · exact Set.disjoint_left.mp h₀₁ hx₀ hy₁
  · exact Set.disjoint_left.mp h₁₀ hx₁ hy₀
  · exact Set.disjoint_left.mp h₁₁ hx₁ hy₁

/-- Extend a separated open pair so that it covers one more closed
zero-dimensional layer. -/
private theorem SeparationStage.extend_across_closed_zeroDimensional
    [SecondCountableTopology X]
    {A B F : Set X} (s : SeparationStage A B)
    (hFclosed : IsClosed F)
    (hFzero : HasSmallInductiveDimensionLT F 1) :
    ∃ t : SeparationStage A B,
      closure s.left ⊆ t.left ∧ closure s.right ⊆ t.right ∧
        F ⊆ t.left ∪ t.right := by
  let D₀ : Set F := Subtype.val ⁻¹' closure s.left
  let D₁ : Set F := Subtype.val ⁻¹' closure s.right
  have hD₀c : IsClosed D₀ := isClosed_closure.preimage continuous_subtype_val
  have hD₁c : IsClosed D₁ := isClosed_closure.preimage continuous_subtype_val
  have hDdisj : Disjoint D₀ D₁ := s.disjoint_closure.preimage Subtype.val
  let U : Bool → Set F := fun i ↦ if i = false then D₁ᶜ else D₀ᶜ
  have hUopen (i : Bool) : IsOpen (U i) := by
    cases i <;> simp [U, hD₀c.isOpen_compl, hD₁c.isOpen_compl]
  have hUcover : ⋃ i, U i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hx : x ∈ D₀
    · exact ⟨false, by simpa [U] using hDdisj.notMem_of_mem_left hx⟩
    · exact ⟨true, by simpa [U] using hx⟩
  obtain ⟨C, hCclopen, hCpair, hCcover, hCsub⟩ :=
    ZeroDimensionalRefinement.exists_disjoint_clopen_refinement
      hFzero U hUopen hUcover
  have hD₀C : D₀ ⊆ C false := by
    intro x hx
    have hxcover : x ∈ ⋃ i, C i := by rw [hCcover]; exact mem_univ x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxcover
    cases i with
    | false => exact hxi
    | true =>
        exact (hCsub true hxi hx).elim
  have hD₁C : D₁ ⊆ C true := by
    intro x hx
    have hxcover : x ∈ ⋃ i, C i := by rw [hCcover]; exact mem_univ x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxcover
    cases i with
    | false =>
        exact (hCsub false hxi hx).elim
    | true => exact hxi
  let E₀ : Set X := Subtype.val '' C false
  let E₁ : Set X := Subtype.val '' C true
  have hE₀c : IsClosed E₀ :=
    hFclosed.isClosedEmbedding_subtypeVal.isClosedMap _ (hCclopen false).isClosed
  have hE₁c : IsClosed E₁ :=
    hFclosed.isClosedEmbedding_subtypeVal.isClosedMap _ (hCclopen true).isClosed
  have hEdisj : Disjoint E₀ E₁ := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
    have hyz : y = z := Subtype.ext heq.symm
    exact Set.disjoint_left.mp (hCpair Bool.false_ne_true) hy (hyz ▸ hz)
  have hleftE₁ : Disjoint (closure s.left) E₁ := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    have hyD : y ∈ D₀ := hx
    exact Set.disjoint_left.mp (hCpair Bool.false_ne_true)
      (hD₀C hyD) hy
  have hE₀right : Disjoint E₀ (closure s.right) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ hx
    have hyD : y ∈ D₁ := hx
    exact Set.disjoint_left.mp (hCpair Bool.false_ne_true) hy (hD₁C hyD)
  have hbigdisj :
      Disjoint (closure s.left ∪ E₀) (closure s.right ∪ E₁) :=
    disjoint_four_unions s.disjoint_closure hleftE₁ hE₀right hEdisj
  obtain ⟨G, H, hG, hH, hsubG, hsubH, hGH⟩ :=
    exists_open_supersets_disjoint_closure
      (isClosed_closure.union hE₀c) (isClosed_closure.union hE₁c) hbigdisj
  let t : SeparationStage A B :=
    ⟨G, H, hG, hH,
      s.A_subset.trans (subset_closure.trans (subset_union_left.trans hsubG)),
      s.B_subset.trans (subset_closure.trans (subset_union_left.trans hsubH)), hGH⟩
  refine ⟨t, subset_union_left.trans hsubG, subset_union_left.trans hsubH, ?_⟩
  intro x hxF
  have hycover : (⟨x, hxF⟩ : F) ∈ ⋃ i, C i := by
    rw [hCcover]
    exact mem_univ _
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hycover
  cases i with
  | false =>
      exact Or.inl (hsubG (Or.inr ⟨⟨x, hxF⟩, hxi, rfl⟩))
  | true =>
      exact Or.inr (hsubH (Or.inr ⟨⟨x, hxF⟩, hxi, rfl⟩))

/-- The zero-dimensional countable closed-sum theorem, in separation form. -/
private theorem exists_clopen_separating_of_closed_iUnion
    [SecondCountableTopology X]
    (F : ℕ → Set X) (hFclosed : ∀ i, IsClosed (F i))
    (hFzero : ∀ i, HasSmallInductiveDimensionLT (F i) 1)
    (hFcover : ⋃ i, F i = univ)
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ C : Set X, IsClopen C ∧ A ⊆ C ∧ B ⊆ Cᶜ := by
  classical
  let s₀ : SeparationStage A B :=
    Classical.choice (exists_initialStage hA hB hAB)
  let next (i : ℕ) (s : SeparationStage A B) : SeparationStage A B :=
    Classical.choose (s.extend_across_closed_zeroDimensional
      (hFclosed i) (hFzero i))
  have next_spec (i : ℕ) (s : SeparationStage A B) :
      closure s.left ⊆ (next i s).left ∧
      closure s.right ⊆ (next i s).right ∧
      F i ⊆ (next i s).left ∪ (next i s).right :=
    Classical.choose_spec (s.extend_across_closed_zeroDimensional
      (hFclosed i) (hFzero i))
  let stages : ℕ → SeparationStage A B :=
    fun n ↦ Nat.rec s₀ (fun i s ↦ next i s) n
  have hstep_left (i : ℕ) : closure (stages i).left ⊆ (stages (i + 1)).left := by
    simpa [stages] using (next_spec i (stages i)).1
  have hstep_right (i : ℕ) : closure (stages i).right ⊆ (stages (i + 1)).right := by
    simpa [stages] using (next_spec i (stages i)).2.1
  have hstep_cover (i : ℕ) :
      F i ⊆ (stages (i + 1)).left ∪ (stages (i + 1)).right := by
    simpa [stages] using (next_spec i (stages i)).2.2
  have hmono_left : Monotone fun i ↦ (stages i).left :=
    monotone_nat_of_le_succ fun i ↦ subset_closure.trans (hstep_left i)
  have hmono_right : Monotone fun i ↦ (stages i).right :=
    monotone_nat_of_le_succ fun i ↦ subset_closure.trans (hstep_right i)
  let G : Set X := ⋃ i, (stages i).left
  let H : Set X := ⋃ i, (stages i).right
  have hGo : IsOpen G := isOpen_iUnion fun i ↦ (stages i).isOpen_left
  have hHo : IsOpen H := isOpen_iUnion fun i ↦ (stages i).isOpen_right
  have hGH : Disjoint G H := by
    rw [Set.disjoint_left]
    intro x hxG hxH
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxG
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxH
    rcases le_total i j with hij | hji
    · exact Set.disjoint_left.mp (stages j).disjoint_closure
        (subset_closure (hmono_left hij hxi)) (subset_closure hxj)
    · exact Set.disjoint_left.mp (stages i).disjoint_closure
        (subset_closure hxi) (subset_closure (hmono_right hji hxj))
  have hcover : G ∪ H = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, F i := by rw [hFcover]; exact mem_univ x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rcases hstep_cover i hxi with hxl | hxr
    · exact Or.inl (mem_iUnion.mpr ⟨i + 1, hxl⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨i + 1, hxr⟩)
  have hGc : IsClosed G := by
    rw [← isOpen_compl_iff]
    have : Gᶜ = H := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases (show x ∈ G ∪ H by rw [hcover]; exact mem_univ x) with hxG | hxH
        · exact (hx hxG).elim
        · exact hxH
      · exact fun x hxH hxG ↦ Set.disjoint_left.mp hGH hxG hxH
    rw [this]
    exact hHo
  refine ⟨G, ⟨hGc, hGo⟩, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨0, s₀.A_subset hx⟩
  · intro x hx
    have hxH : x ∈ H := mem_iUnion.mpr ⟨0, s₀.B_subset hx⟩
    exact fun hxG ↦ Set.disjoint_left.mp hGH hxG hxH

/-- **Countable closed-sum theorem in dimension zero.**

If a second-countable pseudometrizable space is the union of countably many
closed subspaces with `ind < 1`, then it too has `ind < 1`. -/
theorem hasSmallInductiveDimensionLT_one_of_closed_iUnion
    [SecondCountableTopology X]
    (F : ℕ → Set X) (hFclosed : ∀ i, IsClosed (F i))
    (hFzero : ∀ i, HasSmallInductiveDimensionLT (F i) 1)
    (hFcover : ⋃ i, F i = univ) :
    HasSmallInductiveDimensionLT X 1 := by
  rw [hasSmallInductiveDimensionLT_one_iff]
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.isOpen
  · intro x O hxO hOo
    let A : Set X := closure ({x} : Set X)
    have hsingleton : IsClosed A := isClosed_closure
    have hcompl : IsClosed Oᶜ := hOo.isClosed_compl
    have hAO : A ⊆ O := by
      intro y hy
      have hxy : Specializes x y := specializes_iff_mem_closure.mpr hy
      exact hxy.symm.mem_open hOo hxO
    have hdisj : Disjoint A Oᶜ := Set.disjoint_left.mpr fun _ hyA hyO ↦ hyO (hAO hyA)
    obtain ⟨C, hC, hxC, hOC⟩ := exists_clopen_separating_of_closed_iUnion
      F hFclosed hFzero hFcover hsingleton hcompl hdisj
    refine ⟨C, hC, hxC (subset_closure (mem_singleton x)), ?_⟩
    intro y hyC
    by_contra hyO
    exact hOC hyO hyC

private theorem inducing_hasSmallInductiveDimensionLT
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → Z} (hf : IsInducing f) {n : ℕ}
    (h : HasSmallInductiveDimensionLT Z n) :
    HasSmallInductiveDimensionLT Y n := by
  induction h generalizing Y with
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

private theorem range_hasSmallInductiveDimensionLT_of_isEmbedding
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → Z} (hf : IsEmbedding f) {n : ℕ}
    (h : HasSmallInductiveDimensionLT Y n) :
    HasSmallInductiveDimensionLT (Set.range f) n :=
  inducing_hasSmallInductiveDimensionLT hf.toHomeomorph.symm.isInducing h

/-- In a second-countable zero-dimensional space, a closed set contained in
an open set admits a clopen intermediate set. -/
theorem exists_clopen_between
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
    (hzero : HasSmallInductiveDimensionLT Y 1)
    {D U : Set Y} (hD : IsClosed D) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ C : Set Y, IsClopen C ∧ D ⊆ C ∧ C ⊆ U := by
  classical
  let V : Bool → Set Y := fun i ↦ if i = false then U else Dᶜ
  have hVopen (i : Bool) : IsOpen (V i) := by
    cases i <;> simp [V, hU, hD.isOpen_compl]
  have hVcover : ⋃ i, V i = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ D
    · exact mem_iUnion.mpr ⟨false, by simpa [V] using hDU hy⟩
    · exact mem_iUnion.mpr ⟨true, by simpa [V] using hy⟩
  obtain ⟨C, hCclopen, -, hCcover, hCsub⟩ :=
    ZeroDimensionalRefinement.exists_disjoint_clopen_refinement
      hzero V hVopen hVcover
  refine ⟨C false, hCclopen false, ?_, by simpa [V] using hCsub false⟩
  intro y hyD
  have hycover : y ∈ ⋃ i, C i := by rw [hCcover]; exact mem_univ y
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hycover
  cases i with
  | false => exact hyi
  | true => exact (hCsub true hyi hyD).elim

/-- A zero-dimensional subspace of a pseudometric space can be avoided by
the frontier of an arbitrarily small ambient neighbourhood.  This is the
metric form of `TOPDIM_1:38`. -/
theorem exists_open_mem_subset_frontier_disjoint
    [SecondCountableTopology X]
    (N : Set X) (hzero : HasSmallInductiveDimensionLT N 1)
    {x : X} {O : Set X} (hxO : x ∈ O) (hO : IsOpen O) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧
      Disjoint N (frontier W) := by
  classical
  obtain ⟨P, hPn, hPc, hPO⟩ :=
    exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  let Q : Set X := interior P
  have hQo : IsOpen Q := isOpen_interior
  have hxQ : x ∈ Q := mem_interior_iff_mem_nhds.mpr hPn
  have hQcO : closure Q ⊆ O :=
    (closure_minimal (interior_subset) hPc).trans hPO
  let D : Set N := Subtype.val ⁻¹' closure Q
  let U : Set N := Subtype.val ⁻¹' O
  have hDc : IsClosed D := isClosed_closure.preimage continuous_subtype_val
  have hUo : IsOpen U := hO.preimage continuous_subtype_val
  have hDU : D ⊆ U := preimage_mono hQcO
  obtain ⟨C, hCc, hDC, hCU⟩ := exists_clopen_between hzero hDc hUo hDU
  by_cases hCn : C.Nonempty
  · by_cases hCcn : Cᶜ.Nonempty
    · obtain ⟨V, hVo, hVtrace, hVclosure⟩ :=
        MetricSubspaceLift.exists_isOpen_subtype_lift_closure_preimage_eq
          N hCc.isOpen hCn hCcn
      let W : Set X := Q ∪ (V ∩ O)
      have hWo : IsOpen W := hQo.union (hVo.inter hO)
      have hxW : x ∈ W := Or.inl hxQ
      have hWO : W ⊆ O :=
        union_subset (subset_closure.trans hQcO) inter_subset_right
      refine ⟨W, hWo, hxW, hWO, ?_⟩
      rw [Set.disjoint_left]
      intro y hyN hyfr
      let z : N := ⟨y, hyN⟩
      by_cases hzC : z ∈ C
      · have hzV : y ∈ V := by
          change z ∈ Subtype.val ⁻¹' V
          rwa [hVtrace]
        have hzO : y ∈ O := hCU hzC
        apply hyfr.2
        rw [hWo.interior_eq]
        exact Or.inr ⟨hzV, hzO⟩
      · have hycl : y ∈ closure W := hyfr.1
        rw [show closure W = closure Q ∪ closure (V ∩ O) by
          simp [W, closure_union]] at hycl
        rcases hycl with hyQ | hyV
        · exact hzC (hDC hyQ)
        · apply hzC
          have hz : z ∈ Subtype.val ⁻¹' closure V :=
            closure_mono inter_subset_left hyV
          rw [hVclosure, hCc.isClosed.closure_eq] at hz
          exact hz
    · have hCeq : C = univ := by
        rw [← compl_empty_iff]
        exact not_nonempty_iff_eq_empty.mp hCcn
      refine ⟨O, hO, hxO, Subset.rfl, ?_⟩
      rw [Set.disjoint_left]
      intro y hyN hyfr
      have hyC : (⟨y, hyN⟩ : N) ∈ C := by rw [hCeq]; exact mem_univ _
      apply hyfr.2
      rw [hO.interior_eq]
      exact hCU hyC
  · have hCeq : C = ∅ := not_nonempty_iff_eq_empty.mp hCn
    refine ⟨Q, hQo, hxQ, subset_closure.trans hQcO, ?_⟩
    rw [Set.disjoint_left]
    intro y hyN hyfr
    have hyD : (⟨y, hyN⟩ : N) ∈ D := hyfr.1
    have : (⟨y, hyN⟩ : N) ∈ C := hDC hyD
    simpa [hCeq] using this

/-- Adjoining a zero-dimensional subspace raises small inductive dimension by
at most one.  No closedness assumption is needed. -/
theorem hasSmallInductiveDimensionLT_union_zeroDimensional
    [SecondCountableTopology X]
    (A N : Set X) {n : ℕ}
    (hA : HasSmallInductiveDimensionLT A n)
    (hN : HasSmallInductiveDimensionLT N 1) :
    HasSmallInductiveDimensionLT (↑(A ∪ N : Set X)) (n + 1) := by
  let Y : Set X := A ∪ N
  let A' : Set Y := Subtype.val ⁻¹' A
  let N' : Set Y := Subtype.val ⁻¹' N
  have hA' : HasSmallInductiveDimensionLT A' n := by
    apply inducing_hasSmallInductiveDimensionLT
      (f := fun x : A' ↦ (⟨(x : X), x.2⟩ : A)) _ hA
    apply IsInducing.of_comp (g := fun x : A ↦ (x : X))
    · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    · exact continuous_subtype_val
    · simpa [Function.comp_def] using
        (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
  have hN' : HasSmallInductiveDimensionLT N' 1 := by
    apply inducing_hasSmallInductiveDimensionLT
      (f := fun x : N' ↦ (⟨(x : X), x.2⟩ : N)) _ hN
    apply IsInducing.of_comp (g := fun x : N ↦ (x : X))
    · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    · exact continuous_subtype_val
    · simpa [Function.comp_def] using
        (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
  let b : Set (Set Y) :=
    {U | IsOpen U ∧ Disjoint N' (frontier U)}
  have hb : IsTopologicalBasis b :=
    isTopologicalBasis_of_isOpen_of_nhds
      (fun U hU ↦ hU.1)
      (fun x O hx hO ↦ by
        obtain ⟨U, hUo, hxU, hUO, hUf⟩ :=
          exists_open_mem_subset_frontier_disjoint N' hN' hx hO
        exact ⟨U, ⟨hUo, hUf⟩, hxU, hUO⟩)
  refine .succ n b hb ?_
  intro U hUb
  let f : frontier U → A' := fun x ↦ ⟨x, by
    rcases x.1.property with hxA | hxN
    · exact hxA
    · exact (Set.disjoint_left.mp hUb.2 hxN x.2).elim⟩
  apply inducing_hasSmallInductiveDimensionLT (f := f) _ hA'
  apply IsInducing.of_comp (g := fun x : A' ↦ (x : Y))
  · exact (continuous_subtype_val.subtype_mk _)
  · exact continuous_subtype_val
  · simpa [f, Function.comp_def] using
      (IsInducing.subtypeVal : IsInducing ((↑) : frontier U → Y))

/-- The universe-polymorphic assertion that the countable closed-sum theorem
holds at the strict dimension bound `r`. -/
def CountableClosedSumAt (r : ℕ) : Prop :=
  ∀ (Y : Type u) [PseudoMetricSpace Y] [SecondCountableTopology Y]
    (F : ℕ → Set Y), (∀ i, IsClosed (F i)) →
      (∀ i, HasSmallInductiveDimensionLT (F i) r) →
      (⋃ i, F i = univ) → HasSmallInductiveDimensionLT Y r

/-- The checked zero-dimensional base of the mutual closed-sum induction. -/
theorem countableClosedSumAt_one : CountableClosedSumAt.{u} 1 := by
  intro Y _ _ F hFc hFd hFcover
  exact hasSmallInductiveDimensionLT_one_of_closed_iUnion F hFc hFd hFcover

/-- Assuming the closed-sum theorem at rank `n`, a space of strict dimension
`< n+1` splits into a rank-`n` part and a zero-dimensional part.  This is the
`P[n] ⇒ R[n+1]` half of Mizar `TOPDIM_2:3`. -/
theorem exists_disjoint_decomposition_of_countableClosedSumAt
    [SecondCountableTopology X] {n : ℕ}
    (hsum : CountableClosedSumAt.{u} n)
    (hX : HasSmallInductiveDimensionLT X (n + 1)) :
    ∃ A B : Set X, A ∪ B = univ ∧ Disjoint A B ∧
      HasSmallInductiveDimensionLT A n ∧
      HasSmallInductiveDimensionLT B 1 := by
  classical
  obtain ⟨b, hb, hfront⟩ :=
    (DimensionCore.hasSmallInductiveDimensionLT_succ_iff n).mp hX
  obtain ⟨c, hcb, hcc, hcbasis⟩ := hb.exists_countable
  let d : Set (Set X) := insert ∅ c
  have hdc : d.Countable := hcc.insert ∅
  have hdb : d ⊆ insert ∅ b := by
    intro U hU
    rcases hU with rfl | hU
    · exact mem_insert ∅ b
    · exact mem_insert_of_mem ∅ (hcb hU)
  have hdbasis : IsTopologicalBasis d := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with rfl | hU
      · exact isOpen_empty
      · exact hcbasis.isOpen hU
    · intro x O hx hO
      obtain ⟨U, hUc, hxU, hUO⟩ := hcbasis.exists_subset_of_mem_open hx hO
      exact ⟨U, mem_insert_of_mem ∅ hUc, hxU, hUO⟩
  let e : ℕ → Set X := Set.enumerateCountable hdc ∅
  have he_mem (i : ℕ) : e i ∈ d :=
    Set.enumerateCountable_mem hdc (mem_insert ∅ c) i
  have he_range : range e = d :=
    Set.range_enumerateCountable_of_mem hdc (mem_insert ∅ c)
  have he_dim (i : ℕ) :
      HasSmallInductiveDimensionLT (frontier (e i)) n := by
    rcases he_mem i with hei | hei
    · rw [hei]
      rw [frontier_empty]
      exact inferInstance
    · exact hfront (e i) (hcb hei)
  let A : Set X := ⋃ i, frontier (e i)
  let B : Set X := Aᶜ
  let G : ℕ → Set A := fun i ↦ Subtype.val ⁻¹' frontier (e i)
  have hGc (i : ℕ) : IsClosed (G i) :=
    isClosed_frontier.preimage continuous_subtype_val
  have hGdim (i : ℕ) : HasSmallInductiveDimensionLT (G i) n := by
    let f : G i → frontier (e i) := fun x ↦ ⟨(x : X), x.2⟩
    apply inducing_hasSmallInductiveDimensionLT (f := f) _ (he_dim i)
    apply IsInducing.of_comp (g := fun x : frontier (e i) ↦ (x : X))
    · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    · exact continuous_subtype_val
    · simpa [f, Function.comp_def] using
        (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
  have hGcover : ⋃ i, G i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hxi⟩
  have hAdim : HasSmallInductiveDimensionLT A n :=
    hsum A G hGc hGdim hGcover
  have hBdim : HasSmallInductiveDimensionLT B 1 := by
    apply DimensionCore.subtype_hasSmallInductiveDimensionLT_of_basis_frontier_subset
      B 0 d hdbasis (fun U ↦ frontier U)
    · exact fun U _ ↦ Subset.rfl
    · intro U hUd
      have hUrange : U ∈ range e := by rw [he_range]; exact hUd
      obtain ⟨i, rfl⟩ := hUrange
      have hempty : IsEmpty (Subtype.val ⁻¹' frontier (e i) : Set B) :=
        ⟨fun x ↦ x.1.property (mem_iUnion.mpr ⟨i, x.2⟩)⟩
      let := hempty
      exact .zero
  refine ⟨A, B, ?_, disjoint_compl_right, hAdim, hBdim⟩
  exact union_compl_self A

/-- In a regular second-countable space, every open set is a countable union
of closed sets.  We record the explicit sequence form needed when the
disjointized layers of a closed cover are converted back into a closed
cover. -/
theorem exists_closed_iUnion_eq_of_isOpen
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) :
    ∃ K : ℕ → Set X, (∀ i, IsClosed (K i)) ∧ ⋃ i, K i = U := by
  classical
  obtain ⟨b, hbcount, -, hbbasis⟩ := exists_countable_basis X
  let c : Set (Set X) := {V | V ∈ b ∧ closure V ⊆ U}
  have hccount : c.Countable := hbcount.mono fun _ hV ↦ hV.1
  let d : Set (Set X) := insert ∅ c
  have hdcount : d.Countable := hccount.insert ∅
  have hempty : ∅ ∈ d := mem_insert ∅ c
  let e : ℕ → Set X := Set.enumerateCountable hdcount ∅
  have hed (i : ℕ) : e i ∈ d :=
    Set.enumerateCountable_mem hdcount hempty i
  have heU (i : ℕ) : closure (e i) ⊆ U := by
    rcases hed i with hei | hei
    · rw [hei, closure_empty]
      exact empty_subset U
    · exact hei.2
  let K : ℕ → Set X := fun i ↦ closure (e i)
  refine ⟨K, fun i ↦ isClosed_closure, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact heU i hxi
  · intro x hxU
    obtain ⟨W, hWn, hWc, hWU⟩ :=
      exists_mem_nhds_isClosed_subset (hU.mem_nhds hxU)
    have hxint : x ∈ interior W := mem_interior_iff_mem_nhds.mpr hWn
    obtain ⟨V, hVb, hxV, hVsub⟩ :=
      hbbasis.exists_subset_of_mem_open hxint isOpen_interior
    have hVcU : closure V ⊆ U :=
      (closure_minimal (hVsub.trans interior_subset) hWc).trans hWU
    have hVc : V ∈ c := ⟨hVb, hVcU⟩
    have hVrange : V ∈ range e := by
      rw [Set.range_enumerateCountable_of_mem hdcount hempty]
      exact mem_insert_of_mem ∅ hVc
    obtain ⟨i, rfl⟩ := hVrange
    exact mem_iUnion.mpr ⟨i, subset_closure hxV⟩

/-- The successor step of the mutual closed-sum induction.  The closed cover
is first disjointized.  Each locally closed layer is split by
`exists_disjoint_decomposition_of_countableClosedSumAt`; its two parts are
then separately recovered from countable closed covers, and finally joined
with `hasSmallInductiveDimensionLT_union_zeroDimensional`. -/
theorem countableClosedSumAt_succ {n : ℕ}
    (hsum : CountableClosedSumAt.{u} n) :
    CountableClosedSumAt.{u} (n + 1) := by
  intro Y _ _ F hFclosed hFdim hFcover
  classical
  let G : ℕ → Set Y := disjointed F
  have hGsub (i : ℕ) : G i ⊆ F i := by
    simpa [G] using disjointed_subset F i
  have hGpair : Pairwise fun i j ↦ Disjoint (G i) (G j) := by
    simpa [G] using disjoint_disjointed F
  have hGcover : ⋃ i, G i = univ := by
    rw [show (⋃ i, G i) = ⋃ i, F i by
      simpa [G] using iUnion_disjointed (f := F)]
    exact hFcover
  have hGdim (i : ℕ) : HasSmallInductiveDimensionLT (G i) (n + 1) := by
    exact inducing_hasSmallInductiveDimensionLT
      (IsEmbedding.inclusion (hGsub i)).isInducing (hFdim i)
  choose P Q hPQcover hPQdisj hPdim hQdim using fun i ↦
    exists_disjoint_decomposition_of_countableClosedSumAt hsum (hGdim i)
  let PA : ℕ → Set Y := fun i ↦ Subtype.val '' P i
  let QA : ℕ → Set Y := fun i ↦ Subtype.val '' Q i
  have hPAdim (i : ℕ) : HasSmallInductiveDimensionLT (PA i) n := by
    let f : P i → Y := fun x ↦ (x : Y)
    have hf : IsEmbedding f := by
      simpa [f, Function.comp_def] using
        (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    have hrange := range_hasSmallInductiveDimensionLT_of_isEmbedding hf (hPdim i)
    have heq : range f = PA i := by
      ext y
      simp [f, PA]
    rwa [heq] at hrange
  have hQAdim (i : ℕ) : HasSmallInductiveDimensionLT (QA i) 1 := by
    let f : Q i → Y := fun x ↦ (x : Y)
    have hf : IsEmbedding f := by
      simpa [f, Function.comp_def] using
        (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    have hrange := range_hasSmallInductiveDimensionLT_of_isEmbedding hf (hQdim i)
    have heq : range f = QA i := by
      ext y
      simp [f, QA]
    rwa [heq] at hrange
  let A : Set Y := ⋃ i, PA i
  let N : Set Y := ⋃ i, QA i
  have hANcover : A ∪ N = univ := by
    apply eq_univ_of_forall
    intro y
    have hyG : y ∈ ⋃ i, G i := by rw [hGcover]; exact mem_univ y
    obtain ⟨i, hyGi⟩ := mem_iUnion.mp hyG
    have hyPQ : (⟨y, hyGi⟩ : G i) ∈ P i ∪ Q i := by
      rw [hPQcover i]
      exact mem_univ _
    rcases hyPQ with hyP | hyQ
    · exact Or.inl (mem_iUnion.mpr ⟨i, ⟨⟨y, hyGi⟩, hyP, rfl⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨i, ⟨⟨y, hyGi⟩, hyQ, rfl⟩⟩)
  have hANdisj : Disjoint A N := by
    rw [Set.disjoint_left]
    intro y hyA hyN
    obtain ⟨i, yi, hyiP, hyi⟩ := mem_iUnion.mp hyA
    obtain ⟨j, yj, hyjQ, hyj⟩ := mem_iUnion.mp hyN
    have heq : (yi : Y) = (yj : Y) := hyi.trans hyj.symm
    by_cases hij : i = j
    · subst j
      have hyij : yi = yj := Subtype.ext heq
      exact Set.disjoint_left.mp (hPQdisj i) hyiP (hyij ▸ hyjQ)
    · exact Set.disjoint_left.mp (hGpair hij) yi.property (heq ▸ yj.property)
  let Prev : ℕ → Set Y := fun i ↦ ⋃ j ∈ Finset.Iio i, F j
  have hPrevClosed (i : ℕ) : IsClosed (Prev i) := by
    apply isClosed_biUnion_finset
    exact fun j _ ↦ hFclosed j
  choose K hKclosed hKcover using fun i ↦
    exists_closed_iUnion_eq_of_isOpen (X := Y) (hPrevClosed i).isOpen_compl
  let L : ℕ → ℕ → Set Y := fun i k ↦ F i ∩ K i k
  have hLclosed (i k : ℕ) : IsClosed (L i k) :=
    (hFclosed i).inter (hKclosed i k)
  have hLsubG (i k : ℕ) : L i k ⊆ G i := by
    intro y hy
    have hyK : y ∈ (Prev i)ᶜ := by
      rw [← hKcover i]
      exact mem_iUnion.mpr ⟨k, hy.2⟩
    change y ∈ disjointed F i
    rw [disjointed_apply]
    refine ⟨hy.1, ?_⟩
    simpa [Prev, Finset.sup_eq_iSup] using hyK
  have hLcover (i : ℕ) : ⋃ k, L i k = G i := by
    apply Set.Subset.antisymm
    · exact iUnion_subset fun k ↦ hLsubG i k
    · intro y hyG
      have hyF : y ∈ F i := hGsub i hyG
      have hyPrev : y ∈ (Prev i)ᶜ := by
        change y ∈ disjointed F i at hyG
        rw [disjointed_apply] at hyG
        simpa [Prev, Finset.sup_eq_iSup] using hyG.2
      have hyK : y ∈ ⋃ k, K i k := by rwa [hKcover i]
      obtain ⟨k, hyk⟩ := mem_iUnion.mp hyK
      exact mem_iUnion.mpr ⟨k, ⟨hyF, hyk⟩⟩
  have hA_inter_L_subset_PA (i k : ℕ) :
      A ∩ L i k ⊆ PA i := by
    intro y hy
    obtain ⟨j, yj, hyjP, hyjy⟩ := mem_iUnion.mp hy.1
    have hyGi : y ∈ G i := hLsubG i k hy.2
    by_cases hji : j = i
    · subst j
      exact ⟨yj, hyjP, hyjy⟩
    · exact (Set.disjoint_left.mp (hGpair hji) yj.property (hyjy ▸ hyGi)).elim
  have hN_inter_L_subset_QA (i k : ℕ) :
      N ∩ L i k ⊆ QA i := by
    intro y hy
    obtain ⟨j, yj, hyjQ, hyjy⟩ := mem_iUnion.mp hy.1
    have hyGi : y ∈ G i := hLsubG i k hy.2
    by_cases hji : j = i
    · subst j
      exact ⟨yj, hyjQ, hyjy⟩
    · exact (Set.disjoint_left.mp (hGpair hji) yj.property (hyjy ▸ hyGi)).elim
  let CA : ℕ → Set A := fun m ↦
    Subtype.val ⁻¹' L (Nat.unpair m).1 (Nat.unpair m).2
  have hCAclosed (m : ℕ) : IsClosed (CA m) :=
    (hLclosed (Nat.unpair m).1 (Nat.unpair m).2).preimage continuous_subtype_val
  have hCAdim (m : ℕ) : HasSmallInductiveDimensionLT (CA m) n := by
    let i := (Nat.unpair m).1
    let k := (Nat.unpair m).2
    let f : CA m → PA i := fun x ↦ ⟨(x : Y),
      hA_inter_L_subset_PA i k ⟨x.1.property, x.2⟩⟩
    apply inducing_hasSmallInductiveDimensionLT (f := f) _ (hPAdim i)
    apply IsInducing.of_comp (g := fun x : PA i ↦ (x : Y))
    · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    · exact continuous_subtype_val
    · simpa [f, Function.comp_def] using
        (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
  have hCAcover : ⋃ m, CA m = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨i, yi, hyiP, hyiy⟩ := mem_iUnion.mp y.property
    have hyG : (y : Y) ∈ G i := hyiy ▸ yi.property
    have hyL : (y : Y) ∈ ⋃ k, L i k := by rwa [hLcover i]
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hyL
    apply mem_iUnion.mpr
    refine ⟨Nat.pair i k, ?_⟩
    simpa [CA, Nat.unpair_pair] using hyk
  let CN : ℕ → Set N := fun m ↦
    Subtype.val ⁻¹' L (Nat.unpair m).1 (Nat.unpair m).2
  have hCNclosed (m : ℕ) : IsClosed (CN m) :=
    (hLclosed (Nat.unpair m).1 (Nat.unpair m).2).preimage continuous_subtype_val
  have hCNdim (m : ℕ) : HasSmallInductiveDimensionLT (CN m) 1 := by
    let i := (Nat.unpair m).1
    let k := (Nat.unpair m).2
    let f : CN m → QA i := fun x ↦ ⟨(x : Y),
      hN_inter_L_subset_QA i k ⟨x.1.property, x.2⟩⟩
    apply inducing_hasSmallInductiveDimensionLT (f := f) _ (hQAdim i)
    apply IsInducing.of_comp (g := fun x : QA i ↦ (x : Y))
    · exact ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    · exact continuous_subtype_val
    · simpa [f, Function.comp_def] using
        (IsInducing.subtypeVal.comp IsInducing.subtypeVal)
  have hCNcover : ⋃ m, CN m = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨i, yi, hyiQ, hyiy⟩ := mem_iUnion.mp y.property
    have hyG : (y : Y) ∈ G i := hyiy ▸ yi.property
    have hyL : (y : Y) ∈ ⋃ k, L i k := by rwa [hLcover i]
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hyL
    apply mem_iUnion.mpr
    refine ⟨Nat.pair i k, ?_⟩
    simpa [CN, Nat.unpair_pair] using hyk
  have hAdim : HasSmallInductiveDimensionLT A n :=
    hsum A CA hCAclosed hCAdim hCAcover
  have hNdim : HasSmallInductiveDimensionLT N 1 :=
    countableClosedSumAt_one N CN hCNclosed hCNdim hCNcover
  have hUnion : HasSmallInductiveDimensionLT (↑(A ∪ N : Set Y)) (n + 1) :=
    hasSmallInductiveDimensionLT_union_zeroDimensional A N hAdim hNdim
  rw [hANcover] at hUnion
  exact inducing_hasSmallInductiveDimensionLT
    (f := fun y : Y ↦ (⟨y, mem_univ y⟩ : (univ : Set Y)))
    (by
      apply IsInducing.of_comp (g := fun z : (univ : Set Y) ↦ (z : Y))
      · exact continuous_id.subtype_mk _
      · exact continuous_subtype_val
      · change IsInducing (id : Y → Y)
        exact IsInducing.id)
    hUnion

/-- The vacuous strict `-1` case of the closed-sum theorem. -/
theorem countableClosedSumAt_zero : CountableClosedSumAt.{u} 0 := by
  intro Y _ _ F _ hFdim hFcover
  have hYempty : IsEmpty Y := ⟨fun y ↦ by
    have hy : y ∈ ⋃ i, F i := by rw [hFcover]; exact mem_univ y
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    have hi : IsEmpty (F i) := hasSmallInductiveDimensionLT_zero_iff.mp (hFdim i)
    exact hi.false ⟨y, hyi⟩⟩
  let := hYempty
  exact .zero

/-- **Countable closed-sum theorem for small inductive dimension.** -/
theorem countableClosedSumAt (r : ℕ) : CountableClosedSumAt.{u} r := by
  induction r with
  | zero => exact countableClosedSumAt_zero
  | succ r ih =>
      simpa [Nat.succ_eq_add_one] using countableClosedSumAt_succ ih

/-- A countable union of closed subspaces with a common strict
small-inductive-dimension bound has the same bound.  This is the direct form
used by the Euclidean lower-bound decomposition. -/
theorem hasSmallInductiveDimensionLT_iUnion_of_isClosed
    [SecondCountableTopology X] (r : ℕ)
    (F : ℕ → Set X) (hFclosed : ∀ i, IsClosed (F i))
    (hFdim : ∀ i, HasSmallInductiveDimensionLT (F i) r) :
    HasSmallInductiveDimensionLT (↑(⋃ i, F i : Set X)) r := by
  let S : Set X := ⋃ i, F i
  let G : ℕ → Set S := fun i ↦ Subtype.val ⁻¹' F i
  have hGclosed (i : ℕ) : IsClosed (G i) :=
    (hFclosed i).preimage continuous_subtype_val
  have hGdim (i : ℕ) : HasSmallInductiveDimensionLT (G i) r := by
    let e : G i → F i := fun x ↦ ⟨x.1.1, x.2⟩
    have he : IsEmbedding e :=
      (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict _
        (fun x ↦ x.2)
    exact inducing_hasSmallInductiveDimensionLT he.isInducing (hFdim i)
  have hGcover : ⋃ i, G i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hxi⟩
  exact countableClosedSumAt r S G hGclosed hGdim hGcover

/-- A strict rank-`r` second-countable pseudometrizable space is the disjoint
union of `r` zero-dimensional subspaces.  This is the finite-layer form of
the countable closed-sum induction (Mizar `TOPDIM_2:7`). -/
theorem exists_fin_zeroDimensional_partition
    [SecondCountableTopology X] (r : ℕ)
    (hX : HasSmallInductiveDimensionLT X r) :
    ∃ Z : Fin r → Set X,
      ⋃ i, Z i = univ ∧
      Pairwise (fun i j ↦ Disjoint (Z i) (Z j)) ∧
      ∀ i, HasSmallInductiveDimensionLT (Z i) 1 := by
  induction r generalizing X with
  | zero =>
      have hXe : IsEmpty X := hasSmallInductiveDimensionLT_zero_iff.mp hX
      let := hXe
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_, fun i ↦ Fin.elim0 i⟩
      · apply Set.Subset.antisymm
        · exact iUnion_subset fun i ↦ Fin.elim0 i
        · intro x
          exact isEmptyElim x
      · intro i
        exact Fin.elim0 i
  | succ r ih =>
      obtain ⟨A, B, hABcover, hABdisj, hAdim, hBdim⟩ :=
        exists_disjoint_decomposition_of_countableClosedSumAt
          (countableClosedSumAt r) (by simpa [Nat.succ_eq_add_one] using hX)
      obtain ⟨C, hCcover, hCpair, hCdim⟩ := ih hAdim
      let D : Fin r → Set X := fun i ↦ Subtype.val '' C i
      have hDdim (i : Fin r) : HasSmallInductiveDimensionLT (D i) 1 := by
        let f : C i → X := fun x ↦ (x : X)
        have hf : IsEmbedding f := by
          simpa [f, Function.comp_def] using
            (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
        have hrange := range_hasSmallInductiveDimensionLT_of_isEmbedding hf (hCdim i)
        have heq : range f = D i := by
          ext x
          simp [f, D]
        rwa [heq] at hrange
      have hDsub (i : Fin r) : D i ⊆ A := by
        rintro x ⟨y, -, rfl⟩
        exact y.property
      have hDpair : Pairwise (fun i j ↦ Disjoint (D i) (D j)) := by
        intro i j hij
        rw [Set.disjoint_left]
        rintro x ⟨yi, hyi, rfl⟩ ⟨yj, hyj, heq⟩
        have hyij : yi = yj := Subtype.ext heq.symm
        exact Set.disjoint_left.mp (hCpair hij) hyi (hyij ▸ hyj)
      have hDcover : ⋃ i, D i = A := by
        apply Set.Subset.antisymm
        · exact iUnion_subset hDsub
        · intro x hxA
          let y : A := ⟨x, hxA⟩
          have hy : y ∈ ⋃ i, C i := by rw [hCcover]; exact mem_univ y
          obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
          exact mem_iUnion.mpr ⟨i, ⟨y, hyi, rfl⟩⟩
      let Z : Fin (r + 1) → Set X := Fin.cases B D
      refine ⟨Z, ?_, ?_, ?_⟩
      · apply eq_univ_of_forall
        intro x
        have hxAB : x ∈ A ∪ B := by rw [hABcover]; exact mem_univ x
        rcases hxAB with hxA | hxB
        · have hxD : x ∈ ⋃ i, D i := by rwa [hDcover]
          obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
          exact mem_iUnion.mpr ⟨Fin.succ i, by simpa [Z] using hxi⟩
        · exact mem_iUnion.mpr ⟨0, by simpa [Z] using hxB⟩
      · intro i j hij
        exact @Fin.cases r
          (fun i : Fin (r + 1) ↦ ∀ j, i ≠ j → Disjoint (Z i) (Z j))
          (fun j ↦ @Fin.cases r
            (fun j : Fin (r + 1) ↦ (0 : Fin (r + 1)) ≠ j →
              Disjoint (Z 0) (Z j))
            (fun hij ↦ (hij rfl).elim)
            (fun j _ ↦ by
              change Disjoint B (D j)
              exact hABdisj.symm.mono Subset.rfl (hDsub j)) j)
          (fun i j ↦ @Fin.cases r
            (fun j : Fin (r + 1) ↦ Fin.succ i ≠ j →
              Disjoint (Z (Fin.succ i)) (Z j))
            (fun _ ↦ by
              change Disjoint (D i) B
              exact hABdisj.mono (hDsub i) Subset.rfl)
            (fun j hij ↦ by
              change Disjoint (D i) (D j)
              exact hDpair (fun h ↦ hij (congrArg Fin.succ h))) j) i j hij
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change HasSmallInductiveDimensionLT B 1
          exact hBdim
        · change HasSmallInductiveDimensionLT (D j) 1
          exact hDdim j

end Erdos909.ClosedSum

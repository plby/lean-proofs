/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos847.Pictures
import ErdosProblems.Erdos847.ConfinementKernels

/-!
Scratch architecture for the finite core of Erdős 847.

The point of this file is not to duplicate the RRS construction.  It records two reductions that
make the target specialization substantially smaller:

* hypergraphs are finite families of finite vertex sets;
* the `1/3` fractional property is expressed using natural-valued multiplicities.  This is exactly
  what is needed for pullback along the picture projection, and avoids normalized real weights.
-/

namespace Erdos847FiniteArch

open scoped BigOperators
open Function Set
open Erdos847Pictures

/-! A quasiline is best represented parametrically.  This avoids quotienting by the six possible
labellings of a three-element `Finset`, while remaining exactly the unordered notion after taking
the range. -/

def IsQuasilineParam {A I : Type*} (q : A → I → A) : Prop :=
  Function.Injective q ∧ ∀ i, Function.Injective (fun a ↦ q a i) ∨
    ∃ c, ∀ a, q a i = c

lemma line_injective {A I : Type*} [Nontrivial A]
    (L : Combinatorics.Line A I) : Function.Injective L := by
  intro a b hab
  obtain ⟨i, hi⟩ := L.proper
  have := congrFun hab i
  simpa [Combinatorics.Line.coe_apply, hi] using this

lemma line_isQuasilineParam {A I : Type*} [Nontrivial A]
    (L : Combinatorics.Line A I) : IsQuasilineParam L := by
  refine ⟨line_injective L, fun i ↦ ?_⟩
  cases hi : L.idxFun i with
  | none =>
      left
      intro a b hab
      simpa [Combinatorics.Line.coe_apply, hi] using hab
  | some c =>
      right
      exact ⟨c, fun a ↦ by simp [Combinatorics.Line.coe_apply, hi]⟩

abbrev FinHypergraph (V : Type*) [DecidableEq V] := Finset (Finset V)

def Independent {V : Type*} [DecidableEq V] (H : FinHypergraph V) (I : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

/-- The cleared-denominator `1/3` fractional property, only for natural multiplicities. -/
def NatFractionalThird {V : Type*} [Fintype V] [DecidableEq V]
    (H : FinHypergraph V) : Prop :=
  ∀ w : V → ℕ, ∃ I : Finset V, Independent H I ∧
    (∑ x, w x) ≤ 3 * ∑ x ∈ I, w x

/-- A map which sends every source edge onto a target edge. -/
def MapsEdges {U V : Type*} [DecidableEq U] [DecidableEq V]
    (f : U → V) (G : FinHypergraph U) (H : FinHypergraph V) : Prop :=
  ∀ e ∈ G, e.image f ∈ H

lemma independent_preimage {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
    {f : U → V} {G : FinHypergraph U} {H : FinHypergraph V}
    (hf : MapsEdges f G H) {J : Finset V} (hJ : Independent H J) :
    Independent G (Finset.univ.filter fun x ↦ f x ∈ J) := by
  intro e he heI
  apply hJ (e.image f) (hf e he)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (Finset.mem_filter.mp (heI hx)).2

/-- Natural multiplicities are stable under the many-to-one projection used by pictures. -/
lemma NatFractionalThird.pullback {U V : Type*}
    [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    {f : U → V} {G : FinHypergraph U} {H : FinHypergraph V}
    (hH : NatFractionalThird H) (hf : MapsEdges f G H) :
    NatFractionalThird G := by
  intro w
  let W : V → ℕ := fun y ↦ ∑ x with f x = y, w x
  obtain ⟨J, hJ, hweight⟩ := hH W
  let I : Finset U := Finset.univ.filter fun x ↦ f x ∈ J
  refine ⟨I, independent_preimage hf hJ, ?_⟩
  have htotal : (∑ y, W y) = ∑ x, w x := by
    simp only [W]
    simpa using Finset.sum_fiberwise (Finset.univ : Finset U) f w
  have hselected : (∑ y ∈ J, W y) = ∑ x ∈ I, w x := by
    simp only [W, I]
    simpa using Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset U) J f w
  rw [← htotal, ← hselected]
  exact hweight

/-- Characteristic multiplicities recover the hereditary cardinality conclusion. -/
lemma large_independent_subset {V : Type*} [Fintype V] [DecidableEq V]
    {H : FinHypergraph V} (hH : NatFractionalThird H) (Y : Finset V) :
    ∃ Z : Finset V, Z ⊆ Y ∧ Independent H Z ∧ Y.card ≤ 3 * Z.card := by
  let w : V → ℕ := fun x ↦ if x ∈ Y then 1 else 0
  obtain ⟨I, hI, hw⟩ := hH w
  let Z := I ∩ Y
  refine ⟨Z, Finset.inter_subset_right, ?_, ?_⟩
  · exact fun e he heZ ↦ hI e he (heZ.trans Finset.inter_subset_left)
  · simpa [w, Z, Finset.sum_ite_irrel, Finset.filter_mem_eq_inter] using hw

/-! ## Two finite incidence kernels for confinement

After one nonconstant section has been normalized, the ambient confinement proof only needs to
read the three outer line descriptions coordinate by coordinate.  The following two lemmas package
that bookkeeping.  They are deliberately stated for an arbitrary alphabet and coordinate type.
-/

section OuterIncidenceKernels

variable {A I : Type*}

/-- A line is determined by its `idxFun`. -/
lemma line_eq_of_idxFun_eq {U W : Combinatorics.Line A I}
    (h : U.idxFun = W.idxFun) : U = W := by
  cases U
  cases W
  simp_all only [Combinatorics.Line.mk.injEq]

/-- If all coordinates have the `110`, `010`-constant, or `011` pattern displayed below, then
the three lines are concurrent and their moving supports form the exact RRS tripod relation.
The witnesses `sS` and `sT` say that both nonconstant section types really occur, so the three
outer lines are distinct. -/
lemma isRawTripod_of_section_table
    (U W Z : Combinatorics.Line A I) (a : A) (sS sT : I)
    (htable : ∀ s,
      (∃ c, U.idxFun s = some c ∧ W.idxFun s = some c ∧ Z.idxFun s = some c) ∨
      (U.idxFun s = none ∧ W.idxFun s = none ∧ Z.idxFun s = some a) ∨
      (U.idxFun s = some a ∧ W.idxFun s = none ∧ Z.idxFun s = none))
    (hS : U.idxFun sS = none ∧ W.idxFun sS = none ∧ Z.idxFun sS = some a)
    (hT : U.idxFun sT = some a ∧ W.idxFun sT = none ∧ Z.idxFun sT = none) :
    IsRawTripod U W Z := by
  have hUW : U ≠ W := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sT) h
    simp [hT.1, hT.2.1] at this
  have hUZ : U ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.1, hS.2.2] at this
  have hWZ : W ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.2.1, hS.2.2] at this
  have hcommon : RawLinesCommonPoint U W Z := by
    refine ⟨a, a, a, ?_, ?_⟩
    · funext s
      rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
      · simp [Combinatorics.Line.coe_apply, hUc, hWc]
      · simp [Combinatorics.Line.coe_apply, hS'.1, hS'.2.1]
      · simp [Combinatorics.Line.coe_apply, hT'.1, hT'.2.1]
    · funext s
      rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
      · simp [Combinatorics.Line.coe_apply, hWc, hZc]
      · simp [Combinatorics.Line.coe_apply, hS'.2.1, hS'.2.2]
      · simp [Combinatorics.Line.coe_apply, hT'.2.1, hT'.2.2]
  refine ⟨hUW, hUZ, hWZ, hcommon, Or.inr (Or.inl ?_)⟩
  constructor
  · ext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [RawMovingSet, hUc, hWc, hZc]
    · simp [RawMovingSet, hS'.1, hS'.2.1, hS'.2.2]
    · simp [RawMovingSet, hT'.1, hT'.2.1, hT'.2.2]
  · rw [Set.disjoint_left]
    intro s hsU hsZ
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [RawMovingSet, hUc] at hsU
    · simp [RawMovingSet, hS'.2.2] at hsZ
    · simp [RawMovingSet, hT'.1] at hsU

/-- The complementary status table has three pairwise intersections and no common point.  This is
the precise outer-line triangle created by two different source section-lines once a third section
type has been ruled out by linearity of the base hypergraph. -/
lemma isRawTriangle_of_section_table
    (U W Z : Combinatorics.Line A I) (a b : A) (sS sT : I) (hab : a ≠ b)
    (htable : ∀ s,
      (∃ c, U.idxFun s = some c ∧ W.idxFun s = some c ∧ Z.idxFun s = some c) ∨
      (U.idxFun s = none ∧ W.idxFun s = none ∧ Z.idxFun s = some a) ∨
      (U.idxFun s = none ∧ W.idxFun s = some b ∧ Z.idxFun s = none))
    (hS : U.idxFun sS = none ∧ W.idxFun sS = none ∧ Z.idxFun sS = some a)
    (hT : U.idxFun sT = none ∧ W.idxFun sT = some b ∧ Z.idxFun sT = none) :
    IsRawTriangle U W Z := by
  have hUW : U ≠ W := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sT) h
    simp [hT.1, hT.2.1] at this
  have hUZ : U ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.1, hS.2.2] at this
  have hWZ : W ≠ Z := by
    intro h
    have := congrArg (fun L : Combinatorics.Line A I ↦ L.idxFun sS) h
    simp [hS.2.1, hS.2.2] at this
  have hUbW : U b = W b := by
    funext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [Combinatorics.Line.coe_apply, hUc, hWc]
    · simp [Combinatorics.Line.coe_apply, hS'.1, hS'.2.1]
    · simp [Combinatorics.Line.coe_apply, hT'.1, hT'.2.1]
  have hUaZ : U a = Z a := by
    funext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [Combinatorics.Line.coe_apply, hUc, hZc]
    · simp [Combinatorics.Line.coe_apply, hS'.1, hS'.2.2]
    · simp [Combinatorics.Line.coe_apply, hT'.1, hT'.2.2]
  have hWaZb : W a = Z b := by
    funext s
    rcases htable s with ⟨c, hUc, hWc, hZc⟩ | hS' | hT'
    · simp [Combinatorics.Line.coe_apply, hWc, hZc]
    · simp [Combinatorics.Line.coe_apply, hS'.2.1, hS'.2.2]
    · simp [Combinatorics.Line.coe_apply, hT'.2.1, hT'.2.2]
  refine ⟨hUW, hUZ, hWZ, ⟨b, b, hUbW⟩, ⟨a, a, hUaZ⟩,
    ⟨a, b, hWaZb⟩, ?_⟩
  rintro ⟨i, j, k, hij, hjk⟩
  have hSij := congrFun hij sS
  have hSjk := congrFun hjk sS
  have hTij := congrFun hij sT
  simp [Combinatorics.Line.coe_apply, hS.1, hS.2.1, hS.2.2,
    hT.1, hT.2.1, hT.2.2] at hSij hSjk hTij
  apply hab
  exact hSjk.symm.trans (hSij.symm.trans hTij)

end OuterIncidenceKernels

/-! ## The all-outside branch of normalized confinement -/

section NormalizedConfinement

variable {V P C N : Type*} [DecidableEq V]
variable {G : ThreeGraph V}

/-- If all three entries of the normalized source section are outside the music fiber, then the
three chosen outer lines coincide.  This is the easy branch of Proposition 4.5: every other
nonconstant section shares two source points with the normalized section, while a constant section
must be fiber-valued. -/
theorem normalized_lines_eq_of_third_not_fiber
    (source : Picture G P C) (x : V)
    (lines : Set (Combinatorics.Line (MusicFiber source x) N))
    (l : Alphabet → RawAmalgamPoint source x lines)
    (q : NormalizedRawQuasiline source x lines l)
    (hthird : source.proj
      (sectionPoint source x (q.line 2) (q.point 2) q.coordinate) ≠ x) :
    q.line 0 = q.line 1 ∧ q.line 1 = q.line 2 := by
  let base : Alphabet → P := fun i ↦
    sectionPoint source x (q.line i) (q.point i) q.coordinate
  have hbase2 : base 2 = q.point 2 := by
    apply (sectionPoint_mem_fiber_or_eq source x (q.line 2) (q.point 2)
      q.coordinate).resolve_left
    exact hthird
  have hbase_point : base = q.point := by
    funext i
    fin_cases i
    · exact q.section_zero
    · exact q.section_one
    · exact hbase2
  have hp_injective : Injective q.point := by
    intro i j hij
    apply q.source_section.1
    change base i = base j
    rw [hbase_point]
    exact hij
  have hp2 : source.proj (q.point 2) ≠ x := by
    simpa only [base, hbase2] using hthird
  have hp_out : ∀ a, source.proj (q.point a) ≠ x := by
    intro a
    fin_cases a
    · exact q.point_zero_not_fiber
    · exact q.point_one_not_fiber
    · exact hp2
  have hidx : ∀ s i j, (q.line i).idxFun s = (q.line j).idxFun s := by
    intro s i j
    let row : Alphabet → P := fun a ↦
      sectionPoint source x (q.line a) (q.point a) s
    rcases raw_quasiline_section source x lines (fun a ↦ l (q.perm a))
        q.line q.point q.word_eq q.outer_quasiline s with hconstant | hquasi
    · obtain ⟨z, hz⟩ := hconstant
      have hzf : source.proj z = x := by
        by_contra hzout
        have hz0 : z = q.point 0 := by
          exact (hz 0).symm.trans <|
            (sectionPoint_mem_fiber_or_eq source x (q.line 0) (q.point 0) s).resolve_left
              (by simpa [row, hz 0] using hzout)
        have hz1 : z = q.point 1 := by
          exact (hz 1).symm.trans <|
            (sectionPoint_mem_fiber_or_eq source x (q.line 1) (q.point 1) s).resolve_left
              (by simpa [row, hz 1] using hzout)
        exact (by decide : (0 : Alphabet) ≠ 1) <| hp_injective (hz0.symm.trans hz1)
      obtain ⟨fi, hfi, hfiz⟩ := fixed_value_of_sectionPoint_eq source x
        (q.line i) (q.point i) z
        (hp_out i) hzf s (hz i)
      obtain ⟨fj, hfj, hfjz⟩ := fixed_value_of_sectionPoint_eq source x
        (q.line j) (q.point j) z
        (hp_out j) hzf s (hz j)
      have hfij : fi = fj := Subtype.ext (hfiz.trans hfjz.symm)
      simpa [hfi, hfj, hfij]
    · have hrow_line : IsCombinatorialLine source.embed row :=
        source.quasiline_is_line row hquasi
      have hrow_edge : MapsOntoEdge G source.proj row :=
        source.quasiline_maps_edge row hquasi
      have hproj_injective : Injective (fun a ↦ source.proj (row a)) :=
        mapsOntoEdge_proj_injective source hrow_edge
      have hatMostOne : ∀ a b, source.proj (row a) = x →
          source.proj (row b) = x → a = b := by
        intro a b ha hb
        exact hproj_injective (ha.trans hb.symm)
      obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_two_not hatMostOne
      have hrow0 : row (σ 0) = q.point (σ 0) := by
        exact (sectionPoint_mem_fiber_or_eq source x (q.line (σ 0))
          (q.point (σ 0)) s).resolve_left hσ0
      have hrow1 : row (σ 1) = q.point (σ 1) := by
        exact (sectionPoint_mem_fiber_or_eq source x (q.line (σ 1))
          (q.point (σ 1)) s).resolve_left hσ1
      have hp_line : IsCombinatorialLine source.embed q.point := by
        have hp_quasi : IsQuasiline source.embed q.point := by
          simpa only [base, hbase_point] using q.source_section
        exact source.quasiline_is_line q.point hp_quasi
      have hrange : Set.range row = Set.range q.point :=
        combinatorialLine_range_eq_of_two_points source.embed source.embed_injective
          row q.point hrow_line hp_line (σ.injective.ne (by decide : (0 : Alphabet) ≠ 1))
          hrow0 hrow1
      have hadmissible : Erdos847ConfinementKernels.Admissible
          (fun z ↦ source.proj z = x) q.point row := by
        intro a
        simpa only [row] using
          (sectionPoint_mem_fiber_or_eq source x (q.line a) (q.point a) s)
      have hrow_point : row = q.point := by
        by_contra hne
        have hcoordinate_ne : row 0 ≠ q.point 0 ∨ row 1 ≠ q.point 1 ∨
            row 2 ≠ q.point 2 := by
          by_contra hall
          push_neg at hall
          apply hne
          funext a
          fin_cases a
          · exact hall.1
          · exact hall.2.1
          · exact hall.2.2
        have hrange' : Set.range row =
            ({q.point 0, q.point 1, q.point 2} : Set P) := by
          rw [hrange, range_fin3]
        rcases Erdos847ConfinementKernels.same_range_normal_forms
            q.point_zero_not_fiber q.point_one_not_fiber hquasi.1 hadmissible
            hrange' hcoordinate_ne with hswap | hswap
        · exact (hp_injective.ne (by decide : (2 : Alphabet) ≠ 0)) hswap.2.2.2
        · exact (hp_injective.ne (by decide : (2 : Alphabet) ≠ 1)) hswap.2.2.2
      have hmove : ∀ a, (q.line a).idxFun s = none := by
        intro a
        apply (moving_iff_sectionPoint_eq source x (q.line a) (q.point a)
          (hp_out a) s).2
        exact congrFun hrow_point a
      rw [hmove i, hmove j]
  constructor
  · apply line_eq_of_idxFun_eq
    funext s
    exact hidx s 0 1
  · apply line_eq_of_idxFun_eq
    funext s
    exact hidx s 1 2

end NormalizedConfinement

end Erdos847FiniteArch

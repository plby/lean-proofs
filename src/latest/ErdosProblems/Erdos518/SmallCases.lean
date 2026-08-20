/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.BasicBounds
import ErdosProblems.Erdos518.CoreBipartite
import ErdosProblems.Erdos518.DenseBipartite
import ErdosProblems.Erdos518.CoverDevice
import ErdosProblems.Erdos518.ExtensionObstruction
import ErdosProblems.Erdos518.CaseArithmetic

/-!
# The cases `sqrt n <= 3`

This file rules out the finitely many parameter configurations left after the general
minimal-counterexample bounds in the proof of Erdos Problem 518.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance smallCasesDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Complete-core bookkeeping -/

/-- In the red bipartite graph on `X,Y`, the complete right core is exactly `Y0`. -/
lemma rightCore_eq_Y0 : rightCore C.G C.X C.Y = C.Y0 := by
  classical
  ext y
  simp only [rightCore, Finset.mem_filter]
  constructor
  · rintro ⟨hyY, hall⟩
    apply C.mem_Y0.mpr
    refine ⟨hyY, Finset.card_eq_zero.mpr ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxX : x ∈ C.X := (Finset.mem_filter.mp hx).1
    have hblue : C.Gᶜ.Adj y x := (Finset.mem_filter.mp hx).2
    exact ((SimpleGraph.compl_adj C.G y x).mp hblue).2 (hall x hxX).symm
  · intro hy0
    have hy := C.mem_Y0.mp hy0
    exact ⟨hy.1, fun x hx ↦ (C.adj_of_mem_Y0_mem_X hy0 hx).symm⟩

/-- Consequently the exceptional right part is exactly `Y1`. -/
lemma rightExceptional_eq_Y1 : rightExceptional C.G C.X C.Y = C.Y1 := by
  classical
  simp only [rightExceptional, C.rightCore_eq_Y0, Y1]

/-- Every exceptional vertex on the left has a blue neighbour in `Y1`. -/
lemma leftExceptional_has_blue_neighbor {x : V}
    (hx : x ∈ leftExceptional C.G C.X C.Y) :
    ∃ y ∈ C.Y1, C.Gᶜ.Adj y x := by
  classical
  have hxdata : x ∈ C.X ∧ x ∉ leftCore C.G C.X C.Y :=
    Finset.mem_sdiff.mp hx
  have hnall : ¬ ∀ y ∈ C.Y, C.G.Adj x y := by
    intro hall
    apply hxdata.2
    simp only [leftCore, Finset.mem_filter]
    exact ⟨hxdata.1, hall⟩
  push Not at hnall
  obtain ⟨y, hyY, hxy⟩ := hnall
  have hyx : y ≠ x := by
    intro heq
    subst x
    exact Finset.disjoint_left.mp C.X_disjoint_Y hxdata.1 hyY
  have hblue : C.Gᶜ.Adj y x :=
    (SimpleGraph.compl_adj C.G y x).mpr ⟨hyx, fun h ↦ hxy h.symm⟩
  have hpos : 0 < C.blueDegreeToX y := by
    apply Finset.card_pos.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨hxdata.1, hblue⟩⟩
  exact ⟨y, C.mem_Y1.mpr ⟨hyY, hpos.ne'⟩, hblue⟩

/-- If `Y1` is a singleton, the left exceptional part has size at most `mu`. -/
lemma card_leftExceptional_le_mu_of_a1_eq_one (ha1 : C.a1 = 1) :
    (leftExceptional C.G C.X C.Y).card ≤ C.mu := by
  classical
  obtain ⟨z, hzY1⟩ := C.Y1_nonempty
  have hY1 : C.Y1 = {z} := by
    obtain ⟨z', hz'⟩ := Finset.card_eq_one.mp (by simpa [a1] using ha1)
    have hzz' : z = z' := by simpa [hz'] using hzY1
    simpa [hzz'] using hz'
  let B : Finset V := C.X.filter fun x ↦ C.Gᶜ.Adj z x
  have hsub : leftExceptional C.G C.X C.Y ⊆ B := by
    intro x hx
    obtain ⟨y, hy, hblue⟩ := C.leftExceptional_has_blue_neighbor hx
    have hyz : y = z := by simpa [hY1] using hy
    subst y
    exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hx, hblue⟩
  calc
    (leftExceptional C.G C.X C.Y).card ≤ B.card := Finset.card_le_card hsub
    _ = C.blueDegreeToX z := rfl
    _ ≤ C.mu := C.blueDegreeToX_le_mu_of_mem_Y1 hzY1

/-- The complete left core and its exceptional complement partition `X`. -/
lemma card_leftCore_add_leftExceptional :
    (leftCore C.G C.X C.Y).card + (leftExceptional C.G C.X C.Y).card = C.X.card := by
  classical
  have hsub : leftCore C.G C.X C.Y ⊆ C.X := by
    let L : Finset V := C.X.filter fun x ↦ ∀ y ∈ C.Y, C.G.Adj x y
    have hEq : leftCore C.G C.X C.Y = L := by
      ext x
      simp only [leftCore, L, Finset.mem_filter]
    rw [hEq]
    exact Finset.filter_subset _ _
  rw [leftExceptional, Finset.card_sdiff_of_subset hsub]
  exact Nat.add_sub_of_le (Finset.card_mono hsub)

/-- A specialization of the complete-core lemma for singleton `Y1`.  The caller supplies
the exact strict core ratio, which differs in the `a0=1` and `a0=2` applications. -/
lemma has_red_cover_of_a1_eq_one (ha1 : C.a1 = 1)
    (hsize : C.Y.card < C.X.card)
    (hratio : 2 * (leftExceptional C.G C.X C.Y).card <
      (leftCore C.G C.X C.Y).card * C.a0) :
    HasPathCoverOnAtMost C.G (((C.X ∪ C.Y : Finset V) : Set V))
      (C.X.card ⌈/⌉ (C.Y.card + 1)) := by
  classical
  apply complete_core_bipartite_path_cover C.G C.X C.Y C.X_disjoint_Y
  · rw [C.rightCore_eq_Y0]
    exact C.Y0_nonempty
  · exact hsize
  · right
    rw [C.rightExceptional_eq_Y1, C.rightCore_eq_Y0]
    have hY1card : C.Y1.card = 1 := by simpa [a1] using ha1
    simpa [hY1card, a0] using hratio

lemma red_cover_of_union_is_global {k : ℕ}
    (h : HasPathCoverOnAtMost C.G (((C.X ∪ C.Y : Finset V) : Set V)) k) :
    HasPathCoverAtMost C.G k := by
  rw [hasPathCoverAtMost_iff_on_univ]
  simpa [C.X_union_Y] using h

/-- On an outside vertex, the number of non-red neighbours in `X` is its blue degree. -/
lemma card_nonRedNeighboursIn_X_eq_blueDegree {y : V} (hy : y ∈ C.Y) :
    (nonRedNeighboursIn C.G C.X y).card = C.blueDegreeToX y := by
  classical
  congr 1
  ext x
  simp only [nonRedNeighboursIn, blueDegreeToX, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hred⟩
    have hyx : y ≠ x := by
      intro h
      subst x
      exact Finset.disjoint_left.mp C.X_disjoint_Y hx hy
    exact ⟨hx, (SimpleGraph.compl_adj C.G y x).mpr ⟨hyx, hred⟩⟩
  · rintro ⟨hx, hblue⟩
    exact ⟨hx, ((SimpleGraph.compl_adj C.G y x).mp hblue).2⟩

lemma sparse_nonRedNeighboursIn_X {y : V} (hy : y ∈ C.Y1) :
    (nonRedNeighboursIn C.G C.X y).card ≤ C.mu := by
  rw [C.card_nonRedNeighboursIn_X_eq_blueDegree (C.Y1_subset_Y hy)]
  exact C.blueDegreeToX_le_mu_of_mem_Y1 hy

/-! ## A path plus a cover of the unused part of `X` -/

/-- Add one displayed path to a two-path cover of the unused part of `X`.  If the displayed
path contains every vertex of `Y`, this contradicts a `c=3` counterexample. -/
lemma path_plus_unused_X_cover_impossible (hc : C.c = 3) {p : List V}
    (hp : IsPath C.G p) (hpY : ∀ y ∈ C.Y, y ∈ p)
    (hD : HasPathCoverOnAtMost C.G ((C.X \ p.toFinset : Finset V) : Set V) 2) : False := by
  classical
  obtain ⟨ps, hpslen, hpsPath, hpsCover⟩ := hD
  apply C.cover_failures.1
  refine ⟨p :: ps, ?_, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact hpsPath q hq
  · intro v
    by_cases hvp : v ∈ p
    · exact ⟨p, by simp, hvp⟩
    · have hvXY : v ∈ C.X ∪ C.Y := by simpa [C.X_union_Y]
      rcases Finset.mem_union.mp hvXY with hvX | hvY
      · obtain ⟨q, hq, hvq⟩ := hpsCover v
          (Finset.mem_sdiff.mpr ⟨hvX, by simpa using hvp⟩)
        exact ⟨q, by simp [hq], hvq⟩
      · exact (hvp (hpY v hvY)).elim

/-! ## The case `c=2` -/

lemma c_two_mu_one_impossible
    (hc : C.c = 2) (hr : C.r = 4) (hw : C.w = 2)
    (ha0 : C.a0 = 1) (ha1 : C.a1 = 1) (hmu : C.mu = 1) : False := by
  have hXcard : C.X.card = 6 := by
    have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
    norm_num only [hc, hr, hw] at hsum
    omega
  have hYcard : C.Y.card = 2 := by simpa only [C.w_eq_card_Y] using hw
  have hE := C.card_leftExceptional_le_mu_of_a1_eq_one ha1
  have hparts := C.card_leftCore_add_leftExceptional
  have hratio : 2 * (leftExceptional C.G C.X C.Y).card <
      (leftCore C.G C.X C.Y).card * C.a0 := by
    rw [hmu] at hE
    rw [ha0]
    omega
  have hlocal := C.has_red_cover_of_a1_eq_one ha1 (by omega) hratio
  have hceil : C.X.card ⌈/⌉ (C.Y.card + 1) ≤ C.c := by
    rw [hXcard, hYcard, hc]
    norm_num
  exact C.cover_failures.1 (C.red_cover_of_union_is_global (hlocal.mono hceil))

/-- Cardinality of the reservoir outside the predecessor clique. -/
lemma extensionReservoir_card {z : V} (hz : z ∈ C.Y) :
    (C.extensionReservoir z).card = C.X.card - (C.blueDegreeToX z + 1) := by
  classical
  rw [extensionReservoir,
    Finset.card_sdiff_of_subset (C.extensionPredecessorSet_subset_X z),
    C.extensionPredecessorSet_card hz]

lemma c_two_mu_two_impossible
    (hc : C.c = 2) (hr : C.r = 4) (hw : C.w = 2)
    (ha0 : C.a0 = 1) (ha1 : C.a1 = 1) (hmu : C.mu = 2) : False := by
  classical
  have hXcard : C.X.card = 6 := by
    have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
    norm_num only [hc, hr, hw] at hsum
    omega
  have hY0card : C.Y0.card = 1 := by simpa [a0] using ha0
  have hY1card : C.Y1.card = 1 := by simpa [a1] using ha1
  obtain ⟨y0, hY0⟩ := Finset.card_eq_one.mp hY0card
  obtain ⟨z, hY1⟩ := Finset.card_eq_one.mp hY1card
  have hy0 : y0 ∈ C.Y0 := by simp [hY0]
  have hz1 : z ∈ C.Y1 := by simp [hY1]
  have hzY : z ∈ C.Y := C.Y1_subset_Y hz1
  have hy0Y : y0 ∈ C.Y := C.Y0_subset_Y hy0
  have hzy0 : z ≠ y0 := by
    intro h
    subst z
    exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hy0 hz1
  have hzdeg : C.blueDegreeToX z = C.mu := by
    obtain ⟨z', hz', hzdeg⟩ :=
      C.exists_mem_Y1_blueDegreeToX_eq_mu C.Y1_nonempty
    have hzz : z' = z := by simpa [hY1] using hz'
    simpa [hzz] using hzdeg
  let W := C.extensionReservoir z
  have hWcard : W.card = 3 := by
    rw [show W.card = C.X.card - (C.blueDegreeToX z + 1) by
      exact C.extensionReservoir_card hzY]
    rw [hzdeg, hmu, hXcard]
  let R := redNeighboursIn C.G W z
  have hRcard : 1 ≤ R.card := by
    have hbound := card_le_redNeighboursIn_add
      (X := C.X) (D := W) (y := z) (μ := C.mu)
      (C.extensionReservoir_subset_X z) (C.sparse_nonRedNeighboursIn_X hz1)
    change W.card ≤ R.card + C.mu at hbound
    omega
  obtain ⟨x0, hx0R⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  have hx0W : x0 ∈ W := by
    exact (Finset.mem_filter.mp (by simpa [R, redNeighboursIn] using hx0R)).1
  have hsmall : ({x0} : Finset V).card < W.card := by simp [hWcard]
  obtain ⟨x1, hx1W, hx1not⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hx01 : x0 ≠ x1 := by
    intro h
    subst x1
    exact hx1not (by simp)
  have hcount : C.extensionCount z = 2 := by
    simp only [extensionCount]
    rw [hzdeg, hmu, hr]
  apply C.clique_extension_obstruction_list hz1 (by omega : C.blueDegreeToX z < C.r)
      (ys := [z, y0]) (xs := [x0, x1])
  · simp [hcount]
  · simp [hcount]
  · simp [hzy0]
  · simp [hx01]
  · intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact hzY
    · exact hy0Y
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hx0W
    · exact hx1W
  · exact .cons (Finset.mem_filter.mp (by simpa [R, redNeighboursIn] using hx0R)).2
      (.cons (C.adj_of_mem_Y0_mem_X hy0
        (C.extensionReservoir_subset_X z hx1W)) .nil)
  · exact .cons
      (C.adj_of_mem_Y0_mem_X hy0
        (C.extensionReservoir_subset_X z hx0W)).symm .nil

lemma c_two_impossible_of_mu_le
    (hc : C.c = 2) (hmu : C.mu ≤ C.r - 2) : False := by
  have hwlo : 2 ≤ C.w := by
    have h := C.w_ge_c
    omega
  have hrhi : C.r ≤ 4 := by
    have h := C.r_le_two_mul_c
    omega
  obtain ⟨hr, hw⟩ := c_two_parameters hwlo C.w_le_r_sub_two hrhi
  obtain ⟨ha0, ha1⟩ :=
    c_two_partition hw C.w_eq_a0_add_a1 C.one_le_a0 C.one_le_a1
  have hmuLo : 1 ≤ C.mu := C.one_le_mu C.Y1_nonempty
  rcases c_two_mu_cases hr hmuLo hmu with hmu1 | hmu2
  · exact C.c_two_mu_one_impossible hc hr hw ha0 ha1 hmu1
  · exact C.c_two_mu_two_impossible hc hr hw ha0 ha1 hmu2

/-! ## The case `c=3,w=3` -/

lemma c_three_w_three_impossible
    (hc : C.c = 3) (hw : C.w = 3) (hmu : C.mu ≤ C.r - 2) : False := by
  have hrlo : 5 ≤ C.r := by
    have h := C.w_le_r_sub_two
    omega
  have hrhi : C.r ≤ 6 := by
    have h := C.r_le_two_mul_c
    omega
  obtain ⟨ha0, ha1⟩ :=
    c_three_w_three_partition hw C.w_eq_a0_add_a1
      (by have h := C.a0_lower_bound; omega) C.one_le_a1
  have hXcard : C.X.card = 6 + C.r := by
    have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
    norm_num only [hc, hw] at hsum
    omega
  have hYcard : C.Y.card = 3 := by simpa only [C.w_eq_card_Y] using hw
  have hE := C.card_leftExceptional_le_mu_of_a1_eq_one ha1
  have hparts := C.card_leftCore_add_leftExceptional
  have hratio : 2 * (leftExceptional C.G C.X C.Y).card <
      (leftCore C.G C.X C.Y).card * C.a0 := by
    rw [ha0]
    rw [hXcard] at hparts
    omega
  have hlocal := C.has_red_cover_of_a1_eq_one ha1 (by omega) hratio
  have hceil : C.X.card ⌈/⌉ (C.Y.card + 1) ≤ C.c := by
    rw [hXcard, hYcard, hc]
    exact c_three_core_ceil_bound hrhi
  exact C.cover_failures.1 (C.red_cover_of_union_is_global (hlocal.mono hceil))

/-! ## The cases `c=3,w=4,mu=4` and `mu=3` -/

lemma c_three_w_four_mu_four_impossible
    (hc : C.c = 3) (hr : C.r = 6) (hw : C.w = 4)
    (hmu : C.mu = 4) : False := by
  classical
  have hXcard : C.X.card = 11 := by
    have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
    norm_num only [hc, hr, hw] at hsum
    omega
  obtain ⟨z, hz1, hzdeg⟩ := C.exists_mem_Y1_blueDegreeToX_eq_mu C.Y1_nonempty
  have hzY : z ∈ C.Y := C.Y1_subset_Y hz1
  obtain ⟨y0, hy0⟩ := C.Y0_nonempty
  have hy0Y : y0 ∈ C.Y := C.Y0_subset_Y hy0
  have hzy0 : z ≠ y0 := by
    intro h
    subst z
    exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hy0 hz1
  let W := C.extensionReservoir z
  have hWcard : W.card = 6 := by
    rw [show W.card = C.X.card - (C.blueDegreeToX z + 1) by
      exact C.extensionReservoir_card hzY]
    rw [hzdeg, hmu, hXcard]
  let R := redNeighboursIn C.G W z
  have hRcard : 2 ≤ R.card := by
    have hbound := card_le_redNeighboursIn_add
      (X := C.X) (D := W) (y := z) (μ := C.mu)
      (C.extensionReservoir_subset_X z) (C.sparse_nonRedNeighboursIn_X hz1)
    change W.card ≤ R.card + C.mu at hbound
    omega
  obtain ⟨xs, hxsN, hrep⟩ :=
    exists_nodup_representativeList ([R, R] : List (Finset V)) (by
      intro D hD
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hD
      rcases hD with rfl | rfl <;> simpa using hRcard)
  obtain ⟨x0, tail, hx0R, hrepTail, rfl⟩ := List.forall₂_cons_left_iff.mp hrep
  obtain ⟨x1, rest, hx1R, hrepRest, rfl⟩ := List.forall₂_cons_left_iff.mp hrepTail
  have hrest : rest = [] := List.forall₂_nil_left_iff.mp hrepRest
  subst rest
  have hx0W : x0 ∈ W :=
    (Finset.mem_filter.mp (by simpa [R, redNeighboursIn] using hx0R)).1
  have hx1W : x1 ∈ W :=
    (Finset.mem_filter.mp (by simpa [R, redNeighboursIn] using hx1R)).1
  have hcount : C.extensionCount z = 2 := by
    simp only [extensionCount]
    rw [hzdeg, hmu, hr]
  apply C.clique_extension_obstruction_list hz1 (by omega : C.blueDegreeToX z < C.r)
      (ys := [z, y0]) (xs := [x0, x1])
  · simp [hcount]
  · simp [hcount]
  · simp [hzy0]
  · exact hxsN
  · intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact hzY
    · exact hy0Y
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hx0W
    · exact hx1W
  · exact .cons (Finset.mem_filter.mp (by simpa [R, redNeighboursIn] using hx0R)).2
      (.cons (C.adj_of_mem_Y0_mem_X hy0
        (C.extensionReservoir_subset_X z hx1W)) .nil)
  · exact .cons
      (C.adj_of_mem_Y0_mem_X hy0
        (C.extensionReservoir_subset_X z hx0W)).symm .nil

lemma c_three_w_four_mu_three_impossible
    (hc : C.c = 3) (hr : C.r = 6) (hw : C.w = 4)
    (hmu : C.mu = 3) : False := by
  classical
  have hXcard : C.X.card = 11 := by
    have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
    norm_num only [hc, hr, hw] at hsum
    omega
  have hYcard : C.Y.card = 4 := by simpa only [C.w_eq_card_Y] using hw
  obtain ⟨z, hz1, hzdeg⟩ := C.exists_mem_Y1_blueDegreeToX_eq_mu C.Y1_nonempty
  have hzY : z ∈ C.Y := C.Y1_subset_Y hz1
  obtain ⟨y0, hy0⟩ := C.Y0_nonempty
  have hy0Y : y0 ∈ C.Y := C.Y0_subset_Y hy0
  have hzy0 : z ≠ y0 := by
    intro h
    subst z
    exact Finset.disjoint_left.mp C.Y0_disjoint_Y1 hy0 hz1
  have hpaircard : ({z, y0} : Finset V).card = 2 := by simp [hzy0]
  have hsmall : ({z, y0} : Finset V).card < C.Y.card := by omega
  obtain ⟨y2, hy2Y, hy2not⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hy2z : y2 ≠ z := by
    intro h
    subst y2
    exact hy2not (by simp)
  have hy2y0 : y2 ≠ y0 := by
    intro h
    subst y2
    exact hy2not (by simp)
  let W := C.extensionReservoir z
  have hWcard : W.card = 7 := by
    rw [show W.card = C.X.card - (C.blueDegreeToX z + 1) by
      exact C.extensionReservoir_card hzY]
    rw [hzdeg, hmu, hXcard]
  let Rz := redNeighboursIn C.G W z
  let R2 := redNeighboursIn C.G W y2
  have hRzcard : 4 ≤ Rz.card := by
    have hbound := card_le_redNeighboursIn_add
      (X := C.X) (D := W) (y := z) (μ := C.mu)
      (C.extensionReservoir_subset_X z) (C.sparse_nonRedNeighboursIn_X hz1)
    change W.card ≤ Rz.card + C.mu at hbound
    omega
  have hR2card : 4 ≤ R2.card := by
    have hsparse : (nonRedNeighboursIn C.G C.X y2).card ≤ C.mu := by
      have heq : nonRedNeighboursIn C.G C.X y2 =
          C.X.filter fun x ↦ C.Gᶜ.Adj y2 x := by
        ext x
        simp only [nonRedNeighboursIn, Finset.mem_filter]
        constructor
        · rintro ⟨hx, hred⟩
          have hyx : y2 ≠ x := by
            intro h
            subst x
            exact Finset.disjoint_left.mp C.X_disjoint_Y hx hy2Y
          exact ⟨hx, (SimpleGraph.compl_adj C.G y2 x).mpr ⟨hyx, hred⟩⟩
        · rintro ⟨hx, hblue⟩
          exact ⟨hx, ((SimpleGraph.compl_adj C.G y2 x).mp hblue).2⟩
      rw [heq]
      exact C.blueDegreeToX_le_mu_of_mem_Y hy2Y
    have hbound := card_le_redNeighboursIn_add
      (X := C.X) (D := W) (y := y2) (μ := C.mu)
      (C.extensionReservoir_subset_X z) hsparse
    change W.card ≤ R2.card + C.mu at hbound
    omega
  obtain ⟨xs, hxsN, hrep⟩ :=
    exists_nodup_representativeList ([Rz, R2, R2] : List (Finset V)) (by
      intro D hD
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hD
      rcases hD with rfl | rfl | rfl <;> norm_num <;> omega)
  obtain ⟨x0, tail0, hx0R, hrep0, rfl⟩ := List.forall₂_cons_left_iff.mp hrep
  obtain ⟨x1, tail1, hx1R, hrep1, rfl⟩ := List.forall₂_cons_left_iff.mp hrep0
  obtain ⟨x2, rest, hx2R, hrep2, rfl⟩ := List.forall₂_cons_left_iff.mp hrep1
  have hrest : rest = [] := List.forall₂_nil_left_iff.mp hrep2
  subst rest
  have hx0W : x0 ∈ W :=
    (Finset.mem_filter.mp (by simpa [Rz, redNeighboursIn] using hx0R)).1
  have hx1W : x1 ∈ W :=
    (Finset.mem_filter.mp (by simpa [R2, redNeighboursIn] using hx1R)).1
  have hx2W : x2 ∈ W :=
    (Finset.mem_filter.mp (by simpa [R2, redNeighboursIn] using hx2R)).1
  have hcount : C.extensionCount z = 3 := by
    simp only [extensionCount]
    rw [hzdeg, hmu, hr]
  apply C.clique_extension_obstruction_list hz1 (by omega : C.blueDegreeToX z < C.r)
      (ys := [z, y0, y2]) (xs := [x0, x1, x2])
  · simp [hcount]
  · simp [hcount]
  · have hzy2 : z ≠ y2 := Ne.symm hy2z
    have hy0y2 : y0 ≠ y2 := Ne.symm hy2y0
    simp [hzy0, hzy2, hy0y2]
  · exact hxsN
  · intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact hzY
    · exact hy0Y
    · exact hy2Y
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hx0W
    · exact hx1W
    · exact hx2W
  · exact .cons
      (Finset.mem_filter.mp (by simpa [Rz, redNeighboursIn] using hx0R)).2
      (.cons (C.adj_of_mem_Y0_mem_X hy0
        (C.extensionReservoir_subset_X z hx1W))
      (.cons (Finset.mem_filter.mp (by simpa [R2, redNeighboursIn] using hx2R)).2 .nil))
  · have hx1adj : C.G.Adj y2 x1 :=
      (Finset.mem_filter.mp (by simpa [R2, redNeighboursIn] using hx1R)).2
    exact .cons
      (C.adj_of_mem_Y0_mem_X hy0
        (C.extensionReservoir_subset_X z hx0W)).symm
      (.cons hx1adj.symm .nil)

/-! ## The case `c=3,w=4,mu≤2` -/

/-- The dense bipartite lemma gives a red path through all four outside vertices and four
vertices of `X`.  The seven unused vertices of `X` are covered by two more paths using the
covering device.  Its case (iii) is needed exactly when `a0=1`, with `p=3,q=2`. -/
lemma c_three_w_four_mu_le_two_impossible
    (hc : C.c = 3) (hr : C.r = 6) (hw : C.w = 4)
    (hmu : C.mu ≤ 2) : False := by
  classical
  have hXcard : C.X.card = 11 := by
    have hsum : C.X.card + C.w = C.c ^ 2 + C.r := by
      rw [← C.n_eq_card_X_add_w, C.n_eq_c_sq_add_r]
    norm_num only [hc, hr, hw] at hsum
    omega
  have hYcard : C.Y.card = 4 := by simpa only [C.w_eq_card_Y] using hw
  have hdense : ∀ y ∈ C.Y,
      C.X.card + C.Y.card ≤ 2 * (C.X.filter (C.G.Adj y)).card := by
    intro y hy
    have hblue := C.blueDegreeToX_le_mu_of_mem_Y hy
    have hdegree := C.redDegreeToX_add_blueDegreeToX hy
    change C.X.card + C.Y.card ≤ 2 * C.redDegreeToX y
    omega
  have hY : C.Y.Nonempty := Finset.Nonempty.mono C.Y1_subset_Y C.Y1_nonempty
  obtain ⟨P, hP, _hPlen, _hPsub, hPY, hPX⟩ :=
    exists_path_of_dense_bipartite C.G C.X C.Y C.X_disjoint_Y hY hdense
  let D : Finset V := C.X \ P.toFinset
  have hDcard : D.card = 7 := by
    dsimp only [D]
    rw [Finset.card_sdiff, hPX, hYcard, hXcard]
  have hDX : D ⊆ C.X := Finset.sdiff_subset
  have hsparse : ∀ y ∈ C.Y1,
      (nonRedNeighboursIn C.G C.X y).card ≤ C.mu := by
    exact fun y hy ↦ C.sparse_nonRedNeighboursIn_X hy
  have hcases : coverDeviceP D C.Y0 2 ≤ 0 ∨
      (0 < coverDeviceP D C.Y0 2 ∧
        coverDeviceP D C.Y0 2 ≤ (min 2 ((D.card - C.mu) / 2) : ℕ)) ∨
      (0 < coverDeviceP D C.Y0 2 ∧
        coverDeviceP D C.Y0 2 ≤ (coverDeviceQ D C.Y0 2 * C.Y1.card : ℕ) ∧
        coverDeviceP D C.Y0 2 - (coverDeviceQ D C.Y0 2 : ℕ) ≤
          (D.card : ℤ) - 2 * (C.mu : ℤ) ∧
        coverDeviceP D C.Y0 2 + (coverDeviceQ D C.Y0 2 : ℕ) ≤
          (D.card : ℤ) - (C.mu : ℤ)) := by
    have ha0 : 1 ≤ C.a0 := C.one_le_a0
    have ha1 : 1 ≤ C.a1 := C.one_le_a1
    have hasum := C.w_eq_a0_add_a1
    have hpEq : coverDeviceP D C.Y0 2 = 5 - 2 * (C.a0 : ℤ) := by
      simp only [coverDeviceP, hDcard, C.a0_eq_card_Y0]
      omega
    by_cases hp : coverDeviceP D C.Y0 2 ≤ 0
    · exact Or.inl hp
    by_cases ha0two : 2 ≤ C.a0
    · apply Or.inr
      apply Or.inl
      constructor
      · omega
      · have hpBound : coverDeviceP D C.Y0 2 ≤ (2 : ℕ) := by
          have ha0z : (2 : ℤ) ≤ (C.a0 : ℤ) := by exact_mod_cast ha0two
          calc
            coverDeviceP D C.Y0 2 = 5 - 2 * (C.a0 : ℤ) := hpEq
            _ ≤ (2 : ℕ) := by omega
        have hhalf : 2 ≤ (D.card - C.mu) / 2 := by
          rw [hDcard]
          omega
        have hmin : min 2 ((D.card - C.mu) / 2) = 2 := by omega
        simpa [hmin] using hpBound
    · apply Or.inr
      apply Or.inr
      have ha0eq : C.a0 = 1 := by omega
      have ha1eq : C.a1 = 3 := by omega
      have hY1card : C.Y1.card = 3 := by simpa [a1] using ha1eq
      have hpEqThree : coverDeviceP D C.Y0 2 = 3 := by omega
      have hqEq : coverDeviceQ D C.Y0 2 = 2 := by simp [coverDeviceQ, hpEqThree]
      rw [hpEqThree, hqEq, hY1card, hDcard]
      norm_num
      omega
  have hDcover : HasPathCoverOnAtMost C.G (D : Set V) 2 := by
    apply coverDevice (X := C.X) (Y₀ := C.Y0) (Y₁ := C.Y1)
      (D := D) (h := 2) (mu := C.mu)
    · exact hDX
    · omega
    · exact C.X_disjoint_Y.mono_right C.Y0_subset_Y
    · exact C.X_disjoint_Y.mono_right C.Y1_subset_Y
    · exact C.Y0_disjoint_Y1
    · exact fun y hy x hx ↦ C.adj_of_mem_Y0_mem_X hy hx
    · exact hsparse
    · exact C.Y1_nonempty
    · exact hcases
  exact C.path_plus_unused_X_cover_impossible hc hP hPY (by simpa [D] using hDcover)

/-! ## Dispatching the finite parameter cases -/

lemma c_three_impossible_of_mu_le
    (hc : C.c = 3) (hmu : C.mu ≤ C.r - 2) : False := by
  have hwlo : 3 ≤ C.w := by
    have h := C.w_ge_c
    omega
  have hrhi : C.r ≤ 6 := by
    have h := C.r_le_two_mul_c
    omega
  obtain ⟨hw3 | hw4, _hr5or6⟩ :=
    c_three_parameters hwlo C.w_le_r_sub_two hrhi
  · exact C.c_three_w_three_impossible hc hw3 hmu
  · have hr6 := c_three_w_four_r hw4 C.w_le_r_sub_two hrhi
    by_cases hmu2 : C.mu ≤ 2
    · exact C.c_three_w_four_mu_le_two_impossible hc hr6 hw4 hmu2
    · have hmuHi : C.mu ≤ 4 := by omega
      rcases (by omega : C.mu = 3 ∨ C.mu = 4) with hmu3 | hmu4
      · exact C.c_three_w_four_mu_three_impossible hc hr6 hw4 hmu3
      · exact C.c_three_w_four_mu_four_impossible hc hr6 hw4 hmu4

/-- No normalized counterexample with `c≤3` can satisfy the predecessor-clique bound
`mu≤r-2`. -/
theorem small_c_impossible_of_mu_le
    (hc : C.c ≤ 3) (hmu : C.mu ≤ C.r - 2) : False := by
  have hcpos := C.one_le_c
  rcases (by omega : C.c = 1 ∨ C.c = 2 ∨ C.c = 3) with hc1 | hc2 | hc3
  · apply c_one_impossible (r := C.r) (w := C.w)
    · have h := C.w_ge_c
      omega
    · exact C.w_le_r_sub_two
    · have h := C.r_le_two_mul_c
      omega
  · exact C.c_two_impossible_of_mu_le hc2 hmu
  · exact C.c_three_impossible_of_mu_le hc3 hmu

end Configuration
end Erdos518

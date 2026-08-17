import ErdosProblems.Erdos113.AnchorConstruction
import ErdosProblems.Erdos113.DynamicPruning

open scoped SimpleGraph

namespace Erdos113FourCycleSelection

noncomputable section

open Erdos113Cycles Erdos113FourCycles Erdos113CyclePruning
  Erdos113AnchorConstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rotate a labelled four-cycle by one step. -/
def rotateFour (x : Fin 4 → V) : Fin 4 → V := fun i ↦ x (i + 1)

lemma fin4_add_one_injective : Function.Injective (fun i : Fin 4 ↦ i + 1) := by
  decide +revert

lemma fin4_add_one_add_one (i : Fin 4) : i + 1 + 1 = i + 2 := by
  decide +revert

lemma fin4_sub_one_add_one (i : Fin 4) : i - 1 + 1 = i := by
  decide +revert

lemma rotateFour_injective : Function.Injective (rotateFour : (Fin 4 → V) → Fin 4 → V) := by
  intro x y hxy
  funext i
  have h := congrFun hxy (i - 1)
  simpa [rotateFour, fin4_sub_one_add_one] using h

lemma rotateFour_genuine {G : SimpleGraph V} {x : Fin 4 → V}
    (hx : IsGenuineCycle G x) : IsGenuineCycle G (rotateFour x) := by
  constructor
  · exact hx.1.comp fin4_add_one_injective
  · intro i
    simpa [rotateFour, fin4_add_one_add_one] using hx.2 (i + 1)

@[simp] lemma rotateFour_zero (x : Fin 4 → V) : rotateFour x 0 = x 1 := rfl
@[simp] lemma rotateFour_one (x : Fin 4 → V) : rotateFour x 1 = x 2 := rfl
@[simp] lemma rotateFour_two (x : Fin 4 → V) : rotateFour x 2 = x 3 := rfl
@[simp] lemma rotateFour_three (x : Fin 4 → V) : rotateFour x 3 = x 0 := rfl

/-- Ordered four-cycles for which the diagonal through coordinates `0,2`
has at least the codegree of the other diagonal. -/
def orientedFourCycles (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Fin 4 → V) :=
  (genuineCycles G 4).filter fun x ↦
    codegree G (x 1) (x 3) ≤ codegree G (x 0) (x 2)

@[simp] lemma mem_orientedFourCycles
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : Fin 4 → V} :
    x ∈ orientedFourCycles G ↔
      IsGenuineCycle G x ∧
        codegree G (x 1) (x 3) ≤ codegree G (x 0) (x 2) := by
  simp [orientedFourCycles]

lemma rotateFour_mem_oriented_of_not
    {G : SimpleGraph V} [DecidableRel G.Adj] {x : Fin 4 → V}
    (hx : IsGenuineCycle G x)
    (hnot : ¬codegree G (x 1) (x 3) ≤ codegree G (x 0) (x 2)) :
    rotateFour x ∈ orientedFourCycles G := by
  rw [mem_orientedFourCycles]
  refine ⟨rotateFour_genuine hx, ?_⟩
  simp only [rotateFour_zero, rotateFour_one, rotateFour_two, rotateFour_three]
  have hlt : codegree G (x 0) (x 2) < codegree G (x 1) (x 3) := by omega
  simpa [codegree, commonNeighborFinset, Finset.inter_comm] using hlt.le

/-- At least half of the labelled ordered four-cycles have the preferred
diagonal orientation. -/
theorem genuineCycles_four_card_le_twice_oriented
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (genuineCycles G 4).card ≤ 2 * (orientedFourCycles G).card := by
  let f : ↑(genuineCycles G 4) →
      ↑(orientedFourCycles G) ⊕ ↑(orientedFourCycles G) := fun x ↦
    if h : codegree G (x.1 1) (x.1 3) ≤ codegree G (x.1 0) (x.1 2) then
      Sum.inl ⟨x.1, (mem_orientedFourCycles).mpr
        ⟨(mem_genuineCycles).mp x.2, h⟩⟩
    else
      Sum.inr ⟨rotateFour x.1,
        rotateFour_mem_oriented_of_not (mem_genuineCycles.mp x.2) h⟩
  have hf : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    split at hxy <;> split at hxy
    · exact Subtype.ext (congrArg (fun z ↦ z.elim Subtype.val Subtype.val) hxy)
    · contradiction
    · contradiction
    · apply Subtype.ext
      apply rotateFour_injective
      exact congrArg (fun z ↦ z.elim Subtype.val Subtype.val) hxy
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  simpa only [Fintype.card_sum, two_mul] using hcard

lemma exists_fiber_with_card_bound
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (hT : T.Nonempty) (f : A → B)
    (hf : ∀ x ∈ S, f x ∈ T) :
    ∃ y ∈ T, S.card ≤ T.card * (S.filter fun x ↦ f x = y).card := by
  classical
  let w : B → ℕ := fun y ↦ (S.filter fun x ↦ f x = y).card
  obtain ⟨y, hyT, hymax⟩ := Finset.exists_max_image T w hT
  refine ⟨y, hyT, ?_⟩
  rw [Finset.card_eq_sum_card_fiberwise (s := S) (t := T) hf]
  calc
    (∑ z ∈ T, (S.filter fun x ↦ f x = z).card) ≤
        ∑ _z ∈ T, w y := by
      apply Finset.sum_le_sum
      intro z hz
      exact hymax z hz
    _ = T.card * (S.filter fun x ↦ f x = y).card := by simp [w]

def orientedFourCyclesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset (Fin 4 → V) :=
  (orientedFourCycles G).filter fun x ↦ x 0 = v

@[simp] lemma mem_orientedFourCyclesAt
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {x : Fin 4 → V} :
    x ∈ orientedFourCyclesAt G v ↔
      x ∈ orientedFourCycles G ∧ x 0 = v := by
  simp [orientedFourCyclesAt]

theorem exists_anchor_with_many_oriented_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : (orientedFourCycles G).Nonempty) :
    ∃ v : V, (orientedFourCycles G).card ≤
      Fintype.card V * (orientedFourCyclesAt G v).card := by
  have hV : (Finset.univ : Finset V).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x 0, Finset.mem_univ _⟩
  obtain ⟨v, _hv, hcard⟩ := exists_fiber_with_card_bound
    (orientedFourCycles G) (Finset.univ : Finset V) hV (fun x ↦ x 0)
      (by simp)
  refine ⟨v, ?_⟩
  simpa [orientedFourCyclesAt] using hcard

/-- A total logarithmic bucket; values larger than `N` are clamped into the
last bucket.  On values at most `N` it is the ordinary base-two logarithm. -/
def boundedLogIndex (N a : ℕ) : Fin (Nat.log 2 N + 1) :=
  ⟨min (Nat.log 2 a) (Nat.log 2 N), by omega⟩

lemma boundedLogIndex_val_of_le {N a : ℕ} (ha : a ≤ N) :
    (boundedLogIndex N a).val = Nat.log 2 a := by
  dsimp [boundedLogIndex]
  rw [min_eq_left]
  exact Nat.log_mono_right ha

def dyadicFiber {A : Type*} [DecidableEq A]
    (S : Finset A) (N : ℕ) (f : A → ℕ)
    (i : Fin (Nat.log 2 N + 1)) : Finset A :=
  S.filter fun x ↦ boundedLogIndex N (f x) = i

@[simp] lemma mem_dyadicFiber {A : Type*} [DecidableEq A]
    {S : Finset A} {N : ℕ} {f : A → ℕ}
    {i : Fin (Nat.log 2 N + 1)} {x : A} :
    x ∈ dyadicFiber S N f i ↔ x ∈ S ∧ boundedLogIndex N (f x) = i := by
  simp [dyadicFiber]

theorem exists_large_dyadicFiber
    {A : Type*} [DecidableEq A] (S : Finset A) (N : ℕ) (f : A → ℕ) :
    ∃ i : Fin (Nat.log 2 N + 1),
      S.card ≤ (Nat.log 2 N + 1) * (dyadicFiber S N f i).card := by
  have hT : (Finset.univ : Finset (Fin (Nat.log 2 N + 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _hi, hcard⟩ := exists_fiber_with_card_bound S
    (Finset.univ : Finset (Fin (Nat.log 2 N + 1))) hT
      (fun x ↦ boundedLogIndex N (f x)) (by simp)
  refine ⟨i, ?_⟩
  simpa [dyadicFiber] using hcard

lemma dyadicFiber_bounds
    {A : Type*} [DecidableEq A] {S : Finset A} {N : ℕ} {f : A → ℕ}
    {i : Fin (Nat.log 2 N + 1)} {x : A}
    (hx : x ∈ dyadicFiber S N f i) (hpos : 0 < f x) (hle : f x ≤ N) :
    2 ^ i.val ≤ f x ∧ f x < 2 ^ (i.val + 1) := by
  have hlog : Nat.log 2 (f x) = i.val := by
    have hi := (mem_dyadicFiber.mp hx).2
    have hb := boundedLogIndex_val_of_le hle
    exact hb.symm.trans (congrArg Fin.val hi)
  exact (Nat.log_eq_iff (b := 2) (m := i.val) (n := f x)
    (Or.inr ⟨Nat.one_lt_two, hpos.ne'⟩)).mp hlog

lemma two_le_codegree_diagonal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : Fin 4 → V} (hx : IsGenuineCycle G x) :
    2 ≤ codegree G (x 0) (x 2) := by
  rw [codegree]
  apply Finset.one_lt_card.mpr
  refine ⟨x 1, ?_, x 3, ?_, hx.1.ne (by decide)⟩
  · rw [mem_commonNeighborFinset]
    exact ⟨hx.2 0, (hx.2 1).symm⟩
  · rw [mem_commonNeighborFinset]
    exact ⟨(hx.2 3).symm, hx.2 2⟩

lemma codegree_le_card (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) :
    codegree G u w ≤ Fintype.card V := by
  rw [codegree]
  exact Finset.card_le_univ _

lemma codegree_comm (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) :
    codegree G u w = codegree G w u := by
  simp [codegree, commonNeighborFinset, Finset.inter_comm]

def sideVertices (side : V → Bool) (b : Bool) : Finset V :=
  Finset.univ.filter fun v ↦ side v = b

@[simp] lemma mem_sideVertices {side : V → Bool} {b : Bool} {v : V} :
    v ∈ sideVertices side b ↔ side v = b := by
  simp [sideVertices]

def activeSideVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) : Finset V :=
  Finset.univ.filter fun v ↦ side v = b ∧ 0 < G.degree v

@[simp] lemma mem_activeSideVertices
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V} :
    v ∈ activeSideVertices G side b ↔ side v = b ∧ 0 < G.degree v := by
  simp [activeSideVertices]

def orientedFourCyclesOnSide
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) : Finset (Fin 4 → V) :=
  (orientedFourCycles G).filter fun x ↦ side (x 0) = b

@[simp] lemma mem_orientedFourCyclesOnSide
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {x : Fin 4 → V} :
    x ∈ orientedFourCyclesOnSide G side b ↔
      x ∈ orientedFourCycles G ∧ side (x 0) = b := by
  simp [orientedFourCyclesOnSide]

theorem exists_side_with_many_oriented_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) :
    ∃ b : Bool, (orientedFourCycles G).card ≤
      2 * (orientedFourCyclesOnSide G side b).card := by
  obtain ⟨b, _hb, hcard⟩ := exists_fiber_with_card_bound
    (orientedFourCycles G) (Finset.univ : Finset Bool)
      (by simp) (fun x ↦ side (x 0)) (by simp)
  refine ⟨b, ?_⟩
  simpa [orientedFourCyclesOnSide] using hcard

def orientedFourCyclesAtSideAnchor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V) : Finset (Fin 4 → V) :=
  (orientedFourCyclesOnSide G side b).filter fun x ↦ x 0 = v

@[simp] lemma mem_orientedFourCyclesAtSideAnchor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V} {x : Fin 4 → V} :
    x ∈ orientedFourCyclesAtSideAnchor G side b v ↔
      x ∈ orientedFourCycles G ∧ side (x 0) = b ∧ x 0 = v := by
  simp [orientedFourCyclesAtSideAnchor, and_assoc]

theorem exists_side_anchor_with_many_oriented_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (hne : (orientedFourCycles G).Nonempty) :
    ∃ (b : Bool) (v : V), side v = b ∧
      (orientedFourCycles G).card ≤
        2 * (activeSideVertices G side b).card *
          (orientedFourCyclesAtSideAnchor G side b v).card := by
  obtain ⟨b, hb⟩ := exists_side_with_many_oriented_cycles G side
  have hsideNe : (orientedFourCyclesOnSide G side b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hOzero : (orientedFourCycles G).card = 0 := by
      rw [hempty] at hb
      simpa using hb
    exact hne.ne_empty (Finset.card_eq_zero.mp hOzero)
  obtain ⟨x, hx⟩ := hsideNe
  have hT : (activeSideVertices G side b).Nonempty := by
    have hxgen := (mem_orientedFourCycles.mp
      (mem_orientedFourCyclesOnSide.mp hx).1).1
    refine ⟨x 0, (mem_activeSideVertices).mpr
      ⟨(mem_orientedFourCyclesOnSide.mp hx).2, ?_⟩⟩
    rw [← G.card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨x 1, (G.mem_neighborFinset (x 0) (x 1)).mpr (hxgen.2 0)⟩
  obtain ⟨v, hv, hvcard⟩ := exists_fiber_with_card_bound
    (orientedFourCyclesOnSide G side b) (activeSideVertices G side b) hT
      (fun x ↦ x 0) (by
        intro z hz
        have hzdata := mem_orientedFourCyclesOnSide.mp hz
        have hzgen := (mem_orientedFourCycles.mp hzdata.1).1
        rw [mem_activeSideVertices]
        refine ⟨hzdata.2, ?_⟩
        rw [← G.card_neighborFinset_eq_degree, Finset.card_pos]
        exact ⟨z 1, (G.mem_neighborFinset (z 0) (z 1)).mpr (hzgen.2 0)⟩)
  refine ⟨b, v, (mem_activeSideVertices.mp hv).1, ?_⟩
  calc
    (orientedFourCycles G).card ≤
        2 * (orientedFourCyclesOnSide G side b).card := hb
    _ ≤ 2 * ((activeSideVertices G side b).card *
        (orientedFourCyclesAtSideAnchor G side b v).card) := by
      gcongr
      simpa [orientedFourCyclesAtSideAnchor] using hvcard
    _ = 2 * (activeSideVertices G side b).card *
        (orientedFourCyclesAtSideAnchor G side b v).card := by ring

def anchorCodegreeDyadicCycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1)) : Finset (Fin 4 → V) :=
  dyadicFiber (orientedFourCyclesAtSideAnchor G side b v)
    (Fintype.card V) (fun x ↦ codegree G v (x 2)) i

theorem exists_side_anchor_dyadic_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (hne : (genuineCycles G 4).Nonempty) :
    ∃ (b : Bool) (v : V)
      (i : Fin (Nat.log 2 (Fintype.card V) + 1)),
      side v = b ∧ 1 ≤ i.val ∧
      (genuineCycles G 4).card ≤
        4 * (activeSideVertices G side b).card *
          (Nat.log 2 (Fintype.card V) + 1) *
            (anchorCodegreeDyadicCycles G side b v i).card := by
  have hgenpos := Finset.card_pos.mpr hne
  have hOpos : 0 < (orientedFourCycles G).card := by
    have hhalf := genuineCycles_four_card_le_twice_oriented G
    omega
  obtain ⟨b, v, hvside, hanchor⟩ :=
    exists_side_anchor_with_many_oriented_cycles G side (Finset.card_pos.mp hOpos)
  obtain ⟨i, hi⟩ := exists_large_dyadicFiber
    (orientedFourCyclesAtSideAnchor G side b v) (Fintype.card V)
      (fun x ↦ codegree G v (x 2))
  have hbinne : (anchorCodegreeDyadicCycles G side b v i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hAtpos : 0 < (orientedFourCyclesAtSideAnchor G side b v).card := by
      have : 0 < (orientedFourCycles G).card := hOpos
      nlinarith
    change (orientedFourCyclesAtSideAnchor G side b v).card ≤
      (Nat.log 2 (Fintype.card V) + 1) *
        (anchorCodegreeDyadicCycles G side b v i).card at hi
    rw [hempty] at hi
    exact (not_le_of_gt hAtpos) (by simpa using hi)
  obtain ⟨x, hx⟩ := hbinne
  have hxAt := (mem_dyadicFiber.mp hx).1
  have hxdata := mem_orientedFourCyclesAtSideAnchor.mp hxAt
  have hxgen := (mem_orientedFourCycles.mp hxdata.1).1
  have hxzero : x 0 = v := hxdata.2.2
  have hbounds := dyadicFiber_bounds hx
    (by
      have := two_le_codegree_diagonal hxgen
      simpa [hxzero] using (lt_of_lt_of_le Nat.zero_lt_two this))
    (codegree_le_card G v (x 2))
  have hiOne : 1 ≤ i.val := by
    by_contra! hiZero
    have : i.val = 0 := by omega
    rw [this] at hbounds
    have htwo : 2 ≤ codegree G v (x 2) := by
      simpa [hxzero] using two_le_codegree_diagonal hxgen
    omega
  refine ⟨b, v, i, hvside, hiOne, ?_⟩
  calc
    (genuineCycles G 4).card ≤ 2 * (orientedFourCycles G).card :=
      genuineCycles_four_card_le_twice_oriented G
    _ ≤ 2 * (2 * (activeSideVertices G side b).card *
        (orientedFourCyclesAtSideAnchor G side b v).card) := by gcongr
    _ ≤ 2 * (2 * (activeSideVertices G side b).card *
        ((Nat.log 2 (Fintype.card V) + 1) *
          (anchorCodegreeDyadicCycles G side b v i).card)) := by
      gcongr
      simpa [anchorCodegreeDyadicCycles] using hi
    _ = 4 * (activeSideVertices G side b).card *
        (Nat.log 2 (Fintype.card V) + 1) *
          (anchorCodegreeDyadicCycles G side b v i).card := by ring

structure Triple (V : Type*) where
  left : V
  middle : V
  right : V
deriving DecidableEq, Fintype

def cycleTriple (x : Fin 4 → V) : Triple V :=
  ⟨x 1, x 2, x 3⟩

def swapTriple (p : Triple V) : Triple V :=
  ⟨p.right, p.middle, p.left⟩

@[simp] lemma swapTriple_swapTriple (p : Triple V) :
    swapTriple (swapTriple p) = p := by cases p; rfl

lemma cycleTriple_injOn_at_anchor
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)} :
    Set.InjOn cycleTriple
      (↑(anchorCodegreeDyadicCycles G side b v i) : Set (Fin 4 → V)) := by
  intro x hx y hy hxy
  have hxAt := (mem_dyadicFiber.mp hx).1
  have hyAt := (mem_dyadicFiber.mp hy).1
  have hxzero := (mem_orientedFourCyclesAtSideAnchor.mp hxAt).2.2
  have hyzero := (mem_orientedFourCyclesAtSideAnchor.mp hyAt).2.2
  funext j
  fin_cases j
  · exact hxzero.trans hyzero.symm
  · exact congrArg Triple.left hxy
  · exact congrArg Triple.middle hxy
  · exact congrArg Triple.right hxy

/-- Symmetrize the selected oriented four-cycles in their two endpoint
coordinates. -/
def selectedTriples
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1)) : Finset (Triple V) :=
  let A := (anchorCodegreeDyadicCycles G side b v i).image cycleTriple
  A ∪ A.image swapTriple

lemma cycleTriple_mem_selectedTriples
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)}
    {x : Fin 4 → V} (hx : x ∈ anchorCodegreeDyadicCycles G side b v i) :
    cycleTriple x ∈ selectedTriples G side b v i := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

lemma selectedTriples_symmetric
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1))
    {p : Triple V} (hp : p ∈ selectedTriples G side b v i) :
    swapTriple p ∈ selectedTriples G side b v i := by
  simp only [selectedTriples, Finset.mem_union, Finset.mem_image] at hp ⊢
  rcases hp with hp | hp
  · right
    exact ⟨p, hp, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := hp
    left
    simpa using hq

lemma anchorCodegreeDyadicCycles_data
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)}
    {x : Fin 4 → V} (hx : x ∈ anchorCodegreeDyadicCycles G side b v i) :
    IsGenuineCycle G x ∧ x 0 = v ∧
      codegree G (x 1) (x 3) ≤ codegree G v (x 2) ∧
      2 ^ i.val ≤ codegree G v (x 2) ∧
      codegree G v (x 2) < 2 ^ (i.val + 1) := by
  have hxAt := (mem_dyadicFiber.mp hx).1
  have hxdata := mem_orientedFourCyclesAtSideAnchor.mp hxAt
  have hxorient := mem_orientedFourCycles.mp hxdata.1
  have hxzero := hxdata.2.2
  have hbounds := dyadicFiber_bounds hx
    (by
      have htwo := two_le_codegree_diagonal hxorient.1
      rw [hxzero] at htwo
      omega)
    (codegree_le_card G v (x 2))
  exact ⟨hxorient.1, hxzero, by simpa [hxzero] using hxorient.2,
    hbounds.1, hbounds.2⟩

lemma selectedTriples_card_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (b : Bool) (v : V)
    (i : Fin (Nat.log 2 (Fintype.card V) + 1)) :
    (anchorCodegreeDyadicCycles G side b v i).card ≤
      (selectedTriples G side b v i).card := by
  let A := (anchorCodegreeDyadicCycles G side b v i).image cycleTriple
  calc
    (anchorCodegreeDyadicCycles G side b v i).card = A.card := by
      exact (Finset.card_image_of_injOn cycleTriple_injOn_at_anchor).symm
    _ ≤ (A ∪ A.image swapTriple).card :=
      Finset.card_le_card (Finset.subset_union_left)
    _ = (selectedTriples G side b v i).card := by
      rfl

lemma selectedTriple_data
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {side : V → Bool} {b : Bool} {v : V}
    {i : Fin (Nat.log 2 (Fintype.card V) + 1)}
    {p : Triple V} (hp : p ∈ selectedTriples G side b v i) :
    G.Adj v p.left ∧ G.Adj p.left p.middle ∧
      G.Adj p.middle p.right ∧ G.Adj p.right v ∧
      p.middle ≠ v ∧
      p.left ≠ p.right ∧
      codegree G p.left p.right ≤ codegree G v p.middle ∧
      2 ^ i.val ≤ codegree G v p.middle ∧
      codegree G v p.middle < 2 ^ (i.val + 1) := by
  simp only [selectedTriples, Finset.mem_union, Finset.mem_image] at hp
  rcases hp with hp | hp
  · obtain ⟨x, hx, rfl⟩ := hp
    have h := anchorCodegreeDyadicCycles_data hx
    exact ⟨by simpa [cycleTriple, h.2.1] using h.1.2 0,
      by simpa [cycleTriple] using h.1.2 1,
      by simpa [cycleTriple] using h.1.2 2,
      by simpa [cycleTriple, h.2.1] using h.1.2 3,
      by
        simpa [cycleTriple, h.2.1] using h.1.1.ne (by decide : (2 : Fin 4) ≠ 0),
      by simpa [cycleTriple] using h.1.1.ne (by decide : (1 : Fin 4) ≠ 3),
      by simpa [cycleTriple] using h.2.2.1,
      by simpa [cycleTriple] using h.2.2.2.1,
      by simpa [cycleTriple] using h.2.2.2.2⟩
  · obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := hq
    have h := anchorCodegreeDyadicCycles_data hx
    exact ⟨by simpa [cycleTriple, swapTriple, h.2.1] using (h.1.2 3).symm,
      by simpa [cycleTriple, swapTriple] using (h.1.2 2).symm,
      by simpa [cycleTriple, swapTriple] using (h.1.2 1).symm,
      by simpa [cycleTriple, swapTriple, h.2.1] using (h.1.2 0).symm,
      by
        simpa [cycleTriple, swapTriple, h.2.1] using
          h.1.1.ne (by decide : (2 : Fin 4) ≠ 0),
      by
        simpa [cycleTriple, swapTriple] using
          h.1.1.ne (by decide : (3 : Fin 4) ≠ 1),
      by
        change codegree G (x 3) (x 1) ≤ codegree G v (x 2)
        rw [codegree_comm]
        exact h.2.2.1,
      by simpa [cycleTriple, swapTriple] using h.2.2.2.1,
      by simpa [cycleTriple, swapTriple] using h.2.2.2.2⟩

structure FirstSelection (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) where
  anchorSide : Bool
  anchor : V
  scaleIndex : Fin (Nat.log 2 (Fintype.card V) + 1)
  triples : Finset (Triple V)
  anchor_side : side anchor = anchorSide
  scaleIndex_pos : 1 ≤ scaleIndex.val
  triples_nonempty : triples.Nonempty
  many : (genuineCycles G 4).card ≤
    4 * (activeSideVertices G side anchorSide).card *
      (Nat.log 2 (Fintype.card V) + 1) * triples.card
  symmetric : ∀ ⦃p⦄, p ∈ triples → swapTriple p ∈ triples
  data : ∀ ⦃p⦄, p ∈ triples →
    G.Adj anchor p.left ∧ G.Adj p.left p.middle ∧
      G.Adj p.middle p.right ∧ G.Adj p.right anchor ∧
      p.middle ≠ anchor ∧
      p.left ≠ p.right ∧
      codegree G p.left p.right ≤ codegree G anchor p.middle ∧
      2 ^ scaleIndex.val ≤ codegree G anchor p.middle ∧
      codegree G anchor p.middle < 2 ^ (scaleIndex.val + 1)

theorem exists_firstSelection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (hne : (genuineCycles G 4).Nonempty) :
    Nonempty (FirstSelection G side) := by
  obtain ⟨b, v, i, hvside, hipos, hmany⟩ :=
    exists_side_anchor_dyadic_cycles G side hne
  exact ⟨{
    anchorSide := b
    anchor := v
    scaleIndex := i
    triples := selectedTriples G side b v i
    anchor_side := hvside
    scaleIndex_pos := hipos
    triples_nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsel := selectedTriples_card_lower G side b v i
      rw [hempty] at hsel
      simp only [Finset.card_empty] at hsel
      have hbucket :
          (anchorCodegreeDyadicCycles G side b v i).card = 0 := by
        omega
      have hzero : (genuineCycles G 4).card = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa [hbucket] using hmany
      exact hne.ne_empty (Finset.card_eq_zero.mp hzero)
    many := hmany.trans (by
      gcongr
      exact selectedTriples_card_lower G side b v i)
    symmetric := fun {_} hp ↦ selectedTriples_symmetric
      (G := G) (side := side) (b := b) (v := v) (i := i) hp
    data := fun {_} hp ↦ selectedTriple_data
      (G := G) (side := side) (b := b) (v := v) (i := i) hp }⟩

namespace FirstSelection

variable {G : SimpleGraph V} [DecidableRel G.Adj] {side : V → Bool}

/-- The symmetric ternary predicate encoded by a first-stage selection. -/
def predicate (S : FirstSelection G side) (x y z : V) : Prop :=
  (⟨x, y, z⟩ : Triple V) ∈ S.triples

instance predicate_decidable (S : FirstSelection G side) (x y z : V) :
    Decidable (S.predicate x y z) := by
  change Decidable ((⟨x, y, z⟩ : Triple V) ∈ S.triples)
  infer_instance

lemma predicate_symm (S : FirstSelection G side) (x y z : V) :
    S.predicate x y z ↔ S.predicate z y x := by
  constructor
  · intro h
    exact S.symmetric h
  · intro h
    simpa [predicate, swapTriple] using S.symmetric h

/-- The ordered pair of neighbours of the anchor occurring as the two
endpoints of a selected triple. -/
def endpointPair (S : FirstSelection G side) (p : ↑S.triples) :
    NeighborVertex G S.anchor × NeighborVertex G S.anchor :=
  (⟨p.1.left, (G.mem_neighborFinset S.anchor p.1.left).mpr
      (S.data p.2).1⟩,
    ⟨p.1.right, (G.mem_neighborFinset S.anchor p.1.right).mpr
      (S.data p.2).2.2.2.1.symm⟩)

@[simp] lemma endpointPair_fst_val (S : FirstSelection G side)
    (p : ↑S.triples) : (S.endpointPair p).1.1 = p.1.left := rfl

@[simp] lemma endpointPair_snd_val (S : FirstSelection G side)
    (p : ↑S.triples) : (S.endpointPair p).2.1 = p.1.right := rfl

def middleCount (S : FirstSelection G side)
    (ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor) : ℕ :=
  (selectedMiddle G S.anchor S.predicate ab.1 ab.2).card

lemma triple_middle_mem (S : FirstSelection G side) (p : ↑S.triples) :
    p.1.middle ∈ selectedMiddle G S.anchor S.predicate
      (S.endpointPair p).1 (S.endpointPair p).2 := by
  rw [mem_selectedMiddle]
  have h := S.data p.2
  exact ⟨h.2.1, h.2.2.1.symm, h.2.2.2.2.1, p.2⟩

/-- Selected triples are exactly selected-middle incidences over ordered
pairs of neighbours of the anchor. -/
def tripleIncidenceEquiv (S : FirstSelection G side) :
    ↑S.triples ≃
      Σ ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor,
        ↑(selectedMiddle G S.anchor S.predicate ab.1 ab.2) where
  toFun p := ⟨S.endpointPair p, ⟨p.1.middle, S.triple_middle_mem p⟩⟩
  invFun q :=
    ⟨⟨q.1.1.1, q.2.1, q.1.2.1⟩,
      (mem_selectedMiddle G S.anchor S.predicate).mp q.2.2 |>.2.2.2⟩
  left_inv p := by
    rcases p with ⟨⟨left, middle, right⟩, hp⟩
    rfl
  right_inv q := by
    rcases q with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨y, hy⟩⟩
    rfl

theorem triples_card_eq_sum_middleCount (S : FirstSelection G side) :
    S.triples.card =
      ∑ ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor,
        S.middleCount ab := by
  rw [← Fintype.card_coe, Fintype.card_congr S.tripleIncidenceEquiv,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro ab _hab
  exact Fintype.card_coe (selectedMiddle G S.anchor S.predicate ab.1 ab.2)

lemma selectedMiddle_card_le_codegree (S : FirstSelection G side)
    (ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor) :
    S.middleCount ab ≤ codegree G ab.1.1 ab.2.1 := by
  rw [middleCount, codegree]
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_inter.mpr
    ⟨(G.mem_neighborFinset ab.1.1 y).mpr
        ((mem_selectedMiddle G S.anchor S.predicate).mp hy |>.1),
      (G.mem_neighborFinset ab.2.1 y).mpr
        ((mem_selectedMiddle G S.anchor S.predicate).mp hy |>.2.1)⟩

lemma middleCount_pos_at_triple (S : FirstSelection G side)
    (p : ↑S.triples) : 0 < S.middleCount (S.endpointPair p) := by
  rw [middleCount]
  exact Finset.card_pos.mpr ⟨p.1.middle, S.triple_middle_mem p⟩

lemma middleCount_lt_scaleCap_at_triple (S : FirstSelection G side)
    (p : ↑S.triples) :
    S.middleCount (S.endpointPair p) < 2 ^ (S.scaleIndex.val + 1) := by
  have hdata := S.data p.2
  exact (S.selectedMiddle_card_le_codegree (S.endpointPair p)).trans_lt
    (hdata.2.2.2.2.2.2.1.trans_lt hdata.2.2.2.2.2.2.2.2)

/-- The second dyadic bucket, now sorting selected triples by the number of
selected middles above their ordered endpoint pair. -/
def secondDyadicTriples (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    Finset ↑S.triples :=
  dyadicFiber (Finset.univ : Finset ↑S.triples)
    (2 ^ (S.scaleIndex.val + 1))
    (fun p ↦ S.middleCount (S.endpointPair p)) j

def secondDyadicPairs (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    Finset (NeighborVertex G S.anchor × NeighborVertex G S.anchor) :=
  (S.secondDyadicTriples j).image S.endpointPair

theorem exists_second_dyadic_bucket (S : FirstSelection G side) :
    ∃ j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1),
      S.triples.card ≤
        (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
          (S.secondDyadicTriples j).card := by
  obtain ⟨j, hj⟩ := exists_large_dyadicFiber
    (Finset.univ : Finset ↑S.triples) (2 ^ (S.scaleIndex.val + 1))
      (fun p ↦ S.middleCount (S.endpointPair p))
  refine ⟨j, ?_⟩
  simpa [secondDyadicTriples] using hj

lemma secondDyadicTriples_count_bounds (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {p : ↑S.triples} (hp : p ∈ S.secondDyadicTriples j) :
    2 ^ j.val ≤ S.middleCount (S.endpointPair p) ∧
      S.middleCount (S.endpointPair p) < 2 ^ (j.val + 1) := by
  apply dyadicFiber_bounds hp (S.middleCount_pos_at_triple p)
  exact (S.middleCount_lt_scaleCap_at_triple p).le

lemma secondDyadicPairs_count_bounds (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor}
    (hab : ab ∈ S.secondDyadicPairs j) :
    2 ^ j.val ≤ S.middleCount ab ∧
      S.middleCount ab < 2 ^ (j.val + 1) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hab
  exact S.secondDyadicTriples_count_bounds hp

lemma secondDyadicPairs_ne (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor}
    (hab : ab ∈ S.secondDyadicPairs j) : ab.1 ≠ ab.2 := by
  obtain ⟨p, _hp, hpab⟩ := Finset.mem_image.mp hab
  intro heq
  have hval := congrArg (fun q : NeighborVertex G S.anchor ↦ q.1) heq
  have hpdata := S.data p.2
  apply hpdata.2.2.2.2.2.1
  simpa [← hpab] using hval

lemma card_le_image_card_mul_of_fiber_le
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (T : Finset A) (f : A → B) (M : ℕ)
    (hfiber : ∀ b ∈ T.image f,
      (T.filter fun a ↦ f a = b).card ≤ M) :
    T.card ≤ (T.image f).card * M := by
  rw [Finset.card_eq_sum_card_fiberwise
    (s := T) (t := T.image f) (fun a ha ↦ Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
  calc
    (∑ b ∈ T.image f, (T.filter fun a ↦ f a = b).card) ≤
        ∑ _b ∈ T.image f, M := by
      apply Finset.sum_le_sum
      intro b hb
      exact hfiber b hb
    _ = (T.image f).card * M := by simp

lemma secondDyadic_fiber_card_le_middleCount (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor} :
    ((S.secondDyadicTriples j).filter fun p ↦ S.endpointPair p = ab).card ≤
      S.middleCount ab := by
  rw [middleCount]
  apply Finset.card_le_card_of_injOn (fun p : ↑S.triples ↦ p.1.middle)
  · intro p hp
    have hpdata := Finset.mem_filter.mp hp
    have hm := S.triple_middle_mem p
    simpa [hpdata.2] using hm
  · intro p hp q hq hmiddle
    have hpPair := (Finset.mem_filter.mp hp).2
    have hqPair := (Finset.mem_filter.mp hq).2
    have hpqPair : S.endpointPair p = S.endpointPair q :=
      hpPair.trans hqPair.symm
    apply Subtype.ext
    rcases p with ⟨⟨pl, pm, pr⟩, hp'⟩
    rcases q with ⟨⟨ql, qm, qr⟩, hq'⟩
    simp only [endpointPair] at hpqPair
    simp only at hmiddle ⊢
    have hleft : pl = ql := congrArg (fun z ↦ z.1.1) hpqPair
    have hright : pr = qr := congrArg (fun z ↦ z.2.1) hpqPair
    subst ql
    subst qm
    subst qr
    rfl

theorem secondDyadicTriples_card_le_pairs (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    (S.secondDyadicTriples j).card ≤
      (S.secondDyadicPairs j).card * 2 ^ (j.val + 1) := by
  apply card_le_image_card_mul_of_fiber_le
  intro ab hab
  exact (S.secondDyadic_fiber_card_le_middleCount (j := j) (ab := ab)).trans
    (S.secondDyadicPairs_count_bounds hab).2.le

/-- The auxiliary graph on neighbours of the chosen anchor at the second
dyadic scale. -/
def auxiliaryGraph (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    SimpleGraph (NeighborVertex G S.anchor) :=
  selectedPairGraph G S.anchor S.predicate (2 ^ j.val)

noncomputable instance auxiliaryGraph_decidableRel (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    DecidableRel (S.auxiliaryGraph j).Adj := Classical.decRel _

lemma secondDyadicPairs_adj (S : FirstSelection G side)
    {j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)}
    {ab : NeighborVertex G S.anchor × NeighborVertex G S.anchor}
    (hab : ab ∈ S.secondDyadicPairs j) :
    (S.auxiliaryGraph j).Adj ab.1 ab.2 := by
  have hb := S.secondDyadicPairs_count_bounds hab
  rw [auxiliaryGraph, selectedPairGraph, SimpleGraph.fromRel_adj]
  refine ⟨S.secondDyadicPairs_ne hab, Or.inl ?_⟩
  constructor
  · simpa [middleCount] using hb.1
  · have hpow : 2 ^ (j.val + 1) = 2 * 2 ^ j.val := by
      simp [pow_succ, Nat.mul_comm]
    rw [hpow] at hb
    simpa [middleCount] using hb.2.le

theorem secondDyadicPairs_card_le_twice_edges (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    (S.secondDyadicPairs j).card ≤
      2 * (S.auxiliaryGraph j).edgeFinset.card := by
  have hsubset : S.secondDyadicPairs j ⊆
      (Finset.univ.filter fun ab :
        NeighborVertex G S.anchor × NeighborVertex G S.anchor ↦
          (S.auxiliaryGraph j).Adj ab.1 ab.2) := by
    intro ab hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.secondDyadicPairs_adj hab
  exact (Finset.card_le_card hsubset).trans_eq
    (S.auxiliaryGraph j).two_mul_card_edgeFinset.symm

theorem secondDyadicTriples_card_le_auxiliary_edges
    (S : FirstSelection G side)
    (j : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)) :
    (S.secondDyadicTriples j).card ≤
      2 ^ (j.val + 2) * (S.auxiliaryGraph j).edgeFinset.card := by
  calc
    (S.secondDyadicTriples j).card ≤
        (S.secondDyadicPairs j).card * 2 ^ (j.val + 1) :=
      S.secondDyadicTriples_card_le_pairs j
    _ ≤ (2 * (S.auxiliaryGraph j).edgeFinset.card) *
        2 ^ (j.val + 1) := by
      gcongr
      exact S.secondDyadicPairs_card_le_twice_edges j
    _ = 2 ^ (j.val + 2) * (S.auxiliaryGraph j).edgeFinset.card := by
      simp [pow_succ]
      ring

/-- The output of Janzer's two dyadic pigeonhole steps.  Its auxiliary
graph has `2^index` to `2^(index+1)` selected middles above each of the
ordered pairs retained by the bucket, and its edge count controls the
number of first-stage triples. -/
structure SecondSelection (S : FirstSelection G side) where
  index : Fin (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1)
  bucket_nonempty : (S.secondDyadicTriples index).Nonempty
  many : S.triples.card ≤
    (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
      2 ^ (index.val + 2) * (S.auxiliaryGraph index).edgeFinset.card

theorem exists_secondSelection (S : FirstSelection G side) :
    Nonempty S.SecondSelection := by
  obtain ⟨j, hj⟩ := S.exists_second_dyadic_bucket
  exact ⟨{
    index := j
    bucket_nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at hj
      simp at hj
      exact S.triples_nonempty.ne_empty hj
    many := hj.trans (by
      calc
        (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
            (S.secondDyadicTriples j).card ≤
            (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
              (2 ^ (j.val + 2) *
                (S.auxiliaryGraph j).edgeFinset.card) := by
          gcongr
          exact S.secondDyadicTriples_card_le_auxiliary_edges j
        _ = (Nat.log 2 (2 ^ (S.scaleIndex.val + 1)) + 1) *
              2 ^ (j.val + 2) *
                (S.auxiliaryGraph j).edgeFinset.card := by ring) }⟩

lemma SecondSelection.auxiliary_edge
    (S : FirstSelection G side) (R : S.SecondSelection) :
    ∃ a b, (S.auxiliaryGraph R.index).Adj a b := by
  obtain ⟨p, hp⟩ := R.bucket_nonempty
  let ab := S.endpointPair p
  exact ⟨ab.1, ab.2, S.secondDyadicPairs_adj
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩

end FirstSelection

end

end Erdos113FourCycleSelection

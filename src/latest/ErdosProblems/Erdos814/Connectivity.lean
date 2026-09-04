import ErdosProblems.Erdos814.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Erdős 814: connectedness reductions

The extremal argument may be run one connected component at a time.  This file records that
reduction in the fixed-ambient-set language of `Basic.lean`.  If an induced graph of minimum
degree at least `k` is disconnected, one of the two sides of a component has at most half of the
vertices and still has minimum degree at least `k`.
-/

open Finset SimpleGraph

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph induced by `A` is connected. -/
def ConnectedOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  (G.induce (↑A : Set V)).Connected

/-- `U` is one of the small minimum-degree cores forbidden in a counterexample.  The
cardinality inequality is kept integral: it says `|U| ≤ (1 - 1 / D)|A|`. -/
def IsSmallCoreOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k D : ℕ) (U : Finset V) : Prop :=
  U ⊆ A ∧ HasMinDegreeOn G U k ∧ D * U.card ≤ (D - 1) * A.card

/-- A counterexample on `A` has no core satisfying the prescribed integral size bound. -/
def NoSmallCoreOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k D : ℕ) : Prop :=
  ¬ ∃ U, IsSmallCoreOn G A k D U

/-- A core which saves a `1 / D` fraction also satisfies every weaker
`1 / E` saving when `D ≤ E`. -/
lemma IsSmallCoreOn.mono_den
    {G : SimpleGraph V} [DecidableRel G.Adj] {A U : Finset V} {k D E : ℕ}
    (hD : 1 ≤ D) (hDE : D ≤ E) (h : IsSmallCoreOn G A k D U) :
    IsSmallCoreOn G A k E U := by
  rcases h with ⟨hUA, hmin, hsmall⟩
  refine ⟨hUA, hmin, ?_⟩
  have hcard : U.card ≤ A.card := card_le_card hUA
  have hE : E = D + (E - D) := by omega
  have hsub : E - 1 = (D - 1) + (E - D) := by omega
  calc
    E * U.card = D * U.card + (E - D) * U.card := by
      conv_lhs => rw [hE, add_mul]
    _ ≤ (D - 1) * A.card + (E - D) * A.card :=
      Nat.add_le_add hsmall (Nat.mul_le_mul_left (E - D) hcard)
    _ = (E - 1) * A.card := by
      conv_rhs => rw [hsub, add_mul]

/-- Absence of a core at the weaker denominator `E` implies absence at every
stronger denominator `D ≤ E`. -/
lemma NoSmallCoreOn.anti_den
    {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V} {k D E : ℕ}
    (hD : 1 ≤ D) (hDE : D ≤ E) (hno : NoSmallCoreOn G A k E) :
    NoSmallCoreOn G A k D := by
  rintro ⟨U, hU⟩
  exact hno ⟨U, hU.mono_den hD hDE⟩

/-- If `U ⊆ A` is closed under all neighbors which lie in `A`, restriction from `A` to `U`
does not change the degree of a vertex of `U`. -/
lemma degreeOn_eq_of_neighbor_closed
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V}
    (hUA : U ⊆ A)
    (hclosed : ∀ {x}, x ∈ U → ∀ {y}, y ∈ A → G.Adj x y → y ∈ U)
    {v : V} (hv : v ∈ U) :
    degreeOn G U v = degreeOn G A v := by
  unfold degreeOn
  congr 1
  ext w
  simp only [mem_inter]
  constructor
  · rintro ⟨hvw, hwU⟩
    exact ⟨hvw, hUA hwU⟩
  · rintro ⟨hvw, hwA⟩
    refine ⟨hvw, hclosed hv hwA ?_⟩
    simpa [SimpleGraph.mem_neighborFinset] using hvw

/-- A disconnected induced graph of minimum degree at least `k` has a nonempty proper side of
size at most half which still has minimum degree at least `k`.

The side is either one connected component or its complement.  Both are closed under adjacency
inside `A`; choosing the smaller gives the cardinality inequality. -/
lemma exists_small_minDegree_side_of_not_connectedOn
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {k : ℕ}
    (hmin : HasMinDegreeOn G A k) (hconn : ¬ ConnectedOn G A) :
    ∃ U : Finset V,
      U ⊆ A ∧ U ≠ A ∧ HasMinDegreeOn G U k ∧ 2 * U.card ≤ A.card := by
  classical
  let H : SimpleGraph (↑A : Set V) := G.induce (↑A : Set V)
  let : Nonempty (↑A : Set V) := hmin.1.to_subtype
  have hnconnected : ¬ H.Connected := by
    simpa [ConnectedOn, H] using hconn
  have hnpreconnected : ¬ H.Preconnected := by
    intro hpre
    exact hnconnected ⟨hpre⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hnpreconnected
  obtain ⟨u, v, huv⟩ := hnpreconnected
  let InComponent : V → Prop := fun x ↦
    ∃ hx : x ∈ A, H.Reachable u ⟨x, hx⟩
  let C : Finset V := A.filter InComponent
  have hCA : C ⊆ A := filter_subset _ _
  have huC : (u : V) ∈ C := by
    rw [mem_filter]
    exact ⟨u.property, u.property, SimpleGraph.Reachable.rfl⟩
  have hvC : (v : V) ∉ C := by
    intro hv
    have hv' := (mem_filter.mp hv).2
    rcases hv' with ⟨hvA, huv'⟩
    apply huv
    simpa using huv'
  have hCne : C ≠ A := by
    intro hCAeq
    exact hvC (hCAeq.symm ▸ v.property)
  have hCclosed :
      ∀ {x}, x ∈ C → ∀ {y}, y ∈ A → G.Adj x y → y ∈ C := by
    intro x hx y hy hxy
    rw [mem_filter] at hx ⊢
    rcases hx with ⟨hxA, _hxA', hxreach⟩
    refine ⟨hy, hy, ?_⟩
    have hadj : H.Adj ⟨x, hxA⟩ ⟨y, hy⟩ := by simpa [H] using hxy
    exact hxreach.trans hadj.reachable
  have hCmin : HasMinDegreeOn G C k := by
    refine ⟨⟨u, huC⟩, ?_⟩
    intro x hx
    rw [degreeOn_eq_of_neighbor_closed G hCA hCclosed hx]
    exact hmin.2 x (hCA hx)
  by_cases hsmall : 2 * C.card ≤ A.card
  · exact ⟨C, hCA, hCne, hCmin, hsmall⟩
  · let U : Finset V := A \ C
    have hUA : U ⊆ A := sdiff_subset
    have hvU : (v : V) ∈ U := by
      exact mem_sdiff.mpr ⟨v.property, hvC⟩
    have huU : (u : V) ∉ U := by
      simp only [U, mem_sdiff]
      exact fun h ↦ h.2 huC
    have hUne : U ≠ A := by
      intro hUAeq
      exact huU (hUAeq.symm ▸ u.property)
    have hUclosed :
        ∀ {x}, x ∈ U → ∀ {y}, y ∈ A → G.Adj x y → y ∈ U := by
      intro x hx y hy hxy
      rw [mem_sdiff] at hx ⊢
      refine ⟨hy, ?_⟩
      intro hyC
      apply hx.2
      rw [mem_filter] at hyC ⊢
      rcases hyC with ⟨hyA, _hyA', hyreach⟩
      refine ⟨hx.1, hx.1, ?_⟩
      have hadj : H.Adj ⟨y, hyA⟩ ⟨x, hx.1⟩ := by simpa [H] using hxy.symm
      exact hyreach.trans hadj.reachable
    have hUmin : HasMinDegreeOn G U k := by
      refine ⟨⟨v, hvU⟩, ?_⟩
      intro x hx
      rw [degreeOn_eq_of_neighbor_closed G hUA hUclosed hx]
      exact hmin.2 x (hUA hx)
    have hcard : U.card = A.card - C.card := by
      simp [U, card_sdiff_of_subset hCA]
    have hCle : C.card ≤ A.card := card_le_card hCA
    have hUsmall : 2 * U.card ≤ A.card := by
      rw [hcard]
      omega
    exact ⟨U, hUA, hUne, hUmin, hUsmall⟩

/-- A minimum-degree counterexample to the `1 - 1 / D` core bound is connected as soon as
`D ≥ 2`. -/
lemma connectedOn_of_noSmallCoreOn
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {k D : ℕ}
    (hD : 2 ≤ D) (hmin : HasMinDegreeOn G A k)
    (hnosmall : NoSmallCoreOn G A k D) :
    ConnectedOn G A := by
  by_contra hconn
  obtain ⟨U, hUA, -, hUmin, hhalf⟩ :=
    exists_small_minDegree_side_of_not_connectedOn G hmin hconn
  apply hnosmall
  refine ⟨U, hUA, hUmin, ?_⟩
  have hcoef : D ≤ 2 * (D - 1) := by omega
  calc
    D * U.card ≤ (2 * (D - 1)) * U.card := Nat.mul_le_mul_right U.card hcoef
    _ = (D - 1) * (2 * U.card) := by ring
    _ ≤ (D - 1) * A.card := Nat.mul_le_mul_left (D - 1) hhalf

end Erdos814

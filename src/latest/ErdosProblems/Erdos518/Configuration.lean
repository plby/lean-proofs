/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Setup
import ErdosProblems.Erdos518.Cover
import ErdosProblems.Erdos518.Sqrt

/-!
# Erdős Problem 518: normalized counterexample configurations

This file packages the data and elementary finite-set bookkeeping used after choosing a
minimal counterexample and exchanging the two colours so that a globally longest path has the
complement colour.  No structural assertion about a counterexample beyond the fields of the
configuration is made here.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

/-- The broad induction hypothesis supplied by minimality of the counterexample order: every
two-colouring on a strictly smaller finite type satisfies Problem 518. -/
def HoldsForSmallerTypes (V : Type u) [Fintype V] : Prop :=
  ∀ {W : Type u} [Fintype W], Fintype.card W < Fintype.card V →
    ∀ K : SimpleGraph W, Erdos518ForType K

/-- A normalized minimal-counterexample configuration.  `induced_minimality` is precisely the
part of minimality used later: every proper induced subcolouring satisfies Problem 518. -/
structure Configuration (V : Type u) [Fintype V] where
  G : SimpleGraph V
  Q : List V
  q_isPath : IsPath Gᶜ Q
  q_isGloballyLongest : IsGloballyLongestMonoPath G Q
  q_closed_if_cut : IsCutColoring G → IsClosedPath Gᶜ Q
  isCounterexample : ¬ Erdos518ForType G
  induced_minimality :
    ∀ S : Finset V, S.card < Fintype.card V →
      Erdos518ForType (G.induce (S : Set V))

/-- A counterexample together with the broad strict-size induction hypothesis yields a
normalized configuration.  The graph in the configuration is the original graph or its
complement; in the cut case its chosen path is the actual closed cut witness. -/
theorem exists_configuration_of_counterexample {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : ¬ Erdos518ForType G)
    (hsmaller : HoldsForSmallerTypes V) :
    ∃ C : Configuration V, C.G = G ∨ C.G = Gᶜ := by
  obtain ⟨H, Q, hHG, hQ, hlongest, hproblem, -, hclosed⟩ :=
    exists_compl_normalized_longest_path_with_cut_witness G
  refine ⟨{
    G := H
    Q := Q
    q_isPath := hQ
    q_isGloballyLongest := hlongest
    q_closed_if_cut := hclosed
    isCounterexample := fun hH ↦ hG (hproblem.mp hH)
    induced_minimality := ?_ }, hHG⟩
  intro S hS
  apply hsmaller (W := S) ?_ (H.induce (S : Set V))
  simpa using hS

namespace Configuration

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance configurationDecidableEq : DecidableEq V := Classical.decEq V

/-- The vertices on the normalized longest path. -/
noncomputable def X : Finset V := by
  classical
  exact C.Q.toFinset

/-- The vertices outside the normalized longest path. -/
noncomputable def Y : Finset V := by
  classical
  exact Finset.univ \ C.X

/-- Complement-colour degree of `y` into `X`. -/
noncomputable def blueDegreeToX (y : V) : ℕ := by
  classical
  exact (C.X.filter fun x ↦ C.Gᶜ.Adj y x).card

/-- `G`-colour degree of `y` into `X`. -/
noncomputable def redDegreeToX (y : V) : ℕ := by
  classical
  exact (C.X.filter fun x ↦ C.G.Adj y x).card

/-- Outside vertices with no complement-colour neighbour on `Q`. -/
noncomputable def Y0 : Finset V := by
  classical
  exact C.Y.filter fun y ↦ C.blueDegreeToX y = 0

/-- Outside vertices with at least one complement-colour neighbour on `Q`. -/
noncomputable def Y1 : Finset V := by
  classical
  exact C.Y \ C.Y0

/-- The order of the ambient complete graph. -/
def n (_C : Configuration V) : ℕ := Fintype.card V

/-- The integer square root of the order. -/
def c : ℕ := Nat.sqrt C.n

/-- The remainder in `n = c² + r`. -/
def r : ℕ := C.n - C.c ^ 2

/-- The number of vertices outside `Q`. -/
noncomputable def w : ℕ := C.Y.card

/-- The size of the zero-complement-degree part of `Y`. -/
noncomputable def a0 : ℕ := C.Y0.card

/-- The size of the positive-complement-degree part of `Y`. -/
noncomputable def a1 : ℕ := C.Y1.card

/-- The maximum complement-colour degree into `X` among vertices of `Y1`.
`Finset.sup` gives the stipulated default value `0` when `Y1` is empty. -/
noncomputable def mu : ℕ := C.Y1.sup C.blueDegreeToX

@[simp] lemma mem_X {v : V} : v ∈ C.X ↔ v ∈ C.Q := by
  classical
  simp [X]

@[simp] lemma mem_Y {v : V} : v ∈ C.Y ↔ v ∉ C.X := by
  classical
  simp [Y]

@[simp] lemma mem_Y0 {v : V} :
    v ∈ C.Y0 ↔ v ∈ C.Y ∧ C.blueDegreeToX v = 0 := by
  classical
  simp [Y0]

@[simp] lemma mem_Y1 {v : V} :
    v ∈ C.Y1 ↔ v ∈ C.Y ∧ C.blueDegreeToX v ≠ 0 := by
  classical
  constructor
  · intro hv
    have h := Finset.mem_sdiff.mp hv
    refine ⟨h.1, ?_⟩
    intro hzero
    exact h.2 (C.mem_Y0.mpr ⟨h.1, hzero⟩)
  · rintro ⟨hvY, hne⟩
    exact Finset.mem_sdiff.mpr ⟨hvY, fun hv0 ↦ hne (C.mem_Y0.mp hv0).2⟩

@[simp] lemma card_X : C.X.card = C.Q.length := by
  classical
  simpa [X] using List.toFinset_card_of_nodup C.q_isPath.2.1

lemma X_union_Y : C.X ∪ C.Y = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_union, C.mem_X, C.mem_Y, Finset.mem_univ, iff_true]
  exact Classical.em (v ∈ C.Q)

lemma X_disjoint_Y : Disjoint C.X C.Y := by
  classical
  rw [Finset.disjoint_left]
  simp

lemma Y0_subset_Y : C.Y0 ⊆ C.Y := by
  classical
  intro v hv
  exact (C.mem_Y0.mp hv).1

lemma Y1_subset_Y : C.Y1 ⊆ C.Y := by
  classical
  intro v hv
  exact (C.mem_Y1.mp hv).1

lemma Y0_union_Y1 : C.Y0 ∪ C.Y1 = C.Y := by
  classical
  simpa only [Y1] using Finset.union_sdiff_of_subset C.Y0_subset_Y

lemma Y0_disjoint_Y1 : Disjoint C.Y0 C.Y1 := by
  classical
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  exact (Finset.mem_sdiff.mp hv1).2 hv0

@[simp] lemma n_eq_card : C.n = Fintype.card V := rfl

@[simp] lemma c_eq_sqrt : C.c = Nat.sqrt C.n := rfl

@[simp] lemma r_eq_sub_sq : C.r = C.n - C.c ^ 2 := rfl

@[simp] lemma w_eq_card_Y : C.w = C.Y.card := rfl

@[simp] lemma a0_eq_card_Y0 : C.a0 = C.Y0.card := rfl

@[simp] lemma a1_eq_card_Y1 : C.a1 = C.Y1.card := rfl

lemma n_eq_card_X_add_w : C.n = C.X.card + C.w := by
  classical
  calc
    C.n = (Finset.univ : Finset V).card := by simp [n]
    _ = (C.X ∪ C.Y).card := by rw [C.X_union_Y]
    _ = C.X.card + C.Y.card := Finset.card_union_of_disjoint C.X_disjoint_Y
    _ = C.X.card + C.w := rfl

lemma n_eq_Q_length_add_w : C.n = C.Q.length + C.w := by
  rw [C.n_eq_card_X_add_w, C.card_X]

lemma w_eq_a0_add_a1 : C.w = C.a0 + C.a1 := by
  classical
  calc
    C.w = C.Y.card := rfl
    _ = (C.Y0 ∪ C.Y1).card := by rw [C.Y0_union_Y1]
    _ = C.Y0.card + C.Y1.card := Finset.card_union_of_disjoint C.Y0_disjoint_Y1
    _ = C.a0 + C.a1 := rfl

lemma c_sq_le_n : C.c ^ 2 ≤ C.n := by
  simpa [c, n] using sqrt_sq_le (Fintype.card V)

lemma n_eq_c_sq_add_r : C.n = C.c ^ 2 + C.r := by
  simpa [n, c, r, sqrtRemainder] using
    (sqrt_sq_add_remainder (Fintype.card V)).symm

lemma r_le_two_mul_c : C.r ≤ 2 * C.c := by
  simpa [n, c, r, sqrtRemainder] using
    sqrt_remainder_le_two_mul (Fintype.card V)

lemma blueDegreeToX_le_card_X (y : V) : C.blueDegreeToX y ≤ C.X.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma blueDegreeToX_pos_of_mem_Y1 {y : V} (hy : y ∈ C.Y1) :
    1 ≤ C.blueDegreeToX y := by
  exact Nat.one_le_iff_ne_zero.mpr (C.mem_Y1.mp hy).2

lemma blueDegreeToX_le_mu_of_mem_Y1 {y : V} (hy : y ∈ C.Y1) :
    C.blueDegreeToX y ≤ C.mu := by
  exact Finset.le_sup hy

lemma exists_mem_Y1_blueDegreeToX_eq_mu (hY1 : C.Y1.Nonempty) :
    ∃ y ∈ C.Y1, C.blueDegreeToX y = C.mu := by
  obtain ⟨y, hy, hmu⟩ := Finset.exists_mem_eq_sup C.Y1 hY1 C.blueDegreeToX
  exact ⟨y, hy, hmu.symm⟩

lemma one_le_mu (hY1 : C.Y1.Nonempty) : 1 ≤ C.mu := by
  obtain ⟨y, hy⟩ := hY1
  exact (C.blueDegreeToX_pos_of_mem_Y1 hy).trans
    (C.blueDegreeToX_le_mu_of_mem_Y1 hy)

lemma mu_le_card_X (hY1 : C.Y1.Nonempty) : C.mu ≤ C.X.card := by
  obtain ⟨y, -, hy⟩ := C.exists_mem_Y1_blueDegreeToX_eq_mu hY1
  rw [← hy]
  exact C.blueDegreeToX_le_card_X y

lemma blueDegreeToX_le_mu_of_mem_Y {y : V} (hy : y ∈ C.Y) :
    C.blueDegreeToX y ≤ C.mu := by
  classical
  by_cases hy0 : y ∈ C.Y0
  · rw [(C.mem_Y0.mp hy0).2]
    exact Nat.zero_le _
  · exact C.blueDegreeToX_le_mu_of_mem_Y1 (C.mem_Y1.mpr ⟨hy, by
      intro hzero
      exact hy0 (C.mem_Y0.mpr ⟨hy, hzero⟩)⟩)

/-- For a vertex outside `X`, its two coloured degrees into `X` add to `|X|`. -/
lemma redDegreeToX_add_blueDegreeToX {y : V} (hy : y ∈ C.Y) :
    C.redDegreeToX y + C.blueDegreeToX y = C.X.card := by
  classical
  let R := C.X.filter fun x ↦ C.G.Adj y x
  let B := C.X.filter fun x ↦ C.Gᶜ.Adj y x
  have hyX : y ∉ C.X := C.mem_Y.mp hy
  have hUnion : R ∪ B = C.X := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxR | hxB
      · exact (Finset.mem_filter.mp hxR).1
      · exact (Finset.mem_filter.mp hxB).1
    · intro hx
      by_cases hadj : C.G.Adj y x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hadj⟩)
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hx, (SimpleGraph.compl_adj C.G y x).2 ⟨by
          intro hyx
          apply hyX
          simpa [hyx] using hx, hadj⟩⟩
  have hDisjoint : Disjoint R B := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    have hred : C.G.Adj y x := (Finset.mem_filter.mp hxR).2
    have hblue : C.Gᶜ.Adj y x := (Finset.mem_filter.mp hxB).2
    exact ((SimpleGraph.compl_adj C.G y x).mp hblue).2 hred
  have hcard : (R ∪ B).card = R.card + B.card :=
    Finset.card_union_of_disjoint hDisjoint
  rw [hUnion] at hcard
  simpa [redDegreeToX, blueDegreeToX, R, B] using hcard.symm

lemma redDegreeToX_eq_card_X_sub_blueDegreeToX {y : V} (hy : y ∈ C.Y) :
    C.redDegreeToX y = C.X.card - C.blueDegreeToX y := by
  have hsum := C.redDegreeToX_add_blueDegreeToX hy
  omega

lemma card_X_sub_mu_le_redDegreeToX {y : V} (hy : y ∈ C.Y) :
    C.X.card - C.mu ≤ C.redDegreeToX y := by
  calc
    C.X.card - C.mu ≤ C.X.card - C.blueDegreeToX y :=
      Nat.sub_le_sub_left (C.blueDegreeToX_le_mu_of_mem_Y hy) C.X.card
    _ = C.redDegreeToX y := (C.redDegreeToX_eq_card_X_sub_blueDegreeToX hy).symm

/-- All elementary maximum-degree bounds, in the form used after `Y1` has been proved
nonempty in the counterexample argument. -/
lemma mu_degree_bounds (hY1 : C.Y1.Nonempty) :
    1 ≤ C.mu ∧ C.mu ≤ C.X.card ∧
      ∀ y ∈ C.Y,
        C.blueDegreeToX y ≤ C.mu ∧
          C.X.card - C.mu ≤ C.redDegreeToX y := by
  refine ⟨C.one_le_mu hY1, C.mu_le_card_X hY1, ?_⟩
  intro y hy
  exact ⟨C.blueDegreeToX_le_mu_of_mem_Y hy, C.card_X_sub_mu_le_redDegreeToX hy⟩

end Configuration

end Erdos518

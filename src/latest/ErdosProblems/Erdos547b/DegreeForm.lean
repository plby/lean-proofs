/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Regularity
import ErdosProblems.Erdos547b.Stability
import Mathlib.Tactic

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoDegreeForm

open SimpleGraph
open Erdos547b.ZhaoStability

/-- The small bad-cluster/bad-vertex fraction used to derive degree form. -/
def cleanupFraction (ε : ℚ) : ℝ := min ((ε : ℝ) / 64) (1 / 64)

/-- The ordinary-regularity parameter fed to Mathlib. -/
def ordinaryError (ε : ℚ) : ℝ := cleanupFraction ε ^ 2 / 2

/-- The number of parts requested from ordinary regularity. -/
def requestedParts (m₀ : ℕ) : ℕ := max 1 (2 * m₀)

/-- A graph-independent upper bound on the number of ordinary parts. -/
def degreeFormBound (ε : ℚ) (m₀ : ℕ) : ℕ :=
  SzemerediRegularity.bound (ordinaryError ε) (requestedParts m₀)

/-- An explicit host threshold.  Five vertices per possible ordinary part are
enough for all rounding, trimming, and slicing inequalities below. -/
def degreeFormThreshold (ε : ℚ) (m₀ : ℕ) : ℕ :=
  5 * degreeFormBound ε m₀

theorem cleanupFraction_pos {ε : ℚ} (hε : 0 < ε) :
    0 < cleanupFraction ε := by
  unfold cleanupFraction
  positivity

theorem cleanupFraction_le_eps_div {ε : ℚ} :
    cleanupFraction ε ≤ (ε : ℝ) / 64 := min_le_left _ _

theorem cleanupFraction_le_one_div (ε : ℚ) :
    cleanupFraction ε ≤ (1 : ℝ) / 64 := min_le_right _ _

theorem ordinaryError_pos {ε : ℚ} (hε : 0 < ε) :
    0 < ordinaryError ε := by
  have hq := cleanupFraction_pos hε
  unfold ordinaryError
  positivity

theorem ordinaryError_le_cleanup_sq (ε : ℚ) :
    ordinaryError ε ≤ cleanupFraction ε ^ 2 := by
  unfold ordinaryError
  nlinarith [sq_nonneg (cleanupFraction ε)]

theorem twice_ordinaryError_le_eps {ε : ℚ} (hε : 0 < ε) :
    2 * ordinaryError ε ≤ (ε : ℝ) := by
  have hqpos := cleanupFraction_pos hε
  have hqε := cleanupFraction_le_eps_div (ε := ε)
  have hqone := cleanupFraction_le_one_div ε
  unfold ordinaryError
  nlinarith

/-- All finite rounding inequalities used by the cleanup.  The constant `5`
is deliberately generous; this keeps the host threshold completely explicit. -/
theorem cleanup_numerics {ε : ℚ} (hε : 0 < ε) {a : ℕ} (ha : 5 ≤ a) :
    let q := cleanupFraction ε
    let η := ordinaryError ε
    let r := ⌈q * ((a + 1 : ℕ) : ℝ)⌉₊
    q * ((a + 1 : ℕ) : ℝ) ≤ (r : ℝ) ∧
      r < a ∧
      a + 1 < 2 * (a - r) ∧
      ((a + 1 : ℕ) : ℝ) * η ≤ ((a - r : ℕ) : ℝ) ∧
      ((a + 1 : ℕ) : ℝ) * η ≤ ((a - r : ℕ) : ℝ) * (ε : ℝ) := by
  dsimp only
  let q := cleanupFraction ε
  let η := ordinaryError ε
  let r := ⌈q * ((a + 1 : ℕ) : ℝ)⌉₊
  have hqpos : 0 < q := cleanupFraction_pos hε
  have hq0 : 0 ≤ q := hqpos.le
  have hqone : q ≤ (1 : ℝ) / 64 := cleanupFraction_le_one_div ε
  have hqε : q ≤ (ε : ℝ) / 64 := cleanupFraction_le_eps_div
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hηeq : η = q ^ 2 / 2 := rfl
  have hη0 : 0 ≤ η := by rw [hηeq]; positivity
  have hηone : η ≤ (1 : ℝ) / 8192 := by
    rw [hηeq]
    nlinarith
  have hqsqε : q ^ 2 ≤ (ε : ℝ) / 4096 := by
    calc
      q ^ 2 = q * q := by ring
      _ ≤ q * ((ε : ℝ) / 64) :=
        mul_le_mul_of_nonneg_left hqε hq0
      _ ≤ ((1 : ℝ) / 64) * ((ε : ℝ) / 64) :=
        mul_le_mul_of_nonneg_right hqone (by positivity)
      _ = (ε : ℝ) / 4096 := by ring
  have hηε : η ≤ (ε : ℝ) / 8192 := by
    rw [hηeq]
    nlinarith
  have hceilLower : q * ((a + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
    exact Nat.le_ceil _
  have hceilUpper : (r : ℝ) < q * ((a + 1 : ℕ) : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg hq0 (Nat.cast_nonneg _))
  have hqmul : q * ((a + 1 : ℕ) : ℝ) ≤
      ((1 : ℝ) / 64) * ((a + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hqone (Nat.cast_nonneg _)
  have haR : (5 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hrlt : (r : ℝ) < (a : ℝ) / 4 := by
    norm_num at hqmul ⊢
    push_cast at hqmul hceilUpper
    nlinarith
  have hra : r < a := by exact_mod_cast (hrlt.trans_le (by nlinarith : (a : ℝ) / 4 ≤ a))
  have hrle : r ≤ a := hra.le
  have hsub : ((a - r : ℕ) : ℝ) = (a : ℝ) - (r : ℝ) := by
    rw [Nat.cast_sub hrle]
  have hmLower : (3 : ℝ) * a / 4 < ((a - r : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith
  have hdouble : a + 1 < 2 * (a - r) := by
    exact_mod_cast (by
      push_cast
      nlinarith [hmLower, haR] :
        ((a + 1 : ℕ) : ℝ) < (2 * (a - r) : ℕ))
  have hηmul : ((a + 1 : ℕ) : ℝ) * η ≤
      ((a + 1 : ℕ) : ℝ) / 8192 := by
    calc
      ((a + 1 : ℕ) : ℝ) * η ≤
          ((a + 1 : ℕ) : ℝ) * ((1 : ℝ) / 8192) :=
        mul_le_mul_of_nonneg_left hηone (Nat.cast_nonneg _)
      _ = ((a + 1 : ℕ) : ℝ) / 8192 := by ring
  have hηmulε : ((a + 1 : ℕ) : ℝ) * η ≤
      ((a + 1 : ℕ) : ℝ) * (ε : ℝ) / 8192 := by
    calc
      ((a + 1 : ℕ) : ℝ) * η ≤
          ((a + 1 : ℕ) : ℝ) * ((ε : ℝ) / 8192) :=
        mul_le_mul_of_nonneg_left hηε (Nat.cast_nonneg _)
      _ = ((a + 1 : ℕ) : ℝ) * (ε : ℝ) / 8192 := by ring
  have hlarge : ((a + 1 : ℕ) : ℝ) * η ≤ ((a - r : ℕ) : ℝ) := by
    have hsmall : ((a + 1 : ℕ) : ℝ) / 8192 < (3 : ℝ) * a / 4 := by
      push_cast
      nlinarith [haR]
    exact hηmul.trans hsmall.le |>.trans hmLower.le
  have hscale : ((a + 1 : ℕ) : ℝ) * η ≤
      ((a - r : ℕ) : ℝ) * (ε : ℝ) := by
    apply hηmulε.trans
    push_cast
    have := mul_lt_mul_of_pos_right hmLower hεR
    nlinarith
  exact ⟨hceilLower, hra, hdouble, hlarge, hscale⟩

/-- Convert Mathlib's real-valued regularity predicate to the rational
predicate used by the stability reduced graph. -/
theorem isUniform_rat_of_real {V : Type*} {G : SimpleGraph V}
    [DecidableRel G.Adj] {ε : ℚ} {A B : Finset V}
    (h : G.IsUniform (ε : ℝ) A B) : G.IsUniform ε A B := by
  intro A' hA' B' hB' hAc hBc
  have hAc' : (#A : ℝ) * (ε : ℝ) ≤ (#A' : ℝ) := by exact_mod_cast hAc
  have hBc' : (#B : ℝ) * (ε : ℝ) ≤ (#B' : ℝ) := by exact_mod_cast hBc
  have hh := h hA' hB' hAc' hBc'
  exact_mod_cast hh

/-- The assignment associated to a partition of the complement of `E`.
The cluster index literally contains the corresponding part. -/
def partitionAssignment {n : ℕ} (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E)) :
    ClusterAssignment (Fin n) {W // W ∈ Q.parts} :=
  fun x => if hx : x ∈ (Finset.univ : Finset (Fin n)) \ E then
    some ⟨Q.part x, Q.part_mem.mpr hx⟩ else none

@[simp] theorem partitionAssignment_eq_none_iff {n : ℕ}
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E)) (x : Fin n) :
    partitionAssignment E Q x = none ↔ x ∈ E := by
  classical
  simp [partitionAssignment]

@[simp] theorem exceptionalVertices_partitionAssignment {n : ℕ}
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E)) :
    exceptionalVertices (partitionAssignment E Q) = E := by
  classical
  ext x
  simp

@[simp] theorem partitionAssignment_eq_some_iff {n : ℕ}
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (x : Fin n) (i : {W // W ∈ Q.parts}) :
    partitionAssignment E Q x = some i ↔ x ∈ i.1 := by
  classical
  constructor
  · intro hx
    unfold partitionAssignment at hx
    split at hx
    · simp only [Option.some.injEq, Subtype.ext_iff] at hx
      rw [← hx]
      exact Q.mem_part (by assumption)
    · contradiction
  · intro hx
    have hiSub : i.1 ⊆ (Finset.univ : Finset (Fin n)) \ E := Q.le i.2
    have hxcomp := hiSub hx
    unfold partitionAssignment
    rw [dif_pos hxcomp]
    have hsub :
        (⟨Q.part x, Q.part_mem.mpr hxcomp⟩ : {W // W ∈ Q.parts}) = i := by
      apply Subtype.ext
      exact Q.part_eq_of_mem i.2 hx
    exact congrArg some hsub

@[simp] theorem clusterVertices_partitionAssignment {n : ℕ}
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (i : {W // W ∈ Q.parts}) :
    clusterVertices (partitionAssignment E Q) i = i.1 := by
  classical
  ext x
  simp

private theorem edgeDensity_eq_of_adj_iff {V : Type*}
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {A B : Finset V}
    (h : ∀ x ∈ A, ∀ y ∈ B, H.Adj x y ↔ G.Adj x y) :
    H.edgeDensity A B = G.edgeDensity A B := by
  have hinter : H.interedges A B = G.interedges A B := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff]
    constructor
    · rintro ⟨hpA, hpB, hp⟩
      exact ⟨hpA, hpB, (h p.1 hpA p.2 hpB).mp hp⟩
    · rintro ⟨hpA, hpB, hp⟩
      exact ⟨hpA, hpB, (h p.1 hpA p.2 hpB).mpr hp⟩
  rw [H.edgeDensity_def, G.edgeDensity_def, hinter]

private theorem isUniform_of_adj_iff {V : Type*}
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {ε : ℚ} {A B : Finset V} (hG : G.IsUniform ε A B)
    (h : ∀ x ∈ A, ∀ y ∈ B, H.Adj x y ↔ G.Adj x y) :
    H.IsUniform ε A B := by
  intro A' hA' B' hB' hAc hBc
  rw [edgeDensity_eq_of_adj_iff G H
      (fun x hx y hy => h x (hA' hx) y (hB' hy)),
    edgeDensity_eq_of_adj_iff G H h]
  exact hG hA' hB' hAc hBc

private theorem isUniform_of_no_cross_edges {V : Type*}
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {ε : ℚ} (hε : 0 < ε) {A B : Finset V}
    (h : ∀ x ∈ A, ∀ y ∈ B, ¬H.Adj x y) :
    H.IsUniform ε A B := by
  intro A' hA' B' hB' _ _
  have hz : H.edgeDensity A B = 0 := by
    rw [H.edgeDensity_def]
    have hinter : H.interedges A B = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [SimpleGraph.mem_interedges_iff] at hp
      exact h p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [hinter]
    simp
  have hz' : H.edgeDensity A' B' = 0 := by
    rw [H.edgeDensity_def]
    have hinter : H.interedges A' B' = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [SimpleGraph.mem_interedges_iff] at hp
      exact h p.1 (hA' hp.1) p.2 (hB' hp.2.1) hp.2.2
    rw [hinter]
    simp
  rw [hz, hz']
  simpa using hε

/-- The spanning degree-form graph.  All edges touching the exceptional set
are retained.  Between clean clusters we retain precisely the pairs whose
source pair was ordinary-regular and whose final density is strictly above
`d`. -/
def cleanedGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (η : ℝ) (d : ℚ) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧
    (x ∈ E ∨ y ∈ E ∨
      ∃ i j : {W // W ∈ Q.parts}, x ∈ i.1 ∧ y ∈ j.1 ∧ i ≠ j ∧
        G.IsUniform η (source i) (source j) ∧
        d < G.edgeDensity i.1 j.1)
  symm := ⟨by
    rintro x y ⟨hxy, hxE | hyE | hclean⟩
    · exact ⟨hxy.symm, Or.inr (Or.inl hxE)⟩
    · exact ⟨hxy.symm, Or.inl hyE⟩
    · rcases hclean with ⟨i, j, hxi, hyj, hij, hreg, hdense⟩
      exact ⟨hxy.symm, Or.inr (Or.inr ⟨j, i, hyj, hxi, hij.symm,
        hreg.symm, by rwa [G.edgeDensity_comm]⟩)⟩⟩
  loopless := ⟨fun x hx => G.loopless.irrefl x hx.1⟩

instance cleanedGraph.instDecidableRelAdj {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (η : ℝ) (d : ℚ) : DecidableRel (cleanedGraph G E Q source η d).Adj :=
  Classical.decRel _

theorem cleanedGraph_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (η : ℝ) (d : ℚ) : cleanedGraph G E Q source η d ≤ G :=
  fun _ _ h => h.1

theorem cleanedGraph_adj_on_clusters_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (η : ℝ) (d : ℚ) (i j : {W // W ∈ Q.parts})
    {x y : Fin n} (hx : x ∈ i.1) (hy : y ∈ j.1) :
    (cleanedGraph G E Q source η d).Adj x y ↔
      G.Adj x y ∧ i ≠ j ∧ G.IsUniform η (source i) (source j) ∧
        d < G.edgeDensity i.1 j.1 := by
  classical
  have hiSub := Q.le i.2 hx
  have hjSub := Q.le j.2 hy
  have hxE : x ∉ E := (Finset.mem_sdiff.mp hiSub).2
  have hyE : y ∉ E := (Finset.mem_sdiff.mp hjSub).2
  constructor
  · rintro ⟨hG, hclean⟩
    rcases hclean with hxE' | hyE' | ⟨i', j', hxi', hyj', hij', hreg, hdense⟩
    · exact (hxE hxE').elim
    · exact (hyE hyE').elim
    · have hii' : i = i' := by
        apply Subtype.ext
        by_contra hne
        exact (Finset.disjoint_left.mp (Q.disjoint i.2 i'.2 hne) hx hxi').elim
      have hjj' : j = j' := by
        apply Subtype.ext
        by_contra hne
        exact (Finset.disjoint_left.mp (Q.disjoint j.2 j'.2 hne) hy hyj').elim
      subst i'; subst j'
      exact ⟨hG, hij', hreg, hdense⟩
  · rintro ⟨hG, hij, hreg, hdense⟩
    exact ⟨hG, Or.inr (Or.inr ⟨i, j, hx, hy, hij, hreg, hdense⟩)⟩

/-- Exact loss used in the output theorem.  Here `K` is the number of
ordinary parts, `m` the final common cluster size, and `s` the ordinary
upper cluster size. -/
def explicitDegreeLoss (ε d : ℚ) (K m s : ℕ) : ℕ :=
  m + ⌈(2 * cleanupFraction ε + (d : ℝ) + 2 * ordinaryError ε) * K * s⌉₊

private theorem degree_loss_of_cleanup
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} (hε : 0 < ε) (hd : 0 < d)
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hequip : P.IsEquipartition)
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (m : ℕ)
    (hsourceInj : Function.Injective source)
    (hsource : ∀ i,
      i.1.card = m ∧
      source i ∈ P.parts \ P.badClusters G (ordinaryError ε) (cleanupFraction ε) ∧
      i.1 ⊆ source i \ P.upperBadVertices G (ordinaryError ε) (cleanupFraction ε) (source i) ∧
      (#(P.irregularPairsFrom G (ordinaryError ε) (source i)) : ℝ) ≤
        cleanupFraction ε * (#P.parts : ℝ) ∧
      ∀ x ∈ i.1,
        (#(P.upperAtypicalPartnersAt G (ordinaryError ε) (source i) x) : ℝ) ≤
          cleanupFraction ε * (#P.parts : ℝ))
    (hlarge : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤ (m : ℝ)) :
    DegreeLossAtMost G
      (cleanedGraph G E Q source (ordinaryError ε) d)
      (explicitDegreeLoss ε d #P.parts m (n / #P.parts + 1)) := by
  classical
  let η := ordinaryError ε
  let q := cleanupFraction ε
  let K := #P.parts
  let smax := n / K + 1
  let H := cleanedGraph G E Q source η d
  let loss := explicitDegreeLoss ε d K m smax
  have hη0 : 0 ≤ η := (ordinaryError_pos hε).le
  have hq0 : 0 ≤ q := (cleanupFraction_pos hε).le
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpartSize : ∀ U ∈ P.parts, #U ≤ smax := by
    intro U hU
    dsimp [smax, K]
    simpa using hequip.card_part_le_average_add_one hU
  intro x
  by_cases hxE : x ∈ E
  · have hneighbors : H.neighborFinset x = G.neighborFinset x := by
      ext y
      simp only [SimpleGraph.mem_neighborFinset]
      constructor
      · exact fun h => h.1
      · intro hxy
        exact ⟨hxy, Or.inl hxE⟩
    have hdegreeEq : H.degree x = G.degree x := congrArg Finset.card hneighbors
    change G.degree x ≤ H.degree x + loss
    rw [hdegreeEq]
    exact Nat.le_add_right _ _
  · have hxcomp : x ∈ (Finset.univ : Finset (Fin n)) \ E := by simp [hxE]
    let i : {W // W ∈ Q.parts} := ⟨Q.part x, Q.part_mem.mpr hxcomp⟩
    have hxi : x ∈ i.1 := Q.mem_part hxcomp
    let U := source i
    have hiSpec := hsource i
    have hUP : U ∈ P.parts := (Finset.mem_sdiff.mp hiSpec.2.1).1
    have hxiU : x ∈ U := (Finset.mem_sdiff.mp (hiSpec.2.2.1 hxi)).1
    let Missing := G.neighborFinset x \ H.neighborFinset x
    let Irr : Finset (Fin n) :=
      (P.irregularPairsFrom G η U).biUnion fun UV => UV.2
    let Upper : Finset (Fin n) :=
      (P.upperAtypicalPartnersAt G η U x).biUnion id
    let LowSources : Finset (Finset (Fin n)) :=
      P.parts.filter fun V =>
        U ≠ V ∧ G.IsUniform η U V ∧
        x ∉ SimpleGraph.upperAtypicalVertices G η U V ∧
        ∃ j : {W // W ∈ Q.parts}, source j = V ∧
          G.edgeDensity i.1 j.1 ≤ d
    let Low : Finset (Fin n) :=
      LowSources.biUnion fun V => V.filter fun y => G.Adj x y
    have hMissingSub : Missing ⊆ i.1 ∪ Irr ∪ Upper ∪ Low := by
      intro y hy
      have hyG : G.Adj x y := by
        simpa using (Finset.mem_sdiff.mp hy).1
      have hyNotH : ¬H.Adj x y := by
        simpa using (Finset.mem_sdiff.mp hy).2
      have hyNotE : y ∉ E := by
        intro hyE
        exact hyNotH ⟨hyG, Or.inr (Or.inl hyE)⟩
      have hycomp : y ∈ (Finset.univ : Finset (Fin n)) \ E := by simp [hyNotE]
      let j : {W // W ∈ Q.parts} := ⟨Q.part y, Q.part_mem.mpr hycomp⟩
      have hyj : y ∈ j.1 := Q.mem_part hycomp
      have hjSpec := hsource j
      let V := source j
      have hVP : V ∈ P.parts := (Finset.mem_sdiff.mp hjSpec.2.1).1
      have hyV : y ∈ V := (Finset.mem_sdiff.mp (hjSpec.2.2.1 hyj)).1
      by_cases hij : i = j
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (by simpa [hij] using hyj)))
      by_cases hUV : U = V
      · exact (hij (hsourceInj (by simpa [U, V] using hUV))).elim
      by_cases hreg : G.IsUniform η U V
      · by_cases hupper : x ∈ SimpleGraph.upperAtypicalVertices G η U V
        · apply Finset.mem_union_left Low
          apply Finset.mem_union_right (i.1 ∪ Irr)
          apply Finset.mem_biUnion.mpr
          refine ⟨V, ?_, hyV⟩
          simp [Finpartition.upperAtypicalPartnersAt, hUV, hreg, hupper, hVP]
        · apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨V, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨hVP, hUV, hreg, hupper, j, rfl, ?_⟩
            apply le_of_not_gt
            intro hdense
            exact hyNotH <| (cleanedGraph_adj_on_clusters_iff
              G E Q source η d i j hxi hyj).mpr ⟨hyG, hij, hreg, hdense⟩
          · exact Finset.mem_filter.mpr ⟨hyV, hyG⟩
      · apply Finset.mem_union_left Low
        apply Finset.mem_union_left Upper
        apply Finset.mem_union_right i.1
        apply Finset.mem_biUnion.mpr
        refine ⟨(U, V), ?_, hyV⟩
        simp [Finpartition.irregularPairsFrom,
          Finpartition.mk_mem_nonUniforms, hUP, hVP, hUV, hreg]
    have hIrrCard : (#Irr : ℝ) ≤ q * K * smax := by
      calc
        (#Irr : ℝ) ≤
            (#(P.irregularPairsFrom G η U) : ℝ) * smax := by
          exact_mod_cast Finset.card_biUnion_le_card_mul
            (P.irregularPairsFrom G η U) (fun UV => UV.2) smax
              (fun UV hUV => hpartSize UV.2
                ((Finpartition.mk_mem_nonUniforms (P := P) (G := G) (ε := η)).mp
                  (Finset.mem_filter.mp hUV).1).2.1)
        _ ≤ (q * K) * smax := by
          exact mul_le_mul_of_nonneg_right hiSpec.2.2.2.1 (Nat.cast_nonneg _)
        _ = q * K * smax := rfl
    have hUpperCard : (#Upper : ℝ) ≤ q * K * smax := by
      calc
        (#Upper : ℝ) ≤
            (#(P.upperAtypicalPartnersAt G η U x) : ℝ) * smax := by
          exact_mod_cast Finset.card_biUnion_le_card_mul
            (P.upperAtypicalPartnersAt G η U x) id smax
              (fun V hV => hpartSize V (Finset.mem_filter.mp hV).1)
        _ ≤ (q * K) * smax := by
          exact mul_le_mul_of_nonneg_right (hiSpec.2.2.2.2 x hxi)
            (Nat.cast_nonneg _)
        _ = q * K * smax := rfl
    have hLowPiece : ∀ V ∈ LowSources,
        (#(V.filter fun y => G.Adj x y) : ℝ) ≤ ((d : ℝ) + 2 * η) * smax := by
      intro V hV
      rcases Finset.mem_filter.mp hV with ⟨hVP', hUV, hreg, htypical,
        j, hjSource, hdense⟩
      have hjSpec := hsource j
      have hVsize : (#V : ℝ) ≤ (smax : ℝ) := by
        exact_mod_cast hpartSize V hVP'
      have hUsize : (#U : ℝ) ≤ (smax : ℝ) := by
        exact_mod_cast hpartSize U hUP
      have hiCardR : (#i.1 : ℝ) = (m : ℝ) := by exact_mod_cast hiSpec.1
      have hjCardR : (#j.1 : ℝ) = (m : ℝ) := by exact_mod_cast hjSpec.1
      have hiSubU : i.1 ⊆ U :=
        (hiSpec.2.2.1).trans (Finset.sdiff_subset)
      have hjSubV : j.1 ⊆ V := by
        rw [← hjSource]
        exact (hjSpec.2.2.1).trans (Finset.sdiff_subset)
      have hiLarge : (#U : ℝ) * η ≤ (#i.1 : ℝ) := by
        calc
          (#U : ℝ) * η ≤ (smax : ℝ) * η :=
            mul_le_mul_of_nonneg_right hUsize hη0
          _ ≤ (m : ℝ) := by simpa [η, smax, K] using hlarge
          _ = (#i.1 : ℝ) := hiCardR.symm
      have hjLarge : (#V : ℝ) * η ≤ (#j.1 : ℝ) := by
        calc
          (#V : ℝ) * η ≤ (smax : ℝ) * η :=
            mul_le_mul_of_nonneg_right hVsize hη0
          _ ≤ (m : ℝ) := by simpa [η, smax, K] using hlarge
          _ = (#j.1 : ℝ) := hjCardR.symm
      have hdensityClose := hreg hiSubU hjSubV hiLarge hjLarge
      have horig : (G.edgeDensity U V : ℝ) <
          (G.edgeDensity i.1 j.1 : ℝ) + η := by
        rw [abs_sub_lt_iff] at hdensityClose
        linarith
      have hcoef : (G.edgeDensity U V : ℝ) + η < (d : ℝ) + 2 * η := by
        have hdenseR : (G.edgeDensity i.1 j.1 : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast hdense
        linarith
      have hxNotUpper : ¬((G.edgeDensity U V : ℝ) + η) * (#V : ℝ) <
          (#{y ∈ V | G.Adj x y} : ℝ) := by
        simpa [SimpleGraph.upperAtypicalVertices, hxiU] using htypical
      have hcount : (#{y ∈ V | G.Adj x y} : ℝ) ≤
          ((G.edgeDensity U V : ℝ) + η) * (#V : ℝ) := le_of_not_gt hxNotUpper
      calc
        (#{y ∈ V | G.Adj x y} : ℝ) ≤
            ((G.edgeDensity U V : ℝ) + η) * (#V : ℝ) := hcount
        _ ≤ ((d : ℝ) + 2 * η) * (#V : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg _)
        _ ≤ ((d : ℝ) + 2 * η) * smax := by
          exact mul_le_mul_of_nonneg_left hVsize (by positivity)
    have hLowCard : (#Low : ℝ) ≤ ((d : ℝ) + 2 * η) * K * smax := by
      calc
        (#Low : ℝ) ≤
            ∑ V ∈ LowSources, (#(V.filter fun y => G.Adj x y) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _V ∈ LowSources, ((d : ℝ) + 2 * η) * smax := by
          exact Finset.sum_le_sum fun V hV => hLowPiece V hV
        _ = (#LowSources : ℝ) * (((d : ℝ) + 2 * η) * smax) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (K : ℝ) * (((d : ℝ) + 2 * η) * smax) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_filter_le P.parts _
          · positivity
        _ = ((d : ℝ) + 2 * η) * K * smax := by ring
    have hMissingCard : (#Missing : ℝ) ≤
        (m : ℝ) + (2 * q + (d : ℝ) + 2 * η) * K * smax := by
      calc
        (#Missing : ℝ) ≤ (#(i.1 ∪ Irr ∪ Upper ∪ Low) : ℝ) := by
          exact_mod_cast Finset.card_le_card hMissingSub
        _ ≤ (#i.1 : ℝ) + #Irr + #Upper + #Low := by
          exact_mod_cast (Finset.card_union_le (i.1 ∪ Irr ∪ Upper) Low |>.trans
            (Nat.add_le_add_right
              ((Finset.card_union_le (i.1 ∪ Irr) Upper).trans
                (Nat.add_le_add_right (Finset.card_union_le i.1 Irr) _)) _))
        _ ≤ (m : ℝ) + (q * K * smax) + (q * K * smax) +
            (((d : ℝ) + 2 * η) * K * smax) := by
          gcongr
          · exact_mod_cast hiSpec.1.le
        _ = (m : ℝ) + (2 * q + (d : ℝ) + 2 * η) * K * smax := by ring
    have hMissingNat : #Missing ≤ loss := by
      have hceil :
          (2 * q + (d : ℝ) + 2 * η) * K * smax ≤
            (⌈(2 * q + (d : ℝ) + 2 * η) * K * smax⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hcast : (#Missing : ℝ) ≤ (loss : ℝ) := by
        have hsum : (m : ℝ) +
            (2 * q + (d : ℝ) + 2 * η) * K * smax ≤
            (m : ℝ) +
              (⌈(2 * q + (d : ℝ) + 2 * η) * K * smax⌉₊ : ℝ) := by
          gcongr
        have hh := hMissingCard.trans hsum
        simpa [loss, explicitDegreeLoss, q, η] using hh
      exact_mod_cast hcast
    have hHsubG : H.neighborFinset x ⊆ G.neighborFinset x := by
      intro y hy
      have hyAdj : H.Adj x y := by simpa using hy
      have : G.Adj x y := (cleanedGraph_le G E Q source η d) hyAdj
      simpa using this
    have hdegreeSplit : G.degree x = H.degree x + #Missing := by
      calc
        G.degree x = #(G.neighborFinset x) := rfl
        _ = #(H.neighborFinset x) + #Missing := by
          dsimp [Missing]
          rw [Finset.card_sdiff_of_subset hHsubG]
          have hcard := Finset.card_le_card hHsubG
          exact (Nat.add_sub_of_le hcard).symm
        _ = H.degree x + #Missing := rfl
    rw [hdegreeSplit]
    exact Nat.add_le_add_left hMissingNat _

private theorem cleaned_pair_uniform_G
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε : ℚ} (hε : 0 < ε)
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hequip : P.IsEquipartition)
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (m r : ℕ)
    (hsource : ∀ i,
      i.1.card = m ∧ source i ∈ P.parts ∧ i.1 ⊆ source i)
    (hlarge : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤ (m : ℝ))
    (hscale : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤
      (m : ℝ) * (ε : ℝ))
    (hm : m = n / #P.parts - r)
    {i j : {W // W ∈ Q.parts}}
    (hreg : G.IsUniform (ordinaryError ε) (source i) (source j)) :
    G.IsUniform ε i.1 j.1 := by
  have hi := hsource i
  have hj := hsource j
  apply isUniform_rat_of_real
  apply Finpartition.IsEquipartition.isUniform_of_cleaned_subsets_fin
    P hequip (ordinaryError_pos hε).le
  · simpa [hm] using hlarge
  · simpa [hm] using hscale
  · exact twice_ordinaryError_le_eps hε
  · exact hi.2.1
  · exact hj.2.1
  · exact hi.2.2
  · exact hj.2.2
  · simpa [hm] using hi.1
  · simpa [hm] using hj.1
  · exact hreg

private theorem cleanedGraph_pair_uniform
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} (hε : 0 < ε)
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hequip : P.IsEquipartition)
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (m r : ℕ)
    (hsource : ∀ i,
      i.1.card = m ∧ source i ∈ P.parts ∧ i.1 ⊆ source i)
    (hlarge : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤ (m : ℝ))
    (hscale : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤
      (m : ℝ) * (ε : ℝ))
    (hm : m = n / #P.parts - r)
    (i j : {W // W ∈ Q.parts}) :
    (cleanedGraph G E Q source (ordinaryError ε) d).IsUniform ε i.1 j.1 := by
  classical
  let H := cleanedGraph G E Q source (ordinaryError ε) d
  by_cases hkeep : i ≠ j ∧
      G.IsUniform (ordinaryError ε) (source i) (source j) ∧
      d < G.edgeDensity i.1 j.1
  · apply isUniform_of_adj_iff G H
      (cleaned_pair_uniform_G hε P hequip E Q source m r hsource
        hlarge hscale hm hkeep.2.1)
    intro x hx y hy
    rw [cleanedGraph_adj_on_clusters_iff
      G E Q source (ordinaryError ε) d i j hx hy]
    exact and_iff_left hkeep
  · apply isUniform_of_no_cross_edges H hε
    intro x hx y hy hxy
    have hh := (cleanedGraph_adj_on_clusters_iff
      G E Q source (ordinaryError ε) d i j hx hy).mp hxy
    exact hkeep ⟨hh.2.1, hh.2.2.1, hh.2.2.2⟩

private theorem cleanedGraph_pair_density
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ}
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (i j : {W // W ∈ Q.parts}) :
    (cleanedGraph G E Q source (ordinaryError ε) d).edgeDensity i.1 j.1 = 0 ∨
      d < (cleanedGraph G E Q source (ordinaryError ε) d).edgeDensity i.1 j.1 := by
  classical
  let H := cleanedGraph G E Q source (ordinaryError ε) d
  by_cases hkeep : i ≠ j ∧
      G.IsUniform (ordinaryError ε) (source i) (source j) ∧
      d < G.edgeDensity i.1 j.1
  · right
    rw [edgeDensity_eq_of_adj_iff G H]
    · exact hkeep.2.2
    · intro x hx y hy
      rw [cleanedGraph_adj_on_clusters_iff
        G E Q source (ordinaryError ε) d i j hx hy]
      exact and_iff_left hkeep
  · left
    rw [H.edgeDensity_def]
    have hinter : H.interedges i.1 j.1 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [SimpleGraph.mem_interedges_iff] at hp
      have hh := (cleanedGraph_adj_on_clusters_iff
        G E Q source (ordinaryError ε) d i j hp.1 hp.2.1).mp hp.2.2
      exact hkeep ⟨hh.2.1, hh.2.2.1, hh.2.2.2⟩
    rw [hinter]
    simp

private theorem cleanedGraph_respects_reduced
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} (hε : 0 < ε)
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (hequip : P.IsEquipartition)
    (E : Finset (Fin n))
    (Q : Finpartition ((Finset.univ : Finset (Fin n)) \ E))
    (source : {W // W ∈ Q.parts} → Finset (Fin n))
    (m r : ℕ)
    (hsource : ∀ i,
      i.1.card = m ∧ source i ∈ P.parts ∧ i.1 ⊆ source i)
    (hlarge : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤ (m : ℝ))
    (hscale : (((n / #P.parts + 1 : ℕ) : ℝ) * ordinaryError ε) ≤
      (m : ℝ) * (ε : ℝ))
    (hm : m = n / #P.parts - r) :
    EdgesRespectReducedGraph (partitionAssignment E Q)
      (cleanedGraph G E Q source (ordinaryError ε) d)
      (regularityReducedGraph G (fun i : {W // W ∈ Q.parts} => i.1) ε d) := by
  intro x y i j hxi hyj hxy
  have hxi' : x ∈ i.1 := (partitionAssignment_eq_some_iff E Q x i).mp hxi
  have hyj' : y ∈ j.1 := (partitionAssignment_eq_some_iff E Q y j).mp hyj
  have hh := (cleanedGraph_adj_on_clusters_iff
    G E Q source (ordinaryError ε) d i j hxi' hyj').mp hxy
  rw [regularityReducedGraph_adj]
  refine ⟨hh.2.1, ?_, hh.2.2.2.le⟩
  exact cleaned_pair_uniform_G hε P hequip E Q source m r hsource
    hlarge hscale hm hh.2.2.1

/-- A fully concrete degree-form regularity output, indexed directly by the
parts of the cleaned finpartition. -/
structure DegreeFormWitness {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ε d : ℚ) (m₀ M : ℕ) where
  ordinaryParts : ℕ
  clusterSize : ℕ
  exceptional : Finset (Fin n)
  partition : Finpartition ((Finset.univ : Finset (Fin n)) \ exceptional)
  graph : SimpleGraph (Fin n)
  graph_decidable : DecidableRel graph.Adj
  loss : ℕ
  ordinaryParts_pos : 0 < ordinaryParts
  five_ordinaryParts_le_host : 5 * ordinaryParts ≤ n
  twice_requested_le_ordinary : 2 * m₀ ≤ ordinaryParts
  clusterSize_pos : 0 < clusterSize
  clusterSize_le_average : clusterSize ≤ n / ordinaryParts
  discardedParts_lt :
    ((ordinaryParts - #partition.parts : ℕ) : ℝ) <
      cleanupFraction ε * (ordinaryParts : ℝ)
  trim_lt :
    ((n / ordinaryParts - clusterSize : ℕ) : ℝ) <
      cleanupFraction ε * ((n / ordinaryParts + 1 : ℕ) : ℝ) + 1
  lower_parts : m₀ ≤ #partition.parts
  cleaned_le_ordinary : #partition.parts ≤ ordinaryParts
  upper_parts : ordinaryParts ≤ M
  equal_clusters : ∀ W ∈ partition.parts, #W = clusterSize
  exceptional_card : #exceptional = n - #partition.parts * clusterSize
  graph_le : graph ≤ G
  no_intra_edges : ∀ i : {W // W ∈ partition.parts},
    ∀ ⦃x y⦄, x ∈ i.1 → y ∈ i.1 → ¬graph.Adj x y
  pair_uniform : ∀ i j : {W // W ∈ partition.parts},
    @SimpleGraph.IsUniform _ ℚ _ _ graph graph_decidable ε i.1 j.1
  pair_density : ∀ i j : {W // W ∈ partition.parts},
    @SimpleGraph.edgeDensity _ graph graph_decidable i.1 j.1 = 0 ∨
      d < @SimpleGraph.edgeDensity _ graph graph_decidable i.1 j.1
  respects_reduced : EdgesRespectReducedGraph
    (partitionAssignment exceptional partition) graph
    (regularityReducedGraph G
      (fun i : {W // W ∈ partition.parts} => i.1) ε d)
  degree_loss : @DegreeLossAtMost _ _ G graph _ graph_decidable loss
  loss_eq : loss = explicitDegreeLoss ε d ordinaryParts clusterSize
    (n / ordinaryParts + 1)

/-- **Unconditional degree-form regularity lemma.**  Once the explicit
threshold is met, every finite graph has the exact cleaned output consumed by
`ZhaoStability`: equal clusters, a spanning subgraph, regular zero-or-dense
pairs, reduced-graph compatibility, and pointwise degree loss. -/
theorem exists_degreeFormWitness {ε d : ℚ} (hε : 0 < ε) (hd : 0 < d)
    (m₀ n : ℕ) (hn : degreeFormThreshold ε m₀ ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Nonempty (DegreeFormWitness G ε d m₀ (degreeFormBound ε m₀)) := by
  classical
  let η := ordinaryError ε
  let q := cleanupFraction ε
  let l := requestedParts m₀
  let M := degreeFormBound ε m₀
  have hηpos : 0 < η := ordinaryError_pos hε
  have hqpos : 0 < q := cleanupFraction_pos hε
  have hlM : l ≤ M := by
    exact SzemerediRegularity.le_bound η l
  have hMn : M ≤ n := by
    apply le_trans (Nat.le_mul_of_pos_left M (by decide : 0 < 5))
    simpa [degreeFormThreshold, M] using hn
  have hln : l ≤ n := hlM.trans hMn
  have hln' : l ≤ Fintype.card (Fin n) := by simpa using hln
  obtain ⟨P, hequip, hKlower, hKupper, hreg⟩ :=
    szemeredi_regularity G hηpos hln'
  let K := #P.parts
  have hKpos : 0 < K := by
    have hlpos : 0 < l := by simp [l, requestedParts]
    exact hlpos.trans_le hKlower
  have hfiveK : 5 * K ≤ n := by
    calc
      5 * K ≤ 5 * M := Nat.mul_le_mul_left 5 hKupper
      _ ≤ n := by simpa [degreeFormThreshold, M] using hn
  have hfiveAvg : 5 ≤ n / K := by
    rw [Nat.le_div_iff_mul_le hKpos]
    exact hfiveK
  let r := ⌈q * (((n / K) + 1 : ℕ) : ℝ)⌉₊
  have hnum := cleanup_numerics hε hfiveAvg
  change
    q * (((n / K) + 1 : ℕ) : ℝ) ≤ (r : ℝ) ∧
      r < n / K ∧
      n / K + 1 < 2 * (n / K - r) ∧
      ((((n / K) + 1 : ℕ) : ℝ) * η ≤ ((n / K - r : ℕ) : ℝ)) ∧
      ((((n / K) + 1 : ℕ) : ℝ) * η ≤
        ((n / K - r : ℕ) : ℝ) * (ε : ℝ)) at hnum
  obtain ⟨E, Q, hbad, hQcard, hEcard, hQspec⟩ :=
    Finpartition.IsUniform.exists_degree_cleanup_partition_fin
      P hequip hreg hηpos.le hqpos
        (by simpa [η, q] using ordinaryError_le_cleanup_sq ε)
        hnum.1 hnum.2.1
  let m := n / K - r
  have hchoose : ∀ i : {W // W ∈ Q.parts},
      ∃ U ∈ P.parts \ P.badClusters G η q,
        i.1 ⊆ U \ P.upperBadVertices G η q U ∧
        (#(P.irregularPairsFrom G η U) : ℝ) ≤ q * (#P.parts : ℝ) ∧
        ∀ x ∈ i.1,
          (#(P.upperAtypicalPartnersAt G η U x) : ℝ) ≤ q * (#P.parts : ℝ) := by
    intro i
    exact (hQspec i.1 i.2).2
  choose source hsource using hchoose
  have hsourceFull : ∀ i : {W // W ∈ Q.parts},
      i.1.card = m ∧
      source i ∈ P.parts \ P.badClusters G η q ∧
      i.1 ⊆ source i \ P.upperBadVertices G η q (source i) ∧
      (#(P.irregularPairsFrom G η (source i)) : ℝ) ≤ q * (#P.parts : ℝ) ∧
      ∀ x ∈ i.1,
        (#(P.upperAtypicalPartnersAt G η (source i) x) : ℝ) ≤
          q * (#P.parts : ℝ) := by
    intro i
    exact ⟨by simpa [m, K] using (hQspec i.1 i.2).1, hsource i⟩
  have hsourceSimple : ∀ i : {W // W ∈ Q.parts},
      i.1.card = m ∧ source i ∈ P.parts ∧ i.1 ⊆ source i := by
    intro i
    exact ⟨(hsourceFull i).1,
      (Finset.mem_sdiff.mp (hsourceFull i).2.1).1,
      (hsourceFull i).2.2.1.trans Finset.sdiff_subset⟩
  have hsourceInj : Function.Injective source := by
    intro i j hs
    by_contra hij
    have hijval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hdj : Disjoint i.1 j.1 := Q.disjoint i.2 j.2 hijval
    have hUnionSub : i.1 ∪ j.1 ⊆ source i := by
      apply Finset.union_subset
      · exact (hsourceSimple i).2.2
      · rw [hs]
        exact (hsourceSimple j).2.2
    have hUnionCard : #(i.1 ∪ j.1) = 2 * m := by
      rw [Finset.card_union_of_disjoint hdj, (hsourceSimple i).1,
        (hsourceSimple j).1]
      omega
    have hSourceUpper : #(source i) ≤ n / K + 1 := by
      simpa [K] using hequip.card_part_le_average_add_one (hsourceSimple i).2.1
    have hTwoM : 2 * m ≤ n / K + 1 := by
      rw [← hUnionCard]
      exact (Finset.card_le_card hUnionSub).trans hSourceUpper
    have hTooLarge : n / K + 1 < 2 * m := by
      simpa [m] using hnum.2.2.1
    omega
  have hlarge : ((((n / K) + 1 : ℕ) : ℝ) * η ≤ (m : ℝ)) := by
    simpa [m] using hnum.2.2.2.1
  have hscale : ((((n / K) + 1 : ℕ) : ℝ) * η ≤
      (m : ℝ) * (ε : ℝ)) := by
    simpa [m] using hnum.2.2.2.2
  let H := cleanedGraph G E Q source η d
  let loss := explicitDegreeLoss ε d K m (n / K + 1)
  have hbad2 : 2 * #(P.badClusters G η q) < K := by
    have hqbound : q ≤ (1 : ℝ) / 64 := by
      simpa [q] using cleanupFraction_le_one_div ε
    have hKR : 0 < (K : ℝ) := by exact_mod_cast hKpos
    have hbad' : (#(P.badClusters G η q) : ℝ) < q * K := by
      simpa [η, q, K] using hbad
    have hqK : q * (K : ℝ) ≤ ((1 : ℝ) / 64) * K :=
      mul_le_mul_of_nonneg_right hqbound hKR.le
    have hbhalf : (#(P.badClusters G η q) : ℝ) < (K : ℝ) / 2 := by
      exact (hbad'.trans_le hqK).trans (by nlinarith)
    have h2R : (((2 * #(P.badClusters G η q) : ℕ) : ℕ) : ℝ) < (K : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h2R
  have htwom₀K : 2 * m₀ ≤ K := by
    exact (le_max_right 1 (2 * m₀)).trans hKlower
  have hlowerClean : m₀ ≤ #Q.parts := by
    rw [hQcard]
    change m₀ ≤ K - #(P.badClusters G η q)
    omega
  have hcleanLe : #Q.parts ≤ K := by
    rw [hQcard]
    exact Nat.sub_le _ _
  have hEexact : #E = n - #Q.parts * m := by
    rw [hEcard, hQcard]
  have hdegree : DegreeLossAtMost G H loss := by
    apply degree_loss_of_cleanup hε hd P hequip E Q source m hsourceInj
    · simpa [η, q] using hsourceFull
    · simpa [η, K] using hlarge
  refine ⟨{
    ordinaryParts := K
    clusterSize := m
    exceptional := E
    partition := Q
    graph := H
    graph_decidable := inferInstance
    loss := loss
    ordinaryParts_pos := hKpos
    five_ordinaryParts_le_host := hfiveK
    twice_requested_le_ordinary := htwom₀K
    clusterSize_pos := by
      dsimp [m]
      exact Nat.sub_pos_of_lt hnum.2.1
    clusterSize_le_average := by
      dsimp [m]
      exact Nat.sub_le _ _
    discardedParts_lt := by
      have hbadC : P.badClusters G η q ⊆ P.parts := Finset.filter_subset _ _
      have hbadle : #(P.badClusters G η q) ≤ K := by
        simpa [K] using Finset.card_le_card hbadC
      have heq : K - #Q.parts = #(P.badClusters G η q) := by
        rw [hQcard]
        omega
      rw [heq]
      simpa [q, K] using hbad
    trim_lt := by
      have hrle : r ≤ n / K := hnum.2.1.le
      have hceil : (r : ℝ) <
          q * (((n / K) + 1 : ℕ) : ℝ) + 1 := by
        exact Nat.ceil_lt_add_one
          (mul_nonneg hqpos.le (Nat.cast_nonneg _))
      rw [show n / K - m = r by
        dsimp [m]
        omega]
      simpa [q, K] using hceil
    lower_parts := hlowerClean
    cleaned_le_ordinary := hcleanLe
    upper_parts := by
      simpa [K, M, degreeFormBound, η, l] using hKupper
    equal_clusters := ?_
    exceptional_card := hEexact
    graph_le := cleanedGraph_le G E Q source η d
    no_intra_edges := ?_
    pair_uniform := ?_
    pair_density := ?_
    respects_reduced := ?_
    degree_loss := hdegree
    loss_eq := rfl }⟩
  · intro W hW
    exact (hsourceFull ⟨W, hW⟩).1
  · intro i x y hx hy hxy
    have hh := (cleanedGraph_adj_on_clusters_iff
      G E Q source η d i i hx hy).mp hxy
    exact hh.2.1 rfl
  · intro i j
    exact cleanedGraph_pair_uniform hε P hequip E Q source m r hsourceSimple
      (by simpa [η, K] using hlarge) (by simpa [η, K] using hscale) rfl i j
  · intro i j
    exact cleanedGraph_pair_density E Q source i j
  · exact cleanedGraph_respects_reduced hε P hequip E Q source m r hsourceSimple
      (by simpa [η, K] using hlarge) (by simpa [η, K] using hscale) rfl

/-- Threshold/existence form, with no graph-side premise other than finiteness. -/
theorem degreeFormRegularity {ε d : ℚ} (hε : 0 < ε) (hd : 0 < d)
    (m₀ : ℕ) :
    ∃ N M : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      [DecidableRel G.Adj] → Nonempty (DegreeFormWitness G ε d m₀ M) := by
  refine ⟨degreeFormThreshold ε m₀, degreeFormBound ε m₀, ?_⟩
  intro n hn G _
  exact exists_degreeFormWitness hε hd m₀ n hn G

/-- The even-host specialization used verbatim by Zhao's stability argument. -/
theorem exists_evenHostDegreeFormWitness {ε d : ℚ} (hε : 0 < ε) (hd : 0 < d)
    (m₀ n : ℕ) (hn : degreeFormThreshold ε m₀ ≤ 2 * n)
    (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj] :
    Nonempty (DegreeFormWitness G ε d m₀ (degreeFormBound ε m₀)) :=
  exists_degreeFormWitness hε hd m₀ (2 * n) hn G

#print axioms exists_degreeFormWitness
#print axioms degreeFormRegularity
#print axioms exists_evenHostDegreeFormWitness

end Erdos547b.ZhaoDegreeForm

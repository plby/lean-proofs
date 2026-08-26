import ErdosProblems.Erdos118.Ordinal
import ErdosProblems.Erdos118.Imported591.PieceIndiv
import ErdosProblems.Erdos118.Imported591.StrongIteration
import ErdosProblems.Erdos118.Imported591.GlobalIndiv

/-!
# The uniform small-neighborhood case

This proves a sufficient condition for a full independent copy. It does not
assume or assert the still missing positive-three partition theorem.
The countable fusion input is supplied by an explicit identity-reindexing
step; no endpoint thinning hypothesis is left as an argument.
-/

open Set Ordinal

namespace Erdos118.BoundedNeighborhoods

open Schipperus.K4Core StrongIteration

variable {B Y X : Type}
variable [LinearOrder B] [LinearOrder Y] [Nonempty Y] [LinearOrder X]

/-- Removing a small neighborhood in each reservoir preserves the whole
index set. Only the selected reservoir also loses a bounded initial segment. -/
theorem step_of_small_neighborhoods
    (hind : FinitelyIndivisible Y)
    (hinit : ∀ a : Y, ¬ Large Y (Set.Iic a))
    (G : SimpleGraph X) (hsmall : ∀ x, ¬ Large Y {z | G.Adj x z}) :
    StepOracle (B := B) (Y := Y) G := by
  classical
  intro A F mu _
  let a : Y := Classical.arbitrary Y
  let x : X := A.embedding mu a
  let N : B → Set Y := fun b ↦ {y | G.Adj x (A.embedding b y)}
  have hN (b : B) : ¬ Large Y (N b) := by
    rintro ⟨f⟩
    apply hsmall x
    refine ⟨OrderEmbedding.ofStrictMono
      (fun y ↦ ⟨A.embedding b (f y), (f y).2⟩) ?_⟩
    intro y z hyz
    exact (A.embedding b).strictMono (f.strictMono hyz)
  let Q : B → Set Y := fun b ↦
    if b = mu then (Set.univ \ N b) \ Set.Iic a else Set.univ \ N b
  have hQ (b : B) : Large Y (Q b) := by
    have hbase : Large Y (Set.univ \ N b) :=
      Large.diff_of_not_large hind Large.univ (hN b)
    by_cases hb : b = mu
    · simpa [Q, hb] using Large.diff_of_not_large hind hbase (hinit a)
    · simpa [Q, hb] using hbase
  let keep (b : B) : Y ↪o Q b := Classical.choice (hQ b)
  have keep_not_adj (b : B) (y : Y) :
      ¬ G.Adj x (A.embedding b (keep b y)) := by
    have hy := (keep b y).2
    by_cases hb : b = mu
    · have hmem : (keep b y : Y) ∈ (Set.univ \ N b) \ Set.Iic a := by
        simpa [Q, hb] using hy
      exact hmem.1.2
    · have hmem : (keep b y : Y) ∈ Set.univ \ N b := by
        simpa [Q, hb] using hy
      exact hmem.2
  let nextEmb (b : B) : Y ↪o X :=
    ((keep b).trans (OrderEmbedding.subtype (Q b))).trans (A.embedding b)
  let next : BlockFamily B Y X :=
    { embedding := nextEmb
      separated := by
        intro b c hbc y z
        exact A.separated hbc (keep b y) (keep c z) }
  refine ⟨
    { point := x
      reindex := OrderEmbedding.id B
      fixes := by intro b _; rfl
      point_mem := ⟨a, rfl⟩
      next := next
      next_sub := by intro b y; exact ⟨keep b y, rfl⟩
      not_adj := keep_not_adj
      point_below := ?_ }⟩
  intro y
  have hy : (keep mu y : Y) ∈ (Set.univ \ N mu) \ Set.Iic a := by
    simpa [Q] using (keep mu y).2
  exact (A.embedding mu).strictMono (lt_of_not_ge hy.2)

/-- Exact order type obtained by countable fusion under the uniform bound. -/
theorem exists_independent_of_small_neighborhoods
    [WellFoundedLT B] [Countable B] [Nonempty B] [WellFoundedLT X]
    (hind : FinitelyIndivisible Y)
    (hinit : ∀ a : Y, ¬ Large Y (Set.Iic a))
    (G : SimpleGraph X) (hsmall : ∀ x, ¬ Large Y {z | G.Adj x z})
    (start : BlockFamily B Y X) :
    ∃ S : Set X, typeLT S = ω * typeLT B ∧ G.IsIndepSet S := by
  obtain ⟨S, htype, hfree⟩ := exists_set_type_not_adj G
    (step_of_small_neighborhoods hind hinit G hsmall) start
  exact ⟨S, htype, hfree⟩

section OrdinalBounds

variable [WellFoundedLT B] [WellFoundedLT Y] [WellFoundedLT X]

/-- The ordinal product identity supplies separated copies of the reservoir. -/
noncomputable def blocks_of_type_mul
    (htype : (typeLT Y) * (typeLT B) = typeLT X) : BlockFamily B Y X := by
  let L := B ×ₗ Y
  have hL : typeLT L = typeLT X := by
    change Ordinal.type (Prod.Lex ((· < ·) : B → B → Prop)
      ((· < ·) : Y → Y → Prop)) = _
    rw [Ordinal.type_prod_lex, htype]
  let i : ((· < ·) : L → L → Prop) ≃r ((· < ·) : X → X → Prop) :=
    Classical.choice (Ordinal.type_eq.mp hL)
  let e : L ↪o X := OrderEmbedding.ofStrictMono i
    (fun _ _ h ↦ i.map_rel_iff.mpr h)
  refine
    { embedding := fun b ↦ OrderEmbedding.ofStrictMono
        (fun y ↦ e (toLex (b, y))) ?_
      separated := ?_ }
  · intro y z hyz
    exact e.strictMono (Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hyz⟩))
  · intro b c hbc y z
    exact e.strictMono (Prod.Lex.lt_iff.mpr (Or.inl hbc))

omit [Nonempty Y] in
/-- An ordinal bound is sufficient for the embedding-based smallness condition. -/
theorem not_large_of_type_lt {S : Set X} (h : typeLT S < typeLT Y) :
    ¬ Large Y S := by
  rintro ⟨e⟩
  exact (not_le_of_gt h) (Ordinal.type_le_iff'.mpr ⟨e.ltEmbedding⟩)

omit [Nonempty Y] in
/-- Pulling back a graph along an order embedding cannot enlarge neighborhoods. -/
theorem comap_neighborhood_type_le (G : SimpleGraph X) (e : Y ↪o X) (y : Y) :
    typeLT {z | (G.comap e).Adj y z} ≤ typeLT {z | G.Adj (e y) z} := by
  let f : {z | (G.comap e).Adj y z} ↪o {z | G.Adj (e y) z} :=
    OrderEmbedding.ofStrictMono (fun z ↦ ⟨e z, z.2⟩)
      (fun _ _ h ↦ e.strictMono h)
  exact Ordinal.type_le_iff'.mpr ⟨f.ltEmbedding⟩

end OrdinalBounds

noncomputable def reservoir (r : ℕ) : Ordinal.{0} := ω ^ (ω * (r : Ordinal))

theorem omega_mul_nat_lt_omega_sq (r : ℕ) :
    (ω : Ordinal.{0}) * (r : Ordinal) < ω ^ (2 : Ordinal) := by
  change (ω : Ordinal.{0}) * (r : Ordinal) < ω ^ ((2 : ℕ) : Ordinal)
  rw [Ordinal.opow_natCast, pow_two]
  exact mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 r) Ordinal.omega0_pos

theorem reservoir_mul_lambda (r : ℕ) : reservoir r * lambda = lambda := by
  rw [reservoir, lambda, ← Ordinal.opow_add,
    Ordinal.add_omega0_opow (omega_mul_nat_lt_omega_sq r)]

theorem omega_mul_lambda : (ω : Ordinal.{0}) * lambda = lambda := by
  have h : (1 : Ordinal.{0}) < ω ^ (2 : Ordinal) := by
    exact lt_of_lt_of_le Ordinal.one_lt_omega0
      (by simpa using (le_of_lt (omega_mul_nat_lt_omega_sq 1)))
  rw [lambda, ← Ordinal.opow_one_add, Ordinal.add_omega0_opow h]

/-- A proved sufficient condition at the precise counterexample ordinal.
The uniform neighborhood hypothesis is not inferred from triangle-freeness. -/
theorem exists_independent_lambda_of_bounded_neighborhoods
    (G : SimpleGraph lambda.ToType) (r : ℕ) (hr : 0 < r)
    (hbound : ∀ x, typeLT {z | G.Adj x z} < reservoir r) :
    ∃ S : Set lambda.ToType, typeLT S = lambda ∧ G.IsIndepSet S := by
  let Y := (reservoir r).ToType
  let : Nonempty Y := Ordinal.nonempty_toType_iff.mpr
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
  let : Nonempty lambda.ToType := Ordinal.nonempty_toType_iff.mpr
    (ne_of_gt (Ordinal.omega0_pos.trans omega_lt_lambda))
  let : Countable lambda.ToType := lambda_countable
  have hind : FinitelyIndivisible Y :=
    Schipperus.PieceIndiv.omegaPower_finitelyIndivisible_of_le
      Erdos590.erdos_590 (ω * (r : Ordinal)) r (Ordinal.type_toType _) le_rfl
  have hlim : Order.IsSuccLimit (typeLT Y) := by
    rw [Ordinal.type_toType]
    apply Ordinal.isSuccLimit_opow Ordinal.one_lt_omega0
    exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
      (by exact_mod_cast hr)
  have hsmall (x : lambda.ToType) : ¬ Large Y {z | G.Adj x z} := by
    apply not_large_of_type_lt
    simpa only [Y, Ordinal.type_toType] using hbound x
  have hprod : (typeLT Y) * (typeLT lambda.ToType) = typeLT lambda.ToType := by
    simpa only [Y, Ordinal.type_toType] using reservoir_mul_lambda r
  obtain ⟨S, hS, hfree⟩ := exists_independent_of_small_neighborhoods hind
    (Schipperus.PieceIndiv.not_large_Iic_of_isSuccLimit hlim) G hsmall
    (blocks_of_type_mul hprod)
  exact ⟨S, by simpa only [Ordinal.type_toType, omega_mul_lambda] using hS, hfree⟩

/-- Absence of a full independent copy forces the high-degree vertices to
retain full order type, for every finite reservoir bound. -/
theorem high_degree_set_type (G : SimpleGraph lambda.ToType)
    (hno : ¬ ∃ S : Set lambda.ToType, G.IsIndepSet S ∧ typeLT S = lambda)
    (r : ℕ) (hr : 0 < r) :
    typeLT {x | reservoir r ≤ typeLT {z | G.Adj x z}} = lambda := by
  classical
  let L : Set lambda.ToType := {x | typeLT {z | G.Adj x z} < reservoir r}
  have hL : ¬ Large lambda.ToType L := by
    rintro ⟨e⟩
    let f : lambda.ToType ↪o lambda.ToType :=
      e.trans (OrderEmbedding.subtype L)
    have hbound (x : lambda.ToType) :
        typeLT {z | (G.comap f).Adj x z} < reservoir r := by
      exact (comap_neighborhood_type_le G f x).trans_lt (e x).2
    obtain ⟨S, htype, hfree⟩ :=
      exists_independent_lambda_of_bounded_neighborhoods (G.comap f) r hr hbound
    obtain ⟨g, hg⟩ :=
      (exists_independent_type_iff (G.comap f) lambda).mp ⟨S, hfree, htype⟩
    apply hno
    apply (exists_independent_type_iff G lambda).mpr
    exact ⟨g.trans f, hg⟩
  have hind : FinitelyIndivisible lambda.ToType := by
    have heq : Positive.GlobalIndiv.lambda = lambda :=
      lambda_eq_natural_inner_power.symm
    rw [← heq]
    exact Positive.GlobalIndiv.lambda_finitelyIndivisible
  have hhigh : Large lambda.ToType (Set.univ \ L) :=
    Large.diff_of_not_large hind Large.univ hL
  have htype := Schipperus.K4Core.typeLT_eq_of_large hhigh
  have hset : Set.univ \ L = {x | reservoir r ≤ typeLT {z | G.Adj x z}} := by
    ext x
    simp [L]
  rw [hset, Ordinal.type_toType] at htype
  exact htype

end Erdos118.BoundedNeighborhoods

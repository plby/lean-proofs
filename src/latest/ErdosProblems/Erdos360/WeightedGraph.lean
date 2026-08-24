import ErdosProblems.Erdos360.FiberCoherence

/-!
# Weighted graph-sum cells for the affine-alignment step of Erdős 360

This file proves the layer-cake reduction and its unweighted incident-cell
bound, then packages controlled affine alignment for the product fibres.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Pair-sum cells of the graph of `x` above `A`. -/
def graphPairCells (A : Finset ℕ) (x : ℕ → G) : Finset (ℕ × G) :=
  (A.product A).image fun p => (p.1 + p.2, x p.1 + x p.2)

/-- Cells having a representation with one endpoint in `T` and the other in
`A`.  Commutativity means that one orientation suffices. -/
def incidentGraphPairCells (A T : Finset ℕ) (x : ℕ → G) : Finset (ℕ × G) :=
  (T.product A).image fun p => (p.1 + p.2, x p.1 + x p.2)

/-- The weight of a cell is the largest endpoint weight occurring in any of
its representations. -/
def graphCellWeight (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ)
    (c : ℕ × G) : ℕ :=
  ((A.product A).filter fun p =>
      (p.1 + p.2, x p.1 + x p.2) = c).sup fun p => max (w p.1) (w p.2)

lemma mem_graphPairCells {A : Finset ℕ} {x : ℕ → G} {c : ℕ × G} :
    c ∈ graphPairCells A x ↔
      ∃ a ∈ A, ∃ b ∈ A, c = (a + b, x a + x b) := by
  rw [graphPairCells, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hp
    exact ⟨p.1, hp, p.2, hq, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

lemma mem_incidentGraphPairCells {A T : Finset ℕ} {x : ℕ → G}
    {c : ℕ × G} :
    c ∈ incidentGraphPairCells A T x ↔
      ∃ a ∈ T, ∃ b ∈ A, c = (a + b, x a + x b) := by
  rw [incidentGraphPairCells, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hp
    exact ⟨p.1, hp, p.2, hq, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

lemma incidentGraphPairCells_subset (A T : Finset ℕ) (x : ℕ → G)
    (hTA : T ⊆ A) : incidentGraphPairCells A T x ⊆ graphPairCells A x := by
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_incidentGraphPairCells.mp hc
  exact mem_graphPairCells.mpr ⟨a, hTA ha, b, hb, rfl⟩

lemma image_fst_incidentGraphPairCells
    (A T : Finset ℕ) (x : ℕ → G) :
    (incidentGraphPairCells A T x).image Prod.fst = T + A := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨c, hc, hck⟩ := Finset.mem_image.mp hk
    obtain ⟨a, ha, b, hb, hcEq⟩ := mem_incidentGraphPairCells.mp hc
    subst c
    exact Finset.mem_add.mpr ⟨a, ha, b, hb, by simpa using hck⟩
  · intro hk
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hk
    apply Finset.mem_image.mpr
    refine ⟨(a + b, x a + x b), ?_, rfl⟩
    exact mem_incidentGraphPairCells.mpr ⟨a, ha, b, hb, rfl⟩

lemma card_add_le_card_incidentGraphPairCells
    (A T : Finset ℕ) (x : ℕ → G) :
    (T + A).card ≤ (incidentGraphPairCells A T x).card := by
  rw [← image_fst_incidentGraphPairCells A T x]
  exact Finset.card_image_le

/-- For threshold sets of size at most roughly two thirds of `A`, the
required `5/2` estimate is just the ordered-group sumset inequality; no
affine-failure input is needed. -/
lemma five_card_le_two_card_incident_of_three_card_le
    (A T : Finset ℕ) (x : ℕ → G)
    (hA : A.Nonempty) (hT : T.Nonempty)
    (hsmallT : 3 * T.card ≤ 2 * (A.card - 1)) :
    5 * T.card ≤ 2 * (incidentGraphPairCells A T x).card := by
  have hadd : T.card + A.card - 1 ≤ (T + A).card :=
    cauchy_davenport_add_of_linearOrder_isCancelAdd hT hA
  have hinc := card_add_le_card_incidentGraphPairCells A T x
  omega

/-- A layer of positive cell weight is exactly the set of cells incident to
the corresponding layer of positive vertex weight. -/
lemma filter_graphCellWeight_eq_incident
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (t : ℕ) :
    (graphPairCells A x).filter (fun c => t < graphCellWeight A x w c) =
      incidentGraphPairCells A (A.filter fun a => t < w a) x := by
  classical
  ext c
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hc, hcw⟩
    rw [graphCellWeight, Finset.lt_sup_iff] at hcw
    obtain ⟨p, hp, hweight⟩ := hcw
    have hp' := Finset.mem_filter.mp hp
    have hpA := Finset.mem_product.mp hp'.1
    have hcEq := hp'.2
    rw [lt_max_iff] at hweight
    rcases hweight with hleft | hright
    · exact mem_incidentGraphPairCells.mpr
        ⟨p.1, Finset.mem_filter.mpr ⟨hpA.1, hleft⟩,
          p.2, hpA.2, hcEq.symm⟩
    · exact mem_incidentGraphPairCells.mpr
        ⟨p.2, Finset.mem_filter.mpr ⟨hpA.2, hright⟩,
          p.1, hpA.1, by simpa [add_comm] using hcEq.symm⟩
  · intro hc
    have hcGraph : c ∈ graphPairCells A x :=
      incidentGraphPairCells_subset A (A.filter fun a => t < w a) x
        (Finset.filter_subset _ _) hc
    refine ⟨hcGraph, ?_⟩
    obtain ⟨a, ha, b, hb, hcEq⟩ := mem_incidentGraphPairCells.mp hc
    have ha' := Finset.mem_filter.mp ha
    rw [graphCellWeight, Finset.lt_sup_iff]
    refine ⟨(a, b), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha'.1, hb⟩,
        hcEq.symm⟩
    · exact ha'.2.trans_le (le_max_left _ _)

lemma graphCellWeight_le
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (M : ℕ)
    (hmax : ∀ a ∈ A, w a ≤ M) (c : ℕ × G) :
    graphCellWeight A x w c ≤ M := by
  apply Finset.sup_le
  intro p hp
  have hpA := (Finset.mem_filter.mp hp).1
  exact max_le (hmax p.1 (Finset.mem_product.mp hpA).1)
    (hmax p.2 (Finset.mem_product.mp hpA).2)

private lemma generic_sum_card_filter_lt_eq_sum
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (M : ℕ)
    (hf : ∀ a ∈ S, f a ≤ M) :
    (∑ t ∈ Finset.range M, (S.filter fun a => t < f a).card) =
      ∑ a ∈ S, f a := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range M).filter (fun t => t < f a) =
      Finset.range (f a) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro ht
      exact ⟨ht.trans_le (hf a ha), ht⟩
  rw [hfilter]
  simp

/-- Exact weighted/unweighted layer-cake identity. -/
theorem weighted_graph_cells_layerCake
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (M : ℕ)
    (hmax : ∀ a ∈ A, w a ≤ M) :
    (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) =
      ∑ t ∈ Finset.range M,
        (incidentGraphPairCells A (A.filter fun a => t < w a) x).card := by
  rw [← generic_sum_card_filter_lt_eq_sum (graphPairCells A x)
    (graphCellWeight A x w) M
      (fun c _ => graphCellWeight_le A x w M hmax c)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [filter_graphCellWeight_eq_incident]

/-- Consequently the desired weighted `5/2` inequality follows from the
unweighted incident-cell bound at every nonempty threshold. -/
theorem weighted_graph_bound_of_incident_bounds
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (M : ℕ)
    (hmax : ∀ a ∈ A, w a ≤ M)
    (hincident : ∀ t ∈ Finset.range M,
      5 * (A.filter fun a => t < w a).card ≤
        2 * (incidentGraphPairCells A (A.filter fun a => t < w a) x).card) :
    5 * (∑ a ∈ A, w a) ≤
      2 * ∑ c ∈ graphPairCells A x, graphCellWeight A x w c := by
  have hwLayer := sum_card_filter_lt_eq_sum A w M hmax
  have hsum := Finset.sum_le_sum hincident
  rw [← Finset.mul_sum, hwLayer] at hsum
  rw [weighted_graph_cells_layerCake A x w M hmax]
  simpa only [Finset.mul_sum] using hsum

/-- Only the high-density threshold case is genuinely new.  This wrapper
discharges empty and at-most-two-thirds layers automatically. -/
theorem weighted_graph_bound_of_high_incident_bounds
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (M : ℕ)
    (hA : A.Nonempty) (hmax : ∀ a ∈ A, w a ≤ M)
    (hhigh : ∀ t ∈ Finset.range M,
      2 * (A.card - 1) < 3 * (A.filter fun a => t < w a).card →
      5 * (A.filter fun a => t < w a).card ≤
        2 * (incidentGraphPairCells A (A.filter fun a => t < w a) x).card) :
    5 * (∑ a ∈ A, w a) ≤
      2 * ∑ c ∈ graphPairCells A x, graphCellWeight A x w c := by
  apply weighted_graph_bound_of_incident_bounds A x w M hmax
  intro t ht
  let T := A.filter fun a => t < w a
  by_cases hT : T.Nonempty
  · by_cases hdense : 2 * (A.card - 1) < 3 * T.card
    · exact hhigh t ht (by simpa [T] using hdense)
    · exact five_card_le_two_card_incident_of_three_card_le A T x hA hT
        (by omega)
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [T, hTempty, incidentGraphPairCells]

/-! ## A graph-valued `3k-4` induction

The following generalized affine predicate avoids division by the common
difference.  It is the convenient induction invariant when deleting the
largest first coordinate changes the gcd of the support.
-/

def GeneralizedAffineOn (A : Finset ℕ) (x : ℕ → G) (p q : ℕ) : Prop :=
  ∃ u v : G, ∀ a ∈ A, ∃ k : ℤ,
    (a : ℤ) = (p : ℤ) + k * ((q : ℤ) - p) ∧ x a = k • u + v

lemma preservesPairSums_of_generalizedAffineOn
    {A : Finset ℕ} {x : ℕ → G} {p q : ℕ} (hpq : p < q)
    (haff : GeneralizedAffineOn A x p q) :
    PreservesPairSums A x := by
  obtain ⟨u, v, haff⟩ := haff
  intro a ha b hb c hc z hz habcz
  obtain ⟨ka, hka, hxa⟩ := haff a ha
  obtain ⟨kb, hkb, hxb⟩ := haff b hb
  obtain ⟨kc, hkc, hxc⟩ := haff c hc
  obtain ⟨kz, hkz, hxz⟩ := haff z hz
  have hdpos : (0 : ℤ) < (q : ℤ) - p := by omega
  have hcoeff : ka + kb = kc + kz := by
    have hcast : (a : ℤ) + b = c + z := by exact_mod_cast habcz
    rw [hka, hkb, hkc, hkz] at hcast
    have hmul : (ka + kb - (kc + kz)) * ((q : ℤ) - p) = 0 := by
      linear_combination hcast
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · omega
    · omega
  rw [hxa, hxb, hxc, hxz]
  calc
    ka • u + v + (kb • u + v) = (ka + kb) • u + (v + v) := by
      simp only [add_zsmul]
      abel
    _ = (kc + kz) • u + (v + v) := by rw [hcoeff]
    _ = kc • u + v + (kz • u + v) := by
      simp only [add_zsmul]
      abel

lemma generalizedAffineOn_of_ternaryGenerates
    {A : Finset ℕ} {x : ℕ → G} {p q : ℕ}
    (hpq : p < q) (hgen : TernaryGenerates A p q)
    (hpres : PreservesPairSums A x) :
    GeneralizedAffineOn A x p q := by
  let u : G := x q - x p
  let v : G := x p
  let C : Set ℕ := {a | a ∈ A ∧ ∃ k : ℤ,
    (a : ℤ) = (p : ℤ) + k * ((q : ℤ) - p) ∧ x a = k • u + v}
  have hpC : p ∈ C := by
    refine ⟨hgen.1, 0, ?_, ?_⟩
    · simp
    · simp [v]
  have hqC : q ∈ C := by
    refine ⟨hgen.2.1, 1, ?_, ?_⟩
    · simp
    · simp [u, v]
  have hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ z ∈ A,
      z + a = b + c → z ∈ C := by
    intro a ha b hb c hc z hz hrel
    obtain ⟨ka, hka, hxa⟩ := ha.2
    obtain ⟨kb, hkb, hxb⟩ := hb.2
    obtain ⟨kc, hkc, hxc⟩ := hc.2
    refine ⟨hz, kb + kc - ka, ?_, ?_⟩
    · have hcast : (z : ℤ) + a = b + c := by exact_mod_cast hrel
      rw [hka, hkb, hkc] at hcast
      linear_combination hcast
    · have hxrel : x z + x a = x b + x c :=
        hpres z hz a ha.1 b hb.1 c hc.1 hrel
      calc
        x z = (x z + x a) - x a := by abel
        _ = (x b + x c) - x a := by rw [hxrel]
        _ = (kb • u + v) + (kc • u + v) - (ka • u + v) := by
          rw [hxa, hxb, hxc]
        _ = (kb + kc - ka) • u + v := by
          simp only [add_zsmul, sub_zsmul]
          abel
  refine ⟨u, v, ?_⟩
  intro a ha
  exact (hgen.2.2 C (fun _ h => h.1) hpC hqC hclosed ha).2

lemma generalizedAffineOn_insert_of_relation
    {B : Finset ℕ} {x : ℕ → G} {m p q a r s : ℕ}
    (hpq : p < q) (haff : GeneralizedAffineOn B x p q)
    (ha : a ∈ B) (hr : r ∈ B) (hs : s ∈ B)
    (hnum : m + a = r + s) (hlab : x m + x a = x r + x s) :
    GeneralizedAffineOn (insert m B) x p q := by
  obtain ⟨u, v, haff⟩ := haff
  obtain ⟨ka, hka, hxa⟩ := haff a ha
  obtain ⟨kr, hkr, hxr⟩ := haff r hr
  obtain ⟨ks, hks, hxs⟩ := haff s hs
  let km : ℤ := kr + ks - ka
  have hkm : (m : ℤ) = (p : ℤ) + km * ((q : ℤ) - p) := by
    have hcast : (m : ℤ) + a = r + s := by exact_mod_cast hnum
    rw [hka, hkr, hks] at hcast
    dsimp only [km]
    linear_combination hcast
  have hxm : x m = km • u + v := by
    calc
      x m = (x m + x a) - x a := by abel
      _ = (x r + x s) - x a := by rw [hlab]
      _ = (kr • u + v) + (ks • u + v) - (ka • u + v) := by
        rw [hxa, hxr, hxs]
      _ = km • u + v := by
        dsimp only [km]
        simp only [add_zsmul, sub_zsmul]
        abel
  refine ⟨u, v, ?_⟩
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · exact ⟨km, hkm, hxm⟩
  · exact haff z hz

def GraphProgressionStructured (A : Finset ℕ) (x : ℕ → G) : Prop :=
  ∃ p q : ℕ, p < q ∧ TernaryGenerates A p q ∧
    GeneralizedAffineOn A x p q

lemma graphProgressionStructured_preserves
    {A : Finset ℕ} {x : ℕ → G}
    (h : GraphProgressionStructured A x) : PreservesPairSums A x := by
  obtain ⟨p, q, hpq, -, haff⟩ := h
  exact preservesPairSums_of_generalizedAffineOn hpq haff

lemma image_fst_graphPairCells (A : Finset ℕ) (x : ℕ → G) :
    (graphPairCells A x).image Prod.fst = A + A := by
  simpa [graphPairCells, incidentGraphPairCells] using
    image_fst_incidentGraphPairCells A A x

private lemma graphPairCells_mono {A B : Finset ℕ} {x : ℕ → G}
    (hBA : B ⊆ A) : graphPairCells B x ⊆ graphPairCells A x := by
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_graphPairCells.mp hc
  exact mem_graphPairCells.mpr ⟨a, hBA ha, b, hBA hb, rfl⟩

private lemma graphTranslate_card (B : Finset ℕ) (x : ℕ → G) (m : ℕ) :
    (B.image fun a => (m + a, x m + x a)).card = B.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact Nat.add_left_cancel (congrArg Prod.fst hab)

/-- Balasubramanian--Pandey's graph-valued `3k-4` theorem, in the exact
ternary-generation form useful for the incident-cell argument. -/
theorem graphProgressionStructured_of_three_card_sub_four
    (A : Finset ℕ) (x : ℕ → G) (hcard : 3 ≤ A.card)
    (hsmall : (graphPairCells A x).card ≤ 3 * A.card - 4) :
    GraphProgressionStructured A x := by
  classical
  generalize hk : A.card = k at hcard hsmall ⊢
  induction k using Nat.strong_induction_on generalizing A with
  | h k ih =>
      by_cases hk3 : k = 3
      · have hkA : A.card = 3 := hk.trans hk3
        have hApos : 0 < A.card := by rw [hkA]; omega
        have hAne : A.Nonempty := Finset.card_pos.mp hApos
        have hproj : (A + A).card ≤ (graphPairCells A x).card := by
          rw [← image_fst_graphPairCells A x]
          exact Finset.card_image_le
        have hAAfive : 5 ≤ (A + A).card := by
          have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hAne hAne
          omega
        have hgraphFive : (graphPairCells A x).card = 5 := by omega
        have hprojFive : (A + A).card = 5 := by omega
        have hfstCard : ((graphPairCells A x).image Prod.fst).card =
            (graphPairCells A x).card := by
          rw [image_fst_graphPairCells, hprojFive, hgraphFive]
        have hfstInj := Finset.injOn_of_card_image_eq hfstCard
        have hpres : PreservesPairSums A x := by
          intro a ha b hb c hc z hz habcz
          let u : ℕ × G := (a + b, x a + x b)
          let v : ℕ × G := (c + z, x c + x z)
          have hu : u ∈ graphPairCells A x :=
            mem_graphPairCells.mpr ⟨a, ha, b, hb, rfl⟩
          have hv : v ∈ graphPairCells A x :=
            mem_graphPairCells.mpr ⟨c, hc, z, hz, rfl⟩
          have huv : u = v := hfstInj hu hv (by simpa [u, v] using habcz)
          exact congrArg Prod.snd huv
        have hgen := progressionTernaryGenerates_of_card_eq_three hkA hprojFive.le
        obtain ⟨p, q, hpq, htern⟩ := hgen
        exact ⟨p, q, hpq, htern,
          generalizedAffineOn_of_ternaryGenerates hpq htern hpres⟩
      have hk4 : 4 ≤ k := by omega
      have hApos : 0 < A.card := by rw [hk]; omega
      have hAne : A.Nonempty := Finset.card_pos.mp hApos
      let m := A.max' hAne
      let B := A.erase m
      have hmA : m ∈ A := A.max'_mem hAne
      have hBA : B ⊆ A := Finset.erase_subset _ _
      have hAeq : A = insert m B := (Finset.insert_erase hmA).symm
      have hBcard : B.card = k - 1 := by
        dsimp [B]
        rw [Finset.card_erase_of_mem hmA, hk]
      have hBcard3 : 3 ≤ B.card := by omega
      have hBlt : B.card < k := by omega
      have hBpos : 0 < B.card := by rw [hBcard]; omega
      have hBne : B.Nonempty := Finset.card_pos.mp hBpos
      have hmB : m ∉ B := Finset.notMem_erase _ _
      have hBmem_lt : ∀ {a}, a ∈ B → a < m := by
        intro a ha
        exact A.lt_max'_of_mem_erase_max' hAne ha
      by_cases hBstruct : GraphProgressionStructured B x
      · obtain ⟨p, q, hpq, hgen, haff⟩ := hBstruct
        by_cases hcollision : ∃ a ∈ B,
            (m + a, x m + x a) ∈ graphPairCells B x
        · obtain ⟨a, ha, hcell⟩ := hcollision
          obtain ⟨r, hr, s, hs, heq⟩ := mem_graphPairCells.mp hcell
          have hnum : m + a = r + s := congrArg Prod.fst heq
          have hlab : x m + x a = x r + x s := congrArg Prod.snd heq
          refine ⟨p, q, hpq, ?_, ?_⟩
          · rw [hAeq]
            exact ternaryGenerates_insert_of_relation hgen ha hr hs hnum
          · rw [hAeq]
            exact generalizedAffineOn_insert_of_relation hpq haff ha hr hs
              hnum hlab
        · push_neg at hcollision
          let T := B.image fun a => (m + a, x m + x a)
          have hdis : Disjoint (graphPairCells B x) T := by
            rw [Finset.disjoint_left]
            intro z hzB hzT
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzT
            exact hcollision a ha hzB
          let mm : ℕ × G := (m + m, x m + x m)
          have hmmB : mm ∉ graphPairCells B x := by
            intro hz
            obtain ⟨a, ha, b, hb, heq⟩ := mem_graphPairCells.mp hz
            have haLt := hBmem_lt ha
            have hbLt := hBmem_lt hb
            have := congrArg Prod.fst heq
            dsimp only [mm] at this
            omega
          have hmmT : mm ∉ T := by
            intro hz
            obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hz
            have haLt := hBmem_lt ha
            have := congrArg Prod.fst heq
            dsimp only [mm] at this
            omega
          let U := insert mm (graphPairCells B x ∪ T)
          have hUsub : U ⊆ graphPairCells A x := by
            intro z hz
            simp only [U, Finset.mem_insert, Finset.mem_union] at hz
            rcases hz with rfl | hzB | hzT
            · exact mem_graphPairCells.mpr ⟨m, hmA, m, hmA, rfl⟩
            · exact graphPairCells_mono hBA hzB
            · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzT
              exact mem_graphPairCells.mpr ⟨m, hmA, a, hBA ha, rfl⟩
          have hUcard : U.card =
              (graphPairCells B x).card + B.card + 1 := by
            dsimp only [U]
            rw [Finset.card_insert_of_notMem, Finset.card_union_of_disjoint hdis,
              graphTranslate_card]
            simp only [Finset.mem_union, not_or]
            exact ⟨hmmB, hmmT⟩
          have hBBproj : (B + B).card ≤ (graphPairCells B x).card := by
            rw [← image_fst_graphPairCells B x]
            exact Finset.card_image_le
          have hBBordinary : B.card + B.card - 1 ≤ (B + B).card :=
            cauchy_davenport_add_of_linearOrder_isCancelAdd hBne hBne
          have hUle := Finset.card_le_card hUsub
          omega
      · have hBBlarge : 3 * B.card - 3 ≤ (graphPairCells B x).card := by
          by_contra hnot
          have hBBsmall : (graphPairCells B x).card ≤ 3 * B.card - 4 := by omega
          exact hBstruct (ih B.card hBlt B rfl hBcard3 hBBsmall)
        let b := B.max' hBne
        let C := B.erase b
        have hbB : b ∈ B := B.max'_mem hBne
        have hbm : b < m := hBmem_lt hbB
        have hCB : C ⊆ B := Finset.erase_subset _ _
        have hCmem_lt : ∀ {a}, a ∈ C → a < b := by
          intro a ha
          exact B.lt_max'_of_mem_erase_max' hBne ha
        have hcellC : ∀ a ∈ C,
            (m + a, x m + x a) ∈ graphPairCells B x := by
          intro a ha
          by_contra hnot
          have haB := hCB ha
          have hab : a < b := hCmem_lt ha
          let ca : ℕ × G := (m + a, x m + x a)
          let cb : ℕ × G := (m + b, x m + x b)
          let cm : ℕ × G := (m + m, x m + x m)
          have hcbNot : cb ∉ graphPairCells B x := by
            intro hz
            obtain ⟨r, hr, s, hs, heq⟩ := mem_graphPairCells.mp hz
            have hrle : r ≤ b := Finset.le_max' B r hr
            have hsle : s ≤ b := Finset.le_max' B s hs
            have := congrArg Prod.fst heq
            dsimp only [cb] at this
            omega
          have hcmNot : cm ∉ graphPairCells B x := by
            intro hz
            obtain ⟨r, hr, s, hs, heq⟩ := mem_graphPairCells.mp hz
            have hrle : r ≤ b := Finset.le_max' B r hr
            have hsle : s ≤ b := Finset.le_max' B s hs
            have := congrArg Prod.fst heq
            dsimp only [cm] at this
            omega
          let U := insert cm (insert cb (insert ca (graphPairCells B x)))
          have hUsub : U ⊆ graphPairCells A x := by
            intro z hz
            simp only [U, Finset.mem_insert] at hz
            rcases hz with rfl | rfl | rfl | hzB
            · exact mem_graphPairCells.mpr ⟨m, hmA, m, hmA, rfl⟩
            · exact mem_graphPairCells.mpr ⟨m, hmA, b, hBA hbB, rfl⟩
            · exact mem_graphPairCells.mpr ⟨m, hmA, a, hBA haB, rfl⟩
            · exact graphPairCells_mono hBA hzB
          have hUcard : U.card = (graphPairCells B x).card + 3 := by
            dsimp only [U]
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem]
            · omega
            · simpa only [Finset.mem_insert, not_or] using
                (show cb ≠ ca ∧ cb ∉ graphPairCells B x by
                  refine ⟨?_, hcbNot⟩
                  intro heq
                  have := congrArg Prod.fst heq
                  dsimp only [cb, ca] at this
                  omega)
            · simpa only [Finset.mem_insert, not_or] using
                (show cm ≠ cb ∧ cm ≠ ca ∧ cm ∉ graphPairCells B x by
                  refine ⟨?_, ?_, hcmNot⟩ <;> intro heq
                  · have := congrArg Prod.fst heq
                    dsimp only [cm, cb] at this
                    omega
                  · have := congrArg Prod.fst heq
                    dsimp only [cm, ca] at this
                    omega)
          have hUle := Finset.card_le_card hUsub
          omega
        have htern : TernaryGenerates (insert m B) b m := by
          refine ⟨Finset.mem_insert_of_mem hbB, Finset.mem_insert_self _ _, ?_⟩
          intro D hD hbD hmD hclosed
          have hBDaux : ∀ e : ℕ, ∀ z ∈ B, b - z = e → z ∈ D := by
            intro e
            induction e using Nat.strong_induction_on with
            | h e ihe =>
                intro z hz hdist
                have hzb : z ≤ b := Finset.le_max' B z hz
                by_cases hzbEq : z = b
                · simpa [hzbEq] using hbD
                have hzC : z ∈ C := Finset.mem_erase.mpr ⟨hzbEq, hz⟩
                obtain ⟨r, hr, s, hs, heq⟩ :=
                  mem_graphPairCells.mp (hcellC z hzC)
                have hnum : m + z = r + s := congrArg Prod.fst heq
                have hrle : r ≤ b := Finset.le_max' B r hr
                have hsle : s ≤ b := Finset.le_max' B s hs
                have hzr : z < r := by omega
                have hzs : z < s := by omega
                have hrD : r ∈ D := ihe (b - r) (by omega) r hr rfl
                have hsD : s ∈ D := ihe (b - s) (by omega) s hs rfl
                exact hclosed m hmD r hrD s hsD z
                  (Finset.mem_insert_of_mem hz) (by simpa [add_comm] using hnum)
          have hBD : (B : Set ℕ) ⊆ D := by
            intro z hz
            exact hBDaux (b - z) z hz rfl
          intro z hz
          rw [Finset.mem_coe, Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact hmD
          · exact hBD hz
        have haff : GeneralizedAffineOn (insert m B) x b m := by
          let g : G := x m - x b
          let v : G := x b
          have hAffAux : ∀ e : ℕ, ∀ z ∈ B, b - z = e →
              ∃ kz : ℤ, (z : ℤ) = (b : ℤ) + kz * ((m : ℤ) - b) ∧
                x z = kz • g + v := by
            intro e
            induction e using Nat.strong_induction_on with
            | h e ihe =>
                intro z hz hdist
                have hzb : z ≤ b := Finset.le_max' B z hz
                by_cases hzbEq : z = b
                · subst z
                  exact ⟨0, by simp, by simp [v]⟩
                have hzC : z ∈ C := Finset.mem_erase.mpr ⟨hzbEq, hz⟩
                obtain ⟨r, hr, s, hs, heq⟩ :=
                  mem_graphPairCells.mp (hcellC z hzC)
                have hnum : m + z = r + s := congrArg Prod.fst heq
                have hlab : x m + x z = x r + x s := congrArg Prod.snd heq
                have hrle : r ≤ b := Finset.le_max' B r hr
                have hsle : s ≤ b := Finset.le_max' B s hs
                have hzr : z < r := by omega
                have hzs : z < s := by omega
                obtain ⟨kr, hkr, hxr⟩ := ihe (b - r) (by omega) r hr rfl
                obtain ⟨ks, hks, hxs⟩ := ihe (b - s) (by omega) s hs rfl
                refine ⟨kr + ks - 1, ?_, ?_⟩
                · have hcast : (m : ℤ) + z = r + s := by exact_mod_cast hnum
                  rw [hkr, hks] at hcast
                  linear_combination hcast
                · calc
                    x z = (x m + x z) - x m := by abel
                    _ = (x r + x s) - x m := by rw [hlab]
                    _ = (kr • g + v) + (ks • g + v) - x m := by
                      rw [hxr, hxs]
                    _ = (kr + ks - 1) • g + v := by
                      dsimp only [g, v]
                      simp only [add_zsmul, sub_zsmul, one_zsmul]
                      abel
          refine ⟨g, v, ?_⟩
          intro z hz
          rw [Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact ⟨1, by simp, by simp [g, v]⟩
          · exact hAffAux (b - z) z hz rfl
        rw [← hAeq] at htern haff
        exact ⟨b, m, hbm, htern, haff⟩

/-- Contrapositive form: a non-Freiman graph has at least `3k-3` cells. -/
theorem three_card_sub_three_le_graphPairCells_of_not_preserves
    (A : Finset ℕ) (x : ℕ → G) (hcard : 3 ≤ A.card)
    (hfail : ¬ PreservesPairSums A x) :
    3 * A.card - 3 ≤ (graphPairCells A x).card := by
  by_contra hnot
  have hsmall : (graphPairCells A x).card ≤ 3 * A.card - 4 := by omega
  exact hfail (graphProgressionStructured_preserves
    (graphProgressionStructured_of_three_card_sub_four A x hcard hsmall))

lemma graphPairCells_card_le_choose_two_add_card
    (C : Finset ℕ) (x : ℕ → G) :
    (graphPairCells C x).card ≤ C.card.choose 2 + C.card := by
  classical
  let f : ℕ × ℕ → ℕ × G := fun p => (p.1 + p.2, x p.1 + x p.2)
  let P := ((C.product C).filter fun p => p.1 < p.2) ∪ C.diag
  have hsub : graphPairCells C x ⊆ P.image f := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_graphPairCells.mp hy
    rcases lt_trichotomy a b with hab | hab | hab
    · apply Finset.mem_image.mpr
      refine ⟨(a, b), Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩), rfl⟩
    · subst b
      apply Finset.mem_image.mpr
      exact ⟨(a, a), Finset.mem_union_right _ (by simp [ha]), rfl⟩
    · apply Finset.mem_image.mpr
      refine ⟨(b, a), Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hab⟩), ?_⟩
      simp only [f]
      rw [add_comm a b, add_comm (x a) (x b)]
  calc
    (graphPairCells C x).card ≤ (P.image f).card := Finset.card_le_card hsub
    _ ≤ P.card := Finset.card_image_le
    _ ≤ (((C.product C).filter fun p => p.1 < p.2).card + C.diag.card) :=
      by simpa only [P] using (Finset.card_union_le
        ((C.product C).filter fun p => p.1 < p.2) C.diag)
    _ = C.card.choose 2 + C.card := by
      rw [show ((C.product C).filter fun p => p.1 < p.2).card =
          C.card.choose 2 by exact Finset.card_product_filter_lt,
        Finset.diag_card]

lemma graphPairCells_union_le_incident_add
    {A T C U : Finset ℕ} (x : ℕ → G)
    (hTA : T ⊆ A) (hCA : C ⊆ A) (hU : U = T ∪ C) :
    (graphPairCells U x).card ≤
      (incidentGraphPairCells A T x).card + (graphPairCells C x).card := by
  have hsub : graphPairCells U x ⊆
      incidentGraphPairCells A T x ∪ graphPairCells C x := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_graphPairCells.mp hy
    rw [hU, Finset.mem_union] at ha hb
    rcases ha with haT | haC
    · exact Finset.mem_union_left _
        (mem_incidentGraphPairCells.mpr ⟨a, haT, b,
          (hb.elim (fun hbT => hTA hbT) (fun hbC => hCA hbC)), rfl⟩)
    · rcases hb with hbT | hbC
      · apply Finset.mem_union_left
        exact mem_incidentGraphPairCells.mpr ⟨b, hbT, a, hCA haC,
          by simp [add_comm]⟩
      · exact Finset.mem_union_right _
          (mem_graphPairCells.mpr ⟨a, haC, b, hbC, rfl⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- A small set of extra vertices carrying a non-Freiman witness forces the
incident graph above a dense core to have at least `5/2` cells per core
vertex.  The exceptional case of no extra vertex needs six core vertices. -/
private lemma five_card_le_two_incident_of_bad_extension
    {A T C U : Finset ℕ} (x : ℕ → G)
    (hTA : T ⊆ A) (hCA : C ⊆ A) (hdis : Disjoint T C)
    (hU : U = T ∪ C) (hTcard : 4 ≤ T.card) (hCcard : C.card ≤ 4)
    (hzero : C.card = 0 → 6 ≤ T.card)
    (hfail : ¬ PreservesPairSums U x) :
    5 * T.card ≤ 2 * (incidentGraphPairCells A T x).card := by
  have hUcard : U.card = T.card + C.card := by
    rw [hU, Finset.card_union_of_disjoint hdis]
  have hUthree : 3 ≤ U.card := by omega
  have hgraph := three_card_sub_three_le_graphPairCells_of_not_preserves
    U x hUthree hfail
  have hunion := graphPairCells_union_le_incident_add x hTA hCA hU
  have hsmall := graphPairCells_card_le_choose_two_add_card C x
  have hcombined : 3 * (T.card + C.card) - 3 ≤
      (incidentGraphPairCells A T x).card + (graphPairCells C x).card := by
    omega
  interval_cases hCr : C.card <;> simp_all [Nat.choose] <;> omega

/-- High-density incident-cell bound.  This is the exact unweighted input
needed by the layer-cake argument: if the labeling is not a Freiman
homomorphism on `A`, every subset containing more than two thirds of `A`
meets at least `5/2` graph-sum cells per vertex. -/
theorem five_card_le_two_card_incident_of_not_preserves
    (A T : Finset ℕ) (x : ℕ → G) (hTA : T ⊆ A)
    (hAcard : 6 ≤ A.card)
    (hdense : 2 * (A.card - 1) < 3 * T.card)
    (hfail : ¬ PreservesPairSums A x) :
    5 * T.card ≤ 2 * (incidentGraphPairCells A T x).card := by
  classical
  have hTcard : 4 ≤ T.card := by omega
  rw [PreservesPairSums] at hfail
  push Not at hfail
  obtain ⟨a, ha, b, hb, c, hc, z, hz, hsum, hlabel⟩ := hfail
  let W : Finset ℕ := {a, b, c, z}
  let C : Finset ℕ := W \ T
  let U : Finset ℕ := T ∪ C
  have hCsubW : C ⊆ W := Finset.sdiff_subset
  have hCA : C ⊆ A := by
    intro y hy
    have hyW := hCsubW hy
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hyW
    rcases hyW with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hz
  have hdis : Disjoint T C := by
    rw [Finset.disjoint_left]
    intro y hyT hyC
    exact (Finset.mem_sdiff.mp hyC).2 hyT
  have hWcard : W.card ≤ 4 := by
    dsimp only [W]
    calc
      ({a, b, c, z} : Finset ℕ).card ≤ ({b, c, z} : Finset ℕ).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (({c, z} : Finset ℕ).card + 1) + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ((({z} : Finset ℕ).card + 1) + 1) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ ≤ 4 := by simp
  have hCcard : C.card ≤ 4 :=
    (Finset.card_le_card hCsubW).trans hWcard
  have haU : a ∈ U := by simp [U, C, W]
  have hbU : b ∈ U := by simp [U, C, W]
  have hcU : c ∈ U := by simp [U, C, W]
  have hzU : z ∈ U := by simp [U, C, W]
  have hfailU : ¬ PreservesPairSums U x := by
    intro hpres
    exact hlabel (hpres a haU b hbU c hcU z hzU hsum)
  by_cases hCzero : C.card = 0
  · have hCempty : C = ∅ := Finset.card_eq_zero.mp hCzero
    have hUeqT : U = T := by simp [U, hCempty]
    have haT : a ∈ T := by simpa [hUeqT] using haU
    have hbT : b ∈ T := by simpa [hUeqT] using hbU
    have hcT : c ∈ T := by simpa [hUeqT] using hcU
    have hzT : z ∈ T := by simpa [hUeqT] using hzU
    by_cases hTsix : 6 ≤ T.card
    · exact five_card_le_two_incident_of_bad_extension x hTA hCA hdis rfl
        hTcard hCcard (fun _ => hTsix) hfailU
    · have hTltA : T.card < A.card := by omega
      have hnotSub : ¬ A ⊆ T := by
        intro hAT
        have := Finset.card_le_card hAT
        omega
      obtain ⟨e, heA, heT⟩ := Finset.not_subset.mp hnotSub
      let C' : Finset ℕ := {e}
      let U' : Finset ℕ := T ∪ C'
      have hC'A : C' ⊆ A := by simpa [C'] using heA
      have hdis' : Disjoint T C' := by
        simp [C', Finset.disjoint_left, heT]
      have hfailU' : ¬ PreservesPairSums U' x := by
        intro hpres
        have hTU : T ⊆ U' := by simp [U']
        exact hlabel (hpres a (hTU haT) b (hTU hbT) c (hTU hcT) z
          (hTU hzT) hsum)
      exact five_card_le_two_incident_of_bad_extension x hTA hC'A hdis'
        (by rfl : U' = T ∪ C') hTcard (by simp [C']) (by simp [C']) hfailU'
  · exact five_card_le_two_incident_of_bad_extension x hTA hCA hdis
      (by rfl : U = T ∪ C) hTcard hCcard (fun hC => (hCzero hC).elim) hfailU

/-- The sharp weighted graph-cell inequality obtained by applying the dense
incident theorem to every superlevel set of the vertex weights. -/
theorem weighted_graph_bound_of_not_preserves
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (M : ℕ)
    (hAcard : 6 ≤ A.card) (hmax : ∀ a ∈ A, w a ≤ M)
    (hfail : ¬ PreservesPairSums A x) :
    5 * (∑ a ∈ A, w a) ≤
      2 * ∑ c ∈ graphPairCells A x, graphCellWeight A x w c := by
  apply weighted_graph_bound_of_high_incident_bounds A x w M
    (Finset.card_pos.mp (by omega)) hmax
  intro t ht hdense
  exact five_card_le_two_card_incident_of_not_preserves A
    (A.filter fun a => t < w a) x (Finset.filter_subset _ _)
      hAcard hdense hfail

/-! ## Controlled quotient labels of coherent fibres -/

/-- If all occupied fibres lie in cosets of one subgroup, then their chosen
representatives, modulo that very subgroup, preserve pair sums.  The proof is
quantitative: failure would give the sharp weighted graph-cell lower bound,
while every graph cell injects its weight into the corresponding quotient
cell of `X + X`. -/
theorem coordinateFiberRepresentative_preservesPairSums_of_common_cosets
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (H : AddSubgroup (ZMod d))
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hAll : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a))
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    PreservesPairSums (firstCoordinateSet X)
      (fun a => QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)) := by
  classical
  let A := firstCoordinateSet X
  let x : ℕ → ZMod d ⧸ H := fun a =>
    QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let q : ℕ × ZMod d → ℕ × (ZMod d ⧸ H) := fun p =>
    (p.1, QuotientAddGroup.mk' H p.2)
  have hquot : ∀ {a : ℕ}, a ∈ A → ∀ {y : ZMod d},
      y ∈ coordinateFiber X a → QuotientAddGroup.mk' H y = x a := by
    intro a ha y hy
    obtain ⟨r, hr⟩ := hAll a (by simpa [A] using ha)
    have hyr := hr (by simpa using hy)
    have hrr := hr (by simpa using
      (coordinateFiberRepresentative_mem (X := X) (a := a)
        (by simpa [A] using ha)))
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyr hrr
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    have hdiff := H.sub_mem hyr hrr
    convert hdiff using 1 <;> simp [vadd_eq_add] <;> abel
  have hwmax : ∀ a ∈ A, w a ≤ X.card := by
    intro a ha
    dsimp only [w]
    rw [card_coordinateFiber]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  by_contra hfail
  have hweighted := weighted_graph_bound_of_not_preserves
    A x w X.card (by simpa [A] using hAcard) hwmax hfail
  have hone : ∀ c ∈ graphPairCells A x,
      graphCellWeight A x w c ≤ ((X + X).filter fun p => q p = c).card := by
    intro c hc
    rw [graphCellWeight]
    apply Finset.sup_le
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpA := Finset.mem_product.mp hp'.1
    have hleft : (coordinateFiber X p.1).Nonempty :=
      coordinateFiber_nonempty_iff.mpr (by simpa [A] using hpA.1)
    have hright : (coordinateFiber X p.2).Nonempty :=
      coordinateFiber_nonempty_iff.mpr (by simpa [A] using hpA.2)
    have hmax : max (w p.1) (w p.2) ≤
        (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
      dsimp only [w]
      exact max_le (Finset.card_le_card_add_right hright)
        (Finset.card_le_card_add_left hleft)
    refine hmax.trans ?_
    let f : ZMod d → ℕ × ZMod d := fun y => (p.1 + p.2, y)
    calc
      (coordinateFiber X p.1 + coordinateFiber X p.2).card =
          ((coordinateFiber X p.1 + coordinateFiber X p.2).image f).card :=
        (Finset.card_image_iff.mpr (by
          intro y hy z hz hyz
          exact congrArg Prod.snd hyz)).symm
      _ ≤ ((X + X).filter fun r => q r = c).card := by
        apply Finset.card_le_card
        intro r hr
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hy
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.add_mem_add (mem_coordinateFiber.mp hu)
            (mem_coordinateFiber.mp hv)
        · calc
            q (p.1 + p.2, u + v) =
                (p.1 + p.2,
                  QuotientAddGroup.mk' H u + QuotientAddGroup.mk' H v) := by
                    simp [q]
            _ = (p.1 + p.2, x p.1 + x p.2) := by
              rw [hquot hpA.1 hu, hquot hpA.2 hv]
            _ = c := hp'.2
  have hcellSum :
      (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) ≤
        (X + X).card := by
    calc
      (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) ≤
          ∑ c ∈ graphPairCells A x,
            ((X + X).filter fun p => q p = c).card :=
        Finset.sum_le_sum hone
      _ = ((X + X).filter fun p => q p ∈ graphPairCells A x).card := by
        exact Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ (X + X).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
  have hXcard : X.card = ∑ a ∈ A, w a := by
    simpa [A, w] using card_eq_sum_card_coordinateFiber X
  have hlarge : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hweighted.trans (Nat.mul_le_mul_left 2 hcellSum)
  omega

/-- Packaged controlled-subgroup conclusion for the cyclic inverse step.
Besides common coset containment and the existing subgroup-mass bound, the
chosen coset labels are a Freiman homomorphism modulo the same subgroup. -/
theorem exists_common_dense_coset_with_mass_bound_and_preserving_labels
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        (∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a)) ∧
        (firstCoordinateSet X).card * Nat.card H ≤
          4 * ((X + X).card - X.card) ∧
        PreservesPairSums (firstCoordinateSet X)
          (fun a => QuotientAddGroup.mk' H
            (coordinateFiberRepresentative X a)) := by
  obtain ⟨base, hbase, H, hbaseCos, hHdense, hbaseMax, hAll, hmass⟩ :=
    exists_common_dense_coset_with_mass_bound X hA hAzero hAcard hgcd hsmall
  have hpres := coordinateFiberRepresentative_preservesPairSums_of_common_cosets
    X H hAcard hAll hsmall
  exact ⟨base, hbase, H, hbaseCos, hHdense, hbaseMax, hAll, hmass, hpres⟩

end Erdos360

#print axioms Erdos360.weighted_graph_cells_layerCake
#print axioms Erdos360.weighted_graph_bound_of_high_incident_bounds
#print axioms Erdos360.graphProgressionStructured_of_three_card_sub_four
#print axioms Erdos360.three_card_sub_three_le_graphPairCells_of_not_preserves
#print axioms Erdos360.five_card_le_two_card_incident_of_not_preserves
#print axioms Erdos360.weighted_graph_bound_of_not_preserves
#print axioms Erdos360.coordinateFiberRepresentative_preservesPairSums_of_common_cosets
#print axioms Erdos360.exists_common_dense_coset_with_mass_bound_and_preserving_labels

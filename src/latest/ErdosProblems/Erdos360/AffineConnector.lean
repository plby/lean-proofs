import ErdosProblems.Erdos360.WeightedGraph

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G]

/-- On a normalized support, a generalized affine graph is genuinely affine:
the common coordinate step divides the gcd and hence equals one. -/
theorem affineOn_of_generalizedAffineOn_normalized
    {A : Finset ℕ} {x : ℕ → G} {p q : ℕ}
    (hzero : 0 ∈ A) (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hpq : p < q) (haff : GeneralizedAffineOn A x p q) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  obtain ⟨u, v, haff⟩ := haff
  let d := q - p
  have hmod : ∀ a ∈ A, a ≡ p [MOD d] := by
    intro a ha
    obtain ⟨k, hk, -⟩ := haff a ha
    rw [Nat.modEq_iff_dvd]
    have hdcast : ((d : ℕ) : ℤ) = (q : ℤ) - p := by
      dsimp only [d]
      omega
    rw [hdcast]
    refine ⟨-k, ?_⟩
    linear_combination -hk
  have hdiv : d ∣ A.gcd (fun n : ℕ => n) := by
    apply Finset.dvd_gcd
    intro a ha
    apply Nat.modEq_zero_iff_dvd.mp
    exact ((hmod 0 hzero).trans (hmod a ha).symm).symm
  have hd : d = 1 := by
    rw [hgcd] at hdiv
    exact Nat.eq_one_of_dvd_one hdiv
  refine ⟨u, v - p • u, ?_⟩
  intro a ha
  obtain ⟨k, hk, hxa⟩ := haff a ha
  have hqp : q = p + 1 := by dsimp only [d] at hd; omega
  have hk' : k = (a : ℤ) - p := by
    rw [hqp] at hk
    simp only [Int.natCast_add, Int.natCast_one] at hk
    linear_combination -hk
  calc
    x a = k • u + v := hxa
    _ = ((a : ℤ) - p) • u + v := by rw [hk']
    _ = a • u + (v - p • u) := by
      simp only [sub_zsmul, natCast_zsmul]
      abel

private lemma generalizedAffine_point_of_relation
    {B : Finset ℕ} {x : ℕ → G} {p q m a r s : ℕ} {u v : G}
    (haff : ∀ z ∈ B, ∃ k : ℤ,
      (z : ℤ) = (p : ℤ) + k * ((q : ℤ) - p) ∧ x z = k • u + v)
    (ha : a ∈ B) (hr : r ∈ B) (hs : s ∈ B)
    (hnum : m + a = r + s) (hlab : x m + x a = x r + x s) :
    ∃ k : ℤ, (m : ℤ) = (p : ℤ) + k * ((q : ℤ) - p) ∧
      x m = k • u + v := by
  obtain ⟨ka, hka, hxa⟩ := haff a ha
  obtain ⟨kr, hkr, hxr⟩ := haff r hr
  obtain ⟨ks, hks, hxs⟩ := haff s hs
  refine ⟨kr + ks - ka, ?_, ?_⟩
  · have hcast : (m : ℤ) + a = r + s := by exact_mod_cast hnum
    rw [hka, hkr, hks] at hcast
    linear_combination hcast
  · calc
      x m = (x m + x a) - x a := by abel
      _ = (x r + x s) - x a := by rw [hlab]
      _ = (kr • u + v) + (ks • u + v) - (ka • u + v) := by
        rw [hxa, hxr, hxs]
      _ = (kr + ks - ka) • u + v := by
        simp only [add_zsmul, sub_zsmul]
        abel

/-- A small incident graph above a six-point core makes the generalized
affine structure supplied by graph `3k-4` extend to every vertex of `A`.
If a translate had no collision with the core graph, it would itself add a
whole new core-sized family of incident cells. -/
theorem generalizedAffineOn_of_small_incident
    [DecidableEq G] (A T : Finset ℕ) (x : ℕ → G)
    (hTA : T ⊆ A) (hTcard : 6 ≤ T.card)
    (_hpres : PreservesPairSums A x)
    (hsmall : 2 * (incidentGraphPairCells A T x).card < 5 * T.card) :
    ∃ p q : ℕ, p < q ∧ GeneralizedAffineOn A x p q := by
  classical
  have hgraphSub : graphPairCells T x ⊆ incidentGraphPairCells A T x := by
    intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_graphPairCells.mp hc
    exact mem_incidentGraphPairCells.mpr ⟨a, ha, b, hTA hb, rfl⟩
  have hgraphCard : (graphPairCells T x).card ≤ 3 * T.card - 4 := by
    have := Finset.card_le_card hgraphSub
    omega
  obtain ⟨p, q, hpq, hgen, haff⟩ :=
    graphProgressionStructured_of_three_card_sub_four T x
      (by omega) hgraphCard
  obtain ⟨u, v, haff⟩ := haff
  refine ⟨p, q, hpq, u, v, ?_⟩
  intro m hmA
  by_cases hmT : m ∈ T
  · exact haff m hmT
  · have hcollision : ∃ a ∈ T,
        (m + a, x m + x a) ∈ graphPairCells T x := by
      by_contra hnone
      push Not at hnone
      let S := T.image fun a => (m + a, x m + x a)
      have hScard : S.card = T.card := by
        dsimp only [S]
        apply Finset.card_image_iff.mpr
        intro a ha b hb hab
        exact Nat.add_left_cancel (congrArg Prod.fst hab)
      have hdis : Disjoint (graphPairCells T x) S := by
        rw [Finset.disjoint_left]
        intro c hcG hcS
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcS
        exact hnone a ha hcG
      have hsub : graphPairCells T x ∪ S ⊆
          incidentGraphPairCells A T x := by
        intro c hc
        rcases Finset.mem_union.mp hc with hcG | hcS
        · exact hgraphSub hcG
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcS
          exact mem_incidentGraphPairCells.mpr
            ⟨a, ha, m, hmA, by simp [add_comm]⟩
      have hTT : 2 * T.card - 1 ≤ (graphPairCells T x).card := by
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hTne hTne
        have hproj : (T + T).card ≤ (graphPairCells T x).card := by
          rw [← image_fst_graphPairCells T x]
          exact Finset.card_image_le
        omega
      have hUcard : (graphPairCells T x ∪ S).card =
          (graphPairCells T x).card + T.card := by
        rw [Finset.card_union_of_disjoint hdis, hScard]
      have hUle := Finset.card_le_card hsub
      omega
    obtain ⟨a, ha, hcell⟩ := hcollision
    obtain ⟨r, hr, s, hs, heq⟩ := mem_graphPairCells.mp hcell
    have hnum : m + a = r + s := congrArg Prod.fst heq
    have hlab : x m + x a = x r + x s := congrArg Prod.snd heq
    exact generalizedAffine_point_of_relation haff ha hr hs hnum hlab

/-- Normalization turns the preceding generalized affine conclusion into an
ordinary affine formula. -/
theorem affineOn_of_small_incident
    [DecidableEq G] (A T : Finset ℕ) (x : ℕ → G)
    (hzero : 0 ∈ A) (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hTA : T ⊆ A) (hTcard : 6 ≤ T.card)
    (hpres : PreservesPairSums A x)
    (hsmall : 2 * (incidentGraphPairCells A T x).card < 5 * T.card) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  obtain ⟨p, q, hpq, haff⟩ :=
    generalizedAffineOn_of_small_incident A T x hTA hTcard hpres hsmall
  exact affineOn_of_generalizedAffineOn_normalized hzero hgcd hpq haff

/-! If the full graph has fewer than `3|A|-3` cells, graph `3k-4`
already supplies generalized affine structure.  Gcd normalization makes it
ordinary affine.  This gives an axiom-free treatment of small threshold
sets by subtracting the at most three omitted vertices. -/

lemma three_card_sub_three_le_graphPairCells_of_not_affine_normalized
    [DecidableEq G] (A : Finset ℕ) (x : ℕ → G)
    (hzero : 0 ∈ A) (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hcard : 3 ≤ A.card)
    (hnot : ¬ ∃ u v : G, ∀ a ∈ A, x a = a • u + v) :
    3 * A.card - 3 ≤ (graphPairCells A x).card := by
  by_contra hlt
  have hsmall : (graphPairCells A x).card ≤ 3 * A.card - 4 := by omega
  obtain ⟨p, q, hpq, _hgen, haff⟩ :=
    graphProgressionStructured_of_three_card_sub_four A x hcard hsmall
  exact hnot (affineOn_of_generalizedAffineOn_normalized hzero hgcd hpq haff)

/-! Combining the six-point extension argument with the full-graph growth
bound gives the exact high-density incident statement needed by layer cake. -/

/-- Under the normalized dense-support hypotheses, a genuinely small
incident graph forces an ordinary affine label on all of `A`. -/
theorem affineOn_of_small_incident_normalized
    [DecidableEq G] (A T : Finset ℕ) (x : ℕ → G)
    (hA : A.Nonempty) (hzero : 0 ∈ A) (hAcard : 6 ≤ A.card)
    (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (_hspan : 2 * A.max' hA < 3 * A.card)
    (hTA : T ⊆ A) (hdense : 2 * (A.card - 1) < 3 * T.card)
    (hpres : PreservesPairSums A x)
    (hsmall : 2 * (incidentGraphPairCells A T x).card < 5 * T.card) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  by_cases hTcard : 6 ≤ T.card
  · exact affineOn_of_small_incident A T x hzero hgcd hTA hTcard hpres hsmall
  · by_contra hnot
    let C := A \ T
    have hTcard4 : 4 ≤ T.card := by omega
    have hCcardEq : C.card = A.card - T.card := by
      simpa [C] using Finset.card_sdiff_of_subset hTA
    have hCcard : C.card ≤ 3 := by omega
    have hCA : C ⊆ A := Finset.sdiff_subset
    have hdis : Disjoint T C := by
      rw [Finset.disjoint_left]
      intro a haT haC
      exact (Finset.mem_sdiff.mp haC).2 haT
    have hU : A = T ∪ C := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, C]
      constructor
      · intro ha
        by_cases haT : a ∈ T
        · exact Or.inl haT
        · exact Or.inr ⟨ha, haT⟩
      · rintro (haT | ⟨ha, -⟩)
        · exact hTA haT
        · exact ha
    have hgraph :=
      three_card_sub_three_le_graphPairCells_of_not_affine_normalized
        A x hzero hgcd (by omega) hnot
    have hunion := graphPairCells_union_le_incident_add x hTA hCA hU
    have hsmallC := graphPairCells_card_le_choose_two_add_card C x
    have hcombined : 3 * A.card - 3 ≤
        (incidentGraphPairCells A T x).card + (graphPairCells C x).card := by
      omega
    interval_cases hCr : C.card <;>
      norm_num [Nat.choose] at hsmallC <;> omega

/-- Contrapositive form of `affineOn_of_small_incident_normalized`: every
dense threshold set sees at least `5/2` as many incident graph cells when
the label is not affine. -/
theorem five_card_le_two_card_incident_of_not_affine
    [DecidableEq G] (A T : Finset ℕ) (x : ℕ → G)
    (hA : A.Nonempty) (hzero : 0 ∈ A) (hAcard : 6 ≤ A.card)
    (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hspan : 2 * A.max' hA < 3 * A.card)
    (hTA : T ⊆ A) (hdense : 2 * (A.card - 1) < 3 * T.card)
    (hpres : PreservesPairSums A x)
    (hnot : ¬ ∃ u v : G, ∀ a ∈ A, x a = a • u + v) :
    5 * T.card ≤ 2 * (incidentGraphPairCells A T x).card := by
  by_contra hlt
  have hsmall : 2 * (incidentGraphPairCells A T x).card < 5 * T.card := by
    omega
  exact hnot (affineOn_of_small_incident_normalized A T x hA hzero hAcard
    hgcd hspan hTA hdense hpres hsmall)

/-- Weighted affine-alignment inequality.  Failure of ordinary affine
structure costs `5/2` of the total vertex mass in graph-cell mass. -/
theorem weighted_graph_bound_of_not_affine
    [DecidableEq G] (A : Finset ℕ) (x : ℕ → G)
    (w : ℕ → ℕ) (M : ℕ)
    (hA : A.Nonempty) (hzero : 0 ∈ A) (hAcard : 6 ≤ A.card)
    (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hspan : 2 * A.max' hA < 3 * A.card)
    (hmax : ∀ a ∈ A, w a ≤ M)
    (hpres : PreservesPairSums A x)
    (hnot : ¬ ∃ u v : G, ∀ a ∈ A, x a = a • u + v) :
    5 * (∑ a ∈ A, w a) ≤
      2 * ∑ c ∈ graphPairCells A x, graphCellWeight A x w c := by
  apply weighted_graph_bound_of_high_incident_bounds A x w M hA hmax
  intro t ht hdense
  exact five_card_le_two_card_incident_of_not_affine A
    (A.filter fun a => t < w a) x hA hzero hAcard hgcd hspan
      (Finset.filter_subset _ _) hdense hpres hnot

/-! ## From controlled common cosets to controlled affine common cosets -/

/-- If every occupied fibre is contained in a coset of `H`, the total
graph-cell weight of the quotient labels injects fibrewise into `X + X`.
This is the upper-bound half of the affine-alignment contradiction. -/
theorem common_coset_graphCellWeight_le_sumset
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (H : AddSubgroup (ZMod d))
    (hAll : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a)) :
    (∑ c ∈ graphPairCells (firstCoordinateSet X)
        (fun a => QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)),
      graphCellWeight (firstCoordinateSet X)
        (fun a => QuotientAddGroup.mk' H (coordinateFiberRepresentative X a))
        (fun a => (coordinateFiber X a).card) c) ≤ (X + X).card := by
  classical
  let A := firstCoordinateSet X
  let x : ℕ → ZMod d ⧸ H := fun a =>
    QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let q : ℕ × ZMod d → ℕ × (ZMod d ⧸ H) := fun p =>
    (p.1, QuotientAddGroup.mk' H p.2)
  change (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) ≤
    (X + X).card
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
    convert hdiff using 1 <;> simp [vadd_eq_add]
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
  calc
    (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) ≤
        ∑ c ∈ graphPairCells A x,
          ((X + X).filter fun p => q p = c).card :=
      Finset.sum_le_sum hone
    _ = ((X + X).filter fun p => q p ∈ graphPairCells A x).card := by
      exact Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ (X + X).card :=
      Finset.card_le_card (Finset.filter_subset _ _)

/-- For a controlled common subgroup, strict product doubling forces the
chosen quotient representatives to be an affine function of the first
coordinate. -/
theorem coordinateFiberRepresentative_affine_of_common_cosets
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (H : AddSubgroup (ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hAll : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a))
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ u v : ZMod d ⧸ H, ∀ a ∈ firstCoordinateSet X,
      QuotientAddGroup.mk' H (coordinateFiberRepresentative X a) =
        a • u + v := by
  classical
  let A := firstCoordinateSet X
  let x : ℕ → ZMod d ⧸ H := fun a =>
    QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  have hgcdNat : A.gcd (fun n : ℕ => n) = 1 := by
    have hgcd' := hgcd
    rw [Erdos13Additive.nat_int_finset_gcd] at hgcd'
    exact_mod_cast hgcd'
  have hspan : 2 * A.max' (by simpa [A] using hA) < 3 * A.card := by
    simpa [A] using fiber_span_lt_three_halves X hA hzero hAcard hgcd hsmall
  have hpres : PreservesPairSums A x := by
    simpa [A, x] using
      coordinateFiberRepresentative_preservesPairSums_of_common_cosets
        X H hAcard hAll hsmall
  have hmax : ∀ a ∈ A, w a ≤ X.card := by
    intro a ha
    dsimp only [w]
    rw [card_coordinateFiber]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  by_contra hnot
  have hlower := weighted_graph_bound_of_not_affine A x w X.card
    (by simpa [A] using hA) (by simpa [A] using hzero)
    (by simpa [A] using hAcard) hgcdNat hspan hmax hpres hnot
  have hupper :
      (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) ≤
        (X + X).card := by
    simpa [A, x, w] using common_coset_graphCellWeight_le_sumset X H hAll
  have hXcard : X.card = ∑ a ∈ A, w a := by
    simpa [A, w] using card_eq_sum_card_coordinateFiber X
  have hlarge : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hlower.trans (Nat.mul_le_mul_left 2 hupper)
  omega

/-- Lift affine quotient labels to representatives in `ZMod d`; every
occupied fibre then lies in the corresponding affine `H`-coset. -/
theorem affine_commonFiberCosets_of_common_cosets
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (H : AddSubgroup (ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hAll : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a))
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ u v : ZMod d, ∀ a ∈ firstCoordinateSet X,
      ∀ y ∈ coordinateFiber X a, y - (a • u + v) ∈ H := by
  classical
  obtain ⟨ubar, vbar, haff⟩ :=
    coordinateFiberRepresentative_affine_of_common_cosets X H hA hzero
      hAcard hgcd hAll hsmall
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk'_surjective H ubar
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective H vbar
  refine ⟨u, v, ?_⟩
  intro a ha y hy
  have hquot : QuotientAddGroup.mk' H y =
      QuotientAddGroup.mk' H (coordinateFiberRepresentative X a) := by
    obtain ⟨r, hr⟩ := hAll a ha
    have hyr := hr (by simpa using hy)
    have hrr := hr (by simpa using
      (coordinateFiberRepresentative_mem (X := X) (a := a) ha))
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyr hrr
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    have hdiff := H.sub_mem hyr hrr
    convert hdiff using 1 <;> simp [vadd_eq_add]
  apply (QuotientAddGroup.eq_iff_sub_mem).1
  calc
    QuotientAddGroup.mk' H y =
        QuotientAddGroup.mk' H (coordinateFiberRepresentative X a) := hquot
    _ = a • ubar + vbar := haff a ha
    _ = QuotientAddGroup.mk' H (a • u + v) := by
      rw [← hu, ← hv]
      simp

/-- Full controlled affine-coset package for the cyclic inverse theorem. -/
theorem exists_common_dense_coset_with_mass_bound_and_affine_labels
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ∃ u v : ZMod d,
        ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        (∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a)) ∧
        (firstCoordinateSet X).card * Nat.card H ≤
          4 * ((X + X).card - X.card) ∧
        (∀ a ∈ firstCoordinateSet X, ∀ y ∈ coordinateFiber X a,
          y - (a • u + v) ∈ H) := by
  obtain ⟨base, hbase, H, hbaseCos, hHdense, hbaseMax, hAll, hmass,
    _hpres⟩ :=
    exists_common_dense_coset_with_mass_bound_and_preserving_labels X hA
      hzero hAcard hgcd hsmall
  obtain ⟨u, v, haff⟩ := affine_commonFiberCosets_of_common_cosets X H
    hA hzero hAcard hgcd hAll hsmall
  exact ⟨base, hbase, H, u, v, hbaseCos, hHdense, hbaseMax, hAll, hmass,
    haff⟩

end Erdos360

#print axioms Erdos360.weighted_graph_bound_of_not_affine
#print axioms Erdos360.coordinateFiberRepresentative_affine_of_common_cosets
#print axioms Erdos360.affine_commonFiberCosets_of_common_cosets
#print axioms Erdos360.exists_common_dense_coset_with_mass_bound_and_affine_labels

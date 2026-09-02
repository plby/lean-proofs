import ErdosProblems.Erdos652.PinnedCircles
import ErdosProblems.Erdos652.CircleCyclicSuccessorArcs
import ErdosProblems.Erdos652.CircleArcDrawingAssembly

open scoped BigOperators Real
noncomputable section

namespace Erdos652

/-- Build all cyclic successor arcs on distance circles containing at least
three points of `Q`.  The conclusion packages exactly the data needed by the
general circle drawing assembly, together with the incidence lower bound. -/
lemma retainedCircleArcFamily
    (P Q : Finset Point) (t : ℕ) (hPQ : Disjoint P Q)
    (ht : ∀ p ∈ P, (distanceRadii p Q).card ≤ t) :
    ∃ (ι : Type) (_instF : Fintype ι) (_instD : DecidableEq ι)
      (A : Finset ι) (endpoint : ι → Sym2 Q)
      (center : ι → circleKeys P Q)
      (arcStart arcEnd : ι → Q)
      (carrier arcInterior : ι → Set Point)
      (γ : ι → Set.Icc (0 : ℝ) 1 → Point),
      P.card * Q.card ≤ A.card + 2 * P.card * t ∧
        (∀ i ∈ A, ¬ (endpoint i).IsDiag) ∧
          (∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i)) ∧
            (∀ i ∈ A, (arcStart i : Point) ≠ (arcEnd i : Point)) ∧
              (∀ i ∈ A,
                (arcStart i : Point) ∈ circle (center i : CircleKey) ∧
                  (arcEnd i : Point) ∈ circle (center i : CircleKey)) ∧
                (∀ i ∈ A,
                  Continuous (γ i) ∧ Function.Injective (γ i) ∧
                    (∀ u, γ i u ∈ circle (center i : CircleKey)) ∧
                      γ i ⟨0, by simp⟩ = (arcStart i : Point) ∧
                        γ i ⟨1, by simp⟩ = (arcEnd i : Point) ∧
                          carrier i = Set.range (γ i) ∧
                            arcInterior i = Set.range
                              (fun u : {u : ℝ // 0 < u ∧ u < 1} =>
                                γ i ⟨u.1, ⟨le_of_lt u.2.1, le_of_lt u.2.2⟩⟩)) ∧
                  (∀ i ∈ A, carrier i ⊆ circle (center i : CircleKey)) ∧
                    (∀ i ∈ A, ∀ v : Q, (v : Point) ∉ arcInterior i) ∧
                      (∀ i ∈ A, ∀ j ∈ A, center i = center j → i ≠ j →
                        arcInterior i ∩ arcInterior j = ∅) ∧
                        (∀ i ∈ A, ∀ j ∈ A, center i = center j →
                          endpoint i = endpoint j → i = j) ∧
                          (∀ i ∈ A, 0 < (center i : CircleKey).2) := by
  classical
  let GoodRadius (p : P) :=
    {r : ℝ // r ∈ (distanceRadii p.1 Q).filter
      (fun r => 3 ≤ (Q.filter fun q => dist p.1 q = r).card)}
  let Retained := Sigma GoodRadius
  let S : Retained → Finset Point := fun a =>
    Q.filter fun q => dist a.1.1 q = a.2.1
  have hS_card : ∀ a : Retained, 3 ≤ (S a).card := by
    intro a
    exact (Finset.mem_filter.mp a.2.2).2
  have hS_circle : ∀ a : Retained,
      (↑(S a) : Set Point) ⊆ circle (a.1.1, a.2.1) := by
    intro a q hq
    have hdist := (Finset.mem_filter.mp hq).2
    simpa [circle, dist_comm] using hdist
  have hkey_mem : ∀ a : Retained, (a.1.1, a.2.1) ∈ circleKeys P Q := by
    intro a
    apply mem_circleKeys_iff.mpr
    exact ⟨a.1.2, (Finset.mem_filter.mp a.2.2).1⟩
  have hcircle : ∀ a : Retained,
      ∃ (succ : {x : Point // x ∈ S a} → {x : Point // x ∈ S a})
        (carrier arcInterior : {x : Point // x ∈ S a} → Set Point)
        (γ : (x : {x : Point // x ∈ S a}) → Set.Icc (0 : ℝ) 1 → Point),
        Function.Bijective succ ∧
          (∀ x, x.1 ≠ (succ x).1) ∧
            (∀ x, Continuous (γ x) ∧ Function.Injective (γ x) ∧
              (∀ u, γ x u ∈ circle (a.1.1, a.2.1)) ∧
                γ x ⟨0, by simp⟩ = x.1 ∧
                  γ x ⟨1, by simp⟩ = (succ x).1 ∧
                    carrier x = Set.range (γ x) ∧
                      arcInterior x = Set.range
                        (fun u : {u : ℝ // 0 < u ∧ u < 1} =>
                          γ x ⟨u.1, ⟨le_of_lt u.2.1, le_of_lt u.2.2⟩⟩)) ∧
              (∀ x y : {y : Point // y ∈ S a}, y.1 ∉ arcInterior x) ∧
                (∀ x y, x ≠ y → arcInterior x ∩ arcInterior y = ∅) ∧
                  (∀ x y, (Sym2.mk x.1 (succ x).1 : Sym2 Point) =
                    Sym2.mk y.1 (succ y).1 → x = y) := by
    intro a
    have hpos : 0 < a.2.1 :=
      circleKey_radius_pos hPQ (hkey_mem a)
    exact circleCyclicSuccessorArcs a.1.1 a.2.1 hpos (S a)
      (hS_circle a) (hS_card a)
  choose succ carrierOne interiorOne γOne hsucc hne harc hnov hdisj huniq
    using hcircle
  let ι := Sigma fun a : Retained => {x : Point // x ∈ S a}
  let A : Finset ι := Finset.univ
  let center : ι → circleKeys P Q := fun i =>
    ⟨(i.1.1.1, i.1.2.1), hkey_mem i.1⟩
  let arcStart : ι → Q := fun i =>
    ⟨i.2.1, (Finset.mem_filter.mp i.2.2).1⟩
  let arcEnd : ι → Q := fun i =>
    ⟨(succ i.1 i.2).1, (Finset.mem_filter.mp (succ i.1 i.2).2).1⟩
  let endpoint : ι → Sym2 Q := fun i => Sym2.mk (arcStart i) (arcEnd i)
  let carrier : ι → Set Point := fun i => carrierOne i.1 i.2
  let arcInterior : ι → Set Point := fun i => interiorOne i.1 i.2
  let γ : ι → Set.Icc (0 : ℝ) 1 → Point := fun i => γOne i.1 i.2
  have hAcard : A.card =
      ∑ p ∈ P, ∑ r ∈ (distanceRadii p Q).filter
          (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
        (Q.filter fun q => dist p q = r).card := by
    dsimp [A, ι]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    rw [Fintype.sum_sigma]
    change (∑ p : P, ∑ r : GoodRadius p, (S ⟨p, r⟩).card) = _
    calc
      (∑ p : P, ∑ r : GoodRadius p, (S ⟨p, r⟩).card) =
          ∑ p : P, ∑ r ∈ (distanceRadii p.1 Q).filter
            (fun r => 3 ≤ (Q.filter fun q => dist p.1 q = r).card),
              (Q.filter fun q => dist p.1 q = r).card := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_subtype
          (s := (distanceRadii p.1 Q).filter
            (fun r => 3 ≤ (Q.filter fun q => dist p.1 q = r).card))
          (p := fun r : ℝ => r ∈ (distanceRadii p.1 Q).filter
            (fun r => 3 ≤ (Q.filter fun q => dist p.1 q = r).card))
          (f := fun r => (Q.filter fun q => dist p.1 q = r).card)]
        intro r
        rfl
      _ = ∑ p ∈ P, ∑ r ∈ (distanceRadii p Q).filter
          (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
            (Q.filter fun q => dist p q = r).card := by
        rw [← Finset.sum_subtype (s := P) (p := fun p : Point => p ∈ P)
          (f := fun p => ∑ r ∈ (distanceRadii p Q).filter
            (fun r => 3 ≤ (Q.filter fun q => dist p q = r).card),
              (Q.filter fun q => dist p q = r).card)]
        intro p
        rfl
  have hcount : P.card * Q.card ≤ A.card + 2 * P.card * t := by
    rw [hAcard]
    exact retained_circle_incidence_lower P Q t ht
  have h_endpoints_distinct : ∀ i ∈ A, (arcStart i : Point) ≠ (arcEnd i : Point) := by
    intro i hi
    simpa [arcStart, arcEnd] using hne i.1 i.2
  have h_nondiag : ∀ i ∈ A, ¬(endpoint i).IsDiag := by
    intro i hi hdiag
    have hsub : arcStart i = arcEnd i :=
      (Sym2.mk_isDiag_iff (x := arcStart i) (y := arcEnd i)).mp (by
        simpa [endpoint] using hdiag)
    exact h_endpoints_distinct i hi (congrArg Subtype.val hsub)
  have h_endpoint_eq : ∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i) :=
    fun _ _ => rfl
  have h_endpoints_on_circle : ∀ i ∈ A,
      (arcStart i : Point) ∈ circle (center i : CircleKey) ∧
        (arcEnd i : Point) ∈ circle (center i : CircleKey) := by
    intro i hi
    constructor
    · simpa [arcStart, center] using (hS_circle i.1 i.2.2)
    · simpa [arcEnd, center] using (hS_circle i.1 (succ i.1 i.2).2)
  have h_arc_param : ∀ i ∈ A,
      Continuous (γ i) ∧ Function.Injective (γ i) ∧
        (∀ u, γ i u ∈ circle (center i : CircleKey)) ∧
          γ i ⟨0, by simp⟩ = (arcStart i : Point) ∧
            γ i ⟨1, by simp⟩ = (arcEnd i : Point) ∧
              carrier i = Set.range (γ i) ∧
                arcInterior i = Set.range
                  (fun u : {u : ℝ // 0 < u ∧ u < 1} =>
                    γ i ⟨u.1, ⟨le_of_lt u.2.1, le_of_lt u.2.2⟩⟩) := by
    intro i hi
    simpa [γ, carrier, arcInterior, center, arcStart, arcEnd] using harc i.1 i.2
  have h_carrier_circle : ∀ i ∈ A, carrier i ⊆ circle (center i : CircleKey) := by
    intro i hi z hz
    rcases h_arc_param i hi with ⟨_, _, hcircle, _, _, hcarrier, _⟩
    rw [hcarrier] at hz
    rcases hz with ⟨u, rfl⟩
    exact hcircle u
  have h_no_vertex : ∀ i ∈ A, ∀ v : Q, (v : Point) ∉ arcInterior i := by
    intro i hi v hv
    have hvCircle : (v : Point) ∈ circle (i.1.1.1, i.1.2.1) := by
      have hv' := hv
      change (v : Point) ∈ interiorOne i.1 i.2 at hv'
      rw [(harc i.1 i.2).2.2.2.2.2.2] at hv'
      rcases hv' with ⟨u, hu⟩
      rw [← hu]
      exact (harc i.1 i.2).2.2.1 _
    have hvS : (v : Point) ∈ S i.1 := by
      apply Finset.mem_filter.mpr
      exact ⟨v.2, by simpa [circle, dist_comm] using hvCircle⟩
    exact hnov i.1 i.2 ⟨v, hvS⟩ (by simpa [arcInterior] using hv)
  have h_same_disjoint : ∀ i ∈ A, ∀ j ∈ A, center i = center j → i ≠ j →
      arcInterior i ∩ arcInterior j = ∅ := by
    rintro ⟨a, x⟩ hi ⟨b, y⟩ hj hc hij
    cases a with
    | mk p r =>
      cases b with
      | mk q s =>
        have hkey := congrArg Subtype.val hc
        have hpq : p = q := Subtype.ext (congrArg Prod.fst hkey)
        subst q
        have hrs : r = s := Subtype.ext (congrArg Prod.snd hkey)
        subst s
        have hxy : x ≠ y := by
          intro hxy
          apply hij
          cases hxy
          rfl
        simpa [arcInterior] using hdisj ⟨p, r⟩ x y hxy
  have h_same_unique : ∀ i ∈ A, ∀ j ∈ A, center i = center j →
      endpoint i = endpoint j → i = j := by
    rintro ⟨a, x⟩ hi ⟨b, y⟩ hj hc hend
    cases a with
    | mk p r =>
      cases b with
      | mk q s =>
        have hkey := congrArg Subtype.val hc
        have hpq : p = q := Subtype.ext (congrArg Prod.fst hkey)
        subst q
        have hrs : r = s := Subtype.ext (congrArg Prod.snd hkey)
        subst s
        have hamb : (Sym2.mk x.1 (succ ⟨p, r⟩ x).1 : Sym2 Point) =
            Sym2.mk y.1 (succ ⟨p, r⟩ y).1 := by
          simpa [endpoint, arcStart, arcEnd] using
            congrArg (Sym2.map fun z : Q => (z : Point)) hend
        have hxy := huniq ⟨p, r⟩ x y hamb
        cases hxy
        rfl
  have h_radius : ∀ i ∈ A, 0 < (center i : CircleKey).2 := by
    intro i hi
    exact circleKey_radius_pos hPQ (center i).2
  exact ⟨ι, inferInstance, inferInstance, A, endpoint, center, arcStart, arcEnd,
    carrier, arcInterior, γ, hcount, h_nondiag, h_endpoint_eq,
    h_endpoints_distinct, h_endpoints_on_circle, h_arc_param, h_carrier_circle,
    h_no_vertex, h_same_disjoint, h_same_unique, h_radius⟩

end Erdos652

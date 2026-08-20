import ErdosProblems.Erdos733.ST.UnitCircle
import ErdosProblems.Erdos733.ST.UnitCircleCyclicSuccessorArcs
import ErdosProblems.Erdos733.ST.UnitCirclesIntersectionsAtMostTwo

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

-- [TABLET NODE: UnitCircleRetainedArcEndpointQuotient]
lemma UnitCircleRetainedArcEndpointQuotient
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ (ι : Type) (instF : Fintype ι) (instD : DecidableEq ι)
      (A : Finset ι) (endpoint : ι → Sym2 P)
      (center arcStart arcEnd : ι → P)
      (carrier arcInterior : ι → Set (EuclideanSpace ℝ (Fin 2)))
      (γ : ι → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      (A.card : ℝ) =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) ∧
        (∀ i ∈ A, ¬ (endpoint i).IsDiag) ∧
          (∀ e ∈ A.image endpoint,
            (A.filter (fun i => endpoint i = e)).card ≤ 2) ∧
            (∀ i ∈ A,
              3 ≤ (P.filter
                (fun q => q ∈ UnitCircle (center i : EuclideanSpace ℝ (Fin 2)))).card) ∧
              (∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i)) ∧
                (∀ i ∈ A,
                  (arcStart i : EuclideanSpace ℝ (Fin 2)) ≠
                    (arcEnd i : EuclideanSpace ℝ (Fin 2))) ∧
                  (∀ i ∈ A,
                    (arcStart i : EuclideanSpace ℝ (Fin 2)) ∈
                        UnitCircle (center i : EuclideanSpace ℝ (Fin 2)) ∧
                      (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∈
                        UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
                    (∀ i ∈ A,
                      Continuous (γ i) ∧
                        Function.Injective (γ i) ∧
                          (∀ t, γ i t ∈
                            UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
                            γ i ⟨0, by simp⟩ =
                              (arcStart i : EuclideanSpace ℝ (Fin 2)) ∧
                              γ i ⟨1, by simp⟩ =
                                (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∧
                                carrier i = Set.range (γ i) ∧
                                  arcInterior i =
                                    Set.range
                                      (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                                        γ i
                                          ⟨t.1, ⟨le_of_lt t.2.1,
                                            le_of_lt t.2.2⟩⟩)) ∧
                      (∀ i ∈ A, carrier i ⊆
                        UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
                        (∀ i ∈ A, ∀ v : P,
                          (v : EuclideanSpace ℝ (Fin 2)) ∉ arcInterior i) ∧
                          (∀ i ∈ A, ∀ j ∈ A,
                            center i = center j → i ≠ j →
                              arcInterior i ∩ arcInterior j = ∅) ∧
                            (∀ i ∈ A, ∀ j ∈ A,
                              center i = center j → endpoint i = endpoint j →
                                i = j) := by
-- BODY
  classical
  let retainedCenters : Finset (EuclideanSpace ℝ (Fin 2)) :=
    P.filter (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card)
  let Retained : Type :=
    {p : EuclideanSpace ℝ (Fin 2) // p ∈ retainedCenters}
  let S : Retained → Finset (EuclideanSpace ℝ (Fin 2)) :=
    fun p => P.filter (fun q => q ∈ UnitCircle (p : EuclideanSpace ℝ (Fin 2)))
  have retained_mem_P : ∀ p : Retained,
      (p : EuclideanSpace ℝ (Fin 2)) ∈ P := by
    intro p
    have hp : (p : EuclideanSpace ℝ (Fin 2)) ∈
        P.filter (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card) := by
      simpa [retainedCenters] using p.2
    exact (Finset.mem_filter.mp hp).1
  have hS_subset : ∀ p : Retained,
      (↑(S p) : Set (EuclideanSpace ℝ (Fin 2))) ⊆
        UnitCircle (p : EuclideanSpace ℝ (Fin 2)) := by
    intro p x hx
    exact (Finset.mem_filter.mp hx).2
  have hS_card : ∀ p : Retained, 3 ≤ (S p).card := by
    intro p
    dsimp [S]
    have hp : (p : EuclideanSpace ℝ (Fin 2)) ∈
        P.filter (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card) := by
      simpa [retainedCenters] using p.2
    exact (Finset.mem_filter.mp hp).2
  have hcircle : ∀ p : Retained,
      ∃ (succ :
          {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p} →
            {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p})
        (carrier arcInterior :
          {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p} →
            Set (EuclideanSpace ℝ (Fin 2)))
        (γ :
          (x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p}) →
            Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
        Function.Bijective succ ∧
          (∀ x, x.1 ≠ (succ x).1) ∧
            (∀ x,
              Continuous (γ x) ∧
                Function.Injective (γ x) ∧
                  (∀ t, γ x t ∈
                    UnitCircle (p : EuclideanSpace ℝ (Fin 2))) ∧
                    γ x ⟨0, by simp⟩ = x.1 ∧
                      γ x ⟨1, by simp⟩ = (succ x).1 ∧
                        carrier x = Set.range (γ x) ∧
                          arcInterior x =
                            Set.range
                              (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                                γ x
                                  ⟨t.1, ⟨le_of_lt t.2.1,
                                    le_of_lt t.2.2⟩⟩)) ∧
              (∀ x y : {y : EuclideanSpace ℝ (Fin 2) // y ∈ S p},
                y.1 ∉ arcInterior x) ∧
                (∀ x y,
                  x ≠ y → arcInterior x ∩ arcInterior y = ∅) ∧
                  (∀ x y,
                    (Sym2.mk x.1 (succ x).1 :
                        Sym2 (EuclideanSpace ℝ (Fin 2))) =
                      Sym2.mk y.1 (succ y).1 →
                      x = y) := by
    intro p
    exact UnitCircleCyclicSuccessorArcs
      (p : EuclideanSpace ℝ (Fin 2)) (S p) (hS_subset p) (hS_card p)
  choose succ carrierOne arcInteriorOne γOne hsucc_bij hsucc_ne hArc
    hNoS hDisjoint hEndpoint using hcircle
  let ι : Type := Sigma (fun p : Retained =>
    {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p})
  let A : Finset ι := Finset.univ
  let center : ι → P := fun i =>
    ⟨(i.1 : EuclideanSpace ℝ (Fin 2)), retained_mem_P i.1⟩
  let arcStart : ι → P := fun i =>
    ⟨i.2.1, (Finset.mem_filter.mp i.2.2).1⟩
  let arcEnd : ι → P := fun i =>
    ⟨(succ i.1 i.2).1, (Finset.mem_filter.mp (succ i.1 i.2).2).1⟩
  let endpoint : ι → Sym2 P := fun i => Sym2.mk (arcStart i) (arcEnd i)
  let carrier : ι → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    carrierOne i.1 i.2
  let arcInterior : ι → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    arcInteriorOne i.1 i.2
  let γ : ι → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) := fun i =>
    γOne i.1 i.2
  have h_card :
      (A.card : ℝ) =
        ∑ p ∈ P.filter
          (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
          ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) := by
    have hnat :
        A.card =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            (P.filter (fun q => q ∈ UnitCircle p)).card := by
      dsimp [A]
      change Fintype.card
          (Sigma (fun p : Retained =>
            {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p})) =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            (P.filter (fun q => q ∈ UnitCircle p)).card
      calc
        Fintype.card
            (Sigma (fun p : Retained =>
              {x : EuclideanSpace ℝ (Fin 2) // x ∈ S p})) =
            ∑ p : Retained, (S p).card := by
              rw [Fintype.card_sigma]
              simp
        _ =
            ∑ p ∈ P.filter
              (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
              (P.filter (fun q => q ∈ UnitCircle p)).card := by
              rw [← Finset.sum_subtype
                (s := P.filter
                  (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card))
                (p := fun p : EuclideanSpace ℝ (Fin 2) => p ∈ retainedCenters)
                (f := fun p => (P.filter (fun q => q ∈ UnitCircle p)).card)]
              intro p
              simpa [retainedCenters]
    exact_mod_cast hnat
  have h_endpoints_distinct : ∀ i ∈ A,
      (arcStart i : EuclideanSpace ℝ (Fin 2)) ≠
        (arcEnd i : EuclideanSpace ℝ (Fin 2)) := by
    intro i hi
    simpa [arcStart, arcEnd] using hsucc_ne i.1 i.2
  have h_nondiag : ∀ i ∈ A, ¬ (endpoint i).IsDiag := by
    intro i hi hdiag
    have hsub : arcStart i = arcEnd i := by
      simpa [endpoint] using
        (Sym2.mk_isDiag_iff (x := arcStart i) (y := arcEnd i)).mp hdiag
    exact h_endpoints_distinct i hi (congrArg Subtype.val hsub)
  have h_endpoint_eq : ∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i) := by
    intro i hi
    rfl
  have h_retained : ∀ i ∈ A,
      3 ≤ (P.filter
        (fun q => q ∈ UnitCircle (center i : EuclideanSpace ℝ (Fin 2)))).card := by
    intro i hi
    simpa [center, S] using hS_card i.1
  have h_endpoints_on_circle : ∀ i ∈ A,
      (arcStart i : EuclideanSpace ℝ (Fin 2)) ∈
          UnitCircle (center i : EuclideanSpace ℝ (Fin 2)) ∧
        (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∈
          UnitCircle (center i : EuclideanSpace ℝ (Fin 2)) := by
    intro i hi
    constructor
    · simpa [arcStart, center, S] using (Finset.mem_filter.mp i.2.2).2
    · simpa [arcEnd, center, S] using
        (Finset.mem_filter.mp (succ i.1 i.2).2).2
  have h_arc_param : ∀ i ∈ A,
      Continuous (γ i) ∧
        Function.Injective (γ i) ∧
          (∀ t, γ i t ∈
            UnitCircle (center i : EuclideanSpace ℝ (Fin 2))) ∧
            γ i ⟨0, by simp⟩ =
              (arcStart i : EuclideanSpace ℝ (Fin 2)) ∧
              γ i ⟨1, by simp⟩ =
                (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∧
                carrier i = Set.range (γ i) ∧
                  arcInterior i =
                    Set.range
                      (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                        γ i
                          ⟨t.1, ⟨le_of_lt t.2.1,
                            le_of_lt t.2.2⟩⟩) := by
    intro i hi
    simpa [γ, carrier, arcInterior, center, arcStart, arcEnd] using hArc i.1 i.2
  have h_carrier_circle : ∀ i ∈ A, carrier i ⊆
      UnitCircle (center i : EuclideanSpace ℝ (Fin 2)) := by
    intro i hi x hx
    rcases hArc i.1 i.2 with ⟨_, _, hcircle_mem, _, _, hcarrier, _⟩
    have hx' : x ∈ carrierOne i.1 i.2 := by simpa [carrier] using hx
    rw [hcarrier] at hx'
    rcases hx' with ⟨t, rfl⟩
    simpa [center] using hcircle_mem t
  have h_no_vertex_in_interior : ∀ i ∈ A, ∀ v : P,
      (v : EuclideanSpace ℝ (Fin 2)) ∉ arcInterior i := by
    intro i hi v hv
    rcases hArc i.1 i.2 with ⟨_, _, hcircle_mem, _, _, _, hinterior⟩
    have hvInteriorOne : (v : EuclideanSpace ℝ (Fin 2)) ∈ arcInteriorOne i.1 i.2 := by
      simpa [arcInterior] using hv
    have hvCircle : (v : EuclideanSpace ℝ (Fin 2)) ∈
        UnitCircle (i.1 : EuclideanSpace ℝ (Fin 2)) := by
      rw [hinterior] at hvInteriorOne
      rcases hvInteriorOne with ⟨t, ht⟩
      rw [← ht]
      exact hcircle_mem
        ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩
    have hvS : (v : EuclideanSpace ℝ (Fin 2)) ∈ S i.1 := by
      exact Finset.mem_filter.mpr ⟨v.2, hvCircle⟩
    exact (hNoS i.1 i.2 ⟨(v : EuclideanSpace ℝ (Fin 2)), hvS⟩)
      (by simpa [arcInterior] using hv)
  have h_same_center_disjoint : ∀ i ∈ A, ∀ j ∈ A,
      center i = center j → i ≠ j →
        arcInterior i ∩ arcInterior j = ∅ := by
    intro i hi j hj hc hij
    cases i with
    | mk p x =>
      cases j with
      | mk q y =>
        have hpq : p = q := by
          have hval : (p : EuclideanSpace ℝ (Fin 2)) =
              (q : EuclideanSpace ℝ (Fin 2)) := by
            simpa [center] using
              congrArg (fun z : P => (z : EuclideanSpace ℝ (Fin 2))) hc
          apply Subtype.ext
          exact hval
        subst q
        have hxy : x ≠ y := by
          intro hxy
          apply hij
          cases hxy
          rfl
        simpa [arcInterior] using hDisjoint p x y hxy
  have h_same_center_endpoint_unique : ∀ i ∈ A, ∀ j ∈ A,
      center i = center j → endpoint i = endpoint j →
        i = j := by
    intro i hi j hj hc hend
    cases i with
    | mk p x =>
      cases j with
      | mk q y =>
        have hpq : p = q := by
          have hval : (p : EuclideanSpace ℝ (Fin 2)) =
              (q : EuclideanSpace ℝ (Fin 2)) := by
            simpa [center] using
              congrArg (fun z : P => (z : EuclideanSpace ℝ (Fin 2))) hc
          apply Subtype.ext
          exact hval
        subst q
        have hamb :
            (Sym2.mk x.1 (succ p x).1 :
                Sym2 (EuclideanSpace ℝ (Fin 2))) =
              Sym2.mk y.1 (succ p y).1 := by
          have hend' :
              (Sym2.mk (arcStart (Sigma.mk p x)) (arcEnd (Sigma.mk p x)) :
                  Sym2 P) =
                Sym2.mk (arcStart (Sigma.mk p y)) (arcEnd (Sigma.mk p y)) := by
            simpa [endpoint] using hend
          rcases (Sym2.eq_iff).mp hend' with hdir | hswap
          · have hstart : x.1 = y.1 := by
              simpa [arcStart] using
                congrArg (fun z : P => (z : EuclideanSpace ℝ (Fin 2))) hdir.1
            have hendp : (succ p x).1 = (succ p y).1 := by
              simpa [arcEnd] using
                congrArg (fun z : P => (z : EuclideanSpace ℝ (Fin 2))) hdir.2
            exact (Sym2.eq_iff).mpr (Or.inl ⟨hstart, hendp⟩)
          · have hstart : x.1 = (succ p y).1 := by
              simpa [arcStart, arcEnd] using
                congrArg (fun z : P => (z : EuclideanSpace ℝ (Fin 2))) hswap.1
            have hendp : (succ p x).1 = y.1 := by
              simpa [arcStart, arcEnd] using
                congrArg (fun z : P => (z : EuclideanSpace ℝ (Fin 2))) hswap.2
            exact (Sym2.eq_iff).mpr (Or.inr ⟨hstart, hendp⟩)
        have hxy : x = y := hEndpoint p x y hamb
        cases hxy
        rfl
  have h_multiplicity : ∀ e ∈ A.image endpoint,
      (A.filter (fun i => endpoint i = e)).card ≤ 2 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨i0, hi0A, hi0e⟩
    let a : P := arcStart i0
    let b : P := arcEnd i0
    have hab : (a : EuclideanSpace ℝ (Fin 2)) ≠
        (b : EuclideanSpace ℝ (Fin 2)) := by
      simpa [a, b] using h_endpoints_distinct i0 hi0A
    let F : Finset ι := A.filter (fun i => endpoint i = e)
    have hcenter_inj : Set.InjOn
        (fun i : ι => (center i : EuclideanSpace ℝ (Fin 2))) (↑F : Set ι) := by
      intro i hi j hj hc
      have hiF : i ∈ F := by simpa using hi
      have hjF : j ∈ F := by simpa using hj
      have hiF' : i ∈ A.filter (fun k : ι => endpoint k = e) := by
        simpa only [F] using hiF
      have hjF' : j ∈ A.filter (fun k : ι => endpoint k = e) := by
        simpa only [F] using hjF
      have hiA : i ∈ A := (Finset.mem_filter.mp hiF').1
      have hjA : j ∈ A := (Finset.mem_filter.mp hjF').1
      have hie : endpoint i = e := (Finset.mem_filter.mp hiF').2
      have hje : endpoint j = e := (Finset.mem_filter.mp hjF').2
      have hc' : center i = center j := Subtype.ext hc
      exact h_same_center_endpoint_unique i hiA j hjA hc' (hie.trans hje.symm)
    have circle_symm (c v : P)
        (h : (v : EuclideanSpace ℝ (Fin 2)) ∈
            UnitCircle (c : EuclideanSpace ℝ (Fin 2))) :
        (c : EuclideanSpace ℝ (Fin 2)) ∈
            UnitCircle (v : EuclideanSpace ℝ (Fin 2)) := by
      simpa [UnitCircle, dist_comm] using h
    have hmaps : ∀ i ∈ (↑F : Set ι),
        (center i : EuclideanSpace ℝ (Fin 2)) ∈
          {x : EuclideanSpace ℝ (Fin 2) |
            x ∈ UnitCircle (a : EuclideanSpace ℝ (Fin 2)) ∧
              x ∈ UnitCircle (b : EuclideanSpace ℝ (Fin 2))} := by
      intro i hi
      have hiF : i ∈ F := by simpa using hi
      have hiF' : i ∈ A.filter (fun k : ι => endpoint k = e) := by
        simpa only [F] using hiF
      have hiA : i ∈ A := (Finset.mem_filter.mp hiF').1
      have hie : endpoint i = e := (Finset.mem_filter.mp hiF').2
      have hiEndpoint :
          (Sym2.mk (arcStart i) (arcEnd i) : Sym2 P) = Sym2.mk a b := by
        calc
          (Sym2.mk (arcStart i) (arcEnd i) : Sym2 P) = endpoint i := by
            exact (h_endpoint_eq i hiA).symm
          _ = e := hie
          _ = endpoint i0 := hi0e.symm
          _ = Sym2.mk a b := by
            simpa [a, b] using h_endpoint_eq i0 hi0A
      rcases h_endpoints_on_circle i hiA with ⟨hstart_circle, hend_circle⟩
      rcases (Sym2.eq_iff).mp hiEndpoint with hdir | hswap
      · have hca : (center i : EuclideanSpace ℝ (Fin 2)) ∈
            UnitCircle (a : EuclideanSpace ℝ (Fin 2)) := by
          have hstart : arcStart i = a := hdir.1
          simpa [hstart] using circle_symm (center i) (arcStart i) hstart_circle
        have hcb : (center i : EuclideanSpace ℝ (Fin 2)) ∈
            UnitCircle (b : EuclideanSpace ℝ (Fin 2)) := by
          have hendp : arcEnd i = b := hdir.2
          simpa [hendp] using circle_symm (center i) (arcEnd i) hend_circle
        exact ⟨hca, hcb⟩
      · have hca : (center i : EuclideanSpace ℝ (Fin 2)) ∈
            UnitCircle (a : EuclideanSpace ℝ (Fin 2)) := by
          have hendp : arcEnd i = a := hswap.2
          simpa [hendp] using circle_symm (center i) (arcEnd i) hend_circle
        have hcb : (center i : EuclideanSpace ℝ (Fin 2)) ∈
            UnitCircle (b : EuclideanSpace ℝ (Fin 2)) := by
          have hstart : arcStart i = b := hswap.1
          simpa [hstart] using circle_symm (center i) (arcStart i) hstart_circle
        exact ⟨hca, hcb⟩
    have htwo := UnitCirclesIntersectionsAtMostTwo
      (a : EuclideanSpace ℝ (Fin 2)) (b : EuclideanSpace ℝ (Fin 2)) hab
    have hle_ncard :
        (↑F : Set ι).ncard ≤
          ({x : EuclideanSpace ℝ (Fin 2) |
            x ∈ UnitCircle (a : EuclideanSpace ℝ (Fin 2)) ∧
              x ∈ UnitCircle (b : EuclideanSpace ℝ (Fin 2))}.ncard) :=
      Set.ncard_le_ncard_of_injOn
        (fun i : ι => (center i : EuclideanSpace ℝ (Fin 2)))
        hmaps hcenter_inj htwo.1
    calc
      (A.filter (fun i => endpoint i = e)).card = F.card := by rfl
      _ = (↑F : Set ι).ncard := by simp
      _ ≤ ({x : EuclideanSpace ℝ (Fin 2) |
            x ∈ UnitCircle (a : EuclideanSpace ℝ (Fin 2)) ∧
              x ∈ UnitCircle (b : EuclideanSpace ℝ (Fin 2))}.ncard) := hle_ncard
      _ ≤ 2 := htwo.2
  refine ⟨ι, inferInstance, inferInstance, A, endpoint, center, arcStart, arcEnd,
    carrier, arcInterior, γ, h_card, h_nondiag, h_multiplicity, h_retained,
    h_endpoint_eq, h_endpoints_distinct, h_endpoints_on_circle, h_arc_param,
    h_carrier_circle, h_no_vertex_in_interior, h_same_center_disjoint,
    h_same_center_endpoint_unique⟩

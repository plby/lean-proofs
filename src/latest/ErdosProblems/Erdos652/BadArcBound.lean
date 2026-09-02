import ErdosProblems.Erdos652.PerpendicularBisectors
import ErdosProblems.Erdos652.PinnedCircles
import Util.IncidenceGeometry.LineIncidences

open scoped BigOperators Real
noncomputable section

namespace Erdos652

open Classical in
/-- Arcs whose unordered endpoint pair occurs at least twice are controlled by
incidences of their centers with the corresponding perpendicular bisectors. -/
lemma repeatedEndpointArcCard_le
    (P Q : Finset Point) (t : ℕ)
    {ι : Type} [Finite ι]
    (A : Finset ι) (endpoint : ι → Sym2 Q)
    (center : ι → circleKeys P Q)
    (arcStart arcEnd : ι → Q)
    (arcInterior : ι → Set Point)
    (γ : ι → Set.Icc (0 : ℝ) 1 → Point)
    (ht : ∀ p ∈ P, (distanceRadii p Q).card ≤ t)
    (h_endpoint_eq : ∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i))
    (h_endpoints_distinct : ∀ i ∈ A,
      (arcStart i : Point) ≠ (arcEnd i : Point))
    (h_endpoints_on_circle : ∀ i ∈ A,
      (arcStart i : Point) ∈ circle (center i : CircleKey) ∧
        (arcEnd i : Point) ∈ circle (center i : CircleKey))
    (h_arc_param : ∀ i ∈ A,
      Continuous (γ i) ∧ Function.Injective (γ i) ∧
        (∀ u, γ i u ∈ circle (center i : CircleKey)) ∧
          γ i ⟨0, by simp⟩ = (arcStart i : Point) ∧
            γ i ⟨1, by simp⟩ = (arcEnd i : Point) ∧
              arcInterior i = Set.range
                (fun u : {u : ℝ // 0 < u ∧ u < 1} =>
                  γ i ⟨u.1, ⟨le_of_lt u.2.1, le_of_lt u.2.2⟩⟩))
    (h_same_center_disjoint : ∀ i ∈ A, ∀ j ∈ A,
      center i = center j → i ≠ j →
        arcInterior i ∩ arcInterior j = ∅)
    (h_same_center_unique : ∀ i ∈ A, ∀ j ∈ A,
      center i = center j → endpoint i = endpoint j → i = j)
    (L : Finset {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ})
    (hLmem : ∀ ℓ, ℓ ∈ L ↔
      2 ≤ (P.filter (fun p => p ∈ (ℓ.1 : AffineSubspace ℝ Point))).card) :
    (A.filter (fun i =>
      2 ≤ (A.filter (fun j => endpoint j = endpoint i)).card)).card ≤
      2 * t * LineIncidences P L := by
  let B : Finset ι := A.filter (fun i =>
    2 ≤ (A.filter (fun j => endpoint j = endpoint i)).card)
  let Bad := {i : ι // i ∈ B}
  let U : Finset Bad := Finset.univ
  have hBadA (i : Bad) : i.1 ∈ A :=
    (Finset.mem_filter.mp i.2).1
  have hBadTwo (i : Bad) :
      2 ≤ (A.filter (fun j => endpoint j = endpoint i.1)).card :=
    (Finset.mem_filter.mp i.2).2
  let rawLine (i : Bad) : AffineSubspace ℝ Point :=
    AffineSubspace.perpBisector (arcStart i.1 : Point) (arcEnd i.1 : Point)
  let lineOf (i : Bad) : {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ} :=
    ⟨rawLine i, perpBisector_isAffineLine (h_endpoints_distinct i.1 (hBadA i))⟩
  have rawLine_eq_of_endpoint_eq (i j : Bad)
      (hij : endpoint i.1 = endpoint j.1) : rawLine i = rawLine j := by
    have hm : (Sym2.mk (arcStart i.1) (arcEnd i.1) : Sym2 Q) =
        Sym2.mk (arcStart j.1) (arcEnd j.1) := by
      rw [← h_endpoint_eq i.1 (hBadA i), ← h_endpoint_eq j.1 (hBadA j)]
      exact hij
    rcases (Sym2.rel_iff.mp (Sym2.exact hm)) with h | h
    · rcases h with ⟨hs, he⟩
      simp only [rawLine]
      rw [congrArg Subtype.val hs, congrArg Subtype.val he]
    · rcases h with ⟨hs, he⟩
      simp only [rawLine]
      rw [congrArg Subtype.val hs, congrArg Subtype.val he]
      exact AffineSubspace.perpBisector_comm _ _
  have center_key_ne_of_ne_of_endpoint_eq (i j : Bad) (hij : i ≠ j)
      (he : endpoint i.1 = endpoint j.1) : center i.1 ≠ center j.1 := by
    intro hc
    apply hij
    apply Subtype.ext
    exact h_same_center_unique i.1 (hBadA i) j.1 (hBadA j) hc he
  have center_point_ne_of_ne_of_endpoint_eq (i j : Bad) (hij : i ≠ j)
      (he : endpoint i.1 = endpoint j.1) :
      (center i.1 : CircleKey).1 ≠ (center j.1 : CircleKey).1 := by
    intro hp
    have hm : (Sym2.mk (arcStart i.1) (arcEnd i.1) : Sym2 Q) =
        Sym2.mk (arcStart j.1) (arcEnd j.1) := by
      rw [← h_endpoint_eq i.1 (hBadA i), ← h_endpoint_eq j.1 (hBadA j)]
      exact he
    rcases (Sym2.rel_iff.mp (Sym2.exact hm)) with h | h
    · rcases h with ⟨hs, _he⟩
      have hi := (h_endpoints_on_circle i.1 (hBadA i)).1
      have hj := (h_endpoints_on_circle j.1 (hBadA j)).1
      have hr : (center i.1 : CircleKey).2 = (center j.1 : CircleKey).2 := by
        rw [mem_circle] at hi hj
        calc
          (center i.1 : CircleKey).2 = dist (arcStart i.1 : Point)
              (center i.1 : CircleKey).1 := hi.symm
          _ = dist (arcStart j.1 : Point) (center j.1 : CircleKey).1 := by
            rw [congrArg Subtype.val hs, hp]
          _ = (center j.1 : CircleKey).2 := hj
      exact center_key_ne_of_ne_of_endpoint_eq i j hij he
        (Subtype.ext (Prod.ext hp hr))
    · rcases h with ⟨hs, _he⟩
      have hi := (h_endpoints_on_circle i.1 (hBadA i)).1
      have hj := (h_endpoints_on_circle j.1 (hBadA j)).2
      have hr : (center i.1 : CircleKey).2 = (center j.1 : CircleKey).2 := by
        rw [mem_circle] at hi hj
        calc
          (center i.1 : CircleKey).2 = dist (arcStart i.1 : Point)
              (center i.1 : CircleKey).1 := hi.symm
          _ = dist (arcEnd j.1 : Point) (center j.1 : CircleKey).1 := by
            rw [congrArg Subtype.val hs, hp]
          _ = (center j.1 : CircleKey).2 := hj
      exact center_key_ne_of_ne_of_endpoint_eq i j hij he
        (Subtype.ext (Prod.ext hp hr))
  have center_mem_line (i j : Bad) (he : endpoint j.1 = endpoint i.1) :
      (center j.1 : CircleKey).1 ∈ rawLine i := by
    have hj := h_endpoints_on_circle j.1 (hBadA j)
    have heq : dist (center j.1 : CircleKey).1 (arcStart j.1 : Point) =
        dist (center j.1 : CircleKey).1 (arcEnd j.1 : Point) := by
      rw [dist_comm, dist_comm (center j.1 : CircleKey).1]
      simpa [mem_circle] using hj.1.trans hj.2.symm
    have hjmem : (center j.1 : CircleKey).1 ∈ rawLine j :=
      AffineSubspace.mem_perpBisector_iff_dist_eq.mpr heq
    rwa [rawLine_eq_of_endpoint_eq j i he] at hjmem
  have lineOf_mem_L (i : Bad) : lineOf i ∈ L := by
    apply (hLmem (lineOf i)).mpr
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by
      simpa only [Nat.lt_iff_add_one_le] using hBadTwo i)
    let ai : Bad := ⟨a, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp ha).1, by
        simpa [(Finset.mem_filter.mp ha).2] using hBadTwo i⟩⟩
    let bi : Bad := ⟨b, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hb).1, by
        simpa [(Finset.mem_filter.mp hb).2] using hBadTwo i⟩⟩
    have hae : endpoint ai.1 = endpoint i.1 := (Finset.mem_filter.mp ha).2
    have hbe : endpoint bi.1 = endpoint i.1 := (Finset.mem_filter.mp hb).2
    have hab' : ai ≠ bi := by
      intro h
      exact hab (congrArg Subtype.val h)
    have hpne := center_point_ne_of_ne_of_endpoint_eq ai bi hab' (hae.trans hbe.symm)
    apply Finset.one_lt_card.mpr
    refine ⟨(center ai.1 : CircleKey).1, ?_,
      (center bi.1 : CircleKey).1, ?_, hpne⟩
    · apply Finset.mem_filter.mpr
      exact ⟨(mem_circleKeys_iff.mp (center ai.1).2).1,
        center_mem_line i ai hae⟩
    · apply Finset.mem_filter.mpr
      exact ⟨(mem_circleKeys_iff.mp (center bi.1).2).1,
        center_mem_line i bi hbe⟩
  have hmeet (i : Bad) : ∃ u : {u : ℝ // 0 < u ∧ u < 1},
      γ i.1 ⟨u.1, ⟨le_of_lt u.2.1, le_of_lt u.2.2⟩⟩ ∈ rawLine i := by
    rcases h_arc_param i.1 (hBadA i) with ⟨hc, _, _, hs, he, _⟩
    exact path_meets_perpBisector_interior
      (h_endpoints_distinct i.1 (hBadA i)) (γ i.1) hc hs he
  let crossParam (i : Bad) : {u : ℝ // 0 < u ∧ u < 1} := (hmeet i).choose
  let crossPoint (i : Bad) : Point :=
    γ i.1 ⟨(crossParam i).1,
      ⟨le_of_lt (crossParam i).2.1, le_of_lt (crossParam i).2.2⟩⟩
  have cross_mem_line (i : Bad) : crossPoint i ∈ rawLine i :=
    (hmeet i).choose_spec
  have cross_mem_interior (i : Bad) : crossPoint i ∈ arcInterior i.1 := by
    rw [(h_arc_param i.1 (hBadA i)).2.2.2.2.2]
    exact Set.mem_range_self (crossParam i)
  have cross_mem_circle (i : Bad) :
      crossPoint i ∈ circle (center i.1 : CircleKey) :=
    (h_arc_param i.1 (hBadA i)).2.2.1 _
  have cross_ne_of_same_center (i j : Bad) (hc : center i.1 = center j.1)
      (hij : i ≠ j) : crossPoint i ≠ crossPoint j := by
    intro heq
    have hboth : crossPoint i ∈ arcInterior i.1 ∩ arcInterior j.1 :=
      ⟨cross_mem_interior i, by simpa [heq] using cross_mem_interior j⟩
    have hd := h_same_center_disjoint i.1 (hBadA i) j.1 (hBadA j) hc (by
      intro h
      exact hij (Subtype.ext h))
    simp [hd] at hboth
  have keyLineFiber_card_le_two
      (S : Finset Bad) (k : circleKeys P Q)
      (ℓ : {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ})
      (hk : ∀ i ∈ S, center i.1 = k)
      (hline : ∀ i ∈ S, lineOf i = ℓ) : S.card ≤ 2 := by
    by_contra hnot
    obtain ⟨i, hi, j, hj, z, hz, hij, hiz, hjz⟩ :=
      Finset.two_lt_card.mp (lt_of_not_ge hnot)
    have hcij : center i.1 = center j.1 := (hk i hi).trans (hk j hj).symm
    have hciz : center i.1 = center z.1 := (hk i hi).trans (hk z hz).symm
    have hcjz : center j.1 = center z.1 := (hk j hj).trans (hk z hz).symm
    have hil : crossPoint i ∈ ℓ.1 := by
      have := cross_mem_line i
      change crossPoint i ∈ (lineOf i).1 at this
      rwa [hline i hi] at this
    have hjl : crossPoint j ∈ ℓ.1 := by
      have := cross_mem_line j
      change crossPoint j ∈ (lineOf j).1 at this
      rwa [hline j hj] at this
    have hzl : crossPoint z ∈ ℓ.1 := by
      have := cross_mem_line z
      change crossPoint z ∈ (lineOf z).1 at this
      rwa [hline z hz] at this
    exact affineLine_circle_no_three ℓ.2 hil hjl hzl
      (by simpa [mem_circle, hk i hi] using cross_mem_circle i)
      (by simpa [mem_circle, hk j hj] using cross_mem_circle j)
      (by simpa [mem_circle, hk z hz] using cross_mem_circle z)
      (cross_ne_of_same_center i j hcij hij)
      (cross_ne_of_same_center i z hciz hiz)
      (cross_ne_of_same_center j z hcjz hjz)
  let base (i : Bad) : Point × {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ} :=
    ((center i.1 : CircleKey).1, lineOf i)
  have base_mem_incidence (i : Bad) :
      base i ∈ (P.product L).filter (fun pℓ =>
        pℓ.1 ∈ (pℓ.2.1 : AffineSubspace ℝ Point)) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨(mem_circleKeys_iff.mp (center i.1).2).1, lineOf_mem_L i⟩, ?_⟩
    exact center_mem_line i i rfl
  have baseFiber_card_le
      (b : Point × {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ})
      (hbP : b.1 ∈ P) :
      (U.filter (fun i => base i = b)).card ≤ 2 * t := by
    let F := U.filter (fun i => base i = b)
    have hcenterImage : (F.image (fun i => center i.1)).card ≤ t := by
      have hvalinj : Set.InjOn (fun k : circleKeys P Q => (k : CircleKey))
          ((F.image fun i => center i.1 : Finset (circleKeys P Q)) : Set _) :=
        fun _ _ _ _ h => Subtype.ext h
      have hcardeq : (F.image (fun i => center i.1)).card =
          ((F.image (fun i => center i.1)).image
            (fun k : circleKeys P Q => (k : CircleKey))).card := by
        symm
        exact Finset.card_image_iff.mpr hvalinj
      rw [hcardeq]
      calc
        ((F.image (fun i => center i.1)).image
            (fun k : circleKeys P Q => (k : CircleKey))).card ≤
            ((circleKeys P Q).filter (fun k => k.1 = b.1)).card := by
          apply Finset.card_le_card
          intro k hk
          rcases Finset.mem_image.mp hk with ⟨ck, hck, rfl⟩
          rcases Finset.mem_image.mp hck with ⟨i, hi, rfl⟩
          apply Finset.mem_filter.mpr
          refine ⟨(center i.1).2, ?_⟩
          have hbase := (Finset.mem_filter.mp hi).2
          exact congrArg Prod.fst hbase
        _ ≤ (distanceRadii b.1 Q).card :=
          circleKeys_fixed_center_card_le P Q b.1
        _ ≤ t := ht b.1 hbP
    have hsum : F.card = ∑ k ∈ F.image (fun i => center i.1),
        (F.filter (fun i => center i.1 = k)).card := by
      simpa using Finset.card_eq_sum_card_image (fun i : Bad => center i.1) F
    rw [show (U.filter (fun i => base i = b)).card = F.card by rfl, hsum]
    calc
      ∑ k ∈ F.image (fun i => center i.1),
          (F.filter (fun i => center i.1 = k)).card ≤
          ∑ _k ∈ F.image (fun i => center i.1), 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply keyLineFiber_card_le_two
        · intro i hi
          exact (Finset.mem_filter.mp hi).2
        · intro i hi
          have hbase := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
          exact congrArg Prod.snd hbase
      _ = 2 * (F.image (fun i => center i.1)).card := by
        simp [Nat.mul_comm]
      _ ≤ 2 * t := Nat.mul_le_mul_left 2 hcenterImage
  have hUcard : U.card = ∑ b ∈ U.image base,
      (U.filter (fun i => base i = b)).card := by
    simpa using Finset.card_eq_sum_card_image base U
  have himage : (U.image base).card ≤ LineIncidences P L := by
    rw [LineIncidences]
    apply Finset.card_le_card
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
    exact base_mem_incidence i
  calc
    B.card = U.card := by simp [U, Bad]
    _ = ∑ b ∈ U.image base, (U.filter (fun i => base i = b)).card := hUcard
    _ ≤ ∑ _b ∈ U.image base, 2 * t := by
      exact Finset.sum_le_sum (fun b hb => baseFiber_card_le b (by
        rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
        exact (mem_circleKeys_iff.mp (center i.1).2).1))
    _ = 2 * t * (U.image base).card := by simp [Nat.mul_comm]
    _ ≤ 2 * t * LineIncidences P L := Nat.mul_le_mul_left _ himage
    _ = 2 * t * LineIncidences P L := rfl

end Erdos652

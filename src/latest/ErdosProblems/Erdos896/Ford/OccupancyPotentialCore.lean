/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OccupancyCount
import ErdosProblems.Erdos896.Ford.Abel
import ErdosProblems.Erdos896.Ford.GeneralizedParkingUpper

/-!
# The exponential potential of a good occupancy (core estimates)

This file isolates the extra condition used in Ford's Lemma 4.9.  If the
first `j` boxes contain `N j` balls, its contribution is `2 ^ (N j - j)`.
For a placement below the diagonal all these contributions are at most one,
but that pointwise observation is not uniform in the number of boxes.  The
useful estimate is instead a finite first-moment bound, followed by Markov's
inequality.
-/

namespace Erdos896.Ford.Occupancy

open scoped BigOperators

/-- The number of balls in the boxes from `0` through `j` (inclusive). -/
def prefixOccupancy {v : ℕ} (f : Fin v → Fin v) (j : Fin v) : ℕ :=
  ((occupancyList f).take (j.1 + 1)).sum

/-- The same prefix count, in the form best suited to finite counting. -/
def cumulativeOccupancy {v : ℕ} (f : Fin v → Fin v) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i ↦ (f i).val < k).card

theorem sum_take_occupancyList_eq_cumulative {v : ℕ}
    (f : Fin v → Fin v) {k : ℕ} (hk : k ≤ v) :
    ((occupancyList f).take k).sum = cumulativeOccupancy f k := by
  induction k with
  | zero => simp [cumulativeOccupancy]
  | succ k ih =>
      have hklt : k < v := by omega
      have ih' := ih (by omega)
      let A := (Finset.univ.filter fun i : Fin v ↦ (f i).val < k)
      let B := (Finset.univ.filter fun i : Fin v ↦ (f i).val = k)
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro i hiA hiB
        simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
        omega
      have hunion :
          (Finset.univ.filter fun i : Fin v ↦ (f i).val < k + 1) = A ∪ B := by
        ext i
        simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        omega
      have hkocc : k < (occupancyList f).length := by simpa using hklt
      rw [List.sum_take_succ (occupancyList f) k (by simpa using hklt), ih']
      change A.card + (occupancyList f)[k]'hkocc =
        (Finset.univ.filter fun i : Fin v ↦ (f i).val < k + 1).card
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      congr 1
      simp only [occupancyList, List.getElem_ofFn, boxOccupancy, B]
      congr 1
      ext i
      simp [Fin.ext_iff]

@[simp]
theorem prefixOccupancy_eq_cumulative {v : ℕ} (f : Fin v → Fin v)
    (j : Fin v) :
    prefixOccupancy f j = cumulativeOccupancy f (j.1 + 1) := by
  exact sum_take_occupancyList_eq_cumulative f (by omega)

/-- Ford's exponential prefix potential. -/
def expPotential {v : ℕ} (f : Fin v → Fin v) : ℚ :=
  ∑ j : Fin v,
    (2 : ℚ) ^ prefixOccupancy f j / (2 : ℚ) ^ (j.1 + 1)

/-- A good placement whose exponential prefix potential is bounded by `B`. -/
def GoodPotential {v : ℕ} (B : ℚ) (f : Fin v → Fin v) : Prop :=
  Good f ∧ expPotential f ≤ B

noncomputable instance {v : ℕ} (B : ℚ) :
    DecidablePred (@GoodPotential v B) :=
  Classical.decPred _

theorem prefixOccupancy_le {v : ℕ} {f : Fin v → Fin v}
    (hf : Good f) (j : Fin v) :
    prefixOccupancy f j ≤ j.1 + 1 := by
  exact hf (j.1 + 1) (by simpa using j.isLt)

theorem expPotential_nonneg {v : ℕ} (f : Fin v → Fin v) :
    0 ≤ expPotential f := by
  unfold expPotential
  positivity

/-- The elementary bound supplied by the ballot condition alone.  The
moment argument below is what removes its dependence on `v`. -/
theorem expPotential_le_card {v : ℕ} {f : Fin v → Fin v}
    (hf : Good f) : expPotential f ≤ v := by
  unfold expPotential
  calc
    (∑ j : Fin v,
        (2 : ℚ) ^ prefixOccupancy f j / (2 : ℚ) ^ (j.1 + 1)) ≤
        ∑ _j : Fin v, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [div_le_one (by positivity : (0 : ℚ) < (2 : ℚ) ^ (j.1 + 1))]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        (prefixOccupancy_le hf j)
    _ = v := by simp

/-! ## Finite Markov inequality -/

/-- Elementary counting form of Markov's inequality over `ℚ`. -/
theorem counting_markov_rat {Ω : Type*} [Fintype Ω]
    (g : Ω → ℚ) (c : ℚ) (hc : 0 < c)
    (hg : ∀ ω, 0 ≤ g ω) :
    ((Finset.univ.filter fun ω ↦ c ≤ g ω).card : ℚ) * c ≤
      ∑ ω, g ω := by
  have h := Finset.sum_le_sum fun x (_hx : x ∈ (Finset.univ : Finset Ω)) ↦
    show (if c ≤ g x then c else 0) ≤ g x by
      split_ifs <;> linarith [hg x]
  simpa [Finset.sum_ite] using h

/-! ## Cutting a good occupancy -/

/-- The event that a good path has deficit exactly `d` after `k` boxes. -/
def CutEvent {v : ℕ} (k d : ℕ) (f : Fin v → Fin v) : Prop :=
  Good f ∧ cumulativeOccupancy f k + d = k

noncomputable instance {v : ℕ} (k d : ℕ) :
    DecidablePred (@CutEvent v k d) :=
  Classical.decPred _

theorem cumulativeOccupancy_le {v : ℕ} {f : Fin v → Fin v}
    (hf : Good f) {k : ℕ} (hk : k ≤ v) :
    cumulativeOccupancy f k ≤ k := by
  rw [← sum_take_occupancyList_eq_cumulative f hk]
  exact hf k (by simpa using hk)

private def cutSet {v : ℕ} (f : Fin v → Fin v) (k : ℕ) : Finset (Fin v) :=
  Finset.univ.filter fun i ↦ (f i).val < k

@[simp]
private theorem card_cutSet {v : ℕ} (f : Fin v → Fin v) (k : ℕ) :
    (cutSet f k).card = cumulativeOccupancy f k := by
  rfl

private theorem card_filter_orderIsoOfFin
    {α : Type*} [Fintype α] [LinearOrder α]
    (S : Finset α) {n : ℕ} (hS : S.card = n) (p : α → Prop)
    [DecidablePred p] :
    ((Finset.univ : Finset (Fin n)).filter fun i ↦
        p (Finset.orderIsoOfFin S hS i)).card = (S.filter p).card := by
  let e := Finset.orderIsoOfFin S hS
  apply Finset.card_bij
      (fun i _hi ↦ (e i).val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨(e i).property, hi⟩
  · intro i₁ hi₁ i₂ hi₂ heq
    exact e.injective (Subtype.ext heq)
  · intro x hx
    simp only [Finset.mem_filter] at hx
    let y : Fin n := e.symm ⟨x, hx.1⟩
    refine ⟨y, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, y]
      have he : e (e.symm ⟨x, hx.1⟩) = ⟨x, hx.1⟩ := e.apply_symm_apply _
      rw [he]
      exact hx.2
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx.1⟩)

private theorem card_cutSubset (v m : ℕ) :
    Fintype.card {S : Finset (Fin v) // S.card = m} = v.choose m := by
  rw [Fintype.card_subtype]
  rw [show ((Finset.univ : Finset (Finset (Fin v))).filter
      fun S ↦ S.card = m) =
      Finset.powersetCard m (Finset.univ : Finset (Fin v)) by
    ext S
    simp [Finset.mem_powersetCard]]
  simp

/-- Cutting at a prescribed positive interior deficit embeds the placement
into a choice of labels and two independent generalized parking words. -/
private theorem card_cutEvent_le_parking_product
    {v k d : ℕ} (hd : d ≤ k) (hm : 0 < k - d) (hk : k < v) :
    (Finset.univ.filter (@CutEvent v k d)).card ≤
      v.choose (k - d) *
        (Finset.univ.filter
          (@Erdos896.Ford.generalizedParkingGood (k - d) 1 (d + 1))).card *
        (Finset.univ.filter
          (@Erdos896.Ford.generalizedParkingGood (v - (k - d)) (d + 1) 1)).card := by
  classical
  let E := {f : Fin v → Fin v // CutEvent k d f}
  let A := {a : Fin (k - d) → Fin ((k - d) - 1 + (d + 1)) //
    Erdos896.Ford.generalizedParkingGood (k - d) 1 (d + 1) a}
  let B := {b : Fin (v - (k - d)) →
      Fin ((v - (k - d)) - (d + 1) + 1) //
    Erdos896.Ford.generalizedParkingGood (v - (k - d)) (d + 1) 1 b}
  let C := {S : Finset (Fin v) // S.card = k - d}
  have hAbox : (k - d) - 1 + (d + 1) = k := by omega
  have hBbox : (v - (k - d)) - (d + 1) + 1 = v - k := by omega
  let encode : E → C × A × B := fun x ↦ by
    let S := cutSet x.1 k
    have hS : S.card = k - d := by
      have hx := x.2.2
      rw [card_cutSet]
      omega
    let eA := Finset.orderIsoOfFin S hS
    have hScard : Sᶜ.card = v - (k - d) := by
      rw [Finset.card_compl, hS]
      simp
    let eB := Finset.orderIsoOfFin Sᶜ hScard
    let a : Fin (k - d) → Fin ((k - d) - 1 + (d + 1)) := fun i ↦
      Fin.cast hAbox.symm ⟨(x.1 (eA i)).val, by
        have hi := (eA i).property
        simpa only [S, cutSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩
    let b : Fin (v - (k - d)) →
        Fin ((v - (k - d)) - (d + 1) + 1) := fun i ↦
      Fin.cast hBbox.symm ⟨(x.1 (eB i)).val - k, by
        have hi := (eB i).property
        have hnot : ¬ (x.1 (eB i)).val < k := by
          simpa only [S, cutSet, Finset.mem_compl, Finset.mem_filter,
            Finset.mem_univ, true_and, not_lt] using hi
        omega⟩
    have ha : Erdos896.Ford.generalizedParkingGood (k - d) 1 (d + 1) a := by
      intro r
      have hrk : r.val < k := by omega
      have hfilter :
          ((Finset.univ : Finset (Fin (k - d))).filter fun i ↦
              (a i).val < r.val).card =
            (Finset.univ.filter fun i : Fin v ↦ (x.1 i).val < r.val).card := by
        calc
          ((Finset.univ : Finset (Fin (k - d))).filter fun i ↦
              (a i).val < r.val).card =
              (S.filter fun i ↦ (x.1 i).val < r.val).card := by
                simpa only [a, eA, Fin.val_cast] using
                  card_filter_orderIsoOfFin S hS
                    (fun i ↦ (x.1 i).val < r.val)
          _ = (Finset.univ.filter fun i : Fin v ↦
                (x.1 i).val < r.val).card := by
              congr 1
              ext i
              simp only [S, cutSet, Finset.mem_filter, Finset.mem_univ,
                true_and]
              omega
      rw [hfilter]
      have hg := cumulativeOccupancy_le x.2.1 (show r.val ≤ v by omega)
      change cumulativeOccupancy x.1 r.val ≤ 1 + r.val - 1
      simpa using hg
    have hb : Erdos896.Ford.generalizedParkingGood
        (v - (k - d)) (d + 1) 1 b := by
      intro r
      let T := Sᶜ.filter fun i ↦ (x.1 i).val < k + r.val
      have hfilter :
          ((Finset.univ : Finset (Fin (v - (k - d)))).filter fun i ↦
              (b i).val < r.val).card = T.card := by
        calc
          ((Finset.univ : Finset (Fin (v - (k - d)))).filter fun i ↦
              (b i).val < r.val).card =
              (Sᶜ.filter fun i ↦ (x.1 i).val - k < r.val).card := by
                simpa only [b, eB, Fin.val_cast] using
                  card_filter_orderIsoOfFin Sᶜ hScard
                    (fun i ↦ (x.1 i).val - k < r.val)
          _ = (Sᶜ.filter fun i ↦ (x.1 i).val < k + r.val).card := by
              congr 1
              ext i
              simp only [Finset.mem_filter, Finset.mem_compl]
              constructor
              · rintro ⟨hi, hir⟩
                refine ⟨hi, ?_⟩
                have hik : k ≤ (x.1 i).val := by
                  simpa only [S, cutSet, Finset.mem_filter, Finset.mem_univ,
                    true_and, not_lt] using hi
                omega
              · rintro ⟨hi, hir⟩
                refine ⟨hi, ?_⟩
                have hik : k ≤ (x.1 i).val := by
                  simpa only [S, cutSet, Finset.mem_filter, Finset.mem_univ,
                    true_and, not_lt] using hi
                omega
          _ = T.card := rfl
      rw [hfilter]
      have hdisj : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro i hiS hiT
        exact (Finset.mem_compl.mp (Finset.mem_of_mem_filter i hiT)) hiS
      have hsub : S ∪ T ⊆
          Finset.univ.filter fun i : Fin v ↦ (x.1 i).val < k + r.val := by
        intro i hi
        rcases Finset.mem_union.mp hi with hiS | hiT
        · have hi' : (x.1 i).val < k := by
            simpa only [S, cutSet, Finset.mem_filter, Finset.mem_univ,
              true_and] using hiS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hiT).2⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, hS] at hcard
      change (k - d) + T.card ≤ cumulativeOccupancy x.1 (k + r.val) at hcard
      have hcum := cumulativeOccupancy_le x.2.1
        (show k + r.val ≤ v by omega)
      change T.card ≤ d + 1 + r.val - 1
      omega
    exact ⟨⟨S, hS⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩
  have hencode : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hS : cutSet x.1 k = cutSet y.1 k := by
      exact congrArg (fun z : C × A × B ↦ z.1.val) hxy
    by_cases hi : i ∈ cutSet x.1 k
    · have hiy : i ∈ cutSet y.1 k := by simpa [← hS] using hi
      have hAeq := congrArg (fun z : C × A × B ↦ z.2.1.val) hxy
      have hxcard : (cutSet x.1 k).card = k - d := by
        rw [card_cutSet]
        have hx := x.2.2
        omega
      let ex := Finset.orderIsoOfFin (cutSet x.1 k) hxcard
      let t : Fin (k - d) := ex.symm ⟨i, hi⟩
      have ht := congrFun hAeq t
      have exi : (ex t).val = i := by
        exact congrArg Subtype.val (ex.apply_symm_apply ⟨i, hi⟩)
      have hycard : (cutSet y.1 k).card = k - d := by
        rw [card_cutSet]
        have hy := y.2.2
        omega
      let ey := Finset.orderIsoOfFin (cutSet y.1 k) hycard
      have hSco : ((cutSet x.1 k : Finset (Fin v)) : Set (Fin v)) =
          ((cutSet y.1 k : Finset (Fin v)) : Set (Fin v)) := by
        exact congrArg (fun s : Finset (Fin v) ↦ (s : Set (Fin v))) hS
      let cxy := OrderIso.setCongr
        ((cutSet x.1 k : Finset (Fin v)) : Set (Fin v))
        ((cutSet y.1 k : Finset (Fin v)) : Set (Fin v)) hSco
      have heq : ex.trans cxy = ey := Subsingleton.elim _ _
      have eyi :
          ((Finset.orderIsoOfFin (cutSet y.1 k) hycard) t).val = i := by
        change (ey t).val = i
        rw [← heq]
        change (cxy (ex t)).val = i
        simpa only [cxy, OrderIso.setCongr, exi]
      have ht' := congrArg Fin.val ht
      change (x.1 ((Finset.orderIsoOfFin (cutSet x.1 k) _) t)).val =
        (y.1 ((Finset.orderIsoOfFin (cutSet y.1 k) _) t)).val at ht'
      rw [show ((Finset.orderIsoOfFin (cutSet x.1 k) _) t).val = i by
          simpa only [ex] using exi,
        show ((Finset.orderIsoOfFin (cutSet y.1 k) _) t).val = i by
          simpa using eyi] at ht'
      exact Fin.ext ht'
    · have hiy : i ∉ cutSet y.1 k := by simpa [← hS] using hi
      have hBeq := congrArg (fun z : C × A × B ↦ z.2.2.val) hxy
      have hxcard : (cutSet x.1 k)ᶜ.card = v - (k - d) := by
        rw [Finset.card_compl, show Fintype.card (Fin v) = v by simp,
          card_cutSet]
        have hx := x.2.2
        omega
      let ex := Finset.orderIsoOfFin (cutSet x.1 k)ᶜ hxcard
      let t : Fin (v - (k - d)) := ex.symm ⟨i, by simpa using hi⟩
      have ht := congrFun hBeq t
      have hxi : k ≤ (x.1 i).val := by
        simpa only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] using hi
      have hyi : k ≤ (y.1 i).val := by
        simpa only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] using hiy
      have hvx : (x.1 i).val < v := (x.1 i).isLt
      have hvy : (y.1 i).val < v := (y.1 i).isLt
      have exi : (ex t).val = i := by
        exact congrArg Subtype.val (ex.apply_symm_apply ⟨i, by simpa using hi⟩)
      have hycard : (cutSet y.1 k)ᶜ.card = v - (k - d) := by
        rw [Finset.card_compl, show Fintype.card (Fin v) = v by simp,
          card_cutSet]
        have hy := y.2.2
        omega
      let ey := Finset.orderIsoOfFin (cutSet y.1 k)ᶜ hycard
      have hScomp : (cutSet x.1 k)ᶜ = (cutSet y.1 k)ᶜ :=
        congrArg (·ᶜ) hS
      have hSco : (((cutSet x.1 k)ᶜ : Finset (Fin v)) : Set (Fin v)) =
          (((cutSet y.1 k)ᶜ : Finset (Fin v)) : Set (Fin v)) := by
        exact congrArg (fun s : Finset (Fin v) ↦ (s : Set (Fin v))) hScomp
      let cxy := OrderIso.setCongr
        (((cutSet x.1 k)ᶜ : Finset (Fin v)) : Set (Fin v))
        (((cutSet y.1 k)ᶜ : Finset (Fin v)) : Set (Fin v)) hSco
      have heq : ex.trans cxy = ey := Subsingleton.elim _ _
      have eyi :
          ((Finset.orderIsoOfFin (cutSet y.1 k)ᶜ hycard) t).val = i := by
        change (ey t).val = i
        rw [← heq]
        change (cxy (ex t)).val = i
        simpa only [cxy, OrderIso.setCongr, exi]
      have ht' := congrArg Fin.val ht
      change (x.1 ((Finset.orderIsoOfFin (cutSet x.1 k)ᶜ _) t)).val - k =
        (y.1 ((Finset.orderIsoOfFin (cutSet y.1 k)ᶜ _) t)).val - k at ht'
      rw [show ((Finset.orderIsoOfFin (cutSet x.1 k)ᶜ _) t).val = i by
          simpa only [ex] using exi,
        show ((Finset.orderIsoOfFin (cutSet y.1 k)ᶜ _) t).val = i by
          simpa using eyi] at ht'
      apply Fin.ext
      omega
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [E, C, A, B, Fintype.card_prod, card_cutSubset,
    Fintype.card_subtype, Nat.mul_assoc] using hcard

private theorem card_cutEvent_interior_le
    {v k d : ℕ} (hd : d ≤ k) (hm : 0 < k - d) (hk : k < v)
    (hfirst :
      (k - d) *
          (Finset.univ.filter
            (@Erdos896.Ford.generalizedParkingGood (k - d) 1 (d + 1))).card ≤
        64 * (d + 1) ^ 2 * k ^ (k - d))
    (hsecond :
      (v - (k - d)) *
          (Finset.univ.filter
            (@Erdos896.Ford.generalizedParkingGood
              (v - (k - d)) (d + 1) 1)).card ≤
        1024 * (d + 1) * (v - k) ^ (v - (k - d))) :
    (Finset.univ.filter (@CutEvent v k d)).card ≤
      65536 * (d + 1) ^ 4 * v.choose (k - d) *
        k ^ (k - d - 1) * (v - k) ^ (v - (k - d) - 1) := by
  let m := k - d
  let q := v - (k - d)
  let L := v - k
  let CE := (Finset.univ.filter (@CutEvent v k d)).card
  let PA := (Finset.univ.filter
    (@Erdos896.Ford.generalizedParkingGood (k - d) 1 (d + 1))).card
  let PB := (Finset.univ.filter
    (@Erdos896.Ford.generalizedParkingGood
      (v - (k - d)) (d + 1) 1)).card
  have hmpos : 0 < m := by simpa [m] using hm
  have hqpos : 0 < q := by dsimp [q]; omega
  have hsplit : CE ≤ v.choose m * PA * PB := by
    simpa [CE, PA, PB, m] using card_cutEvent_le_parking_product hd hm hk
  have hmul : m * q * CE ≤
      v.choose m * (m * PA) * (q * PB) := by
    have := Nat.mul_le_mul_left (m * q) hsplit
    calc
      m * q * CE ≤ m * q * (v.choose m * PA * PB) := this
      _ = v.choose m * (m * PA) * (q * PB) := by ring
  have hparking :
      v.choose m * (m * PA) * (q * PB) ≤
        65536 * (d + 1) ^ 3 * v.choose m * k ^ m * L ^ q := by
    calc
      v.choose m * (m * PA) * (q * PB) ≤
          v.choose m * (64 * (d + 1) ^ 2 * k ^ m) *
            (1024 * (d + 1) * L ^ q) := by
              exact Nat.mul_le_mul
                (Nat.mul_le_mul_left _ (by simpa [m, PA] using hfirst))
                (by simpa [q, L, PB] using hsecond)
      _ = 65536 * (d + 1) ^ 3 * v.choose m * k ^ m * L ^ q := by ring
  have hdm : d ≤ d * m := by
    calc
      d = d * 1 := by omega
      _ ≤ d * m := Nat.mul_le_mul_left d hmpos
  have hkm : k ≤ (d + 1) * m := by
    calc
      k = m + d := by dsimp [m]; omega
      _ ≤ m + d * m := Nat.add_le_add_left hdm m
      _ = (d + 1) * m := by ring
  have hLq : L ≤ q := by dsimp [L, q]; omega
  have hkpow : k ^ m = k ^ (m - 1) * k := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hLpow : L ^ q = L ^ (q - 1) * L := by
    conv_lhs => rw [show q = (q - 1) + 1 by omega]
    rw [pow_succ]
  have hbase : k ^ m * L ^ q ≤
      (d + 1) * m * q * (k ^ (m - 1) * L ^ (q - 1)) := by
    rw [hkpow, hLpow]
    calc
      k ^ (m - 1) * k * (L ^ (q - 1) * L) ≤
          k ^ (m - 1) * ((d + 1) * m) *
            (L ^ (q - 1) * q) := by gcongr
      _ = (d + 1) * m * q *
          (k ^ (m - 1) * L ^ (q - 1)) := by ring
  let R := 65536 * (d + 1) ^ 4 * v.choose m *
    k ^ (m - 1) * L ^ (q - 1)
  have hfinalmul : m * q * CE ≤ m * q * R := by
    calc
      m * q * CE ≤
          65536 * (d + 1) ^ 3 * v.choose m * k ^ m * L ^ q :=
        hmul.trans hparking
      _ = (65536 * (d + 1) ^ 3 * v.choose m) *
          (k ^ m * L ^ q) := by ring
      _ ≤ (65536 * (d + 1) ^ 3 * v.choose m) *
          ((d + 1) * m * q *
            (k ^ (m - 1) * L ^ (q - 1))) :=
              Nat.mul_le_mul_left
                (65536 * (d + 1) ^ 3 * v.choose m) hbase
      _ = m * q * R := by dsimp [R]; ring
  have hCER : CE ≤ R :=
    Nat.le_of_mul_le_mul_left hfinalmul (Nat.mul_pos hmpos hqpos)
  simpa [CE, R, m, q, L, Nat.mul_assoc] using hCER

/-! ## A summable polynomial loss -/

private def potentialTail (n : ℕ) : ℚ :=
  2 * (n : ℚ) ^ 4 + 16 * (n : ℚ) ^ 3 + 72 * (n : ℚ) ^ 2 +
    208 * (n : ℚ) + 300

private theorem potentialTail_recurrence (n : ℕ) :
    potentialTail n = (n + 1 : ℕ) ^ 4 + potentialTail (n + 1) / 2 := by
  unfold potentialTail
  norm_num
  push_cast
  ring

private theorem potentialTail_nonneg (n : ℕ) : 0 ≤ potentialTail n := by
  unfold potentialTail
  positivity

private theorem sum_polynomial_geometric_with_tail (n : ℕ) :
    (∑ d ∈ Finset.range n, ((d + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ d) +
        potentialTail n / (2 : ℚ) ^ n = 300 := by
  induction n with
  | zero => norm_num [potentialTail]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrec := potentialTail_recurrence n
      have hpow : (2 : ℚ) ^ (n + 1) = (2 : ℚ) ^ n * 2 := by
        rw [pow_succ]
      rw [hpow]
      calc
        (∑ d ∈ Finset.range n,
              ((d + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ d) +
              ((n + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ n +
              potentialTail (n + 1) / ((2 : ℚ) ^ n * 2) =
            (∑ d ∈ Finset.range n,
              ((d + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ d) +
              ((((n + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ n) +
                potentialTail (n + 1) / ((2 : ℚ) ^ n * 2)) := by ring
        _ = (∑ d ∈ Finset.range n,
              ((d + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ d) +
              potentialTail n / (2 : ℚ) ^ n := by
            congr 1
            rw [hrec]
            field_simp
            <;> ring
        _ = 300 := ih

private theorem sum_polynomial_geometric_le (n : ℕ) :
    ∑ d ∈ Finset.range n, ((d + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ d ≤ 300 := by
  have h := sum_polynomial_geometric_with_tail n
  have ht : 0 ≤ potentialTail n / (2 : ℚ) ^ n :=
    div_nonneg (potentialTail_nonneg n) (by positivity)
  linarith

/-! ## The Abel sum over the position of a cut -/

private theorem exp_four_le_eighty_one : Real.exp 4 ≤ 81 := by
  rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num,
    Real.exp_nat_mul]
  calc
    Real.exp 1 ^ 4 ≤ 3 ^ 4 := by gcongr; exact Real.exp_one_lt_three.le
    _ = 81 := by norm_num

private theorem sum_interior_kernel_le {v d : ℕ} (hv : 2 ≤ v) :
    (∑ k ∈ Finset.Icc (d + 1) (v - 1),
        (v.choose (k - d) : ℝ) * (k : ℝ) ^ (k - d - 1) *
          (v - k : ℕ) ^ (v - (k - d) - 1)) ≤
      Real.exp 4 * (v : ℝ) ^ (v - 1) := by
  let K := Finset.Icc (d + 1) (v - 1)
  let Q := (Finset.Icc 1 (v - 1)).filter
    (fun q : ℕ ↦ 0 < -(d : ℝ) + (q : ℝ))
  have hsum :
      (∑ k ∈ K,
          (v.choose (k - d) : ℝ) * (k : ℝ) ^ (k - d - 1) *
            (v - k : ℕ) ^ (v - (k - d) - 1)) =
        ∑ q ∈ Q,
          (v.choose q : ℝ) * (-(d : ℝ) + (q : ℝ)) ^ (q - 1) *
            ((d : ℝ) + (v - q : ℕ)) ^ (v - q - 1) := by
    classical
    apply Finset.sum_bij'
        (fun k _hk ↦ v - k + d)
        (fun q _hq ↦ v - q + d)
    · intro k hk
      simp only [K, Q, Finset.mem_Icc, Finset.mem_filter] at hk ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      norm_num
      exact_mod_cast (show k < v by omega)
    · intro q hq
      simp only [K, Q, Finset.mem_Icc, Finset.mem_filter] at hq ⊢
      rcases hq with ⟨⟨hq1, hqv⟩, hqd⟩
      have hdq : d < q := by exact_mod_cast (by linarith : (d : ℝ) < q)
      constructor <;> omega
    · intro k hk
      simp only [K, Finset.mem_Icc] at hk
      omega
    · intro q hq
      simp only [Q, Finset.mem_filter, Finset.mem_Icc] at hq
      have hdq : d < q := by
        exact_mod_cast (by linarith [hq.2] : (d : ℝ) < q)
      omega
    · intro k hk
      simp only [K, Finset.mem_Icc] at hk
      have hkd : d ≤ k := by omega
      have hkv : k ≤ v := by omega
      have hqv : v - k + d ≤ v := by omega
      have hcomp : v - (v - k + d) = k - d := by omega
      have hchoose : v.choose (k - d) = v.choose (v - k + d) := by
        rw [← Nat.choose_symm hqv, hcomp]
      have hexp : v - (k - d) - 1 = v - k + d - 1 := by omega
      have hleft : (-(d : ℝ) + (v - k + d : ℕ) : ℝ) = v - k := by
        rw [Nat.cast_add, Nat.cast_sub hkv]
        push_cast
        ring
      have hright : (d : ℝ) + (v - (v - k + d) : ℕ) = k := by
        rw [hcomp, Nat.cast_sub hkd]
        push_cast
        ring
      have hcastvk : ((v - k : ℕ) : ℝ) = (v : ℝ) - k := by
        exact Nat.cast_sub hkv
      rw [← hchoose]
      rw [hleft, hright, hcomp, hexp, hcastvk]
      ring
  rw [show (∑ k ∈ Finset.Icc (d + 1) (v - 1),
        (v.choose (k - d) : ℝ) * (k : ℝ) ^ (k - d - 1) *
          (v - k : ℕ) ^ (v - (k - d) - 1)) =
      Erdos896.Ford.fordLemmaFourTwoSum v (-(d : ℝ)) d by
    rw [Erdos896.Ford.fordLemmaFourTwoSum]
    exact hsum]
  simpa using Erdos896.Ford.lemma_four_two hv (by positivity)
    (show 0 < (v : ℝ) + -(d : ℝ) + d by
      norm_num
      positivity)

/-! ## Decomposition of the first moment into cut events -/

private theorem two_pow_ratio_of_add_eq {a b d : ℕ} (h : a + d = b) :
    (2 : ℚ) ^ a / (2 : ℚ) ^ b = 1 / (2 : ℚ) ^ d := by
  rw [← h, pow_add]
  field_simp

private theorem sum_prefix_term_eq_sum_cutEvent {v k : ℕ} (hk : k ≤ v) :
    (∑ f ∈ Finset.univ.filter (@Good v),
        (2 : ℚ) ^ cumulativeOccupancy f k / (2 : ℚ) ^ k) =
      ∑ d ∈ Finset.range (k + 1),
        ((Finset.univ.filter (@CutEvent v k d)).card : ℚ) /
          (2 : ℚ) ^ d := by
  classical
  let G := Finset.univ.filter (@Good v)
  let deficit : (Fin v → Fin v) → ℕ := fun f ↦ k - cumulativeOccupancy f k
  have hmaps : ∀ f ∈ G, deficit f ∈ Finset.range (k + 1) := by
    intro f hf
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [Finset.mem_range, deficit]
    have hc := cumulativeOccupancy_le hf hk
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun f : Fin v → Fin v ↦
      (2 : ℚ) ^ cumulativeOccupancy f k / (2 : ℚ) ^ k)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro d hd
  have hdk : d ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  have hevent :
      (G.filter fun f ↦ deficit f = d) =
        Finset.univ.filter (@CutEvent v k d) := by
    ext f
    simp only [G, deficit, CutEvent, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hf, hdef⟩
      refine ⟨hf, ?_⟩
      have hc := cumulativeOccupancy_le hf hk
      omega
    · rintro ⟨hf, heq⟩
      refine ⟨hf, ?_⟩
      have hc := cumulativeOccupancy_le hf hk
      omega
  calc
    (∑ f ∈ G with deficit f = d,
        (2 : ℚ) ^ cumulativeOccupancy f k / (2 : ℚ) ^ k) =
        ∑ _f ∈ G.filter fun f ↦ deficit f = d,
          1 / (2 : ℚ) ^ d := by
            apply Finset.sum_congr rfl
            intro f hf
            simp only [Finset.mem_filter] at hf
            have hgood : Good f := by
              simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and]
                using hf.1
            have hc := cumulativeOccupancy_le hgood hk
            apply two_pow_ratio_of_add_eq
            dsimp only [deficit] at hf
            omega
    _ = ((Finset.univ.filter (@CutEvent v k d)).card : ℚ) /
          (2 : ℚ) ^ d := by
        rw [hevent]
        simp [div_eq_mul_inv]

/-! ## The two boundary cuts -/

private theorem card_cutEvent_maxDeficit_le {v k : ℕ} (hk : k < v) :
    (Finset.univ.filter (@CutEvent v k k)).card ≤
      (Finset.univ.filter
        (@Erdos896.Ford.generalizedParkingGood v (k + 1) 1)).card := by
  classical
  let E := {f : Fin v → Fin v // CutEvent k k f}
  let P := {g : Fin v → Fin (v - (k + 1) + 1) //
    Erdos896.Ford.generalizedParkingGood v (k + 1) 1 g}
  have hbox : v - (k + 1) + 1 = v - k := by omega
  let encode : E → P := fun x ↦ by
    have hzero : cumulativeOccupancy x.1 k = 0 := by
      have hx := x.2.2
      omega
    have hge : ∀ i, k ≤ (x.1 i).val := by
      intro i
      by_contra hi
      have himem : i ∈ Finset.univ.filter fun t ↦ (x.1 t).val < k := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hpos : 0 < cumulativeOccupancy x.1 k := by
        exact Finset.card_pos.mpr ⟨i, himem⟩
      omega
    let g : Fin v → Fin (v - (k + 1) + 1) := fun i ↦
      Fin.cast hbox.symm ⟨(x.1 i).val - k, by
        have hi := (x.1 i).isLt
        omega⟩
    have hg : Erdos896.Ford.generalizedParkingGood v (k + 1) 1 g := by
      intro r
      have hr : k + r.val ≤ v := by omega
      have heq :
          (Finset.univ.filter fun i ↦ (g i).val < r.val) =
            Finset.univ.filter fun i ↦ (x.1 i).val < k + r.val := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, g,
          Fin.val_cast]
        have hi := hge i
        omega
      rw [heq]
      change cumulativeOccupancy x.1 (k + r.val) ≤ k + 1 + r.val - 1
      have hthr : k + 1 + r.val - 1 = k + r.val := by omega
      rw [hthr]
      exact cumulativeOccupancy_le x.2.1 hr
    exact ⟨g, hg⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hzeroX : cumulativeOccupancy x.1 k = 0 := by
      have hx := x.2.2
      omega
    have hzeroY : cumulativeOccupancy y.1 k = 0 := by
      have hy := y.2.2
      omega
    have hxge : k ≤ (x.1 i).val := by
      by_contra hi
      have himem : i ∈ Finset.univ.filter fun t ↦ (x.1 t).val < k := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have := Finset.card_pos.mpr ⟨i, himem⟩
      change 0 < cumulativeOccupancy x.1 k at this
      omega
    have hyge : k ≤ (y.1 i).val := by
      by_contra hi
      have himem : i ∈ Finset.univ.filter fun t ↦ (y.1 t).val < k := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have := Finset.card_pos.mpr ⟨i, himem⟩
      change 0 < cumulativeOccupancy y.1 k at this
      omega
    have hi := congrArg (fun z : P ↦ (z.1 i).val) hxy
    change (x.1 i).val - k = (y.1 i).val - k at hi
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [E, P, Fintype.card_subtype] using hcard

private theorem card_cutEvent_full_le_parking {v : ℕ} (hv : 1 ≤ v) :
    (Finset.univ.filter (@CutEvent v v 0)).card ≤
      (Finset.univ.filter
        (@Erdos896.Ford.generalizedParkingGood v 1 1)).card := by
  classical
  let E := {f : Fin v → Fin v // CutEvent v 0 f}
  let P := {g : Fin v → Fin (v - 1 + 1) //
    Erdos896.Ford.generalizedParkingGood v 1 1 g}
  have hbox : v - 1 + 1 = v := by omega
  let encode : E → P := fun x ↦ by
    let g : Fin v → Fin (v - 1 + 1) := fun i ↦ Fin.cast hbox.symm (x.1 i)
    have hg : Erdos896.Ford.generalizedParkingGood v 1 1 g := by
      intro r
      change cumulativeOccupancy x.1 r.val ≤ 1 + r.val - 1
      simpa only [Nat.one_add, Nat.succ_sub_one] using
        cumulativeOccupancy_le x.2.1 (show r.val ≤ v by omega)
    exact ⟨g, hg⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi := congrArg (fun z : P ↦ (z.1 i).val) hxy
    exact Fin.ext hi
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [E, P, Fintype.card_subtype] using hcard

private theorem cutEvent_full_positive_deficit_empty {v d : ℕ} (hd : 0 < d) :
    Finset.univ.filter (@CutEvent v v d) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, CutEvent] at hf
  have hfull : cumulativeOccupancy f v = v := by
    unfold cumulativeOccupancy
    simp
  omega

/-! ## The global cut moment -/

private noncomputable def cutMomentRat (v : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 v, ∑ d ∈ Finset.range (k + 1),
    ((Finset.univ.filter (@CutEvent v k d)).card : ℚ) / (2 : ℚ) ^ d

private theorem sum_expPotential_eq_cutMomentRat (v : ℕ) :
    (∑ f ∈ Finset.univ.filter (@Good v), expPotential f) = cutMomentRat v := by
  classical
  unfold expPotential
  calc
    (∑ f ∈ Finset.univ.filter (@Good v),
        ∑ j : Fin v,
          (2 : ℚ) ^ prefixOccupancy f j / (2 : ℚ) ^ (j.1 + 1)) =
      ∑ j : Fin v, ∑ f ∈ Finset.univ.filter (@Good v),
        (2 : ℚ) ^ prefixOccupancy f j / (2 : ℚ) ^ (j.1 + 1) := by
          exact Finset.sum_comm
    _ = ∑ j : Fin v, ∑ f ∈ Finset.univ.filter (@Good v),
        (2 : ℚ) ^ cumulativeOccupancy f (j.val + 1) /
          (2 : ℚ) ^ (j.val + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            funext f
            rw [prefixOccupancy_eq_cumulative]
    _ = ∑ j ∈ Finset.range v, ∑ f ∈ Finset.univ.filter (@Good v),
        (2 : ℚ) ^ cumulativeOccupancy f (j + 1) / (2 : ℚ) ^ (j + 1) := by
          exact Fin.sum_univ_eq_sum_range
            (fun j ↦ ∑ f ∈ Finset.univ.filter (@Good v),
              (2 : ℚ) ^ cumulativeOccupancy f (j + 1) / (2 : ℚ) ^ (j + 1)) v
    _ = cutMomentRat v := by
      unfold cutMomentRat
      apply Finset.sum_bij (fun j _hj ↦ j + 1)
      · intro j hj
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_Icc]
        omega
      · intro j₁ hj₁ j₂ hj₂ heq
        omega
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        refine ⟨k - 1, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · omega
      · intro j hj
        simp only [Finset.mem_range] at hj
        exact sum_prefix_term_eq_sum_cutEvent (v := v) (k := j + 1) (by omega)

private def ParkingBoundStatement : Prop :=
  ∀ k U : ℕ, 1 ≤ k → 1 ≤ U → U ≤ k →
    k * (Finset.univ.filter
      (@Erdos896.Ford.generalizedParkingGood k U 1)).card ≤
      1024 * U * (k - U + 1) ^ k

private theorem parkingBoundStatement : ParkingBoundStatement := by
  intro k U hk hU hUk
  simpa only [Nat.one_pow, Nat.mul_one] using
    Erdos896.Ford.generalizedParkingGood_card_bound
      k U 1 hk hU hUk (by omega)

private theorem card_cutEvent_interior_real_le_of_parking
    (hpark : ParkingBoundStatement) {v k d : ℕ}
    (hd : d < k) (hk : k < v) :
    ((Finset.univ.filter (@CutEvent v k d)).card : ℝ) ≤
      65536 * (d + 1 : ℕ) ^ 4 * (v.choose (k - d) : ℕ) *
        (k : ℝ) ^ (k - d - 1) *
          (v - k : ℕ) ^ (v - (k - d) - 1) := by
  have hm : 0 < k - d := by omega
  have hfirst := Erdos896.Ford.generalizedParkingGood_card_bound_U_one
    (k - d) (d + 1) (by omega) (by omega)
  have hsecond := hpark (v - (k - d)) (d + 1)
    (by omega) (by omega) (by omega)
  have hfirst' :
      (k - d) * (Finset.univ.filter
        (@Erdos896.Ford.generalizedParkingGood (k - d) 1 (d + 1))).card ≤
        64 * (d + 1) ^ 2 * k ^ (k - d) := by
    have hbase : k - d - 1 + (d + 1) = k := by omega
    simpa only [Nat.one_mul, Nat.mul_one, hbase] using hfirst
  have hsecond' :
      (v - (k - d)) * (Finset.univ.filter
        (@Erdos896.Ford.generalizedParkingGood
          (v - (k - d)) (d + 1) 1)).card ≤
        1024 * (d + 1) * (v - k) ^ (v - (k - d)) := by
    have hbase : v - (k - d) - (d + 1) + 1 = v - k := by omega
    simpa only [Nat.one_pow, Nat.mul_one, hbase] using hsecond
  have hnat := card_cutEvent_interior_le (show d ≤ k by omega) hm hk
    hfirst' hsecond'
  exact_mod_cast hnat

private theorem card_cutEvent_maxDeficit_real_le_of_parking
    (hpark : ParkingBoundStatement) {v k : ℕ} (hk : k < v) :
    (v : ℝ) * ((Finset.univ.filter (@CutEvent v k k)).card : ℝ) ≤
      1024 * (k + 1 : ℕ) * (v - k : ℕ) ^ v := by
  have hv : 1 ≤ v := by omega
  have hp := hpark v (k + 1) hv (by omega) (by omega)
  have hcut := card_cutEvent_maxDeficit_le hk
  have hnat :
      v * (Finset.univ.filter (@CutEvent v k k)).card ≤
        1024 * (k + 1) * (v - k) ^ v := by
    calc
      v * (Finset.univ.filter (@CutEvent v k k)).card ≤
          v * (Finset.univ.filter
            (@Erdos896.Ford.generalizedParkingGood v (k + 1) 1)).card :=
        Nat.mul_le_mul_left v hcut
      _ ≤ 1024 * (k + 1) * (v - k) ^ v := by
        have hbase : v - (k + 1) + 1 = v - k := by omega
        simpa only [Nat.one_pow, Nat.mul_one, hbase] using hp
  exact_mod_cast hnat

private theorem card_cutEvent_full_real_le
    {v : ℕ} (hv : 1 ≤ v) :
    (v : ℝ) * ((Finset.univ.filter (@CutEvent v v 0)).card : ℝ) ≤
      64 * (v : ℝ) ^ v := by
  have hp := Erdos896.Ford.generalizedParkingGood_card_bound_U_one
    v 1 hv (by omega)
  have hcut := card_cutEvent_full_le_parking hv
  have hnat :
      v * (Finset.univ.filter (@CutEvent v v 0)).card ≤ 64 * v ^ v := by
    calc
      v * (Finset.univ.filter (@CutEvent v v 0)).card ≤
          v * (Finset.univ.filter
            (@Erdos896.Ford.generalizedParkingGood v 1 1)).card :=
        Nat.mul_le_mul_left v hcut
      _ ≤ 64 * v ^ v := by
        have hbase : v - 1 + 1 = v := by omega
        simpa only [Nat.one_pow, Nat.one_mul, Nat.mul_one, hbase] using hp
  exact_mod_cast hnat

private theorem interior_cut_sum_real_le_of_parking
    (hpark : ParkingBoundStatement) {v : ℕ} (hv : 2 ≤ v) (d : ℕ) :
    (v : ℝ) *
        (∑ k ∈ Finset.Icc (d + 1) (v - 1),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) ≤
      5308416 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by
  let kernel : ℕ → ℝ := fun k ↦
    (v.choose (k - d) : ℝ) * (k : ℝ) ^ (k - d - 1) *
      (v - k : ℕ) ^ (v - (k - d) - 1)
  have hpoint : ∀ k ∈ Finset.Icc (d + 1) (v - 1),
      ((Finset.univ.filter (@CutEvent v k d)).card : ℝ) ≤
        65536 * (d + 1 : ℕ) ^ 4 * kernel k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simpa only [kernel, mul_assoc] using
      card_cutEvent_interior_real_le_of_parking hpark
        (show d < k by omega) (show k < v by omega)
  have hsum :
      (∑ k ∈ Finset.Icc (d + 1) (v - 1),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) ≤
        65536 * (d + 1 : ℕ) ^ 4 *
          ∑ k ∈ Finset.Icc (d + 1) (v - 1), kernel k := by
    calc
      (∑ k ∈ Finset.Icc (d + 1) (v - 1),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) ≤
          ∑ k ∈ Finset.Icc (d + 1) (v - 1),
            65536 * (d + 1 : ℕ) ^ 4 * kernel k := by
              exact Finset.sum_le_sum hpoint
      _ = 65536 * (d + 1 : ℕ) ^ 4 *
          ∑ k ∈ Finset.Icc (d + 1) (v - 1), kernel k := by
            rw [Finset.mul_sum]
  have habel :
      (∑ k ∈ Finset.Icc (d + 1) (v - 1), kernel k) ≤
        Real.exp 4 * (v : ℝ) ^ (v - 1) := by
    simpa only [kernel] using sum_interior_kernel_le (d := d) hv
  have hvnonneg : (0 : ℝ) ≤ v := by positivity
  have hpow : (v : ℝ) ^ v = (v : ℝ) ^ (v - 1) * v := by
    simpa only [show v - 1 + 1 = v by omega] using
      (pow_succ (v : ℝ) (v - 1))
  calc
    (v : ℝ) *
        (∑ k ∈ Finset.Icc (d + 1) (v - 1),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) ≤
      v * (65536 * (d + 1 : ℕ) ^ 4 *
        ∑ k ∈ Finset.Icc (d + 1) (v - 1), kernel k) := by gcongr
    _ ≤ v * (65536 * (d + 1 : ℕ) ^ 4 *
        (Real.exp 4 * (v : ℝ) ^ (v - 1))) := by gcongr
    _ ≤ v * (65536 * (d + 1 : ℕ) ^ 4 *
        (81 * (v : ℝ) ^ (v - 1))) := by
          gcongr
          exact exp_four_le_eighty_one
    _ = 5308416 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by
      rw [hpow]
      ring

private theorem cut_slice_real_le_of_parking
    (hpark : ParkingBoundStatement) {v d : ℕ} (hv : 2 ≤ v) (hdv : d ≤ v) :
    (v : ℝ) *
        (∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) ≤
      5309440 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by
  classical
  let t : ℕ → ℝ := fun k ↦
    ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)
  have hfilter :
      (Finset.Icc 1 v).filter (fun k ↦ d ≤ k) =
        Finset.Icc (max 1 d) v := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  by_cases hd0 : d = 0
  · subst d
    have hdecomp :
        (∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ 0 ≤ k), t k) =
          t v + ∑ k ∈ Finset.Icc 1 (v - 1), t k := by
      rw [hfilter]
      simp only [max_eq_left (by omega : 1 ≥ 0)]
      rw [← Finset.insert_Icc_sub_one_right_eq_Icc (show 1 ≤ v by omega)]
      rw [Finset.sum_insert (by simp; omega)]
    have hfull : (v : ℝ) * t v ≤ 64 * (v : ℝ) ^ v := by
      simpa only [t] using card_cutEvent_full_real_le (by omega)
    have hinterior :
        (v : ℝ) * (∑ k ∈ Finset.Icc 1 (v - 1), t k) ≤
          5308416 * (v : ℝ) ^ v := by
      convert interior_cut_sum_real_le_of_parking hpark hv 0 using 1 <;>
        norm_num [t]
    rw [hdecomp]
    calc
      (v : ℝ) * (t v + ∑ k ∈ Finset.Icc 1 (v - 1), t k) =
          v * t v + v * (∑ k ∈ Finset.Icc 1 (v - 1), t k) := by ring
      _ ≤ 64 * (v : ℝ) ^ v + 5308416 * (v : ℝ) ^ v := by gcongr
      _ ≤ 5309440 * ((0 + 1 : ℕ) : ℝ) ^ 4 * (v : ℝ) ^ v := by
        have hp : 0 ≤ (v : ℝ) ^ v := by positivity
        norm_num
        nlinarith
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_cases hdvEq : d = v
    · subst d
      have hempty := cutEvent_full_positive_deficit_empty
        (v := v) (d := v) (by omega)
      rw [hfilter]
      simp only [max_eq_right (by omega : 1 ≤ v), Finset.Icc_self,
        Finset.sum_singleton, hempty, Finset.card_empty, Nat.cast_zero,
        mul_zero]
      positivity
    · have hdltv : d < v := lt_of_le_of_ne hdv hdvEq
      have hdecomp :
          (∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k), t k) =
            t d + ∑ k ∈ Finset.Icc (d + 1) (v - 1), t k := by
        rw [hfilter]
        simp only [max_eq_right (by omega : 1 ≤ d)]
        rw [← Finset.insert_Icc_sub_one_right_eq_Icc (show d ≤ v by omega)]
        rw [Finset.sum_insert (by simp; omega)]
        rw [← Finset.insert_Icc_add_one_left_eq_Icc
          (show d ≤ v - 1 by omega)]
        rw [Finset.sum_insert (by simp)]
        have hempty := cutEvent_full_positive_deficit_empty (v := v) hdpos
        simp only [t, hempty, Finset.card_empty, Nat.cast_zero, zero_add]
      have hmax := card_cutEvent_maxDeficit_real_le_of_parking hpark hdltv
      have hpoly : ((d + 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 4 := by
        exact_mod_cast (Nat.le_pow (a := d + 1) (b := 4) (by omega))
      have hsub : ((v - d : ℕ) : ℝ) ≤ (v : ℝ) := by
        exact_mod_cast Nat.sub_le v d
      have hbasepow : ((v - d : ℕ) : ℝ) ^ v ≤ (v : ℝ) ^ v :=
        pow_le_pow_left₀ (by positivity) hsub v
      have hmax' : (v : ℝ) * t d ≤
          1024 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by
        calc
          (v : ℝ) * t d ≤
              1024 * (d + 1 : ℕ) * (v - d : ℕ) ^ v := by
                simpa only [t] using hmax
          _ ≤ 1024 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by
            gcongr
      have hinterior :
          (v : ℝ) * (∑ k ∈ Finset.Icc (d + 1) (v - 1), t k) ≤
            5308416 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by
        simpa only [t] using interior_cut_sum_real_le_of_parking hpark hv d
      rw [hdecomp]
      calc
        (v : ℝ) * (t d + ∑ k ∈ Finset.Icc (d + 1) (v - 1), t k) =
            v * t d + v * (∑ k ∈ Finset.Icc (d + 1) (v - 1), t k) := by
              ring
        _ ≤ 1024 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v +
            5308416 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by gcongr
        _ = 5309440 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v := by ring

private noncomputable def cutMomentReal (v : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 v, ∑ d ∈ Finset.range (k + 1),
    ((Finset.univ.filter (@CutEvent v k d)).card : ℝ) / (2 : ℝ) ^ d

private theorem cast_cutMomentRat (v : ℕ) :
    (cutMomentRat v : ℝ) = cutMomentReal v := by
  unfold cutMomentRat cutMomentReal
  push_cast
  rfl

private theorem cutMomentReal_reorder (v : ℕ) :
    cutMomentReal v =
      ∑ d ∈ Finset.range (v + 1),
        (∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) /
            (2 : ℝ) ^ d := by
  classical
  unfold cutMomentReal
  calc
    (∑ k ∈ Finset.Icc 1 v, ∑ d ∈ Finset.range (k + 1),
        ((Finset.univ.filter (@CutEvent v k d)).card : ℝ) / (2 : ℝ) ^ d) =
      ∑ k ∈ Finset.Icc 1 v, ∑ d ∈ Finset.range (v + 1),
        if d ≤ k then
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ) / (2 : ℝ) ^ d
        else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkv : k ≤ v := (Finset.mem_Icc.mp hk).2
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext d
        simp only [Finset.mem_range, Finset.mem_filter]
        omega
      · intro d hd
        rfl
    _ = ∑ d ∈ Finset.range (v + 1), ∑ k ∈ Finset.Icc 1 v,
        if d ≤ k then
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ) / (2 : ℝ) ^ d
        else 0 := by exact Finset.sum_comm
    _ = ∑ d ∈ Finset.range (v + 1),
        (∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
          ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) /
            (2 : ℝ) ^ d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      rw [Finset.sum_div]

private theorem cutMomentReal_bound_of_parking
    (hpark : ParkingBoundStatement) {v : ℕ} (hv : 2 ≤ v) :
    (v : ℝ) * cutMomentReal v ≤ 1600000000 * (v : ℝ) ^ v := by
  rw [cutMomentReal_reorder]
  rw [Finset.mul_sum]
  have hterm : ∀ d ∈ Finset.range (v + 1),
      (v : ℝ) *
          ((∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
            ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) /
              (2 : ℝ) ^ d) ≤
        (5309440 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v) /
          (2 : ℝ) ^ d := by
    intro d hd
    have hdv : d ≤ v := by
      have := Finset.mem_range.mp hd
      omega
    have hs := cut_slice_real_le_of_parking hpark hv hdv
    calc
      (v : ℝ) *
          ((∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
            ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) /
              (2 : ℝ) ^ d) =
        ((v : ℝ) *
          (∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
            ((Finset.univ.filter (@CutEvent v k d)).card : ℝ))) /
              (2 : ℝ) ^ d := by ring
      _ ≤ (5309440 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v) /
              (2 : ℝ) ^ d := by gcongr
  calc
    (∑ d ∈ Finset.range (v + 1),
        (v : ℝ) *
          ((∑ k ∈ (Finset.Icc 1 v).filter (fun k ↦ d ≤ k),
            ((Finset.univ.filter (@CutEvent v k d)).card : ℝ)) /
              (2 : ℝ) ^ d)) ≤
      ∑ d ∈ Finset.range (v + 1),
        (5309440 * (d + 1 : ℕ) ^ 4 * (v : ℝ) ^ v) /
          (2 : ℝ) ^ d := Finset.sum_le_sum hterm
    _ = 5309440 * (v : ℝ) ^ v *
        (∑ d ∈ Finset.range (v + 1),
          ((d + 1 : ℕ) ^ 4 : ℝ) / (2 : ℝ) ^ d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 5309440 * (v : ℝ) ^ v * 300 := by
      gcongr
      have hq := sum_polynomial_geometric_le (v + 1)
      have hc :
          ((∑ d ∈ Finset.range (v + 1),
            ((d + 1 : ℕ) ^ 4 : ℚ) / (2 : ℚ) ^ d : ℚ) : ℝ) ≤
              ((300 : ℚ) : ℝ) := Rat.cast_le.mpr hq
      push_cast at hc
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    _ ≤ 1600000000 * (v : ℝ) ^ v := by
      have hc : (5309440 : ℝ) * 300 ≤ 1600000000 := by norm_num
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ v by positivity) v]

private theorem cutMomentRat_bound_of_parking
    (hpark : ParkingBoundStatement) {v : ℕ} (hv : 2 ≤ v) :
    (v : ℚ) * cutMomentRat v ≤ 1600000000 * (v : ℚ) ^ v := by
  have hreal := cutMomentReal_bound_of_parking hpark hv
  rw [← cast_cutMomentRat] at hreal
  exact_mod_cast hreal

private theorem expPotential_moment_bound_of_parking
    (hpark : ParkingBoundStatement) {v : ℕ} (hv : 2 ≤ v) :
    (v : ℚ) *
        (∑ f ∈ Finset.univ.filter (@Good v), expPotential f) ≤
      1600000000 * (v : ℚ) ^ v := by
  rw [sum_expPotential_eq_cutMomentRat]
  exact cutMomentRat_bound_of_parking hpark hv

private theorem one_le_card_goodPotential_fin_one {B : ℚ} (hB : 1 ≤ B) :
    1 ≤ (Finset.univ.filter (@GoodPotential 1 B)).card := by
  classical
  let f : Fin 1 → Fin 1 := fun _ ↦ 0
  apply Finset.one_le_card.mpr
  refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  constructor
  · intro j hj
    have hj1 : j ≤ 1 := by simpa using hj
    interval_cases j <;>
      norm_num [occupancyList, boxOccupancy, f]
  · calc
      expPotential f = 1 := by
        simp [expPotential, prefixOccupancy, occupancyList, boxOccupancy, f]
      _ ≤ B := hB

private theorem goodPotential_count_of_parking
    (hpark : ParkingBoundStatement) (v : ℕ) (hv : 1 ≤ v) :
    (1 / 2 : ℚ) * (v : ℚ) ^ v ≤
      (v : ℚ) *
        ((Finset.univ.filter
          (@GoodPotential v (3200000000 : ℚ))).card : ℚ) := by
  classical
  by_cases hv1 : v = 1
  · subst v
    have hc := one_le_card_goodPotential_fin_one
      (B := (3200000000 : ℚ)) (by norm_num)
    norm_num only [Nat.cast_one, one_pow, one_mul] at ⊢
    change (1 / 2 : ℚ) ≤
      ((Finset.univ.filter (@GoodPotential 1 (3200000000 : ℚ))).card : ℚ)
    have hcq : (1 : ℚ) ≤
        ((Finset.univ.filter (@GoodPotential 1 (3200000000 : ℚ))).card : ℚ) := by
      exact_mod_cast hc
    linarith
  · have hv2 : 2 ≤ v := by omega
    let B : ℚ := 3200000000
    let G := Finset.univ.filter (@Good v)
    let P := Finset.univ.filter (@GoodPotential v B)
    let D := Finset.univ.filter
      (fun f : Fin v → Fin v ↦ Good f ∧ B < expPotential f)
    let H := Finset.univ.filter
      (fun f : Fin v → Fin v ↦ Good f ∧ B ≤ expPotential f)
    have hpartition : G = P ∪ D := by
      ext f
      simp only [G, P, D, Finset.mem_filter, Finset.mem_univ, true_and,
        GoodPotential, Finset.mem_union]
      constructor
      · intro hf
        by_cases hp : expPotential f ≤ B
        · exact Or.inl ⟨hf, hp⟩
        · exact Or.inr ⟨hf, lt_of_not_ge hp⟩
      · rintro (⟨hf, _⟩ | ⟨hf, _⟩) <;> exact hf
    have hdisj : Disjoint P D := by
      rw [Finset.disjoint_left]
      intro f hfP hfD
      simp only [P, D, Finset.mem_filter, Finset.mem_univ, true_and,
        GoodPotential] at hfP hfD
      linarith
    have hcardpart : G.card = P.card + D.card := by
      rw [hpartition, Finset.card_union_of_disjoint hdisj]
    have hDH : D ⊆ H := by
      intro f hf
      simp only [D, H, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact ⟨hf.1, hf.2.le⟩
    have hcardDH : D.card ≤ H.card := Finset.card_le_card hDH
    let g : (Fin v → Fin v) → ℚ := fun f ↦
      if Good f then expPotential f else 0
    have hg : ∀ f, 0 ≤ g f := by
      intro f
      dsimp only [g]
      split_ifs
      · exact expPotential_nonneg f
      · norm_num
    have hBpos : 0 < B := by norm_num [B]
    have hmark := counting_markov_rat g B hBpos hg
    have hevent :
        Finset.univ.filter (fun f ↦ B ≤ g f) = H := by
      ext f
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hgf
        have hf : Good f := by
          by_contra hnot
          dsimp only [g] at hgf
          rw [if_neg hnot] at hgf
          linarith
        refine ⟨hf, ?_⟩
        simpa only [g, hf, if_true] using hgf
      · rintro ⟨hf, hpot⟩
        simpa only [g, hf, if_true] using hpot
    have hsum : (∑ f, g f) =
        ∑ f ∈ Finset.univ.filter (@Good v), expPotential f := by
      simp [g, Finset.sum_ite]
    rw [hevent, hsum] at hmark
    have hmoment := expPotential_moment_bound_of_parking hpark hv2
    have hbad :
        (v : ℚ) * (H.card : ℚ) * B ≤
          1600000000 * (v : ℚ) ^ v := by
      calc
        (v : ℚ) * (H.card : ℚ) * B =
            (v : ℚ) * ((H.card : ℚ) * B) := by ring
        _ ≤ (v : ℚ) *
            (∑ f ∈ Finset.univ.filter (@Good v), expPotential f) := by
          gcongr
        _ ≤ 1600000000 * (v : ℚ) ^ v := hmoment
    have hbadHalf :
        2 * (v : ℚ) * (H.card : ℚ) ≤ (v : ℚ) ^ v := by
      dsimp only [B] at hbad
      linarith
    have hcycleNat := pow_le_mul_card_good v (by omega)
    have hcycle : (v : ℚ) ^ v ≤ (v : ℚ) * (G.card : ℚ) := by
      exact_mod_cast hcycleNat
    have hpartCast : (G.card : ℚ) = (P.card : ℚ) + (D.card : ℚ) := by
      exact_mod_cast hcardpart
    have hDHCast : (D.card : ℚ) ≤ (H.card : ℚ) := by
      exact_mod_cast hcardDH
    change (1 / 2 : ℚ) * (v : ℚ) ^ v ≤ (v : ℚ) * (P.card : ℚ)
    have hvq : (0 : ℚ) ≤ v := by positivity
    rw [hpartCast] at hcycle
    nlinarith

/-- At least half of the cycle-lemma lower bound consists of placements with
uniformly bounded exponential potential. -/
theorem goodPotential_half_count (v : ℕ) (hv : 1 ≤ v) :
    (1 / 2 : ℚ) * (v : ℚ) ^ v ≤
      (v : ℚ) *
        ((Finset.univ.filter
          (@GoodPotential v (3200000000 : ℚ))).card : ℚ) := by
  exact goodPotential_count_of_parking
    parkingBoundStatement v hv

/-- A fixed absolute potential threshold for which the retained proportion
is exactly one half of the cycle-lemma lower bound. -/
theorem exists_goodPotential_half_count :
    ∃ B : ℚ, 0 < B ∧ ∀ v : ℕ, 1 ≤ v →
      (1 / 2 : ℚ) * (v : ℚ) ^ v ≤
        (v : ℚ) *
          ((Finset.univ.filter
            (GoodPotential B : (Fin v → Fin v) → Prop)).card : ℚ) := by
  refine ⟨3200000000, by norm_num, ?_⟩
  intro v hv
  exact goodPotential_half_count v hv

/-- Existential-constant form of `exists_goodPotential_half_count`. -/
theorem exists_goodPotential_count :
    ∃ B c : ℚ, 0 < B ∧ 0 < c ∧ ∀ v : ℕ, 1 ≤ v →
      c * (v : ℚ) ^ v ≤
        (v : ℚ) *
          ((Finset.univ.filter
            (GoodPotential B : (Fin v → Fin v) → Prop)).card : ℚ) := by
  refine ⟨3200000000, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro v hv
  exact goodPotential_half_count v hv

end Erdos896.Ford.Occupancy

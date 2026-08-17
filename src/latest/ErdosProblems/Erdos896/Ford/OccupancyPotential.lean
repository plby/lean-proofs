/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OccupancyPotentialCore
import ErdosProblems.Erdos896.Ford.OccupancyMultinomial

/-!
# Quadratic high-end caps for the occupancy potential

This file combines the exponential-potential estimate with the high-end
occupancy cap used in Ford's Lemma 4.9.  The counting argument selects the
balls in an overfull suffix, applies the generalized parking-word bound to
the remaining placement, and sums the resulting factorial tail.
-/

namespace Erdos896.Ford.Occupancy

open scoped BigOperators

def suffixOccupancy {v : ℕ} (f : Fin v → Fin v) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun t ↦ v - d ≤ (f t).val).card

/-- The last `i+1` boxes contain at most `M+(i+1)^2` balls. -/
def HighOccupancyCap {v : ℕ} (M : ℕ) (f : Fin v → Fin v) : Prop :=
  ∀ i : Fin v,
    (Finset.univ.filter fun t ↦ v - (i.val + 1) ≤ (f t).val).card ≤
      M + (i.val + 1) ^ 2

noncomputable instance {v M : ℕ} :
    DecidablePred (@HighOccupancyCap v M) := Classical.decPred _

theorem sum_pow_suffixOccupancy (v d : ℕ) (hd : d ≤ v) :
    (∑ f : Fin v → Fin v, (2 : ℝ) ^ suffixOccupancy f d) =
      (v + d : ℕ) ^ v := by
  classical
  let w : Fin v → ℝ := fun y ↦ if v - d ≤ y.val then 2 else 1
  have hwprod : ∀ f : Fin v → Fin v,
      (∏ i, w (f i)) = (2 : ℝ) ^ suffixOccupancy f d := by
    intro f
    simp only [w, suffixOccupancy, Finset.prod_ite, Finset.prod_const_one,
      one_pow]
    rw [Finset.prod_const]
    simp
  have hwsum : (∑ y : Fin v, w y) = (v + d : ℕ) := by
    have hc : (Finset.univ.filter fun y : Fin v ↦ v - d ≤ y.val).card = d := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin v)))
        (p := fun y : Fin v ↦ y.val < v - d)
      rw [Fin.card_filter_val_lt] at hpart
      simp only [Finset.card_univ, Fintype.card_fin, Nat.min_eq_right (Nat.sub_le v d),
        not_lt] at hpart
      omega
    have hccomp :
        (Finset.univ.filter fun y : Fin v ↦ ¬ v - d ≤ y.val).card = v - d := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin v)))
        (p := fun y : Fin v ↦ v - d ≤ y.val)
      rw [hc] at hpart
      simp only [Finset.card_univ, Fintype.card_fin] at hpart
      omega
    rw [show (∑ y : Fin v, w y) =
        (∑ y ∈ Finset.univ.filter (fun y : Fin v ↦ v - d ≤ y.val), (2 : ℝ)) +
          ∑ y ∈ Finset.univ.filter (fun y : Fin v ↦ ¬ v - d ≤ y.val), (1 : ℝ) by
      simp only [w, Finset.sum_ite]]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hc, hccomp]
    norm_num
    push_cast
    rw [Nat.cast_sub hd]
    ring
  calc
    (∑ f : Fin v → Fin v, (2 : ℝ) ^ suffixOccupancy f d) =
        ∑ f : Fin v → Fin v, ∏ i, w (f i) := by
          apply Finset.sum_congr rfl
          intro f hf
          exact (hwprod f).symm
    _ = (∑ y : Fin v, w y) ^ v := by
      symm
      simpa using (Finset.sum_pow' (Finset.univ : Finset (Fin v)) w v)
    _ = (v + d : ℕ) ^ v := by rw [hwsum]

private theorem card_filter_orderIsoOfFin
    {α : Type*} [Fintype α] [LinearOrder α]
    (S : Finset α) {n : ℕ} (hS : S.card = n) (p : α → Prop)
    [DecidablePred p] :
    ((Finset.univ : Finset (Fin n)).filter fun i ↦
        p (Finset.orderIsoOfFin S hS i)).card = (S.filter p).card := by
  let e := Finset.orderIsoOfFin S hS
  apply Finset.card_bij (fun i _hi ↦ (e i).val)
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
      rw [e.apply_symm_apply]
      exact hx.2
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx.1⟩)

private theorem card_cutSubset (v a : ℕ) :
    Fintype.card {S : Finset (Fin v) // S.card = a} = v.choose a := by
  rw [Fintype.card_subtype]
  rw [show ((Finset.univ : Finset (Finset (Fin v))).filter
      fun S ↦ S.card = a) =
      Finset.powersetCard a (Finset.univ : Finset (Fin v)) by
    ext S
    simp [Finset.mem_powersetCard]]
  simp

def GoodSuffixAtLeast {v : ℕ} (d a : ℕ) (f : Fin v → Fin v) : Prop :=
  Good f ∧ a ≤ suffixOccupancy f d

noncomputable instance {v : ℕ} (d a : ℕ) :
    DecidablePred (@GoodSuffixAtLeast v d a) := Classical.decPred _

private theorem card_goodSuffixAtLeast_le {v d a : ℕ}
    (hd : d ≤ v) (ha : a < v) :
    (Finset.univ.filter (@GoodSuffixAtLeast v d a)).card ≤
      v.choose a * d ^ a *
        (Finset.univ.filter
          (@Erdos896.Ford.generalizedParkingGood (v - a) 1 (a + 1))).card := by
  classical
  let E := {f : Fin v → Fin v // GoodSuffixAtLeast d a f}
  let C := {S : Finset (Fin v) // S.card = a}
  let A := Fin a → Fin d
  have hbox : (v - a) - 1 + (a + 1) = v := by omega
  let B := {g : Fin (v - a) → Fin ((v - a) - 1 + (a + 1)) //
    Erdos896.Ford.generalizedParkingGood (v - a) 1 (a + 1) g}
  let encode : E → C × A × B := fun x ↦ by
    let T := Finset.univ.filter fun i : Fin v ↦ v - d ≤ (x.1 i).val
    have hTa : a ≤ T.card := x.2.2
    let S := (Finset.exists_subset_card_eq hTa).choose
    have hST : S ⊆ T := (Finset.exists_subset_card_eq hTa).choose_spec.1
    have hS : S.card = a := (Finset.exists_subset_card_eq hTa).choose_spec.2
    let eA := Finset.orderIsoOfFin S hS
    have hScard : Sᶜ.card = v - a := by
      rw [Finset.card_compl, hS]
      simp
    let eB := Finset.orderIsoOfFin Sᶜ hScard
    let af : A := fun i ↦ ⟨(x.1 (eA i)).val - (v - d), by
      have hi := hST (eA i).property
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hxlt := (x.1 (eA i)).isLt
      omega⟩
    let bf : Fin (v - a) → Fin ((v - a) - 1 + (a + 1)) := fun i ↦
      Fin.cast hbox.symm (x.1 (eB i))
    have hbf : Erdos896.Ford.generalizedParkingGood (v - a) 1 (a + 1) bf := by
      intro r
      have hr : r.val ≤ v := by omega
      have hfilter :
          ((Finset.univ : Finset (Fin (v - a))).filter fun i ↦
              (bf i).val < r.val).card =
            (Sᶜ.filter fun i ↦ (x.1 i).val < r.val).card := by
        simpa only [bf, eB, Fin.val_cast] using
          card_filter_orderIsoOfFin Sᶜ hScard
            (fun i ↦ (x.1 i).val < r.val)
      rw [hfilter]
      have hsub : Sᶜ.filter (fun i ↦ (x.1 i).val < r.val) ⊆
          Finset.univ.filter (fun i : Fin v ↦ (x.1 i).val < r.val) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      have hcard := Finset.card_le_card hsub
      have hgood := cumulativeOccupancy_le x.2.1 hr
      change _ ≤ 1 + r.val - 1
      change _ ≤ cumulativeOccupancy x.1 r.val at hcard
      omega
    exact ⟨⟨S, hS⟩, af, ⟨bf, hbf⟩⟩
  have hencode : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hS : (encode x).1.val = (encode y).1.val :=
      congrArg (fun z : C × A × B ↦ z.1.val) hxy
    by_cases hi : i ∈ (encode x).1.val
    · have hiy : i ∈ (encode y).1.val := by simpa [← hS] using hi
      have hAeq := congrArg (fun z : C × A × B ↦ z.2.1) hxy
      dsimp only [encode] at hAeq
      let Sx := (Finset.exists_subset_card_eq x.2.2).choose
      let Sy := (Finset.exists_subset_card_eq y.2.2).choose
      let eAx := Finset.orderIsoOfFin Sx
        (Finset.exists_subset_card_eq x.2.2).choose_spec.2
      let eAy := Finset.orderIsoOfFin Sy
        (Finset.exists_subset_card_eq y.2.2).choose_spec.2
      let ex := Finset.orderIsoOfFin (encode x).1.val (encode x).1.property
      let ey := Finset.orderIsoOfFin (encode y).1.val (encode y).1.property
      let t : Fin a := ex.symm ⟨i, hi⟩
      have ht := congrFun hAeq t
      have ht' := congrArg Fin.val ht
      have exi : (ex t).val = i :=
        congrArg Subtype.val (ex.apply_symm_apply ⟨i, hi⟩)
      have hSco : (((encode x).1.val : Finset (Fin v)) : Set (Fin v)) =
          (((encode y).1.val : Finset (Fin v)) : Set (Fin v)) := by
        exact congrArg (fun s : Finset (Fin v) ↦ (s : Set (Fin v))) hS
      let cxy := OrderIso.setCongr
        (((encode x).1.val : Finset (Fin v)) : Set (Fin v))
        (((encode y).1.val : Finset (Fin v)) : Set (Fin v)) hSco
      have heq : ex.trans cxy = ey := Subsingleton.elim _ _
      have eyi : (ey t).val = i := by
        rw [← heq]
        change (cxy (ex t)).val = i
        simpa only [cxy, OrderIso.setCongr, exi]
      change (x.1 (eAx t)).val - (v - d) =
        (y.1 (eAy t)).val - (v - d) at ht'
      have heAx : eAx = ex := Subsingleton.elim _ _
      have heAy : eAy = ey := Subsingleton.elim _ _
      have hxge : v - d ≤ (x.1 i).val := by
        have hsub := (Finset.exists_subset_card_eq x.2.2).choose_spec.1 hi
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hsub
      have hyge : v - d ≤ (y.1 i).val := by
        have hsub := (Finset.exists_subset_card_eq y.2.2).choose_spec.1 hiy
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hsub
      rw [heAx, heAy, show (ex t).val = i by simpa only [ex] using exi,
        show (ey t).val = i by simpa only [ey] using eyi] at ht'
      apply Fin.ext
      omega
    · have hiy : i ∉ (encode y).1.val := by simpa [← hS] using hi
      have hBeq := congrArg (fun z : C × A × B ↦ z.2.2.val) hxy
      dsimp only [encode] at hBeq
      let Sx := (Finset.exists_subset_card_eq x.2.2).choose
      let Sy := (Finset.exists_subset_card_eq y.2.2).choose
      have hSxcard : Sxᶜ.card = v - a := by
        rw [Finset.card_compl,
          (Finset.exists_subset_card_eq x.2.2).choose_spec.2]
        simp
      have hSycard : Syᶜ.card = v - a := by
        rw [Finset.card_compl,
          (Finset.exists_subset_card_eq y.2.2).choose_spec.2]
        simp
      let eBx := Finset.orderIsoOfFin Sxᶜ hSxcard
      let eBy := Finset.orderIsoOfFin Syᶜ hSycard
      have hxcard : (encode x).1.valᶜ.card = v - a := by
        rw [Finset.card_compl, (encode x).1.property]
        simp
      have hycard : (encode y).1.valᶜ.card = v - a := by
        rw [Finset.card_compl, (encode y).1.property]
        simp
      let ex := Finset.orderIsoOfFin (encode x).1.valᶜ hxcard
      let ey := Finset.orderIsoOfFin (encode y).1.valᶜ hycard
      let t : Fin (v - a) := ex.symm ⟨i, by simpa using hi⟩
      have ht := congrFun hBeq t
      have ht' := congrArg Fin.val ht
      have exi : (ex t).val = i :=
        congrArg Subtype.val (ex.apply_symm_apply ⟨i, by simpa using hi⟩)
      have hScomp : (encode x).1.valᶜ = (encode y).1.valᶜ :=
        congrArg (·ᶜ) hS
      have hSco : ((((encode x).1.valᶜ : Finset (Fin v))) : Set (Fin v)) =
          ((((encode y).1.valᶜ : Finset (Fin v))) : Set (Fin v)) := by
        exact congrArg (fun s : Finset (Fin v) ↦ (s : Set (Fin v))) hScomp
      let cxy := OrderIso.setCongr
        ((((encode x).1.valᶜ : Finset (Fin v))) : Set (Fin v))
        ((((encode y).1.valᶜ : Finset (Fin v))) : Set (Fin v)) hSco
      have heq : ex.trans cxy = ey := Subsingleton.elim _ _
      have eyi : (ey t).val = i := by
        rw [← heq]
        change (cxy (ex t)).val = i
        simpa only [cxy, OrderIso.setCongr, exi]
      change (Fin.cast hbox.symm (x.1 (eBx t))).val =
        (Fin.cast hbox.symm (y.1 (eBy t))).val at ht'
      simp only [Fin.val_cast] at ht'
      have heBx : eBx = ex := Subsingleton.elim _ _
      have heBy : eBy = ey := Subsingleton.elim _ _
      rw [heBx, heBy, show (ex t).val = i by simpa only [ex] using exi,
        show (ey t).val = i by simpa only [ey] using eyi] at ht'
      exact Fin.ext ht'
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [E, C, A, B, Fintype.card_prod, card_cutSubset,
    Fintype.card_subtype, Nat.mul_assoc] using hcard

private theorem goodSuffixAtLeast_real_le {v d a : ℕ}
    (hd : d ≤ v) (ha : a < v) :
    (v : ℝ) *
        ((Finset.univ.filter (@GoodSuffixAtLeast v d a)).card : ℝ) ≤
      64 * (a + 1 : ℕ) ^ 3 * (d : ℝ) ^ a /
        (a.factorial : ℝ) * (v : ℝ) ^ v := by
  let C := (Finset.univ.filter
    (@Erdos896.Ford.generalizedParkingGood (v - a) 1 (a + 1))).card
  let H := (Finset.univ.filter (@GoodSuffixAtLeast v d a)).card
  have hn : 1 ≤ v - a := by omega
  have hp := Erdos896.Ford.generalizedParkingGood_card_bound_U_one
    (v - a) (a + 1) hn (by omega)
  have hbase : v - a - 1 + (a + 1) = v := by omega
  have hp' : (v - a) * C ≤ 64 * (a + 1) ^ 2 * v ^ (v - a) := by
    simpa only [C, Nat.one_mul, Nat.mul_one, hbase] using hp
  have hpR : ((v - a : ℕ) : ℝ) * (C : ℝ) ≤
      64 * ((a + 1 : ℕ) : ℝ) ^ 2 * (v : ℝ) ^ (v - a) := by
    exact_mod_cast hp'
  have hnR : (0 : ℝ) < ((v - a : ℕ) : ℝ) := by exact_mod_cast hn
  have hC : (C : ℝ) ≤
      (64 * ((a + 1 : ℕ) : ℝ) ^ 2 * (v : ℝ) ^ (v - a)) /
        ((v - a : ℕ) : ℝ) := by
    exact (le_div_iff₀ hnR).2 (by simpa [mul_comm] using hpR)
  have hinj := card_goodSuffixAtLeast_le hd ha
  have hinjR : (H : ℝ) ≤ (v.choose a : ℕ) * (d : ℝ) ^ a * (C : ℝ) := by
    exact_mod_cast hinj
  have hchoose : ((v.choose a : ℕ) : ℝ) ≤
      (v : ℝ) ^ a / (a.factorial : ℝ) :=
    Nat.choose_le_pow_div a v
  have hvdiv : (v : ℝ) / ((v - a : ℕ) : ℝ) ≤ (a + 1 : ℕ) := by
    apply (div_le_iff₀ hnR).2
    have hnat : v ≤ (a + 1) * (v - a) := by
      calc
        v = a * 1 + (v - a) := by omega
        _ ≤ a * (v - a) + (v - a) := by gcongr
        _ = (a + 1) * (v - a) := by ring
    exact_mod_cast hnat
  have hvpow : (v : ℝ) ^ a * (v : ℝ) ^ (v - a) = (v : ℝ) ^ v := by
    rw [← pow_add]
    congr
    omega
  calc
    (v : ℝ) * (H : ℝ) ≤
        (v : ℝ) * ((v.choose a : ℕ) * (d : ℝ) ^ a * (C : ℝ)) := by
          gcongr
    _ ≤ (v : ℝ) * (((v : ℝ) ^ a / (a.factorial : ℝ)) *
        (d : ℝ) ^ a *
          ((64 * ((a + 1 : ℕ) : ℝ) ^ 2 * (v : ℝ) ^ (v - a)) /
            (v - a : ℕ))) := by gcongr
    _ = 64 * ((a + 1 : ℕ) : ℝ) ^ 2 *
        ((v : ℝ) / ((v - a : ℕ) : ℝ)) *
          ((d : ℝ) ^ a / (a.factorial : ℝ)) * (v : ℝ) ^ v := by
            rw [← hvpow]
            ring
    _ ≤ 64 * ((a + 1 : ℕ) : ℝ) ^ 2 * (a + 1 : ℕ) *
          ((d : ℝ) ^ a / (a.factorial : ℝ)) * (v : ℝ) ^ v := by
            gcongr
    _ = 64 * (a + 1 : ℕ) ^ 3 * (d : ℝ) ^ a /
        (a.factorial : ℝ) * (v : ℝ) ^ v := by ring

private theorem card_goodSuffixAtLeast_full_le {v d : ℕ} (hd : d ≤ v) :
    (Finset.univ.filter (@GoodSuffixAtLeast v d v)).card ≤ d ^ v := by
  classical
  let E := {f : Fin v → Fin v // GoodSuffixAtLeast d v f}
  let encode : E → (Fin v → Fin d) := fun x i ↦ by
    have hset : (Finset.univ.filter fun t : Fin v ↦
        v - d ≤ (x.1 t).val) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa only [Finset.card_univ, Fintype.card_fin, suffixOccupancy] using x.2.2
    have hi : v - d ≤ (x.1 i).val := by
      have hi' : i ∈ (Finset.univ.filter fun t : Fin v ↦
          v - d ≤ (x.1 t).val) := by rw [hset]; simp
      exact (Finset.mem_filter.mp hi').2
    exact ⟨(x.1 i).val - (v - d), by have := (x.1 i).isLt; omega⟩
  have hencode : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have ht := congrFun hxy i
    have ht' := congrArg Fin.val ht
    change (x.1 i).val - (v - d) = (y.1 i).val - (v - d) at ht'
    have hxset : (Finset.univ.filter fun t : Fin v ↦
        v - d ≤ (x.1 t).val) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa only [Finset.card_univ, Fintype.card_fin, suffixOccupancy] using x.2.2
    have hyset : (Finset.univ.filter fun t : Fin v ↦
        v - d ≤ (y.1 t).val) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa only [Finset.card_univ, Fintype.card_fin, suffixOccupancy] using y.2.2
    have hxi : v - d ≤ (x.1 i).val := by
      have hi' : i ∈ (Finset.univ.filter fun t : Fin v ↦
          v - d ≤ (x.1 t).val) := by rw [hxset]; simp
      exact (Finset.mem_filter.mp hi').2
    have hyi : v - d ≤ (y.1 i).val := by
      have hi' : i ∈ (Finset.univ.filter fun t : Fin v ↦
          v - d ≤ (y.1 t).val) := by rw [hyset]; simp
      exact (Finset.mem_filter.mp hi').2
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [E, Fintype.card_fun, Fintype.card_subtype] using hcard

private theorem goodSuffixAtLeast_full_real_le {v d : ℕ}
    (hv : 1 ≤ v) (hd : d ≤ v) :
    (v : ℝ) *
        ((Finset.univ.filter (@GoodSuffixAtLeast v d v)).card : ℝ) ≤
      64 * (v + 1 : ℕ) ^ 3 * (d : ℝ) ^ v /
        (v.factorial : ℝ) * (v : ℝ) ^ v := by
  have hc := card_goodSuffixAtLeast_full_le hd
  have hcR :
      ((Finset.univ.filter (@GoodSuffixAtLeast v d v)).card : ℝ) ≤
        (d : ℝ) ^ v := by exact_mod_cast hc
  have hfac : v.factorial ≤ v ^ v := Nat.factorial_le_pow v
  have hcoefNat : v * v.factorial ≤ 64 * (v + 1) ^ 3 * v ^ v := by
    have hvcoef : v ≤ 64 * (v + 1) ^ 3 := by
      calc
        v ≤ v + 1 := by omega
        _ ≤ (v + 1) ^ 3 := Nat.le_pow (by omega)
        _ ≤ 64 * (v + 1) ^ 3 :=
          Nat.le_mul_of_pos_left _ (by omega)
    calc
      v * v.factorial ≤ v * v ^ v := Nat.mul_le_mul_left v hfac
      _ ≤ 64 * (v + 1) ^ 3 * v ^ v :=
        Nat.mul_le_mul_right (v ^ v) hvcoef
  have hcoef : (v : ℝ) ≤
      64 * ((v + 1 : ℕ) : ℝ) ^ 3 /
        (v.factorial : ℝ) * (v : ℝ) ^ v := by
    rw [show 64 * ((v + 1 : ℕ) : ℝ) ^ 3 /
        (v.factorial : ℝ) * (v : ℝ) ^ v =
      (64 * ((v + 1 : ℕ) : ℝ) ^ 3 * (v : ℝ) ^ v) /
        (v.factorial : ℝ) by ring]
    apply (le_div_iff₀ (show (0 : ℝ) < v.factorial by positivity)).2
    exact_mod_cast hcoefNat
  calc
    (v : ℝ) *
        ((Finset.univ.filter (@GoodSuffixAtLeast v d v)).card : ℝ) ≤
      (v : ℝ) * (d : ℝ) ^ v := by gcongr
    _ ≤ (64 * ((v + 1 : ℕ) : ℝ) ^ 3 /
        (v.factorial : ℝ) * (v : ℝ) ^ v) * (d : ℝ) ^ v := by gcongr
    _ = 64 * (v + 1 : ℕ) ^ 3 * (d : ℝ) ^ v /
        (v.factorial : ℝ) * (v : ℝ) ^ v := by ring

private theorem self_pow_div_factorial_le_exp_one_pow (a : ℕ) :
    (a : ℝ) ^ a / (a.factorial : ℝ) ≤ Real.exp 1 ^ a := by
  rw [← Real.exp_nat_mul, mul_one, Real.exp_eq_exp_ℝ,
    NormedSpace.exp_eq_tsum_div]
  exact Summable.le_tsum
    (show Summable (fun n : ℕ ↦ (a : ℝ) ^ n / (n.factorial : ℝ)) from
      Real.summable_pow_div_factorial (a : ℝ))
    a (fun _ _ ↦ by positivity)

private theorem pow_div_factorial_le_half_pow {d a : ℕ}
    (ha : 1 ≤ a) (hda : 6 * d ≤ a) :
    (d : ℝ) ^ a / (a.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ a := by
  have hself := self_pow_div_factorial_le_exp_one_pow a
  have hexp : Real.exp 1 ^ a ≤ (3 : ℝ) ^ a := by
    gcongr
    exact Real.exp_one_lt_three.le
  have hfacpos : (0 : ℝ) < a.factorial := by positivity
  have haa : (a : ℝ) ^ a ≤ (3 : ℝ) ^ a * (a.factorial : ℝ) := by
    exact (div_le_iff₀ hfacpos).mp (hself.trans hexp)
  have hpow : ((6 * d : ℕ) : ℝ) ^ a ≤ (a : ℝ) ^ a := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hda) a
  have hmain : (3 : ℝ) ^ a * ((2 : ℝ) ^ a * (d : ℝ) ^ a) ≤
      (3 : ℝ) ^ a * (a.factorial : ℝ) := by
    calc
      (3 : ℝ) ^ a * ((2 : ℝ) ^ a * (d : ℝ) ^ a) =
          ((6 * d : ℕ) : ℝ) ^ a := by
            rw [← mul_pow, ← mul_pow]
            simp only [Nat.cast_mul, Nat.cast_ofNat]
            congr 1 <;> ring
      _ ≤ (a : ℝ) ^ a := hpow
      _ ≤ (3 : ℝ) ^ a * (a.factorial : ℝ) := haa
  have hcancel : (2 : ℝ) ^ a * (d : ℝ) ^ a ≤ (a.factorial : ℝ) :=
    le_of_mul_le_mul_left hmain (by positivity)
  apply (div_le_iff₀ hfacpos).2
  rw [div_pow, one_pow]
  rw [show (1 : ℝ) / (2 : ℝ) ^ a * (a.factorial : ℝ) =
      (a.factorial : ℝ) / (2 : ℝ) ^ a by ring]
  exact (le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a by positivity)).2
    (by simpa only [mul_comm] using hcancel)

private noncomputable def highCapTail (n : ℕ) : ℝ :=
  (4 / 3 : ℝ) * n ^ 6 + (32 / 3 : ℝ) * n ^ 5 +
    (400 / 9 : ℝ) * n ^ 4 + (3520 / 27 : ℝ) * n ^ 3 +
      (7600 / 27 : ℝ) * n ^ 2 + (32864 / 81 : ℝ) * n + 71120 / 243

private theorem highCapTail_recurrence (n : ℕ) :
    highCapTail n = ((n + 1 : ℕ) : ℝ) ^ 6 + highCapTail (n + 1) / 4 := by
  unfold highCapTail
  norm_num
  push_cast
  ring

private theorem highCapTail_nonneg (n : ℕ) : 0 ≤ highCapTail n := by
  unfold highCapTail
  positivity

private theorem sum_sixth_geometric_with_tail (n : ℕ) :
    (∑ d ∈ Finset.range n, (((d + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ d) +
        highCapTail n / (4 : ℝ) ^ n = 71120 / 243 := by
  induction n with
  | zero => norm_num [highCapTail]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrec := highCapTail_recurrence n
      have hpow : (4 : ℝ) ^ (n + 1) = (4 : ℝ) ^ n * 4 := by rw [pow_succ]
      rw [hpow]
      calc
        (∑ d ∈ Finset.range n, (((d + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ d) +
              (((n + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ n +
              highCapTail (n + 1) / ((4 : ℝ) ^ n * 4) =
            (∑ d ∈ Finset.range n, (((d + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ d) +
              ((((n + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ n +
                highCapTail (n + 1) / ((4 : ℝ) ^ n * 4)) := by ring
        _ = (∑ d ∈ Finset.range n, (((d + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ d) +
              highCapTail n / (4 : ℝ) ^ n := by
            congr 1
            rw [hrec]
            field_simp
            <;> ring
        _ = 71120 / 243 := ih

private theorem sum_sixth_geometric_le (n : ℕ) :
    ∑ d ∈ Finset.range n, (((d + 1 : ℕ) : ℝ) ^ 6) / (4 : ℝ) ^ d ≤ 300 := by
  have h := sum_sixth_geometric_with_tail n
  have ht : 0 ≤ highCapTail n / (4 : ℝ) ^ n :=
    div_nonneg (highCapTail_nonneg n) (by positivity)
  have hc : (71120 / 243 : ℝ) ≤ 300 := by norm_num
  linarith

private theorem goodSuffixAtLeast_uniform_real_le {v d a : ℕ}
    (hv : 1 ≤ v) (hd : d ≤ v) :
    (v : ℝ) *
        ((Finset.univ.filter (@GoodSuffixAtLeast v d a)).card : ℝ) ≤
      64 * (a + 1 : ℕ) ^ 3 * (d : ℝ) ^ a /
        (a.factorial : ℝ) * (v : ℝ) ^ v := by
  rcases lt_trichotomy a v with hav | hav | hav
  · exact goodSuffixAtLeast_real_le hd hav
  · subst a
    exact goodSuffixAtLeast_full_real_le hv hd
  · have hempty :
        Finset.univ.filter (@GoodSuffixAtLeast v d a) = ∅ := by
      ext f
      constructor
      · intro hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          GoodSuffixAtLeast] at hf
        have hc : suffixOccupancy f d ≤ v := by
          simpa only [suffixOccupancy, Finset.card_univ, Fintype.card_fin] using
            Finset.card_le_card
              (Finset.filter_subset (fun t : Fin v ↦ v - d ≤ (f t).val)
                (Finset.univ : Finset (Fin v)))
        omega
      · simp
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity

private theorem goodSuffixAtLeast_cap_real_le {v d : ℕ}
    (hv : 1 ≤ v) (hd : 1 ≤ d) (hdv : d ≤ v) :
    (v : ℝ) *
        ((Finset.univ.filter
          (@GoodSuffixAtLeast v d (40 + d ^ 2 + 1))).card : ℝ) ≤
      (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) *
        ((d : ℝ) ^ 6 / (4 : ℝ) ^ (d - 1)) * (v : ℝ) ^ v := by
  let a := 40 + d ^ 2 + 1
  have hcount := goodSuffixAtLeast_uniform_real_le
    (a := a) hv hdv
  have h6da : 6 * d ≤ a := by
    have hs : (0 : ℝ) ≤ ((d : ℝ) - 3) ^ 2 := sq_nonneg _
    have hreal : (6 * d : ℕ) ≤ a := by
      exact_mod_cast (show (6 : ℝ) * d ≤ (a : ℝ) by
        dsimp only [a]
        push_cast
        nlinarith)
    exact hreal
  have hfac := pow_div_factorial_le_half_pow
    (d := d) (a := a) (by omega) h6da
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have ha1 : ((a + 1 : ℕ) : ℝ) ≤ 43 * (d : ℝ) ^ 2 := by
    dsimp only [a]
    push_cast
    nlinarith
  have ha1pow : ((a + 1 : ℕ) : ℝ) ^ 3 ≤
      (43 : ℝ) ^ 3 * (d : ℝ) ^ 6 := by
    calc
      ((a + 1 : ℕ) : ℝ) ^ 3 ≤ (43 * (d : ℝ) ^ 2) ^ 3 := by
        gcongr
      _ = (43 : ℝ) ^ 3 * (d : ℝ) ^ 6 := by ring
  have hexp : 38 + 2 * d ≤ a := by
    have hs : (0 : ℝ) ≤ ((d : ℝ) - 1) ^ 2 := sq_nonneg _
    exact_mod_cast (show (38 : ℝ) + 2 * d ≤ (a : ℝ) by
      dsimp only [a]
      push_cast
      nlinarith)
  have hhalf : (1 / 2 : ℝ) ^ a ≤
      (1 / 2 : ℝ) ^ (38 + 2 * d) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  have hhalf' : (1 / 2 : ℝ) ^ a ≤
      (1 / (2 : ℝ) ^ 40) * (1 / (4 : ℝ) ^ (d - 1)) := by
    calc
      (1 / 2 : ℝ) ^ a ≤ (1 / 2 : ℝ) ^ (38 + 2 * d) := hhalf
      _ = (1 / (2 : ℝ) ^ 40) * (1 / (4 : ℝ) ^ (d - 1)) := by
        rw [show 38 + 2 * d = 40 + 2 * (d - 1) by omega,
          pow_add, pow_mul]
        field_simp
        rw [← mul_pow]
        norm_num
  calc
    (v : ℝ) *
        ((Finset.univ.filter
          (@GoodSuffixAtLeast v d (40 + d ^ 2 + 1))).card : ℝ) ≤
      64 * ((a + 1 : ℕ) : ℝ) ^ 3 *
          ((d : ℝ) ^ a / (a.factorial : ℝ)) * (v : ℝ) ^ v := by
        convert hcount using 1 <;> ring
    _ ≤ 64 * ((a + 1 : ℕ) : ℝ) ^ 3 *
          (1 / 2 : ℝ) ^ a * (v : ℝ) ^ v := by gcongr
    _ ≤ 64 * ((43 : ℝ) ^ 3 * (d : ℝ) ^ 6) *
          ((1 / (2 : ℝ) ^ 40) *
            (1 / (4 : ℝ) ^ (d - 1))) * (v : ℝ) ^ v := by gcongr
    _ = (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) *
        ((d : ℝ) ^ 6 / (4 : ℝ) ^ (d - 1)) * (v : ℝ) ^ v := by
          ring_nf

private noncomputable def highCapBadCover (v : ℕ) :
    Finset (Fin v → Fin v) :=
  (Finset.range v).biUnion fun r ↦
    Finset.univ.filter
      (@GoodSuffixAtLeast v (r + 1) (40 + (r + 1) ^ 2 + 1))

private theorem good_not_highOccupancyCap_subset_cover (v : ℕ) :
    Finset.univ.filter
        (fun f : Fin v → Fin v ↦ Good f ∧ ¬ HighOccupancyCap 40 f) ⊆
      highCapBadCover v := by
  classical
  intro f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
  unfold HighOccupancyCap at hf
  push_neg at hf
  obtain ⟨i, hi⟩ := hf.2
  rw [highCapBadCover, Finset.mem_biUnion]
  refine ⟨i.val, by simpa using i.isLt, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    GoodSuffixAtLeast, suffixOccupancy]
  exact ⟨hf.1, by omega⟩

/-- The good placements which violate the quadratic cap on their final
boxes cost at most one quarter of the cycle-lemma lower bound. -/
theorem good_not_highOccupancyCap_count_real (v : ℕ) (hv : 1 ≤ v) :
    (v : ℝ) *
        ((Finset.univ.filter
          (fun f : Fin v → Fin v ↦ Good f ∧
            ¬ HighOccupancyCap 40 f)).card : ℝ) ≤
      (1 / 4 : ℝ) * (v : ℝ) ^ v := by
  classical
  let D := Finset.univ.filter
    (fun f : Fin v → Fin v ↦ Good f ∧ ¬ HighOccupancyCap 40 f)
  have hsub : D ⊆ highCapBadCover v :=
    good_not_highOccupancyCap_subset_cover v
  have hcardNat : D.card ≤
      ∑ r ∈ Finset.range v,
        (Finset.univ.filter
          (@GoodSuffixAtLeast v (r + 1)
            (40 + (r + 1) ^ 2 + 1))).card := by
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcard : (D.card : ℝ) ≤
      ∑ r ∈ Finset.range v,
        ((Finset.univ.filter
          (@GoodSuffixAtLeast v (r + 1)
            (40 + (r + 1) ^ 2 + 1))).card : ℝ) := by
    exact_mod_cast hcardNat
  have hpoint : ∀ r ∈ Finset.range v,
      (v : ℝ) *
          ((Finset.univ.filter
            (@GoodSuffixAtLeast v (r + 1)
              (40 + (r + 1) ^ 2 + 1))).card : ℝ) ≤
        (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) *
          ((((r + 1 : ℕ) : ℝ) ^ 6 / (4 : ℝ) ^ r)) *
            (v : ℝ) ^ v := by
    intro r hr
    have hrv : r + 1 ≤ v := by simpa using hr
    simpa only [Nat.add_sub_cancel] using
      (goodSuffixAtLeast_cap_real_le hv (by omega) hrv)
  have hsum := sum_sixth_geometric_le v
  have hcoef :
      (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) * 300 ≤ 1 / 4 := by
    norm_num
  change (v : ℝ) * (D.card : ℝ) ≤ (1 / 4 : ℝ) * (v : ℝ) ^ v
  calc
    (v : ℝ) * (D.card : ℝ) ≤
        (v : ℝ) *
          (∑ r ∈ Finset.range v,
            ((Finset.univ.filter
              (@GoodSuffixAtLeast v (r + 1)
                (40 + (r + 1) ^ 2 + 1))).card : ℝ)) := by gcongr
    _ = ∑ r ∈ Finset.range v,
          (v : ℝ) *
            ((Finset.univ.filter
              (@GoodSuffixAtLeast v (r + 1)
                (40 + (r + 1) ^ 2 + 1))).card : ℝ) := by
          simp only [Finset.mul_sum]
    _ ≤ ∑ r ∈ Finset.range v,
          (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) *
            ((((r + 1 : ℕ) : ℝ) ^ 6 / (4 : ℝ) ^ r)) *
              (v : ℝ) ^ v := by
          exact Finset.sum_le_sum fun r hr ↦ hpoint r hr
    _ = (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) *
          (∑ r ∈ Finset.range v,
            (((r + 1 : ℕ) : ℝ) ^ 6 / (4 : ℝ) ^ r)) *
              (v : ℝ) ^ v := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (64 * (43 : ℝ) ^ 3 / (2 : ℝ) ^ 40) * 300 *
          (v : ℝ) ^ v := by gcongr
    _ ≤ (1 / 4 : ℝ) * (v : ℝ) ^ v := by gcongr

/-- A single-box consequence of the cumulative cap. -/
theorem highOccupancyCap_box_le {v M : ℕ} {f : Fin v → Fin v}
    (hcap : HighOccupancyCap M f) (j : Fin v) :
    boxOccupancy f j ≤ M + (v - j.val) ^ 2 := by
  let i : Fin v := ⟨v - j.val - 1, by omega⟩
  have h := hcap i
  have hsub :
      Finset.univ.filter (fun t : Fin v ↦ f t = j) ⊆
        Finset.univ.filter
          (fun t : Fin v ↦ v - (i.val + 1) ≤ (f t).val) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [ht]
    dsimp only [i]
    omega
  have hc := Finset.card_le_card hsub
  unfold boxOccupancy
  have hrhs : M + (i.val + 1) ^ 2 = M + (v - j.val) ^ 2 := by
    dsimp only [i]
    congr 2
    omega
  rw [← hrhs]
  exact hc.trans h

/-- The number of balls in any suffix is determined by the occupancy
vector. -/
theorem suffixOccupancy_eq_of_occupancyVector_eq {v d : ℕ}
    {f g : Fin v → Fin v} (hfg : occupancyVector f = occupancyVector g) :
    suffixOccupancy f d = suffixOccupancy g d := by
  classical
  have hbox : ∀ j, boxOccupancy f j = boxOccupancy g j := by
    intro j
    exact congrFun hfg j
  let p := permOfSameOccupancy f g hbox
  unfold suffixOccupancy
  apply Finset.card_bij (fun i _hi ↦ p i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    change v - d ≤ (g (permOfSameOccupancy f g hbox i)).val
    rw [permOfSameOccupancy_map f g hbox i]
    exact hi
  · intro i₁ hi₁ i₂ hi₂ heq
    exact p.injective heq
  · intro y hy
    refine ⟨p.symm y, ?_, p.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    change v - d ≤ (f (p.symm y)).val
    rw [← permOfSameOccupancy_map f g hbox (p.symm y),
      p.apply_symm_apply]
    exact hy

/-- The high-end cap is invariant on multinomial occupancy fibers. -/
theorem highOccupancyCap_iff_of_occupancyVector_eq {v M : ℕ}
    {f g : Fin v → Fin v} (hfg : occupancyVector f = occupancyVector g) :
    HighOccupancyCap M f ↔ HighOccupancyCap M g := by
  unfold HighOccupancyCap
  constructor
  · intro h (i : Fin v)
    change suffixOccupancy g (i.val + 1) ≤ M + (i.val + 1) ^ 2
    change ∀ i : Fin v,
      suffixOccupancy f (i.val + 1) ≤ M + (i.val + 1) ^ 2 at h
    rw [← suffixOccupancy_eq_of_occupancyVector_eq (d := i.val + 1) hfg]
    exact h i
  · intro h (i : Fin v)
    change suffixOccupancy f (i.val + 1) ≤ M + (i.val + 1) ^ 2
    change ∀ i : Fin v,
      suffixOccupancy g (i.val + 1) ≤ M + (i.val + 1) ^ 2 at h
    rw [suffixOccupancy_eq_of_occupancyVector_eq (d := i.val + 1) hfg]
    exact h i

/-- The cap-selected placements form a union of complete multinomial
occupancy fibers. -/
theorem highOccupancyCap_occupancyInvariant {v M : ℕ} :
    OccupancyInvariant
      (Finset.univ.filter (@HighOccupancyCap v M)) := by
  intro f g hfg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact highOccupancyCap_iff_of_occupancyVector_eq hfg

/-- At least one quarter of the cycle-lemma lower bound simultaneously has
bounded exponential potential and the quadratic cap on the last boxes. -/
theorem goodPotential_highCap_quarter_count (v : ℕ) (hv : 1 ≤ v) :
    (1 / 4 : ℚ) * (v : ℚ) ^ v ≤
      (v : ℚ) *
        ((Finset.univ.filter
          (fun f : Fin v → Fin v ↦
            GoodPotential (3200000000 : ℚ) f ∧
              HighOccupancyCap 40 f)).card : ℚ) := by
  classical
  let P := Finset.univ.filter
    (@GoodPotential v (3200000000 : ℚ))
  let C := Finset.univ.filter
    (fun f : Fin v → Fin v ↦
      GoodPotential (3200000000 : ℚ) f ∧ HighOccupancyCap 40 f)
  let D := Finset.univ.filter
    (fun f : Fin v → Fin v ↦
      GoodPotential (3200000000 : ℚ) f ∧ ¬ HighOccupancyCap 40 f)
  have hpartition : P = C ∪ D := by
    ext f
    simp only [P, C, D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    tauto
  have hdisj : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro f hfC hfD
    simp only [C, D, Finset.mem_filter, Finset.mem_univ, true_and] at hfC hfD
    exact hfD.2 hfC.2
  have hcardpart : P.card = C.card + D.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisj]
  let H := Finset.univ.filter
    (fun f : Fin v → Fin v ↦ Good f ∧ ¬ HighOccupancyCap 40 f)
  have hDH : D ⊆ H := by
    intro f hf
    have hfD := (Finset.mem_filter.mp hf).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨hfD.1.1, hfD.2⟩⟩
  have hcardDH : D.card ≤ H.card := Finset.card_le_card hDH
  have hhalfQ := goodPotential_half_count v hv
  have hhalf : (1 / 2 : ℝ) * (v : ℝ) ^ v ≤
      (v : ℝ) * (P.card : ℝ) := by
    have hhalfQ' : (1 / 2 : ℚ) * (v : ℚ) ^ v ≤
        (v : ℚ) * (P.card : ℚ) := by
      simpa only [P] using hhalfQ
    have hc := (Rat.cast_le (K := ℝ)).2 hhalfQ'
    norm_num [Rat.cast_pow] at hc ⊢
    exact hc
  have hbadH := good_not_highOccupancyCap_count_real v hv
  have hbadD : (v : ℝ) * (D.card : ℝ) ≤
      (1 / 4 : ℝ) * (v : ℝ) ^ v := by
    calc
      (v : ℝ) * (D.card : ℝ) ≤ (v : ℝ) * (H.card : ℝ) := by
        gcongr
      _ ≤ (1 / 4 : ℝ) * (v : ℝ) ^ v := by
        simpa only [H] using hbadH
  have hpart : (P.card : ℝ) = (C.card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast hcardpart
  have hreal : (1 / 4 : ℝ) * (v : ℝ) ^ v ≤
      (v : ℝ) * (C.card : ℝ) := by
    rw [hpart] at hhalf
    nlinarith [show (0 : ℝ) ≤ v by positivity]
  have hc : (((1 / 4 : ℚ) * (v : ℚ) ^ v : ℚ) : ℝ) ≤
      (((v : ℚ) * (C.card : ℚ) : ℚ) : ℝ) := by
    norm_num [Rat.cast_pow]
    exact hreal
  exact (Rat.cast_le (K := ℝ)).mp (by simpa only [C] using hc)

/-- Fixed-constant form of the capped occupancy-potential theorem. -/
theorem exists_goodPotential_highCap_quarter_count :
    ∃ M : ℕ, ∃ B : ℚ, 0 < B ∧ ∀ v : ℕ, 1 ≤ v →
      (1 / 4 : ℚ) * (v : ℚ) ^ v ≤
        (v : ℚ) *
          ((Finset.univ.filter
            (fun f : Fin v → Fin v ↦
              GoodPotential B f ∧ HighOccupancyCap M f)).card : ℚ) := by
  refine ⟨40, 3200000000, by norm_num, ?_⟩
  intro v hv
  exact goodPotential_highCap_quarter_count v hv

/-- Existential-constant form of the capped occupancy-potential theorem. -/
theorem exists_goodPotential_highCap_count :
    ∃ M : ℕ, ∃ B c : ℚ, 0 < B ∧ 0 < c ∧ ∀ v : ℕ, 1 ≤ v →
      c * (v : ℚ) ^ v ≤
        (v : ℚ) *
          ((Finset.univ.filter
            (fun f : Fin v → Fin v ↦
              GoodPotential B f ∧ HighOccupancyCap M f)).card : ℚ) := by
  refine ⟨40, 3200000000, 1 / 4, by norm_num, by norm_num, ?_⟩
  intro v hv
  exact goodPotential_highCap_quarter_count v hv

end Erdos896.Ford.Occupancy

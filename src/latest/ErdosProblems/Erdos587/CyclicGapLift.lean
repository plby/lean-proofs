import ErdosProblems.Erdos587.BohrProgression
import ErdosProblems.Erdos587.FreimanLift

open scoped BigOperators Pointwise

namespace Erdos587

noncomputable section

/-! ## Linearizing a Freiman map on a cyclic progression -/

structure IntegerGeneralizedAP where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace IntegerGeneralizedAP

abbrev Param (Q : IntegerGeneralizedAP) :=
  (i : Fin Q.rank) → Fin (Q.length i + 1)

def eval (Q : IntegerGeneralizedAP) (x : Q.Param) : ℤ :=
  Q.base + ∑ i, (x i : ℤ) * Q.step i

noncomputable def carrier (Q : IntegerGeneralizedAP) : Finset ℤ :=
  (Finset.univ : Finset Q.Param).image Q.eval

def Proper (Q : IntegerGeneralizedAP) : Prop := Function.Injective Q.eval

lemma mem_carrier_iff (Q : IntegerGeneralizedAP) {z : ℤ} :
    z ∈ Q.carrier ↔ ∃ x : Q.Param, Q.eval x = z := by
  simp [carrier]

lemma card_carrier_of_proper (Q : IntegerGeneralizedAP) (hQ : Q.Proper) :
    Q.carrier.card = ∏ i, (Q.length i + 1) := by
  rw [carrier, Finset.card_image_of_injective _ hQ, Finset.card_univ]
  simp [Param]

end IntegerGeneralizedAP

namespace CyclicCenteredGAP

variable {N : ℕ}

def minParam (Q : CyclicCenteredGAP N) : Q.Param := fun _ => 0

def unitParam (Q : CyclicCenteredGAP N) (i : Fin Q.rank)
    (hi : 0 < Q.radius i) : Q.Param := fun j =>
  if hji : j = i then ⟨1, by subst j; omega⟩ else 0

def predParam (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) : Q.Param := fun j =>
  if hji : j = i then
    ⟨(x i : ℕ) - 1, by
      subst j
      have hx := (x i).isLt
      omega⟩
  else x j

@[simp] lemma minParam_apply (Q : CyclicCenteredGAP N) (i : Fin Q.rank) :
    (Q.minParam i : ℕ) = 0 := rfl

@[simp] lemma unitParam_apply_self (Q : CyclicCenteredGAP N)
    (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    (Q.unitParam i hi i : ℕ) = 1 := by
  simp [unitParam]

@[simp] lemma unitParam_apply_ne (Q : CyclicCenteredGAP N)
    (i j : Fin Q.rank) (hi : 0 < Q.radius i) (hji : j ≠ i) :
    (Q.unitParam i hi j : ℕ) = 0 := by
  simp [unitParam, hji]

@[simp] lemma predParam_apply_self (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (Q.predParam x i hi i : ℕ) = (x i : ℕ) - 1 := by
  simp [predParam]

@[simp] lemma predParam_apply_ne (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i j : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hji : j ≠ i) :
    (Q.predParam x i hi j : ℕ) = x j := by
  simp [predParam, hji]

lemma eval_eq_eval_minParam_add_sum {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param) :
    Q.eval x = Q.eval Q.minParam +
      ∑ i, (x i : ZMod N) * Q.step i := by
  simp only [eval, coeff, minParam, Fin.zero_eta, Fin.val_zero,
    Nat.cast_zero, Int.ofNat_eq_coe, Int.cast_sub, Int.cast_natCast,
    zero_sub, neg_mul, Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Int.cast_neg, Int.cast_natCast]
  ring

lemma eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    Q.eval (Q.unitParam i hi) = Q.eval Q.minParam + Q.step i := by
  rw [Q.eval_eq_eval_minParam_add_sum]
  congr 1
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  simp only [unitParam_apply_self, Nat.cast_one, one_mul]
  have hzero : ∑ j ∈ Finset.univ.erase i,
      ((Q.unitParam i hi j : ℕ) : ZMod N) * Q.step j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by
      exact Finset.ne_of_mem_erase hj
    simp [Q.unitParam_apply_ne i j hi hji]
  rw [hzero, zero_add]

lemma eval_predParam_add_eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    Q.eval (Q.predParam x i hi) + Q.eval (Q.unitParam i hradius) =
      Q.eval x + Q.eval Q.minParam := by
  have hpred := Q.eval_eq_eval_minParam_add_sum (Q.predParam x i hi)
  have hunit := Q.eval_unitParam i hradius
  have hx := Q.eval_eq_eval_minParam_add_sum x
  rw [hpred, hunit, hx]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          Q.step i =
        ∑ j, (x j : ZMod N) * Q.step j := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => (x j : ZMod N) * Q.step j) (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j =
      ∑ j ∈ Finset.univ.erase i, (x j : ZMod N) * Q.step j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Q.predParam_apply_ne x i j hi hji]
    rw [hrest, Q.predParam_apply_self]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    push_cast
    rw [← hxi]
    push_cast
    ring
  calc
    Q.eval Q.minParam +
          (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          (Q.eval Q.minParam + Q.step i) =
        Q.eval Q.minParam + Q.eval Q.minParam +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
            Q.step i) := by abel
    _ = Q.eval Q.minParam + Q.eval Q.minParam +
          ∑ j, (x j : ZMod N) * Q.step j := by rw [hsum]
    _ = Q.eval Q.minParam + (∑ j, (x j : ZMod N) * Q.step j) +
          Q.eval Q.minParam := by abel

lemma sum_predParam_add_one (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (∑ j, (Q.predParam x i hi j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ)) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Q.predParam x i hi j : ℕ) =
        ∑ j ∈ Finset.univ.erase i, (x j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)
  rw [hrest, Q.predParam_apply_self]
  omega

end CyclicCenteredGAP

noncomputable def cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) : IntegerGeneralizedAP where
  rank := Q.rank
  base := L (Q.eval Q.minParam)
  step i := if hi : 0 < Q.radius i then
      L (Q.eval (Q.unitParam i hi)) - L (Q.eval Q.minParam)
    else 0
  length i := 2 * Q.radius i

@[simp] lemma cyclicGapFreimanImage_rank {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) :
    (cyclicGapFreimanImage Q L).rank = Q.rank := rfl

@[simp] lemma cyclicGapFreimanImage_length {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) (i : Fin Q.rank) :
    (cyclicGapFreimanImage Q L).length i = 2 * Q.radius i := rfl

lemma eval_cyclicGapFreimanImage_pred_add_step {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    (cyclicGapFreimanImage Q L).eval x =
      (cyclicGapFreimanImage Q L).eval (Q.predParam x i hi) +
        ((cyclicGapFreimanImage Q L).step i) := by
  simp only [IntegerGeneralizedAP.eval, cyclicGapFreimanImage, dif_pos hradius]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
          (if hj : 0 < Q.radius j then
            L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
        (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) =
      ∑ j, ((x j : ℕ) : ℤ) *
          (if hj : 0 < Q.radius j then
            L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => ((x j : ℕ) : ℤ) *
        (if hj : 0 < Q.radius j then
          L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0))
      (Finset.mem_univ i)]
    have hrest :
        ∑ j ∈ Finset.univ.erase i, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) =
          ∑ j ∈ Finset.univ.erase i, ((x j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)]
    rw [hrest, Q.predParam_apply_self]
    simp only [dif_pos hradius]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    have hxiZ : (((x i : ℕ) - 1 : ℕ) : ℤ) + 1 = (x i : ℤ) := by
      exact_mod_cast hxi
    linear_combination
      (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) * hxiZ
  calc
    L (Q.eval Q.minParam) +
          ∑ j, ((x j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) =
        L (Q.eval Q.minParam) +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
            (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam))) := by
              rw [hsum]
    _ = (L (Q.eval Q.minParam) +
          ∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
          (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) := by
            ring

theorem eval_cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (D : Finset (ZMod N))
    (hQD : Q.carrier ⊆ D) (L : ZMod N → ℤ)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d)
    (x : Q.Param) :
    (cyclicGapFreimanImage Q L).eval x = L (Q.eval x) := by
  classical
  have hmem (y : Q.Param) : Q.eval y ∈ D := by
    apply hQD
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  induction hweight : (∑ i, (x i : ℕ)) using Nat.strong_induction_on generalizing x with
  | h k ih =>
      by_cases hk : k = 0
      · have hsumzero : ∑ i, (x i : ℕ) = 0 := hweight.trans hk
        have hxzero (i : Fin Q.rank) : (x i : ℕ) = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun _ _ => Nat.zero_le _)).mp hsumzero i (Finset.mem_univ i)
        have hx : x = Q.minParam := by
          funext i
          apply Fin.ext
          exact hxzero i
        subst x
        simp [IntegerGeneralizedAP.eval, cyclicGapFreimanImage,
          CyclicCenteredGAP.minParam]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hsumpos : 0 < ∑ i, (x i : ℕ) := by omega
        rw [Finset.sum_pos_iff_of_nonneg (by simp)] at hsumpos
        obtain ⟨i, _hiuniv, hi⟩ := hsumpos
        have hradius : 0 < Q.radius i := by
          have hix := (x i).isLt
          change (x i : ℕ) < 2 * Q.radius i + 1 at hix
          omega
        let y := Q.predParam x i hi
        have hyweight : (∑ j, (y j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
          exact Q.sum_predParam_add_one x i hi
        have hylt : (∑ j, (y j : ℕ)) < k := by omega
        have ihy : (cyclicGapFreimanImage Q L).eval y = L (Q.eval y) :=
          ih _ hylt y rfl
        have hrel : L (Q.eval y) + L (Q.eval (Q.unitParam i hradius)) =
            L (Q.eval x) + L (Q.eval Q.minParam) := by
          apply hadd (hmem y) (hmem (Q.unitParam i hradius))
            (hmem x) (hmem Q.minParam)
          exact Q.eval_predParam_add_eval_unitParam x i hi hradius
        rw [eval_cyclicGapFreimanImage_pred_add_step Q L x i hi hradius, ihy]
        simp only [cyclicGapFreimanImage, dif_pos hradius]
        omega

theorem proper_cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (hQ : Q.Proper)
    (D : Finset (ZMod N)) (hQD : Q.carrier ⊆ D)
    (L : ZMod N → ℤ) (hLinj : Set.InjOn L D)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d) :
    (cyclicGapFreimanImage Q L).Proper := by
  intro x y hxy
  have hx := eval_cyclicGapFreimanImage Q D hQD L hadd x
  have hy := eval_cyclicGapFreimanImage Q D hQD L hadd y
  rw [hx, hy] at hxy
  apply hQ
  exact hLinj (by
    apply hQD
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩) (by
    apply hQD
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩) hxy

theorem carrier_cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (D : Finset (ZMod N))
    (hQD : Q.carrier ⊆ D) (L : ZMod N → ℤ)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d) :
    (cyclicGapFreimanImage Q L).carrier = Q.carrier.image L := by
  ext z
  simp only [IntegerGeneralizedAP.mem_carrier_iff, Finset.mem_image]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Q.eval x, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    · exact (eval_cyclicGapFreimanImage Q D hQD L hadd x).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨x, eval_cyclicGapFreimanImage Q D hQD L hadd x⟩

/-!
## Lifting a cyclic progression back through a Freiman model

The inverse of an order-eight Freiman isomorphism extends to the fourfold
difference set.  On a proper cyclic GAP the preceding linearization theorem
turns that extension into a proper affine GAP in `ℤ`, with no loss of rank or
cardinality.
-/

theorem exists_proper_integerGAP_lift_of_cyclic
    {N : ℕ} [NeZero N]
    (A : Finset ℤ) (B : Finset (ZMod N)) (hB : B.Nonempty)
    (f : ℤ → ZMod N)
    (hf : IsAddFreimanIso 8 (A : Set ℤ) (B : Set (ZMod N)) f)
    (Q : CyclicCenteredGAP N) (hQproper : Q.Proper)
    (hQsub : Q.carrier ⊆ 2 • B - 2 • B) :
    ∃ P : IntegerGeneralizedAP,
      P.rank = Q.rank ∧
      P.Proper ∧
      P.carrier ⊆ 2 • A - 2 • A ∧
      P.carrier.card = Q.carrier.card := by
  let g : ZMod N → ℤ := Function.invFunOn f (A : Set ℤ)
  have hg : IsAddFreimanIso 8 (B : Set (ZMod N)) (A : Set ℤ) g := by
    simpa only [g] using hf.invFunOn
  let D : Finset (ZMod N) := 2 • B - 2 • B
  let L : ZMod N → ℤ := freimanFourfoldLift B hB g
  have hLinj : Set.InjOn L D := by
    simpa only [L, D] using
      (freimanFourfoldLift_injOn hB (hg.mono (hmn := by omega)))
  have hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d := by
    intro a b c d ha hb hc hd hab
    exact (freimanFourfoldLift_add_eq_add hB hg ha hb hc hd).mpr hab
  let P : IntegerGeneralizedAP := cyclicGapFreimanImage Q L
  have hPproper : P.Proper := by
    exact proper_cyclicGapFreimanImage Q hQproper D hQsub L hLinj hadd
  have hPcarrier : P.carrier = Q.carrier.image L := by
    exact carrier_cyclicGapFreimanImage Q D hQsub L hadd
  refine ⟨P, rfl, hPproper, ?_, ?_⟩
  · rw [hPcarrier]
    intro z hz
    obtain ⟨x, hxQ, rfl⟩ := Finset.mem_image.mp hz
    exact freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul hB
      hg.bijOn.mapsTo (hQsub hxQ)
  · rw [hPcarrier]
    exact Finset.card_image_of_injOn (hLinj.mono hQsub)

end

end Erdos587

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.ParkingAbelTail

/-!
# Finite confined parking words

This file contains the finite first-empty decomposition for the confined
parking words occurring in Ford's order-statistics bound.  It is deliberately
independent of `GeneralizedParkingUpper`: the latter imports this file and
identifies its reverse-bin predicate with `confinedParkingGood` below.
-/

namespace Erdos896.Ford

open scoped BigOperators

/-- A word of length `k` on `k - U + W` letters satisfies the reverse parking
barriers.  The index `s` is zero based. -/
def confinedParkingGood (k U W : ℕ)
    (f : Fin k → Fin (k - U + W)) : Prop :=
  ∀ s < k - U + 1,
    s + 1 ≤
      ((Finset.univ.filter fun i ↦ (f i).val < W + s).card)

noncomputable instance (k U W : ℕ) :
    DecidablePred (@confinedParkingGood k U W) :=
  Classical.decPred _

/-- The ordinary `W`-parking condition on `j` labelled cars.  There are
`j - 1 + W` linear places. -/
def ordinaryParkingGood (j W : ℕ)
    (f : Fin j → Fin (j - 1 + W)) : Prop :=
  ∀ s < j,
    s + 1 ≤
      ((Finset.univ.filter fun i ↦ (f i).val < W + s).card)

noncomputable instance (j W : ℕ) :
    DecidablePred (@ordinaryParkingGood j W) :=
  Classical.decPred _

/-- A reverse parking word first fails at `j`. -/
def confinedParkingFirstFailure {k U W : ℕ}
    (f : Fin k → Fin (k - U + W)) (j : ℕ) : Prop :=
  (∀ s < j,
      s + 1 ≤
        ((Finset.univ.filter fun i ↦ (f i).val < W + s).card)) ∧
    ((Finset.univ.filter fun i ↦ (f i).val < W + j).card < j + 1)

noncomputable instance (k U W j : ℕ) :
    DecidablePred (fun f : Fin k → Fin (k - U + W) ↦
      confinedParkingFirstFailure f j) :=
  Classical.decPred _

theorem confinedParkingFirstFailure_unique
    {k U W : ℕ} {f : Fin k → Fin (k - U + W)} {i j : ℕ}
    (hi : confinedParkingFirstFailure f i)
    (hj : confinedParkingFirstFailure f j) : i = j := by
  unfold confinedParkingFirstFailure at hi hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (Nat.not_lt_of_ge (hj.1 i hij)) hi.2
  · exact (Nat.not_lt_of_ge (hi.1 j hji)) hj.2

private theorem card_filter_eq_of_firstFailure
    {k U W j : ℕ} {f : Fin k → Fin (k - U + W)}
    (hf : confinedParkingFirstFailure f j) :
    (Finset.univ.filter fun i ↦ (f i).val < W + j).card = j := by
  have hle :
      (Finset.univ.filter fun i ↦ (f i).val < W + j).card ≤ j := by
    exact Nat.le_of_lt_succ hf.2
  by_cases hj0 : j = 0
  · omega
  · have hprev := hf.1 (j - 1) (by omega)
    have hprev' : j ≤
        (Finset.univ.filter fun i ↦ (f i).val < W + (j - 1)).card := by
      convert hprev using 1 <;> omega
    have hsub :
        (Finset.univ.filter fun i ↦ (f i).val < W + (j - 1)) ⊆
          Finset.univ.filter fun i ↦ (f i).val < W + j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega
    have hcard := Finset.card_le_card hsub
    omega

private abbrev labelSubset (k j : ℕ) :=
  {S : Finset (Fin k) // S.card = j}

private theorem card_labelSubset (k j : ℕ) :
    Fintype.card (labelSubset k j) = k.choose j := by
  classical
  unfold labelSubset
  rw [Fintype.card_subtype]
  rw [show ((Finset.univ : Finset (Finset (Fin k))).filter
      fun S ↦ S.card = j) =
      Finset.powersetCard j (Finset.univ : Finset (Fin k)) by
    ext S
    simp [Finset.mem_powersetCard]]
  simp

private abbrev ordinaryParkingWord (j W : ℕ) :=
  {f : Fin j → Fin (j - 1 + W) // ordinaryParkingGood j W f}

private abbrev firstFailureCode (k U W j : ℕ) :=
  labelSubset k j × ordinaryParkingWord j W ×
    (Fin (k - j) → Fin (k - U - j))

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

private theorem card_ordinaryParkingWord (j W : ℕ) :
    Fintype.card (ordinaryParkingWord j W) =
      (Finset.univ.filter (@ordinaryParkingGood j W)).card := by
  classical
  unfold ordinaryParkingWord
  rw [Fintype.card_subtype]

private theorem card_firstFailureCode (k U W j : ℕ) :
    Fintype.card (firstFailureCode k U W j) =
      k.choose j *
        (Finset.univ.filter (@ordinaryParkingGood j W)).card *
          (k - U - j) ^ (k - j) := by
  classical
  unfold firstFailureCode
  rw [Fintype.card_prod, Fintype.card_prod, card_labelSubset,
    card_ordinaryParkingWord]
  simp [mul_assoc]

private def decodeFirstFailure
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) : Fin k → Fin (k - U + W) := by
  let S := c.1.1
  have hS : S.card = j := c.1.2
  have hSc : Sᶜ.card = k - j := by
    rw [Finset.card_compl, hS]
    simp
  let eL := (Finset.orderIsoOfFin S hS).toEquiv
  let eR := (Finset.orderIsoOfFin Sᶜ hSc).toEquiv
  intro i
  by_cases hi : i ∈ S
  · let q : Fin j := eL.symm ⟨i, hi⟩
    exact ⟨(c.2.1.1 q).val, by
      have hleft : (c.2.1.1 q).val < j - 1 + W := (c.2.1.1 q).isLt
      omega⟩
  · have hic : i ∈ Sᶜ := by simp [hi]
    let q : Fin (k - j) := eR.symm ⟨i, hic⟩
    exact ⟨W + j + (c.2.2 q).val, by
      have hright : (c.2.2 q).val < k - U - j := (c.2.2 q).isLt
      omega⟩

private theorem decodeFirstFailure_mem_left
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) (i : Fin k) (hi : i ∈ c.1.1) :
    (decodeFirstFailure hUk hj c i).val < j - 1 + W := by
  simp only [decodeFirstFailure, hi, dite_true]
  exact (c.2.1.1 _).isLt

private theorem decodeFirstFailure_mem_right
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) (i : Fin k) (hi : i ∉ c.1.1) :
    W + j ≤ (decodeFirstFailure hUk hj c i).val := by
  simp only [decodeFirstFailure, hi, dite_false]
  omega

private theorem decodeFirstFailure_left_apply
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) (q : Fin j) :
    (decodeFirstFailure hUk hj c
        (Finset.orderIsoOfFin c.1.1 c.1.2 q).val).val =
      (c.2.1.1 q).val := by
  let e := Finset.orderIsoOfFin c.1.1 c.1.2
  simp only [decodeFirstFailure]
  split
  · rename_i hi
    have hidx : e.symm ⟨(e q).val, hi⟩ = q := by
      apply e.injective
      rw [e.apply_symm_apply]
    change (c.2.1.1 (e.symm ⟨(e q).val, hi⟩)).val =
      (c.2.1.1 q).val
    exact congrArg (fun z : Fin j ↦ (c.2.1.1 z).val) hidx
  · rename_i hi
    exact False.elim (hi (e q).property)

private theorem decodeFirstFailure_right_apply
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) (q : Fin (k - j)) :
    (decodeFirstFailure hUk hj c
        (Finset.orderIsoOfFin c.1.1ᶜ (by
          rw [Finset.card_compl, c.1.2]
          simp) q).val).val =
      W + j + (c.2.2 q).val := by
  have hcard : c.1.1ᶜ.card = k - j := by
    rw [Finset.card_compl, c.1.2]
    simp
  let e := Finset.orderIsoOfFin c.1.1ᶜ hcard
  simp only [decodeFirstFailure]
  split
  · rename_i hi
    have hnot : (e q).val ∉ c.1.1 := by
      simpa only [Finset.mem_compl] using (e q).property
    exact False.elim (hnot hi)
  · rename_i hi
    have hidx : e.symm ⟨(e q).val, by simpa using (e q).property⟩ = q := by
      apply e.injective
      rw [e.apply_symm_apply]
    change W + j + (c.2.2
      (e.symm ⟨(e q).val, by simpa using (e q).property⟩)).val =
        W + j + (c.2.2 q).val
    rw [hidx]

private theorem filter_decodeFirstFailure_lt_failure
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) :
    (Finset.univ.filter fun i ↦
      (decodeFirstFailure hUk hj c i).val < W + j) = c.1.1 := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hin
    have hr := decodeFirstFailure_mem_right hUk hj c i hin
    omega
  · intro hi
    have hl := decodeFirstFailure_mem_left hUk hj c i hi
    omega

private theorem filter_decodeFirstFailure_lt_before
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) {s : ℕ} (hs : s < j) :
    (Finset.univ.filter fun i ↦
      (decodeFirstFailure hUk hj c i).val < W + s).card =
    (Finset.univ.filter fun q ↦ (c.2.1.1 q).val < W + s).card := by
  classical
  have hrestrict :
      (Finset.univ.filter fun i ↦
          (decodeFirstFailure hUk hj c i).val < W + s) =
        c.1.1.filter fun i ↦
          (decodeFirstFailure hUk hj c i).val < W + s := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      refine ⟨?_, hi⟩
      by_contra hin
      have hr := decodeFirstFailure_mem_right hUk hj c i hin
      omega
    · exact fun hi ↦ hi.2
  rw [hrestrict]
  rw [← card_filter_orderIsoOfFin c.1.1 c.1.2
    (fun i ↦ (decodeFirstFailure hUk hj c i).val < W + s)]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have happly :
      (decodeFirstFailure hUk hj c
          (Finset.orderIsoOfFin c.1.1 c.1.2 q).val).val =
        (c.2.1.1 q).val := by
    let e := Finset.orderIsoOfFin c.1.1 c.1.2
    simp only [decodeFirstFailure, e]
    split
    · rename_i hi
      have hsub : (⟨(e q).val, hi⟩ : {i // i ∈ c.1.1}) = e q :=
        Subtype.ext (by rfl)
      change (c.2.1.1 (e.symm ⟨(e q).val, hi⟩)).val =
        (c.2.1.1 q).val
      simp [hsub]
    · rename_i hi
      exact False.elim (hi (e q).property)
  rw [happly]

private theorem decodeFirstFailure_firstFailure
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (c : firstFailureCode k U W j) :
    confinedParkingFirstFailure (decodeFirstFailure hUk hj c) j := by
  constructor
  · intro s hs
    rw [filter_decodeFirstFailure_lt_before hUk hj c hs]
    exact c.2.1.2 s hs
  · rw [filter_decodeFirstFailure_lt_failure hUk hj c, c.1.2]
    omega

private theorem decodeFirstFailure_injective
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1) :
    Function.Injective (@decodeFirstFailure k U W j hUk hj) := by
  classical
  intro c d hcd
  have hsets : c.1 = d.1 := by
    apply Subtype.ext
    have hfilter := congrArg
      (fun f : Fin k → Fin (k - U + W) ↦
        Finset.univ.filter fun i ↦ (f i).val < W + j) hcd
    rw [filter_decodeFirstFailure_lt_failure hUk hj c,
      filter_decodeFirstFailure_lt_failure hUk hj d] at hfilter
    exact hfilter
  rcases c with ⟨S, a, b⟩
  rcases d with ⟨T, a', b'⟩
  dsimp only at hsets
  cases hsets
  have ha : a = a' := by
    apply Subtype.ext
    funext q
    apply Fin.ext
    have hq := congrArg Fin.val
      (congrFun hcd (Finset.orderIsoOfFin S.1 S.2 q).val)
    have hc := decodeFirstFailure_left_apply hUk hj (⟨S, a, b⟩) q
    have hd := decodeFirstFailure_left_apply hUk hj (⟨S, a', b'⟩) q
    exact hc.symm.trans (hq.trans hd)
  cases ha
  have hb : b = b' := by
    funext q
    apply Fin.ext
    have hcard : S.1ᶜ.card = k - j := by
      rw [Finset.card_compl, S.2]
      simp
    have hq := congrArg Fin.val
      (congrFun hcd (Finset.orderIsoOfFin S.1ᶜ hcard q).val)
    have hc := decodeFirstFailure_right_apply hUk hj (⟨S, a, b⟩) q
    have hd := decodeFirstFailure_right_apply hUk hj (⟨S, a, b'⟩) q
    have hsums : W + j + (b q).val = W + j + (b' q).val :=
      hc.symm.trans (hq.trans hd)
    omega
  cases hb
  rfl

private def encodeFirstFailure
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (f : Fin k → Fin (k - U + W))
    (hf : confinedParkingFirstFailure f j) : firstFailureCode k U W j := by
  let S := Finset.univ.filter fun i ↦ (f i).val < W + j
  have hS : S.card = j := card_filter_eq_of_firstFailure hf
  have hSc : Sᶜ.card = k - j := by
    rw [Finset.card_compl, hS]
    simp
  let eL := (Finset.orderIsoOfFin S hS).toEquiv
  let eR := (Finset.orderIsoOfFin Sᶜ hSc).toEquiv
  have hleft (q : Fin j) : (f (eL q)).val < j - 1 + W := by
    by_cases hj0 : j = 0
    · exact Fin.elim0 (Fin.cast hj0 q)
    · let L := Finset.univ.filter fun i ↦ (f i).val < W + (j - 1)
      have hLS : L ⊆ S := by
        intro i hi
        simp only [L, S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        omega
      have hLcard : j ≤ L.card := by
        convert hf.1 (j - 1) (by omega) using 1 <;> omega
      have hSL : S ⊆ L := by
        exact (Finset.eq_of_subset_of_card_le hLS (by omega)).symm.subset
      have hi : (eL q).val ∈ L := hSL (eL q).property
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
  let a : Fin j → Fin (j - 1 + W) := fun q ↦ ⟨(f (eL q)).val, hleft q⟩
  have ha : ordinaryParkingGood j W a := by
    intro s hs
    have hrestrict :
        (Finset.univ.filter fun i ↦ (f i).val < W + s) =
          S.filter fun i ↦ (f i).val < W + s := by
      ext i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi
        exact ⟨by omega, hi⟩
      · exact fun hi ↦ hi.2
    have hcard := card_filter_orderIsoOfFin S hS
      (fun i ↦ (f i).val < W + s)
    have heq :
        (Finset.univ.filter fun q ↦ (a q).val < W + s).card =
          (Finset.univ.filter fun i ↦ (f i).val < W + s).card := by
      rw [hrestrict, ← hcard]
      congr 1
    rw [heq]
    exact hf.1 s hs
  have hright (q : Fin (k - j)) :
      (f (eR q)).val - (W + j) < k - U - j := by
    have hnot : (eR q).val ∉ S := by
      simpa only [Finset.mem_compl] using (eR q).property
    have hlo : W + j ≤ (f (eR q)).val := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] using hnot
    have hv := (f (eR q)).isLt
    omega
  let b : Fin (k - j) → Fin (k - U - j) := fun q ↦
    ⟨(f (eR q)).val - (W + j), hright q⟩
  exact ⟨⟨S, hS⟩, ⟨a, ha⟩, b⟩

private theorem encodeFirstFailure_set
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (f : Fin k → Fin (k - U + W))
    (hf : confinedParkingFirstFailure f j) :
    (encodeFirstFailure hUk hj f hf).1.1 =
      Finset.univ.filter fun i ↦ (f i).val < W + j := by
  rfl

private theorem encodeFirstFailure_left_apply
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (f : Fin k → Fin (k - U + W))
    (hf : confinedParkingFirstFailure f j) (q : Fin j) :
    ((encodeFirstFailure hUk hj f hf).2.1.1 q).val =
      (f (Finset.orderIsoOfFin
        (Finset.univ.filter fun i ↦ (f i).val < W + j)
        (card_filter_eq_of_firstFailure hf) q).val).val := by
  rfl

private theorem encodeFirstFailure_right_apply
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (f : Fin k → Fin (k - U + W))
    (hf : confinedParkingFirstFailure f j) (q : Fin (k - j)) :
    ((encodeFirstFailure hUk hj f hf).2.2 q).val =
      (f (Finset.orderIsoOfFin
        (Finset.univ.filter fun i ↦ (f i).val < W + j)ᶜ
        (by
          rw [Finset.card_compl, card_filter_eq_of_firstFailure hf]
          simp) q).val).val - (W + j) := by
  rfl

private theorem decode_encodeFirstFailure
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1)
    (f : Fin k → Fin (k - U + W))
    (hf : confinedParkingFirstFailure f j) :
    decodeFirstFailure hUk hj (encodeFirstFailure hUk hj f hf) = f := by
  classical
  funext i
  apply Fin.ext
  let S := Finset.univ.filter fun i ↦ (f i).val < W + j
  have hS : S.card = j := card_filter_eq_of_firstFailure hf
  have hSc : Sᶜ.card = k - j := by
    rw [Finset.card_compl, hS]
    simp
  by_cases hi : i ∈ S
  · let e := Finset.orderIsoOfFin S hS
    let q : Fin j := e.symm ⟨i, hi⟩
    have heq : (e q).val = i := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
    calc
      (decodeFirstFailure hUk hj (encodeFirstFailure hUk hj f hf) i).val =
          (decodeFirstFailure hUk hj (encodeFirstFailure hUk hj f hf)
            (e q).val).val := by rw [heq]
      _ = ((encodeFirstFailure hUk hj f hf).2.1.1 q).val := by
        exact decodeFirstFailure_left_apply hUk hj
          (encodeFirstFailure hUk hj f hf) q
      _ = (f (e q).val).val := by
        exact encodeFirstFailure_left_apply hUk hj f hf q
      _ = (f i).val := by rw [heq]
  · have hic : i ∈ Sᶜ := by simpa using hi
    let e := Finset.orderIsoOfFin Sᶜ hSc
    let q : Fin (k - j) := e.symm ⟨i, hic⟩
    have heq : (e q).val = i := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hic⟩)
    have hlo : W + j ≤ (f i).val := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] using hi
    calc
      (decodeFirstFailure hUk hj (encodeFirstFailure hUk hj f hf) i).val =
          (decodeFirstFailure hUk hj (encodeFirstFailure hUk hj f hf)
            (e q).val).val := by rw [heq]
      _ = W + j + ((encodeFirstFailure hUk hj f hf).2.2 q).val := by
        exact decodeFirstFailure_right_apply hUk hj
          (encodeFirstFailure hUk hj f hf) q
      _ = W + j + ((f (e q).val).val - (W + j)) := by
        rw [encodeFirstFailure_right_apply hUk hj f hf q]
      _ = (f i).val := by rw [heq]; omega

private abbrev firstFailureWord (k U W j : ℕ) :=
  {f : Fin k → Fin (k - U + W) // confinedParkingFirstFailure f j}

private noncomputable def firstFailureCodeEquiv
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1) :
    firstFailureCode k U W j ≃ firstFailureWord k U W j where
  toFun c := ⟨decodeFirstFailure hUk hj c,
    decodeFirstFailure_firstFailure hUk hj c⟩
  invFun f := encodeFirstFailure hUk hj f.1 f.2
  left_inv c := by
    apply decodeFirstFailure_injective hUk hj
    exact decode_encodeFirstFailure hUk hj
      (decodeFirstFailure hUk hj c)
      (decodeFirstFailure_firstFailure hUk hj c)
  right_inv f := by
    apply Subtype.ext
    exact decode_encodeFirstFailure hUk hj f.1 f.2

private theorem card_firstFailureWord
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1) :
    Fintype.card (firstFailureWord k U W j) =
      k.choose j *
        (Finset.univ.filter (@ordinaryParkingGood j W)).card *
          (k - U - j) ^ (k - j) := by
  rw [Fintype.card_congr (firstFailureCodeEquiv hUk hj).symm]
  exact card_firstFailureCode k U W j

theorem card_confinedParkingFirstFailure
    {k U W j : ℕ} (hUk : U ≤ k) (hj : j < k - U + 1) :
    (Finset.univ.filter (fun f : Fin k → Fin (k - U + W) ↦
      confinedParkingFirstFailure f j)).card =
      k.choose j *
        (Finset.univ.filter (@ordinaryParkingGood j W)).card *
          (k - U - j) ^ (k - j) := by
  rw [← card_firstFailureWord hUk hj]
  unfold firstFailureWord
  rw [Fintype.card_subtype]

private theorem not_confinedParkingGood_iff_exists_firstFailure
    {k U W : ℕ} (f : Fin k → Fin (k - U + W)) :
    ¬ confinedParkingGood k U W f ↔
      ∃ j < k - U + 1, confinedParkingFirstFailure f j := by
  classical
  constructor
  · intro hf
    unfold confinedParkingGood at hf
    push_neg at hf
    let j := Nat.find hf
    have hj := Nat.find_spec hf
    refine ⟨j, hj.1, ?_, hj.2⟩
    intro s hs
    by_contra hbad
    have hbad' :
        (Finset.univ.filter fun i ↦ (f i).val < W + s).card < s + 1 :=
      Nat.lt_of_not_ge hbad
    have hminimal := Nat.find_min' hf ⟨hs.trans hj.1, hbad'⟩
    exact (Nat.not_lt_of_ge hminimal) hs
  · rintro ⟨j, hj, hfirst⟩ hgood
    exact (Nat.not_lt_of_ge (hgood j hj)) hfirst.2

private abbrev badConfinedParkingWord (k U W : ℕ) :=
  {f : Fin k → Fin (k - U + W) // ¬ confinedParkingGood k U W f}

private abbrev indexedFirstFailureWord (k U W : ℕ) :=
  (j : Fin (k - U + 1)) × firstFailureWord k U W j.val

private theorem sigmaSubtype_ext
    {ι α : Type*} {p : ι → α → Prop}
    {x y : (i : ι) × {a : α // p i a}}
    (hidx : x.1 = y.1) (hval : x.2.1 = y.2.1) : x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  dsimp only at hidx hval
  subst j
  congr 1
  exact Subtype.ext hval

private noncomputable def badConfinedParkingWordEquiv
    {k U W : ℕ} (hUk : U ≤ k) :
    badConfinedParkingWord k U W ≃ indexedFirstFailureWord k U W where
  toFun f := by
    let hex :=
      (not_confinedParkingGood_iff_exists_firstFailure f.1).mp f.2
    let j := Nat.find hex
    have hj := Nat.find_spec hex
    exact ⟨⟨j, hj.1⟩, ⟨f.1, hj.2⟩⟩
  invFun p := ⟨p.2.1, by
    apply (not_confinedParkingGood_iff_exists_firstFailure p.2.1).mpr
    exact ⟨p.1.val, p.1.isLt, p.2.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv p := by
    let hex :=
      (not_confinedParkingGood_iff_exists_firstFailure p.2.1).mp (by
        apply (not_confinedParkingGood_iff_exists_firstFailure p.2.1).mpr
        exact ⟨p.1.val, p.1.isLt, p.2.2⟩)
    have hj := Nat.find_spec hex
    have heq : Nat.find hex = p.1.val :=
      confinedParkingFirstFailure_unique hj.2 p.2.2
    have hidx :
        (⟨Nat.find hex, hj.1⟩ : Fin (k - U + 1)) = p.1 :=
      Fin.ext heq
    exact sigmaSubtype_ext hidx rfl

private theorem card_badConfinedParkingWord
    {k U W : ℕ} (hUk : U ≤ k) :
    Fintype.card (badConfinedParkingWord k U W) =
      ∑ j ∈ Finset.range (k - U + 1),
        k.choose j *
          (Finset.univ.filter (@ordinaryParkingGood j W)).card *
            (k - U - j) ^ (k - j) := by
  rw [Fintype.card_congr (badConfinedParkingWordEquiv hUk)]
  rw [Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ Fintype.card (firstFailureWord k U W j))
    (k - U + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [card_firstFailureWord hUk (Finset.mem_range.mp hj)]

theorem card_not_confinedParkingGood
    {k U W : ℕ} (hUk : U ≤ k) :
    (Finset.univ.filter (fun f : Fin k → Fin (k - U + W) ↦
      ¬ confinedParkingGood k U W f)).card =
      ∑ j ∈ Finset.range (k - U + 1),
        k.choose j *
          (Finset.univ.filter (@ordinaryParkingGood j W)).card *
            (k - U - j) ^ (k - j) := by
  rw [← card_badConfinedParkingWord hUk]
  unfold badConfinedParkingWord
  rw [Fintype.card_subtype]

theorem card_confinedParkingGood_add_firstFailureSum
    {k U W : ℕ} (hUk : U ≤ k) :
    (Finset.univ.filter (@confinedParkingGood k U W)).card +
        ∑ j ∈ Finset.range (k - U + 1),
          k.choose j *
            (Finset.univ.filter (@ordinaryParkingGood j W)).card *
              (k - U - j) ^ (k - j) =
      (k - U + W) ^ k := by
  rw [← card_not_confinedParkingGood hUk]
  rw [Finset.card_filter_add_card_filter_not]
  simp

theorem card_confinedParkingGood_eq_remainder
    {k U W : ℕ} (hUk : U ≤ k) :
    (Finset.univ.filter (@confinedParkingGood k U W)).card =
      (k - U + W) ^ k -
        ∑ j ∈ Finset.range (k - U + 1),
          k.choose j *
            (Finset.univ.filter (@ordinaryParkingGood j W)).card *
              (k - U - j) ^ (k - j) := by
  exact Nat.eq_sub_of_add_eq (card_confinedParkingGood_add_firstFailureSum hUk)

/-- The ordinary `W`-parking words are counted by Abel's rooted-forest
factor. -/
theorem card_ordinaryParkingGood_eq_parkingAbelP (k W : ℕ) :
    (Finset.univ.filter (@ordinaryParkingGood k W)).card =
      parkingAbelP k W := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp only [parkingAbelP_zero]
        rw [Finset.filter_eq_self.mpr]
        · simp
        · intro f _hf
          intro s hs
          omega
      · have hk : 1 ≤ k := by omega
        have hrec := card_confinedParkingGood_eq_remainder
          (k := k) (U := 1) (W := W) hk
        have hpred :
            (Finset.univ.filter (@confinedParkingGood k 1 W)) =
              Finset.univ.filter (@ordinaryParkingGood k W) := by
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp only [confinedParkingGood, ordinaryParkingGood]
          have hindex : k - 1 + 1 = k := by omega
          rw [hindex]
        rw [hpred] at hrec
        have hsum :
            (∑ j ∈ Finset.range k,
              k.choose j *
                (Finset.univ.filter (@ordinaryParkingGood j W)).card *
                  (k - 1 - j) ^ (k - j)) =
              ∑ j ∈ Finset.range k,
                k.choose j * parkingAbelP j W *
                  (k - 1 - j) ^ (k - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih j (Finset.mem_range.mp hj)]
        rw [show k - 1 + 1 = k by omega, hsum] at hrec
        exact hrec.trans (parkingAbelP_recurrence k W hk).symm

/-- Exact first-violation enumeration of the confined parking words. -/
theorem card_confinedParkingGood_eq_abelRemainder
    {k U W : ℕ} (hUk : U ≤ k) :
    (Finset.univ.filter (@confinedParkingGood k U W)).card =
      (k - U + W) ^ k -
        ∑ j ∈ Finset.range (k - U + 1),
          k.choose j * parkingAbelP j W *
            (k - U - j) ^ (k - j) := by
  rw [card_confinedParkingGood_eq_remainder hUk]
  apply congrArg ((k - U + W) ^ k - ·)
  apply Finset.sum_congr rfl
  intro j _hj
  rw [card_ordinaryParkingGood_eq_parkingAbelP]

end Erdos896.Ford

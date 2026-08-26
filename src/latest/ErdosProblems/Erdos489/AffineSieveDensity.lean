import ErdosProblems.Erdos489.HeilbronnRohrbach

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos489

/-- Number of parameters `k<N` for which `Q*k+1` avoids every modulus in `l`. -/
def affineAvoidCount (l : List ℕ) (Q N : ℕ) : ℕ :=
  ((Finset.range N).filter fun k => ∀ a ∈ l, ¬a ∣ Q * k + 1).card

/-- Multiplication by a number coprime to `P`, followed by translation by one,
permutes the residue classes modulo `P`. -/
lemma affine_mod_permutes_range (Q P : ℕ) (hP : 0 < P)
    (hcop : Nat.Coprime Q P) :
    Finset.image (fun k => (Q * k + 1) % P) (Finset.range P) =
      Finset.range P := by
  let f : ℕ → ℕ := fun k => (Q * k + 1) % P
  have hinj : Set.InjOn f (Finset.range P : Set ℕ) := by
    intro x hx y hy hxyf
    have hxP : x < P := Finset.mem_range.mp hx
    have hyP : y < P := Finset.mem_range.mp hy
    change (Q * x + 1) % P = (Q * y + 1) % P at hxyf
    have hmod : Nat.ModEq P (Q * x + 1) (Q * y + 1) := hxyf
    have hmulmod : Nat.ModEq P (Q * x) (Q * y) :=
      Nat.ModEq.add_right_cancel' 1 hmod
    rcases le_total x y with hxy | hyx
    · have hQxy : Q * x ≤ Q * y := Nat.mul_le_mul_left Q hxy
      have hd : P ∣ Q * y - Q * x :=
        (Nat.modEq_iff_dvd' hQxy).mp hmulmod
      rw [← Nat.mul_sub_left_distrib] at hd
      have hPd : P ∣ y - x := hcop.symm.dvd_of_dvd_mul_left hd
      have hdlt : y - x < P := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hPd hdlt
      omega
    · have hQyx : Q * y ≤ Q * x := Nat.mul_le_mul_left Q hyx
      have hd : P ∣ Q * x - Q * y :=
        (Nat.modEq_iff_dvd' hQyx).mp hmulmod.symm
      rw [← Nat.mul_sub_left_distrib] at hd
      have hPd : P ∣ x - y := hcop.symm.dvd_of_dvd_mul_left hd
      have hdlt : x - y < P := by omega
      have hz := Nat.eq_zero_of_dvd_of_lt hPd hdlt
      omega
  have hsubset : Finset.image f (Finset.range P) ⊆ Finset.range P := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hP)
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [Finset.card_range, Finset.card_image_iff.mpr hinj, Finset.card_range]

/-- Divisibility by a modulus `a|P` is unchanged on replacing a number by its
remainder modulo `P`. -/
lemma dvd_affine_mod_iff (a Q k P : ℕ) (haP : a ∣ P) :
    a ∣ (Q * k + 1) % P ↔ a ∣ Q * k + 1 := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.mod_mod_of_dvd _ haP]

/-- The affine map identifies the finite affine sieve with the ordinary sieve
on a full product period. -/
lemma affineAvoidCount_eq_avoidCount (l : List ℕ) (Q : ℕ)
    (hl : ∀ a ∈ l, 0 < a) (hcop : Nat.Coprime Q l.prod) :
    affineAvoidCount l Q l.prod = avoidCount l l.prod := by
  let P := l.prod
  let f : ℕ → ℕ := fun k => (Q * k + 1) % P
  let A : Finset ℕ :=
    (Finset.range P).filter fun k => ∀ a ∈ l, ¬a ∣ Q * k + 1
  let O : Finset ℕ :=
    (Finset.range P).filter fun n => ∀ a ∈ l, ¬a ∣ n
  have hP : 0 < P := List.prod_pos hl
  have hperm : Finset.image f (Finset.range P) = Finset.range P := by
    exact affine_mod_permutes_range Q P hP hcop
  have hpred : ∀ k, (∀ a ∈ l, ¬a ∣ Q * k + 1) ↔
      (∀ a ∈ l, ¬a ∣ f k) := by
    intro k
    constructor
    · intro hk a ha haf
      apply hk a ha
      exact (dvd_affine_mod_iff a Q k P (List.dvd_prod ha)).mp haf
    · intro hk a ha haf
      apply hk a ha
      exact (dvd_affine_mod_iff a Q k P (List.dvd_prod ha)).mpr haf
  have hinj : Set.InjOn f (Finset.range P : Set ℕ) := by
    have hcard := congrArg Finset.card hperm
    exact Finset.card_image_iff.mp (by simpa using hcard)
  have hAO : Finset.image f A = O := by
    apply Finset.Subset.antisymm
    · intro n hn
      rcases Finset.mem_image.mp hn with ⟨k, hkA, rfl⟩
      have hk := Finset.mem_filter.mp hkA
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hP), (hpred k).mp hk.2⟩
    · intro n hnO
      have hnrange : n ∈ Finset.range P := (Finset.mem_filter.mp hnO).1
      rw [← hperm] at hnrange
      rcases Finset.mem_image.mp hnrange with ⟨k, hk, hkf⟩
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, hkf⟩
      exact (hpred k).mpr (hkf ▸ (Finset.mem_filter.mp hnO).2)
  have hcardA : A.card = O.card := by
    rw [← hAO, Finset.card_image_iff.mpr (hinj.mono (Finset.filter_subset _ _))]
  exact hcardA

/-- Affine finite Heilbronn--Rohrbach density.  If `Q` is coprime to every
modulus (equivalently here to their product), then over the product period at
least `∏(a-1)` parameters `k` have `Qk+1` avoiding every modulus. -/
theorem affine_heilbronn_rohrbach_count (l : List ℕ) (Q : ℕ)
    (hl : ∀ a ∈ l, 1 < a) (hcop : Nat.Coprime Q l.prod) :
    (l.map fun a => a - 1).prod ≤ affineAvoidCount l Q l.prod := by
  rw [affineAvoidCount_eq_avoidCount l Q (fun a ha => (hl a ha).trans' Nat.zero_lt_one) hcop]
  exact heilbronn_rohrbach_count l hl

end Erdos489

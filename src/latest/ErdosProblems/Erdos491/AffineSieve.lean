import ErdosProblems.Erdos491.ResidueSieve

/-! # Residues excluded by small affine cofactors -/

open scoped BigOperators

namespace Erdos491

noncomputable def inverseResidues (q H : ℕ) : Finset (ZMod q) :=
  (Finset.Icc 1 H).image (fun u : ℕ ↦ -(u : ZMod q)⁻¹)

lemma inverseResidues_card {q H : ℕ} (hq : q.Prime) (hH : H < q) :
    (inverseResidues q H).card = H := by
  classical
  let _ : Fact q.Prime := ⟨hq⟩
  rw [inverseResidues, Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb heq
    have hab : (a : ZMod q) = b := inv_injective (neg_injective heq)
    have hv := congrArg ZMod.val hab
    have ha' : a < q := (Finset.mem_Icc.mp ha).2.trans_lt hH
    have hb' : b < q := (Finset.mem_Icc.mp hb).2.trans_lt hH
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using hv

lemma mem_inverseResidues_iff {q H n : ℕ} (hq : q.Prime) (hH : H < q) :
    (n : ZMod q) ∈ inverseResidues q H ↔
      ∃ u : ℕ, 1 ≤ u ∧ u ≤ H ∧ q ∣ n * u + 1 := by
  classical
  let _ : Fact q.Prime := ⟨hq⟩
  have hiff (u : ℕ) (hu1 : 1 ≤ u) (huH : u ≤ H) :
      -(u : ZMod q)⁻¹ = (n : ZMod q) ↔ q ∣ n * u + 1 := by
    have huq : u < q := huH.trans_lt hH
    have hu0 : (u : ZMod q) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt huq, ZMod.val_zero] at hv
      omega
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro hn
      rw [← hn]
      field_simp
      ring
    · intro hn
      apply (mul_right_cancel₀ hu0)
      field_simp
      linear_combination -hn
  simp only [inverseResidues, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨u, ⟨hu1, huH⟩, heq⟩
    exact ⟨u, hu1, huH, (hiff u hu1 huH).mp heq⟩
  · rintro ⟨u, hu1, huH, hdvd⟩
    exact ⟨u, ⟨hu1, huH⟩, (hiff u hu1 huH).mpr hdvd⟩

theorem affine_avoidance_second_moment (Q P : Finset ℕ) (H T : ℕ)
    (hprime : ∀ q ∈ Q, q.Prime) (hH : ∀ q ∈ Q, H < q)
    (hP : P ⊆ Finset.range T)
    (havoid : ∀ n ∈ P, ∀ q ∈ Q, ∀ u : ℕ, 1 ≤ u → u ≤ H → ¬ q ∣ n * u + 1) :
    (P.card : ℝ) * (∑ q ∈ Q, (H : ℝ) / q) ^ 2 ≤
      (T : ℝ) * (∑ q ∈ Q, (H : ℝ) / q) +
        (∑ q ∈ Q, (q : ℝ)) + (∑ q ∈ Q, (q : ℝ)) ^ 2 := by
  classical
  let q : {q // q ∈ Q} → ℕ := Subtype.val
  let _ : ∀ i : {q // q ∈ Q}, NeZero (q i) :=
    fun i ↦ ⟨(hprime i i.property).ne_zero⟩
  let A (i : {q // q ∈ Q}) := inverseResidues (q i) H
  have hcard (i : {q // q ∈ Q}) : (A i).card = H :=
    inverseResidues_card (hprime i i.property) (hH i i.property)
  have hcop : ∀ i ∈ Q.attach, ∀ j ∈ Q.attach, i ≠ j → (q i).Coprime (q j) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hprime i i.property) (hprime j j.property)).mpr
      (fun heq ↦ hij (Subtype.ext heq))
  have ha : ∀ n ∈ P, ∀ i ∈ Q.attach, (n : ZMod (q i)) ∉ A i := by
    intro n hn i _ hi
    obtain ⟨u, hu1, huH, hdvd⟩ :=
      (mem_inverseResidues_iff (hprime i i.property) (hH i i.property)).mp hi
    exact havoid n hn i i.property u hu1 huH hdvd
  have h := residue_avoidance_bound Q.attach q A T P hP hcop ha
  have hsum : (∑ i ∈ Q.attach, (H : ℝ) / (i.val : ℝ)) =
      ∑ q ∈ Q, (H : ℝ) / q := Finset.sum_attach Q (fun q : ℕ ↦ (H : ℝ) / q)
  simpa only [hcard, q, hsum, Finset.sum_attach] using h

end Erdos491

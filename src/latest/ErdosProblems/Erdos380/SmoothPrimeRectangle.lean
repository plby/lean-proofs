import ErdosProblems.Erdos380.SingletonCount
import ErdosProblems.Erdos380.TupleResidues

/-!
# An injective rectangular construction of smooth integers

Choose one prime from each of disjoint pools, and a positive cofactor
smaller than every chosen prime.  Unique factorization recovers every
coordinate, so no factorial multiplicity loss is incurred.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def smoothRectangleValue (s : I → Finset ℕ) (M : ℕ)
    (v : (Finset.Icc 1 M) × (∀ i, s i)) : ℕ := v.1.1 * tupleNaturalProduct s v.2

lemma smoothRectangleValue_injective (s : I → Finset ℕ) (M : ℕ)
    (hs : ∀ i p, p ∈ s i → p.Prime)
    (hlarge : ∀ i p, p ∈ s i → M < p)
    (hdisjoint : Pairwise fun i j => Disjoint (s i) (s j)) :
    Function.Injective (smoothRectangleValue s M) := by
  classical
  rintro ⟨a, f⟩ ⟨b, g⟩ hfg
  have heq : a.1 * (∏ i, (f i).1) = b.1 * (∏ i, (g i).1) := hfg
  have htuple : f = g := by
    funext i
    have hp := hs i (f i).1 (f i).2
    have hpf : (f i).1 ∣ ∏ j, (f j).1 := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hpbg : (f i).1 ∣ b.1 * ∏ j, (g j).1 := by
      rw [← heq]
      exact hpf.trans (dvd_mul_left _ _)
    have hpnb : ¬ (f i).1 ∣ b.1 := Nat.not_dvd_of_pos_of_lt
      (by have := (Finset.mem_Icc.mp b.2).1; omega)
      ((Finset.mem_Icc.mp b.2).2.trans_lt (hlarge i (f i).1 (f i).2))
    have hpg : (f i).1 ∣ ∏ j, (g j).1 := (hp.dvd_mul.mp hpbg).resolve_left hpnb
    obtain ⟨j, _, hpj⟩ := hp.prime.exists_mem_finset_dvd hpg
    have hpq : (f i).1 = (g j).1 :=
      (Nat.prime_dvd_prime_iff_eq hp (hs j (g j).1 (g j).2)).mp hpj
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hdisjoint hij) (f i).2 (by rw [hpq]; exact (g j).2)
    subst j
    exact Subtype.ext hpq
  have hprod : 0 < ∏ i, (g i).1 := Finset.prod_pos fun i _ => (hs i (g i).1 (g i).2).pos
  have hab : a.1 = b.1 := Nat.eq_of_mul_eq_mul_right hprod (by simpa only [htuple] using heq)
  exact Prod.ext (Subtype.ext hab) htuple

lemma smoothRectangleValue_mem (s : I → Finset ℕ) (P : I → ℕ) {M x y : ℕ}
    (hs : ∀ i p, p ∈ s i → p.Prime) (hP : ∀ i p, p ∈ s i → p ≤ P i)
    (hy : 1 ≤ y) (hMy : M ≤ y) (hsy : ∀ i p, p ∈ s i → p ≤ y)
    (hsize : M * (∏ i, P i) ≤ x) (v : (Finset.Icc 1 M) × (∀ i, s i)) :
    smoothRectangleValue s M v ∈ Nat.smoothNumbersUpTo x (y + 1) := by
  have ha := Finset.mem_Icc.mp v.1.2
  have hprodpos : 0 < tupleNaturalProduct s v.2 := Finset.prod_pos fun i _ =>
    (hs i (v.2 i).1 (v.2 i).2).pos
  have hnpos : 0 < smoothRectangleValue s M v := Nat.mul_pos (by omega) hprodpos
  apply Nat.mem_smoothNumbersUpTo.mpr
  constructor
  · exact (Nat.mul_le_mul ha.2 (Finset.prod_le_prod' fun i _ => hP i (v.2 i).1 (v.2 i).2)).trans hsize
  · apply (mem_smoothNumbers_iff_largestPrimeFactor hy).mpr
    refine ⟨hnpos.ne', largestPrimeFactor_le hy ?_⟩
    intro p hp hpn
    rcases hp.dvd_mul.mp hpn with hpa | hpprod
    · exact ((Nat.le_of_dvd (by omega : 0 < v.1.1) hpa).trans ha.2).trans hMy
    · obtain ⟨i, _, hpi⟩ := hp.prime.exists_mem_finset_dvd hpprod
      have hpeq := (Nat.prime_dvd_prime_iff_eq hp (hs i (v.2 i).1 (v.2 i).2)).mp hpi
      rw [hpeq]
      exact hsy i (v.2 i).1 (v.2 i).2

/-- A smooth-number lower bound with no multiplicity loss. -/
theorem smoothCount_ge_prime_rectangle
    (s : I → Finset ℕ) (P : I → ℕ) {M x y : ℕ}
    (hs : ∀ i p, p ∈ s i → p.Prime) (hP : ∀ i p, p ∈ s i → p ≤ P i)
    (hlarge : ∀ i p, p ∈ s i → M < p)
    (hdisjoint : Pairwise fun i j => Disjoint (s i) (s j))
    (hy : 1 ≤ y) (hMy : M ≤ y) (hsy : ∀ i p, p ∈ s i → p ≤ y)
    (hsize : M * (∏ i, P i) ≤ x) :
    M * (∏ i, (s i).card) ≤ smoothCount x y := by
  classical
  let S := (Finset.univ : Finset ((Finset.Icc 1 M) × (∀ i, s i))).image (smoothRectangleValue s M)
  have hsub : S ⊆ Nat.smoothNumbersUpTo x (y + 1) := by
    intro n hn
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hn
    exact smoothRectangleValue_mem s P hs hP hy hMy hsy hsize v
  have hcard : S.card = M * (∏ i, (s i).card) := by
    rw [Finset.card_image_of_injective _ (smoothRectangleValue_injective s M hs hlarge hdisjoint)]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Nat.card_Icc,
      Nat.add_sub_cancel, Fintype.card_pi]
  rw [← hcard]
  exact Finset.card_le_card hsub

end

end Erdos380

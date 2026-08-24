import ErdosProblems.Erdos587.CoordinateResidueCorrection

/-!
Homogenize a standardized GAP using a disjoint reserve of original elements.
The translation preserves properness and actual subset-sum containment.
-/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

def translateBy (P : GeneralizedAP) (t : ℤ) : GeneralizedAP := { P with base := P.base + t }

theorem eval_translateBy (P : GeneralizedAP) (t : ℤ) (x : P.Param) :
    (P.translateBy t).eval x = P.eval x + t := by
  simp only [translateBy, eval]
  abel

theorem carrier_translateBy (P : GeneralizedAP) (t : ℤ) :
    (P.translateBy t).carrier = P.carrier.image (fun x => x + t) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (P.translateBy t).mem_carrier_iff.mp hz
    refine Finset.mem_image.mpr ⟨P.eval x, P.mem_carrier_iff.mpr ⟨x, rfl⟩, ?_⟩
    exact (P.eval_translateBy t x).symm.trans hx
  · intro hz
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx⟩ := P.mem_carrier_iff.mp hy
    apply (P.translateBy t).mem_carrier_iff.mpr
    refine ⟨x, ?_⟩
    rw [P.eval_translateBy, hx]
    exact heq

theorem proper_translateBy (P : GeneralizedAP) (hP : P.Proper) (t : ℤ) :
    (P.translateBy t).Proper := by
  intro x y hxy
  have heq : P.eval x + t = P.eval y + t :=
    (P.eval_translateBy t x).symm.trans (hxy.trans (P.eval_translateBy t y))
  exact hP (add_right_cancel heq)

/-- Every common divisor of the steps divides the base. -/
def HasHomogeneousBase (P : GeneralizedAP) : Prop :=
  ∀ d : ℤ, (∀ i, d ∣ P.step i) → d ∣ P.base

theorem translate_subsetSum_of_disjoint_reserve (P : GeneralizedAP)
    (U S : Finset ℤ) (hP : P.carrier ⊆ U.subsetSum) (hdisjoint : Disjoint U S) :
    (P.translateBy (∑ x ∈ S, x)).carrier ⊆ (U ∪ S).subsetSum := by
  rw [P.carrier_translateBy]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨W, hWU, hsum⟩ := Finset.mem_subsetSum_iff.mp (hP hy)
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨W ∪ S, Finset.union_subset_union hWU (Finset.Subset.refl S), ?_⟩
  rw [Finset.sum_union (hdisjoint.mono_left hWU), hsum]

end Erdos587.GeneralizedAP

namespace Erdos587.CFP

variable {α G : Type*} [DecidableEq α] [AddCommGroup G]

/-- Reserving a used set subtracts its cardinality from the available
deletion-stability radius, without changing the generated subgroup. -/
theorem stable_generators_after_reserving (φ : α → G) (A U : Finset α)
    (hUA : U ⊆ A) (r q : ℕ) (hbudget : U.card + q ≤ r)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup φ D = generatedSubgroup φ A) :
    generatedSubgroup φ (A \ U) = generatedSubgroup φ A ∧
      ∀ D ⊆ A \ U, (A \ U).card ≤ D.card + q →
        generatedSubgroup φ D = generatedSubgroup φ (A \ U) := by
  have hcard : A.card = (A \ U).card + U.card := by
    rw [Finset.card_sdiff_of_subset hUA, Nat.sub_add_cancel (Finset.card_le_card hUA)]
  have hgen := hstable (A \ U) Finset.sdiff_subset (by omega)
  refine ⟨hgen, ?_⟩
  intro D hD hcost
  rw [hstable D (hD.trans Finset.sdiff_subset) (by omega), hgen]

/-- Once a full-rank standardized GAP is present in the used subset sums,
a stable disjoint reserve makes its base homogeneous at bounded extra cost.
This theorem retains, rather than assumes away, subset-sum provenance. -/
theorem exists_homogeneous_translate_from_reserve
    (P Q : GeneralizedAP) (A U : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (hUA : U ⊆ A) (hQ : Q.Proper)
    (hQsum : Q.carrier ⊆ U.subsetSum) (hrank : Q.rank = P.rank)
    (a : Fin P.rank → ℤ) (ha : ∀ i, a i ≠ 0) (B r : ℕ)
    (hbound : ∀ i, |a i| ≤ (B : ℤ))
    (hsteps : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val → Q.step i = a j * P.step j)
    (hbudget : U.card + B ^ P.rank ≤ r)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A) :
    ∃ S ⊆ A \ U, S.card + 1 ≤ B ^ P.rank ∧
      (Q.translateBy (∑ x ∈ S, x)).Proper ∧
      (Q.translateBy (∑ x ∈ S, x)).HasHomogeneousBase ∧
      (Q.translateBy (∑ x ∈ S, x)).carrier ⊆ (U ∪ S).subsetSum := by
  have hbase : Q.base ∈ Q.carrier := Q.mem_carrier_iff.mpr
    ⟨fun _ => 0, by simp [GeneralizedAP.eval]⟩
  obtain ⟨W, hWU, hWsum⟩ := Finset.mem_subsetSum_iff.mp (hQsum hbase)
  let v := ∑ x ∈ W, P.centeredCoordinates x
  have hv : v ∈ generatedSubgroup P.centeredCoordinates A := by
    apply (generatedSubgroup P.centeredCoordinates A).sum_mem
    intro x hx
    exact AddSubgroup.subset_closure ⟨x, hUA (hWU hx), rfl⟩
  have hlin : P.linearEval v = Q.base := by
    change P.nvLinearEvalHom (∑ x ∈ W, P.centeredCoordinates x) = Q.base
    rw [map_sum]
    calc
      (∑ x ∈ W, P.nvLinearEvalHom (P.centeredCoordinates x)) = ∑ x ∈ W, x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact P.linearEval_centeredCoordinates hzero (hA (hUA (hWU hx)))
      _ = Q.base := hWsum
  obtain ⟨hreserve, hresstable⟩ := stable_generators_after_reserving
    P.centeredCoordinates A U hUA r (B ^ P.rank) hbudget hstable
  have hv' : v ∈ generatedSubgroup P.centeredCoordinates (A \ U) := hreserve.symm ▸ hv
  obtain ⟨S, hS, hScard, z, hcorrection⟩ := exists_homogeneous_coordinate_correction
    P (A \ U) hzero (Finset.sdiff_subset.trans hA) (B ^ P.rank) B hresstable
      a ha hbound (Nat.le_succ _) hv'
  have hdisjoint : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxS
    exact (Finset.mem_sdiff.mp (hS hxS)).2 hxU
  refine ⟨S, hS, hScard, Q.proper_translateBy hQ _, ?_,
    Q.translate_subsetSum_of_disjoint_reserve U S hQsum hdisjoint⟩
  intro d hd
  change d ∣ Q.base + ∑ x ∈ S, x
  rw [← hlin, hcorrection]
  apply Finset.dvd_sum
  intro j hj
  have hdiv : d ∣ a j * P.step j := by
    have hh := hd (Fin.cast hrank.symm j)
    change d ∣ Q.step (Fin.cast hrank.symm j) at hh
    rwa [hsteps (Fin.cast hrank.symm j) j (by simp)] at hh
  exact dvd_mul_of_dvd_right hdiv (z j)

end Erdos587.CFP

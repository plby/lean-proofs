import ErdosProblems.Erdos1148.InvariantVisitCount

/-! # Natural-number labels for sampled orbit visit patterns -/

namespace Erdos1148.DukeArithmetic

noncomputable def orbitBlockPattern {X : Type*} (f : X → X) (Q : Set X)
    (n k : ℕ) (x : X) : Finset ℕ :=
  (orbitVisitPattern (f^[n]) Q k x).image Fin.val

lemma mem_orbitBlockPattern {X : Type*} (f : X → X) (Q : Set X)
    (n k : ℕ) (x : X) (j : ℕ) :
    j ∈ orbitBlockPattern f Q n k x ↔ j < k ∧ f^[j * n] x ∈ Q := by
  classical
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hpred : (f^[n])^[i.val] x ∈ Q := (Finset.mem_filter.mp hi).2
    refine ⟨i.isLt, ?_⟩
    simpa only [← Function.iterate_mul, Nat.mul_comm n i.val] using hpred
  · rintro ⟨hj, hp⟩
    refine Finset.mem_image.mpr ⟨⟨j, hj⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [← Function.iterate_mul, Nat.mul_comm n j] using hp

lemma orbitBlockPattern_subset_range {X : Type*} (f : X → X) (Q : Set X)
    (n k : ℕ) (x : X) : orbitBlockPattern f Q n k x ⊆ Finset.range k := by
  intro j hj
  exact Finset.mem_range.mpr ((mem_orbitBlockPattern f Q n k x j).mp hj).1

lemma orbitBlockPattern_card {X : Type*} (f : X → X) (Q : Set X) (n k : ℕ) (x : X) :
    (orbitBlockPattern f Q n k x).card = (orbitVisitPattern (f^[n]) Q k x).card :=
  Finset.card_image_of_injective _ Fin.val_injective

end Erdos1148.DukeArithmetic

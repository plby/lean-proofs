import ErdosProblems.Erdos19.GraphDegreeAccounting
import ErdosProblems.Erdos19.GraphLoadStep

/-! # Degree margins for a packing round -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*} [Fintype V]

theorem between_self_support_subset (G : _root_.SimpleGraph V) (A : Set V) :
    (G.between A A).support ⊆ A := by
  rintro v ⟨w, hw⟩
  exact hw.2.elim And.left And.left

theorem neighbor_ncard_between_self_le (G : _root_.SimpleGraph V) (A : Set V) (v : V) :
    ((G.between A A).neighborSet v).ncard ≤ (G.neighborSet v).ncard :=
  Set.ncard_le_ncard (fun _ h ↦ h.1)

theorem neighbor_ncard_le_between_self_add_compl (G : _root_.SimpleGraph V)
    (A : Set V) {v : V} (hv : v ∈ A) :
    (G.neighborSet v).ncard ≤ ((G.between A A).neighborSet v).ncard + Aᶜ.ncard := by
  classical
  have hsub : G.neighborSet v ⊆ (G.between A A).neighborSet v ∪ Aᶜ := by
    intro w hw
    by_cases hwA : w ∈ A
    · exact Or.inl ⟨hw, Or.inl ⟨hv, hwA⟩⟩
    · exact Or.inr hwA
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)

theorem base_degree_bounds (G R U : _root_.SimpleGraph V)
    (hRG : R ≤ G) (hUG : U ≤ G) (a r i L : ℕ) (v : V)
    (hG : Fintype.card V ≤ (G.neighborSet v).ncard + a)
    (hRlo : r ≤ (R.neighborSet v).ncard + a)
    (hRhi : (R.neighborSet v).ncard ≤ r + a)
    (hUlo : i ≤ (U.neighborSet v).ncard + a)
    (hUhi : (U.neighborSet v).ncard ≤ i)
    (hload : ((R ⊓ U).neighborSet v).ncard ≤ L) :
    Fintype.card V ≤ ((G \ (R ⊔ U)).neighborSet v).ncard + r + i + 2 * a ∧
    ((G \ (R ⊔ U)).neighborSet v).ncard + r + i ≤ Fintype.card V + 2 * a + L := by
  have hidentity := base_reservoir_used_degree_identity G R U hRG hUG v
  have hGhi : (G.neighborSet v).ncard ≤ Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (G.neighborSet v)
  omega

theorem active_base_degree_bounds (G R U : _root_.SimpleGraph V)
    (hRG : R ≤ G) (hUG : U ≤ G) (A : Set V) (a r i L : ℕ)
    (hsmall : Aᶜ.ncard ≤ a) (hri : r + i + 3 * a ≤ Fintype.card V)
    (hG : ∀ v, Fintype.card V ≤ (G.neighborSet v).ncard + a)
    (hRlo : ∀ v, r ≤ (R.neighborSet v).ncard + a)
    (hRhi : ∀ v, (R.neighborSet v).ncard ≤ r + a)
    (hUlo : ∀ v, i ≤ (U.neighborSet v).ncard + a)
    (hUhi : ∀ v, (U.neighborSet v).ncard ≤ i)
    (hload : ∀ v, ((R ⊓ U).neighborSet v).ncard ≤ L) :
    (∀ v ∈ A, Fintype.card V - r - i - 3 * a ≤
      (((G \ (R ⊔ U)).between A A).neighborSet v).ncard) ∧
    (∀ v, (((G \ (R ⊔ U)).between A A).neighborSet v).ncard ≤
      Fintype.card V - r - i + 2 * a + L) := by
  constructor
  · intro v hv
    have hb := (base_degree_bounds G R U hRG hUG a r i L v
      (hG v) (hRlo v) (hRhi v) (hUlo v) (hUhi v) (hload v)).1
    have hrestrict := neighbor_ncard_le_between_self_add_compl (G \ (R ⊔ U)) A hv
    omega
  · intro v
    have hb := (base_degree_bounds G R U hRG hUG a r i L v
      (hG v) (hRlo v) (hRhi v) (hUlo v) (hUhi v) (hload v)).2
    have hrestrict := neighbor_ncard_between_self_le (G \ (R ⊔ U)) A v
    omega

theorem active_base_uncovered_bound (A : Set V) (a r i L c : ℕ)
    (hri : r + i + 3 * a ≤ Fintype.card V)
    (hsize : Fintype.card V ≤ c * (Fintype.card V - r - i - 3 * a + 1)) :
    A.ncard * ((Fintype.card V - r - i + 2 * a + L) + 1 -
      (Fintype.card V - r - i - 3 * a)) ≤
    (c * (5 * a + L + 1)) * ((Fintype.card V - r - i + 2 * a + L) + 1) := by
  have hA : A.ncard ≤ Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card A
  have hdiff : ((Fintype.card V - r - i + 2 * a + L) + 1 -
      (Fintype.card V - r - i - 3 * a)) = 5 * a + L + 1 := by omega
  rw [hdiff]
  have hsize' : Fintype.card V ≤ c * (Fintype.card V - r - i + 2 * a + L + 1) :=
    hsize.trans (Nat.mul_le_mul_left c (by omega))
  nlinarith only [Nat.mul_le_mul_right (5 * a + L + 1) (hA.trans hsize')]

theorem available_reservoir_degree_lower (R U : _root_.SimpleGraph V) (r a L : ℕ)
    (hR : ∀ v, r ≤ (R.neighborSet v).ncard + a)
    (hload : ∀ v, ((R ⊓ U).neighborSet v).ncard ≤ L) :
    ∀ v, r ≤ ((R \ U).neighborSet v).ncard + a + L := by
  intro v
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (R.neighborSet v) (U.neighborSet v)
  rw [neighborSet_sdiff]
  have hr := hR v
  have hl := hload v
  rw [neighborSet_inf] at hl
  omega

#print axioms active_base_degree_bounds
#print axioms active_base_uncovered_bound

end Erdos19

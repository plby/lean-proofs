import ErdosProblems.Erdos19.ExceptionalColorTrace

/-! # Bounding the number of singleton colors with large coverage -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]

noncomputable def largeCoverageColors (H : SetHypergraph V) (c : H → C) (A : ℕ) : Finset C :=
  univ.filter fun a ↦ A < (H.coveredVertices {e | c e = a}).ncard

theorem exists_singleton_edge_of_large_coverage (H : SetHypergraph V) (c : H → C)
    (A : ℕ) (hbounded : H.IsCoverBoundedColoring c A) (a : C)
    (ha : A < (H.coveredVertices {e | c e = a}).ncard) :
    ∃ e : H, c e = a ∧ A < e.1.ncard ∧ H.coveredVertices {f | c f = a} = e.1 := by
  have hsmall : ({e : H | c e = a} : Set H).ncard ≤ 1 :=
    (hbounded a).resolve_right (Nat.not_le.mpr ha)
  obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show
    0 < (H.coveredVertices {e | c e = a}).ncard by omega)
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hea, _⟩ := Set.mem_iUnion.mp he
  have hcover := H.coveredVertices_eq_of_singleton_family _ hsmall e hea
  exact ⟨e, hea, by simpa only [hcover] using ha, hcover⟩

theorem largeCoverageColors_pair_budget (H : SetHypergraph V) (hlinear : H.IsLinear)
    (c : H → C) (A : ℕ) (hbounded : H.IsCoverBoundedColoring c A) :
    (H.largeCoverageColors c A).card * A * (A + 1) ≤ Fintype.card V * (Fintype.card V - 1) := by
  classical
  let T := H.largeCoverageColors c A
  have hex (a : T) := H.exists_singleton_edge_of_large_coverage c A hbounded a.1
    (mem_filter.mp a.2).2
  choose edge hedge hsize hcover using hex
  have hinj : Function.Injective edge := by
    intro a b hab
    apply Subtype.ext
    exact (hedge a).symm.trans ((congrArg c hab).trans (hedge b))
  let incl : T ↪ H := ⟨edge, hinj⟩
  have hweight (a : T) : A * (A + 1) ≤ (edge a).1.ncard * ((edge a).1.ncard - 1) := by
    have h1 : A + 1 ≤ (edge a).1.ncard := hsize a
    have h2 : A ≤ (edge a).1.ncard - 1 := by omega
    simpa only [Nat.mul_comm A (A + 1)] using Nat.mul_le_mul h1 h2
  calc
    _ = ∑ _a : T, A * (A + 1) := by simp [T, Nat.mul_assoc]
    _ ≤ ∑ a : T, (edge a).1.ncard * ((edge a).1.ncard - 1) :=
      sum_le_sum (fun a _ ↦ hweight a)
    _ = ∑ e ∈ univ.map incl, e.1.ncard * (e.1.ncard - 1) := by rw [sum_map]; rfl
    _ ≤ ∑ e : H, e.1.ncard * (e.1.ncard - 1) := sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := H.sum_ncard_mul_sub_one_le hlinear

theorem largeCoverageColors_card_le_constant (n w : ℕ) (hw : 0 < w) (hn : w ≤ n)
    (H : SetHypergraph (Fin n)) (hlinear : H.IsLinear) (c : H → C)
    (hbounded : H.IsCoverBoundedColoring c (n / w)) :
    (H.largeCoverageColors c (n / w)).card ≤ 4 * w ^ 2 := by
  let A := n / w
  have hA : 0 < A := (Nat.le_div_iff_mul_le hw).mpr (by simpa using hn)
  have hfloor := Nat.lt_mul_div_succ n hw
  have hnscale : n ≤ 2 * w * A := by
    have hscale := Nat.mul_le_mul_left w (show A + 1 ≤ 2 * A by omega)
    change n < w * (A + 1) at hfloor
    nlinarith only [hfloor, hscale]
  have hbudget := H.largeCoverageColors_pair_budget hlinear c A hbounded
  simp only [Fintype.card_fin] at hbudget
  have hnsub := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hsquare := Nat.mul_self_le_mul_self hnscale
  have hweight : (H.largeCoverageColors c A).card * A ^ 2 ≤
      (H.largeCoverageColors c A).card * A * (A + 1) := by
    have h := Nat.mul_le_mul_left ((H.largeCoverageColors c A).card * A)
      (Nat.le_succ A)
    nlinarith only [h]
  apply Nat.le_of_mul_le_mul_left (c := A ^ 2) _ (pow_pos hA 2)
  nlinarith only [hweight, hbudget, hnsub, hsquare]

#print axioms largeCoverageColors_card_le_constant

end Erdos19.SetHypergraph

import Mathlib

namespace Erdos526

open Set
open scoped BigOperators
noncomputable section

def weightedCover {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (w : κ → Finset ι → ℝ) : List κ → Finset ι → ℝ
  | [], U => if U = ∅ then 1 else 0
  | k :: K, U => ∑ S : Finset ι, w k S * weightedCover w K (U \ S)

def weightedTotal {ι κ : Type*} [Fintype ι]
    (w : κ → Finset ι → ℝ) (K : List κ) : ℝ :=
  (K.map fun k ↦ ∑ S : Finset ι, w k S).prod

lemma weightedCover_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {w : κ → Finset ι → ℝ} (hw : ∀ k S, 0 ≤ w k S) :
    ∀ K U, 0 ≤ weightedCover w K U := by
  intro K
  induction K with
  | nil =>
      intro U
      simp only [weightedCover]
      split_ifs <;> norm_num
  | cons k K ih =>
      intro U
      simp only [weightedCover]
      exact Finset.sum_nonneg fun S _ ↦ mul_nonneg (hw k S) (ih (U \ S))

lemma weightedTotal_nonneg {ι κ : Type*} [Fintype ι]
    {w : κ → Finset ι → ℝ} (hw : ∀ k S, 0 ≤ w k S) :
    ∀ K, 0 ≤ weightedTotal w K := by
  intro K
  unfold weightedTotal
  exact List.prod_nonneg fun r hr ↦ by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    exact Finset.sum_nonneg fun S _ ↦ hw k S

lemma weightedCover_anti {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {w : κ → Finset ι → ℝ} (hw : ∀ k S, 0 ≤ w k S) :
    ∀ K {U V : Finset ι}, U ⊆ V → weightedCover w K V ≤ weightedCover w K U := by
  intro K
  induction K with
  | nil =>
      intro U V hUV
      simp only [weightedCover]
      by_cases hV : V = ∅
      · have hU : U = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun x hx ↦ by
          have := hUV hx
          simpa [hV] using this
        simp [hU, hV]
      · split_ifs <;> norm_num
  | cons k K ih =>
      intro U V hUV
      simp only [weightedCover]
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left
        (ih (Finset.sdiff_subset_sdiff_left S hUV))
        (hw k S)

lemma weightedTotal_cons {ι κ : Type*} [Fintype ι]
    (w : κ → Finset ι → ℝ) (k : κ) (K : List κ) :
    weightedTotal w (k :: K) =
      (∑ S : Finset ι, w k S) * weightedTotal w K := by
  simp [weightedTotal]

lemma weightedCover_contaminate_empty {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    {d b : κ → Finset ι → ℝ} {h : κ → ℝ}
    (hd : ∀ k S, 0 ≤ d k S) (hh : ∀ k, 0 ≤ h k)
    (hb : ∀ k S, b k S = d k S + if S = ∅ then h k else 0) :
    ∀ K U,
      weightedCover b K U * weightedTotal d K ≤
        weightedCover d K U * weightedTotal b K := by
  intro K
  induction K with
  | nil =>
      intro U
      rfl
  | cons k K ih =>
      intro U
      have hbnonneg : ∀ k S, 0 ≤ b k S := by
        intro r S
        rw [hb]
        split_ifs
        · exact add_nonneg (hd r S) (hh r)
        · simpa using hd r S
      let D : ℝ := ∑ S : Finset ι, d k S
      let H : ℝ := h k
      let R : ℝ := weightedCover d K U
      let C : ℝ := weightedCover d (k :: K) U
      let B : ℝ := ∑ S : Finset ι, b k S * weightedCover d K (U \ S)
      have hD : 0 ≤ D := Finset.sum_nonneg fun S _ ↦ hd k S
      have hH : 0 ≤ H := hh k
      have htaild : 0 ≤ weightedTotal d K := weightedTotal_nonneg hd K
      have htailb : 0 ≤ weightedTotal b K := weightedTotal_nonneg hbnonneg K
      have hfirstTotal : (∑ S : Finset ι, b k S) = D + H := by
        simp_rw [hb]
        rw [Finset.sum_add_distrib]
        have hempty : (∑ S : Finset ι, if S = ∅ then h k else 0) = h k := by
          simp
        rw [hempty]
      have hB : B = C + H * R := by
        dsimp only [B, C, H, R]
        simp only [weightedCover]
        simp_rw [hb]
        simp only [add_mul, Finset.sum_add_distrib]
        simp
      have hDR : D * R ≤ C := by
        dsimp only [D, R, C]
        simp only [weightedCover]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_left
          (weightedCover_anti hd K Finset.sdiff_subset) (hd k S)
      have hstep : B * D ≤ C * (D + H) := by
        rw [hB]
        nlinarith
      have hmix : weightedCover b (k :: K) U * weightedTotal d K ≤
          B * weightedTotal b K := by
        simp only [weightedCover]
        calc
          (∑ S : Finset ι, b k S * weightedCover b K (U \ S)) *
              weightedTotal d K =
              ∑ S : Finset ι,
                b k S * (weightedCover b K (U \ S) * weightedTotal d K) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro S hS
                  ring
          _ ≤ ∑ S : Finset ι,
              b k S * (weightedCover d K (U \ S) * weightedTotal b K) := by
                apply Finset.sum_le_sum
                intro S hS
                exact mul_le_mul_of_nonneg_left (ih (U \ S)) (hbnonneg k S)
          _ = B * weightedTotal b K := by
            dsimp only [B]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro S hS
            ring
      rw [weightedTotal_cons, weightedTotal_cons, hfirstTotal]
      calc
        weightedCover b (k :: K) U * (D * weightedTotal d K) =
            (weightedCover b (k :: K) U * weightedTotal d K) * D := by ring
        _ ≤ (B * weightedTotal b K) * D :=
          mul_le_mul_of_nonneg_right hmix hD
        _ = (B * D) * weightedTotal b K := by ring
        _ ≤ (C * (D + H)) * weightedTotal b K :=
          mul_le_mul_of_nonneg_right hstep htailb
        _ = weightedCover d (k :: K) U *
            ((D + H) * weightedTotal b K) := by
              dsimp only [C]
              ring

universe u v

def StateAssignments (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Finset ι × StateAssignments ι n

instance stateAssignmentsFintype (ι : Type u) [Fintype ι] (n : ℕ) :
    Fintype (StateAssignments ι n) := by
  induction n with
  | zero =>
      simp only [StateAssignments]
      infer_instance
  | succ n ih =>
      simp only [StateAssignments]
      letI := ih
      infer_instance

def assignmentUnion {ι : Type u} [DecidableEq ι] :
    { n : ℕ } → StateAssignments ι n → Finset ι
  | 0, _ => ∅
  | _ + 1, q => q.1 ∪ assignmentUnion q.2

def assignmentWeight {ι : Type u} {κ : Type v} [DecidableEq ι]
    (w : κ → Finset ι → ℝ) :
    (K : List κ) → StateAssignments ι K.length → ℝ
  | [], _ => 1
  | k :: K, q => w k q.1 * assignmentWeight w K q.2

lemma subset_union_iff_sdiff_subset' {U S T : Finset ι} [DecidableEq ι] :
    U ⊆ S ∪ T ↔ U \ S ⊆ T := by
  constructor
  · intro h x hx
    have hxu := h (Finset.mem_sdiff.1 hx).1
    rcases Finset.mem_union.1 hxu with hxs | hxt
    · exact False.elim ((Finset.mem_sdiff.1 hx).2 hxs)
    · exact hxt
  · intro h x hx
    by_cases hxs : x ∈ S
    · exact Finset.mem_union_left T hxs
    · exact Finset.mem_union_right S (h (Finset.mem_sdiff.2 ⟨hx, hxs⟩))

lemma weightedCover_eq_assignmentSum {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] (w : κ → Finset ι → ℝ) :
    ∀ (K : List κ) (U : Finset ι),
      weightedCover w K U =
        ∑ q : StateAssignments ι K.length,
          if U ⊆ assignmentUnion q then assignmentWeight w K q else 0 := by
  intro K
  induction K with
  | nil =>
      intro U
      change (if U = ∅ then 1 else 0) =
        ∑ _q : PUnit, if U ⊆ (∅ : Finset ι) then 1 else 0
      rw [Fintype.sum_unique]
      simp only [Finset.subset_empty]
  | cons k K ih =>
      intro U
      rw [weightedCover]
      change (∑ S : Finset ι, w k S * weightedCover w K (U \ S)) =
        ∑ x : Finset ι × StateAssignments ι K.length,
          if U ⊆ x.1 ∪ assignmentUnion x.2 then
            w k x.1 * assignmentWeight w K x.2 else 0
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro S hS
      simp only [Prod.fst, Prod.snd]
      simp only [subset_union_iff_sdiff_subset']
      rw [ih]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> ring

end
end Erdos526

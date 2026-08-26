import Mathlib
import ErdosProblems.Erdos336.DensePowerSaturation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A dense coset progression has a long full-fibre double
-/

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The elementary numerical threshold behind the long central core. -/
lemma dense_progression_core_arithmetic {L : ℕ} (hL : 15 ≤ L) :
    5 * (L + 1 + (L + 1) / 2) ≤ 8 * L := by
  omega

lemma dense_progression_core_density {L V n : ℕ} (hL : 15 ≤ L)
    (hdense : 4 * L * V < 5 * n) :
    (L + 1 + (L + 1) / 2) * V < 2 * n := by
  have hcoef := dense_progression_core_arithmetic hL
  have hmul : 5 * ((L + 1 + (L + 1) / 2) * V) ≤
      8 * (L * V) := by
    nlinarith [Nat.zero_le V]
  have hdense2 : 8 * (L * V) < 10 * n := by nlinarith
  omega

/-- If a finite set and its reflection around `y` have union smaller than
`2|S|`, they intersect, so `y∈S+S`. -/
theorem groupRepExactly_two_of_reflection_union_bound
    {S : Set G} {y : G} {K : ℕ}
    (hunion : ((S.toFinite.toFinset) ∪
      (S.toFinite.toFinset).image (fun x => y - x)).card ≤ K)
    (hsmall : K < 2 * S.ncard) :
    GroupRepExactly S 2 y := by
  classical
  let A : Finset G := S.toFinite.toFinset
  let R : Finset G := A.image (fun x => y - x)
  have hcardA : A.card = S.ncard := by
    dsimp [A]
    rw [Set.ncard_eq_toFinset_card]
  have hinj : Function.Injective (fun x : G => y - x) :=
    sub_right_injective
  have hcardR : R.card = A.card := by
    dsimp [R]
    exact Finset.card_image_of_injective A hinj
  have hnotdisj : ¬ Disjoint A R := by
    intro hdisj
    have hcardUnion := Finset.card_union_of_disjoint hdisj
    have hle : (A ∪ R).card ≤ K := by simpa [A, R] using hunion
    rw [hcardUnion, hcardR, hcardA] at hle
    omega
  obtain ⟨z, hzA, hzR⟩ := Finset.not_disjoint_iff.mp hnotdisj
  obtain ⟨x, hxA, hx⟩ := Finset.mem_image.mp hzR
  refine ⟨[z, x], by simp, ?_, ?_⟩
  · intro w hw
    simp at hw
    rcases hw with rfl | rfl
    · exact S.toFinite.mem_toFinset.mp hzA
    · exact S.toFinite.mem_toFinset.mp hxA
  · simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [← hx]
    abel

/-- A convenient explicit finite fibre. -/
def homFiberFinset {m : ℕ} (π : G →+ ZMod m) (z : ZMod m) : Finset G :=
  Finset.univ.filter fun x => π x = z

@[simp] theorem mem_homFiberFinset {m : ℕ} (π : G →+ ZMod m)
    {z : ZMod m} {x : G} :
    x ∈ homFiberFinset π z ↔ π x = z := by
  simp [homFiberFinset]

/-- If `S` is supported on `L+1` consecutive quotient fibres and has the
Lev-rank-one density `4L V < 5|S|`, then `2S` contains every fibre in a
consecutive quotient interval of span `L`.  Here `V` is any uniform upper
bound for the quotient-fibre cardinalities. -/
theorem dense_outer_interval_gives_full_fiber_core
    {m : ℕ} (π : G →+ ZMod m) {S : Set G}
    {α : ZMod m} {L V : ℕ}
    (hL : 15 ≤ L)
    (houter : ∀ x ∈ S, ∃ k : ℕ, k ≤ L ∧
      π x = α + (k : ZMod m))
    (hfiber : ∀ z : ZMod m, (homFiberFinset π z).card ≤ V)
    (hdense : 4 * L * V < 5 * S.ncard) :
    let β : ZMod m := α + α + (L - L / 2 : ℕ)
    ∀ s : ℕ, s ≤ L → ∀ y : G,
      π y = β + (s : ZMod m) → GroupRepExactly S 2 y := by
  classical
  dsimp only
  intro s hs y hy
  let r : ℕ := L / 2
  let lo : ℕ := min r s
  let hi : ℕ := L + max r s
  let I : Finset ℕ := Finset.Icc lo hi
  let label : ℕ → ZMod m := fun n => α - (r : ZMod m) + (n : ZMod m)
  let J : Finset (ZMod m) := I.image label
  let U : Finset G := J.biUnion (homFiberFinset π)
  let A : Finset G := S.toFinite.toFinset
  let R : Finset G := A.image (fun x => y - x)
  have hA_sub : A ⊆ U := by
    intro x hx
    have hxS : x ∈ S := S.toFinite.mem_toFinset.mp hx
    obtain ⟨k, hk, hπx⟩ := houter x hxS
    let n : ℕ := r + k
    have hnlo : lo ≤ n := by dsimp [lo, n]; omega
    have hnhi : n ≤ hi := by dsimp [hi, n]; omega
    have hnI : n ∈ I := by simp [I, hnlo, hnhi]
    have hlabel : label n = π x := by
      dsimp [label, n, r]
      rw [hπx]
      push_cast
      ring
    have hJ : π x ∈ J := by
      exact Finset.mem_image.2 ⟨n, hnI, hlabel⟩
    dsimp [U]
    rw [Finset.mem_biUnion]
    exact ⟨π x, hJ, by simp [homFiberFinset]⟩
  have hR_sub : R ⊆ U := by
    intro z hz
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hz
    have hxS : x ∈ S := S.toFinite.mem_toFinset.mp hxA
    obtain ⟨k, hk, hπx⟩ := houter x hxS
    let n : ℕ := L + s - k
    have hkn : k ≤ L + s := le_trans hk (Nat.le_add_right L s)
    have hnlo : lo ≤ n := by dsimp [lo, n]; omega
    have hnhi : n ≤ hi := by dsimp [hi, n]; omega
    have hnI : n ∈ I := by simp [I, hnlo, hnhi]
    have hlabel : label n = π (y - x) := by
      rw [map_sub, hy, hπx]
      dsimp [label, n, r]
      rw [Nat.cast_sub hkn, Nat.cast_sub (Nat.div_le_self L 2)]
      push_cast
      ring
    have hJ : π (y - x) ∈ J := by
      exact Finset.mem_image.2 ⟨n, hnI, hlabel⟩
    dsimp [U]
    rw [Finset.mem_biUnion]
    exact ⟨π (y - x), hJ, by simp [homFiberFinset]⟩
  have hIcard : I.card ≤ L + 1 + (L + 1) / 2 := by
    dsimp [I, lo, hi, r]
    rw [Nat.card_Icc]
    omega
  have hJcard : J.card ≤ L + 1 + (L + 1) / 2 :=
    le_trans Finset.card_image_le hIcard
  have hUcard : U.card ≤ (L + 1 + (L + 1) / 2) * V := by
    calc
      U.card ≤ J.card * V := by
        dsimp [U]
        exact Finset.card_biUnion_le_card_mul J (homFiberFinset π) V
          (fun z _ => hfiber z)
      _ ≤ (L + 1 + (L + 1) / 2) * V :=
        Nat.mul_le_mul_right V hJcard
  have hunion : (A ∪ R).card ≤
      (L + 1 + (L + 1) / 2) * V := by
    exact le_trans (Finset.card_le_card (Finset.union_subset hA_sub hR_sub)) hUcard
  have hsmall := dense_progression_core_density hL hdense
  exact groupRepExactly_two_of_reflection_union_bound hunion hsmall

end Erdos336

import ErdosProblems.Erdos421.ZeroRepresentation

/-! # Bounding coupled equations by compatible tuple fibers

For each fixed pair of restricted tuples, zero representations dominate
the free-variable count. A finite code bounds the number of compatible
partners, without another Fourier estimate.
-/

namespace Erdos421

theorem card_product_filter_eq_sum {X Y : Type*} (S : Finset X) (T : Finset Y)
    (P : X → Y → Prop) [∀ x, DecidablePred (P x)] :
    ((S ×ˢ T).filter (fun z ↦ P z.1 z.2)).card = ∑ x ∈ S, (T.filter (P x)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem coupled_count_eq_sum_difference {X Y G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset X) (T : Finset Y) (f : X → G) (g : Y → G) :
    (((S ×ˢ T) ×ˢ (S ×ˢ T)).filter
      (fun p ↦ f p.1.1 + g p.1.2 = f p.2.1 + g p.2.2)).card =
      ∑ xy ∈ S ×ˢ S, ((T ×ˢ T).filter (fun uv ↦ g uv.1 - g uv.2 = f xy.2 - f xy.1)).card := by
  rw [card_product_filter_eq_sum (S ×ˢ T) (S ×ˢ T)
    (fun a b ↦ f a.1 + g a.2 = f b.1 + g b.2)]
  have hleft (a : X × Y) := card_product_filter_eq_sum S T
    (fun y v ↦ f a.1 + g a.2 = f y + g v)
  have hright (xy : X × X) := card_product_filter_eq_sum T T
    (fun u v ↦ g u - g v = f xy.2 - f xy.1)
  simp only [hleft, hright, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro u _
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter, sub_eq_sub_iff_add_eq_add, add_comm]

theorem compatible_pair_count_le {X C : Type*} [DecidableEq C] (S : Finset X)
    (code : X → C) {B : ℕ} (hB : ∀ c : C, (S.filter (fun x ↦ code x = c)).card ≤ B) :
    ((S ×ˢ S).filter (fun xy ↦ code xy.1 = code xy.2)).card ≤ S.card * B := by
  rw [card_product_filter_eq_sum S S (fun x y ↦ code x = code y)]
  calc
    _ ≤ ∑ _x ∈ S, B := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [eq_comm] using hB (code x)
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

theorem coupled_count_le_compatible_fibers {X Y G C : Type*}
    [AddCommGroup G] [DecidableEq G] [DecidableEq C]
    (S : Finset X) (T : Finset Y) (f : X → G) (g : Y → G) (code : X → C)
    {B : ℕ} (hB : ∀ c : C, (S.filter (fun x ↦ code x = c)).card ≤ B)
    (hcompat : ∀ x ∈ S, ∀ y ∈ S, ∀ u ∈ T, ∀ v ∈ T,
      f x + g u = f y + g v → code x = code y) :
    (((S ×ˢ T) ×ˢ (S ×ˢ T)).filter
      (fun p ↦ f p.1.1 + g p.1.2 = f p.2.1 + g p.2.2)).card ≤
      S.card * B * ((T ×ˢ T).filter (fun uv ↦ g uv.1 - g uv.2 = 0)).card := by
  classical
  let Z := ((T ×ˢ T).filter (fun uv ↦ g uv.1 - g uv.2 = 0)).card
  have hpair (xy : X × X) (hxy : xy ∈ S ×ˢ S) :
      ((T ×ˢ T).filter (fun uv ↦ g uv.1 - g uv.2 = f xy.2 - f xy.1)).card ≤
        if code xy.1 = code xy.2 then Z else 0 := by
    by_cases he : code xy.1 = code xy.2
    · rw [if_pos he]
      exact card_difference_fiber_le_zero T g (f xy.2 - f xy.1)
    · rw [if_neg he]
      apply Nat.le_zero.mpr
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro uv huv
      obtain ⟨huvT, heq⟩ := Finset.mem_filter.mp huv
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huvT
      apply he (hcompat xy.1 hx xy.2 hy uv.1 hu uv.2 hv ?_)
      simpa only [sub_eq_sub_iff_add_eq_add, add_comm] using heq
  calc
    _ = ∑ xy ∈ S ×ˢ S,
        ((T ×ˢ T).filter (fun uv ↦ g uv.1 - g uv.2 = f xy.2 - f xy.1)).card :=
      coupled_count_eq_sum_difference S T f g
    _ ≤ ∑ xy ∈ S ×ˢ S, if code xy.1 = code xy.2 then Z else 0 := Finset.sum_le_sum hpair
    _ = ((S ×ˢ S).filter (fun xy ↦ code xy.1 = code xy.2)).card * Z := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    _ ≤ S.card * B * Z := Nat.mul_le_mul_right Z (compatible_pair_count_le S code hB)

end Erdos421

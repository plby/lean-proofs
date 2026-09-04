import ErdosProblems.Erdos489.PrimitiveRayPacking
import ErdosProblems.Erdos489.RoughCoprimePairs

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- A finite, pairwise nonproportional family of positive quotient vectors in
one diagonal strip obeys the same fan-area bound as an explicitly ordered
family. -/
theorem positive_ray_finset_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hbsX : ∀ z ∈ T, b * z.2 ≤ X)
    (hside : ∀ z ∈ T, b * z.2 < a * z.1)
    (hstrip : ∀ z ∈ T, a * z.1 ≤ b * z.2 + D)
    (hnonprop : ∀ z ∈ T, ∀ w ∈ T,
      z.1 * w.2 = w.1 * z.2 → z = w) :
    a * b * (T.card - 1) ≤ 2 * X * D := by
  by_cases hsmall : T.card ≤ 1
  · have hz : T.card - 1 = 0 := Nat.sub_eq_zero_of_le hsmall
    simp [hz]
  · have hcard : 1 < T.card := by omega
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    let α := {z : ℕ × ℕ // z ∈ T}
    let key : α → ℚ := fun z => (z.1.1 : ℚ) / (z.1.2 : ℚ)
    have hkeyinj : Function.Injective key := by
      intro z w hkey
      apply Subtype.ext
      apply hnonprop z.1 z.2 w.1 w.2
      have hzs : (z.1.2 : ℚ) ≠ 0 := by
        exact_mod_cast (hs z.1 z.2).ne'
      have hws : (w.1.2 : ℚ) ≠ 0 := by
        exact_mod_cast (hs w.1 w.2).ne'
      have hcross : (z.1.1 : ℚ) * (w.1.2 : ℚ) =
          (w.1.1 : ℚ) * (z.1.2 : ℚ) :=
        (div_eq_div_iff hzs hws).mp hkey
      exact_mod_cast hcross
    let rel : α → α → Prop := fun z w => key z ≤ key w
    let : IsTrans α rel := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
    let : Std.Antisymm rel :=
      ⟨fun _ _ h₁ h₂ => hkeyinj (le_antisymm h₁ h₂)⟩
    let : Std.Total rel := ⟨fun z w => le_total (key z) (key w)⟩
    let U : Finset α := Finset.univ
    let Ls : List α := U.sort rel
    obtain ⟨zv, hzv⟩ := hTne
    let z0 : α := ⟨zv, hzv⟩
    let z : ℕ → ℕ × ℕ := fun i => (Ls.getD i z0).1
    have hlen : Ls.length = T.card := by
      dsimp [Ls, U]
      rw [Finset.length_sort, Finset.card_univ, Fintype.card_coe]
    have hzmem : ∀ i, z i ∈ T := by
      intro i
      by_cases hi : i < Ls.length
      · have hzi : z i = Ls[i].1 := by
          dsimp [z]
          rw [List.getD_eq_getElem Ls z0 hi]
        rw [hzi]
        exact Ls[i].2
      · have hi' : Ls.length ≤ i := by omega
        simpa [z, List.getD_eq_default _ _ hi'] using z0.2
    have hzorder : ∀ i < T.card - 1,
        (z i).1 * (z (i + 1)).2 < (z (i + 1)).1 * (z i).2 := by
      intro i hi
      have hi0 : i < Ls.length := by omega
      have hi1 : i + 1 < Ls.length := by omega
      have hlekey : key Ls[i] ≤ key Ls[i + 1] := by
        have hpw := Finset.pairwise_sort U rel
        exact (List.pairwise_iff_getElem.mp hpw) i (i + 1) hi0 hi1 (by omega)
      have hneα : Ls[i] ≠ Ls[i + 1] := by
        intro heq
        have hiEq : i = i + 1 :=
          (Finset.sort_nodup U rel).getElem_inj_iff.mp heq
        omega
      have hnekey : key Ls[i] ≠ key Ls[i + 1] :=
        fun heq => hneα (hkeyinj heq)
      have hltkey : key Ls[i] < key Ls[i + 1] :=
        lt_of_le_of_ne hlekey hnekey
      have hden0 : (0 : ℚ) < (Ls[i].1.2 : ℕ) := by
        exact_mod_cast hs Ls[i].1 Ls[i].2
      have hden1 : (0 : ℚ) < (Ls[i + 1].1.2 : ℕ) := by
        exact_mod_cast hs Ls[i + 1].1 Ls[i + 1].2
      have hcrossQ : (Ls[i].1.1 : ℚ) * (Ls[i + 1].1.2 : ℕ) <
          (Ls[i + 1].1.1 : ℚ) * (Ls[i].1.2 : ℕ) := by
        exact (div_lt_div_iff₀ hden0 hden1).mp hltkey
      have hcrossN : Ls[i].1.1 * Ls[i + 1].1.2 <
          Ls[i + 1].1.1 * Ls[i].1.2 := by
        exact_mod_cast hcrossQ
      have hzi : z i = Ls[i].1 := by
        dsimp [z]
        rw [List.getD_eq_getElem Ls z0 hi0]
      have hzi1 : z (i + 1) = Ls[i + 1].1 := by
        dsimp [z]
        rw [List.getD_eq_getElem Ls z0 hi1]
      rw [hzi, hzi1]
      exact hcrossN
    apply ordered_positive_ray_count_bound (T.card - 1) a b X D
      (fun i => (z i).1) (fun i => (z i).2) ha hb hX hD
    · intro i
      exact hr (z i) (hzmem i)
    · intro i
      exact hs (z i) (hzmem i)
    · intro i
      exact hbsX (z i) (hzmem i)
    · intro i
      exact hside (z i) (hzmem i)
    · intro i
      exact hstrip (z i) (hzmem i)
    · exact hzorder

/-- Coprime covered vectors cannot represent the same quotient ray twice. -/
theorem quotient_pair_eq_of_proportional_of_covered_coprime
    (a b r s u v : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hprop : r * v = u * s)
    (hc₁ : Nat.Coprime (a * r) (b * s))
    (hc₂ : Nat.Coprime (a * u) (b * v)) :
    (r, s) = (u, v) := by
  have hcovered : (a * r) * (b * v) = (b * s) * (a * u) := by
    calc
      (a * r) * (b * v) = (a * b) * (r * v) := by ring
      _ = (a * b) * (u * s) := by rw [hprop]
      _ = (b * s) * (a * u) := by ring
  have heq := nat_pair_eq_of_proportional_of_coprime
    (a * r) (b * s) (a * u) (b * v) hcovered hc₁ hc₂
  apply Prod.ext
  · exact Nat.eq_of_mul_eq_mul_left ha heq.1
  · exact Nat.eq_of_mul_eq_mul_left hb heq.2

/-- One-sided capacity bound for a finite set of quotient pairs whose covered
vectors are primitive. -/
theorem primitive_covered_positive_ray_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hprimitive : ∀ z ∈ T, Nat.Coprime (a * z.1) (b * z.2))
    (hbsX : ∀ z ∈ T, b * z.2 ≤ X)
    (hside : ∀ z ∈ T, b * z.2 < a * z.1)
    (hstrip : ∀ z ∈ T, a * z.1 ≤ b * z.2 + D) :
    a * b * (T.card - 1) ≤ 2 * X * D := by
  apply positive_ray_finset_count_bound T a b X D ha hb hX hD
    hr hs hbsX hside hstrip
  intro z hz w hw hprop
  exact quotient_pair_eq_of_proportional_of_covered_coprime
    a b z.1 z.2 w.1 w.2 ha hb hprop (hprimitive z hz) (hprimitive w hw)

/-- The symmetric one-sided bound for the strip `0 < b*s-a*r ≤ D`. -/
theorem primitive_covered_negative_ray_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hprimitive : ∀ z ∈ T, Nat.Coprime (a * z.1) (b * z.2))
    (harX : ∀ z ∈ T, a * z.1 ≤ X)
    (hside : ∀ z ∈ T, a * z.1 < b * z.2)
    (hstrip : ∀ z ∈ T, b * z.2 ≤ a * z.1 + D) :
    a * b * (T.card - 1) ≤ 2 * X * D := by
  let swapPair : ℕ × ℕ → ℕ × ℕ := fun z => (z.2, z.1)
  let U := T.image swapPair
  have hcard : U.card = T.card := by
    apply Finset.card_image_of_injective
    intro z w h
    dsimp [swapPair] at h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hbound := primitive_covered_positive_ray_count_bound U b a X D
    hb ha hX hD
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hs w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hr w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact (hprimitive w hw).symm)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact harX w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hside w hw)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      exact hstrip w hw)
  rw [hcard] at hbound
  simpa [Nat.mul_comm, Nat.mul_left_comm] using hbound

/-- Two-sided primitive-ray capacity.  Primitive covered vectors in
`0 < |a*r-b*s| ≤ D`, with both covered coordinates at most `X`, satisfy the
cross-multiplied count bound `ab·#T ≤ 4XD+2ab`. -/
theorem primitive_covered_two_sided_count_bound
    (T : Finset (ℕ × ℕ)) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hr : ∀ z ∈ T, 0 < z.1) (hs : ∀ z ∈ T, 0 < z.2)
    (hprimitive : ∀ z ∈ T, Nat.Coprime (a * z.1) (b * z.2))
    (harX : ∀ z ∈ T, a * z.1 ≤ X)
    (hbsX : ∀ z ∈ T, b * z.2 ≤ X)
    (hne : ∀ z ∈ T, a * z.1 ≠ b * z.2)
    (hdist : ∀ z ∈ T, Nat.dist (a * z.1) (b * z.2) ≤ D) :
    a * b * T.card ≤ 4 * X * D + 2 * (a * b) := by
  let Tp := T.filter fun z => b * z.2 < a * z.1
  let Tn := T.filter fun z => a * z.1 < b * z.2
  have hcover : T ⊆ Tp ∪ Tn := by
    intro z hz
    have hneq := hne z hz
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact Finset.mem_union_right Tp (Finset.mem_filter.mpr ⟨hz, hlt⟩)
    · exact Finset.mem_union_left Tn (Finset.mem_filter.mpr ⟨hz, hgt⟩)
  have hcardcover : T.card ≤ Tp.card + Tn.card := by
    calc
      T.card ≤ (Tp ∪ Tn).card := Finset.card_le_card hcover
      _ ≤ Tp.card + Tn.card := Finset.card_union_le Tp Tn
  have hp := primitive_covered_positive_ray_count_bound Tp a b X D
    ha hb hX hD
    (fun z hz => hr z (Finset.mem_filter.mp hz).1)
    (fun z hz => hs z (Finset.mem_filter.mp hz).1)
    (fun z hz => hprimitive z (Finset.mem_filter.mp hz).1)
    (fun z hz => hbsX z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => by
      have hzT := (Finset.mem_filter.mp hz).1
      have hdistz := hdist z hzT
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le
        (Nat.le_of_lt (Finset.mem_filter.mp hz).2)] at hdistz
      omega)
  have hn := primitive_covered_negative_ray_count_bound Tn a b X D
    ha hb hX hD
    (fun z hz => hr z (Finset.mem_filter.mp hz).1)
    (fun z hz => hs z (Finset.mem_filter.mp hz).1)
    (fun z hz => hprimitive z (Finset.mem_filter.mp hz).1)
    (fun z hz => harX z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => by
      have hzT := (Finset.mem_filter.mp hz).1
      have hdistz := hdist z hzT
      rw [Nat.dist_eq_sub_of_le
        (Nat.le_of_lt (Finset.mem_filter.mp hz).2)] at hdistz
      omega)
  have hp' : a * b * Tp.card ≤ 2 * X * D + a * b := by
    have hc : Tp.card ≤ (Tp.card - 1) + 1 := by omega
    have hm := Nat.mul_le_mul_left (a * b) hc
    calc
      a * b * Tp.card ≤ a * b * ((Tp.card - 1) + 1) := hm
      _ = a * b * (Tp.card - 1) + a * b := by ring
      _ ≤ 2 * X * D + a * b := Nat.add_le_add_right hp _
  have hn' : a * b * Tn.card ≤ 2 * X * D + a * b := by
    have hc : Tn.card ≤ (Tn.card - 1) + 1 := by omega
    have hm := Nat.mul_le_mul_left (a * b) hc
    calc
      a * b * Tn.card ≤ a * b * ((Tn.card - 1) + 1) := hm
      _ = a * b * (Tn.card - 1) + a * b := by ring
      _ ≤ 2 * X * D + a * b := Nat.add_le_add_right hn _
  have hmulcover := Nat.mul_le_mul_left (a * b) hcardcover
  calc
    a * b * T.card ≤ a * b * (Tp.card + Tn.card) := hmulcover
    _ = a * b * Tp.card + a * b * Tn.card := by ring
    _ ≤ (2 * X * D + a * b) + (2 * X * D + a * b) :=
      Nat.add_le_add hp' hn'
    _ = 4 * X * D + 2 * (a * b) := by ring

end Erdos489

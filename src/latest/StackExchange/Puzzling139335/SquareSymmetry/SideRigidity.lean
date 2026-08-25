import StackExchange.Puzzling139335.SquareSymmetry.Basic
import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity.Normalized

/-!
# Congruences matching square-side endpoints

If a congruence matches a side's two endpoints to another side's endpoints,
and takes a set with nonempty interior from the square into the square,
then it preserves the whole square. The source set need not contain the
endpoints: fitting any of its interior points already determines the inward
choice of side. In particular, the result applies to the dissection pieces.
-/

open Set

namespace Puzzling139335.SquareSymmetry

noncomputable section

/-- Normalizing a corner takes either adjacent corner to a positive unit
coordinate vector. -/
theorem cornerFlip_adjacent (a a' : Fin 4)
    (ha : a' = a + 1 ∨ a' = a + 3) :
    cornerFlip a (corner a') = corner 1 ∨ cornerFlip a (corner a') = corner 3 := by
  rcases ha with rfl | rfl <;> fin_cases a <;>
    norm_num [cornerFlipPoint, corner, Fin.ext_iff, Fin.val_add]

/-- Two ordered adjacent-corner images determine a square symmetry, once
a set with nonempty interior is known to fit on both sides. -/
theorem side_rigidity_of_adjacent_images (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a a' b b' : Fin 4) (ha : a' = a + 1 ∨ a' = a + 3)
    (hb : b' = b + 1 ∨ b' = b + 3)
    (hfirst : e (corner a) = corner b) (hsecond : e (corner a') = corner b')
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e '' unitSquare = unitSquare := by
  let g : Plane ≃ᵃⁱ[ℝ] Plane := ((cornerFlip a).trans e).trans (cornerFlip b)
  have hg (p : Plane) : g p = cornerFlip b (e (cornerFlip a p)) := rfl
  have hgzero : g 0 = 0 := by
    rw [hg, cornerFlip_zero, hfirst, cornerFlip_corner]
  have hgadj : g (cornerFlip a (corner a')) = cornerFlip b (corner b') := by
    rw [hg, cornerFlip_involutive, hsecond]
  have hgside : g (corner 1) = corner 1 ∨ g (corner 1) = corner 3 ∨
      g (corner 3) = corner 1 ∨ g (corner 3) = corner 3 := by
    rcases cornerFlip_adjacent a a' ha with h₀ | h₀ <;>
      rcases cornerFlip_adjacent b b' hb with h₁ | h₁
    · exact Or.inl (by simpa only [h₀, h₁] using hgadj)
    · exact Or.inr (Or.inl (by simpa only [h₀, h₁] using hgadj))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [h₀, h₁] using hgadj)))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [h₀, h₁] using hgadj)))
  have hsource : cornerFlip a '' P ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    exact (cornerFlip_mem_unitSquare a).mpr (hP hp)
  have htarget : g '' (cornerFlip a '' P) ⊆ unitSquare := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [hg, cornerFlip_involutive]
    exact (cornerFlip_mem_unitSquare b).mpr (heP (mem_image_of_mem e hp))
  have hsourceInt : (interior (cornerFlip a '' P)).Nonempty := by
    obtain ⟨p, hp⟩ := hint
    refine ⟨cornerFlip a p, ?_⟩
    exact (mem_interior_image_affineIsometry (cornerFlip a)).mpr hp
  have hgSquare := normalized_side_rigidity g hgzero hgside hsource htarget hsourceInt
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hmem : g (cornerFlip a p) ∈ unitSquare := by
      rw [← hgSquare]
      exact mem_image_of_mem g ((cornerFlip_mem_unitSquare a).mpr hp)
    rw [hg, cornerFlip_involutive] at hmem
    exact (cornerFlip_mem_unitSquare b).mp hmem
  · intro p hp
    have hmem : cornerFlip b p ∈ g '' unitSquare := by
      rw [hgSquare]
      exact (cornerFlip_mem_unitSquare b).mpr hp
    obtain ⟨q, hq, heq⟩ := hmem
    refine ⟨cornerFlip a q, (cornerFlip_mem_unitSquare a).mpr hq, ?_⟩
    exact (cornerFlip b).injective heq

/-- Ordered endpoint formulation for counterclockwise square sides. -/
theorem side_rigidity_ordered (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hfirst : e (corner a) = corner b)
    (hsecond : e (corner (a + 1)) = corner (b + 1))
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e '' unitSquare = unitSquare :=
  side_rigidity_of_adjacent_images e a (a + 1) b (b + 1)
    (Or.inl rfl) (Or.inl rfl) hfirst hsecond hP heP hint

/-- Endpoint formulation allowing the order on the target side to reverse. -/
theorem side_rigidity_either_order (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hends : (e (corner a) = corner b ∧ e (corner (a + 1)) = corner (b + 1)) ∨
      (e (corner a) = corner (b + 1) ∧ e (corner (a + 1)) = corner b))
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e '' unitSquare = unitSquare := by
  rcases hends with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact side_rigidity_ordered e a b hfirst hsecond hP heP hint
  · apply side_rigidity_of_adjacent_images e a (a + 1) (b + 1) b
      (Or.inl rfl) (Or.inr ?_) hfirst hsecond hP heP hint
    fin_cases b <;> rfl

theorem corner_ne_successor (a : Fin 4) : corner a ≠ corner (a + 1) := by
  intro h
  have hdist : dist (corner a) (corner (a + 1)) ^ 2 = 1 := by
    fin_cases a <;> norm_num [plane_dist_sq, corner, Fin.ext_iff, Fin.val_add]
  rw [h, dist_self] at hdist
  norm_num at hdist

/-- An unordered endpoint-image equality has one of the two possible orders. -/
theorem side_endpoints_either_order (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hends : e '' {corner a, corner (a + 1)} = {corner b, corner (b + 1)}) :
    (e (corner a) = corner b ∧ e (corner (a + 1)) = corner (b + 1)) ∨
      (e (corner a) = corner (b + 1) ∧ e (corner (a + 1)) = corner b) := by
  have hfirst : e (corner a) = corner b ∨ e (corner a) = corner (b + 1) := by
    have hmem : e (corner a) ∈ e '' {corner a, corner (a + 1)} :=
      mem_image_of_mem e (by simp)
    rw [hends] at hmem
    simpa only [mem_insert_iff, mem_singleton_iff] using hmem
  have hsecond : e (corner (a + 1)) = corner b ∨
      e (corner (a + 1)) = corner (b + 1) := by
    have hmem : e (corner (a + 1)) ∈ e '' {corner a, corner (a + 1)} :=
      mem_image_of_mem e (by simp)
    rw [hends] at hmem
    simpa only [mem_insert_iff, mem_singleton_iff] using hmem
  have hne : e (corner a) ≠ e (corner (a + 1)) :=
    fun heq => corner_ne_successor a (e.injective heq)
  rcases hfirst with h₀ | h₀ <;> rcases hsecond with h₁ | h₁
  · exact (hne (h₀.trans h₁.symm)).elim
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact (hne (h₀.trans h₁.symm)).elim

/-- Unordered side endpoints force an actual symmetry of the square. -/
theorem side_rigidity_unordered (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hends : e '' {corner a, corner (a + 1)} = {corner b, corner (b + 1)})
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e '' unitSquare = unitSquare :=
  side_rigidity_either_order e a b (side_endpoints_either_order e a b hends) hP heP hint

/-- Every such side-endpoint congruence fixes the square's center. -/
theorem center_fixed_of_side_endpoints (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hends : e '' {corner a, corner (a + 1)} = {corner b, corner (b + 1)})
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e squareCenter = squareCenter :=
  center_fixed_of_preserves_square e (side_rigidity_unordered e a b hends hP heP hint)

end

end Puzzling139335.SquareSymmetry

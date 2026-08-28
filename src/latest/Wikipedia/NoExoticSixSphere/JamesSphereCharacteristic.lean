import Wikipedia.NoExoticSixSphere.JamesSphereSeparation
import Wikipedia.NoExoticSixSphere.JamesWordStrata
import Wikipedia.NoExoticSixSphere.JamesCellCubeCoordinates

/-!
# Actual characteristic maps for the James sphere cells

Each block of `n` cube coordinates maps to the standard `n`-sphere. The
resulting ordered word is the characteristic map of the length-`k` cell.
Its open disk is injective and consists precisely of words of length `k`;
its boundary has strictly smaller word length. For positive `n`, its
closed disk maps onto the entire `k`th James stage.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.Cell

open JamesCellCube

def array (n k : ℕ) : C((Fin (k * n) → ℝ), Fin k → Sphere n) :=
  ⟨fun x i ↦ SmoothCube.quotient n (block n k (cube (k * n) x) i),
    continuous_pi (fun i ↦ (SmoothCube.quotient n).continuous.comp
      (continuous_pi (fun j ↦ continuous_interval.comp
        (continuous_apply (finProdFinEquiv (i, j))))))⟩

def characteristic (n k : ℕ) : C((Fin (k * n) → ℝ), James.Space (Sphere n) (spherePole n)) :=
  ⟨fun x ↦ James.word (spherePole n) (List.ofFn (array n k x)),
    (James.continuous_word_array (spherePole n) k).comp (array n k).continuous⟩

theorem characteristic_mem_stage (n k : ℕ) (x : Fin (k * n) → ℝ) :
    characteristic n k x ∈ James.stage (spherePole n) k := by
  rw [← James.range_word_array]
  exact mem_range_self (array n k x)

theorem size_characteristic_eq_iff (n k : ℕ) (x : Fin (k * n) → ℝ) :
    James.size (spherePole n) (characteristic n k x) = k ↔ x ∈ ball 0 1 := by
  change James.size (spherePole n) (James.word (spherePole n)
    (List.ofFn (array n k x))) = k ↔ _
  rw [James.size_word_array_eq_iff]
  change (∀ i, SmoothCube.quotient n (block n k (cube (k * n) x) i) ≠ spherePole n) ↔ _
  simp only [ne_eq, SmoothCube.quotient_eq_pole_iff]
  rw [block_not_boundary_iff, cube_not_boundary_iff]

theorem image_closedBall (n k : ℕ) (hn : 0 < n) :
    characteristic n k '' closedBall 0 1 = James.stage (spherePole n) k := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, _, rfl⟩
    exact characteristic_mem_stage n k x
  · intro w hw
    obtain ⟨v, hv⟩ := James.exists_array_of_mem_stage (spherePole n) hw
    choose u hu using (fun i : Fin k ↦ SmoothCube.quotient_surjective hn (v i))
    let x := unscale (k * n) (pack n k u)
    have ha : array n k x = v := by
      funext i
      change SmoothCube.quotient n
        (block n k (cube (k * n) (unscale (k * n) (pack n k u))) i) = v i
      rw [cube_unscale, block_pack]
      exact hu i
    refine ⟨x, unscale_mem_closedBall (k * n) (pack n k u), ?_⟩
    change James.word (spherePole n) (List.ofFn (array n k x)) = w
    rw [ha, hv]

theorem image_ball (n k : ℕ) (hn : 0 < n) :
    characteristic n k '' ball 0 1 = {w | James.size (spherePole n) w = k} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (size_characteristic_eq_iff n k x).mpr hx
  · intro w hw
    have hs : w ∈ James.stage (spherePole n) k := le_of_eq hw
    rw [← image_closedBall n k hn] at hs
    obtain ⟨x, _, rfl⟩ := hs
    exact ⟨x, (size_characteristic_eq_iff n k x).mp hw, rfl⟩

theorem injOn_ball (n k : ℕ) : Set.InjOn (characteristic n k) (ball 0 1) := by
  intro x hx y hy h
  have hax : ∀ i, array n k x i ≠ spherePole n :=
    (James.size_word_array_eq_iff (spherePole n) k _).mp
      ((size_characteristic_eq_iff n k x).mpr hx)
  have hay : ∀ i, array n k y i ≠ spherePole n :=
    (James.size_word_array_eq_iff (spherePole n) k _).mp
      ((size_characteristic_eq_iff n k y).mpr hy)
  have ha : array n k x = array n k y :=
    James.word_array_injective_of_forall_ne (spherePole n) hax hay h
  apply cube_injOn_closedBall (k * n) (ball_subset_closedBall hx) (ball_subset_closedBall hy)
  funext l
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
  have he := congrFun ha i
  change SmoothCube.quotient n (block n k (cube (k * n) x) i) =
    SmoothCube.quotient n (block n k (cube (k * n) y) i) at he
  rcases (SmoothCube.quotient_eq_iff n _ _).mp he with hb | hb
  · exact congrFun hb j
  · exact False.elim (hax i (SmoothCube.quotient_boundary n _ hb.1))

theorem boundary_size_lt (n k : ℕ) {x : Fin (k * n) → ℝ} (hx : x ∈ sphere 0 1) :
    James.size (spherePole n) (characteristic n k x) < k := by
  have hnot : x ∉ ball 0 1 := by
    simp only [mem_ball, mem_sphere.mp hx, lt_self_iff_false, not_false_eq_true]
  have hle : James.size (spherePole n) (characteristic n k x) ≤ k :=
    characteristic_mem_stage n k x
  have hne : James.size (spherePole n) (characteristic n k x) ≠ k :=
    fun h ↦ hnot ((size_characteristic_eq_iff n k x).mp h)
  omega

end NoExoticSixSphere.JamesSphere.Cell

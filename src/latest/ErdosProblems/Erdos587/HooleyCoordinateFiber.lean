import ErdosProblems.Erdos587.HooleyCoordinateCover
import ErdosProblems.Erdos587.HooleyCoordinateCoverFiber
import ErdosProblems.Erdos587.GreedyDensity

/-! # Small distinct-element blocks with dense fibers in coefficient boxes -/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

lemma delta_subsetSum_coordinate_bound {d : ℕ} (A : Finset (Fin d → ℤ))
    (L : Fin d → ℕ) (hA : ∀ a ∈ A, ∀ i, |a i| ≤ (L i : ℤ))
    (n : ℕ) (hcard : A.card ≤ n) :
    ∀ z ∈ A.subsetSum, ∀ i, |z i| ≤ (n : ℤ) * L i := by
  intro z hz i
  obtain ⟨S, hSA, rfl⟩ := Finset.mem_subsetSum_iff.mp hz
  rw [Finset.sum_apply]
  calc
    _ ≤ ∑ a ∈ S, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ S, (L i : ℤ) := Finset.sum_le_sum (fun a ha => hA a (hSA ha) i)
    _ = (S.card : ℤ) * L i := by simp
    _ ≤ (n : ℤ) * L i := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_card hSA).trans hcard) (by positivity)

lemma delta_symmetric_coordinate_cover {d : ℕ} (A : Finset (Fin d → ℤ))
    (L : Fin d → ℕ) (c : ℕ) (hc : 0 < c)
    (hA : ∀ x ∈ A, ∀ i, |x i| ≤ (c : ℤ) * L i) :
    ∃ F : Finset (Fin d → ℤ), F.card ≤ c ^ d ∧
      A ⊆ F + nvCoordBox (fun i => 2 * L i) := by
  classical
  obtain ⟨F, hFcard, hcover⟩ := delta_coordBox_dilate_cover (fun i => 2 * L i) c hc
  let center : Fin d → ℤ := fun i => (c : ℤ) * L i
  refine ⟨F.image (fun f => f - center), Finset.card_image_le.trans hFcard, ?_⟩
  intro x hx
  have hxp : x + center ∈ nvCoordBox (fun i => c * (2 * L i)) := by
    apply mem_nvCoordBox_iff.mpr
    intro i
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hA x hx i)
    change 0 ≤ x i + (c : ℤ) * L i ∧ x i + (c : ℤ) * L i ≤ (c * (2 * L i) : ℕ)
    push_cast
    constructor <;> nlinarith
  obtain ⟨f, hf, y, hy, heq⟩ := Finset.mem_add.mp (hcover hxp)
  refine Finset.mem_add.mpr ⟨f - center, Finset.mem_image.mpr ⟨f, hf, rfl⟩, y, hy, ?_⟩
  calc
    (f - center) + y = (f + y) - center := by abel
    _ = x := by rw [heq]; abel

theorem delta_exists_greedy_coordinate_fiber {d : ℕ} (A : Finset (Fin d → ℤ))
    (L : Fin d → ℕ) (hA : ∀ a ∈ A, ∀ i, |a i| ≤ (L i : ℤ))
    (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hbudget : (2 * h) * (Nat.log 2 (nvCoordBox (fun i => 2 * (h * L i))).card + 1) ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (nvCoordBox (fun i => 2 * (h * L i))).card < M * (h • insert 0 D).card) :
    let T := (nvCoordBox (fun i => 2 * (h * L i))).card
    let c := 2 * (Nat.log 2 T + 1)
    ∃ S ⊆ A, S.card ≤ c * h ∧ ∃ z : Fin d → ℤ, ∃ X : Finset (Fin d → ℤ),
      X ⊆ nvCoordBox (fun i => 2 * (h * L i)) ∧ ({z} : Finset (Fin d → ℤ)) + X ⊆ S.subsetSum ∧
        T < (M * c ^ d) * X.card := by
  classical
  let T := (nvCoordBox (fun i => 2 * (h * L i))).card
  let c := 2 * (Nat.log 2 T + 1)
  obtain ⟨S, hSA, hScard, hSsize⟩ :=
    exists_small_subset_with_dense_subsetSums A h M T r hh hM hbudget hdense
  have hScard' : S.card ≤ c * h := by
    have heq : (2 * h) * (Nat.log 2 T + 1) = c * h := by dsimp [c]; ring
    simpa only [heq] using hScard
  have hbounds : ∀ z ∈ S.subsetSum, ∀ i, |z i| ≤ (c : ℤ) * (h * L i : ℕ) := by
    intro z hz i
    have hh := delta_subsetSum_coordinate_bound S L (fun a ha => hA a (hSA ha))
      (c * h) hScard' z hz i
    simpa only [Nat.cast_mul, mul_assoc] using hh
  obtain ⟨F, hFcard, hcover⟩ := delta_symmetric_coordinate_cover S.subsetSum
    (fun i => h * L i) c (by dsimp [c]; positivity) hbounds
  obtain ⟨z, _, X, hX, hcount, hsub⟩ := delta_exists_dense_cover_fiber S.subsetSum
    (nvCoordBox (fun i => 2 * (h * L i))) F S.subsetSum_nonempty hcover hFcard
  refine ⟨S, hSA, hScard', z, X, hX, hsub, ?_⟩
  exact hSsize.trans_le (by simpa only [mul_assoc] using Nat.mul_le_mul_left M hcount)

end Erdos587.CFP

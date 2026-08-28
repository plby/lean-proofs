import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry
import Mathlib.Data.Set.Card

/-!
# Positive barycentric support and injective simplex maps

Geometric simplex maps sum coordinates over fibres. Positivity therefore
detects the image of the positive support, and an injective simplex map
remembers all coordinates. These are facts about the actual barycentric
simplices, without any realization identifications.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.SimplexSupport

open FirstHurewicz

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_pos_iff (f : A → B) (t : stdSimplex ℝ A) (b : B) :
    0 < stdSimplex.map f t b ↔ ∃ a, f a = b ∧ 0 < t a := by
  classical
  change 0 < FunOnFinite.linearMap ℝ ℝ f t b ↔ _
  rw [FunOnFinite.linearMap_apply_apply,
    Finset.sum_pos_iff_of_nonneg (fun a _ ↦ stdSimplex.zero_le t a)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem map_positive (f : A → B) (hf : Function.Surjective f)
    (t : stdSimplex ℝ A) (ht : ∀ a, 0 < t a) :
    ∀ b, 0 < stdSimplex.map f t b := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact (map_pos_iff f t (f a)).mpr ⟨a, rfl, ht a⟩

theorem positive_support_map (f : A → B) (t : stdSimplex ℝ A)
    (ht : ∀ a, 0 < t a) :
    {b | 0 < stdSimplex.map f t b} = Set.range f := by
  ext b
  rw [Set.mem_ofPred_eq, map_pos_iff]
  constructor
  · rintro ⟨a, ha, _⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl, ht a⟩

theorem map_coordinate_injective (f : A → B) (hf : Function.Injective f)
    (t : stdSimplex ℝ A) (a : A) : stdSimplex.map f t (f a) = t a := by
  classical
  change FunOnFinite.linearMap ℝ ℝ f t (f a) = t a
  simp [FunOnFinite.linearMap_apply_apply, hf.eq_iff, Finset.sum_filter]

theorem map_injective (f : A → B) (hf : Function.Injective f) :
    Function.Injective (stdSimplex.map (S := ℝ) f) := by
  intro s t h
  apply Subtype.ext
  funext a
  change s a = t a
  have ha := congrArg (fun u : stdSimplex ℝ B ↦ u (f a)) h
  simpa only [map_coordinate_injective f hf] using ha

theorem mono_dim_eq_of_range_eq {m n d : ℕ}
    (f : ⦋m⦌ ⟶ ⦋d⦌) (g : ⦋n⦌ ⟶ ⦋d⦌) [Mono f] [Mono g]
    (h : Set.range f.toOrderHom = Set.range g.toOrderHom) : m = n := by
  have hf := SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f)
  have hg := SimplexCategory.mono_iff_injective.mp (inferInstance : Mono g)
  have hc := congrArg Set.ncard h
  rw [Set.ncard_range_of_injective hf, Set.ncard_range_of_injective hg] at hc
  simpa using hc

theorem mono_eq_of_range_eq {m n : ℕ}
    (f g : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] [Mono g]
    (h : Set.range f.toOrderHom = Set.range g.toOrderHom) : f = g := by
  have hf : StrictMono f.toOrderHom := f.toOrderHom.monotone.strictMono_of_injective
    (SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f))
  have hg : StrictMono g.toOrderHom := g.toOrderHom.monotone.strictMono_of_injective
    (SimplexCategory.mono_iff_injective.mp (inferInstance : Mono g))
  have he : (f.toOrderHom : Fin (m + 1) → Fin (n + 1)) = g.toOrderHom :=
    (hf.range_inj hg).mp h
  apply SimplexCategory.Hom.ext
  exact DFunLike.coe_injective he

end Wikipedia.HopfProblem.OrbitPair.SimplexSupport

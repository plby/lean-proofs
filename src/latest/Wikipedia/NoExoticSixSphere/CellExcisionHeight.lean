import Wikipedia.NoExoticSixSphere.CellExcisionGraph
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Order.Compact

/-!
# Choosing the separating graph from actual compact fibers

Compactness bounds the lower fiber's time coordinates strictly below
one. Urysohn separation gives a height equal to that bound on its
projection and zero on the protected parameters and other fiber.
The graph deformation then removes the lower fiber while preserving
the required top, side, and moving-bottom conditions.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.CellExcisionGraph

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

theorem exists_upper_height (Q : Set (I × P)) (hQ : IsCompact Q)
    (htop : ∀ z ∈ Q, z.1 < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ Q, (z.1 : ℝ) < r := by
  by_cases hne : Q.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hQ.exists_isMaxOn hne
      (continuous_subtype_val.comp continuous_fst).continuousOn
    refine ⟨((z.1 : ℝ) + 1) / 2, ?_, ?_, ?_⟩
    · linarith [z.1.property.1]
    · have ht : (z.1 : ℝ) < 1 := htop z hz
      linarith
    · intro w hw
      have ht : (z.1 : ℝ) < 1 := htop z hz
      have hm : (w.1 : ℝ) ≤ z.1 := hmax hw
      linarith
  · exact ⟨1 / 2, by norm_num, by norm_num, fun z hz ↦ (hne ⟨z, hz⟩).elim⟩

theorem exists_height [T2Space P] [NormalSpace P]
    (Q : Set (I × P)) (hQ : IsCompact Q) (B : Set P) (hB : IsClosed B)
    (hdisj : Disjoint (Prod.snd '' Q) B) (htop : ∀ z ∈ Q, z.1 < 1) :
    ∃ φ : C(P, I), (∀ p ∈ B, φ p = 0) ∧ (∀ p, φ p < 1) ∧
      ∀ z ∈ Q, z.1 < φ z.2 := by
  obtain ⟨r, hr0, hr1, hrQ⟩ := exists_upper_height Q hQ htop
  obtain ⟨η, hη0, hη1, hη⟩ := exists_continuous_zero_one_of_isClosed hB
    (hQ.image continuous_snd).isClosed hdisj.symm
  have hb (p : P) : r * η p ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg hr0.le (hη p).1, ?_⟩
    exact (mul_le_mul_of_nonneg_left (hη p).2 hr0.le).trans (by simpa using hr1.le)
  let φ : C(P, I) := ⟨fun p ↦ ⟨r * η p, hb p⟩,
    (continuous_const.mul η.continuous).subtype_mk _⟩
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro p hp
    apply Subtype.ext
    change r * η p = 0
    rw [hη0 hp]
    exact mul_zero r
  · intro p
    change r * η p < 1
    exact (mul_le_mul_of_nonneg_left (hη p).2 hr0.le).trans_lt
      (by simpa using hr1)
  · intro z hz
    change (z.1 : ℝ) < r * η z.2
    have he : η z.2 = 1 := hη1 ⟨z, hz, rfl⟩
    rw [he, mul_one]
    exact hrQ z hz

theorem exists_separating_height [T2Space P] [NormalSpace P]
    (Q L : Set (I × P)) (hQ : IsCompact Q) (hL : IsCompact L)
    (S : Set P) (hS : IsClosed S)
    (hQL : Disjoint (Prod.snd '' Q) (Prod.snd '' L))
    (hQS : Disjoint (Prod.snd '' Q) S) (htop : ∀ z ∈ Q, z.1 < 1) :
    ∃ φ : C(P, I), (∀ p ∈ S, φ p = 0) ∧ (∀ z ∈ L, φ z.2 = 0) ∧
      (∀ p, φ p < 1) ∧ ∀ z ∈ Q, z.1 < φ z.2 := by
  have hd : Disjoint (Prod.snd '' Q) ((Prod.snd '' L) ∪ S) := by
    apply Set.disjoint_left.mpr
    intro p hp h
    rcases h with h | h
    · exact Set.disjoint_left.mp hQL hp h
    · exact Set.disjoint_left.mp hQS hp h
  obtain ⟨φ, hφ, hφ1, hφQ⟩ := exists_height Q hQ ((Prod.snd '' L) ∪ S)
    ((hL.image continuous_snd).isClosed.union hS) hd htop
  exact ⟨φ, fun p hp ↦ hφ p (Or.inr hp),
    fun z hz ↦ hφ z.2 (Or.inl ⟨z, hz, rfl⟩), hφ1, hφQ⟩

theorem exists_homotopy_avoiding [T2Space P] [NormalSpace P]
    (f : C(I × P, X)) (A B : Set X)
    (hA : IsCompact (f ⁻¹' A)) (hB : IsCompact (f ⁻¹' B))
    (S : Set P) (hS : IsClosed S)
    (hBA : Disjoint (Prod.snd '' (f ⁻¹' B)) (Prod.snd '' (f ⁻¹' A)))
    (hBS : Disjoint (Prod.snd '' (f ⁻¹' B)) S)
    (htop : ∀ z, f z ∈ B → z.1 < 1) (hbottom : ∀ p, f (0, p) ∉ A) :
    ∃ g : C(I × P, X), ∃ H : f.Homotopy g,
      (∀ s p, H (s, (1, p)) = f (1, p)) ∧
      (∀ s t p, p ∈ S → H (s, (t, p)) = f (t, p)) ∧
      (∀ s p, H (s, (0, p)) ∉ A) ∧ ∀ z, g z ∉ B := by
  obtain ⟨φ, hφS, hφA, _, hφB⟩ := exists_separating_height (f ⁻¹' B) (f ⁻¹' A)
    hB hA S hS hBA hBS htop
  exact ⟨f.comp (endpoint φ), homotopy f φ, homotopy_top f φ,
    fun s t p hp ↦ homotopy_fixed f φ s (t, p) (hφS p hp),
    moving_bottom_avoids φ (f ⁻¹' A) hφA hbottom,
    endpoint_avoids φ (f ⁻¹' B) hφB⟩

end NoExoticSixSphere.CellExcisionGraph

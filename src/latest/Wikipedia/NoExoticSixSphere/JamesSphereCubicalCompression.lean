import Wikipedia.NoExoticSixSphere.JamesSphereRelativeCompression

/-!
# Compression of actual cubical maps in the James cone pair

The selected open-cell coordinates give genuine interior disk points.
Point excision, the supported bottom correction, and the two puncture
deformations now combine into a homotopy into the original second
James stage. The bottom ends in its actual lower subspace. The top and
specified parameter faces remain in the James stage; their points in
the common subspace stay fixed.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

open CubicalCellSmoothing

theorem exists_firstChart_point (n : ℕ) (hn : 0 < n) (u : Fin (2 * n) → ℝ) :
    ∃ p : PuncturedStage.Coordinates n 1, ∃ hp : ‖p‖ < 1,
      (firstChart n hn u).val = firstCell n (PuncturedCellAttachment.point p hp) := by
  let p : PuncturedStage.Coordinates n 1 := (Homeomorph.unitBall u).val
  have hp : ‖p‖ < 1 := mem_ball_zero_iff.mp (Homeomorph.unitBall u).property
  exact ⟨p, hp, rfl⟩

theorem exists_secondChart_point (n : ℕ) (v : Fin (n + 1) → ℝ) :
    ∃ q : ConeCoordinates n, ∃ hq : ‖q‖ < 1,
      (secondChart n v).val = cone n (PuncturedCellAttachment.point q hq) := by
  let w : ConeCoordinates n := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm v
  let q : ConeCoordinates n := (Homeomorph.unitBall w).val
  have hq : ‖q‖ < 1 := mem_ball_zero_iff.mp (Homeomorph.unitBall w).property
  exact ⟨q, hq, rfl⟩

theorem exists_cubical_compression (n d : ℕ) (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 2)
    (f : C(I × Parameters d, Space n)) (S : Set (Parameters d)) (hS : IsClosed S)
    (hside : ∀ t p, p ∈ S → f (t, p) ∈ Set.range (base n))
    (htop : ∀ p, f (1, p) ∈ Set.range (base n))
    (hbottom : ∀ p, f (0, p) ∈ Set.range (cone n)) :
    ∃ a : C(I × Parameters d, SecondStage.Space n),
      ∃ F : f.Homotopy ((base n).comp a),
        (∀ p, a (0, p) ∈ StageAttachment.lower n 1) ∧
        (∀ s p, F (s, (0, p)) ∈ Set.range (cone n)) ∧
        (∀ s p, F (s, (1, p)) ∈ Set.range (base n)) ∧
        (∀ s t p, p ∈ S → F (s, (t, p)) ∈ Set.range (base n)) ∧
        ∀ s z, f z ∈ Set.range (base n) → f z ∈ Set.range (cone n) →
          (z.1 = 1 ∨ z.2 ∈ S) → F (s, z) = f z := by
  have hn0 : 0 < n := by omega
  obtain ⟨f₁, L, hfix, hLA, hLC, u, v, _, _, g, H, htopH, hsideH, hbottomH, hg⟩ :=
    exists_point_excision n d hn hdn f S hS hside htop hbottom
  obtain ⟨p, hp, hfirst⟩ := exists_firstChart_point n hn0 u
  obtain ⟨q, hq, hsecond⟩ := exists_secondChart_point n v
  let K : Set (I × Parameters d) := Prod.fst ⁻¹' {0}
  have hK : IsClosed K := isClosed_singleton.preimage continuous_fst
  have hfK : ∀ x ∈ K, f₁ x ∈ Set.range (cone n) := by
    rintro ⟨t, z⟩ ht
    have ht0 : t = 0 := ht
    subst t
    have he := (hLC 1 (0, z)).mpr (hbottom z)
    rwa [L.apply_one] at he
  have hHK : ∀ s x, x ∈ K →
      H (s, x) ≠ firstCell n (PuncturedCellAttachment.point p hp) := by
    rintro s ⟨t, z⟩ ht
    have ht0 : t = 0 := ht
    subst t
    rw [← hfirst]
    exact hbottomH s z
  have hg' : ∀ x, g x ≠ cone n (PuncturedCellAttachment.point q hq) := by
    intro x
    rw [← hsecond]
    exact hg x
  obtain ⟨a, R, haK, hRK, hRA, hRfix⟩ :=
    exists_compression_of_avoidance n hn0 p hp q hq f₁ g H K hK hfK hHK hg'
  have hprotected : ∀ z : I × Parameters d, z.1 = 1 ∨ z.2 ∈ S →
      ∀ s, H (s, z) = f₁ z := by
    rintro ⟨t, z⟩ (ht | hz) s
    · change t = 1 at ht
      subst t
      exact htopH s z
    · exact hsideH s t z hz
  have hprotectedA : ∀ z : I × Parameters d, z.1 = 1 ∨ z.2 ∈ S →
      f z ∈ Set.range (base n) := by
    rintro ⟨t, z⟩ (ht | hz)
    · change t = 1 at ht
      subst t
      exact htop z
    · exact hside t z hz
  have hRA' : ∀ z : I × Parameters d, z.1 = 1 ∨ z.2 ∈ S →
      ∀ s, R (s, z) ∈ Set.range (base n) := by
    intro z hz
    apply hRA z
    intro s
    rw [hprotected z hz s]
    have he := (hLA 1 z).mpr (hprotectedA z hz)
    rwa [L.apply_one] at he
  refine ⟨a, L.trans R, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun z ↦ haK (0, z) rfl
  · intro s z
    apply trans_pointwise_property L R (0, z) (fun y ↦ y ∈ Set.range (cone n)) ?_ ?_ s
    · exact fun t ↦ (hLC t (0, z)).mpr (hbottom z)
    · exact fun t ↦ hRK t (0, z) rfl
  · intro s z
    apply trans_pointwise_property L R (1, z) (fun y ↦ y ∈ Set.range (base n)) ?_ ?_ s
    · exact fun t ↦ (hLA t (1, z)).mpr (htop z)
    · exact hRA' (1, z) (Or.inl rfl)
  · intro s t z hz
    apply trans_pointwise_property L R (t, z) (fun y ↦ y ∈ Set.range (base n)) ?_ ?_ s
    · exact fun r ↦ (hLA r (t, z)).mpr (hside t z hz)
    · exact hRA' (t, z) (Or.inr hz)
  · intro s z hzA hzC hz
    have he : f₁ z = f z := by
      have hf := hfix 1 z hzA hzC
      rwa [L.apply_one] at hf
    apply trans_pointwise_property L R z (fun y ↦ y = f z) ?_ ?_ s
    · exact fun t ↦ hfix t z hzA hzC
    · intro t
      exact (hRfix z (he ▸ hzA) (he ▸ hzC) (hprotected z hz) t).trans he

end NoExoticSixSphere.JamesSphere.SecondStageCone

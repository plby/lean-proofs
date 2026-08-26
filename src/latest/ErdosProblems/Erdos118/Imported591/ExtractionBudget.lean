import ErdosProblems.Erdos118.Imported591.ExactLargeLevels

open Set Ordinal

namespace Erdos118.Negative.Exact.Levels

/-! Concrete ordinal bounds for the finite-depth extraction argument. -/

noncomputable def continuationBound (r : ℕ) : Ordinal.{0} :=
  ω ^ (ω * (r : Ordinal.{0}))

noncomputable def extractionExponent (r d k : ℕ) : Ordinal.{0} :=
  ω * ((r + 1 : ℕ) : Ordinal.{0}) + (((d + 1) * k : ℕ) : Ordinal.{0})

noncomputable def extractionBound (r d k : ℕ) : Ordinal.{0} :=
  ω ^ extractionExponent r d k

theorem omega_mul_nat_add_one (r : ℕ) :
    (ω : Ordinal.{0}) * ((r + 1 : ℕ) : Ordinal.{0}) = ω * r + ω := by
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]

theorem extractionExponent_lt (r d k : ℕ) :
    extractionExponent r d k < ω * ((r + 2 : ℕ) : Ordinal.{0}) := by
  have hstep : (ω : Ordinal.{0}) * ((r + 2 : ℕ) : Ordinal.{0}) =
      ω * ((r + 1 : ℕ) : Ordinal.{0}) + ω := by
    exact omega_mul_nat_add_one (r + 1)
  rw [hstep]
  exact (add_lt_add_iff_left _).2 (Ordinal.natCast_lt_omega0 ((d + 1) * k))

theorem extractionBound_lt_target (r d k : ℕ) :
    extractionBound r d k < continuationBound (r + 2) := by
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
    (extractionExponent_lt r d k)

theorem extractionBound_zero_gt_one (r d : ℕ) :
    1 < extractionBound r d 0 := by
  change 1 < ω ^ (ω * ((r + 1 : ℕ) : Ordinal.{0}) +
    (((d + 1) * 0 : ℕ) : Ordinal.{0}))
  simp only [Nat.mul_zero, Nat.cast_zero, add_zero]
  apply Ordinal.one_lt_opow.mpr
  refine ⟨Ordinal.one_lt_omega0, ?_⟩
  exact mul_ne_zero Ordinal.omega0_ne_zero (by exact_mod_cast Nat.succ_ne_zero r)

theorem continuation_mul_theta_lt (r d k : ℕ) :
    continuationBound r * (ω ^ ω) < extractionBound r d (k + 1) := by
  change ω ^ (ω * (r : Ordinal.{0})) * ω ^ ω <
    ω ^ extractionExponent r d (k + 1)
  rw [← Ordinal.opow_add]
  apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
  rw [← omega_mul_nat_add_one]
  apply lt_add_of_pos_right
  exact_mod_cast Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos k)

theorem extractionBound_mul_delta_lt (r d k : ℕ) :
    extractionBound r d k * ω ^ (d : Ordinal.{0}) <
      extractionBound r d (k + 1) := by
  change ω ^ extractionExponent r d k * ω ^ (d : Ordinal.{0}) <
    ω ^ extractionExponent r d (k + 1)
  rw [← Ordinal.opow_add]
  apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
  simp only [extractionExponent, add_assoc]
  apply (add_lt_add_iff_left _).2
  rw [← Nat.cast_add]
  exact_mod_cast (show (d + 1) * k + d < (d + 1) * (k + 1) by
    rw [Nat.mul_succ]
    omega)

theorem extractionBound_finitelyIndivisible (r d k : ℕ) :
    Erdos118.Schipperus.K4Core.FinitelyIndivisible
      (extractionBound r d k).ToType := by
  apply Erdos118.Schipperus.PieceIndiv.omegaPower_finitelyIndivisible_of_le
    Erdos590.erdos_590 (extractionExponent r d k) (r + 2)
  · exact Ordinal.type_toType _
  · exact (extractionExponent_lt r d k).le

/-- A large fixed-root set has some level with many children retaining
the smaller continuation bound. -/
theorem exists_largeChildren
    (W : Set G) {m : ℕ} (hroot : ∀ x ∈ W, x.1.length = m)
    (r d : ℕ) (hW : continuationBound (r + 2) ≤ typeLT W) :
    ∃ p : List (List ℕ),
      ω ^ (d : Ordinal.{0}) < typeLT (LargeChildren W p (continuationBound r)) := by
  by_contra h
  push Not at h
  have hbound := type_fiber_lt_of_largeChildren_small W hroot
    (continuationBound r) (ω ^ (d : Ordinal.{0})) (extractionBound r d)
    (extractionBound_zero_gt_one r d)
    (continuation_mul_theta_lt r d)
    (extractionBound_mul_delta_lt r d)
    (fun k ↦ extractionBound_finitelyIndivisible r d (k + 1)) h m [] (by simp)
  have hWsmall : typeLT W < extractionBound r d m := by
    have hnil : Fiber W [] = W := by
      ext x
      constructor
      · exact fun hx ↦ hx.1
      · exact fun hx ↦ ⟨hx, List.nil_prefix⟩
    rwa [hnil] at hbound
  exact (not_lt_of_ge hW) (hWsmall.trans (extractionBound_lt_target r d m))

theorem continuationBound_pos (r : ℕ) : 0 < continuationBound r :=
  Ordinal.opow_pos _ Ordinal.omega0_pos

theorem largeChildren_subset_level (W : Set G) (p : List (List ℕ))
    (gamma : Ordinal.{0}) (hgamma : 0 < gamma) :
    LargeChildren W p gamma ⊆ Level W p := by
  intro a ha
  have hpos : 0 < typeLT (Child W p a) := hgamma.trans_le ha
  have hn : Nonempty (Child W p a) :=
    Ordinal.type_ne_zero_iff_nonempty.mp (ne_of_gt hpos)
  rcases hn with ⟨x⟩
  exact ⟨x.1, x.2⟩

/-- The extraction lemma used in the density proof: from two additional
`omega^omega` factors, retain a level above any prescribed finite omega
power and the required continuation in every selected child. -/
theorem exists_large_level_with_slack
    (W : Set G) {m : ℕ} (hroot : ∀ x ∈ W, x.1.length = m)
    (r d : ℕ) (hW : continuationBound (r + 2) ≤ typeLT W) :
    ∃ (U : Set G) (p : List (List ℕ)),
      U ⊆ W ∧ Fiber U p = U ∧
      ω ^ (d : Ordinal.{0}) < typeLT (Level U p) ∧
      ∀ a ∈ Level U p, continuationBound r ≤ typeLT (Child U p a) := by
  obtain ⟨p, hp⟩ := exists_largeChildren W hroot r d hW
  let A := LargeChildren W p (continuationBound r)
  have hA : A ⊆ Level W p :=
    largeChildren_subset_level W p (continuationBound r) (continuationBound_pos r)
  refine ⟨Thin W p A, p, thin_subset W p A, thin_fiber W p A, ?_, ?_⟩
  · rw [level_thin W p A hA]
    exact hp
  · intro a ha
    have haA : a ∈ A := by rwa [level_thin W p A hA] at ha
    rw [child_thin_of_mem W p A haA]
    exact haA

end Erdos118.Negative.Exact.Levels

#print axioms Erdos118.Negative.Exact.Levels.exists_large_level_with_slack

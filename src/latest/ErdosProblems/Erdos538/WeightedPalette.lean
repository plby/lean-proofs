import ErdosProblems.Erdos538.PaletteRelabeling

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

noncomputable section
open Erdos538.IsotropicKernel

/-- A rainbow exact-`k` support, regarded as a child of the palette ground
set. -/
def rainbowChild
    (k m : ℕ) (hk : 0 < k) (c : ℕ → Fin m) (S : Finset ℕ)
    (h : RainbowSupport k c S) : UniformChildren m (k - 1) := by
  refine ⟨S.image c, ?_⟩
  have hinj : Set.InjOn c S := by
    exact Finset.nodup_map_iff_injOn.mp h.1
  rw [Finset.card_image_iff.mpr hinj, h.2]
  omega

/-- Selection predicate obtained from a uniform palette after a permutation of
its color labels. -/
def PaletteSelected
    (k m : ℕ) (hk : 0 < k) (c : ℕ → Fin m) (σ : Equiv.Perm (Fin m))
    (F : Finset (UniformChildren m (k - 1))) (S : Finset ℕ) : Prop :=
  ∃ h : RainbowSupport k c S, σ • rainbowChild k m hk c S h ∈ F

/-- A density-`1/(64k)` palette plus the half-rainbow coloring theorem retains
at least a `1/(128k)` share of every arbitrarily weighted exact support layer. -/
theorem exists_weighted_linear_palette
    (n k : ℕ) (hk : 2 ≤ k) (supports : Finset (Finset ℕ))
    (w : Finset ℕ → ℚ≥0)
    (hsub : ∀ s ∈ supports, s ⊆ Finset.range n)
    (hcard : ∀ s ∈ supports, s.card = k) :
    ∃ (c : ℕ → Fin (2 * k * k))
      (σ : Equiv.Perm (Fin (2 * k * k)))
      (F : Finset (UniformChildren (2 * k * k) (k - 1))),
      Nat.choose (2 * k * k) k ≤ 64 * k * F.card ∧
      (∀ T : Finset (Fin (2 * k * k)),
        ∀ hT : T.card = (k - 1) + 2,
        (Finset.univ.filter fun x : T =>
          parentFacet T hT x ∈ F).card ≤ 2) ∧
      (∑ s ∈ supports, w s) ≤
        (128 * k) • weightedSupportMass supports
          (PaletteSelected k (2 * k * k) (by omega) c σ F) w := by
  classical
  have hkpos : 0 < k := by omega
  obtain ⟨c, hc⟩ := exists_coloring_half_rainbow
    n k (by omega) supports w hsub hcard
  obtain ⟨p, F, hp, hpgt, hple, hdense, hcap⟩ :=
    exists_balanced_linear_density_capTwo_palette k hk
  let good := supports.filter (RainbowSupport k c)
  let C := good
  let weight : C → ℚ≥0 := fun S => w S.1
  let child : C → UniformChildren (2 * k * k) (k - 1) :=
    fun S => rainbowChild k (2 * k * k) hkpos c S.1
      (Finset.mem_filter.mp S.2).2
  let Sel : Equiv.Perm (Fin (2 * k * k)) → C → Prop :=
    fun σ S => σ • child S ∈ F
  have hcol : ∀ S : C,
      Fintype.card (Equiv.Perm (Fin (2 * k * k))) ≤
        (64 * k) * (Finset.univ.filter fun σ => Sel σ S).card := by
    intro S
    exact group_card_le_mul_good_smul (child S) F (64 * k) (by
      have hkpred : k - 1 + 1 = k := by omega
      simpa [Fintype.card_finset_len, hkpred] using hdense)
  obtain ⟨σ, hσ⟩ := exists_weighted_sample_many Sel weight (64 * k) hcol
  have hrainbow : (∑ S : C, weight S) =
      weightedSupportMass supports (RainbowSupport k c) w := by
    simpa [C, good, weight, weightedSupportMass] using
      (Finset.sum_attach good w)
  have hSel (S : C) : Sel σ S ↔
      PaletteSelected k (2 * k * k) hkpos c σ F S.1 := by
    let hr : RainbowSupport k c S.1 := (Finset.mem_filter.mp S.2).2
    constructor
    · intro hs
      exact ⟨hr, hs⟩
    · rintro ⟨hr', hs⟩
      have heq : hr' = hr := Subsingleton.elim _ _
      simpa [Sel, child, heq]
  have hselected :
      (∑ S ∈ Finset.univ.filter (Sel σ), weight S) =
        weightedSupportMass supports
          (PaletteSelected k (2 * k * k) hkpos c σ F) w := by
    simp only [weight, weightedSupportMass, Finset.sum_filter]
    calc
      (∑ S : C, if Sel σ S then w S.1 else 0) =
          ∑ S : C, if PaletteSelected k (2 * k * k) hkpos c σ F S.1
            then w S.1 else 0 := by
        apply Finset.sum_congr rfl
        intro S _
        by_cases hs : Sel σ S
        · have hp := (hSel S).mp hs
          simp [hs, hp]
        · have hp : ¬ PaletteSelected k (2 * k * k) hkpos c σ F S.1 :=
            fun hp => hs ((hSel S).mpr hp)
          simp [hs, hp]
      _ = ∑ S ∈ good, if PaletteSelected k (2 * k * k) hkpos c σ F S
            then w S else 0 := by
        simpa [C] using (Finset.sum_attach good (fun S =>
          if PaletteSelected k (2 * k * k) hkpos c σ F S then w S else 0))
      _ = ∑ S ∈ supports, if PaletteSelected k (2 * k * k) hkpos c σ F S
            then w S else 0 := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro S hSupp hnotgood
        have hnrain : ¬ RainbowSupport k c S := by
          intro hr
          exact hnotgood (Finset.mem_filter.mpr ⟨hSupp, hr⟩)
        have hnPal : ¬ PaletteSelected k (2 * k * k) hkpos c σ F S := by
          rintro ⟨hr, -⟩
          exact hnrain hr
        simp [hnPal]
  have hmassRainbow : weightedSupportMass supports (RainbowSupport k c) w =
      weightedSupportMass supports
        (fun s => (s.1.map c).Nodup) w := by
    unfold weightedSupportMass
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    simp [RainbowSupport, hcard S hS]
  refine ⟨c, σ, F, hdense, hcap, ?_⟩
  rw [hrainbow, hselected] at hσ
  calc
    (∑ s ∈ supports, w s) ≤
        2 • weightedSupportMass supports (RainbowSupport k c) w := by
      rw [hmassRainbow]
      exact hc
    _ ≤ 2 • ((64 * k) • weightedSupportMass supports
          (PaletteSelected k (2 * k * k) hkpos c σ F) w) :=
      nsmul_le_nsmul_right hσ 2
    _ = (128 * k) • weightedSupportMass supports
          (PaletteSelected k (2 * k * k) hkpos c σ F) w := by
      simp [nsmul_eq_mul]
      ring

end

end Erdos538

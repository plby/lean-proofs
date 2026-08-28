import Wikipedia.SmoothSixDPoincare.AmbientRegularLevelTransport
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Smooth ambient transport across an entire critical-point-free band

Nearby exact collar translations carry both levels and whole sublevels.
Such ambient transport is an equivalence relation, so its class is locally
constant along the height interval. Connectedness therefore constructs one
ambient diffeomorphism carrying the actual two endpoint pairs onto each other.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- A genuine ambient diffeomorphism, with both the level and sublevel identities retained. -/
def AmbientEquivalent (f : M → ℝ) (a b : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
    D '' {x : M | f x = a} = {x : M | f x = b} ∧
    D '' {x : M | f x ≤ a} = {x : M | f x ≤ b}

theorem ambientEquivalent_refl (f : M → ℝ) (a : ℝ) : AmbientEquivalent (E := E) f a a := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, ?_, ?_⟩ <;> exact image_id _

theorem ambientEquivalent_symm {f : M → ℝ} {a b : ℝ}
    (h : AmbientEquivalent (E := E) f a b) : AmbientEquivalent (E := E) f b a := by
  obtain ⟨D, hlevel, hsublevel⟩ := h
  have hreverse (S T : Set M) (hST : D '' S = T) : D.symm '' T = S := by
    rw [← hST, image_image]
    have heq : (fun x : M => D.symm (D x)) = id := funext D.symm_apply_apply
    rw [heq, image_id]
  exact ⟨D.symm, hreverse _ _ hlevel, hreverse _ _ hsublevel⟩

theorem ambientEquivalent_trans {f : M → ℝ} {a b c : ℝ}
    (hab : AmbientEquivalent (E := E) f a b) (hbc : AmbientEquivalent (E := E) f b c) :
    AmbientEquivalent (E := E) f a c := by
  obtain ⟨e, he, he'⟩ := hab
  obtain ⟨d, hd, hd'⟩ := hbc
  refine ⟨e.trans d, ?_, ?_⟩
  · change (fun x => d (e x)) '' {x : M | f x = a} = {x : M | f x = c}
    rw [← image_image, he, hd]
  · change (fun x => d (e x)) '' {x : M | f x ≤ a} = {x : M | f x ≤ c}
    rw [← image_image, he', hd']

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Smooth transport of the original manifold, its endpoint levels, and its sublevels
across a critical-point-free band. -/
theorem exists_ambient_regularBand_transport {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧
      D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} := by
  classical
  let B := Icc a b
  let left : B := ⟨a, ⟨le_rfl, hab⟩⟩
  let right : B := ⟨b, ⟨hab, le_rfl⟩⟩
  let reg (t : B) : ∀ x, f x = (t : ℝ) → x ∉ ManifoldMorse.criticalPoints E f :=
    fun x hx => hband x (hx ▸ t.property)
  let P : B → Prop := fun t => AmbientEquivalent (E := E) f a (t : ℝ)
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro t
    obtain ⟨δ, hδ, K, -, htransport⟩ := exists_nearby_ambient_level_diffeomorphs hf (reg t)
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hdist : |(s : ℝ) - (t : ℝ)| < δ := by
      change dist (s : ℝ) (t : ℝ) < δ at hs
      simpa only [Real.dist_eq] using hs
    obtain ⟨D, -, hlevel, hsublevel⟩ := htransport ((s : ℝ) - (t : ℝ)) hdist
    have hts : AmbientEquivalent (E := E) f (t : ℝ) (s : ℝ) := by
      have heq : (t : ℝ) + ((s : ℝ) - (t : ℝ)) = (s : ℝ) := by ring
      refine ⟨D, ?_, ?_⟩
      · simpa only [heq] using hlevel
      · simpa only [heq] using hsublevel
    apply propext
    constructor
    · intro hs
      exact ambientEquivalent_trans hs (ambientEquivalent_symm hts)
    · intro ht
      exact ambientEquivalent_trans ht hts
  let _ : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hconstant : P left = P right := hlocal.apply_eq_of_preconnectedSpace left right
  have hleft : P left := ambientEquivalent_refl f a
  have hright : P right := hconstant ▸ hleft
  exact hright

omit [T2Space M] [CompactSpace M] in
/-- Restrict an ambient diffeomorphism to actual regular levels, using their native atlases. -/
theorem exists_levelDiffeomorph_of_ambient {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hlevel : D '' {x : M | f x = a} = {x : M | f x = b}) :
    letI := chartedSpace hf ha
    letI := chartedSpace hf hb
    ∃ e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
        {x : M // f x = a} {x : M // f x = b} ∞,
      ∀ x, (e x : M) = D x := by
  let _ := chartedSpace hf ha
  let _ := chartedSpace hf hb
  have hiff (x : M) : f x = a ↔ f (D x) = b := by
    constructor
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := ⟨x, hx, rfl⟩
      rwa [hlevel] at hh
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := by rw [hlevel]; exact hx
      obtain ⟨z, hz, hzx⟩ := hh
      exact D.injective hzx ▸ hz
  let e := D.toHomeomorph.subtype (p := fun x => f x = a) (q := fun x => f x = b) hiff
  have he : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e :=
    (contMDiff_iff_inclusion hf hb 𝓘(ℝ, Model E) e).mpr
      (D.contMDiff.comp (contMDiff_inclusion hf ha))
  have hei : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e.symm :=
    (contMDiff_iff_inclusion hf ha 𝓘(ℝ, Model E) e.symm).mpr
      (D.symm.contMDiff.comp (contMDiff_inclusion hf hb))
  let F : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
      {x : M // f x = a} {x : M // f x = b} ∞ := {
    e.toEquiv with
    contMDiff_toFun := he
    contMDiff_invFun := hei }
  exact ⟨F, fun _ => rfl⟩

/-- The two actual regular levels bounding a critical-point-free band are diffeomorphic. -/
theorem nonempty_regularLevelDiffeomorph {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    let ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f :=
      fun x hx => hband x (by rw [hx]; exact ⟨le_rfl, hab⟩)
    let hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f :=
      fun x hx => hband x (by rw [hx]; exact ⟨hab, le_rfl⟩)
    letI := chartedSpace hf ha
    letI := chartedSpace hf hb
    Nonempty (Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
      {x : M // f x = a} {x : M // f x = b} ∞) := by
  let ha : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f :=
    fun x hx => hband x (by rw [hx]; exact ⟨le_rfl, hab⟩)
  let hb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f :=
    fun x hx => hband x (by rw [hx]; exact ⟨hab, le_rfl⟩)
  let _ := chartedSpace hf ha
  let _ := chartedSpace hf hb
  obtain ⟨D, hlevel, -⟩ := exists_ambient_regularBand_transport hf hab hband
  obtain ⟨e, -⟩ := exists_levelDiffeomorph_of_ambient hf ha hb D hlevel
  exact ⟨e⟩

end Wikipedia.SmoothSixDPoincare.RegularLevel

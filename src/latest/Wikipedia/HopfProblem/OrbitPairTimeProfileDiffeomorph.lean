import Wikipedia.HopfProblem.OrbitPairSupportedTimeProfile
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Actual native diffeomorphisms from supported positive time profiles

Positive scalar derivative and fixed exterior times give a bijection on
each time fibre. The full native derivative is triangular with that positive
entry and the spatial identity. The boundaryless inverse-function theorem
then gives a smooth inverse in the unchanged product atlas.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open Wikipedia.SmoothSixDPoincare

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def sourceTimeMap (τ : ℝ × M → ℝ) (p : ℝ × M) : ℝ × M := (τ p, p.2)

theorem sourceTimeMap_smooth {τ : ℝ × M → ℝ}
    (hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ (sourceTimeMap τ) :=
  hτ.prodMk contMDiff_snd

theorem time_profile_hasDerivAt {τ : ℝ × M → ℝ}
    (hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ) (x : M) (t : ℝ) :
    HasDerivAt (fun s => τ (s, x)) (deriv (fun s => τ (s, x)) t) t := by
  have hh : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => τ (s, x)) :=
    hτ.comp (contMDiff_id.prodMk contMDiff_const)
  exact (hh.mdifferentiableAt (by simp)).differentiableAt.hasDerivAt

theorem time_profile_fibre_bijective {τ : ℝ × M → ℝ}
    (hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ)
    (hpos : ∀ x t, 0 < deriv (fun s => τ (s, x)) t)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → τ (t, x) = t) (x : M) :
    Bijective (fun t => τ (t, x)) := by
  have hmono : StrictMono (fun t => τ (t, x)) :=
    strictMono_of_hasDerivAt_pos (time_profile_hasDerivAt hτ x) (hpos x)
  refine ⟨hmono.injective, ?_⟩
  intro y
  have hc : Continuous (fun t => τ (t, x)) :=
    hτ.continuous.comp (continuous_id.prodMk continuous_const)
  apply mem_range_of_exists_le_of_exists_ge hc
  · refine ⟨min a y, ?_⟩
    rw [hfix _ x (fun h => (not_lt_of_ge (min_le_left a y)) h.1)]
    exact min_le_right _ _
  · refine ⟨max b y, ?_⟩
    rw [hfix _ x (fun h => (not_lt_of_ge (le_max_left b y)) h.2)]
    exact le_max_right _ _

theorem sourceTimeMap_bijective {τ : ℝ × M → ℝ}
    (hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ)
    (hpos : ∀ x t, 0 < deriv (fun s => τ (s, x)) t)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → τ (t, x) = t) :
    Bijective (sourceTimeMap τ) := by
  constructor
  · rintro ⟨t, x⟩ ⟨s, y⟩ heq
    have hxy : x = y := congrArg Prod.snd heq
    subst y
    have ht : t = s := (time_profile_fibre_bijective hτ hpos hfix x).injective
      (congrArg Prod.fst heq)
    exact Prod.ext ht rfl
  · rintro ⟨t, x⟩
    obtain ⟨s, hs⟩ := (time_profile_fibre_bijective hτ hpos hfix x).surjective t
    exact ⟨(s, x), Prod.ext hs rfl⟩

theorem sourceTimeMap_invertible_mfderiv {τ : ℝ × M → ℝ}
    (hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ)
    (hpos : ∀ x t, 0 < deriv (fun s => τ (s, x)) t) (q : ℝ × M) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (sourceTimeMap τ) q).IsInvertible := by
  let D : ℝ × E →L[ℝ] ℝ := mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) τ q
  let T : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (sourceTimeMap τ) q
  let B : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t => τ (t, q.2)) q.1
  let d := deriv (fun t => τ (t, q.2)) q.1
  have hT : T = D.prod (ContinuousLinearMap.snd ℝ ℝ E) := by
    have hh := mfderiv_prodMk (hτ.mdifferentiableAt (x := q) (by simp)) mdifferentiableAt_snd
    rw [mfderiv_snd] at hh
    exact hh
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun t : ℝ => (t, q.2)) q.1
      (ContinuousLinearMap.inl ℝ ℝ E) :=
    (hasMFDerivAt_id q.1).prodMk (hasMFDerivAt_const q.2 q.1)
  have hB : B = D.comp (ContinuousLinearMap.inl ℝ ℝ E) := by
    have hh := mfderiv_comp q.1 (hτ.mdifferentiableAt (by simp)) hc.mdifferentiableAt
    rw [hc.mfderiv] at hh
    exact hh
  have hBd : B = ContinuousLinearMap.toSpanSingleton ℝ d :=
    (time_profile_hasDerivAt hτ q.2 q.1).hasFDerivAt.hasMFDerivAt.mfderiv
  have htime : D (1, 0) = d := by
    have hh := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) (hB.symm.trans hBd)
    simpa using hh
  have hi : Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    rintro ⟨t, v⟩ hv
    rw [hT] at hv
    have hv0 : v = 0 := congrArg Prod.snd hv
    subst v
    have ht : D (t, 0) = 0 := congrArg Prod.fst hv
    have he : (t, (0 : E)) = t • ((1 : ℝ), (0 : E)) := by simp
    rw [he, map_smul, htime, smul_eq_mul] at ht
    exact Prod.ext ((mul_eq_zero.mp ht).resolve_right (hpos q.2 q.1).ne') rfl
  have hs : Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
  let L := (LinearEquiv.ofBijective T.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv
  change T.IsInvertible
  exact ⟨L, rfl⟩

theorem exists_time_profile_diffeomorph {τ : ℝ × M → ℝ}
    (hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ)
    (hpos : ∀ x t, 0 < deriv (fun s => τ (s, x)) t)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → τ (t, x) = t) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞,
      ∀ p, Ψ p = (τ p, p.2) := by
  have hl : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (sourceTimeMap τ) := fun p => isLocalDiffeomorphAt_boundaryless isOpen_univ (mem_univ p)
        (sourceTimeMap_smooth hτ).contMDiffOn (sourceTimeMap_invertible_mfderiv hτ hpos p)
  exact ⟨hl.diffeomorphOfBijective (sourceTimeMap_bijective hτ hpos hfix), fun _ => rfl⟩

variable [T2Space M] [CompactSpace M]

theorem exists_supported_source_time_diffeomorph {C U : Set M}
    (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    {a b t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (ht₁ : t₁ ∈ Ioo a b) :
    ∃ Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞,
      (∀ p, (Ψ p).2 = p.2) ∧
      (∀ t x, x ∉ U ∨ t ∉ Ioo a b → Ψ (t, x) = (t, x)) ∧
      (∀ x ∈ C, Ψ =ᶠ[𝓝 (t₀, x)] fun p => (p.1 + (t₁ - t₀), p.2)) ∧
      (∀ x ∈ C, Ψ (t₀, x) = (t₁, x)) ∧
      (∀ x t, 0 < deriv (fun s => (Ψ (s, x)).1) t) := by
  obtain ⟨τ, hτ, hpos, hfix, hgerm, hpoint⟩ :=
    exists_supported_time_profile (I := I) hC hU hCU ht₀ ht₁
  obtain ⟨Ψ, hΨ⟩ := exists_time_profile_diffeomorph hτ hpos
    (fun t x ht => hfix t x (Or.inr ht))
  refine ⟨Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hΨ]
  · intro t x h
    rw [hΨ, hfix t x h]
  · intro x hx
    filter_upwards [hgerm x hx] with p hp
    rw [hΨ, hp]
  · intro x hx
    rw [hΨ, hpoint x hx]
  · intro x t
    have heq : (fun s => (Ψ (s, x)).1) = (fun s => τ (s, x)) := by
      funext s
      rw [hΨ]
    rw [heq]
    exact hpos x t

end Wikipedia.HopfProblem.OrbitPair.NativeFamily

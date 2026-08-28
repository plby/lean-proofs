import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity

/-!
# Parameter-retaining tracks and stability of compact embeddings

For a smooth family on a native manifold source, the track retaining every
parameter is immersive wherever the spatial map is immersive. A compact
embedded immersive source set at one parameter consequently remains
injective for all nearby parameters. This is the local injectivity control
needed when later patches could create collisions near the diagonal.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open Wikipedia.SmoothSixDPoincare

variable {P E G H K X N : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

def track (F : P × X → N) (q : P × X) : P × N := (q.1, F q)

theorem track_smoothOn {F : P × X → N} {W : Set (P × X)}
    (hF : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ F W) :
    ContMDiffOn (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod J) ∞ (track F) W :=
  contMDiff_fst.contMDiffOn.prodMk hF

theorem injective_mfderiv_track {F : P × X → N} (q : P × X)
    (hF : MDifferentiableAt (𝓘(ℝ, P).prod I) J F q)
    (hinj : Injective (mfderiv I J (fun x => F (q.1, x)) q.2)) :
    Injective (mfderiv (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod J) (track F) q) := by
  let A : P × E →L[ℝ] P := mfderiv (𝓘(ℝ, P).prod I) 𝓘(ℝ, P) Prod.fst q
  let D : P × E →L[ℝ] G := mfderiv (𝓘(ℝ, P).prod I) J F q
  let T : P × E →L[ℝ] P × G :=
    mfderiv (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod J) (track F) q
  let S : E →L[ℝ] G := mfderiv I J (fun x => F (q.1, x)) q.2
  have hA : A = ContinuousLinearMap.fst ℝ P E := mfderiv_fst
  have hT : T = A.prod D := mfderiv_prodMk mdifferentiableAt_fst hF
  have hi : HasMFDerivAt I (𝓘(ℝ, P).prod I) (fun x : X => (q.1, x)) q.2
      (ContinuousLinearMap.inr ℝ P E) :=
    (hasMFDerivAt_const q.1 q.2).prodMk (hasMFDerivAt_id q.2)
  let B : E →L[ℝ] P × E :=
    mfderiv I (𝓘(ℝ, P).prod I) (fun x : X => (q.1, x)) q.2
  have hB : B = ContinuousLinearMap.inr ℝ P E := hi.mfderiv
  have hS : S = D.comp (ContinuousLinearMap.inr ℝ P E) := by
    have hcomp : S = D.comp B := mfderiv_comp q.2 hF hi.mdifferentiableAt
    rwa [hB] at hcomp
  change Injective T
  rw [hT, hA]
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨p, v⟩ hv
  have hp : p = 0 := congrArg Prod.fst hv
  subst p
  have hv' : S v = 0 := by
    rw [hS]
    exact congrArg Prod.snd hv
  exact Prod.ext rfl ((injective_iff_map_eq_zero S).mp hinj v hv')

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
  [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ X] [IsManifold J ∞ N] [T2Space N]

theorem eventually_injOn_compact {F : P × X → N} {W : Set (P × X)}
    (hW : IsOpen W) (hF : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ F W)
    {S : Set X} (hS : IsCompact S) (p : P) (hmem : ∀ x ∈ S, (p, x) ∈ W)
    (hinj : InjOn (fun x => F (p, x)) S)
    (hderiv : ∀ x ∈ S, Injective (mfderiv I J (fun y => F (p, y)) x)) :
    ∀ᶠ a in 𝓝 p, InjOn (fun x => F (a, x)) S := by
  let C : Set (P × X) := {p} ×ˢ S
  have hC : IsCompact C := isCompact_singleton.prod hS
  have hCW : C ⊆ W := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    have he : a = p := mem_singleton_iff.mp ha
    subst a
    exact hmem x hx
  have hi : InjOn (track F) C := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩ ⟨b, y⟩ ⟨hb, hy⟩ heq
    have ha' : a = p := mem_singleton_iff.mp ha
    have hb' : b = p := mem_singleton_iff.mp hb
    subst a
    subst b
    exact Prod.ext rfl (hinj hx hy (congrArg Prod.snd heq))
  have hd (q : P × X) (hq : q ∈ C) :
      Injective (mfderiv (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod J) (track F) q) := by
    have hp : q.1 = p := mem_singleton_iff.mp hq.1
    apply injective_mfderiv_track q
      ((hF.contMDiffAt (hW.mem_nhds (hCW hq))).mdifferentiableAt (by simp))
    rw [hp]
    exact hderiv q.2 hq.2
  obtain ⟨V, hV, hCV, -, hVi⟩ := NativeImmersion.exists_open_injOn_near_compact hW
    (track_smoothOn hF) hC hCW hi hd
  have hn := (MorsePerturbation.isOpen_forall_mem_compact hS hV).mem_nhds
    (x := p) (fun x hx => hCV ⟨mem_singleton _, hx⟩)
  filter_upwards [hn] with a ha
  intro x hx y hy hxy
  exact congrArg Prod.snd (hVi (ha x hx) (ha y hy) (Prod.ext rfl hxy))

end Wikipedia.HopfProblem.OrbitPair.NativeFamily

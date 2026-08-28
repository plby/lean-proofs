import Wikipedia.NoExoticSixSphere.FrameBoundaryInterpolation
import Wikipedia.NoExoticSixSphere.UniformProductTube
import Wikipedia.NoExoticSixSphere.RelativePartialFrameSmoothing
import Mathlib.Analysis.Complex.Tietze

/-!
# Prescribed full frames on a protected product of arbitrary transverse dimension

Actual projection-range interpolation and relative smoothing install the
prescribed frame on an entire thinner product over a compact protected
set. The original core elsewhere need not stay unchanged. No new normal
space or independent frame trivialization is supplied.
-/

noncomputable section

open Set Metric Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralProductFrame

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_frameInterpolation_product {N n d : ℕ} {K S : Set (Vector 4)}
    (hK : IsCompact K) (hS : IsCompact S) (r : ℝ) (hr : 0 < r)
    (A F : C(Vector 4 × Vector d, Vector n →L[ℝ] Vector N))
    (P : Vector 4 × Vector d → Vector N →L[ℝ] Vector N)
    (hP : ContinuousOn P (K ×ˢ closedBall (0 : Vector d) r))
    (hA : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, Injective ((P p).comp (A p)))
    (heq : ∀ x ∈ S, F (x, 0) = A (x, 0)) :
    ∃ B : C(Vector 4 × Vector d, Vector n →L[ℝ] Vector N),
      (∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, Injective ((P p).comp (B p))) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ U : Set (Vector 4 × Vector d), IsOpen U ∧
        S ×ˢ closedBall (0 : Vector d) ε ⊆ U ∧ EqOn B F U := by
  have heq' : EqOn F A (S ×ˢ ({0} : Set (Vector d))) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact heq x hx
  obtain ⟨B, hBi, U, hU, hSU, hBF⟩ := exists_boundaryInterpolation
    (hK.prod (isCompact_closedBall (0 : Vector d) r)) (hS.prod isCompact_singleton)
    A F P hP hA heq'
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let q : S × Vector d → Vector 4 × Vector d := fun p ↦ (p.1.val, p.2)
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_closedProductTube (hU.preimage hq)
    (fun x ↦ hSU ⟨x.property, rfl⟩)
  refine ⟨B, hBi, min δ r, lt_min hδ hr, min_le_right _ _, U, hU, ?_, hBF⟩
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  apply hδU ⟨x, hx⟩ v
  have hvr := (closedBall_subset_closedBall (min_le_left δ r)) hv
  simpa only [mem_closedBall, dist_zero_right] using hvr

end Wikipedia.HopfProblem.DegreeCollapse.GeneralProductFrame

noncomputable section

open Set Metric Function Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.GeneralProductFrame

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_smoothProductFrame_collar {N n d : ℕ} {K S : Set (Vector 4)}
    (hK : IsCompact K) (hS : IsCompact S) (hSK : S ⊆ K) (r : ℝ) (hr : 0 < r)
    (P : Vector 4 × Vector d → Vector N →L[ℝ] Vector N)
    (hP : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, IsIdempotentElem (P p))
    (hPs : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, ContDiffAt ℝ ∞ P p)
    (A : Vector 4 × Vector d → Vector n →L[ℝ] Vector N)
    (hAs : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, ContDiffAt ℝ ∞ A p)
    (hAn : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, ∀ w, ‖A p w‖ = ‖w‖)
    (hAr : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, (A p).range = (P p).range)
    (F : C(Vector 4 × Vector d, Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFA : ∀ x ∈ S, F (x, 0) = A (x, 0))
    (hFn : ∀ p ∈ S ×ˢ closedBall (0 : Vector d) r, ∀ w, ‖F p w‖ = ‖w‖)
    (hFr : ∀ p ∈ S ×ˢ closedBall (0 : Vector d) r, (F p).range ≤ (P p).range) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ G : Vector 4 × Vector d → Vector n →L[ℝ] Vector N,
      (∀ p ∈ K ×ˢ closedBall (0 : Vector d) ε, ContDiffAt ℝ ∞ G p) ∧
      (∀ p ∈ K ×ˢ closedBall (0 : Vector d) ε, ∀ w, ‖G p w‖ = ‖w‖) ∧
      (∀ p ∈ K ×ˢ closedBall (0 : Vector d) ε, (G p).range = (P p).range) ∧
      EqOn G F (S ×ˢ closedBall (0 : Vector d) ε) := by
  let K₀ := K ×ˢ closedBall (0 : Vector d) r
  have hK₀ : IsCompact K₀ := hK.prod (isCompact_closedBall (0 : Vector d) r)
  have hAc : Continuous (fun p : K₀ ↦ A p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hAs p.val p.property).continuousAt.comp continuous_subtype_val.continuousAt
  let Ac : C(K₀, Vector n →L[ℝ] Vector N) := ⟨_, hAc⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq hK₀.isClosed
  have heA (p : K₀) : A₀ p.val = A p.val := ContinuousMap.congr_fun hA₀ p
  have hPA (p : Vector 4 × Vector d) (hp : p ∈ K₀) : (P p).comp (A₀ p) = A₀ p := by
    rw [heA ⟨p, hp⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P p) (hP p hp) ⟨A p w, (hAr p hp).le ⟨w, rfl⟩⟩
  have hAi (p : Vector 4 × Vector d) (hp : p ∈ K₀) : Injective ((P p).comp (A₀ p)) := by
    rw [hPA p hp, heA ⟨p, hp⟩]
    exact Stiefel.injective ⟨A p, hAn p hp⟩
  have hFA₀ (x : Vector 4) (hx : x ∈ S) : F (x, 0) = A₀ (x, 0) :=
    (hFA x hx).trans (heA ⟨(x, 0), hSK hx, mem_closedBall_self hr.le⟩).symm
  obtain ⟨B, hBi, ε, hε, hεr, U, hU, hSU, hBF⟩ := exists_frameInterpolation_product
    hK hS r hr A₀ F P (fun p hp ↦ (hPs p hp).continuousAt.continuousWithinAt) hAi hFA₀
  have hKε (p : Vector 4 × Vector d) (hp : p ∈ K ×ˢ closedBall (0 : Vector d) ε) : p ∈ K₀ :=
    ⟨hp.1, (closedBall_subset_closedBall hεr) hp.2⟩
  have hSε (p : Vector 4 × Vector d) (hp : p ∈ S ×ˢ closedBall (0 : Vector d) ε) :
      p ∈ S ×ˢ closedBall (0 : Vector d) r :=
    ⟨hp.1, (closedBall_subset_closedBall hεr) hp.2⟩
  have hBP (p : Vector 4 × Vector d)
      (hp : p ∈ (K ×ˢ closedBall (0 : Vector d) ε) ∩ (S ×ˢ closedBall (0 : Vector d) ε)) :
      (P p).comp (B p) = B p := by
    rw [hBF (hSU hp.2)]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P p) (hP p (hKε p hp.1))
      ⟨F p w, hFr p (hSε p hp.2) ⟨w, rfl⟩⟩
  have hBn (p : Vector 4 × Vector d)
      (hp : p ∈ (K ×ˢ closedBall (0 : Vector d) ε) ∩ (S ×ˢ closedBall (0 : Vector d) ε))
      (w : Vector n) : ‖B p w‖ = ‖w‖ := by
    rw [hBF (hSU hp.2)]
    exact hFn p (hSε p hp.2) w
  have hBs : ContDiffOn ℝ ∞ B U := hFs.contDiffOn.congr hBF
  obtain ⟨G, hGs, hGn, hGr, hGB⟩ := exists_smoothPartialFrame_rel
    (hK.prod (isCompact_closedBall (0 : Vector d) ε)) B B.continuous P
    (fun p hp ↦ hPs p (hKε p hp)) (fun p hp ↦ hBi p (hKε p hp)) hBP hBn
    (hS.isClosed.prod isClosed_closedBall) (hU.mem_nhdsSet.mpr hSU) hBs
  refine ⟨ε, hε, hεr, G, hGs, hGn, ?_, ?_⟩
  · intro p hp
    apply Submodule.eq_of_le_of_finrank_eq (hGr p hp)
    rw [← hAr p (hKε p hp),
      LinearMap.finrank_range_of_inj (Stiefel.injective ⟨G p, hGn p hp⟩),
      LinearMap.finrank_range_of_inj (Stiefel.injective ⟨A p, hAn p (hKε p hp)⟩)]
  · intro p hp
    exact (hGB ⟨⟨hSK hp.1, hp.2⟩, hp⟩).trans (hBF (hSU hp))

end Wikipedia.HopfProblem.DegreeCollapse.GeneralProductFrame

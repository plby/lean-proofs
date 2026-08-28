import Wikipedia.NoExoticSixSphere.FrameBoundaryInterpolation
import Wikipedia.NoExoticSixSphere.UniformProductTube
import Wikipedia.NoExoticSixSphere.RelativePartialFrameSmoothing
import Mathlib.Analysis.Complex.Tietze

/-!

# Exact full frames on protected products in arbitrary disk dimensions

Actual projection interpolation and relative smoothing install the prescribed
frame on an entire thinner product over the protected compact set. The map
and its actual projection ranges do not change. The inner core frame away
from that protected set need not be retained.
-/

noncomputable section

open Set Metric Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowProductFrame

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_frameInterpolation_product {d N n q : ℕ} {K S : Set (Vector (d + 1))}
    (hK : IsCompact K) (hS : IsCompact S) (r : ℝ) (hr : 0 < r)
    (A F : C(Vector (d + 1) × Vector q, Vector n →L[ℝ] Vector N))
    (P : Vector (d + 1) × Vector q → Vector N →L[ℝ] Vector N)
    (hP : ContinuousOn P (K ×ˢ closedBall (0 : Vector q) r))
    (hA : ∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, Injective ((P p).comp (A p)))
    (heq : ∀ x ∈ S, F (x, 0) = A (x, 0)) :
    ∃ B : C(Vector (d + 1) × Vector q, Vector n →L[ℝ] Vector N),
      (∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, Injective ((P p).comp (B p))) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ U : Set (Vector (d + 1) × Vector q), IsOpen U ∧
        S ×ˢ closedBall (0 : Vector q) ε ⊆ U ∧ EqOn B F U := by
  have heq' : EqOn F A (S ×ˢ ({0} : Set (Vector q))) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact heq x hx
  obtain ⟨B, hBi, U, hU, hSU, hBF⟩ := exists_boundaryInterpolation
    (hK.prod (isCompact_closedBall (0 : Vector q) r)) (hS.prod isCompact_singleton)
    A F P hP hA heq'
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let coreInclusion : S × Vector q → Vector (d + 1) × Vector q := fun p ↦ (p.1.val, p.2)
  have hq : Continuous coreInclusion :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_closedProductTube (hU.preimage hq)
    (fun x ↦ hSU ⟨x.property, rfl⟩)
  refine ⟨B, hBi, min δ r, lt_min hδ hr, min_le_right _ _, U, hU, ?_, hBF⟩
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  apply hδU ⟨x, hx⟩ v
  have hvr := (closedBall_subset_closedBall (min_le_left δ r)) hv
  simpa only [mem_closedBall, dist_zero_right] using hvr

end Wikipedia.HopfProblem.DegreeCollapse.LowProductFrame

noncomputable section

open Set Metric Function Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowProductFrame

open NoExoticSixSphere GLOrthonormalization Stiefel

theorem exists_smoothProductFrame_collar {d N n q : ℕ} {K S : Set (Vector (d + 1))}
    (hK : IsCompact K) (hS : IsCompact S) (hSK : S ⊆ K) (r : ℝ) (hr : 0 < r)
    (P : Vector (d + 1) × Vector q → Vector N →L[ℝ] Vector N)
    (hP : ∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, IsIdempotentElem (P p))
    (hPs : ∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, ContDiffAt ℝ ∞ P p)
    (A : Vector (d + 1) × Vector q → Vector n →L[ℝ] Vector N)
    (hAs : ∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, ContDiffAt ℝ ∞ A p)
    (hAn : ∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, ∀ w, ‖A p w‖ = ‖w‖)
    (hAr : ∀ p ∈ K ×ˢ closedBall (0 : Vector q) r, (A p).range = (P p).range)
    (F : C(Vector (d + 1) × Vector q, Vector n →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
    (hFA : ∀ x ∈ S, F (x, 0) = A (x, 0))
    (hFn : ∀ p ∈ S ×ˢ closedBall (0 : Vector q) r, ∀ w, ‖F p w‖ = ‖w‖)
    (hFr : ∀ p ∈ S ×ˢ closedBall (0 : Vector q) r, (F p).range ≤ (P p).range) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ G : Vector (d + 1) × Vector q → Vector n →L[ℝ] Vector N,
      (∀ p ∈ K ×ˢ closedBall (0 : Vector q) ε, ContDiffAt ℝ ∞ G p) ∧
      (∀ p ∈ K ×ˢ closedBall (0 : Vector q) ε, ∀ w, ‖G p w‖ = ‖w‖) ∧
      (∀ p ∈ K ×ˢ closedBall (0 : Vector q) ε, (G p).range = (P p).range) ∧
      EqOn G F (S ×ˢ closedBall (0 : Vector q) ε) := by
  let K₀ := K ×ˢ closedBall (0 : Vector q) r
  have hK₀ : IsCompact K₀ := hK.prod (isCompact_closedBall (0 : Vector q) r)
  have hAc : Continuous (fun p : K₀ ↦ A p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hAs p.val p.property).continuousAt.comp continuous_subtype_val.continuousAt
  let Ac : C(K₀, Vector n →L[ℝ] Vector N) := ⟨_, hAc⟩
  obtain ⟨A₀, hA₀⟩ := Ac.exists_restrict_eq hK₀.isClosed
  have heA (p : K₀) : A₀ p.val = A p.val := ContinuousMap.congr_fun hA₀ p
  have hPA (p : Vector (d + 1) × Vector q) (hp : p ∈ K₀) : (P p).comp (A₀ p) = A₀ p := by
    rw [heA ⟨p, hp⟩]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P p) (hP p hp) ⟨A p w, (hAr p hp).le ⟨w, rfl⟩⟩
  have hAi (p : Vector (d + 1) × Vector q) (hp : p ∈ K₀) : Injective ((P p).comp (A₀ p)) := by
    rw [hPA p hp, heA ⟨p, hp⟩]
    exact Stiefel.injective ⟨A p, hAn p hp⟩
  have hFA₀ (x : Vector (d + 1)) (hx : x ∈ S) : F (x, 0) = A₀ (x, 0) :=
    (hFA x hx).trans (heA ⟨(x, 0), hSK hx, mem_closedBall_self hr.le⟩).symm
  obtain ⟨B, hBi, ε, hε, hεr, U, hU, hSU, hBF⟩ := exists_frameInterpolation_product
    hK hS r hr A₀ F P (fun p hp ↦ (hPs p hp).continuousAt.continuousWithinAt) hAi hFA₀
  have hKε (p : Vector (d + 1) × Vector q) (hp : p ∈ K ×ˢ closedBall (0 : Vector q) ε) : p ∈ K₀ :=
    ⟨hp.1, (closedBall_subset_closedBall hεr) hp.2⟩
  have hSε (p : Vector (d + 1) × Vector q) (hp : p ∈ S ×ˢ closedBall (0 : Vector q) ε) :
      p ∈ S ×ˢ closedBall (0 : Vector q) r :=
    ⟨hp.1, (closedBall_subset_closedBall hεr) hp.2⟩
  have hBP (p : Vector (d + 1) × Vector q)
      (hp : p ∈ (K ×ˢ closedBall (0 : Vector q) ε) ∩ (S ×ˢ closedBall (0 : Vector q) ε)) :
      (P p).comp (B p) = B p := by
    rw [hBF (hSU hp.2)]
    apply ContinuousLinearMap.ext
    intro w
    exact projection_apply_range (P p) (hP p (hKε p hp.1))
      ⟨F p w, hFr p (hSε p hp.2) ⟨w, rfl⟩⟩
  have hBn (p : Vector (d + 1) × Vector q)
      (hp : p ∈ (K ×ˢ closedBall (0 : Vector q) ε) ∩ (S ×ˢ closedBall (0 : Vector q) ε))
      (w : Vector n) : ‖B p w‖ = ‖w‖ := by
    rw [hBF (hSU hp.2)]
    exact hFn p (hSε p hp.2) w
  have hBs : ContDiffOn ℝ ∞ B U := hFs.contDiffOn.congr hBF
  obtain ⟨G, hGs, hGn, hGr, hGB⟩ := exists_smoothPartialFrame_rel
    (hK.prod (isCompact_closedBall (0 : Vector q) ε)) B B.continuous P
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

end Wikipedia.HopfProblem.DegreeCollapse.LowProductFrame


import Wikipedia.NoExoticSixSphere.SphereTargetCorrection
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Mathlib.Topology.Connected.Clopen

/-!
# Move a sphere value by a native diffeomorphism homotopic to the identity

The existing local rotation and its actual homotopy move nearby points.
Compositions of these rotations reach every point of a positive-dimensional
sphere: the reachable set is nonempty, open, and closed. This avoids using
an antipodal reflection as though it were homotopic to the identity.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem exists_nearby_id_homotopic_sphereDiffeomorph {n : ℕ} (a b : Sphere n)
    (h : dist a b < 1 / 2) :
    ∃ D : Sphere n ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n, D a = b ∧
      (ContinuousMap.id (Sphere n)).Homotopic (D.toHomeomorph : C(Sphere n, Sphere n)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  refine ⟨sphereRotation (n := n) a b, sphereRotation_apply a b, ?_⟩
  let F : C(ℝ × Sphere n, Sphere n) := ⟨Prod.snd, continuous_snd⟩
  let j : C(Sphere n, ℝ × Sphere n) :=
    ⟨fun x ↦ (1 / 2, x), continuous_const.prodMk continuous_id⟩
  let H := (SphereTargetCorrection.homotopy b a h F).toHomotopy.compContinuousMap j
  have he : (SphereTargetCorrection.corrected b a h F).comp j =
      ((sphereRotation (n := n) a b).toHomeomorph : C(Sphere n, Sphere n)) := by
    apply ContinuousMap.ext
    intro x
    change sphereRotation (n := n) (CollaredValueCurve.curve b a (by linarith) (1 / 2)) b x = _
    rw [CollaredValueCurve.curve_middle b a _ (by constructor <;> norm_num)]
    rfl
  rw [← he]
  exact ⟨H⟩

theorem exists_id_homotopic_sphereDiffeomorph {n : ℕ} (hn : 0 < n) (a b : Sphere n) :
    ∃ D : Sphere n ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n, D a = b ∧
      (ContinuousMap.id (Sphere n)).Homotopic (D.toHomeomorph : C(Sphere n, Sphere n)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let R : Sphere (n + 1) → Prop := fun c ↦
    ∃ D : Sphere (n + 1) ≃ₘ⟮𝓡 (n + 1), 𝓡 (n + 1)⟯ Sphere (n + 1), D a = c ∧
      (ContinuousMap.id (Sphere (n + 1))).Homotopic
        (D.toHomeomorph : C(Sphere (n + 1), Sphere (n + 1)))
  have hr : R a :=
    ⟨Diffeomorph.refl (𝓡 (n + 1)) (Sphere (n + 1)) ∞, rfl,
      ContinuousMap.Homotopic.refl _⟩
  have hstep : ∀ c d, R c → dist d c < 1 / 2 → R d := by
    intro c d hc hdc
    obtain ⟨D, hD, HD⟩ := hc
    obtain ⟨E, hE, HE⟩ := exists_nearby_id_homotopic_sphereDiffeomorph c d
      (by simpa only [dist_comm] using hdc)
    refine ⟨D.trans E, ?_, ?_⟩
    · change E (D a) = d
      rw [hD, hE]
    · exact HE.comp HD
  have ho : IsOpen {c | R c} := by
    rw [Metric.isOpen_iff]
    intro c hc
    exact ⟨1 / 2, by norm_num, fun d hd ↦ hstep c d hc hd⟩
  have hc : IsClosed {c | R c} := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro c hc
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro d hd hR
    exact hc (hstep d c hR (by rw [dist_comm]; exact hd))
  have hall : {c | R c} = univ := (show IsClopen {c | R c} from ⟨hc, ho⟩).eq_univ ⟨a, hr⟩
  have hb : b ∈ {c | R c} := by rw [hall]; trivial
  exact hb

end NoExoticSixSphere

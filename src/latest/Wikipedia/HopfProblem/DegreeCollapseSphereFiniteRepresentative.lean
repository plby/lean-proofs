import Wikipedia.HopfProblem.DegreeCollapseSphereChartRegularity

/-!
# Finite representatives of actual sphere maps and their product derivatives

The actual stereographic representative inherits smoothness and submersion
from the native sphere map away from the target pole. Cartesian products
with the real identity or with a second copy retain surjectivity of the
explicit Euclidean derivative.
-/

noncomputable section

open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteRepresentative

open NoExoticSixSphere SphereComposition FiniteSphereProductCharts

def point (n : ℕ) : V n → Sphere n := (sphereProjection n).symm

theorem point_ne_pole (n : ℕ) (p : V n) : point n p ≠ spherePole n :=
  chart_symm_ne_pole n (ContinuousLinearEquiv.refl ℝ (V n)) p

theorem point_contMDiff (n : ℕ) : ContMDiff (𝓡 n) (𝓡 n) ∞ (point n) :=
  chart_symm_contMDiff n (ContinuousLinearEquiv.refl ℝ (V n))

theorem point_mfderiv_bijective (n : ℕ) (p : V n) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (point n) p) :=
  chart_symm_mfderiv_bijective n (ContinuousLinearEquiv.refl ℝ (V n)) p

theorem projection_contMDiffAt (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (sphereProjection n) x :=
  chart_contMDiffAt n (ContinuousLinearEquiv.refl ℝ (V n)) hx

theorem projection_mfderiv_bijective (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (sphereProjection n) x) :=
  chart_mfderiv_bijective n (ContinuousLinearEquiv.refl ℝ (V n)) hx

theorem projection_point (n : ℕ) (p : V n) : sphereProjection n (point n p) = p :=
  chart_right_inv n (ContinuousLinearEquiv.refl ℝ (V n)) p

theorem point_projection (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    point n (sphereProjection n x) = x :=
  (sphereProjection n).left_inv (by
    simpa only [sphereProjection_source, Set.mem_compl_iff, Set.mem_singleton_iff] using hx)

variable {m n : ℕ} (f : C(Sphere m, Sphere n))

def value (p : V m) : V n := sphereProjection n (f (point m p))

theorem value_contDiffAt (p : V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p))
    (hb : f (point m p) ≠ spherePole n) :
    ContDiffAt ℝ ∞ (value f) p := by
  have h := ((projection_contMDiffAt n hb).comp (point m p) hf).comp p
    (point_contMDiff m).contMDiffAt
  exact h.contDiffAt

theorem value_fderiv_surjective (p : V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p))
    (hb : f (point m p) ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f (point m p))) :
    Function.Surjective (fderiv ℝ (value f) p) := by
  have hp := (point_contMDiff m).mdifferentiable (by simp) p
  have hm := hf.mdifferentiableAt (by simp)
  have ht := (projection_contMDiffAt n hb).mdifferentiableAt (by simp)
  have h : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) (value f) p) := by
    change Function.Surjective (mfderiv (𝓡 m) (𝓡 n)
      (sphereProjection n ∘ (f ∘ point m)) p)
    rw [mfderiv_comp p ht (hm.comp p hp), mfderiv_comp p hm hp]
    exact (projection_mfderiv_bijective n hb).surjective.comp
      (hs.comp (point_mfderiv_bijective m p).surjective)
  exact (SphereChartRegularity.mfderiv_surjective_iff_fderiv (value f) p).mp h

def line : V m × ℝ → V n × ℝ := Prod.map (value f) id

theorem line_contDiffAt (p : V m × ℝ)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p.1))
    (hb : f (point m p.1) ≠ spherePole n) :
    ContDiffAt ℝ ∞ (line f) p :=
  (value_contDiffAt f p.1 hf hb).prodMap' contDiffAt_id

theorem line_fderiv_surjective (p : V m × ℝ)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p.1))
    (hb : f (point m p.1) ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f (point m p.1))) :
    Function.Surjective (fderiv ℝ (line f) p) := by
  have hd : fderiv ℝ (line f) p =
      (fderiv ℝ (value f) p.1).prodMap (ContinuousLinearMap.id ℝ ℝ) :=
    (HasFDerivAt.prodMap p
      ((value_contDiffAt f p.1 hf hb).differentiableAt (by simp)).hasFDerivAt
      (hasFDerivAt_id p.2)).fderiv
  rw [hd]
  intro z
  obtain ⟨w, hw⟩ := value_fderiv_surjective f p.1 hf hb hs z.1
  exact ⟨(w, z.2), Prod.ext hw rfl⟩

def square : V m × V m → V n × V n := Prod.map (value f) (value f)

theorem square_contDiffAt (p : V m × V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p.1))
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p.2))
    (hb : f (point m p.1) ≠ spherePole n)
    (hc : f (point m p.2) ≠ spherePole n) :
    ContDiffAt ℝ ∞ (square f) p :=
  (value_contDiffAt f p.1 hf hb).prodMap' (value_contDiffAt f p.2 hg hc)

theorem square_fderiv_surjective (p : V m × V m)
    (hf : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p.1))
    (hg : ContMDiffAt (𝓡 m) (𝓡 n) ∞ f (point m p.2))
    (hb : f (point m p.1) ≠ spherePole n)
    (hc : f (point m p.2) ≠ spherePole n)
    (hs : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f (point m p.1)))
    (ht : Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f (point m p.2))) :
    Function.Surjective (fderiv ℝ (square f) p) := by
  have hd : fderiv ℝ (square f) p =
      (fderiv ℝ (value f) p.1).prodMap (fderiv ℝ (value f) p.2) :=
    (HasFDerivAt.prodMap p
      ((value_contDiffAt f p.1 hf hb).differentiableAt (by simp)).hasFDerivAt
      ((value_contDiffAt f p.2 hg hc).differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hd]
  intro z
  obtain ⟨u, hu⟩ := value_fderiv_surjective f p.1 hf hb hs z.1
  obtain ⟨v, hv⟩ := value_fderiv_surjective f p.2 hg hc ht z.2
  exact ⟨(u, v), Prod.ext hu hv⟩

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteRepresentative

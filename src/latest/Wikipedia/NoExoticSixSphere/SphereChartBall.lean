import Wikipedia.NoExoticSixSphere.ManifoldAffineChartDomain

/-!
# Transporting a genuine coordinate ball to time times the original sphere

The whole coordinate ball is required to stay in the source chart target.
Its lifted map is smooth on the actual closed ball and is a closed embedding
when the original coordinate ball is one.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily

def liftChartBall (s : SourceChart) (b : Vector 4 → ℝ × Vector 3) (z : Vector 4) :
    ℝ × Sphere 3 := ((b z).1, s.symm (b z).2)

theorem contMDiffOn_liftChartBall (s : SourceChart) (b : Vector 4 → ℝ × Vector 3)
    (hb : ContDiffOn ℝ ∞ b (closedBall (0 : Vector 4) 1))
    (hs : ∀ z ∈ closedBall (0 : Vector 4) 1, (b z).2 ∈ s.target) :
    ContMDiffOn (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞ (liftChartBall s b)
      (closedBall (0 : Vector 4) 1) := by
  have ht := (contDiff_fst.comp_contDiffOn hb).contMDiffOn
  have hx := s.contMDiffOn_invFun.comp
    (contDiff_snd.comp_contDiffOn hb).contMDiffOn hs
  exact ht.prodMk hx

theorem liftChartBall_center (s : SourceChart) (b : Vector 4 → ℝ × Vector 3)
    (q : ℝ × Sphere 3) (hq : q.2 ∈ s.source) (hb : b 0 = (q.1, s q.2)) :
    liftChartBall s b 0 = q := by
  have hleft : s.symm (s q.2) = q.2 := s.left_inv hq
  simp only [liftChartBall, hb, hleft, Prod.eta]

theorem isClosedEmbedding_liftChartBall (s : SourceChart) (b : Vector 4 → ℝ × Vector 3)
    (hb : ContDiffOn ℝ ∞ b (closedBall (0 : Vector 4) 1))
    (hs : ∀ z ∈ closedBall (0 : Vector 4) 1, (b z).2 ∈ s.target)
    (hi : IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ b z.val)) :
    IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ liftChartBall s b z.val) := by
  have hc := (contMDiffOn_liftChartBall s b hb hs).continuousOn.domRestrict
  apply hc.isClosedEmbedding
  intro z w he
  apply hi.injective
  apply Prod.ext
  · exact congrArg (fun q : ℝ × Sphere 3 ↦ q.1) he
  · have hh := congrArg (fun q : ℝ × Sphere 3 ↦ s q.2) he
    have hz : s (s.symm (b z.val).2) = (b z.val).2 := s.right_inv (hs z.val z.property)
    have hw : s (s.symm (b w.val).2) = (b w.val).2 := s.right_inv (hs w.val w.property)
    change s (s.symm (b z.val).2) = s (s.symm (b w.val).2) at hh
    rwa [hz, hw] at hh

end NoExoticSixSphere.SphereFamily

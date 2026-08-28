import Wikipedia.NoExoticSixSphere.JamesSphereConeStageZero
import Wikipedia.NoExoticSixSphere.CompactAdjunctionGluing

/-!
# The actual inclusions between auxiliary James cone stages

The next quotient agrees with the original word inclusion on the
attaching boundary. Hence it descends to the preceding cone stage.
The exact quotient-fiber formulas prove that this continuous map is
injective, and compact Hausdorff separation makes it a closed embedding.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.ConeStage

def stepProduct (n k : ℕ) :
    C(ReducedCone.Space n × James.stage (spherePole n) k, Space n (k + 1)) :=
  (quotientMap n (k + 1)).comp
    ((ContinuousMap.id _).prodMap (StageAttachment.inclusion n k).hom)

def stepWords (n k : ℕ) : C(James.stage (spherePole n) (k + 1), Space n (k + 1)) :=
  (words n (k + 1)).comp (StageAttachment.inclusion n (k + 1)).hom

theorem step_compatible (n k : ℕ) (a : Sphere n × James.stage (spherePole n) k) :
    stepProduct n k ((data n k).embedding a) = stepWords n k ((data n k).attaching a) := by
  change quotientMap n (k + 1) (ReducedCone.boundary n a.1, StageAttachment.inclusion n k a.2) =
    words n (k + 1) (StageAttachment.inclusion n (k + 1) (stageAction n k a))
  rw [quotient_boundary]
  exact congrArg (words n (k + 1)) (stageAction_inclusion n k a.1 a.2).symm

def step (n k : ℕ) : C(Space n k, Space n (k + 1)) :=
  CompactAdjunction.glue (data n k) (stepProduct n k) (stepWords n k) (step_compatible n k)

theorem step_quotientMap (n k : ℕ) (c : ReducedCone.Space n)
    (w : James.stage (spherePole n) k) :
    step n k (quotientMap n k (c, w)) =
      quotientMap n (k + 1) (c, StageAttachment.inclusion n k w) :=
  CompactAdjunction.glue_quotientMap (data n k) (stepProduct n k) (stepWords n k)
    (step_compatible n k) (c, w)

theorem step_words (n k : ℕ) (w : James.stage (spherePole n) (k + 1)) :
    step n k (words n k w) = words n (k + 1) (StageAttachment.inclusion n (k + 1) w) := rfl

theorem step_injective (n k : ℕ) : Function.Injective (step n k) := by
  intro p q h
  obtain ⟨⟨c, w⟩, rfl⟩ := (quotientMap_isQuotientMap n k).surjective p
  obtain ⟨⟨d, v⟩, rfl⟩ := (quotientMap_isQuotientMap n k).surjective q
  rw [step_quotientMap, step_quotientMap] at h
  rcases (quotient_eq_iff n (k + 1) (c, StageAttachment.inclusion n k w)
    (d, StageAttachment.inclusion n k v)).mp h with he | ⟨a, b, ha, hb, hab⟩
  · have hc : c = d := congrArg Prod.fst he
    have hw : StageAttachment.inclusion n k w = StageAttachment.inclusion n k v :=
      congrArg Prod.snd he
    have hwv : w = v := (StageAttachment.isClosedEmbedding n k).injective hw
    exact congrArg (quotientMap n k) (Prod.ext hc hwv)
  · have hac : ReducedCone.boundary n a.1 = c := congrArg Prod.fst ha
    have hbd : ReducedCone.boundary n b.1 = d := congrArg Prod.fst hb
    have haw : a.2 = StageAttachment.inclusion n k w := congrArg Prod.snd ha
    have hbv : b.2 = StageAttachment.inclusion n k v := congrArg Prod.snd hb
    have hea : a = (a.1, StageAttachment.inclusion n k w) := Prod.ext rfl haw
    have heb : b = (b.1, StageAttachment.inclusion n k v) := Prod.ext rfl hbv
    have hh : stageAction n (k + 1) (a.1, StageAttachment.inclusion n k w) =
        stageAction n (k + 1) (b.1, StageAttachment.inclusion n k v) := by
      calc
        stageAction n (k + 1) (a.1, StageAttachment.inclusion n k w) =
            stageAction n (k + 1) a := congrArg (stageAction n (k + 1)) hea.symm
        _ = stageAction n (k + 1) b := hab
        _ = stageAction n (k + 1) (b.1, StageAttachment.inclusion n k v) :=
          congrArg (stageAction n (k + 1)) heb
    have heq : StageAttachment.inclusion n (k + 1) (stageAction n k (a.1, w)) =
        StageAttachment.inclusion n (k + 1) (stageAction n k (b.1, v)) :=
      (stageAction_inclusion n k a.1 w).trans (hh.trans (stageAction_inclusion n k b.1 v).symm)
    have hact : stageAction n k (a.1, w) = stageAction n k (b.1, v) :=
      (StageAttachment.isClosedEmbedding n (k + 1)).injective heq
    exact (quotient_eq_iff n k (c, w) (d, v)).mpr
      (Or.inr ⟨(a.1, w), (b.1, v), Prod.ext hac rfl, Prod.ext hbd rfl, hact⟩)

theorem step_isClosedEmbedding (n k : ℕ) : IsClosedEmbedding (step n k) :=
  (step n k).continuous.isClosedEmbedding (step_injective n k)

def stepHomeomorph (n k : ℕ) : Space n k ≃ₜ Set.range (step n k) :=
  (step_isClosedEmbedding n k).isEmbedding.toHomeomorph

end NoExoticSixSphere.JamesSphere.ConeStage

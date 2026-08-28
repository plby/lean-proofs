import Wikipedia.NoExoticSixSphere.FamilyFlatteningPairCoordinates
import Wikipedia.NoExoticSixSphere.FamilyDoublePointClosure

/-!
# Shared-time pairs and the actual track double-point closure

The closed track double-point set has equal time coordinates. Inserting a
shared time and recovering it therefore give a homeomorphism with the
original family double-point closure, together with smooth ambient maps.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilySharedTimePairs

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def toTrack (q : T × ((E × ℝ) × (E × ℝ))) : (E × (T × ℝ)) × (E × (T × ℝ)) :=
  ((q.2.1.1, (q.1, q.2.1.2)), (q.2.2.1, (q.1, q.2.2.2)))

def fromTrack (r : (E × (T × ℝ)) × (E × (T × ℝ))) : T × ((E × ℝ) × (E × ℝ)) :=
  (r.1.2.1, ((r.1.1, r.1.2.2), (r.2.1, r.2.2.2)))

theorem contDiff_toTrack : ContDiff ℝ ∞ (toTrack (T := T) (E := E)) :=
  (contDiff_snd.fst.fst.prodMk (contDiff_fst.prodMk contDiff_snd.fst.snd)).prodMk
    (contDiff_snd.snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.snd))

theorem contDiff_fromTrack : ContDiff ℝ ∞ (fromTrack (T := T) (E := E)) :=
  contDiff_fst.snd.fst.prodMk
    ((contDiff_fst.fst.prodMk contDiff_fst.snd.snd).prodMk
      (contDiff_snd.fst.prodMk contDiff_snd.snd.snd))

omit [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem fromTrack_toTrack (q : T × ((E × ℝ) × (E × ℝ))) : fromTrack (toTrack q) = q := rfl

omit [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem toTrack_fromTrack (r : (E × (T × ℝ)) × (E × (T × ℝ)))
    (ht : r.1.2.1 = r.2.2.1) : toTrack (fromTrack r) = r := by
  rcases r with ⟨⟨x, t, z⟩, ⟨y, u, w⟩⟩
  change t = u at ht
  subst u
  rfl

omit [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem toTrack_doublePoints (f : T → E × ℝ → E × F) :
    MapsTo toTrack (FamilyEmbedding.doublePoints f) (FamilyFlattening.trackDoublePoints f) := by
  intro q hq
  refine ⟨?_, ?_⟩
  · intro he
    exact hq.1 (congrArg (fun r : E × (T × ℝ) ↦ (r.1, r.2.2)) he)
  · exact Prod.ext (Prod.ext rfl (congrArg (fun v : E × F ↦ v.1) hq.2))
      (congrArg (fun v : E × F ↦ v.2) hq.2)

omit [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem fromTrack_doublePoints (f : T → E × ℝ → E × F) :
    MapsTo fromTrack (FamilyFlattening.trackDoublePoints f) (FamilyEmbedding.doublePoints f) := by
  rintro ⟨⟨x, t, z⟩, ⟨y, u, w⟩⟩ hr
  have ht : t = u := congrArg (fun v : (T × E) × F ↦ v.1.1) hr.2
  subst u
  refine ⟨?_, ?_⟩
  · intro he
    apply hr.1
    change (x, z) = (y, w) at he
    change (x, (t, z)) = (y, (t, w))
    exact Prod.ext (congrArg (fun v : E × ℝ ↦ v.1) he)
      (Prod.ext rfl (congrArg (fun v : E × ℝ ↦ v.2) he))
  · exact congrArg (fun v : (T × E) × F ↦ (v.1.2, v.2)) hr.2

def closedToTrack (f : T → E × ℝ → E × F) :
    closure (FamilyEmbedding.doublePoints f) → closure (FamilyFlattening.trackDoublePoints f) :=
  fun q ↦ ⟨toTrack q.val, (toTrack_doublePoints f).closure contDiff_toTrack.continuous q.property⟩

def closedFromTrack (f : T → E × ℝ → E × F) :
    closure (FamilyFlattening.trackDoublePoints f) → closure (FamilyEmbedding.doublePoints f) :=
  fun q ↦ ⟨fromTrack q.val,
    (fromTrack_doublePoints f).closure contDiff_fromTrack.continuous q.property⟩

def closedPairHomeomorph (f : T → E × ℝ → E × F) :
    closure (FamilyEmbedding.doublePoints f) ≃ₜ closure (FamilyFlattening.trackDoublePoints f) where
  toFun := closedToTrack f
  invFun := closedFromTrack f
  left_inv q := Subtype.ext (fromTrack_toTrack q.val)
  right_inv q := Subtype.ext
    (toTrack_fromTrack q.val (FamilyFlattening.closedTrackDoublePoints_time_eq q.property))
  continuous_toFun := (contDiff_toTrack.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (contDiff_fromTrack.continuous.comp continuous_subtype_val).subtype_mk _

end NoExoticSixSphere.FamilySharedTimePairs

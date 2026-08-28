import Wikipedia.HopfProblem.SpecialPeriodsThreefold

/-!
# Gluing fibre-preserving flows through the actual four-piece construction

Only local maps and their checked agreement on the three original
filling-to-regular overlaps are inputs.  The full transition compatibility,
global map, and action identities are derived in the already constructed
topological gluing.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Gluing

attribute [local instance] localPieceChartedSpace

variable (F : ∀ i : Index, ℂ → localPiece i → localPiece i)
  (hbase : ∀ i s x, localProjectionToBase i (F i s x) = localProjectionToBase i x)
  (hoverlap : ∀ i s x, x ∈ (localOverlap i).source →
    localOverlap i (F (some i) s x) = F none s (localOverlap i x))

include hbase in
theorem localFlow_mem_overlap (i : Puncture) (s : ℂ) (x : localPiece (some i))
    (hx : x ∈ (localOverlap i).source) : F (some i) s x ∈ (localOverlap i).source := by
  rw [localOverlap_source] at hx ⊢
  change localProjectionToBase (some i) (F (some i) s x) ∈ specialBaseCover.patch none
  rw [hbase]
  exact hx

theorem inclusion_localOverlap (i : Puncture) (x : localPiece (some i))
    (hx : x ∈ (localOverlap i).source) :
    inclusion none (localOverlap i x) = inclusion (some i) x :=
  ((gluingData.inclusion_eq_iff (some i) none x (localOverlap i x)).mpr ⟨hx, rfl⟩).symm

include hbase hoverlap in
/-- The actual star geometry reduces all transition agreements to the
three supplied filling-to-regular equalities. -/
theorem compatible (s : ℂ) :
    gluingData.Compatible (fun i x => inclusion i (F i s x)) := by
  intro i j x hx
  by_cases hij : i = j
  · subst j
    change inclusion i (F i s (gluingData.transition i i x)) = inclusion i (F i s x)
    rw [gluingData.self_eq]
    rfl
  · cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j =>
            change x ∈ (localOverlap j).target at hx
            change inclusion (some j) (F (some j) s ((localOverlap j).symm x)) =
              inclusion none (F none s x)
            have hy := (localOverlap j).map_target hx
            calc
              inclusion (some j) (F (some j) s ((localOverlap j).symm x)) =
                  inclusion none
                    (localOverlap j (F (some j) s ((localOverlap j).symm x))) :=
                (inclusion_localOverlap j _ (localFlow_mem_overlap F hbase j s _ hy)).symm
              _ = inclusion none (F none s (localOverlap j ((localOverlap j).symm x))) :=
                congrArg (inclusion none) (hoverlap j s _ hy)
              _ = inclusion none (F none s x) :=
                congrArg (fun y => inclusion none (F none s y)) ((localOverlap j).right_inv hx)
    | some i =>
        cases j with
        | none =>
            change x ∈ (localOverlap i).source at hx
            change inclusion none (F none s (localOverlap i x)) = inclusion (some i) (F (some i) s x)
            rw [← hoverlap i s x hx]
            exact inclusion_localOverlap i _ (localFlow_mem_overlap F hbase i s x hx)
        | some j =>
            have hij' : i ≠ j := fun h => hij (congrArg some h)
            change x ∈ (gluingStar.transition (some i) (some j)).source at hx
            rw [gluingStar.transition_some_some_source_eq_empty hij'] at hx
            exact hx.elim

/-- The genuine globally defined map on the original glued space. -/
def glue (s : ℂ) : Space → Space :=
  gluingData.descend (fun i x => inclusion i (F i s x)) (compatible F hbase hoverlap s)

@[simp] theorem glue_inclusion (s : ℂ) (i : Index) (x : localPiece i) :
    glue F hbase hoverlap s (inclusion i x) = inclusion i (F i s x) :=
  gluingData.descend_inclusion _ (compatible F hbase hoverlap s) i x

theorem glue_projection (s : ℂ) (x : Space) :
    projection (glue F hbase hoverlap s x) = projection x := by
  obtain ⟨i, x, rfl⟩ := gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, projection_inclusion, projection_inclusion, hbase]

theorem glue_zero (hzero : ∀ i x, F i 0 x = x) (x : Space) :
    glue F hbase hoverlap 0 x = x := by
  obtain ⟨i, x, rfl⟩ := gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, hzero]

theorem glue_add (hadd : ∀ i s t x, F i (s + t) x = F i s (F i t x))
    (s t : ℂ) (x : Space) :
    glue F hbase hoverlap (s + t) x =
      glue F hbase hoverlap s (glue F hbase hoverlap t x) := by
  obtain ⟨i, x, rfl⟩ := gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, glue_inclusion, glue_inclusion, hadd]

theorem glue_int_cast (hint : ∀ i (n : ℤ) x, F i (n : ℂ) x = x)
    (n : ℤ) (x : Space) : glue F hbase hoverlap (n : ℂ) x = x := by
  obtain ⟨i, x, rfl⟩ := gluingData.inclusion_jointly_surjective x
  rw [glue_inclusion, hint]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Gluing

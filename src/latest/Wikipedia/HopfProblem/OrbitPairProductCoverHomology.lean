import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Homology projection through a product cover with contractible pieces

For a two-set cover of the first factor by contractible open sets, the
second projection is an isomorphism in degree n+1 whenever the product
overlap has zero homology in degree n. The proof retains the literal
projection and fixed section; it uses the actual Mayer--Vietoris maps.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.OrbitPair.ProductCover

open SingularMayerVietoris PeriodTorusHigherHomology

variable {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]

abbrev piece (U : Set Y) : Set (Y × X) := Prod.fst ⁻¹' U

def pieceHomeomorph (U : Set Y) : piece (X := X) U ≃ₜ U × X where
  toFun p := (⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk
    continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

def projection (U : Set Y) : C(piece (X := X) U, X) :=
  ⟨fun p => p.val.2, continuous_subtype_val.snd⟩

def fixedSection (U : Set Y) (u : U) : C(X, piece (X := X) U) :=
  ⟨fun x => ⟨(u.val, x), u.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

def pieceHomotopyEquiv (U : Set Y) [ContractibleSpace U] : piece (X := X) U ≃ₕ X :=
  (pieceHomeomorph U).toHomotopyEquiv.trans
    (CircleTopology.contractibleProdHomotopyEquiv U X)

def pieceHomologyEquiv (U : Set Y) [ContractibleSpace U] (n : ℕ) :
    SingularHomology (piece (X := X) U) n ≃ₗ[ℤ] SingularHomology X n :=
  homotopyEquivHomologyEquiv (pieceHomotopyEquiv U) n

@[simp] theorem pieceHomologyEquiv_apply (U : Set Y) [ContractibleSpace U] (n : ℕ)
    (a : SingularHomology (piece (X := X) U) n) :
    pieceHomologyEquiv U n a = singularHomologyMap (projection U) n a := rfl

theorem projection_section (U : Set Y) (u : U) (n : ℕ)
    (a : SingularHomology X n) :
    singularHomologyMap (projection U) n (singularHomologyMap (fixedSection U u) n a) = a := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  change singularHomologyMap (ContinuousMap.id X) n a = a
  rw [singularHomologyMap_id]
  rfl

theorem piece_open (U : Set Y) (hU : IsOpen U) : IsOpen (piece (X := X) U) :=
  hU.preimage continuous_fst

theorem piece_cover (U V : Set Y) (hc : U ∪ V = univ) :
    piece (X := X) U ∪ piece V = univ := by
  rw [piece, piece, ← preimage_union, hc, preimage_univ]

def overlapHomeomorph (U V : Set Y) :
    (piece (X := X) U ∩ piece V : Set (Y × X)) ≃ₜ (U ∩ V : Set Y) × X :=
  pieceHomeomorph (U ∩ V)

def overlapSection (U V : Set Y) (u : (U ∩ V : Set Y)) :
    C(X, (piece (X := X) U ∩ piece V : Set (Y × X))) :=
  ⟨fun x => ⟨(u.val, x), u.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

theorem projection_right (U V : Set Y) [ContractibleSpace U] [ContractibleSpace V]
    (n : ℕ) (p : SingularHomology (piece (X := X) U) n ×
      SingularHomology (piece (X := X) V) n) :
    singularHomologyMap ContinuousMap.snd n (rightHomologyMap (piece U) (piece V) n p) =
      pieceHomologyEquiv U n p.1 + pieceHomologyEquiv V n p.2 := by
  rw [rightHomologyMap_apply, map_add]
  congr 1 <;> rw [← LinearMap.comp_apply, ← singularHomologyMap_comp] <;> rfl

theorem projection_inclusion (U V : Set Y) (hUV : U ⊆ V) (n : ℕ)
    (a : SingularHomology (piece (X := X) U) n) :
    singularHomologyMap (projection V) n
      (singularHomologyMap (ContinuousMap.inclusion (preimage_mono hUV)) n a) =
        singularHomologyMap (projection U) n a := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem snd_homology_bijective (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hc : U ∪ V = univ) [ContractibleSpace U] [ContractibleSpace V]
    (u : (U ∩ V : Set Y)) (n : ℕ)
    [Subsingleton (SingularHomology (piece (X := X) U ∩ piece V : Set (Y × X)) n)] :
    Function.Bijective (singularHomologyMap (ContinuousMap.snd : C(Y × X, X)) (n + 1)) := by
  have hp := piece_cover (X := X) U V hc
  have hU' := piece_open (X := X) U hU
  have hV' := piece_open (X := X) V hV
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro a ha
    have ha' : singularHomologyMap (ContinuousMap.snd : C(Y × X, X)) (n + 1) a = 0 := ha
    have hz : a ∈ LinearMap.ker (connectingHomomorphism (piece U) (piece V) hU' hV' hp n) :=
      Subsingleton.elim _ _
    rw [← exact_at_ambient (piece U) (piece V) hU' hV' hp n] at hz
    obtain ⟨p, rfl⟩ := hz
    rw [projection_right] at ha'
    let b := singularHomologyMap (overlapSection U V u) (n + 1)
      (pieceHomologyEquiv U (n + 1) p.1)
    have hb : leftHomologyMap (piece U) (piece V) (n + 1) b = p := by
      rw [leftHomologyMap_apply]
      apply Prod.ext
      · apply (pieceHomologyEquiv U (n + 1)).injective
        change singularHomologyMap (projection U) (n + 1)
          (singularHomologyMap (ContinuousMap.inclusion _) (n + 1) b) = _
        change singularHomologyMap (projection U) (n + 1)
          (singularHomologyMap _ (n + 1)
            (singularHomologyMap (overlapSection U V u) (n + 1) _)) = _
        rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
          ← LinearMap.comp_apply, ← singularHomologyMap_comp]
        change singularHomologyMap (ContinuousMap.id X) (n + 1) _ = _
        rw [singularHomologyMap_id]
        rfl
      · apply (pieceHomologyEquiv V (n + 1)).injective
        rw [map_neg]
        change -(singularHomologyMap (projection V) (n + 1)
          (singularHomologyMap (ContinuousMap.inclusion _) (n + 1) b)) = _
        change -(singularHomologyMap (projection V) (n + 1)
          (singularHomologyMap _ (n + 1)
            (singularHomologyMap (overlapSection U V u) (n + 1) _))) = _
        rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
          ← LinearMap.comp_apply, ← singularHomologyMap_comp]
        change -(singularHomologyMap (ContinuousMap.id X) (n + 1) _) = _
        rw [singularHomologyMap_id]
        exact (neg_eq_iff_add_eq_zero).mpr ha'
    rw [← hb]
    exact LinearMap.congr_fun (leftHomologyMap_comp_right (piece U) (piece V) (n + 1)) b
  · intro a
    let s : C(X, Y × X) := (ContinuousMap.const X u.val).prodMk (ContinuousMap.id X)
    refine ⟨singularHomologyMap s (n + 1) a, ?_⟩
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (ContinuousMap.id X) (n + 1) a = a
    rw [singularHomologyMap_id]
    rfl

variable {Z : Type} [TopologicalSpace Z]

theorem snd_homology_bijective_homeomorph (e : Y ≃ₜ Z) (n : ℕ)
    (h : Function.Bijective (singularHomologyMap (ContinuousMap.snd : C(Y × X, X)) n)) :
    Function.Bijective (singularHomologyMap (ContinuousMap.snd : C(Z × X, X)) n) := by
  let E := homeomorphHomologyEquiv (e.prodCongr (Homeomorph.refl X)) n
  have he (a : SingularHomology (Y × X) n) :
      singularHomologyMap (ContinuousMap.snd : C(Z × X, X)) n (E a) =
        singularHomologyMap ContinuousMap.snd n a := by
    change singularHomologyMap _ n (singularHomologyMap _ n a) = _
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
    rfl
  constructor
  · intro a b hab
    apply E.symm.injective
    apply h.1
    rw [← he, ← he, E.apply_symm_apply, E.apply_symm_apply]
    exact hab
  · intro a
    obtain ⟨b, hb⟩ := h.2 a
    exact ⟨E b, (he b).trans hb⟩

end Wikipedia.HopfProblem.OrbitPair.ProductCover

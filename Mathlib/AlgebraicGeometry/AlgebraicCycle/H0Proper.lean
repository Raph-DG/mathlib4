/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.PrincipalPartsSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Finiteness of `H⁰(X, 𝒪ₓ)` for a curve proper over a field

Let `X` be an integral Noetherian scheme, regular in codimension one, of Krull dimension at
most one, whose structure morphism to `Spec k` is universally closed (e.g. `X` proper over
`k`) and locally of finite type. This file proves that the global sections of the divisorial
structure sheaf `𝒪ₓ = 𝒪ₓ(0)` — the space `L(0)` of rational functions with everywhere
nonnegative order of vanishing — form a finite-dimensional `k`-vector space, and hence that
`H⁰(X, 𝒪ₓ)` is finite dimensional, discharging the `h0` hypothesis of
`riemann_roch_of_finite_H0_H1`.

## Strategy

* **Center of a valuation** (`exists_factor_stalk_of_universallyClosed`): for a valuation
  subring `V` of the function field `K` containing (the image of) `k`, the valuative
  criterion applied to the universally closed structure morphism produces a lift
  `Spec V ⟶ X` of the canonical `Spec K ⟶ X`, i.e. a point `x : X` and a factorization
  `𝒪_{X,x} ⟶ V ⟶ K` of the canonical map to the function field.
* **Algebraicity** (`isIntegral_of_forall_ord_nonneg`): if `f ∈ K` has `ord_z f ≥ 0` at
  every codimension-one point `z`, then `f` lies in every valuation subring `V ⊇ k`: the
  center `x` of `V` has coheight `0` or `1` (Krull dimension one); in the first case `x` is
  the generic point and `𝒪_{X,x} = K`, in the second `𝒪_{X,x}` is a DVR and `ord_x f ≥ 0`
  puts `f` inside it. By the characterization of integral closures as intersections of
  valuation subrings (Stacks 090P), `f` is integral over `k`.
* **Finiteness** (`finite_regularFunctions`): `L(0)` is consequently an algebraic
  subalgebra of the field `K`, hence itself a field; evaluating at a closed point `p`
  (which exists: either some codimension-one point, which is closed, or `X` is a single
  point) embeds `L(0)` `k`-linearly into the residue field `κ(p)`, which is
  finite-dimensional over `k` by Zariski's lemma (`finite_residueField_of_isClosed`).
* **Transport to cohomology** (`finite_H0_structureSheaf`): `H⁰` of any sheaf of modules is
  its space of global sections (`Sheaf.H.equiv₀`), and for the submodule design the global
  sections of `𝒪ₓ(0)` evaluate isomorphically (and `k`-linearly) onto `L(0)`.

Together with the flasque resolution of `PrincipalPartsSheaf.lean`, this reduces
Riemann–Roch for such an `X` to the finiteness of `H¹(X, 𝒪ₓ)` alone
(`riemann_roch_of_universallyClosed_of_finite_H1`).
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits Order Opposite
  TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

/-! ### The function field as a `k`-algebra -/

section ConstantsAlgebra

variable [IrreducibleSpace X]

/-- On an irreducible (hence nonempty) space, the top open is nonempty. -/
instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

variable (X) in
/-- The composite `k ⟶ Γ(X, ⊤) ⟶ k(X)`: constants as rational functions. -/
noncomputable def constantsToFunctionField : k →+* ↑X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
    (globalSec (X := X) (R := CommRingCat.of k))

/-- The function field of a scheme over `k` is a `k`-algebra via
`constantsToFunctionField`. -/
noncomputable instance : Algebra k ↑X.functionField :=
  (constantsToFunctionField X k).toAlgebra

lemma algebraMap_functionField_eq :
    algebraMap k ↑X.functionField = constantsToFunctionField X k := rfl

lemma algebraMap_functionField_eq_germ (r : k) :
    algebraMap k ↑X.functionField r =
      X.presheaf.germ ⊤ (genericPoint X) trivial
        (globalSec (X := X) (R := CommRingCat.of k) r) := rfl

omit k in
/-- On an irreducible sober space, a point of coheight zero is the generic point. -/
lemma eq_genericPoint_of_coheight_eq_zero {x : X} (hx : coheight x = 0) :
    x = genericPoint X := by
  have hle : x ≤ genericPoint X :=
    Scheme.le_iff_specializes.mpr ((genericPoint_spec X).specializes trivial)
  have hge : genericPoint X ≤ x := (Order.coheight_eq_zero.mp hx) hle
  exact (((Scheme.le_iff_specializes.mp hle).antisymm
    (Scheme.le_iff_specializes.mp hge)).eq).symm

omit k in
/-- On a scheme of Krull dimension at most one, every point has coheight at most one. -/
lemma coheight_le_one [Order.KrullDimLE 1 X] (x : X) : coheight x ≤ 1 := by
  have h1 := Order.coheight_le_krullDim (a := x)
  have h2 : Order.krullDim X ≤ (1 : ℕ) := Order.KrullDimLE.krullDim_le
  exact_mod_cast h1.trans h2

end ConstantsAlgebra

/-! ### Rational functions of nonnegative order lie in the stalks -/

section StalkMembership

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

/-- Elements of (the image of) a codimension-one stalk have nonnegative order. -/
lemma ord_nonneg_of_mem_range_algebraMap_stalk {z : X} (hz : coheight z = 1)
    {f : ↑X.functionField}
    (hf : f ∈ Set.range (algebraMap ↑(X.presheaf.stalk z) ↑X.functionField)) :
    0 ≤ X.ord f z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · exact (mem_range_algebraMap_iff_ord_nonneg hz f).mp hf hf0

/-- Germs of sections have nonnegative order at every codimension-one point of their
domain. -/
lemma ord_germToFunctionField_nonneg {U : X.Opens} [Nonempty U] (g : Γ(X, U)) {z : X}
    (hz : coheight z = 1) (hzU : z ∈ U) :
    0 ≤ X.ord (X.germToFunctionField U g) z :=
  ord_nonneg_of_mem_range_algebraMap_stalk hz
    ⟨X.presheaf.germ U z hzU g, Scheme.algebraMap_germ_eq_germToFunctionField hzU g⟩

variable [Order.KrullDimLE 1 X]

/-- On a curve (Krull dimension at most one), a rational function with nonnegative order at
every codimension-one point lies in the image of **every** stalk: the stalk at a
codimension-one point by the DVR bound, and the stalk at the generic point trivially. -/
lemma mem_range_algebraMap_stalk_of_forall_ord_nonneg (x : X) {f : ↑X.functionField}
    (hf : ∀ z, coheight z = 1 → 0 ≤ X.ord f z) :
    f ∈ Set.range (algebraMap ↑(X.presheaf.stalk x) ↑X.functionField) := by
  rcases Order.le_one_iff.mp (coheight_le_one x) with h | h
  · -- coheight 0: `x` is the generic point, whose stalk is the function field.
    obtain rfl := eq_genericPoint_of_coheight_eq_zero h
    refine ⟨f, ?_⟩
    rw [RingHom.algebraMap_toAlgebra]
    change (X.presheaf.stalkSpecializes _).hom f = f
    rw [TopCat.Presheaf.stalkSpecializes_refl (X.presheaf) (genericPoint X)]
    rfl
  · exact (mem_range_algebraMap_iff_ord_nonneg h f).mpr fun _ => hf x h

end StalkMembership

/-! ### The center of a valuation on the function field -/

section Center

variable [IsIntegral X]

/-- **The center of a valuation.** If the structure morphism `X ⟶ Spec k` is universally
closed, then every valuation subring `V` of the function field containing the constants has
a center on `X`: a point `x` and a factorization `𝒪_{X,x} ⟶ V ⟶ K` of the canonical map
from the stalk to the function field. This is the existence half of the valuative
criterion. -/
lemma exists_factor_stalk_of_universallyClosed
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (V : ValuationSubring ↑X.functionField)
    (hV : Set.range (algebraMap k ↑X.functionField) ⊆ (V : Set ↑X.functionField)) :
    ∃ (x : X) (φ : ↑(X.presheaf.stalk x) →+* V),
      (algebraMap V ↑X.functionField).comp φ =
        algebraMap ↑(X.presheaf.stalk x) ↑X.functionField := by
  -- The valuative square for `V ⊆ K` over `k ⟶ K`.
  letI : Algebra k V :=
    (((algebraMap k ↑X.functionField).codRestrict V.toSubring
      (fun r => hV ⟨r, rfl⟩))).toAlgebra
  let S : ValuativeCommSq (X ↘ Spec (CommRingCat.of k)) :=
    { R := V
      K := ↑X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k V))
      commSq := by
        constructor
        have h1 : (X ↘ Spec (CommRingCat.of k)) =
            X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (globalSec (X := X)
              (R := CommRingCat.of k))) := by
          have := Scheme.toSpecΓ_naturality (X ↘ Spec (CommRingCat.of k))
          rw [← Category.comp_id (X ↘ Spec (CommRingCat.of k)),
            ← toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of k), ← Category.assoc, this,
            Category.assoc, ← Spec.map_comp]
          rfl
        rw [h1, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp, ← Spec.map_comp]
        congr 1 }
  -- Universal closedness gives the existence part of the valuative criterion.
  have hexist : ValuativeCriterion.Existence (X ↘ Spec (CommRingCat.of k)) := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) (X ↘ Spec (CommRingCat.of k)) := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  obtain ⟨⟨ℓ, hfac, -⟩⟩ := (hexist S).exists_lift
  -- The center is the image of the closed point; the stalk map factors the canonical map.
  refine ⟨ℓ (IsLocalRing.closedPoint V), (Scheme.stalkClosedPointTo ℓ).hom, ?_⟩
  have key : Scheme.stalkClosedPointTo ℓ ≫
      CommRingCat.ofHom (algebraMap V ↑X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    -- Both sides become equal after `Spec` and composition with the mono `fromSpecStalk`.
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ℓ (IsLocalRing.closedPoint V)))]
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ]
    rw [SpecMap_stalkSpecializes_fromSpecStalk]
    exact hfac
  ext g
  have := congrArg (fun (ψ : X.presheaf.stalk _ ⟶ X.functionField) => ψ.hom g) key
  simpa [RingHom.algebraMap_toAlgebra] using this

end Center

/-! ### Algebraicity of everywhere-regular rational functions -/

section Algebraicity

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
  [Order.KrullDimLE 1 X]

/-- A rational function of everywhere nonnegative order lies in every valuation subring of
the function field containing the constants, provided the structure morphism is universally
closed: it lies in the stalk at the center of the valuation. -/
lemma mem_valuationSubring_of_forall_ord_nonneg
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    {f : ↑X.functionField} (hf : ∀ z, coheight z = 1 → 0 ≤ X.ord f z)
    (V : ValuationSubring ↑X.functionField)
    (hV : Set.range (algebraMap k ↑X.functionField) ⊆ (V : Set ↑X.functionField)) :
    f ∈ V := by
  obtain ⟨x, φ, hφ⟩ := exists_factor_stalk_of_universallyClosed k V hV
  obtain ⟨g, rfl⟩ := mem_range_algebraMap_stalk_of_forall_ord_nonneg x hf
  rw [← hφ]
  exact (φ g).2

/-- **Algebraicity.** On a curve universally closed over `k`, a rational function of
everywhere nonnegative order is integral (equivalently, algebraic) over the constants:
it lies in every valuation subring containing `k`, and the integral closure is the
intersection of these (Stacks 090P). -/
lemma isIntegral_of_forall_ord_nonneg
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    {f : ↑X.functionField} (hf : ∀ z, coheight z = 1 → 0 ≤ X.ord f z) :
    _root_.IsIntegral k f := by
  -- membership in the integral closure of the image subring
  have hmem : f ∈ integralClosure
      (Subring.closure (Set.range (algebraMap k ↑X.functionField))) ↑X.functionField := by
    have h := iInf_valuationSubring_superset
      (s := Set.range (algebraMap k ↑X.functionField)) (K := ↑X.functionField)
    have hf' : f ∈ ⨅ V : {V : ValuationSubring ↑X.functionField //
        Set.range (algebraMap k ↑X.functionField) ⊆ V.toSubring}, V.1.toSubring := by
      rw [Subring.mem_iInf]
      exact fun V => mem_valuationSubring_of_forall_ord_nonneg k hf V.1 V.2
    rw [h] at hf'
    exact hf'
  -- transfer integrality over the image subring to integrality over `k`
  set R : Subring ↑X.functionField := (algebraMap k ↑X.functionField).range with hR
  have hclos : Subring.closure (Set.range (algebraMap k ↑X.functionField)) = R := by
    rw [hR, ← RingHom.coe_range, Subring.closure_eq]
  rw [hclos] at hmem
  letI : Algebra k R := ((algebraMap k ↑X.functionField).rangeRestrict).toAlgebra
  haveI : IsScalarTower k R ↑X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral k R :=
    Algebra.isIntegral_of_surjective
      (RingHom.rangeRestrict_surjective (algebraMap k ↑X.functionField))
  exact isIntegral_trans f hmem

end Algebraicity

/-! ### `L(0)` as a subalgebra of the function field -/

section RegularFunctions

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

variable (X) in
/-- The space `L(0)` of rational functions of everywhere nonnegative order — the global
sections of the divisorial structure sheaf `𝒪ₓ(0)` — as a `k`-subalgebra of the function
field. -/
noncomputable def regularFunctions : Subalgebra k ↑X.functionField where
  carrier := Sheaf.carrier (0 : AlgebraicCycle X ℤ) ⊤
  add_mem' := Sheaf.add_mem' 0 ⊤
  zero_mem' := Sheaf.zero_mem' 0 ⊤
  mul_mem' {f g} hf hg := Sheaf.mem_carrier_iff.mpr fun hfg => by
    have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg
    have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg
    refine ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z hz => ?_⟩
    by_cases hz1 : coheight z = 1
    · have h1 := (Sheaf.mem_carrier_iff.mp hf hf0).2 z hz
      have h2 := (Sheaf.mem_carrier_iff.mp hg hg0).2 z hz
      rw [ord_mul hz1 hf0 hg0]
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, add_zero] at h1 h2 ⊢
      omega
    · simp [ord_eq_zero_of_coheight_neq_one hz1]
  one_mem' := Sheaf.mem_carrier_iff.mpr fun _ => by
    refine ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z hz => ?_⟩
    by_cases hz1 : coheight z = 1
    · have h1 : X.ord 1 z = 0 := by
        rw [ord_eq_iff hz1 one_ne_zero]
        simp
      simp [h1]
    · simp [ord_eq_zero_of_coheight_neq_one hz1]
  algebraMap_mem' r := Sheaf.mem_carrier_iff.mpr fun _ => by
    refine ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z hz => ?_⟩
    by_cases hz1 : coheight z = 1
    · have h := ord_nonneg_of_mem_range_algebraMap_stalk
        (f := algebraMap k ↑X.functionField r) hz1
        ⟨X.presheaf.germ ⊤ z trivial
          (globalSec (X := X) (R := CommRingCat.of k) r), by
            rw [Scheme.algebraMap_germ_eq_germToFunctionField]
            rfl⟩
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, add_zero]
      omega
    · simp [ord_eq_zero_of_coheight_neq_one hz1]

lemma mem_regularFunctions_iff {f : ↑X.functionField} :
    f ∈ regularFunctions X k ↔ f ∈ Sheaf.carrier (0 : AlgebraicCycle X ℤ) ⊤ := Iff.rfl

/-- Elements of `L(0)` have nonnegative order at every codimension-one point. -/
lemma ord_nonneg_of_mem_regularFunctions {f : ↑X.functionField}
    (hf : f ∈ regularFunctions X k) {z : X} (hz : coheight z = 1) :
    0 ≤ X.ord f z := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · have h := (Sheaf.mem_carrier_iff.mp hf hf0).2 z trivial
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, add_zero] at h
    exact h

variable [Order.KrullDimLE 1 X]

/-- On a curve universally closed over `k`, `L(0)` is a field: each of its nonzero elements
is algebraic over `k`, so its inverse is a polynomial in it and again lies in `L(0)`. -/
lemma isField_regularFunctions [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    IsField (regularFunctions X k) := by
  refine ⟨⟨0, 1, fun h => by simpa using congrArg Subtype.val h⟩,
    mul_comm, fun {a} ha => ?_⟩
  have halg : IsAlgebraic k (a : ↑X.functionField) :=
    (isIntegral_of_forall_ord_nonneg k
      (fun z hz => ord_nonneg_of_mem_regularFunctions k a.2 hz)).isAlgebraic
  have hmem : ((a : ↑X.functionField)⁻¹) ∈ regularFunctions X k :=
    Subalgebra.inv_mem_of_algebraic (A := regularFunctions X k) (x := a) halg
  refine ⟨⟨(a : ↑X.functionField)⁻¹, hmem⟩, ?_⟩
  have ha0 : (a : ↑X.functionField) ≠ 0 := fun h => ha (Subtype.ext h)
  exact Subtype.ext (mul_inv_cancel₀ ha0)

/-- There is a closed point: any codimension-one point is closed, and if there is none, the
curve is a single (generic, closed) point. -/
lemma exists_isClosed_singleton : ∃ p : X, IsClosed ({p} : Set X) := by
  by_cases h : ∃ z : X, coheight z = 1
  · obtain ⟨z, hz⟩ := h
    exact ⟨z, isClosed_singleton_of_coheight_eq_one hz⟩
  · refine ⟨genericPoint X, ?_⟩
    have hall : ∀ x : X, x = genericPoint X := fun x => by
      rcases Order.le_one_iff.mp (coheight_le_one x) with h0 | h1
      · exact eq_genericPoint_of_coheight_eq_zero h0
      · exact absurd ⟨x, h1⟩ h
    have huniv : ({genericPoint X} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun x => (hall x : x ∈ ({genericPoint X} : Set X))
    rw [huniv]
    exact isClosed_univ

section Evaluation

variable (p : X)

/-- The evaluation of a regular function at a point `p`: the residue of its (unique) stalk
representative. This is a ring homomorphism `L(0) →+* κ(p)`. -/
noncomputable def evalRegularFunctions : regularFunctions X k →+* ↑(X.residueField p) :=
  letI e : ↑(X.presheaf.stalk p) ≃+*
      (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField).range :=
    RingEquiv.ofBijective (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective ↑(X.presheaf.stalk p) ↑X.functionField
        (Subtype.ext_iff.mp h),
       RingHom.rangeRestrict_surjective
         (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField)⟩
  (X.residue p).hom.comp <| (e.symm : _ →+* ↑(X.presheaf.stalk p)).comp <|
    ((regularFunctions X k).toSubring.subtype).codRestrict
      (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField).range
      (fun f => mem_range_algebraMap_stalk_of_forall_ord_nonneg p
        (fun z hz => ord_nonneg_of_mem_regularFunctions k f.2 hz))

/-- Characterization of `evalRegularFunctions` through any stalk representative. -/
lemma evalRegularFunctions_eq_residue (f : regularFunctions X k)
    (g : ↑(X.presheaf.stalk p))
    (hg : algebraMap ↑(X.presheaf.stalk p) ↑X.functionField g = (f : ↑X.functionField)) :
    evalRegularFunctions k p f = X.residue p g := by
  unfold evalRegularFunctions
  have hinj : Function.Injective (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField) :=
    IsFractionRing.injective _ _
  set e : ↑(X.presheaf.stalk p) ≃+*
      (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField).range :=
    RingEquiv.ofBijective (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField).rangeRestrict
      ⟨fun _ _ h => hinj (Subtype.ext_iff.mp h),
       RingHom.rangeRestrict_surjective
         (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField)⟩ with he
  simp only [RingHom.comp_apply]
  congr 1
  -- the stalk representative is unique: compare images in the function field
  apply hinj
  rw [hg]
  -- the image of the chosen preimage is the value of `e ∘ e.symm`, i.e. `f` itself
  exact congrArg Subtype.val (RingEquiv.apply_symm_apply e _)

/-- Evaluation of a constant: `evalRegularFunctions` restricted to `k` is evaluation of the
corresponding global section at `p`. -/
lemma evalRegularFunctions_algebraMap (r : k) :
    evalRegularFunctions k p (algebraMap k (regularFunctions X k) r) =
      (X.Γevaluation p).hom (globalSec (X := X) (R := CommRingCat.of k) r) := by
  rw [evalRegularFunctions_eq_residue k p _
    (X.presheaf.germ ⊤ p trivial (globalSec (X := X) (R := CommRingCat.of k) r)) ?_]
  · exact (ConcreteCategory.comp_apply _ _ _).symm
  · rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl

/-- Evaluation as a `k`-linear map into the residue field (with its module structure from
`ResidueFieldModule`). -/
noncomputable def evalRegularFunctionsₗ :
    regularFunctions X k →ₗ[k] ↑(X.residueField p) where
  toFun := evalRegularFunctions k p
  map_add' := map_add _
  map_smul' r f := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, residueField_smul_def, evalRegularFunctions_algebraMap]

/-- **Finiteness of `L(0)`.** On a curve, locally of finite type and universally closed
over `k`, the space of everywhere-regular rational functions is a finite-dimensional
`k`-vector space: it is a field mapping `k`-linearly and injectively to the residue field
of a closed point, which is finite over `k` by Zariski's lemma. -/
theorem finite_regularFunctions
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    Module.Finite k (regularFunctions X k) := by
  obtain ⟨p, hp⟩ := exists_isClosed_singleton (X := X)
  haveI hκ : Module.Finite k ↑(X.residueField p) := finite_residueField_of_isClosed k hp
  haveI : _root_.IsNoetherian k ↑(X.residueField p) := IsNoetherian.iff_fg.mpr hκ
  letI : Field (regularFunctions X k) := (isField_regularFunctions k).toField
  exact Module.Finite.of_injective (evalRegularFunctionsₗ k p)
    (RingHom.injective (evalRegularFunctions k p))

end Evaluation

end RegularFunctions

/-! ### Transport to `H⁰` -/

section Transport

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

variable (X) in
/-- The canonical witness that the generic point lies in `⊤`. -/
noncomputable def topWitness :
    (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj
      (unop (op (⊤ : X.Opens))) :=
  ⟨⟨(trivial : genericPoint X ∈ (⊤ : X.Opens))⟩⟩

variable (X) in
/-- Evaluation of a global section of `𝒪ₓ(0)` (in the submodule design) at the generic-point
witness of `⊤`, as an element of `L(0)`. -/
noncomputable def globalSectionsToRegularFunctions :
    ↑(((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (sheaf (0 : AlgebraicCycle X ℤ))).obj.obj (op ⊤)) →+ regularFunctions X k where
  toFun s := ⟨eval (topWitness X) s.1, s.2 (topWitness X)⟩
  map_zero' := Subtype.ext (eval_zero (topWitness X))
  map_add' s t := Subtype.ext (eval_add (topWitness X) s.1 t.1)

lemma globalSectionsToRegularFunctions_injective :
    Function.Injective (globalSectionsToRegularFunctions X k) := fun s t hst =>
  Subtype.ext ((skyscraperSectionsAddEquiv (genericPoint X)
    (AddCommGrpCat.of ↑X.functionField) (topWitness X)).injective
    (congrArg Subtype.val hst))

variable (X) in
/-- `H⁰(X, 𝒪ₓ(0)) → L(0)`, `k`-linearly: the composite of `H.equiv₀` (`H⁰` is the global
sections) with evaluation of a global section as a rational function. `k`-linearity is the
naturality of `H.equiv₀` applied to the scalar endomorphism `smulEnd`, combined with the
computation `eval_smul` of the skyscraper scalar action on values. -/
noncomputable def h0ToRegularFunctions :
    ((sheaf (0 : AlgebraicCycle X ℤ)).H 0) →ₗ[k] regularFunctions X k where
  toFun x := globalSectionsToRegularFunctions X k
    (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (sheaf (0 : AlgebraicCycle X ℤ))) isTerminalTop x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    -- `r • x` is the functoriality of cohomology along the scalar endomorphism, so
    -- `equiv₀` intertwines it with the scalar action on global sections.
    have hsmul : Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (sheaf (0 : AlgebraicCycle X ℤ))) isTerminalTop (r • x)
        = (smulEnd (R := CommRingCat.of k) (sheaf (0 : AlgebraicCycle X ℤ)) r).hom.app (op ⊤)
            (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj
              (sheaf (0 : AlgebraicCycle X ℤ))) isTerminalTop x) :=
      (CategoryTheory.Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
        (f := smulEnd (R := CommRingCat.of k) (sheaf (0 : AlgebraicCycle X ℤ)) r) x).symm
    rw [hsmul]
    set s := Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (sheaf (0 : AlgebraicCycle X ℤ))) isTerminalTop x with hs
    refine Subtype.ext ?_
    -- On values, the scalar action is multiplication by the constant `r`.
    have h1 : eval (X := X) (topWitness X)
          (((smulEnd (R := CommRingCat.of k) (sheaf (0 : AlgebraicCycle X ℤ)) r).hom.app
            (op ⊤) s).1)
        = X.presheaf.germ ⊤ (genericPoint X) trivial
            (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) *
          eval (topWitness X) s.1 :=
      eval_smul (topWitness X)
        (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) s.1
    have hsg : structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r
        = globalSec (X := X) (R := CommRingCat.of k) r := by
      rw [structureRingHom_apply, Subsingleton.elim (⊤ : X.Opens).leTop.op (𝟙 _)]
      simp
    rw [SetLike.val_smul, Algebra.smul_def]
    show eval (X := X) (topWitness X)
        (((smulEnd (R := CommRingCat.of k) (sheaf (0 : AlgebraicCycle X ℤ)) r).hom.app
          (op ⊤) s).1)
      = algebraMap k ↑X.functionField r * eval (topWitness X) s.1
    rw [h1, hsg]
    rfl

/-- **Finiteness of `H⁰(X, 𝒪ₓ)`.** On a curve, locally of finite type and universally
closed over `k`, the zeroth cohomology of the divisorial structure sheaf is a
finite-dimensional `k`-vector space: it is the space `L(0)` of everywhere-regular rational
functions, which is finite by `finite_regularFunctions`. -/
theorem finite_H0_structureSheaf [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H 0) := by
  haveI hfin : Module.Finite k (regularFunctions X k) := finite_regularFunctions k
  haveI : _root_.IsNoetherian k (regularFunctions X k) := IsNoetherian.iff_fg.mpr hfin
  refine Module.Finite.of_injective (h0ToRegularFunctions X k) ?_
  intro x y hxy
  exact (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (sheaf (0 : AlgebraicCycle X ℤ))) isTerminalTop).injective
    (globalSectionsToRegularFunctions_injective k hxy)

open Order in
/-- **Riemann–Roch, assuming only `H¹` finiteness.** Let `X` be an integral Noetherian
scheme, regular in codimension one, of Krull dimension at most one, whose structure morphism
to `Spec k` is locally of finite type and universally closed (e.g. `X` proper over `k`). If
`H¹(X, 𝒪ₓ)` is finite dimensional over `k`, then for every Weil divisor `D`,
`χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

`H⁰` finiteness is automatic (`finite_H0_structureSheaf`), and everything above degree one
vanishes by the flasque resolution by principal parts; only the genus `h¹(𝒪ₓ)` remains as a
hypothesis. -/
theorem riemann_roch_of_universallyClosed_of_finite_H1 [IsNoetherian X]
    [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (h1 : Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H 1))
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1}) :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k :=
  riemann_roch_of_finite_H0_H1 k (finite_H0_structureSheaf k) h1 hD

end Transport

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

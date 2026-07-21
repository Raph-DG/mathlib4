/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.H0Proper

/-!
# `H¹(X, 𝒪ₓ)` as the cokernel of the principal-parts map

The flasque resolution `0 ⟶ 𝒪ₓ ⟶ 𝒦 ⟶ Q(0) ⟶ 0` of `PrincipalPartsSheaf.lean` identifies
`H¹(X, 𝒪ₓ)` with the cokernel of `H⁰(𝒦) ⟶ H⁰(Q(0))`: in the long exact sequence

`H⁰(𝒦) ⟶ H⁰(Q) ⟶ H¹(𝒪ₓ) ⟶ H¹(𝒦) = 0`

the connecting map is surjective (`𝒦` is flasque, so `H¹(𝒦)` vanishes) with kernel the image
of `H⁰(𝒦)`. Combining with `H.equiv₀` (`H⁰` = global sections), the finiteness of `H¹(X, 𝒪ₓ)`
— the last remaining hypothesis of Riemann–Roch after `H0Proper.lean` — reduces to the
concrete **adelic statement**: the space of finitely-supported families of principal parts
`(f_q)_q ∈ ⊕_q k(X)/𝒪_q` modulo the principal parts of global rational functions is a
finite-dimensional `k`-vector space.

## Main statements

* `finite_H_first_succ_of_coker`: for any short exact sequence of sheaves of modules with
  `H¹(X₂)` trivial, `H¹(X₁)` is finite as soon as `H⁰(X₃)⧸im H⁰(X₂)` is finite.
* `h0SectionsLinearEquiv`: `H⁰(F) ≃ₗ[k] Γ(F, ⊤)` for any sheaf of modules `F`, `k`-linearly.
* `finite_H1_structureSheaf_of_finite_partsCoker`: `H¹(X, 𝒪ₓ)` is finite over `k` if the
  global principal parts modulo rational functions are.
* `riemann_roch_of_universallyClosed_of_finite_partsCoker`: **Riemann–Roch** for a curve,
  universally closed and locally of finite type over `k`, assuming only the adelic
  finiteness statement.

Proving the adelic finiteness (Riemann's inequality) is the remaining campaign.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits Order Opposite
  TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

/-! ### `H¹(X₁)` from the cokernel of `H⁰(X₂) ⟶ H⁰(X₃)` -/

section LesCokernel

variable (o : ShortComplex X.Modules) (hS : (o.map (Modules.toSheafAb X)).ShortExact)

/-- The `k`-module structure on the quotient of a cohomology group by the range of an induced
map, keyed to `k` itself (the instance over `↑(CommRingCat.of k)` is not found for goals
phrased over `k`). -/
noncomputable instance {F G : X.Modules} (ψ : F ⟶ G) {n : ℕ} :
    Module k ((((SheafOfModules.toSheaf X.ringCatSheaf).obj G).H n) ⧸
      LinearMap.range (HMapₗ (R := CommRingCat.of k) ψ n)) :=
  inferInstanceAs (Module ↑(CommRingCat.of k)
    ((((SheafOfModules.toSheaf X.ringCatSheaf).obj G).H n) ⧸
      LinearMap.range (HMapₗ (R := CommRingCat.of k) ψ n)))

include hS in
/-- If `H¹(X₂)` is trivial (e.g. `X₂` flasque), the connecting map identifies `H¹(X₁)` with
the cokernel of `H⁰(X₂) ⟶ H⁰(X₃)`; in particular finiteness of the cokernel gives finiteness
of `H¹(X₁)`. -/
lemma finite_H_first_succ_of_coker
    (h2 : Subsingleton (o.X₂.H 1))
    (hcoker : Module.Finite k ((o.X₃.H 0) ⧸
      LinearMap.range (HMapₗ (R := CommRingCat.of k) o.g 0))) :
    Module.Finite k (o.X₁.H 1) := by
  -- Exactness at `H⁰(X₃)`: the kernel of the connecting map is the image of `H⁰(X₂)`.
  have hker : LinearMap.range (HMapₗ (R := CommRingCat.of k) o.g 0)
      = LinearMap.ker (δₗ (R := CommRingCat.of k) hS 0 1 rfl) :=
    (dAux_exact (CommRingCat.of k) o hS 0 1).moduleCat_range_eq_ker
  -- Exactness at `H¹(X₁)` plus `H¹(X₂) = 0`: the connecting map is surjective.
  have hsurj : Function.Surjective (δₗ (R := CommRingCat.of k) hS 0 1 rfl) := by
    have hex2 : LinearMap.range (δₗ (R := CommRingCat.of k) hS 0 1 rfl)
        = LinearMap.ker (HMapₗ (R := CommRingCat.of k) o.f 1) :=
      (dAux_exact (CommRingCat.of k) o hS 0 2).moduleCat_range_eq_ker
    intro y
    have hy : y ∈ LinearMap.ker (HMapₗ (R := CommRingCat.of k) o.f 1) :=
      LinearMap.mem_ker.mpr (haveI := h2; Subsingleton.elim _ _)
    exact hex2.ge hy
  -- The induced map from the cokernel is surjective onto `H¹(X₁)`.
  haveI := hcoker
  refine Module.Finite.of_surjective
    (Submodule.liftQ (LinearMap.range (HMapₗ (R := CommRingCat.of k) o.g 0))
      (δₗ (R := CommRingCat.of k) hS 0 1 rfl) (le_of_eq hker)) ?_
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨Submodule.Quotient.mk x, hx⟩

end LesCokernel

/-! ### `H⁰` as global sections, `k`-linearly -/

section SectionsEquiv

/-- The `k`-module structure on the sections of a sheaf of modules, keyed to `k` itself.
This is definitionally the `Module R Γ(F, U)` instance of `CohmologyModule` at
`R := CommRingCat.of k`. -/
noncomputable instance (F : X.Modules) {U : X.Opens} : Module k Γ(F, U) :=
  Module.compHom Γ(F, U) (structureRingHom (R := CommRingCat.of k) U)

/-- `H⁰(F)` is the space of global sections of `F`, as a `k`-linear equivalence:
`H.equiv₀` is `k`-linear by its naturality applied to the scalar endomorphism `smulEnd`. -/
noncomputable def h0SectionsLinearEquiv (F : X.Modules) :
    F.H 0 ≃ₗ[k] Γ(F, (⊤ : X.Opens)) :=
  AddEquiv.toLinearEquiv
    (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) isTerminalTop)
    (fun r x =>
      (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
        (f := smulEnd (R := CommRingCat.of k) F r) x).symm)

/-- The map on global sections induced by a morphism of sheaves of modules, as a `k`-linear
map (through the structure map `k ⟶ Γ(X, ⊤)`). -/
noncomputable def appTopₗ {F G : X.Modules} (ψ : F ⟶ G) :
    Γ(F, (⊤ : X.Opens)) →ₗ[k] Γ(G, (⊤ : X.Opens)) where
  toFun := ψ.val.app (op ⊤)
  map_add' := map_add _
  map_smul' r x :=
    map_smul (ψ.val.app (op ⊤)).hom
      (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) x

/-- `h0SectionsLinearEquiv` is natural: it intertwines the induced maps on `H⁰` and on
global sections. -/
lemma h0SectionsLinearEquiv_naturality {F G : X.Modules} (ψ : F ⟶ G) (x : F.H 0) :
    h0SectionsLinearEquiv k G (HMapₗ (R := CommRingCat.of k) ψ 0 x)
      = appTopₗ k ψ (h0SectionsLinearEquiv k F x) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    (f := (SheafOfModules.toSheaf X.ringCatSheaf).map ψ) x).symm

/-- The `k`-module structure on the sections cokernel, keyed to `k`. -/
noncomputable instance {F G : X.Modules} (ψ : F ⟶ G) :
    Module k (Γ(G, (⊤ : X.Opens)) ⧸ LinearMap.range (appTopₗ k ψ)) :=
  Submodule.Quotient.module _

/-- Finiteness of the cokernel on global sections transfers to the cokernel on `H⁰`, along
`h0SectionsLinearEquiv`. -/
lemma finite_H0_coker_of_finite_sections_coker {F G : X.Modules} (ψ : F ⟶ G)
    (h : Module.Finite k (Γ(G, (⊤ : X.Opens)) ⧸ LinearMap.range (appTopₗ k ψ))) :
    Module.Finite k ((G.H 0) ⧸
      LinearMap.range (HMapₗ (R := CommRingCat.of k) ψ 0)) := by
  have hcomp : (h0SectionsLinearEquiv k G).toLinearMap.comp
        (HMapₗ (R := CommRingCat.of k) ψ 0)
      = (appTopₗ k ψ).comp (h0SectionsLinearEquiv k F).toLinearMap :=
    LinearMap.ext fun x => h0SectionsLinearEquiv_naturality k ψ x
  have hmap : (LinearMap.range (HMapₗ (R := CommRingCat.of k) ψ 0)).map
        (h0SectionsLinearEquiv k G).toLinearMap
      = LinearMap.range (appTopₗ k ψ) := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp_of_range_eq_top]
    exact LinearEquiv.range _
  haveI := h
  exact Module.Finite.equiv
    (Submodule.Quotient.equiv _ _ (h0SectionsLinearEquiv k G) hmap).symm

end SectionsEquiv

/-! ### Specialization to the principal-parts resolution -/

section PartsCokernel

variable [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]
  [Order.KrullDimLE 1 X]

open PrincipalParts in
/-- **`H¹(X, 𝒪ₓ)` from the adelic cokernel.** On a curve, the first cohomology of the
divisorial structure sheaf is finite over `k` as soon as the space of global principal parts
modulo the principal parts of rational functions is: the flasque resolution
`0 ⟶ 𝒪ₓ ⟶ 𝒦 ⟶ Q(0) ⟶ 0` identifies `H¹(𝒪ₓ)` with that cokernel (through `H⁰ = Γ`). -/
theorem finite_H1_structureSheaf_of_finite_partsCoker
    (hcoker : Module.Finite k
      (Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) ⧸
        LinearMap.range (appTopₗ k (toPartsHom (0 : AlgebraicCycle X ℤ))))) :
    Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H 1) := by
  -- Codimension-one points are closed on a curve.
  have hcl : ∀ p : X, coheight p = 1 → ∀ y, y ≤ p → y = p := fun p hp y hy =>
    have hmin : IsMin p :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hp.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  -- `H¹(𝒦) = 0` by flasqueness of the skyscraper of rational functions.
  haveI hflasque : TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (functionFieldSheaf X)) :=
    inferInstanceAs (TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (skyscraperSheafOfModules (genericPoint X) X.ringCatSheaf ↑X.functionField)))
  have h2 : Subsingleton ((functionFieldSheaf X).H 1) :=
    inferInstanceAs (Subsingleton
      (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj (functionFieldSheaf X)) (0 + 1)))
  exact finite_H_first_succ_of_coker k (partsComplex (0 : AlgebraicCycle X ℤ))
    (shortExact_map_toSheaf (partsComplex_shortExact (0 : AlgebraicCycle X ℤ) (by simp) hcl))
    h2
    (finite_H0_coker_of_finite_sections_coker k (toPartsHom (0 : AlgebraicCycle X ℤ)) hcoker)

open PrincipalParts in
/-- **Riemann–Roch, assuming only the adelic finiteness.** Let `X` be an integral Noetherian
scheme, regular in codimension one, of Krull dimension at most one, whose structure morphism
to `Spec k` is locally of finite type and universally closed (e.g. `X` proper over `k`). If
the space of finitely-supported families of principal parts modulo the principal parts of
rational functions is finite dimensional over `k` (Riemann's inequality), then for every
Weil divisor `D`, `χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

Both cohomological hypotheses are now discharged: `H⁰` by the valuative-criterion argument
of `H0Proper.lean`, `H¹` by the identification with the adelic cokernel. -/
theorem riemann_roch_of_universallyClosed_of_finite_partsCoker
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (hcoker : Module.Finite k
      (Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) ⧸
        LinearMap.range (appTopₗ k (toPartsHom (0 : AlgebraicCycle X ℤ)))))
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1}) :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k :=
  riemann_roch_of_universallyClosed_of_finite_H1 k
    (finite_H1_structureSheaf_of_finite_partsCoker k hcoker) hD

end PartsCokernel

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

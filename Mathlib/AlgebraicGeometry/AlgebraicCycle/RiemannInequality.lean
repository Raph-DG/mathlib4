/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.H1Cokernel
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Towards Riemann's inequality

After `H0Proper.lean` and `H1Cokernel.lean`, the Riemann–Roch theorem for a curve `X`
universally closed and locally of finite type over `k` rests on a single unproven statement
(**Riemann's inequality**, `riemann_roch_of_universallyClosed_of_finite_partsCoker`): the
space of finitely-supported families of principal parts modulo the principal parts of
rational functions is finite dimensional over `k`.

This file collects the groundwork. The classical proof outline (Chevalley):

1. every rational function `f` is a global section of `𝒪ₓ(-div f)` (`exists_mem_carrier`
  below), so the cokernel is the direct limit over divisors `D` of
  `Γ(Q(0)) bounded by D ⧸ L(D)`, whose dimensions are `deg D - ℓ(D) + ℓ(0)`;
2. finiteness of the limit is equivalent to the boundedness of `deg D - ℓ(D)`
  (Riemann's inequality proper);
3. boundedness is proven by picking a rational function `f` with a pole (`exists_ord_neg`
  below), which is then transcendental over `k` (`transcendental_of_ord_neg` below); the
  extension `k(X)/k(f)` is finite (this needs `k(X)` to be a finitely generated field
  extension, from an affine chart), and a `k(f)`-basis `y₁, …, yₙ` of `k(X)` scaled into
  some `L(C)` yields `n(m+1)` independent elements `f^j yᵢ` of `L(m·B + C)` where `B` is the
  pole divisor of `f`, giving `deg D - ℓ(D)` bounded along the cofinal family `m·B + C`;
  cofinality and the comparison `deg B ≤ [k(X) : k(f)]` are where the arithmetic of the
  pole divisor enters (the fundamental identity `∑ e·f ≤ n` for the valuations over the
  infinite place of `k(f)`).

Step 3's independence and transcendence ingredients are begun here; the dimension
bookkeeping of steps 1–2 and the pole-degree comparison are future work.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
variable [IsIntegral X] [IsLocallyNoetherian X]

/-! ### Every rational function is bounded by a divisor -/

omit k in
/-- Every rational function is a global section of `𝒪ₓ(D)` for some Weil divisor `D`
supported in codimension one — namely `D = -div f`. This makes the space of rational
functions the union of the `L(D)` and the adelic cokernel a direct limit. -/
lemma exists_mem_carrier (f : ↑X.functionField) :
    ∃ D : AlgebraicCycle X ℤ, D.support ⊆ {x | coheight x = 1} ∧
      f ∈ Sheaf.carrier D (⊤ : X.Opens) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by simp, Sheaf.zero_mem' 0 ⊤⟩
  · refine ⟨-div f, fun z hz => ?_, Sheaf.mem_carrier_iff.mpr fun _ =>
      ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z _ => ?_⟩⟩
    · -- the support of `-div f` consists of points with `ord f ≠ 0`, all of codimension one
      have h1 : X.ord f z ≠ 0 := by
        have h2 : ⇑(-div f) z ≠ 0 := Function.mem_support.mp hz
        simpa [div_eq_ord] using h2
      by_contra hz1
      exact h1 (Scheme.ord_eq_zero_of_coheight_neq_one hz1 f)
    · -- the bound `0 ≤ ord f z + (-div f) z` holds with equality
      have : ⇑(-div f) z = - X.ord f z := by simp [div_eq_ord]
      simp [this]

/-! ### Poles and transcendence -/

section Transcendence

variable [IsRegularInCodimensionOne X]

/-- A rational function integral over the constants has nonnegative order everywhere: it is
integral over each codimension-one stalk (which contains the constants), and these stalks
are integrally closed (they are DVRs). Converse companion to
`isIntegral_of_forall_ord_nonneg`. -/
lemma ord_nonneg_of_isIntegral {z : X} (hz : coheight z = 1)
    {f : ↑X.functionField} (hf : _root_.IsIntegral k f) : 0 ≤ X.ord f z := by
  haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk z) :=
    IsRegularInCodimensionOne.stalk_dvr z hz
  -- the constants map into the stalk through the germ of the global section
  letI : Algebra k ↑(X.presheaf.stalk z) :=
    ((X.presheaf.germ ⊤ z trivial).hom.comp
      (globalSec (X := X) (R := CommRingCat.of k))).toAlgebra
  haveI : IsScalarTower k ↑(X.presheaf.stalk z) ↑X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap k ↑X.functionField r
          = algebraMap ↑(X.presheaf.stalk z) ↑X.functionField
            ((X.presheaf.germ ⊤ z trivial).hom
              (globalSec (X := X) (R := CommRingCat.of k) r))
      rw [Scheme.algebraMap_germ_eq_germToFunctionField]
      rfl
  -- integrality ascends the tower, and the stalk is integrally closed in `k(X)`
  have hint : _root_.IsIntegral ↑(X.presheaf.stalk z) f := hf.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ord_nonneg_of_mem_range_algebraMap_stalk hz ⟨y, hy⟩

/-- A rational function with a pole is transcendental over the constants. -/
lemma transcendental_of_ord_neg {z : X} (hz : coheight z = 1)
    {f : ↑X.functionField} (h : X.ord f z < 0) : Transcendental k f := fun halg =>
  absurd (ord_nonneg_of_isIntegral k hz halg.isIntegral) (not_le.mpr h)

omit k in
/-- At every codimension-one point there is a rational function with a pole: the inverse of
a uniformizer of the stalk. -/
lemma exists_ord_neg (z : X) (hz : coheight z = 1) :
    ∃ f : ↑X.functionField, X.ord f z < 0 := by
  haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk z) :=
    IsRegularInCodimensionOne.stalk_dvr z hz
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↑(X.presheaf.stalk z)
  refine ⟨(algebraMap ↑(X.presheaf.stalk z) ↑X.functionField ϖ) ^ (-1 : ℤ), ?_⟩
  rw [ord_zpow_algebraMap_irreducible hz hϖ (-1)]
  norm_num

/-- If `X` has a codimension-one point, the function field contains an element
transcendental over the constants. This is the starting point of Riemann's inequality: the
map to `ℙ¹` along which the counting happens. -/
lemma exists_transcendental_of_coheight_eq_one (z : X) (hz : coheight z = 1) :
    ∃ f : ↑X.functionField, Transcendental k f := by
  obtain ⟨f, hf⟩ := exists_ord_neg z hz
  exact ⟨f, transcendental_of_ord_neg k hz hf⟩

end Transcendence

/-! ### A directed union of uniformly finite-dimensional submodules is finite dimensional -/

section DirectedUnion

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- If a module is covered by a directed family of submodules of uniformly bounded finite
dimension, it is finite dimensional: a submodule of maximal dimension absorbs every member
of the family, hence is everything. -/
lemma module_finite_of_directed_of_bounded {M : Type u} [AddCommGroup M] [Module k M]
    {ι : Type u} [Nonempty ι] (N : ι → Submodule k M)
    (hdir : ∀ i j, ∃ l, N i ≤ N l ∧ N j ≤ N l)
    (hcover : ∀ x : M, ∃ i, x ∈ N i)
    (B : ℕ) (hfin : ∀ i, Module.Finite k (N i))
    (hbound : ∀ i, Module.finrank k (N i) ≤ B) :
    Module.Finite k M := by
  -- a member of maximal dimension
  have hne : (Set.range fun i => Module.finrank k (N i)).Nonempty := Set.range_nonempty _
  have hbdd : BddAbove (Set.range fun i => Module.finrank k (N i)) :=
    ⟨B, fun n ⟨i, hi⟩ => hi ▸ hbound i⟩
  obtain ⟨i₀, hi₀⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ i, Module.finrank k (N i) ≤ Module.finrank k (N i₀) := fun i => by
    have h := le_csSup hbdd (Set.mem_range_self (f := fun i => Module.finrank k (N i)) i)
    rwa [← hi₀] at h
  -- it absorbs every member of the family
  have habs : ∀ i, N i ≤ N i₀ := by
    intro i
    obtain ⟨l, hil, hi₀l⟩ := hdir i i₀
    haveI := hfin l
    -- inside `N l`, the image of `N i₀` is a subspace of full rank, hence everything
    have h1 : Module.finrank k (Submodule.comap (N l).subtype (N i₀))
        = Module.finrank k (N i₀) :=
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hi₀l)
    have h2 : Submodule.comap (N l).subtype (N i₀) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      refine le_antisymm (Submodule.finrank_le _) ?_
      rw [h1]
      simpa using hmax l
    have h3 : N l ≤ N i₀ := fun x hx => by
      have := h2 ▸ Submodule.mem_top (x := (⟨x, hx⟩ : N l))
      exact this
    exact hil.trans h3
  have htop : N i₀ = ⊤ := Submodule.eq_top_iff'.mpr fun x => by
    obtain ⟨i, hi⟩ := hcover x
    exact habs i hi
  haveI := hfin i₀
  rw [htop] at *
  exact Module.Finite.equiv (Submodule.topEquiv (R := k) (M := M))

end DirectedUnion

/-! ### The constants inside the stalks, and `L(D)` as a `k`-submodule -/

section KLinear

/-- The constants map into every stalk: `k ⟶ Γ(X, ⊤) ⟶ 𝒪_{X,p}` via the germ of the global
section. At the generic point this is definitionally the `k`-algebra structure of the
function field. -/
noncomputable instance stalkAlgebra (p : X) : Algebra k ↑(X.presheaf.stalk p) :=
  ((X.presheaf.germ ⊤ p trivial).hom.comp
    (globalSec (X := X) (R := CommRingCat.of k))).toAlgebra

noncomputable instance stalkTower (p : X) :
    IsScalarTower k ↑(X.presheaf.stalk p) ↑X.functionField :=
  IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap k ↑X.functionField r
        = algebraMap ↑(X.presheaf.stalk p) ↑X.functionField
          ((X.presheaf.germ ⊤ p trivial).hom
            (globalSec (X := X) (R := CommRingCat.of k) r))
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl

variable [IsRegularInCodimensionOne X]

/-- Constants have nonnegative order at every codimension-one point. -/
lemma ord_algebraMap_const_nonneg {z : X} (hz : coheight z = 1) (r : k) :
    0 ≤ X.ord (algebraMap k ↑X.functionField r) z :=
  ord_nonneg_of_mem_range_algebraMap_stalk hz
    ⟨algebraMap k _ r, (IsScalarTower.algebraMap_apply k _ _ r).symm⟩

variable (X) in
/-- `L(D)`, the space of rational functions bounded by the divisor `D`, as a `k`-submodule
of the function field. Its dimension is the classical `ℓ(D)`. -/
noncomputable def LSubmodule (D : AlgebraicCycle X ℤ) : Submodule k ↑X.functionField where
  carrier := Sheaf.carrier D ⊤
  add_mem' := Sheaf.add_mem' D ⊤
  zero_mem' := Sheaf.zero_mem' D ⊤
  smul_mem' r f hf := Sheaf.mem_carrier_iff.mpr fun hrf => by
    have hr0 : algebraMap k ↑X.functionField r ≠ 0 := fun h =>
      hrf (by rw [Algebra.smul_def, h, zero_mul])
    have hf0 : f ≠ 0 := fun h => hrf (by rw [h, smul_zero])
    refine ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z hz => ?_⟩
    have h1 := (Sheaf.mem_carrier_iff.mp hf hf0).2 z hz
    by_cases hz1 : coheight z = 1
    · have h2 := ord_algebraMap_const_nonneg k hz1 r
      rw [show r • f = algebraMap k ↑X.functionField r * f from Algebra.smul_def r f,
        ord_mul hz1 hr0 hf0]
      omega
    · rw [show r • f = algebraMap k ↑X.functionField r * f from Algebra.smul_def r f]
      rw [Scheme.ord_eq_zero_of_coheight_neq_one hz1] at h1 ⊢
      exact h1

lemma mem_LSubmodule_iff {D : AlgebraicCycle X ℤ} {f : ↑X.functionField} :
    f ∈ LSubmodule X k D ↔ f ∈ Sheaf.carrier D ⊤ := Iff.rfl

/-- `L` is monotone in the divisor. -/
lemma LSubmodule_mono {D₁ D₂ : AlgebraicCycle X ℤ} (h : D₁ ≤ D₂) :
    LSubmodule X k D₁ ≤ LSubmodule X k D₂ := fun _ hf => carrier_mono h hf

end KLinear

/-! ### The principal-parts map as a `k`-linear map from the function field -/

section PrincipalPartsLinear

variable [IsRegularInCodimensionOne X]

variable (X) in
/-- The global sections of the sheaf of rational functions are the function field,
`k`-linearly: evaluation at the generic-point witness. -/
noncomputable def sectionsEquivK :
    Γ(functionFieldSheaf X, (⊤ : X.Opens)) ≃ₗ[k] ↑X.functionField :=
  AddEquiv.toLinearEquiv
    (skyscraperSectionsAddEquiv (genericPoint X) (AddCommGrpCat.of ↑X.functionField)
      (topWitness X))
    (fun r s => by
      have h1 := eval_smul (X := X) (topWitness X)
        (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) s
      have hsg : structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r
          = globalSec (X := X) (R := CommRingCat.of k) r := by
        rw [structureRingHom_apply, Subsingleton.elim (⊤ : X.Opens).leTop.op (𝟙 _)]
        simp
      show eval (X := X) (topWitness X)
          ((structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) • s)
        = r • eval (topWitness X) s
      rw [h1, hsg, Algebra.smul_def]
      rfl)

variable [IsNoetherian X]

variable (X) in
/-- The principal-parts map `k(X) ⟶ Γ(Q(0), ⊤)`: a rational function goes to its family of
classes at all codimension-one points. -/
noncomputable def principalPartsₗ :
    ↑X.functionField →ₗ[k]
      Γ(PrincipalParts.partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) :=
  (appTopₗ k (PrincipalParts.toPartsHom (0 : AlgebraicCycle X ℤ))).comp
    (sectionsEquivK X k).symm.toLinearMap

/-- The principal-parts map from the function field has the same range as the map on global
sections, so the adelic cokernel can be computed from it. -/
lemma range_principalPartsₗ :
    LinearMap.range (principalPartsₗ X k)
      = LinearMap.range (appTopₗ k (PrincipalParts.toPartsHom (0 : AlgebraicCycle X ℤ))) :=
  LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)

/-- The component of the principal part of a rational function at a codimension-one point is
its class. -/
lemma principalPartsₗ_apply_coe (f : ↑X.functionField)
    (i : PrincipalParts.Index (⊤ : X.Opens)) :
    (principalPartsₗ X k f).1 i = PrincipalParts.Component.mk 0 i.2.1 f := by
  show PrincipalParts.Component.mk 0 i.2.1
      (eval ⟨⟨genericPoint_mem i.2.2⟩⟩ (constSection f)) = _
  rw [eval_constSection]

end PrincipalPartsLinear

/-! ### The classes bounded by a pole order span in bounded dimension

At a codimension-one point `q`, the classes in `k(X)/𝒪_q` of rational functions with pole
order at most `m` are spanned by the `m · dim_k κ(q)` classes `ϖ^{-j}·c` (`1 ≤ j ≤ m`, `c` a
lift of a basis vector of `κ(q)`): peeling off the leading Laurent coefficient reduces the
pole order. This is the local input to `dim P_D ≤ deg D`.
-/

section ComponentSpan

variable [IsRegularInCodimensionOne X]

/-- The `k`-module structure on the space of principal parts at `q`: through the constants
in the stalk. -/
noncomputable instance {q : X} (hq : coheight q = 1) :
    Module k (PrincipalParts.Component (0 : AlgebraicCycle X ℤ) hq) :=
  Module.compHom _ (algebraMap k ↑(X.presheaf.stalk q))

variable (X) in
/-- The class map `k(X) ⟶ k(X)/𝒪_q`, `k`-linearly. -/
noncomputable def componentMkₗ {q : X} (hq : coheight q = 1) :
    ↑X.functionField →ₗ[k] PrincipalParts.Component (0 : AlgebraicCycle X ℤ) hq where
  toFun := PrincipalParts.Component.mk 0 hq
  map_add' := PrincipalParts.Component.mk_add 0 hq
  map_smul' r f := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k ↑(X.presheaf.stalk q)
      ↑X.functionField, ← Algebra.smul_def, PrincipalParts.Component.mk_smul]
    rfl

/-- The residue of a constant multiple: the constants act on the residue field through
evaluation. -/
lemma residue_algebraMap_mul (p : X) (r : k) (c : ↑(X.presheaf.stalk p)) :
    (X.residue p).hom (algebraMap k ↑(X.presheaf.stalk p) r * c)
      = r • (X.residue p).hom c := by
  rw [map_mul, residueField_smul_def]
  congr 1

/-- The class of a function of nonnegative order vanishes. -/
lemma component_mk_eq_zero {q : X} (hq : coheight q = 1) {f : ↑X.functionField}
    (hf : f ∈ ordSubmodule hq 0) :
    PrincipalParts.Component.mk (0 : AlgebraicCycle X ℤ) hq f = 0 := by
  rw [PrincipalParts.Component.mk_eq_zero_iff, mem_ordSubmodule_iff]
  intro hne
  have h := (mem_ordSubmodule_iff hq).mp hf hne
  simpa using h

open PrincipalParts in
/-- **The local span bound.** The classes of rational functions of pole order at most `m` at
`q` lie in the span of `m · dim_k κ(q)` vectors. -/
lemma exists_finset_span_component {q : X} (hq : coheight q = 1)
    [Module.Finite k ↑(X.residueField q)] (m : ℕ) :
    ∃ s : Finset (Component (0 : AlgebraicCycle X ℤ) hq),
      s.card ≤ m * Module.finrank k ↑(X.residueField q) ∧
      ∀ f : ↑X.functionField, f ∈ ordSubmodule hq (-(m : ℤ)) →
        Component.mk 0 hq f ∈
          Submodule.span k ((s : Set (Component (0 : AlgebraicCycle X ℤ) hq))) := by
  classical
  haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk q) :=
    IsRegularInCodimensionOne.stalk_dvr q hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↑(X.presheaf.stalk q)
  set d := Module.finrank k ↑(X.residueField q) with hd
  set b := Module.finBasis k ↑(X.residueField q) with hb
  -- lifts of the residue-field basis into the stalk
  have hres : ∀ e : Fin d, ∃ c : ↑(X.presheaf.stalk q), (X.residue q).hom c = b e :=
    fun e => IsLocalRing.residue_surjective (b e)
  choose c hc using hres
  set ϖK := algebraMap ↑(X.presheaf.stalk q) ↑X.functionField ϖ with hϖK
  have hϖK0 : ϖK ≠ 0 := algebraMap_functionField_ne_zero hϖ.ne_zero
  -- the generators: negative powers of the uniformizer times the basis lifts
  set g : Fin m × Fin d → Component (0 : AlgebraicCycle X ℤ) hq := fun je =>
    Component.mk 0 hq (ϖK ^ (-(je.1.1 + 1 : ℤ)) *
      algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (c je.2)) with hg
  refine ⟨Finset.image g Finset.univ, ?_, ?_⟩
  · calc (Finset.image g Finset.univ).card
        ≤ Finset.univ.card := Finset.card_image_le
      _ = m * d := by simp
  -- induction on the pole order
  have key : ∀ j : ℕ, j ≤ m → ∀ f : ↑X.functionField, f ∈ ordSubmodule hq (-(j : ℤ)) →
      Component.mk 0 hq f ∈
        Submodule.span k ((Finset.image g Finset.univ : Finset _) :
          Set (Component (0 : AlgebraicCycle X ℤ) hq)) := by
    intro j
    induction j with
    | zero =>
      intro _ f hf
      have h0 : PrincipalParts.Component.mk (0 : AlgebraicCycle X ℤ) hq f = 0 :=
        component_mk_eq_zero hq (by simpa using hf)
      rw [h0]
      exact Submodule.zero_mem _
    | succ j ih =>
      intro hjm f hf
      rcases eq_or_ne f 0 with rfl | hf0
      · have h0 : Component.mk (0 : AlgebraicCycle X ℤ) hq (0 : ↑X.functionField) = 0 :=
          map_zero (componentMkₗ X k hq)
        rw [h0]
        exact Submodule.zero_mem _
      by_cases hmem : f ∈ ordSubmodule hq (-(j : ℤ))
      · exact ih (by omega) f hmem
      -- the pole order is exactly `j + 1`
      have horde : X.ord f q = -((j : ℤ) + 1) := by
        have h1 := hf hf0
        have h2 : ¬ (-(j : ℤ) ≤ X.ord f q) := fun hle => hmem fun _ => hle
        push_cast at h1
        omega
      -- extract the unit part `y` of `f · ϖ^{j+1}`
      have hgK0 : X.ord (f * ϖK ^ ((j : ℤ) + 1)) q = 0 := by
        rw [ord_mul hq hf0 (zpow_ne_zero _ hϖK0), ord_zpow_algebraMap_irreducible hq hϖ]
        omega
      obtain ⟨y, hy⟩ := (mem_range_algebraMap_iff_ord_nonneg hq
        (f * ϖK ^ ((j : ℤ) + 1))).mpr (fun _ => hgK0.ge)
      set ρ := (X.residue q).hom y with hρ
      -- subtracting the residue of `y` leaves an element of the maximal ideal
      set z := y - ∑ e : Fin d, algebraMap k ↑(X.presheaf.stalk q) (b.repr ρ e) * c e
        with hzdef
      have hzres : (X.residue q).hom z = 0 := by
        rw [hzdef, map_sub, map_sum]
        have hterm : ∀ e ∈ Finset.univ, (X.residue q).hom
            (algebraMap k ↑(X.presheaf.stalk q) (b.repr ρ e) * c e)
            = b.repr ρ e • b e := fun e _ => by
          rw [residue_algebraMap_mul, hc]
        rw [Finset.sum_congr rfl hterm, Module.Basis.sum_repr]
        exact sub_self ρ
      have hzm : z ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk q) :=
        (IsLocalRing.residue_eq_zero_iff z).mp hzres
      -- the remainder has pole order at most `j`
      have hf' : ϖK ^ (-((j : ℤ) + 1)) *
          algebraMap ↑(X.presheaf.stalk q) ↑X.functionField z
          ∈ ordSubmodule hq (-(j : ℤ)) := by
        rw [mem_ordSubmodule_iff]
        intro hne
        have hz0 : z ≠ 0 := fun h => hne (by rw [h, map_zero, mul_zero])
        have h1 : 1 ≤ X.ord (algebraMap ↑(X.presheaf.stalk q) ↑X.functionField z) q :=
          (mem_maximalIdeal_iff_one_le_ord hq hz0).mp hzm
        rw [ord_mul hq (zpow_ne_zero _ hϖK0) (algebraMap_functionField_ne_zero hz0),
          ord_zpow_algebraMap_irreducible hq hϖ]
        omega
      -- the decomposition of `f`: remainder plus the leading Laurent coefficients
      have hterm : ∀ e : Fin d,
          algebraMap ↑(X.presheaf.stalk q) ↑X.functionField
            (algebraMap k ↑(X.presheaf.stalk q) (b.repr ρ e) * c e)
          = algebraMap k ↑X.functionField (b.repr ρ e)
              * algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (c e) := fun e => by
        rw [map_mul, ← IsScalarTower.algebraMap_apply]
      have hcancel : ϖK ^ (-((j : ℤ) + 1)) * ϖK ^ ((j : ℤ) + 1) = 1 := by
        rw [← zpow_add₀ hϖK0]
        simp
      have hyz : algebraMap ↑(X.presheaf.stalk q) ↑X.functionField y
          = algebraMap ↑(X.presheaf.stalk q) ↑X.functionField z
            + ∑ e : Fin d, algebraMap k ↑X.functionField (b.repr ρ e)
                * algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (c e) := by
        rw [hzdef, map_sub, map_sum, Finset.sum_congr rfl (fun e _ => hterm e)]
        ring
      have hfeq : f = ϖK ^ (-((j : ℤ) + 1)) *
            algebraMap ↑(X.presheaf.stalk q) ↑X.functionField z
          + ∑ e : Fin d, b.repr ρ e •
              (ϖK ^ (-((j : ℤ) + 1)) *
                algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (c e)) := by
        calc f = ϖK ^ (-((j : ℤ) + 1)) * (f * ϖK ^ ((j : ℤ) + 1)) := by
              rw [mul_comm f, ← mul_assoc, hcancel, one_mul]
          _ = ϖK ^ (-((j : ℤ) + 1)) *
                (algebraMap ↑(X.presheaf.stalk q) ↑X.functionField z
                  + ∑ e : Fin d, algebraMap k ↑X.functionField (b.repr ρ e)
                      * algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (c e)) := by
              rw [← hy, hyz]
          _ = _ := by
              rw [mul_add, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Algebra.smul_def]
              ring
      -- conclude by linearity and the inductive hypothesis
      have hspan' := ih (by omega) _ hf'
      have hmklin : Component.mk (0 : AlgebraicCycle X ℤ) hq f = componentMkₗ X k hq f := rfl
      rw [hmklin, hfeq, map_add, map_sum]
      refine Submodule.add_mem _ hspan' (Submodule.sum_mem _ fun e _ => ?_)
      rw [map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr ?_))
      exact Finset.mem_image_of_mem g (Finset.mem_univ (⟨⟨j, by omega⟩, e⟩ : Fin m × Fin d))
  intro f hf
  exact key m le_rfl f hf

end ComponentSpan

/-! ### Families of principal parts bounded by a divisor -/

section BoundedFamilies

variable [IsRegularInCodimensionOne X]

open PrincipalParts

omit [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X] in
/-- A submodule contained in the span of a finite set is finite dimensional, of dimension at
most the cardinality. -/
lemma finite_and_finrank_le_of_le_span {M : Type u} [AddCommGroup M] [Module k M]
    {p : Submodule k M} {s : Finset M} (hle : p ≤ Submodule.span k (s : Set M)) :
    Module.Finite k p ∧ Module.finrank k p ≤ s.card := by
  haveI hspan : Module.Finite k (Submodule.span k (s : Set M)) :=
    Module.Finite.span_of_finite k s.finite_toSet
  have e := Submodule.comapSubtypeEquivOfLe hle
  refine ⟨Module.Finite.equiv e, ?_⟩
  calc Module.finrank k p
      = Module.finrank k (Submodule.comap (Submodule.span k (s : Set M)).subtype p) :=
        (LinearEquiv.finrank_eq e).symm
    _ ≤ Module.finrank k (Submodule.span k (s : Set M)) := Submodule.finrank_le _
    _ ≤ s.card := finrank_span_finset_le_card (R := k) s

variable [IsNoetherian X]

variable (X) in
/-- The component of a global family of principal parts at a codimension-one point,
`k`-linearly. -/
noncomputable def partsProjₗ (i : Index (⊤ : X.Opens)) :
    Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) →ₗ[k]
      Component (0 : AlgebraicCycle X ℤ) i.2.1 where
  toFun s := s.1 i
  map_add' s t := rfl
  map_smul' r s := by
    simp only [RingHom.id_apply]
    have hsg : structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r
        = globalSec (X := X) (R := CommRingCat.of k) r := by
      rw [structureRingHom_apply, Subsingleton.elim (⊤ : X.Opens).leTop.op (𝟙 _)]
      simp
    show X.presheaf.germ ⊤ i.1 i.2.2
        (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) • s.1 i
      = algebraMap k ↑(X.presheaf.stalk i.1) r • s.1 i
    rw [hsg]
    rfl

variable (X) in
/-- The classes of pole order at most `n` at `q`, as a submodule of the principal parts. -/
noncomputable def componentBounded {q : X} (hq : coheight q = 1) (n : ℤ) :
    Submodule k (Component (0 : AlgebraicCycle X ℤ) hq) :=
  Submodule.map (componentMkₗ X k hq) ((ordSubmodule hq (-n)).restrictScalars k)

lemma componentBounded_eq_bot {q : X} (hq : coheight q = 1) {n : ℤ} (hn : n ≤ 0) :
    componentBounded X k hq n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨f, hf, rfl⟩
  refine component_mk_eq_zero hq ?_
  rw [mem_ordSubmodule_iff]
  intro hne
  have h1 := hf hne
  omega

lemma componentBounded_mono {q : X} (hq : coheight q = 1) {n n' : ℤ} (h : n ≤ n') :
    componentBounded X k hq n ≤ componentBounded X k hq n' :=
  Submodule.map_mono fun f hf hne => by
    have h1 := hf hne
    omega

/-- The bounded classes form a finite-dimensional space of dimension at most
`n · dim κ(q)`. -/
lemma finite_finrank_componentBounded {q : X} (hq : coheight q = 1)
    [Module.Finite k ↑(X.residueField q)] (n : ℤ) :
    Module.Finite k (componentBounded X k hq n) ∧
    Module.finrank k (componentBounded X k hq n)
      ≤ n.toNat * Module.finrank k ↑(X.residueField q) := by
  obtain ⟨s, hcard, hspan⟩ := exists_finset_span_component k hq n.toNat
  have hle : componentBounded X k hq n ≤ Submodule.span k (s : Set _) := by
    rintro x ⟨f, hf, rfl⟩
    refine hspan f fun hne => ?_
    have h1 := hf hne
    omega
  obtain ⟨h1, h2⟩ := finite_and_finrank_le_of_le_span k hle
  exact ⟨h1, h2.trans hcard⟩

variable (X) in
/-- The families of principal parts bounded by the divisor `D`. -/
noncomputable def boundedFamilies (D : AlgebraicCycle X ℤ) :
    Submodule k Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) :=
  ⨅ i : Index (⊤ : X.Opens),
    Submodule.comap (partsProjₗ X k i) (componentBounded X k i.2.1 (D i.1))

lemma mem_boundedFamilies_iff {D : AlgebraicCycle X ℤ}
    {s : Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens))} :
    s ∈ boundedFamilies X k D ↔ ∀ i : Index (⊤ : X.Opens),
      partsProjₗ X k i s ∈ componentBounded X k i.2.1 (D i.1) := by
  simp [boundedFamilies, Submodule.mem_iInf]

lemma boundedFamilies_mono {D D' : AlgebraicCycle X ℤ} (h : D ≤ D') :
    boundedFamilies X k D ≤ boundedFamilies X k D' := by
  intro s hs
  rw [mem_boundedFamilies_iff] at hs ⊢
  exact fun i => componentBounded_mono k i.2.1 (h i.1) (hs i)

/-- The support of a divisor on a Noetherian scheme is finite. -/
lemma support_finite (D : AlgebraicCycle X ℤ) : D.support.Finite := by
  refine Set.Finite.subset (LocallyFiniteSupport.finite_inter_support_of_isCompact
    D.locallyFiniteSupport
    (NoetherianSpace.isCompact ((⊤ : TopologicalSpace.Opens ↥X) : Set ↥X))) ?_
  intro q hq
  exact ⟨trivial, hq⟩

/-- **`dim P_D ≤ deg D`.** The families bounded by an effective divisor supported in
codimension one form a finite-dimensional space of dimension at most `deg D`: the family
embeds into the product of its components over the (finite) support, and each component
space has dimension at most `D q · dim κ(q)`. -/
lemma finite_finrank_boundedFamilies (D : AlgebraicCycle X ℤ) (hDpos : 0 ≤ D)
    (hD : D.support ⊆ {x | coheight x = 1})
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q)) :
    Module.Finite k (boundedFamilies X k D) ∧
    (Module.finrank k (boundedFamilies X k D) : ℤ) ≤ D.degree k := by
  classical
  -- the (finite) support of the divisor
  set T : Finset X := (support_finite D).toFinset with hT
  have hmemT : ∀ q : X, q ∈ T ↔ q ∈ D.support := fun q => Set.Finite.mem_toFinset _
  have hcod : ∀ q ∈ T, coheight q = 1 := fun q hq => hD ((hmemT q).mp hq)
  haveI : ∀ q : ↥T, Module.Finite k ↑(X.residueField q.1) :=
    fun q => hκ q.1 (hcod q.1 q.2)
  haveI : ∀ q : ↥T, Module.Finite k (componentBounded X k (hcod q.1 q.2) (D q.1)) :=
    fun q => (finite_finrank_componentBounded k (hcod q.1 q.2) (D q.1)).1
  -- embed into the product of the bounded components over the support
  set Φ : ↥(boundedFamilies X k D) →ₗ[k]
      (∀ q : ↥T, ↥(componentBounded X k (hcod q.1 q.2) (D q.1))) :=
    LinearMap.pi fun q => LinearMap.codRestrict _
      ((partsProjₗ X k ⟨q.1, hcod q.1 q.2, trivial⟩).comp
        (boundedFamilies X k D).subtype)
      (fun s => (mem_boundedFamilies_iff k).mp s.2 ⟨q.1, hcod q.1 q.2, trivial⟩) with hΦ
  have hΦinj : Function.Injective Φ := by
    intro s t hst
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i.1 ∈ D.support
    · exact congrArg Subtype.val (congrFun hst ⟨i.1, (hmemT i.1).mpr hi⟩)
    · have hD0 : D i.1 = 0 := by
        by_contra h0
        exact hi (Function.mem_support.mpr h0)
      have h1 := (mem_boundedFamilies_iff k).mp s.2 i
      have h2 := (mem_boundedFamilies_iff k).mp t.2 i
      rw [hD0, componentBounded_eq_bot k i.2.1 le_rfl, Submodule.mem_bot] at h1 h2
      exact h1.trans h2.symm
  refine ⟨Module.Finite.of_injective Φ hΦinj, ?_⟩
  -- rank comparison through the product
  have h1 : Module.finrank k ↥(boundedFamilies X k D)
      ≤ Module.finrank k (∀ q : ↥T, ↥(componentBounded X k (hcod q.1 q.2) (D q.1))) :=
    LinearMap.finrank_le_finrank_of_injective hΦinj
  rw [Module.finrank_pi_fintype] at h1
  have h2 : ∑ q : ↥T, Module.finrank k ↥(componentBounded X k (hcod q.1 q.2) (D q.1))
      ≤ ∑ q : ↥T, (D q.1).toNat * Module.finrank k ↑(X.residueField q.1) :=
    Finset.sum_le_sum fun q _ => (finite_finrank_componentBounded k (hcod q.1 q.2) (D q.1)).2
  -- identify the degree with the sum over the support
  have h3 : D.degree k
      = ∑ q : ↥T, D q.1 * (Module.finrank k ↑(X.residueField q.1) : ℤ) := by
    rw [AlgebraicCycle.degree,
      finsum_eq_finsetSum_of_support_subset _ (s := T)
        (by
          intro q hq
          have hq' : D q ≠ 0 := left_ne_zero_of_mul hq
          exact (hmemT q).mpr hq')]
    exact (Finset.sum_coe_sort T
      (fun q => D q * (Module.finrank k ↑(X.residueField q) : ℤ))).symm
  calc (Module.finrank k ↥(boundedFamilies X k D) : ℤ)
      ≤ ((∑ q : ↥T, (D q.1).toNat *
          Module.finrank k ↑(X.residueField q.1) : ℕ) : ℤ) := by
        exact_mod_cast h1.trans h2
    _ = D.degree k := by
        rw [h3]
        push_cast
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Int.toNat_of_nonneg (hDpos q.1)]

end BoundedFamilies

/-! ### The reduction: `deg D ≤ ℓ(D) + C` implies a finite adelic cokernel -/

section Reduction

variable [IsRegularInCodimensionOne X] [IsNoetherian X]

open PrincipalParts

/-- The principal parts of functions in `L(D)` are bounded by `D`. -/
lemma map_LSubmodule_le_boundedFamilies (D : AlgebraicCycle X ℤ) :
    Submodule.map (principalPartsₗ X k) (LSubmodule X k D) ≤ boundedFamilies X k D := by
  rintro x ⟨f, hf, rfl⟩
  rw [mem_boundedFamilies_iff]
  intro i
  refine Submodule.mem_map.mpr ⟨f, mem_ordSubmodule_of_mem_carrier (D := D) hf i.2.1 trivial, ?_⟩
  exact (principalPartsₗ_apply_coe k f i).symm

/-- The kernel of the principal-parts map is `L(0)`: a rational function with vanishing
principal parts everywhere is everywhere regular. -/
lemma ker_principalPartsₗ :
    LinearMap.ker (principalPartsₗ X k) = LSubmodule X k (0 : AlgebraicCycle X ℤ) := by
  ext f
  rw [LinearMap.mem_ker, mem_LSubmodule_iff]
  constructor
  · intro h0
    refine mem_carrier_of_forall_ordSubmodule (D := 0) (U := (⊤ : X.Opens)) (by simp)
      ⟨⟨genericPoint X, trivial⟩⟩ fun q hq hqU => ?_
    refine (Component.mk_eq_zero_iff 0 hq).mp ?_
    rw [← principalPartsₗ_apply_coe k f ⟨q, hq, hqU⟩, h0]
    rfl
  · intro hf
    apply Subtype.ext
    funext i
    rw [principalPartsₗ_apply_coe]
    exact ((Component.mk_eq_zero_iff 0 i.2.1).mpr
      (mem_ordSubmodule_of_mem_carrier (D := 0) hf i.2.1 trivial)).trans rfl

/-- `L(D)` is finite dimensional for effective `D` once `L(0)` is: modulo the constants it
embeds into the (finite-dimensional) space of families bounded by `D`. -/
lemma finite_LSubmodule
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    (D : AlgebraicCycle X ℤ) (hDpos : 0 ≤ D)
    (hD : D.support ⊆ {x | coheight x = 1}) :
    Module.Finite k (LSubmodule X k D) := by
  rw [Module.Finite.iff_fg]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (principalPartsₗ X k) ?_ ?_
  · -- the image is contained in the finite-dimensional space of bounded families
    haveI := (finite_finrank_boundedFamilies k D hDpos hD hκ).1
    haveI : Module.Finite k
        (Submodule.map (principalPartsₗ X k) (LSubmodule X k D)) :=
      Module.Finite.equiv
        (Submodule.comapSubtypeEquivOfLe (map_LSubmodule_le_boundedFamilies k D))
    exact Module.Finite.iff_fg.mp ‹_›
  · rw [ker_principalPartsₗ,
      inf_eq_right.mpr (LSubmodule_mono k hDpos)]
    exact Module.Finite.iff_fg.mp hL0

/-- The counting identity `ℓ(D) = dim φ(L(D)) + ℓ(0)`: the principal-parts map on `L(D)` has
kernel exactly the constants `L(0)`. -/
lemma finrank_LSubmodule_eq
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    (D : AlgebraicCycle X ℤ) (hDpos : 0 ≤ D)
    (hD : D.support ⊆ {x | coheight x = 1}) :
    Module.finrank k (LSubmodule X k D)
      = Module.finrank k (Submodule.map (principalPartsₗ X k) (LSubmodule X k D))
        + Module.finrank k (LSubmodule X k (0 : AlgebraicCycle X ℤ)) := by
  haveI := finite_LSubmodule k hκ hL0 D hDpos hD
  have h := LinearMap.finrank_range_add_finrank_ker
    ((principalPartsₗ X k).comp (LSubmodule X k D).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
    ker_principalPartsₗ,
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (LSubmodule_mono k hDpos))] at h
  omega

/-- The **Riemann upper bound** `ℓ(D) ≤ deg D + ℓ(0)` for effective `D` supported in
codimension one: `L(D)` modulo the constants embeds into the space of families of principal
parts bounded by `D`, which has dimension at most `deg D`. This is the easy half of the
Riemann counting, used to compare the degree of a pole divisor with the field degree. -/
lemma finrank_LSubmodule_le
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    (D : AlgebraicCycle X ℤ) (hDpos : 0 ≤ D)
    (hD : D.support ⊆ {x | coheight x = 1}) :
    (Module.finrank k (LSubmodule X k D) : ℤ)
      ≤ D.degree k
        + Module.finrank k (LSubmodule X k (0 : AlgebraicCycle X ℤ)) := by
  haveI := (finite_finrank_boundedFamilies k D hDpos hD hκ).1
  have h1 := finrank_LSubmodule_eq k hκ hL0 D hDpos hD
  have h2 : Module.finrank k
      (Submodule.map (principalPartsₗ X k) (LSubmodule X k D))
      ≤ Module.finrank k (boundedFamilies X k D) :=
    Submodule.finrank_mono (map_LSubmodule_le_boundedFamilies k D)
  have h3 := (finite_finrank_boundedFamilies k D hDpos hD hκ).2
  omega

/-- **The reduction to Riemann's inequality.** If `deg D ≤ ℓ(D) + C` uniformly over
effective divisors supported in codimension one, then the space of global principal parts
modulo rational functions is finite dimensional: it is the directed union over `D` of the
images of the bounded families `P_D`, each of dimension at most
`deg D − ℓ(D) + ℓ(0) ≤ C + ℓ(0)`. -/
theorem finite_partsCoker_of_degree_le
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    (C : ℕ)
    (hC : ∀ D : AlgebraicCycle X ℤ, 0 ≤ D → D.support ⊆ {x | coheight x = 1} →
      D.degree k ≤ (Module.finrank k (LSubmodule X k D) : ℤ) + C) :
    Module.Finite k
      (Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) ⧸
        LinearMap.range (appTopₗ k (toPartsHom (0 : AlgebraicCycle X ℤ)))) := by
  classical
  set R : Submodule k Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) :=
    LinearMap.range (appTopₗ k (toPartsHom (0 : AlgebraicCycle X ℤ))) with hR
  set ι : Type u :=
    {D : AlgebraicCycle X ℤ // 0 ≤ D ∧ D.support ⊆ {x | coheight x = 1}} with hι
  haveI : Nonempty ι := ⟨⟨0, le_refl _, by simp⟩⟩
  set N : ι → Submodule k
      (Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) ⧸ R) :=
    fun D => Submodule.map R.mkQ (boundedFamilies X k D.1) with hN
  refine module_finite_of_directed_of_bounded k N ?_ ?_
    (C + Module.finrank k (LSubmodule X k (0 : AlgebraicCycle X ℤ))) ?_ ?_
  · -- directedness: `D + D'` dominates both
    intro i j
    refine ⟨⟨i.1 + j.1, add_nonneg i.2.1 j.2.1, ?_⟩, ?_, ?_⟩
    · intro q hq
      have h1 : i.1 q + j.1 q ≠ 0 := hq
      rcases eq_or_ne (i.1 q) 0 with h2 | h2
      · exact j.2.2 (Function.mem_support.mpr fun h3 => h1 (by rw [h2, h3, add_zero]))
      · exact i.2.2 (Function.mem_support.mpr h2)
    · exact Submodule.map_mono (boundedFamilies_mono k (le_add_of_nonneg_right j.2.1))
    · exact Submodule.map_mono (boundedFamilies_mono k (le_add_of_nonneg_left i.2.1))
  · -- covering: every class of families is bounded by the divisor of chosen representatives
    intro x
    obtain ⟨s, rfl⟩ := R.mkQ_surjective x
    -- choose a representative for each component, `0` for the zero components
    have hrep : ∀ i : Index (⊤ : X.Opens), ∃ f : ↑X.functionField,
        Component.mk 0 i.2.1 f = s.1 i ∧ (s.1 i = 0 → f = 0) := by
      intro i
      rcases eq_or_ne (s.1 i) 0 with h0 | h0
      · exact ⟨0, by rw [h0]; exact map_zero (componentMkₗ X k i.2.1), fun _ => rfl⟩
      · obtain ⟨f, hf⟩ := Component.mk_surjective 0 i.2.1 (s.1 i)
        exact ⟨f, hf, fun h => absurd h h0⟩
    choose rep hrep1 hrep2 using hrep
    -- the divisor of pole bounds
    set Efun : X → ℤ := fun q => if h : coheight q = 1 then
        max 0 (- X.ord (rep ⟨q, h, trivial⟩) q) else 0 with hEfun
    have hEsupp : Function.support Efun ⊆ suppSet 0 s.1 := by
      intro q hq
      have hq' : (if h : coheight q = 1 then
          max 0 (- X.ord (rep ⟨q, h, trivial⟩) q) else 0) ≠ 0 := hq
      by_cases h : coheight q = 1
      · rw [dif_pos h] at hq'
        have hordneg : X.ord (rep ⟨q, h, trivial⟩) q < 0 := by
          by_contra hle
          push_neg at hle
          exact hq' (by omega)
        have hrep0 : rep ⟨q, h, trivial⟩ ≠ 0 := fun h0 => by
          rw [h0] at hordneg
          simp at hordneg
        show q ∈ suppSet (0 : AlgebraicCycle X ℤ) s.1
        exact ⟨⟨h, (trivial : q ∈ (⊤ : X.Opens))⟩,
          fun h0 => hrep0 (hrep2 ⟨q, h, trivial⟩ h0)⟩
      · rw [dif_neg h] at hq'
        exact absurd rfl hq'
    set E : AlgebraicCycle X ℤ :=
      { toFun := Efun
        supportWithinDomain' := by simp
        supportLocallyFiniteWithinDomain' := fun z _ =>
          ⟨Set.univ, Filter.univ_mem,
            (s.2.subset hEsupp).subset Set.inter_subset_right⟩ }
    have hEpos : (0 : AlgebraicCycle X ℤ) ≤ E := by
      intro q
      show (0 : AlgebraicCycle X ℤ) q ≤ (if h : coheight q = 1 then
          max 0 (- X.ord (rep ⟨q, h, trivial⟩) q) else 0)
      have h0 : (0 : AlgebraicCycle X ℤ) q = 0 := rfl
      rw [h0]
      by_cases h : coheight q = 1
      · rw [dif_pos h]
        exact le_max_left 0 _
      · rw [dif_neg h]
    have hEcod : E.support ⊆ {x | coheight x = 1} := by
      intro q hq
      have h1 : (if h : coheight q = 1 then
          max 0 (- X.ord (rep ⟨q, h, trivial⟩) q) else 0) ≠ 0 := hq
      show coheight q = 1
      by_contra h
      rw [dif_neg h] at h1
      exact h1 rfl
    have hsE : s ∈ boundedFamilies X k E := by
      rw [mem_boundedFamilies_iff]
      intro i
      refine Submodule.mem_map.mpr ⟨rep i, ?_, hrep1 i⟩
      intro hne
      have hE : E i.1 = max 0 (- X.ord (rep ⟨i.1, i.2.1, trivial⟩) i.1) := dif_pos i.2.1
      have hrr : rep i = rep ⟨i.1, i.2.1, trivial⟩ := rfl
      rw [hE, hrr]
      omega
    exact ⟨⟨E, hEpos, hEcod⟩, Submodule.mem_map_of_mem hsE⟩
  · -- each image is finite dimensional
    intro D
    haveI := (finite_finrank_boundedFamilies k D.1 D.2.1 D.2.2 hκ).1
    exact Module.Finite.map _ _
  · -- and of dimension at most `C + ℓ(0)`
    intro D
    haveI hPD := (finite_finrank_boundedFamilies k D.1 D.2.1 D.2.2 hκ).1
    set g : ↥(boundedFamilies X k D.1) →ₗ[k]
        (Γ(partsSheaf (0 : AlgebraicCycle X ℤ), (⊤ : X.Opens)) ⧸ R) :=
      R.mkQ.comp (boundedFamilies X k D.1).subtype with hg
    have hrange : LinearMap.range g = N D := by
      rw [hg, LinearMap.range_comp, Submodule.range_subtype]
    -- the image of `L(D)` sits inside the kernel of `g`
    have hWle : Submodule.comap (boundedFamilies X k D.1).subtype
        (Submodule.map (principalPartsₗ X k) (LSubmodule X k D.1))
        ≤ LinearMap.ker g := by
      rintro ⟨v, hv⟩ hmem
      obtain ⟨f, hf, hvf⟩ := hmem
      rw [LinearMap.mem_ker]
      show R.mkQ v = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hR,
        ← range_principalPartsₗ k]
      exact ⟨f, hvf⟩
    have hWrank : Module.finrank k
        (Submodule.comap (boundedFamilies X k D.1).subtype
          (Submodule.map (principalPartsₗ X k) (LSubmodule X k D.1)))
        = Module.finrank k
          (Submodule.map (principalPartsₗ X k) (LSubmodule X k D.1)) :=
      LinearEquiv.finrank_eq
        (Submodule.comapSubtypeEquivOfLe (map_LSubmodule_le_boundedFamilies k D.1))
    have h5 : Module.finrank k
        (Submodule.map (principalPartsₗ X k) (LSubmodule X k D.1))
        ≤ Module.finrank k (LinearMap.ker g) := by
      rw [← hWrank]
      exact Submodule.finrank_mono hWle
    have hrn := LinearMap.finrank_range_add_finrank_ker g
    have hle : Module.finrank k (N D) = Module.finrank k (LinearMap.range g) := by
      rw [hrange]
    have hdeg := (finite_finrank_boundedFamilies k D.1 D.2.1 D.2.2 hκ).2
    have hCC := hC D.1 D.2.1 D.2.2
    have hcount := finrank_LSubmodule_eq k hκ hL0 D.1 D.2.1 D.2.2
    have hgoal : Module.finrank k (LinearMap.range g)
        ≤ C + Module.finrank k (LSubmodule X k (0 : AlgebraicCycle X ℤ)) := by
      omega
    exact hle.trans_le hgoal

end Reduction

/-! ### The field degree is bounded by the pole degree

For a transcendental rational function `f`, any family of elements of `k(X)` linearly
independent over `k(f)` has size at most `deg (f)_∞`: the products `f^j·yᵢ`, `0 ≤ j ≤ m`,
are `k`-linearly independent (powers of a transcendental element are independent, and
independence multiplies through the tower `k ⊆ k(f) ⊆ k(X)`) and lie in
`L(m·(f)_∞ + C₀)`, whose dimension is at most `m·deg (f)_∞ + O(1)` by the Riemann upper
bound. In particular `k(X)` is a **finite** extension of `k(f)`, of degree at most
`deg (f)_∞` — with no input from the dimension theory of finitely generated algebras. -/

section FieldDegree

variable [IsRegularInCodimensionOne X] [IsNoetherian X]

/-- A Noetherian scheme is compact (for the degree additivity of divisors). -/
noncomputable instance : CompactSpace ↥X := ⟨NoetherianSpace.isCompact _⟩

/-- Powers of a transcendental element are linearly independent over the base field. -/
lemma linearIndependent_pow_of_transcendental {A : Type u} [CommRing A] [Algebra k A]
    {x : A} (hx : Transcendental k x) :
    LinearIndependent k fun j : ℕ => x ^ j := by
  have hker : LinearMap.ker (Polynomial.aeval (R := k) x).toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    exact transcendental_iff.mp hx p hp
  have h := (Polynomial.basisMonomials k).linearIndependent.map'
    (Polynomial.aeval (R := k) x).toLinearMap hker
  have heq : (⇑(Polynomial.aeval (R := k) x).toLinearMap ∘ ⇑(Polynomial.basisMonomials k))
      = fun j : ℕ => x ^ j := by
    funext j
    simp [Polynomial.coe_basisMonomials, Polynomial.aeval_monomial]
  rwa [heq] at h

omit [IsRegularInCodimensionOne X] [IsNoetherian X] in
/-- The order of `1` vanishes everywhere. -/
lemma ord_one (z : X) : X.ord (1 : ↑X.functionField) z = 0 := by
  by_cases hz : coheight z = 1
  · rw [ord_eq_iff hz one_ne_zero]
    simp
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hz 1

omit [IsRegularInCodimensionOne X] [IsNoetherian X] in
/-- The order of a power. -/
lemma ord_pow {f : ↑X.functionField} (hf0 : f ≠ 0) (j : ℕ) (z : X) :
    X.ord (f ^ j) z = (j : ℤ) * X.ord f z := by
  induction j with
  | zero => simpa using ord_one z
  | succ i ih =>
    by_cases hz : coheight z = 1
    · rw [pow_succ, ord_mul hz (pow_ne_zero i hf0) hf0, ih]
      push_cast
      ring
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz,
        Scheme.ord_eq_zero_of_coheight_neq_one hz]
      ring

variable (X) in
/-- The pole divisor `(f)_∞` of a rational function: `max 0 (−ord_q f)` at each point. -/
noncomputable def polePart (f : ↑X.functionField) : AlgebraicCycle X ℤ where
  toFun q := max 0 (- X.ord f q)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z hz := by
    obtain ⟨t, ht, hfin⟩ := (div f).supportLocallyFiniteWithinDomain' z hz
    refine ⟨t, ht, hfin.subset fun q hq => ⟨hq.1, ?_⟩⟩
    have h1 : max 0 (- X.ord f q) ≠ 0 := hq.2
    have h2 : X.ord f q ≠ 0 := by omega
    simpa [div_eq_ord] using h2

lemma polePart_nonneg (f : ↑X.functionField) : 0 ≤ polePart X f := fun q => by
  show (0 : AlgebraicCycle X ℤ) q ≤ max 0 (- X.ord f q)
  have h0 : (0 : AlgebraicCycle X ℤ) q = 0 := rfl
  omega

lemma polePart_support (f : ↑X.functionField) :
    (polePart X f).support ⊆ {x | coheight x = 1} := fun q hq => by
  have h1 : max 0 (- X.ord f q) ≠ 0 := hq
  show coheight q = 1
  by_contra h
  rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at h1
  simp at h1

/-- Every rational function is a global section of `𝒪ₓ((f)_∞)`. -/
lemma mem_carrier_polePart (f : ↑X.functionField) :
    f ∈ Sheaf.carrier (polePart X f) ⊤ :=
  Sheaf.mem_carrier_iff.mpr fun _ => ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z _ => by
    show 0 ≤ X.ord f z + max 0 (- X.ord f z)
    omega⟩

variable (X) in
/-- Evaluation of cycles at a point, as an additive map. -/
noncomputable def evalCycle (q : X) : AlgebraicCycle X ℤ →+ ℤ where
  toFun D := D q
  map_zero' := rfl
  map_add' _ _ := rfl

lemma cycle_finset_sum_apply {ι : Type*} (s : Finset ι) (D : ι → AlgebraicCycle X ℤ)
    (q : X) : (∑ i ∈ s, D i) q = ∑ i ∈ s, D i q :=
  map_sum (evalCycle X q) D s

lemma cycle_nsmul_apply (m : ℕ) (B : AlgebraicCycle X ℤ) (q : X) :
    (m • B) q = (m : ℤ) * B q := by
  have h := map_nsmul (evalCycle X q) m B
  simpa [nsmul_eq_mul] using h

lemma degree_zero : (0 : AlgebraicCycle X ℤ).degree k = 0 := by
  rw [AlgebraicCycle.degree]
  convert finsum_zero with q
  show (0 : AlgebraicCycle X ℤ) q * _ = 0
  rw [show (0 : AlgebraicCycle X ℤ) q = 0 from rfl, zero_mul]

lemma degree_nsmul (m : ℕ) (D : AlgebraicCycle X ℤ) :
    (m • D).degree k = (m : ℤ) * D.degree k := by
  induction m with
  | zero =>
    rw [zero_nsmul, degree_zero k]
    simp
  | succ i ih =>
    rw [succ_nsmul, AlgebraicCycle.degree_sum k _ _, ih]
    push_cast
    ring

lemma degree_nonneg {D : AlgebraicCycle X ℤ} (hD : 0 ≤ D) : 0 ≤ D.degree k := by
  rw [AlgebraicCycle.degree]
  refine finsum_nonneg fun q => ?_
  have h1 : (0 : ℤ) ≤ D q := by
    have h2 := hD q
    rwa [show (0 : AlgebraicCycle X ℤ) q = 0 from rfl] at h2
  exact mul_nonneg h1 (by positivity)

open IntermediateField in
/-- **The field degree is bounded by the pole degree.** Any family of rational functions
linearly independent over `k(f)` has size at most `deg (f)_∞`. -/
theorem card_le_degree_polePart
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {f : ↑X.functionField} (hft : Transcendental k f)
    {n : ℕ} {y : Fin n → ↑X.functionField}
    (hy : LinearIndependent ↥(adjoin k {f}) y) :
    (n : ℤ) ≤ (polePart X f).degree k := by
  classical
  have hf0 : f ≠ 0 := fun h => hft (h ▸ isAlgebraic_zero)
  set B := polePart X f with hB
  set E : Fin n → AlgebraicCycle X ℤ := fun i => polePart X (y i) with hE
  set C₀ : AlgebraicCycle X ℤ := ∑ i, E i with hC₀
  -- the sum of the pole divisors of the `yᵢ` is effective and supported in codimension one
  have hC₀pos : 0 ≤ C₀ := by
    intro q
    show (0 : AlgebraicCycle X ℤ) q ≤ (∑ i, E i) q
    rw [cycle_finset_sum_apply, show (0 : AlgebraicCycle X ℤ) q = 0 from rfl]
    refine Finset.sum_nonneg fun i _ => ?_
    show (0 : ℤ) ≤ max 0 (- X.ord (y i) q)
    omega
  have hC₀cod : C₀.support ⊆ {x | coheight x = 1} := by
    intro q hq
    have h1 : (∑ i, E i) q ≠ 0 := hq
    rw [cycle_finset_sum_apply] at h1
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    exact polePart_support (y i) (Function.mem_support.mpr hi)
  -- each `yᵢ` is a section of `𝒪(C₀)`
  have hEle : ∀ i, E i ≤ C₀ := fun i => by
    intro q
    show E i q ≤ (∑ j, E j) q
    rw [cycle_finset_sum_apply]
    exact Finset.single_le_sum (f := fun j => E j q)
      (fun j _ => by show (0 : ℤ) ≤ max 0 (- X.ord (y j) q); omega) (Finset.mem_univ i)
  have hyC : ∀ i, y i ∈ Sheaf.carrier C₀ ⊤ := fun i =>
    carrier_mono (hEle i) (mem_carrier_polePart (y i))
  -- effectivity and support of the tower divisors
  have hDpos : ∀ m : ℕ, 0 ≤ m • B + C₀ := fun m =>
    add_nonneg (nsmul_nonneg (polePart_nonneg f) m) hC₀pos
  have hDcod : ∀ m : ℕ, (m • B + C₀).support ⊆ {x | coheight x = 1} := by
    intro m q hq
    have h1 : (m • B) q + C₀ q ≠ 0 := hq
    rcases eq_or_ne ((m • B) q) 0 with h2 | h2
    · exact hC₀cod (Function.mem_support.mpr fun h3 => h1 (by rw [h2, h3, add_zero]))
    · rw [cycle_nsmul_apply] at h2
      have h4 : B q ≠ 0 := fun h5 => h2 (by rw [h5, mul_zero])
      exact polePart_support f (Function.mem_support.mpr h4)
  -- the products `f^j·yᵢ` are independent sections of `L(m·B + C₀)`
  have key : ∀ m : ℕ, (m + 1) * n ≤ Module.finrank k (LSubmodule X k (m • B + C₀)) := by
    intro m
    haveI := finite_LSubmodule k hκ hL0 _ (hDpos m) (hDcod m)
    have hmem : ∀ p : Fin (m + 1) × Fin n,
        f ^ (p.1 : ℕ) * y p.2 ∈ LSubmodule X k (m • B + C₀) := by
      rintro ⟨j, i⟩
      have hy0 : y i ≠ 0 := hy.ne_zero i
      rw [mem_LSubmodule_iff]
      refine Sheaf.mem_carrier_iff.mpr fun hne =>
        ⟨⟨⟨genericPoint X, trivial⟩⟩, fun z _ => ?_⟩
      have hyz := (Sheaf.mem_carrier_iff.mp (hyC i) hy0).2 z trivial
      have hordp : X.ord (f ^ (j : ℕ) * y i) z
          = ((j : ℕ) : ℤ) * X.ord f z + X.ord (y i) z := by
        by_cases hz1 : coheight z = 1
        · rw [ord_mul hz1 (pow_ne_zero _ hf0) hy0, ord_pow hf0]
        · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz1,
            Scheme.ord_eq_zero_of_coheight_neq_one hz1,
            Scheme.ord_eq_zero_of_coheight_neq_one hz1]
          ring
      have happ : (m • B + C₀) z = (m : ℤ) * max 0 (- X.ord f z) + C₀ z := by
        have h1 : (m • B + C₀) z = (m • B) z + C₀ z := rfl
        rw [h1, cycle_nsmul_apply]
        rfl
      have hj2 : ((j : ℕ) : ℤ) ≤ (m : ℤ) := by
        exact_mod_cast Nat.lt_succ_iff.mp j.isLt
      have hbound : -((m : ℤ) * max 0 (- X.ord f z)) ≤ ((j : ℕ) : ℤ) * X.ord f z := by
        by_cases h : 0 ≤ X.ord f z
        · have h1 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) * X.ord f z := mul_nonneg (by positivity) h
          have h2 : max 0 (- X.ord f z) = 0 := by omega
          rw [h2, mul_zero, neg_zero]
          exact h1
        · have h' : X.ord f z < 0 := not_le.mp h
          have h2 : max 0 (- X.ord f z) = - X.ord f z := by omega
          rw [h2]
          have h3 : (m : ℤ) * X.ord f z ≤ ((j : ℕ) : ℤ) * X.ord f z :=
            mul_le_mul_of_nonpos_right hj2 (le_of_lt h')
          have h4 : -((m : ℤ) * - X.ord f z) = (m : ℤ) * X.ord f z := by ring
          rw [h4]
          exact h3
      rw [hordp, happ]
      linarith [hbound, hyz]
    -- independence of the products through the tower
    have hgen : Transcendental k (AdjoinSimple.gen k f) := by
      rintro ⟨p, hp0, hp⟩
      refine hft ⟨p, hp0, ?_⟩
      have h3 := Polynomial.aeval_algebraMap_apply ↑X.functionField
        (AdjoinSimple.gen k f) p
      rw [IntermediateField.AdjoinSimple.algebraMap_gen] at h3
      rw [h3, hp]
      exact map_zero _
    have hpow : LinearIndependent k
        fun j : Fin (m + 1) => (AdjoinSimple.gen k f) ^ (j : ℕ) :=
      (linearIndependent_pow_of_transcendental k hgen).comp
        (fun j : Fin (m + 1) => (j : ℕ)) Fin.val_injective
    have hsm := _root_.linearIndependent_smul hpow hy
    have hfun : (fun p : Fin (m + 1) × Fin n =>
          ((AdjoinSimple.gen k f) ^ (p.1 : ℕ)) • y p.2)
        = fun p : Fin (m + 1) × Fin n => f ^ (p.1 : ℕ) * y p.2 := by
      funext p
      rw [Algebra.smul_def]
      congr 1
    rw [hfun] at hsm
    have hres : LinearIndependent k fun p : Fin (m + 1) × Fin n =>
        (⟨f ^ (p.1 : ℕ) * y p.2, hmem p⟩ : ↥(LSubmodule X k (m • B + C₀))) := by
      apply LinearIndependent.of_comp (LSubmodule X k (m • B + C₀)).subtype
      exact hsm
    have hcard := hres.fintype_card_le_finrank
    simpa using hcard
  -- the Riemann upper bound along the tower
  have upper : ∀ m : ℕ, (Module.finrank k (LSubmodule X k (m • B + C₀)) : ℤ)
      ≤ (m : ℤ) * B.degree k + (C₀.degree k
        + (Module.finrank k (LSubmodule X k (0 : AlgebraicCycle X ℤ)) : ℤ)) := by
    intro m
    have h1 := finrank_LSubmodule_le k hκ hL0 _ (hDpos m) (hDcod m)
    have h2 : (m • B + C₀).degree k = (m : ℤ) * B.degree k + C₀.degree k := by
      rw [AlgebraicCycle.degree_sum k _ _, degree_nsmul]
    rw [h2] at h1
    linarith
  -- conclude: `n ≤ deg B` by taking `m` large
  set d := B.degree k with hd
  set c := C₀.degree k
    + (Module.finrank k (LSubmodule X k (0 : AlgebraicCycle X ℤ)) : ℤ) with hc
  have hc0 : 0 ≤ c := add_nonneg (degree_nonneg k hC₀pos) (by positivity)
  by_contra hlt
  push_neg at hlt
  set m : ℕ := c.toNat + 1 with hm
  have h3 : ((m : ℤ) + 1) * n ≤ (m : ℤ) * d + c := by
    calc ((m : ℤ) + 1) * n = (((m + 1) * n : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (Module.finrank k (LSubmodule X k (m • B + C₀)) : ℤ) := by
          exact_mod_cast key m
      _ ≤ (m : ℤ) * d + c := upper m
  have h4 : (m : ℤ) * d ≤ (m : ℤ) * ((n : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have h5 : ((m : ℤ) + 1) * n ≤ (m : ℤ) * ((n : ℤ) - 1) + c :=
    le_trans h3 (by linarith [h4])
  have h6 : (n : ℤ) + (m : ℤ) ≤ c := by nlinarith [h5]
  have h7 : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc0
  omega

open IntermediateField in
/-- **Finiteness of the field degree.** `k(X)` is a finite extension of `k(f)` for any
transcendental rational function `f`. This discharges the field-theoretic input to
Chevalley's proof of Riemann's inequality without any dimension theory of finitely
generated algebras. -/
theorem finite_adjoin_of_transcendental
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {f : ↑X.functionField} (hft : Transcendental k f) :
    Module.Finite ↥(adjoin k {f}) ↑X.functionField := by
  rw [← Module.rank_lt_aleph0_iff]
  have hbound : Module.rank ↥(adjoin k {f}) ↑X.functionField
      ≤ (((polePart X f).degree k).toNat : Cardinal) := by
    refine _root_.rank_le fun s hs => ?_
    have h1 := card_le_degree_polePart k hκ hL0 hft
      (y := fun i : Fin s.card => (s.equivFin.symm i : ↑X.functionField))
      (hs.comp _ s.equivFin.symm.injective)
    omega
  exact lt_of_le_of_lt hbound Cardinal.natCast_lt_aleph0

end FieldDegree

/-! ### Riemann–Roch, assuming only the divisor-theoretic Riemann inequality -/

section RiemannRoch

variable [IsRegularInCodimensionOne X] [IsNoetherian X]

open Order PrincipalParts in
/-- **Riemann–Roch, assuming Riemann's inequality.** Let `X` be an integral Noetherian
scheme, regular in codimension one, of Krull dimension at most one, whose structure morphism
to `Spec k` is locally of finite type and universally closed (e.g. `X` proper over `k`).
If the classical Riemann inequality `deg D ≤ ℓ(D) + C` holds uniformly over effective
divisors supported in codimension one, then for every Weil divisor `D`,
`χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

All sheaf-theoretic inputs are discharged: what remains of the classical Riemann–Roch
argument is the purely divisor-theoretic bound `hC`. -/
theorem riemann_roch_of_universallyClosed_of_degree_le [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (C : ℕ)
    (hC : ∀ D : AlgebraicCycle X ℤ, 0 ≤ D → D.support ⊆ {x | coheight x = 1} →
      D.degree k ≤ (Module.finrank k (LSubmodule X k D) : ℤ) + C)
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1}) :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k := by
  have hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q) :=
    fun q hq => finite_residueField_of_isClosed k (isClosed_singleton_of_coheight_eq_one hq)
  have hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)) := by
    haveI := finite_regularFunctions (X := X) k
    exact Module.Finite.equiv
      (M := ↥(regularFunctions X k))
      { toFun := fun f => ⟨f.1, f.2⟩
        invFun := fun f => ⟨f.1, f.2⟩
        left_inv := fun f => rfl
        right_inv := fun f => rfl
        map_add' := fun a b => rfl
        map_smul' := fun r a => rfl }
  exact riemann_roch_of_universallyClosed_of_finite_partsCoker k
    (finite_partsCoker_of_degree_le k hκ hL0 C hC) hD

end RiemannRoch

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

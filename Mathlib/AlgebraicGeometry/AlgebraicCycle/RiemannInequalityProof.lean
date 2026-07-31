/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.FundamentalInequality
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Riemann's inequality for separated curves

This file closes Chevalley's proof of Riemann's inequality `deg D ≤ ℓ(D) + C` for effective
divisors supported in codimension one, on an integral Noetherian scheme over a field whose
structure morphism is separated (plus regular in codimension one). Combined with the adelic
reduction of `RiemannInequality.lean`, this proves the weak Riemann–Roch theorem
unconditionally for proper curves.

The ingredients:

* `ord_eq_zero_of_isAlgebraic`: elements algebraic over the constants have order zero
  everywhere (immediate from `ord_aeval` applied to the minimal polynomial), so a
  uniformizer at any codimension-one point is transcendental;
* `degree_div_eq_zero`: principal divisors have degree zero — `div g` differs from
  `polePart g⁻¹ − polePart g` by nothing, and the degree identity
  `deg (f)_∞ = [k(X) : k(f)]` applied to `g` and `g⁻¹` (which generate the same subfield)
  gives equal degrees;
* `finrank_LSubmodule_add_div`: multiplication by `h` identifies `L(E + div h)` with `L(E)`;
* `finrank_LSubmodule_le_add_degree_sub`: the relative Riemann bound
  `ℓ(D') ≤ ℓ(D) + deg (D' − D)` for `D ≤ D'`, via the twisted class maps
  `x ↦ [t_q^{D q}·x]` into the bounded component spaces;
* `le_finrank_LSubmodule_nsmul_polePart`: the lower bound `ℓ(m·B + C₀) ≥ (m+1)·n` from the
  independent products `f^j·yᵢ`, where `y` is a `k(f)`-basis of `k(X)`;
* `exists_le_nsmul_polePart_add_div`: cofinality — every effective divisor is dominated by
  `m·B + div h` for a suitable rational function `h` built from minimal polynomials of
  residues of `f`;
* `exists_degree_le_finrank_add` and `riemann_roch_of_proper`: the assembly.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

/-! ### Order-theoretic preliminaries -/

section OrdAlgebraic

/-- Elements algebraic over the constants have nonnegative order everywhere: at a would-be
pole, the leading monomial of the minimal polynomial would dominate, contradicting
`aeval x (minpoly k x) = 0`. -/
lemma ord_nonneg_of_isAlgebraic {q : X} (hq : coheight q = 1) {x : ↑X.functionField}
    (hx0 : x ≠ 0) (halg : IsAlgebraic k x) : 0 ≤ X.ord x q := by
  by_contra hneg
  push_neg at hneg
  exact (ord_aeval k hq hx0 hneg (minpoly k x) (minpoly.ne_zero halg.isIntegral)).1
    (minpoly.aeval k x)

/-- Elements algebraic over the constants have order zero everywhere. -/
lemma ord_eq_zero_of_isAlgebraic {q : X} (hq : coheight q = 1) {x : ↑X.functionField}
    (hx0 : x ≠ 0) (halg : IsAlgebraic k x) : X.ord x q = 0 := by
  have h1 := ord_nonneg_of_isAlgebraic k hq hx0 halg
  have h2 := ord_nonneg_of_isAlgebraic k hq (inv_ne_zero hx0) (IsAlgebraic.inv_iff.mpr halg)
  rw [ord_inv hx0] at h2
  omega

/-- A polynomial in a function regular at `q` is regular at `q`. -/
lemma ord_aeval_nonneg {q : X} (hq : coheight q = 1) {f : ↑X.functionField}
    (hford : 0 ≤ X.ord f q) (P : Polynomial k)
    (haev : Polynomial.aeval f P ≠ 0) :
    0 ≤ X.ord (Polynomial.aeval f P) q := by
  obtain ⟨y, hy⟩ := (mem_range_algebraMap_iff_ord_nonneg hq f).mpr fun _ => hford
  have himg : Polynomial.aeval f P
      = algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (Polynomial.aeval y P) := by
    rw [← hy, Polynomial.aeval_algebraMap_apply]
  have hy0 : Polynomial.aeval y P ≠ 0 := fun h0 => haev (by rw [himg, h0, map_zero])
  rw [himg]
  exact ord_algebraMap_nonneg hq hy0

omit k in
/-- The order of a finite product of nonzero functions is the sum of the orders. -/
lemma ord_finset_prod {ι : Type*} {z : X} (hz : coheight z = 1) (s : Finset ι)
    (F : ι → ↑X.functionField) (hF : ∀ i ∈ s, F i ≠ 0) :
    X.ord (∏ i ∈ s, F i) z = ∑ i ∈ s, X.ord (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ord_one z
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul hz (hF a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

end OrdAlgebraic

/-! ### Support and positivity bookkeeping -/

section Supports

variable [IsNoetherian X]

omit k in
lemma support_add_subset_codim_one {A B : AlgebraicCycle X ℤ}
    (hA : A.support ⊆ {x | coheight x = 1}) (hB : B.support ⊆ {x | coheight x = 1}) :
    (A + B).support ⊆ {x | coheight x = 1} := fun q hq => by
  have h1 : A q + B q ≠ 0 := hq
  rcases eq_or_ne (A q) 0 with h2 | h2
  · refine hB (Function.mem_support.mpr fun h3 => h1 ?_)
    rw [h2, h3, add_zero]
  · exact hA (Function.mem_support.mpr h2)

omit k in
lemma support_nsmul_subset_codim_one {B : AlgebraicCycle X ℤ} (m : ℕ)
    (hB : B.support ⊆ {x | coheight x = 1}) :
    (m • B).support ⊆ {x | coheight x = 1} := fun q hq => by
  have h1 : (m • B) q ≠ 0 := hq
  rw [cycle_nsmul_apply] at h1
  exact hB (Function.mem_support.mpr fun h2 => h1 (by rw [h2, mul_zero]))

omit k in
lemma sum_polePart_nonneg {n : ℕ} (y : Fin n → ↑X.functionField) :
    0 ≤ ∑ i, polePart X (y i) := fun q => by
  show (0 : AlgebraicCycle X ℤ) q ≤ (∑ i, polePart X (y i)) q
  rw [cycle_finset_sum_apply, show (0 : AlgebraicCycle X ℤ) q = 0 from rfl]
  refine Finset.sum_nonneg fun i _ => ?_
  show (0 : ℤ) ≤ max 0 (- X.ord (y i) q)
  omega

omit k in
lemma sum_polePart_support {n : ℕ} (y : Fin n → ↑X.functionField) :
    (∑ i, polePart X (y i)).support ⊆ {x | coheight x = 1} := fun q hq => by
  have h1 : (∑ i, polePart X (y i)) q ≠ 0 := hq
  rw [cycle_finset_sum_apply] at h1
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact polePart_support (y i) (Function.mem_support.mpr hi)

end Supports

/-! ### Principal divisors have degree zero -/

section DegreeDiv

variable [IsNoetherian X]

open IntermediateField in
/-- **Principal divisors have degree zero.** For algebraic `g` the divisor vanishes
identically; for transcendental `g`, `div g + (g)_∞ = (g⁻¹)_∞` pointwise, and the degree
identity applied to `g` and `g⁻¹` (which generate the same intermediate field) gives equal
degrees for the two pole divisors. -/
lemma degree_div_eq_zero [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {g : ↑X.functionField} (hg0 : g ≠ 0) :
    (div g).degree k = 0 := by
  by_cases halg : IsAlgebraic k g
  · have hdiv0 : div g = (0 : AlgebraicCycle X ℤ) := by
      ext z
      show X.ord g z = (0 : AlgebraicCycle X ℤ) z
      rw [show ((0 : AlgebraicCycle X ℤ) z) = 0 from rfl]
      by_cases hz : coheight z = 1
      · exact ord_eq_zero_of_isAlgebraic k hz hg0 halg
      · exact Scheme.ord_eq_zero_of_coheight_neq_one hz g
    rw [hdiv0, degree_zero]
  · have hft : Transcendental k g := halg
    have hftinv : Transcendental k g⁻¹ := fun h => halg (IsAlgebraic.inv_iff.mp h)
    have hkey : div g + polePart X g = polePart X g⁻¹ := by
      ext z
      show X.ord g z + max 0 (- X.ord g z) = max 0 (- X.ord g⁻¹ z)
      rw [ord_inv hg0]
      omega
    have hdeg := AlgebraicCycle.degree_sum k (div g) (polePart X g)
    rw [hkey] at hdeg
    have h1 := degree_polePart_eq_finrank_of_isSeparated k hκ hL0 hft
    have h2 := degree_polePart_eq_finrank_of_isSeparated k hκ hL0 hftinv
    have hadj : adjoin k {g⁻¹} = adjoin k {g} := by
      apply le_antisymm
      · rw [adjoin_le_iff]
        exact Set.singleton_subset_iff.mpr
          (IntermediateField.inv_mem _ (mem_adjoin_simple_self k g))
      · rw [adjoin_le_iff]
        refine Set.singleton_subset_iff.mpr ?_
        have h3 := IntermediateField.inv_mem _ (mem_adjoin_simple_self k g⁻¹)
        rwa [inv_inv] at h3
    rw [hadj] at h2
    rw [h2, h1] at hdeg
    omega

end DegreeDiv

/-! ### Twisting by a principal divisor -/

section MulInvariance

open PrincipalParts

/-- **Twisting invariance.** Multiplication by `h` is a `k`-linear isomorphism
`L(E + div h) ≃ L(E)`, so twisting by a principal divisor does not change `ℓ`. -/
lemma finrank_LSubmodule_add_div {E : AlgebraicCycle X ℤ}
    (hEc : E.support ⊆ {x | coheight x = 1}) {h : ↑X.functionField} (hh0 : h ≠ 0) :
    Module.finrank k (LSubmodule X k (E + div h))
      = Module.finrank k (LSubmodule X k E) := by
  have hEdc : (E + div h).support ⊆ {x | coheight x = 1} := fun q hq => by
    have h1 : E q + div h q ≠ 0 := hq
    rcases eq_or_ne (E q) 0 with h2 | h2
    · have h4 : div h q ≠ 0 := fun h3 => h1 (by rw [h2, h3, add_zero])
      exact div_support (Function.mem_support.mpr h4)
    · exact hEc (Function.mem_support.mpr h2)
  have key : ∀ x : ↑X.functionField, x ∈ LSubmodule X k (E + div h) →
      x * h ∈ LSubmodule X k E := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [zero_mul]
      exact (LSubmodule X k E).zero_mem
    refine mem_carrier_of_forall_ordSubmodule (D := E) (U := ⊤) hEc
      ⟨⟨genericPoint X, trivial⟩⟩ (fun z hz _ => ?_)
    intro hne
    have h1 := mem_ordSubmodule_of_mem_carrier (D := E + div h) hx hz trivial hx0
    have h2 : (E + div h) z = E z + X.ord h z := rfl
    rw [h2] at h1
    rw [ord_mul hz hx0 hh0]
    omega
  have key' : ∀ x : ↑X.functionField, x ∈ LSubmodule X k E →
      x * h⁻¹ ∈ LSubmodule X k (E + div h) := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [zero_mul]
      exact (LSubmodule X k (E + div h)).zero_mem
    refine mem_carrier_of_forall_ordSubmodule (D := E + div h) (U := ⊤) hEdc
      ⟨⟨genericPoint X, trivial⟩⟩ (fun z hz _ => ?_)
    intro hne
    have h1 := mem_ordSubmodule_of_mem_carrier (D := E) hx hz trivial hx0
    have h2 : (E + div h) z = E z + X.ord h z := rfl
    rw [h2, ord_mul hz hx0 (inv_ne_zero hh0), ord_inv hh0]
    omega
  have e : ↥(LSubmodule X k (E + div h)) ≃ₗ[k] ↥(LSubmodule X k E) :=
    { toFun := fun x => ⟨x.1 * h, key x.1 x.2⟩
      invFun := fun y => ⟨y.1 * h⁻¹, key' y.1 y.2⟩
      left_inv := fun x => Subtype.ext (by
        show x.1 * h * h⁻¹ = x.1
        rw [mul_inv_cancel_right₀ hh0])
      right_inv := fun y => Subtype.ext (by
        show y.1 * h⁻¹ * h = y.1
        rw [inv_mul_cancel_right₀ hh0])
      map_add' := fun a b => Subtype.ext (add_mul a.1 b.1 h)
      map_smul' := fun r a => Subtype.ext (smul_mul_assoc r a.1 h) }
  exact LinearEquiv.finrank_eq e

end MulInvariance

/-! ### The relative Riemann bound -/

section RelativeBound

variable [IsNoetherian X]

open PrincipalParts in
/-- **The relative Riemann bound.** For divisors `D ≤ D'` supported in codimension one,
`ℓ(D') ≤ ℓ(D) + deg (D' − D)`: the twisted class maps `x ↦ [t_q^{D q}·x]` at the points of
`supp (D' − D)` have kernel `L(D)` and land in the bounded component spaces. -/
lemma finrank_LSubmodule_le_add_degree_sub
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    {D D' : AlgebraicCycle X ℤ} (hDD' : D ≤ D')
    (hD : D.support ⊆ {x | coheight x = 1}) (hD' : D'.support ⊆ {x | coheight x = 1})
    [Module.Finite k (LSubmodule X k D')] :
    (Module.finrank k (LSubmodule X k D') : ℤ)
      ≤ (Module.finrank k (LSubmodule X k D) : ℤ) + (D' - D).degree k := by
  classical
  have hEapp : ∀ q : X, (D' - D) q = D' q - D q := fun q => rfl
  have hE0 : ∀ q : X, 0 ≤ (D' - D) q := fun q => by
    have h1 : D q ≤ D' q := hDD' q
    rw [hEapp]
    omega
  have hEc : (D' - D).support ⊆ {x | coheight x = 1} := by
    intro q hq
    have h1 : (D' - D) q ≠ 0 := hq
    rw [hEapp] at h1
    rcases eq_or_ne (D q) 0 with h2 | h2
    · exact hD' (Function.mem_support.mpr fun h3 => h1 (by omega))
    · exact hD (Function.mem_support.mpr h2)
  set T : Finset X := (support_finite (D' - D)).toFinset with hT
  have hmemT : ∀ q : X, q ∈ T ↔ q ∈ (D' - D).support := fun q =>
    Set.Finite.mem_toFinset _
  have hcod : ∀ q ∈ T, coheight q = 1 := fun q hq => hEc ((hmemT q).mp hq)
  haveI : ∀ q : ↥T, Module.Finite k ↑(X.residueField q.1) :=
    fun q => hκ q.1 (hcod q.1 q.2)
  haveI : ∀ q : ↥T, Module.Finite k
      (componentBounded X k (hcod q.1 q.2) ((D' - D) q.1)) :=
    fun q => (finite_finrank_componentBounded k (hcod q.1 q.2) ((D' - D) q.1)).1
  -- a uniformizer at each point of the support
  have huni : ∀ q : ↥T, ∃ t : ↑X.functionField, t ≠ 0 ∧ X.ord t q.1 = 1 :=
    fun q => exists_ord_eq_one (hcod q.1 q.2)
  choose t ht0 ht1 using huni
  -- the twisted class maps land in the bounded components
  have hmem : ∀ (q : ↥T) (x : ↥(LSubmodule X k D')),
      componentMkₗ X k (hcod q.1 q.2) (t q ^ (D q.1) * x.1)
        ∈ componentBounded X k (hcod q.1 q.2) ((D' - D) q.1) := by
    intro q x
    refine Submodule.mem_map_of_mem ?_
    intro hne
    have hx0 : x.1 ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    have hx' := mem_ordSubmodule_of_mem_carrier (D := D') x.2 (hcod q.1 q.2) trivial hx0
    rw [ord_mul (hcod q.1 q.2) (zpow_ne_zero _ (ht0 q)) hx0, ord_zpow (ht0 q), ht1,
      hEapp]
    omega
  set Φ : ↥(LSubmodule X k D') →ₗ[k]
      (∀ q : ↥T, ↥(componentBounded X k (hcod q.1 q.2) ((D' - D) q.1))) :=
    LinearMap.pi fun q => LinearMap.codRestrict _
      (((componentMkₗ X k (hcod q.1 q.2)).comp
        (LinearMap.mulLeft k (t q ^ (D q.1)))).comp (LSubmodule X k D').subtype)
      (fun x => hmem q x) with hΦ
  -- the kernel is exactly `L(D)`
  have hker : LinearMap.ker Φ
      = Submodule.comap (LSubmodule X k D').subtype (LSubmodule X k D) := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap]
    constructor
    · intro h0
      show x.1 ∈ LSubmodule X k D
      refine mem_carrier_of_forall_ordSubmodule (D := D) (U := ⊤) hD
        ⟨⟨genericPoint X, trivial⟩⟩ (fun z hz _ => ?_)
      intro hne
      by_cases hzT : z ∈ T
      · have h1 : Φ x ⟨z, hzT⟩ = 0 := by rw [h0]; rfl
        have h2 : componentMkₗ X k (hcod z hzT) (t ⟨z, hzT⟩ ^ (D z) * x.1) = 0 :=
          congrArg Subtype.val h1
        have h3 : Component.mk (0 : AlgebraicCycle X ℤ) (hcod z hzT)
            (t ⟨z, hzT⟩ ^ (D z) * x.1) = 0 := h2
        have h4 := (Component.mk_eq_zero_iff 0 (hcod z hzT)).mp h3
        have hprod0 : t ⟨z, hzT⟩ ^ (D z) * x.1 ≠ 0 :=
          mul_ne_zero (zpow_ne_zero _ (ht0 ⟨z, hzT⟩)) hne
        have h5 := h4 hprod0
        have h6 : -(0 : AlgebraicCycle X ℤ) z = 0 := by
          rw [show ((0 : AlgebraicCycle X ℤ) z) = 0 from rfl]
          ring
        rw [h6] at h5
        rw [ord_mul hz (zpow_ne_zero _ (ht0 ⟨z, hzT⟩)) hne, ord_zpow (ht0 ⟨z, hzT⟩),
          ht1] at h5
        omega
      · -- outside the support of the difference, `D` and `D'` agree
        have hEz : (D' - D) z = 0 := by
          by_contra h1
          exact hzT ((hmemT z).mpr (Function.mem_support.mpr h1))
        rw [hEapp] at hEz
        have h1 := mem_ordSubmodule_of_mem_carrier (D := D') x.2 hz trivial hne
        omega
    · intro hx0
      have hcoord : ∀ q : ↥T, Φ x q = 0 := by
        intro q
        apply Subtype.ext
        show componentMkₗ X k (hcod q.1 q.2) (t q ^ (D q.1) * x.1)
          = (0 : Component (0 : AlgebraicCycle X ℤ) (hcod q.1 q.2))
        have h3 : Component.mk (0 : AlgebraicCycle X ℤ) (hcod q.1 q.2)
            (t q ^ (D q.1) * x.1) = componentMkₗ X k (hcod q.1 q.2)
            (t q ^ (D q.1) * x.1) := rfl
        rw [← h3, Component.mk_eq_zero_iff]
        intro hne
        have hx1 : x.1 ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
        have hx0' : x.1 ∈ LSubmodule X k D := hx0
        have h1 := mem_ordSubmodule_of_mem_carrier (D := D) hx0' (hcod q.1 q.2) trivial hx1
        have h6 : -(0 : AlgebraicCycle X ℤ) q.1 = 0 := by
          rw [show ((0 : AlgebraicCycle X ℤ) q.1) = 0 from rfl]
          ring
        rw [h6, ord_mul (hcod q.1 q.2) (zpow_ne_zero _ (ht0 q)) hx1, ord_zpow (ht0 q),
          ht1]
        omega
      funext q
      exact hcoord q
  -- rank counting
  have hcount := LinearMap.finrank_range_add_finrank_ker Φ
  have hkerrank : Module.finrank k ↥(LinearMap.ker Φ)
      = Module.finrank k ↥(LSubmodule X k D) := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (LSubmodule_mono k hDD'))
  have hrange : Module.finrank k ↥(LinearMap.range Φ)
      ≤ ∑ q : ↥T, ((D' - D) q.1).toNat * Module.finrank k ↑(X.residueField q.1) := by
    calc Module.finrank k ↥(LinearMap.range Φ)
        ≤ Module.finrank k
          (∀ q : ↥T, ↥(componentBounded X k (hcod q.1 q.2) ((D' - D) q.1))) :=
          Submodule.finrank_le _
      _ = ∑ q : ↥T, Module.finrank k
          ↥(componentBounded X k (hcod q.1 q.2) ((D' - D) q.1)) :=
          Module.finrank_pi_fintype k
      _ ≤ ∑ q : ↥T, ((D' - D) q.1).toNat * Module.finrank k ↑(X.residueField q.1) :=
          Finset.sum_le_sum fun q _ =>
            (finite_finrank_componentBounded k (hcod q.1 q.2) ((D' - D) q.1)).2
  -- identify the sum with the degree
  have hdeg : (D' - D).degree k
      = ∑ q : ↥T, (D' - D) q.1 * (Module.finrank k ↑(X.residueField q.1) : ℤ) := by
    rw [AlgebraicCycle.degree,
      finsum_eq_finsetSum_of_support_subset _ (s := T)
        (by
          intro q hq
          have hq' : (D' - D) q ≠ 0 := left_ne_zero_of_mul hq
          exact (hmemT q).mpr hq')]
    exact (Finset.sum_coe_sort T
      (fun q => (D' - D) q * (Module.finrank k ↑(X.residueField q) : ℤ))).symm
  have hcast : ((∑ q : ↥T, ((D' - D) q.1).toNat *
      Module.finrank k ↑(X.residueField q.1) : ℕ) : ℤ) = (D' - D).degree k := by
    rw [hdeg]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Int.toNat_of_nonneg (hE0 q.1)]
  have h1 : (Module.finrank k ↥(LinearMap.range Φ) : ℤ) ≤ (D' - D).degree k := by
    rw [← hcast]
    exact_mod_cast hrange
  omega

end RelativeBound

/-! ### The lower bound along the tower -/

section LowerBound

variable [IsNoetherian X]

open IntermediateField in
/-- **The tower lower bound.** For a `k(f)`-linearly-independent family `y` of size `n`,
the products `f^j·yᵢ` (`0 ≤ j ≤ m`) are `k`-independent sections of
`𝒪(m·(f)_∞ + Σ (yᵢ)_∞)`, so `ℓ(m·B + C₀) ≥ (m+1)·n`. This is the same computation as in
`card_le_degree_polePart`, used here for the opposite estimate. -/
lemma le_finrank_LSubmodule_nsmul_polePart
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {f : ↑X.functionField} (hft : Transcendental k f)
    {n : ℕ} {y : Fin n → ↑X.functionField}
    (hy : LinearIndependent ↥(adjoin k {f}) y) (m : ℕ) :
    (m + 1) * n
      ≤ Module.finrank k (LSubmodule X k (m • polePart X f + ∑ i, polePart X (y i))) := by
  classical
  have hf0 : f ≠ 0 := fun h => hft (h ▸ isAlgebraic_zero)
  set B := polePart X f with hB
  set C₀ : AlgebraicCycle X ℤ := ∑ i, polePart X (y i) with hC₀
  have hC₀pos : 0 ≤ C₀ := sum_polePart_nonneg y
  have hC₀cod : C₀.support ⊆ {x | coheight x = 1} := sum_polePart_support y
  have hEle : ∀ i, polePart X (y i) ≤ C₀ := fun i => by
    intro q
    show polePart X (y i) q ≤ (∑ j, polePart X (y j)) q
    rw [cycle_finset_sum_apply]
    exact Finset.single_le_sum (f := fun j => polePart X (y j) q)
      (fun j _ => by show (0 : ℤ) ≤ max 0 (- X.ord (y j) q); omega) (Finset.mem_univ i)
  have hyC : ∀ i, y i ∈ Sheaf.carrier C₀ ⊤ := fun i =>
    carrier_mono (hEle i) (mem_carrier_polePart (y i))
  have hDpos : 0 ≤ m • B + C₀ :=
    add_nonneg (nsmul_nonneg (polePart_nonneg f) m) hC₀pos
  have hDcod : (m • B + C₀).support ⊆ {x | coheight x = 1} :=
    support_add_subset_codim_one (support_nsmul_subset_codim_one m (polePart_support f))
      hC₀cod
  haveI := finite_LSubmodule k hκ hL0 _ hDpos hDcod
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

end LowerBound

/-! ### Cofinality: dominating a divisor by `m·B + div h` -/

section Cofinality

variable [IsNoetherian X]

open Polynomial in
/-- At a point where `f` is regular, some nonzero polynomial in `f` vanishes: the residue of
`f` satisfies a `k`-linear dependence among its powers (the residue field being
finite-dimensional), and the corresponding polynomial in `f` lies in the maximal ideal. -/
lemma exists_aeval_ord_pos {q : X} (hq : coheight q = 1)
    [Module.Finite k ↑(X.residueField q)]
    {f : ↑X.functionField} (hft : Transcendental k f) (hford : 0 ≤ X.ord f q) :
    ∃ P : Polynomial k, P ≠ 0 ∧ 1 ≤ X.ord (Polynomial.aeval f P) q := by
  classical
  set d : ℕ := Module.finrank k ↑(X.residueField q) with hd
  obtain ⟨y, hy⟩ := (mem_range_algebraMap_iff_ord_nonneg hq f).mpr fun _ => hford
  set ρ : ↑(X.residueField q) := (X.residue q).hom y with hρ
  have hdep : ¬ LinearIndependent k (fun i : Fin (d + 1) => ρ ^ (i : ℕ)) := by
    intro hind
    have h1 := hind.fintype_card_le_finrank
    rw [Fintype.card_fin] at h1
    omega
  obtain ⟨c, hcsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  set P : Polynomial k := ∑ i : Fin (d + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
    with hP
  have hcoeff : P.coeff (i₀ : ℕ) = c i₀ := by
    rw [hP, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i₀ (fun b _ hb => ?_)
      (fun habs => absurd (Finset.mem_univ i₀) habs)]
    · rw [Polynomial.coeff_C_mul_X_pow]
      exact if_pos rfl
    · rw [Polynomial.coeff_C_mul_X_pow]
      exact if_neg fun hh => hb (Fin.val_injective hh).symm
  have hP0 : P ≠ 0 := fun h0 => hi₀ (by rw [← hcoeff, h0, Polynomial.coeff_zero])
  set s : ↑(X.presheaf.stalk q) :=
    ∑ i : Fin (d + 1), algebraMap k ↑(X.presheaf.stalk q) (c i) * y ^ (i : ℕ) with hs
  have hres : (X.residue q).hom s = 0 := by
    rw [hs, map_sum]
    have hterm : ∀ i ∈ Finset.univ, (X.residue q).hom
        (algebraMap k ↑(X.presheaf.stalk q) (c i) * y ^ (i : ℕ)) = c i • ρ ^ (i : ℕ) :=
      fun i _ => by rw [residue_algebraMap_mul, map_pow]
    rw [Finset.sum_congr rfl hterm]
    exact hcsum
  have himg : algebraMap ↑(X.presheaf.stalk q) ↑X.functionField s
      = Polynomial.aeval f P := by
    rw [hs, map_sum, hP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hy, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
      ← IsScalarTower.algebraMap_apply]
  have haev0 : Polynomial.aeval f P ≠ 0 := fun h0 => hft ⟨P, hP0, h0⟩
  have hs0 : s ≠ 0 := fun h0 => haev0 (by rw [← himg, h0, map_zero])
  have hmax : s ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk q) := by
    have hbr : IsLocalRing.residue ↑(X.presheaf.stalk q) s = 0 := hres
    exact (IsLocalRing.residue_eq_zero_iff s).mp hbr
  refine ⟨P, hP0, ?_⟩
  rw [← himg]
  exact (mem_maximalIdeal_iff_one_le_ord hq hs0).mp hmax

open Polynomial in
/-- **Cofinality.** Every effective divisor supported in codimension one is dominated by
`m·(f)_∞ + div h` for suitable `m` and `h`: at each point of `supp D` away from the poles
of `f`, a polynomial in `f` vanishes to high order while acquiring poles only along
`(f)_∞`. -/
lemma exists_le_nsmul_polePart_add_div [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {f : ↑X.functionField} (hf0 : f ≠ 0) (hft : Transcendental k f)
    {D : AlgebraicCycle X ℤ} (hD0 : 0 ≤ D) (hDc : D.support ⊆ {x | coheight x = 1}) :
    ∃ (h : ↑X.functionField) (m : ℕ), h ≠ 0 ∧ (div h).degree k = 0 ∧
      D ≤ m • polePart X f + div h := by
  classical
  set B := polePart X f with hB
  -- the support points of `D` where `f` is regular
  set T : Finset X := (support_finite D).toFinset.filter (fun q => 0 ≤ X.ord f q) with hT
  have hTc : ∀ q ∈ T, coheight q = 1 := fun q hq =>
    hDc ((support_finite D).mem_toFinset.mp (Finset.mem_filter.mp hq).1)
  have hTf : ∀ q ∈ T, 0 ≤ X.ord f q := fun q hq => (Finset.mem_filter.mp hq).2
  -- a vanishing polynomial at each such point
  have hex : ∀ q : ↥T, ∃ P : Polynomial k, P ≠ 0 ∧
      1 ≤ X.ord (Polynomial.aeval f P) q.1 := fun q => by
    haveI := hκ q.1 (hTc q.1 q.2)
    exact exists_aeval_ord_pos k (hTc q.1 q.2) hft (hTf q.1 q.2)
  choose P hP0 hPord using hex
  have hg0 : ∀ q : ↥T, Polynomial.aeval f (P q) ≠ 0 :=
    fun q h0 => hft ⟨P q, hP0 q, h0⟩
  set e : ↥T → ℕ := fun q => (D q.1).toNat with he
  set h : ↑X.functionField := ∏ q : ↥T, Polynomial.aeval f (P q) ^ e q with hh
  have hh0 : h ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ => pow_ne_zero _ (hg0 q)
  -- the principal divisor of `h` has degree zero
  have hdiv1 : div (1 : ↑X.functionField) = (0 : AlgebraicCycle X ℤ) := by
    ext z
    show X.ord (1 : ↑X.functionField) z = (0 : AlgebraicCycle X ℤ) z
    rw [ord_one, show ((0 : AlgebraicCycle X ℤ) z) = 0 from rfl]
  have hpowP : ∀ (x : ↑X.functionField), x ≠ 0 → (div x).degree k = 0 →
      ∀ e' : ℕ, x ^ e' ≠ 0 ∧ (div (x ^ e')).degree k = 0 := by
    intro x hx hdeg e'
    induction e' with
    | zero =>
      refine ⟨by rw [pow_zero]; exact one_ne_zero, ?_⟩
      rw [pow_zero, hdiv1, degree_zero]
    | succ i ih =>
      refine ⟨pow_ne_zero _ hx, ?_⟩
      rw [pow_succ, div_mul _ ih.1 _ hx, degree_sum, ih.2, hdeg, add_zero]
  have hprod : h ≠ 0 ∧ (div h).degree k = 0 := by
    rw [hh]
    refine Finset.prod_induction _ (fun x => x ≠ 0 ∧ (div x).degree k = 0)
      (fun a b ha hb => ⟨mul_ne_zero ha.1 hb.1, ?_⟩)
      ⟨one_ne_zero, by rw [hdiv1, degree_zero]⟩ (fun q _ => ?_)
    · rw [div_mul a ha.1 b hb.1, degree_sum, ha.2, hb.2, add_zero]
    · exact hpowP _ (hg0 q) (degree_div_eq_zero k hκ hL0 (hg0 q)) (e q)
  -- the total pole multiplicity of `h` along `B`, and the height of `D` along `B`
  set M : ℕ := ∑ q : ↥T, e q * (P q).natDegree with hM
  set S : ℕ := Finset.sup (support_finite B).toFinset (fun x => (D x).toNat) with hS
  refine ⟨h, M + S, hh0, hprod.2, ?_⟩
  intro z
  show D z ≤ ((M + S) • B + div h) z
  have happ : ((M + S) • B + div h) z = ((M + S : ℕ) : ℤ) * B z + X.ord h z := by
    have h1 : ((M + S) • B + div h) z = ((M + S) • B) z + div h z := rfl
    rw [h1, cycle_nsmul_apply, div_eq_ord]
  rw [happ]
  by_cases hz : coheight z = 1
  · have hordh : X.ord h z = ∑ q : ↥T, (e q : ℤ) * X.ord (Polynomial.aeval f (P q)) z := by
      rw [hh, ord_finset_prod hz _ _ (fun q _ => pow_ne_zero _ (hg0 q))]
      exact Finset.sum_congr rfl fun q _ => ord_pow (hg0 q) (e q) z
    have hBz : 0 ≤ B z := by
      show (0 : ℤ) ≤ max 0 (- X.ord f z)
      omega
    by_cases hfz : 0 ≤ X.ord f z
    · -- `f` regular at `z`: no help needed from `B`
      have hBz0 : B z = 0 := by
        show max 0 (- X.ord f z) = 0
        omega
      have hterm : ∀ q : ↥T, 0 ≤ (e q : ℤ) * X.ord (Polynomial.aeval f (P q)) z :=
        fun q => mul_nonneg (by positivity)
          (ord_aeval_nonneg k hz hfz (P q) (hg0 q))
      by_cases hzT : z ∈ T
      · have hDz0 : 0 ≤ D z := by
          have h1 := hD0 z
          rwa [show ((0 : AlgebraicCycle X ℤ) z) = 0 from rfl] at h1
        have h2 : (e ⟨z, hzT⟩ : ℤ) = D z := Int.toNat_of_nonneg hDz0
        have hone : (D z : ℤ) ≤ (e ⟨z, hzT⟩ : ℤ)
            * X.ord (Polynomial.aeval f (P ⟨z, hzT⟩)) z := by
          calc (D z : ℤ) = (e ⟨z, hzT⟩ : ℤ) := h2.symm
            _ = (e ⟨z, hzT⟩ : ℤ) * 1 := (mul_one _).symm
            _ ≤ (e ⟨z, hzT⟩ : ℤ) * X.ord (Polynomial.aeval f (P ⟨z, hzT⟩)) z :=
                mul_le_mul_of_nonneg_left (hPord ⟨z, hzT⟩) (by positivity)
        have hsum : (D z : ℤ)
            ≤ ∑ q : ↥T, (e q : ℤ) * X.ord (Polynomial.aeval f (P q)) z :=
          le_trans hone (Finset.single_le_sum (fun q _ => hterm q)
            (Finset.mem_univ (⟨z, hzT⟩ : ↥T)))
        rw [hordh, hBz0, mul_zero, zero_add]
        exact hsum
      · have hDz : D z ≤ 0 := by
          by_contra hlt
          push_neg at hlt
          refine hzT ?_
          rw [hT]
          exact Finset.mem_filter.mpr
            ⟨(support_finite D).mem_toFinset.mpr
              (Function.mem_support.mpr (by omega)), hfz⟩
        have hsum0 : 0 ≤ ∑ q : ↥T, (e q : ℤ) * X.ord (Polynomial.aeval f (P q)) z :=
          Finset.sum_nonneg fun q _ => hterm q
        rw [hordh, hBz0, mul_zero, zero_add]
        omega
    · -- pole of `f` at `z`: the pole of `h` is at most `M · B z`
      push_neg at hfz
      have hBz' : B z = - X.ord f z := by
        show max 0 (- X.ord f z) = - X.ord f z
        omega
      have hgz : ∀ q : ↥T, X.ord (Polynomial.aeval f (P q)) z
          = ((P q).natDegree : ℤ) * X.ord f z :=
        fun q => (ord_aeval k hz hf0 hfz (P q) (hP0 q)).2
      have hordh' : X.ord h z = - (M : ℤ) * B z := by
        rw [hordh]
        have h1 : ∀ q ∈ (Finset.univ : Finset ↥T),
            (e q : ℤ) * X.ord (Polynomial.aeval f (P q)) z
            = ((e q * (P q).natDegree : ℕ) : ℤ) * X.ord f z := fun q _ => by
          rw [hgz q]
          push_cast
          ring
        rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
        have h2 : (∑ q : ↥T, ((e q * (P q).natDegree : ℕ) : ℤ)) = (M : ℤ) := by
          rw [hM]
          push_cast
          rfl
        rw [h2, hBz']
        ring
      have hzB : z ∈ (support_finite B).toFinset := by
        refine (support_finite B).mem_toFinset.mpr (Function.mem_support.mpr ?_)
        rw [hBz']
        omega
      have hDS : (D z : ℤ) ≤ (S : ℤ) := by
        have h1 : (D z).toNat ≤ S := by
          rw [hS]
          exact Finset.le_sup (f := fun x => (D x).toNat) hzB
        omega
      have hBz1 : 1 ≤ B z := by
        rw [hBz']
        omega
      rw [hordh']
      have h3 : ((M + S : ℕ) : ℤ) * B z + (-(M : ℤ) * B z) = (S : ℤ) * B z := by
        push_cast
        ring
      rw [h3]
      calc (D z : ℤ) ≤ (S : ℤ) := hDS
        _ = (S : ℤ) * 1 := (mul_one _).symm
        _ ≤ (S : ℤ) * B z := mul_le_mul_of_nonneg_left hBz1 (by positivity)
  · -- junk points: everything vanishes
    have hDz : D z = 0 := by
      by_contra h0
      exact hz (hDc (Function.mem_support.mpr h0))
    have hBz : B z = 0 := by
      show max 0 (- X.ord f z) = 0
      rw [Scheme.ord_eq_zero_of_coheight_neq_one hz]
      omega
    have hhz : X.ord h z = 0 := Scheme.ord_eq_zero_of_coheight_neq_one hz h
    rw [hDz, hBz, hhz]
    simp

end Cofinality

/-! ### The assembly: Riemann's inequality and Riemann–Roch for proper curves -/

section Assembly

variable [IsNoetherian X]

open IntermediateField in
/-- **Riemann's inequality.** On an integral Noetherian scheme over `k`, regular in
codimension one and with separated structure morphism, there is a constant `C` with
`deg D ≤ ℓ(D) + C` for every effective divisor supported in codimension one. -/
theorem exists_degree_le_finrank_add [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ))) :
    ∃ C : ℕ, ∀ D : AlgebraicCycle X ℤ, 0 ≤ D → D.support ⊆ {x | coheight x = 1} →
      D.degree k ≤ (Module.finrank k (LSubmodule X k D) : ℤ) + C := by
  classical
  by_cases hpt : ∃ q : X, coheight q = 1
  · obtain ⟨q₀, hq₀⟩ := hpt
    obtain ⟨u, hu0, hu1⟩ := exists_ord_eq_one hq₀
    have hft : Transcendental k u := by
      intro halg
      have h1 := ord_eq_zero_of_isAlgebraic k hq₀ hu0 halg
      omega
    haveI hfin := finite_adjoin_of_transcendental k hκ hL0 hft
    set w := Module.finBasis ↥(adjoin k {u}) ↑X.functionField with hw
    have hdegB : (polePart X u).degree k
        = (Module.finrank ↥(adjoin k {u}) ↑X.functionField : ℤ) :=
      degree_polePart_eq_finrank_of_isSeparated k hκ hL0 hft
    refine ⟨((∑ i, polePart X (w i)).degree k).toNat, ?_⟩
    intro D hD0 hDc
    obtain ⟨h, m, hh0, hdivdeg, hDle⟩ :=
      exists_le_nsmul_polePart_add_div k hκ hL0 hu0 hft hD0 hDc
    -- the comparison divisor
    have hGc : ((m • polePart X u + ∑ i, polePart X (w i)) + div h).support
        ⊆ {x | coheight x = 1} :=
      support_add_subset_codim_one
        (support_add_subset_codim_one
          (support_nsmul_subset_codim_one m (polePart_support u))
          (sum_polePart_support (fun i => w i)))
        div_support
    have hDleG : D ≤ (m • polePart X u + ∑ i, polePart X (w i)) + div h := by
      intro z
      show D z ≤ ((m • polePart X u + ∑ i, polePart X (w i)) + div h) z
      have h1 : D z ≤ (m • polePart X u + div h) z := hDle z
      have h2 : (m • polePart X u + div h) z
          = (m : ℤ) * polePart X u z + X.ord h z := by
        have h3 : (m • polePart X u + div h) z = (m • polePart X u) z + div h z := rfl
        rw [h3, cycle_nsmul_apply, div_eq_ord]
      rw [h2] at h1
      have h4 : ((m • polePart X u + ∑ i, polePart X (w i)) + div h) z
          = (m : ℤ) * polePart X u z + (∑ i, polePart X (w i)) z + X.ord h z := by
        have h5 : ((m • polePart X u + ∑ i, polePart X (w i)) + div h) z
            = (m • polePart X u) z + (∑ i, polePart X (w i)) z + div h z := rfl
        rw [h5, cycle_nsmul_apply, div_eq_ord]
      rw [h4]
      have h6 : 0 ≤ (∑ i, polePart X (w i)) z := by
        have h7 : (0 : AlgebraicCycle X ℤ) z ≤ (∑ i, polePart X (w i)) z :=
          sum_polePart_nonneg (X := X) (fun i => w i) z
        rwa [show ((0 : AlgebraicCycle X ℤ) z) = 0 from rfl] at h7
      linarith [h1, h6]
    have hGpos : 0 ≤ (m • polePart X u + ∑ i, polePart X (w i)) + div h :=
      le_trans hD0 hDleG
    haveI hfinG := finite_LSubmodule k hκ hL0 _ hGpos hGc
    -- monotonicity, invariance, and the tower lower bound
    have hmono := finrank_LSubmodule_le_add_degree_sub k hκ hDleG hDc hGc
    have hinv : Module.finrank k
          (LSubmodule X k ((m • polePart X u + ∑ i, polePart X (w i)) + div h))
        = Module.finrank k (LSubmodule X k (m • polePart X u + ∑ i, polePart X (w i))) :=
      finrank_LSubmodule_add_div k
        (support_add_subset_codim_one
          (support_nsmul_subset_codim_one m (polePart_support u))
          (sum_polePart_support (fun i => w i))) hh0
    have hlow := le_finrank_LSubmodule_nsmul_polePart k hκ hL0 hft w.linearIndependent m
    -- degree computations
    have hup1 : (((m • polePart X u + ∑ i, polePart X (w i)) + div h)).degree k
        = (m • polePart X u + ∑ i, polePart X (w i)).degree k := by
      rw [degree_sum, hdivdeg, add_zero]
    have hup2 : (m • polePart X u + ∑ i, polePart X (w i)).degree k
        = (m : ℤ) * (Module.finrank ↥(adjoin k {u}) ↑X.functionField : ℤ)
          + (∑ i, polePart X (w i)).degree k := by
      rw [degree_sum, degree_nsmul, hdegB]
    have hsub : (((m • polePart X u + ∑ i, polePart X (w i)) + div h) - D).degree k
        = (((m • polePart X u + ∑ i, polePart X (w i)) + div h)).degree k
          - D.degree k := degree_minus k _ _
    have hC0 : 0 ≤ (∑ i, polePart X (w i)).degree k :=
      degree_nonneg k (sum_polePart_nonneg (fun i => w i))
    have hN0 : (0 : ℤ) ≤ (Module.finrank ↥(adjoin k {u}) ↑X.functionField : ℤ) :=
      Int.natCast_nonneg _
    have hlow' : ((m : ℤ) + 1) * (Module.finrank ↥(adjoin k {u}) ↑X.functionField : ℤ)
        ≤ (Module.finrank k
          (LSubmodule X k (m • polePart X u + ∑ i, polePart X (w i))) : ℤ) := by
      calc ((m : ℤ) + 1) * (Module.finrank ↥(adjoin k {u}) ↑X.functionField : ℤ)
          = (((m + 1) * Module.finrank ↥(adjoin k {u}) ↑X.functionField : ℕ) : ℤ) := by
            push_cast
            ring
        _ ≤ _ := by exact_mod_cast hlow
    have htoNat : (∑ i, polePart X (w i)).degree k
        ≤ (((∑ i, polePart X (w i)).degree k).toNat : ℤ) := Int.self_le_toNat _
    rw [hsub, hup1] at hmono
    rw [hup2] at hmono hup1
    have hinv' : (Module.finrank k
          (LSubmodule X k ((m • polePart X u + ∑ i, polePart X (w i)) + div h)) : ℤ)
        = (Module.finrank k
          (LSubmodule X k (m • polePart X u + ∑ i, polePart X (w i))) : ℤ) := by
      exact_mod_cast hinv
    linarith [hmono, hlow', hinv', htoNat, hC0, hN0]
  · -- no codimension-one points: every admissible divisor is zero
    refine ⟨0, fun D hD0 hDc => ?_⟩
    have hD0' : D = 0 := by
      ext q
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      by_contra hne
      exact hpt ⟨q, hDc (Function.mem_support.mpr hne)⟩
    rw [hD0', degree_zero]
    positivity

/-- **The weak Riemann–Roch theorem for proper curves.** On an integral Noetherian scheme
of Krull dimension at most one over a field, with structure morphism separated, universally
closed and locally of finite type (e.g. proper), regular in codimension one:
`χ(𝒪(D)) = deg D + χ(𝒪)` for every divisor supported in codimension one. -/
theorem riemann_roch_of_proper [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
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
  obtain ⟨C, hC⟩ := exists_degree_le_finrank_add k hκ hL0
  exact riemann_roch_of_universallyClosed_of_degree_le k C hC hD

end Assembly

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

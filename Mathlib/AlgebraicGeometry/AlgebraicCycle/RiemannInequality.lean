/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.H1Cokernel

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

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

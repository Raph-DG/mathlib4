/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Preorder.Finite

/-!
# Dissociation and span

This file defines dissociation and span of sets in groups. These are analogs to the usual linear
independence and linear span of sets in a vector space but where the scalars are only allowed to be
`0` or `±1`. In characteristic 2 or 3, the two pairs of concepts are actually equivalent.

## Main declarations

* `MulDissociated`/`AddDissociated`: Predicate for a set to be dissociated.
* `Finset.mulSpan`/`Finset.addSpan`: Span of a finset.
-/

variable {α β : Type*} [CommGroup α] [CommGroup β]

section dissociation
variable {s : Set α} {t u : Finset α} {d : ℕ} {a : α}
open Set

/-- A set is dissociated iff all its finite subsets have different products.

This is an analog of linear independence in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/
@[to_additive "A set is dissociated iff all its finite subsets have different sums.

This is an analog of linear independence in a vector space, but with the \"scalars\" restricted to
`0` and `±1`."]
def MulDissociated (s : Set α) : Prop := {t : Finset α | ↑t ⊆ s}.InjOn (∏ x ∈ ·, x)

@[to_additive] lemma mulDissociated_iff_sum_eq_subsingleton :
    MulDissociated s ↔ ∀ a, {t : Finset α | ↑t ⊆ s ∧ ∏ x ∈ t, x = a}.Subsingleton :=
  ⟨fun hs _ _t ht _u hu ↦ hs ht.1 hu.1 <| ht.2.trans hu.2.symm,
    fun hs _t ht _u hu htu ↦ hs _ ⟨ht, htu⟩ ⟨hu, rfl⟩⟩

@[to_additive] lemma MulDissociated.subset {t : Set α} (hst : s ⊆ t) (ht : MulDissociated t) :
    MulDissociated s := ht.mono fun _ ↦ hst.trans'

@[to_additive (attr := simp)] lemma mulDissociated_empty : MulDissociated (∅ : Set α) := by
  simp [MulDissociated, subset_empty_iff]

@[to_additive (attr := simp)]
lemma mulDissociated_singleton : MulDissociated ({a} : Set α) ↔ a ≠ 1 := by
  simp [MulDissociated, setOf_or, -subset_singleton_iff,
    Finset.coe_subset_singleton]

@[to_additive (attr := simp)]
lemma not_mulDissociated :
    ¬ MulDissociated s ↔
      ∃ t : Finset α, ↑t ⊆ s ∧ ∃ u : Finset α, ↑u ⊆ s ∧ t ≠ u ∧ ∏ x ∈ t, x = ∏ x ∈ u, x := by
  simp [MulDissociated, InjOn]; aesop

@[to_additive]
lemma not_mulDissociated_iff_exists_disjoint :
    ¬ MulDissociated s ↔
      ∃ t u : Finset α, ↑t ⊆ s ∧ ↑u ⊆ s ∧ Disjoint t u ∧ t ≠ u ∧ ∏ a ∈ t, a = ∏ a ∈ u, a := by
  classical
  refine not_mulDissociated.trans
    ⟨?_, fun ⟨t, u, ht, hu, _, htune, htusum⟩ ↦ ⟨t, ht, u, hu, htune, htusum⟩⟩
  rintro ⟨t, ht, u, hu, htu, h⟩
  refine ⟨t \ u, u \ t, ?_, ?_, disjoint_sdiff_sdiff, sdiff_ne_sdiff_iff.2 htu,
    Finset.prod_sdiff_eq_prod_sdiff_iff.2 h⟩ <;> push_cast <;> exact diff_subset.trans ‹_›

@[to_additive (attr := simp)] lemma MulEquiv.mulDissociated_preimage (e : β ≃* α) :
    MulDissociated (e ⁻¹' s) ↔ MulDissociated s := by
  simp [MulDissociated, InjOn, ← e.finsetCongr.forall_congr_right, ← e.apply_eq_iff_eq,
    (Finset.map_injective _).eq_iff]

@[to_additive (attr := simp)] lemma mulDissociated_inv : MulDissociated s⁻¹ ↔ MulDissociated s :=
  (MulEquiv.inv α).mulDissociated_preimage

@[to_additive] protected alias ⟨MulDissociated.of_inv, MulDissociated.inv⟩ := mulDissociated_inv

end dissociation

namespace Finset
variable [DecidableEq α] [Fintype α] {s t u : Finset α} {a : α} {d : ℕ}

/-- The span of a finset `s` is the finset of elements of the form `∏ a ∈ s, a ^ ε a` where
`ε ∈ {-1, 0, 1} ^ s`.

This is an analog of the linear span in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/
@[to_additive "The span of a finset `s` is the finset of elements of the form `∑ a ∈ s, ε a • a`
where `ε ∈ {-1, 0, 1} ^ s`.

This is an analog of the linear span in a vector space, but with the \"scalars\" restricted to
`0` and `±1`."]
def mulSpan (s : Finset α) : Finset α :=
  (Fintype.piFinset fun _a ↦ ({-1, 0, 1} : Finset ℤ)).image fun ε ↦ ∏ a ∈ s, a ^ ε a

@[to_additive (attr := simp)]
lemma mem_mulSpan :
    a ∈ mulSpan s ↔ ∃ ε : α → ℤ, (∀ a, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) ∧ ∏ a ∈ s, a ^ ε a = a := by
  simp [mulSpan]

@[to_additive (attr := simp)]
lemma subset_mulSpan : s ⊆ mulSpan s := fun a ha ↦
  mem_mulSpan.2 ⟨Pi.single a 1, fun b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

@[to_additive]
lemma prod_div_prod_mem_mulSpan (ht : t ⊆ s) (hu : u ⊆ s) :
    (∏ a ∈ t, a) / ∏ a ∈ u, a ∈ mulSpan s :=
  mem_mulSpan.2 ⟨Set.indicator t 1 - Set.indicator u 1, fun a ↦ by
    by_cases a ∈ t <;> by_cases a ∈ u <;> simp [*], by simp [prod_div_distrib, zpow_sub,
      ← div_eq_mul_inv, Set.indicator, pow_ite, inter_eq_right.2, *]⟩

/-- If every dissociated subset of `s` has size at most `d`, then `s` is actually generated by a
subset of size at most `d`.

This is a dissociation analog of the fact that a set whose linearly independent subsets all have
size at most `d` is of dimension at most `d` itself. -/
@[to_additive "If every dissociated subset of `s` has size at most `d`, then `s` is actually
generated by a subset of size at most `d`.

This is a dissociation analog of the fact that a set whose linearly independent subspaces all have
size at most `d` is of dimension at most `d` itself."]
lemma exists_subset_mulSpan_card_le_of_forall_mulDissociated
    (hs : ∀ s', s' ⊆ s → MulDissociated (s' : Set α) → s'.card ≤ d) :
    ∃ s', s' ⊆ s ∧ s'.card ≤ d ∧ s ⊆ mulSpan s' := by
  classical
  obtain ⟨s', hs'⟩ :=
   (s.powerset.filter fun s' : Finset α ↦ MulDissociated (s' : Set α)).exists_maximal
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset] at hs'
  refine ⟨s', hs'.1.1, hs _ hs'.1.1 hs'.1.2, fun a ha ↦ ?_⟩
  by_cases ha' : a ∈ s'
  · exact subset_mulSpan ha'
  obtain ⟨t, u, ht, hu, htu⟩ := not_mulDissociated_iff_exists_disjoint.1 fun h ↦
    hs'.not_gt ⟨insert_subset_iff.2 ⟨ha, hs'.1.1⟩, h⟩ <| ssubset_insert ha'
  by_cases hat : a ∈ t
  · have : a = (∏ b ∈ u, b) / ∏ b ∈ t.erase a, b := by
      rw [prod_erase_eq_div hat, htu.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan
      ((subset_insert_iff_of_notMem <| disjoint_left.1 htu.1 hat).1 hu) (subset_insert_iff.1 ht)
  rw [coe_subset, subset_insert_iff_of_notMem hat] at ht
  by_cases hau : a ∈ u
  · have : a = (∏ b ∈ t, b) / ∏ b ∈ u.erase a, b := by
      rw [prod_erase_eq_div hau, htu.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan ht (subset_insert_iff.1 hu)
  · rw [coe_subset, subset_insert_iff_of_notMem hau] at hu
    cases not_mulDissociated_iff_exists_disjoint.2 ⟨t, u, ht, hu, htu⟩ hs'.1.2

end Finset

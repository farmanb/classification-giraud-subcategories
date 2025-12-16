/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Order.PFilter
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
--import Mathlib.Topology.Defs.Filter

open scoped Topology
open Filter
open scoped Pointwise

--import Mathlib.Topology.Defs.Basic
/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
`a : A`, the colon ideal `(I : a)` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is torsion if every element is torsion.
* `GabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
This is again a filter.
* `IsGabriel F` : a filter `F` is uniform if

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* https://ncatlab.org/nlab/show/uniform+filter
* https://ncatlab.org/nlab/show/Gabriel+filter
* https://ncatlab.org/nlab/show/Gabriel+composition+of+filters

## Tags

category theory, ideal, filter, ultrafilter, Gabriel filter
-/
universe u v

abbrev IdealFilter (A : Type u) [Ring A] := Order.PFilter (Ideal A)

--abbrev sets {A : Type u} [Ring A] (F : IdealFilter A) : Set (Ideal A) := F.carrier
/- variable (A : Type u) [Ring A] (F : IdealFilter A)
#check  -/


namespace IdealFilter

variable {A : Type u} [Ring A]

--structure IsUniform {A : Type u} [Ring A] (F : IdealFilter A) : Prop where
structure IsUniform (F : IdealFilter A) : Prop where
   (colon_closed : ∀ {I : Ideal A}, I ∈ F →
      ∀ a : A, (I.colon (Ideal.span {a})) ∈ F)

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`.  That is, there exists `L ∈ F` such that every `a ∈ L` satisfies
`a • m = 0`. -/
def IsTorsionElem (F : IdealFilter A)
      {M : Type v} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
   ∃ L ∈ F, ∀ a ∈ L, a • m = 0

/-- We say that an `A`-module `M` is `F`-torsion if every element of `M` is `F`-torsion in the
sense of `IsTorsionElem`. -/
def IsTorsion (F : IdealFilter A)
      (M : Type v) [AddCommMonoid M] [Module A M] : Prop :=
   ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`.  Equivalently, for each `k ∈ K` there exists `I ∈ F`
such that `I ≤ L.colon (Ideal.span {k})`. That is to say, every `a ∈ I` satisfies `a * k ∈ L`.
This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
   ∀ k ∈ K, ∃ I ∈ F, I ≤ L.colon (Ideal.span {k})

/-- If `k ∈ K`, then intersecting with `K` does not change the colon ideal. That is to say, there is
an equality of colon ideals: `(L : k) = (L ⊓ K : k)`. -/
lemma colon_inf_eq_for_mem (L K : Ideal A) {k : A} (h_k : k ∈ K) :
    (L ⊓ K).colon (Ideal.span ({k} : Set A)) = L.colon (Ideal.span ({k} : Set A)) := by
  -- ext `a : A` and unpack `Submodule.mem_colon`
  ext a
  constructor <;> intro h_a
  · -- `a ∈ (L ⊓ K).colon(span{k})` ⇒ `a ∈ L.colon(span{k})`
    -- use Submodule.mem_colon to rewrite membership
    rcases (Submodule.mem_colon).1 h_a with h
    -- need: ∀ p ∈ span{k}, a • p ∈ L
    apply (Submodule.mem_colon).2
    intro p h_p
    -- p ∈ span{k} ⇒ p = r * k
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 h_p
    -- from h we know: a • (r * k) ∈ L ⊓ K
    specialize h (r * k) ?_
    · exact h_p
    · rcases h with ⟨h_L, h_K⟩
      exact h_L
  · -- same in the other direction, using that k ∈ K gives automatic K-membership
    rcases (Submodule.mem_colon).1 h_a with h
    apply (Submodule.mem_colon).2
    intro p h_p
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 h_p
    -- a • (r * k) ∈ L by h
    have h_L : a • (r * k) ∈ L := h (r*k) h_p
    -- and also a • (r * k) ∈ K because k ∈ K and K is an ideal
    have h_K : a • (r * k) ∈ K := by
      -- use closure of K under multiplication by scalars and membership of k
      -- this is just Ideal.mul_mem_left followed by ring simp
      simpa [mul_assoc, smul_mul_assoc] using
        Ideal.mul_mem_left K a (Ideal.mul_mem_left K r h_k)
    exact ⟨h_L, h_K⟩

/-- Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the right. -/
@[simp]
lemma IsTorsionQuot_inter_left_iff
     (F : IdealFilter A)
    (L K : Ideal A) :
    IsTorsionQuot F L K ↔ IsTorsionQuot F (L ⊓ K) K := by
  unfold IsTorsionQuot
  constructor
  · intro h k h_k
    -- use the witness from `h`, then rewrite the colon using the lemma
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    refine ⟨I, h_I, ?_⟩
    -- `I ≤ L.colon(span{k})` and those two colon ideals are equal
    · have hcol :=
        colon_inf_eq_for_mem (L := L) (K := K) (k := k) h_k
      simpa [hcol] using h_I_le
  · intro h k h_k
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    refine ⟨I, h_I, ?_⟩ -- now use equality in the opposite direction
    · have hcol := colon_inf_eq_for_mem (L := L) (K := K) (k := k) h_k
      simpa [hcol] using h_I_le

@[simp] lemma IsTorsion_def (F : IdealFilter A)
      (M : Type v) [AddCommMonoid M] [Module A M] : IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m :=
  Iff.rfl

@[simp] lemma IsTorsionQuot_def (F : IdealFilter A) (L K : Ideal A) :
      IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F, I ≤ L.colon (Ideal.span {k}) :=
  Iff.rfl

/-- If `x ∈ I`, then the colon ideal `(x : I)` is the whole ring. -/
lemma colon_span_singleton_eq_top_of_mem {I : Ideal A} {x : A} (h_x : x ∈ I) :
    I.colon (Ideal.span {x}) = ⊤ := by
  apply (Ideal.eq_top_iff_one (I.colon (Ideal.span {x}))).mpr
  apply Submodule.mem_colon.mpr
  intro p h_p
  obtain ⟨a,rfl⟩ := Ideal.mem_span_singleton'.mp h_p
  simp only [one_smul,Ideal.mul_mem_left,h_x]

/-- For any filter `F` and ideal `J`, the quotient `J/J` is `F`-torsion in the sense of
`IsTorsionQuot`. -/
lemma IsTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x h_x
  obtain ⟨J, h_J⟩ := F.nonempty
  exact ⟨J, h_J, by simp[colon_span_singleton_eq_top_of_mem h_x]⟩

lemma IsTorsionQuot_mono_left (F : IdealFilter A)
    {I J K : Ideal A} (I_leq_J : I ≤ J) : IsTorsionQuot F I K → IsTorsionQuot F J K := by
  intro I_tors x h_x
  obtain ⟨L, ⟨L_in_F, h_L⟩⟩ := I_tors x h_x
  exact ⟨L, L_in_F, fun y h_y ⦃a⦄ a_1 ↦ I_leq_J (h_L h_y a_1)⟩

lemma isPFilter (F G : IdealFilter A) :
    Order.IsPFilter {L : Ideal A | ∃ K ∈ G, F.IsTorsionQuot L K} := by
    refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
    · obtain ⟨J,h_J⟩ := G.nonempty
      exact ⟨J, J, h_J, IsTorsionQuot_self F J⟩
    · rintro I ⟨K, h_K, h_IK⟩ J ⟨L, h_L, h_JL⟩
      refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
      · refine ⟨K ⊓ L, ?_, ?_⟩
        · exact Order.PFilter.inf_mem h_K h_L
        · rintro x h_x
          rcases h_x with ⟨x_K, x_L⟩
          obtain ⟨K₁, h_K₁F, h_K₁⟩ := h_IK x x_K
          obtain ⟨K₂, h_K₂F, h_K₂⟩ := h_JL x x_L
          refine ⟨K₁ ⊓ K₂, Order.PFilter.inf_mem h_K₁F h_K₂F, ?_⟩
          rintro y ⟨h_y₁, h_y₂⟩
          have h₁ := Submodule.mem_colon.mp (h_K₁ h_y₁)
          have h₂ := Submodule.mem_colon.mp (h_K₂ h_y₂)
          exact Submodule.mem_colon.mpr (fun p h_p => ⟨h₁ p h_p, h₂ p h_p⟩)
    · intro I J h_IJ ⟨K, h_K, h_IK⟩
      exact ⟨K, h_K, IsTorsionQuot_mono_left F h_IJ h_IK⟩

def GabrielComposition (F G : IdealFilter A) : IdealFilter A := (isPFilter F G).toPFilter

-- Declare notation for Gabriel composition
infixl:70 " • " => GabrielComposition

structure IsGabriel (F : IdealFilter A) extends IsUniform F where
    gabriel_closed : ∀ (I : Ideal A), (∃ J ∈ F, ∀ x ∈ J, I.colon (Ideal.span {x}) ∈ F) →
    I ∈ F

theorem isGabriel_iff (F : IdealFilter A) :
    F.IsGabriel ↔ F.IsUniform ∧ F • F = F := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    ext I
    constructor <;> intro h_I
    · rcases h_I with ⟨J,h_J, h_tors⟩
      unfold IsTorsionQuot at h_tors
      refine h₂ I ⟨J, h_J, ?_⟩
      intro x h_x
      rcases h_tors x h_x with ⟨K, h_K, h_incl⟩
      exact Order.PFilter.mem_of_le h_incl h_K
    · exact ⟨I, h_I, IsTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    rintro I ⟨J, h_J, h_colon⟩
    rw[←h₂]
    refine ⟨J, h_J,?_⟩
    intro x h_x
    exact ⟨I.colon (Ideal.span {x}), h_colon x h_x, by rfl⟩

section Topology
variable (F : IdealFilter A)

def addGroupFilterBasis : AddGroupFilterBasis A where
  sets := {(I : Set A) | I ∈ F}
  nonempty := by
    obtain ⟨I, h_I⟩ := F.nonempty
    exact ⟨I, ⟨I,h_I, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, h_I, rfl⟩ ⟨J, h_J, rfl⟩
    refine ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem h_I h_J, rfl⟩, ?_⟩
    intro x h
    exact h
  zero' := by
    rintro s ⟨I,h_I,rfl⟩
    exact zero_mem I
  add' := by
    rintro s ⟨I, h_I, rfl⟩
    refine ⟨I, ⟨I, h_I,rfl⟩, Set.add_subset_iff.mpr ?_⟩
    exact fun x a y a_1 ↦ add_mem a a_1
  neg' := by
    rintro s ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, by simp⟩
  conj' := by
    rintro x₀ s ⟨I,h_I,rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩,by simp⟩

def ringFilterBasis (uni_F : IsUniform F) : RingFilterBasis A where
  sets := F.addGroupFilterBasis.sets
  nonempty := F.addGroupFilterBasis.nonempty
  inter_sets := F.addGroupFilterBasis.inter_sets
  zero' := F.addGroupFilterBasis.zero'
  add' := F.addGroupFilterBasis.add'
  neg' := F.addGroupFilterBasis.neg'
  conj' := F.addGroupFilterBasis.conj'
  mul' := by
    rintro s ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, Set.mul_subset_iff.mpr fun _ h₁ _ h₂ => mul_mem h₁ h₂⟩
  mul_left' := by
    rintro x₀ s ⟨I, h_I, rfl⟩
    refine ⟨I, ⟨I,h_I,rfl⟩, ?_⟩
    intro x h_x
    exact Ideal.mul_mem_left I x₀ h_x
  mul_right' := by
    rintro x₀ s ⟨I, h_I, rfl⟩
    refine ⟨I.colon (Ideal.span {x₀}), ?_, ?_⟩
    · exact ⟨I.colon (Ideal.span {x₀}), uni_F.colon_closed h_I x₀, rfl⟩
    · intro x h_x
      exact Submodule.mem_colon.mp h_x x₀ (Ideal.mem_span_singleton_self x₀)

def topology : TopologicalSpace A := (addGroupFilterBasis F).topology

def isTopologicalAddGroup :
    letI : TopologicalSpace A := F.topology
    IsTopologicalAddGroup A :=
  F.addGroupFilterBasis.isTopologicalAddGroup

def ringTopology (uni_F : IsUniform F) : TopologicalSpace A :=
  (ringFilterBasis F uni_F).topology

def isTopologicalRing (uni_F : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    IsTopologicalRing A :=
  (F.ringFilterBasis uni_F).isTopologicalRing

/-- In the topology on `A` induced by an ideal filter `F`, every translate `x +ᵥ I` of an ideal
`I ∈ F` is an open neighborhood of `x`.

This is the basic “linear” feature of `topology_of_IdealFilter`: neighborhoods are generated by
(translates of) ideals coming from the filter. -/
lemma isOpen_leftAddCoset (x : A) {I : Ideal A} (h_I : I ∈ F) :
    letI : TopologicalSpace A := F.topology
    IsOpen (x +ᵥ (I : Set A)) := by
  letI : TopologicalSpace A := F.topology
  refine (isOpen_iff_mem_nhds).mpr ?_
  rintro y ⟨z, h_z, rfl⟩
  have : x +ᵥ (I : Set A) = (x + z) +ᵥ (I : Set A) := by
    have : z +ᵥ (I : Set A) = (I : Set A) :=
      leftAddCoset_mem_leftAddCoset I.toAddSubgroup h_z
    rw[← leftAddCoset_assoc,this]
  rw[this]
  refine ((F.addGroupFilterBasis).nhds_hasBasis (x + z)).mem_iff.2 ?_
  refine ⟨(I : Set A), ?_, ?_⟩
  · exact ⟨I, h_I, rfl⟩
  · intro y hy; exact hy

lemma mem_nhds_iff (a : A) (s : Set A) :
    letI : TopologicalSpace A := F.topology
    s ∈ 𝓝 a ↔ ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro h_s
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 h_s with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨(I : Set A), ⟨I, hI, rfl⟩, hIs⟩

/-- A set is open in `topology_of_IdealFilter F` iff it contains a basic coset neighborhood around
each of its points. -/
lemma isOpen_iff_exists_leftAddCoset_subset (s : Set A) :
    letI : TopologicalSpace A := F.topology
    IsOpen s ↔ ∀ a ∈ s, ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  letI : TopologicalSpace A := F.topology
  constructor
  · intro h_s a h_a
    rw[← F.mem_nhds_iff a s]
    exact IsOpen.mem_nhds h_s h_a
  · intro h
    refine (isOpen_iff_mem_nhds).2 ?_
    intro a h_a
    exact (F.mem_nhds_iff a s).2 (h a h_a)


end Topology

end IdealFilter

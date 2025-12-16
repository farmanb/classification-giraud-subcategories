/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
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

## Tags

category theory, ideal, filter, ultrafilter, Gabriel filter
-/
universe u v

structure IdealFilter (A : Type u) [Ring A] where
  (sets : Set (Ideal A))
  (nonempty : sets.Nonempty)
  (upward_closed : ∀ {I J : Ideal A}, I ∈ sets → I ≤ J → J ∈ sets)
  (inter_closed  : ∀ {I J : Ideal A}, I ∈ sets → J ∈ sets → I ⊓ J ∈ sets)

namespace IdealFilter

variable {A : Type u} [Ring A]

@[ext]
lemma ext {F G : IdealFilter A} (h : F.sets = G.sets) : F = G := by
  cases F; cases G
  cases h
  simp

--structure IsUniform {A : Type u} [Ring A] (F : IdealFilter A) : Prop where
structure IsUniform (F : IdealFilter A) : Prop where
   (colon_closed : ∀ {I : Ideal A}, I ∈ F.sets →
      ∀ a : A, (I.colon (Ideal.span {a})) ∈ F.sets)

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`.  That is, there exists `L ∈ F.sets` such that every `a ∈ L` satisfies
`a • m = 0`. -/
def IsTorsionElem (F : IdealFilter A)
      {M : Type v} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
   ∃ L ∈ F.sets, ∀ a ∈ L, a • m = 0

/-- We say that an `A`-module `M` is `F`-torsion if every element of `M` is `F`-torsion in the
sense of `IsTorsionElem`. -/
def IsTorsion (F : IdealFilter A)
      (M : Type v) [AddCommMonoid M] [Module A M] : Prop :=
   ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`.  Equivalently, for each `k ∈ K` there exists `I ∈ F.sets`
such that `I ≤ L.colon (Ideal.span {k})`. That is to say, every `a ∈ I` satisfies `a * k ∈ L`.
This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
   ∀ k ∈ K, ∃ I ∈ F.sets, I ≤ L.colon (Ideal.span {k})

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
      IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F.sets, I ≤ L.colon (Ideal.span {k}) :=
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

def GabrielComposition (F G : IdealFilter A) : IdealFilter A where
  sets := {L : Ideal A | ∃ K ∈ G.sets, F.IsTorsionQuot L K}
  nonempty := by
    obtain ⟨J,h_J⟩ := G.nonempty
    exact ⟨J, J, h_J, IsTorsionQuot_self F J⟩
  upward_closed := by
    rintro I J ⟨K, h_KG, h_K⟩ h_IJ
    exact ⟨K, h_KG, IsTorsionQuot_mono_left F h_IJ h_K⟩
  inter_closed := by
    rintro I J ⟨K,h_KG,h_K⟩ ⟨L,h_LG,h_L⟩
    refine ⟨K ⊓ L, G.inter_closed h_KG h_LG, ?_⟩
    · rintro x ⟨x_K, x_L⟩
      obtain ⟨K₁, K₁_F, h_K₁⟩ := h_K x x_K
      obtain ⟨K₂, K₂_F, h_K₂⟩ := h_L x x_L
      refine ⟨K₁ ⊓ K₂, F.inter_closed K₁_F K₂_F, ?_⟩
      · rintro y ⟨y_K₁, y_K₂⟩
        have h₁ := Submodule.mem_colon.mp (h_K₁ y_K₁)
        have h₂ := Submodule.mem_colon.mp (h_K₂ y_K₂)
        exact Submodule.mem_colon.mpr (fun p h_p => ⟨h₁ p h_p, h₂ p h_p⟩)

-- Declare notation for Gabriel composition
infixl:70 " • " => GabrielComposition

structure IsGabriel (F : IdealFilter A) extends IsUniform F where
    gabriel_closed : ∀ (I : Ideal A), (∃ J ∈ F.sets, ∀ x ∈ J, I.colon (Ideal.span {x}) ∈ F.sets) →
    I ∈ F.sets

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
      exact F.upward_closed h_K h_incl
    · exact ⟨I, h_I, IsTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    rintro I ⟨J, h_J, h_colon⟩
    rw[←h₂]
    refine ⟨J, h_J,?_⟩
    intro x h_x
    exact ⟨I.colon (Ideal.span {x}), h_colon x h_x, by rfl⟩

section topology
variable (F : IdealFilter A)

def nhds_basis_of_IdealFilter (a : A) : FilterBasis A where
  --sets := a +ᵥ {s | ∃ I ∈ F.sets, s = I.carrier}
  sets := a +ᵥ {s | ∃ I ∈ F.sets, s = (I : Set A)}
  nonempty := by
    obtain ⟨I, h_I⟩ := F.nonempty
    exact ⟨a +ᵥ (I : Set A), ⟨(I : Set A), ⟨I, h_I, rfl⟩, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨s', ⟨I,h_I,rfl⟩, rfl⟩ ⟨t', ⟨J, h_J, rfl⟩, rfl⟩
    exact ⟨a +ᵥ ((I ⊓ J) : Set A),
      ⟨((I ⊓ J) : Set A), ⟨I ⊓ J, F.inter_closed h_I h_J, rfl⟩, rfl⟩,
      by simp⟩

def nhds_of_IdealFilter (a : A) : Filter A := FilterBasis.filter (nhds_basis_of_IdealFilter F a)

/-- The topology on `A` induced by an ideal filter `F`.

A subset `s : Set A` is declared open if for every `x ∈ s` there exists an ideal `I ∈ F.sets`
such that the (left) coset `x +ᵥ I` is contained in `s`. Equivalently, the sets `x +ᵥ I` with
`I ∈ F.sets` form a neighborhood basis at each point `x`.

This is the standard way to build a (left) linear topology from a family of ideals, and it is
the starting point for proving that additional hypotheses on `F` (e.g. uniformity) make `A` into
a topological ring. -/
def topology_of_IdealFilter : TopologicalSpace A :=
  TopologicalSpace.mkOfNhds (nhds_of_IdealFilter F)

/-- In the topology on `A` induced by an ideal filter `F`, every translate `x +ᵥ I` of an ideal
`I ∈ F.sets` is an open neighborhood of `x`.

This is the basic “linear” feature of `topology_of_IdealFilter`: neighborhoods are generated by
(translates of) ideals coming from the filter. -/
lemma isOpen_leftAddCoset (x : A) {I : Ideal A} (h_I : I ∈ F.sets) :
      letI : TopologicalSpace A := topology_of_IdealFilter F
      IsOpen (x +ᵥ (I : Set A)) := by
  rintro y ⟨z, h_z : z ∈ I, h_sum : x + z = y⟩
  refine ⟨y +ᵥ (I : Set A), ⟨(I : Set A), ⟨I, h_I, rfl⟩, rfl⟩, ?_⟩
  have : x +ᵥ (I : Set A) = y +ᵥ (I : Set A) := by
    apply (leftAddCoset_eq_iff (I.toAddSubgroup)).mpr
    simp[← h_sum,h_z]
  rw[this]

/-- If `s : Set A` contains the translate `(a + b) +ᵥ I` of an ideal `I`, then the preimage of `s`
under addition contains the rectangle `(a +ᵥ I) ×ˢ (b +ᵥ I)`. In other words, translating by `I`
in each coordinate keeps sums inside `s`. -/
lemma prod_leftAddCoset_subset_preimage_add
    (s : Set A) (a b : A) (I : Ideal A)
    (h_translate : (a + b) +ᵥ (I : Set A) ⊆ s) :
    (a +ᵥ (I : Set A)) ×ˢ (b +ᵥ (I : Set A)) ⊆ (fun p : A × A ↦ p.1 + p.2) ⁻¹' s := by
  rintro ⟨p₁, p₂⟩ ⟨⟨u, h_u, rfl⟩, ⟨v, h_v, rfl⟩⟩
  apply h_translate
  refine ⟨u + v, I.add_mem h_u h_v, ?_⟩
  change a + b + (u + v) = a + u + (b + v)
  abel

/-- Membership in `nhds_of_IdealFilter F a` means that the set contains a basic coset neighborhood
`a +ᵥ I` with `I ∈ F.sets`. -/
lemma mem_nhds_of_IdealFilter_iff (a : A) (s : Set A) :
    s ∈ nhds_of_IdealFilter F a ↔ ∃ I : Ideal A, I ∈ F.sets ∧ a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro h_s
    rcases h_s with ⟨t,h_t,h_incl⟩
    rcases h_t with ⟨u,h_u,rfl⟩
    rcases h_u with ⟨I, h_I, rfl⟩
    exact ⟨I,h_I,h_incl⟩
  · rintro ⟨I, h_I, h_incl⟩
    refine (FilterBasis.mem_filter_iff (F.nhds_basis_of_IdealFilter a)).2 ?_
    refine ⟨a +ᵥ (I : Set A), ?_, h_incl⟩
    exact ⟨(I : Set A), ⟨I, h_I, rfl⟩, rfl⟩

/-- In the topology `topology_of_IdealFilter F`, the neighborhood filter at `a` is exactly the
filter `nhds_of_IdealFilter F a` generated by the basic cosets `a +ᵥ I` with `I ∈ F.sets`.

Equivalently, a set `n : Set A` is a neighborhood of `a` (i.e. `n ∈ 𝓝 a`) iff it contains some
basic coset neighborhood `a +ᵥ I` with `I ∈ F.sets`. -/
@[simp]
lemma nhds_eq_nhds_of_IdealFilter (a : A) :
    letI : TopologicalSpace A := topology_of_IdealFilter F
    𝓝 a = nhds_of_IdealFilter F a := by
  letI : TopologicalSpace A := topology_of_IdealFilter F
  ext n
  constructor <;> rw[mem_nhds_iff]
  · rintro ⟨t, h_tn, open_t, h_at⟩
    exact mem_of_superset (open_t a h_at) h_tn
  · rw[mem_nhds_of_IdealFilter_iff]
    rintro ⟨I, h_I, h_incl⟩
    refine ⟨a +ᵥ (I : Set A),
      h_incl,
      isOpen_leftAddCoset F a h_I,
      mem_own_leftAddCoset I.toAddSubmonoid a⟩

/-- A set is open in `topology_of_IdealFilter F` iff it contains a basic coset neighborhood around
each of its points. -/
lemma isOpen_iff_exists_leftAddCoset_subset (s : Set A) :
    letI : TopologicalSpace A := F.topology_of_IdealFilter
    IsOpen s ↔ ∀ a ∈ s, ∃ I ∈ F.sets, a +ᵥ (I : Set A) ⊆ s := by
  letI : TopologicalSpace A := F.topology_of_IdealFilter
  exact ⟨fun h_s a h_a => (mem_nhds_of_IdealFilter_iff F a s).mp (h_s a h_a),
    fun h a h_a => (mem_nhds_of_IdealFilter_iff F a s).mpr (h a h_a)⟩

/-- The underlying additive group of `A` is a topological group for the topology induced by an
ideal filter `F`.

More precisely, with `TopologicalSpace A` given by `topology_of_IdealFilter F` (whose neighborhoods
of a point `x` are generated by cosets `x +ᵥ I` for ideals `I ∈ F.sets`), both addition
`(fun p : A × A ↦ p.1 + p.2)` and negation `(fun x : A ↦ -x)` are continuous, yielding an
`IsTopologicalAddGroup` instance. -/
def isTopologicalAddGroup :
    letI : TopologicalSpace A := topology_of_IdealFilter F
    IsTopologicalAddGroup A := by
  letI isTopologicalSpace : TopologicalSpace A := topology_of_IdealFilter F
  refine { toContinuousAdd := ?_, toContinuousNeg := ?_ }
  · refine { continuous_add := ?_ }
    refine {
      isOpen_preimage := by
        intro s h_s
        refine isOpen_prod_iff.mpr ?_
        intro a b (h_ab : a + b ∈ s)
        rcases ((F.isOpen_iff_exists_leftAddCoset_subset s).mp h_s (a + b) h_ab)
          with ⟨I, h_I, h_incl⟩
        refine ⟨a +ᵥ (I : Set A),
          b +ᵥ (I : Set A),
          isOpen_leftAddCoset F a h_I,
          isOpen_leftAddCoset F b h_I,
          mem_own_leftAddCoset I.toAddSubmonoid a,
          mem_own_leftAddCoset I.toAddSubmonoid b,
          prod_leftAddCoset_subset_preimage_add s a b I h_incl⟩
    }
  · refine { continuous_neg := {
      isOpen_preimage := by
        intro s h_s x (h_nx : -x ∈ s)
        rcases ((F.isOpen_iff_exists_leftAddCoset_subset s).mp h_s (-x) h_nx) with
          ⟨I, h_I, h_incl⟩
        change -x +ᵥ (I : Set A) ⊆ s at h_incl
        refine ⟨x +ᵥ (I : Set A), ⟨I, ⟨I, h_I, rfl⟩,rfl⟩,?_⟩
        intro y ⟨z,h_z,(h_sum : x + z = y)⟩
        change -y ∈ s
        rw[← h_sum, neg_add]
        apply h_incl
        exact ⟨-z, Submodule.neg_mem I h_z, rfl⟩
  } }

/-- If `F` is uniform, then `topology_of_IdealFilter F` makes `A` into a topological ring. -/
def isTopologicalRing (uni_F : IsUniform F) :
    letI : TopologicalSpace A := topology_of_IdealFilter F
    IsTopologicalRing A := by
      letI isTopologicalSpace_A: TopologicalSpace A := topology_of_IdealFilter F
      letI isTopologicalAddGroup_A : IsTopologicalAddGroup A := isTopologicalAddGroup F
      exact{
      continuous_add := continuous_add
      continuous_mul := {
        isOpen_preimage := by
          intro s h_s
          refine isOpen_prod_iff.mpr ?_
          intro a b (h_ab : a*b ∈ s)
          rcases (F.isOpen_iff_exists_leftAddCoset_subset s).mp h_s (a*b) h_ab with
            ⟨I, h_I, h_incl⟩
          refine ⟨a +ᵥ ((I.colon (Ideal.span {b})) : Set A),
            b +ᵥ (I : Set A),
            isOpen_leftAddCoset F a (uni_F.colon_closed h_I b),
            isOpen_leftAddCoset F b h_I,
            mem_own_leftAddCoset _ a,
            mem_own_leftAddCoset _ b,
            ?_⟩
          · rintro ⟨p₁,p₂⟩ ⟨h_p₁, h_p₂⟩
            rcases h_p₁ with ⟨x, h_x, rfl⟩
            rcases h_p₂ with ⟨y, h_y, rfl⟩
            apply h_incl
            change (a + x) * (b + y) ∈ (a*b) +ᵥ (I : Set A)
            refine (mem_leftAddCoset_iff (a*b)).mpr ?_
            rw[add_mul, mul_add, ← add_assoc, ← add_assoc, neg_add_cancel, zero_add, mul_add,
               ←add_assoc]
            exact I.add_mem
              (I.add_mem (Ideal.mul_mem_left I a h_y)
                (Submodule.mem_colon.mp h_x b (Ideal.mem_span_singleton_self b)))
              (Ideal.mul_mem_left I x h_y)}
      continuous_neg := continuous_neg}

end topology

end IdealFilter

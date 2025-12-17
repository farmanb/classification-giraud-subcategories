import ClassificationGiraudSubcategories.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.FilterBasis

open scoped Pointwise
open scoped Topology

namespace IdealFilter

variable {A : Type u} [Ring A] (F : IdealFilter A)

def addGroupFilterBasis : AddGroupFilterBasis A where
  sets := {(I : Set A) | I ∈ F}
  nonempty := by
    obtain ⟨I, h_I⟩ := F.nonempty
    exact ⟨I, ⟨I, h_I, rfl⟩⟩
  inter_sets := by
    rintro s t ⟨I, h_I, rfl⟩ ⟨J, h_J, rfl⟩
    refine ⟨I ⊓ J, ⟨I ⊓ J, Order.PFilter.inf_mem h_I h_J, rfl⟩, ?_⟩
    intro x h
    exact h
  zero' := by
    rintro s ⟨I, h_I, rfl⟩
    exact zero_mem I
  add' := by
    rintro s ⟨I, h_I, rfl⟩
    refine ⟨I, ⟨I, h_I, rfl⟩, Set.add_subset_iff.mpr ?_⟩
    exact fun x a y a_1 ↦ add_mem a a_1
  neg' := by
    rintro s ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, by simp⟩
  conj' := by
    rintro x₀ s ⟨I, h_I, rfl⟩
    exact ⟨I, ⟨I, h_I, rfl⟩, by simp⟩

def ringFilterBasis (uni_F : F.IsUniform) : RingFilterBasis A where
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
    refine ⟨I, ⟨I, h_I, rfl⟩, ?_⟩
    intro x h_x
    exact Ideal.mul_mem_left I x₀ h_x
  mul_right' := by
    rintro x₀ s ⟨I, h_I, rfl⟩
    refine ⟨I.colon (Ideal.span {x₀}), ?_, ?_⟩
    · exact ⟨I.colon (Ideal.span {x₀}), uni_F.colon_mem h_I x₀, rfl⟩
    · intro x h_x
      exact Submodule.mem_colon.mp h_x x₀ (Ideal.mem_span_singleton_self x₀)

def addGroupTopology : TopologicalSpace A := (addGroupFilterBasis F).topology

theorem isTopologicalAddGroup :
    letI : TopologicalSpace A := F.addGroupTopology
    IsTopologicalAddGroup A :=
  F.addGroupFilterBasis.isTopologicalAddGroup

def ringTopology (uni_F : F.IsUniform) : TopologicalSpace A :=
  (ringFilterBasis F uni_F).topology

theorem isTopologicalRing (uni_F : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    IsTopologicalRing A :=
  (F.ringFilterBasis uni_F).isTopologicalRing

lemma mem_nhds_iff (a : A) (s : Set A) :
    letI : TopologicalSpace A := F.addGroupTopology
    s ∈ 𝓝 a ↔ ∃ I ∈ F, a +ᵥ (I : Set A) ⊆ s := by
  constructor
  · intro h_s
    rcases ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.1 h_s with ⟨t, ht, hts⟩
    rcases ht with ⟨I, hI, rfl⟩
    exact ⟨I, hI, hts⟩
  · rintro ⟨I, hI, hIs⟩
    refine ((F.addGroupFilterBasis).nhds_hasBasis a).mem_iff.2 ?_
    exact ⟨(I : Set A), ⟨I, hI, rfl⟩, hIs⟩


theorem isLinearTopology_addGroupTopology :
    letI : TopologicalSpace A := F.addGroupTopology
    IsLinearTopology A A := by
  letI : TopologicalSpace A := F.addGroupTopology
  have hBasis :
      (𝓝 (0 : A)).HasBasis (fun I : Ideal A => I ∈ F) (fun I : Ideal A => (I : Set A)) := by
    refine ⟨?_⟩
    intro U
    simpa using (F.mem_nhds_iff (a := (0 : A)) (s := U))
  refine IsLinearTopology.mk_of_hasBasis' (R := A) (M := A)
      (ι := Ideal A) (S := Ideal A)
      (p := fun I : Ideal A => I ∈ F) (s := fun I : Ideal A => I)
      ?basis ?closure
  · simpa using hBasis
  · intro I r m hm
    simpa using Ideal.mul_mem_left I r hm

theorem isLinearTopology_ringTopology (uni_F : F.IsUniform) :
    letI : TopologicalSpace A := F.ringTopology uni_F
    IsLinearTopology A A := by
  letI : TopologicalSpace A := F.ringTopology uni_F
  have hBasis :
      (𝓝 (0 : A)).HasBasis (fun I : Ideal A => I ∈ F) (fun I : Ideal A => (I : Set A)) := by
    refine ⟨?_⟩
    intro U
    simpa using (F.mem_nhds_iff (a := (0 : A)) (s := U))
  refine IsLinearTopology.mk_of_hasBasis' (R := A) (M := A)
      (ι := Ideal A) (S := Ideal A)
      (p := fun I : Ideal A => I ∈ F) (s := fun I : Ideal A => I)
      ?basis ?closure
  · simpa using hBasis
  · intro I r m hm
    simpa using Ideal.mul_mem_left I r hm
end IdealFilter

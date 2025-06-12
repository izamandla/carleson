import Carleson.Project.modules.Utiles
open Extra
open BinaryRepresentationSet
open Walsh
/- ## Main result -/

theorem aboutM1 {N M :ℕ } (h1 : M ∈ binaryRepresentationSet N) : 2 ^ M ≤ N := by
  rw[← binaryRepresentationSet_explicit N]
  exact CanonicallyOrderedAddCommMonoid.single_le_sum h1

theorem aboutM2help {M: ℕ} : ∑ k ∈ Finset.range M, 2^k < 2^M :=by
  refine Nat.geomSum_lt ?_ ?_
  · simp
  · simp

theorem aboutM2 {N M :ℕ } (h1 : M ∈ binaryRepresentationSet N)  (h2: ∀ j > M, j ∉ binaryRepresentationSet N) :  N< 2^(M+1) := by
  rw[← binaryRepresentationSet_explicit N]
  have h0 : binaryRepresentationSet N ⊆ Finset.range (M+1) := by
    intro k hk
    simp only [Finset.mem_range]
    exact Nat.gt_of_not_le fun a ↦ h2 k a hk
  have h : ∑ k ∈ binaryRepresentationSet N, 2 ^ k < ∑ k ∈ Finset.range (M+1), 2^k :=by
    -- Finset.sum_lt_sum_of_subset h0  coś nie działa
    sorry
  refine Nat.geomSum_lt ?_ ?_
  · simp
  · exact fun k a ↦ Nat.gt_of_not_le fun a_1 ↦ h2 k a_1 a


theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
  Walsh.walshFourierPartialSum f N x = (∫ y in Set.Ico 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
  unfold Walsh.walshFourierPartialSum
  by_cases hN : N = 0
  · rw[hN]
    simp only [Finset.range_zero, Finset.sum_empty]
    --cos chyba robie zle
    sorry
  push_neg at hN
  obtain ⟨M, hM⟩ := max_binaryRepresentationSet N (Nat.zero_lt_of_ne_zero hN)
  have hM1 : 2^M ≤ N := aboutM1 hM.1
  have hM2 : N < 2^(M+1) := aboutM2 hM.1 hM.2
  set N' := N - 2^M with hN'
  rw[partition hM1, lemma1_2 hM1 hM2, lemma2 hM1 hM2 hN']
  unfold walshInnerProduct
  --simp only [Pi.mul_apply]
  --MeasureTheory.integral_finset_sum
  --jak wlozyc sume pod calke?


  all_goals sorry

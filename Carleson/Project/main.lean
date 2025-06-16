import Carleson.Project.modules.Utiles
open Extra
open BinaryRepresentationSet
open Walsh
/- ## Main result -/




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
  have hM2 : N < 2^(M+1) := sorry -- aboutM2 hM.1 hM.2
  set N' := N - 2^M with hN'
  rw[partition hM1, lemma1_2 hM1 hM2] --lemma2 hM1 hM2 hN']
  unfold walshInnerProduct
  --simp only [Pi.mul_apply]
  --rw[MeasureTheory.integral_finset_sum]
  --jak wlozyc sume pod calke?


  all_goals sorry

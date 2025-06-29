import Carleson.Project.modules.Utiles
open Extra
open BinaryRepresentationSet
open Walsh Function Set MeasureTheory
/- ## Main result -/




theorem mainresult (N : ℕ) (f : ℝ → ℝ) (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x < 1) (hf : MeasureTheory.LocallyIntegrable f):
  Walsh.walshFourierPartialSum f N x = (∫ y in Set.Ico 0 1, f y * Walsh.walsh N y * Walsh.walsh N x * Kernel.kernel N x y) := by
  have hf' : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Ico 0 1)) := by
      refine MeasureTheory.IntegrableOn.integrable ?_
      apply MeasureTheory.IntegrableOn.mono_set ( t := Icc 0 1)
      · rw[MeasureTheory.locallyIntegrable_iff] at hf
        apply hf
        exact isCompact_Icc
      · exact Ico_subset_Icc_self
  unfold Walsh.walshFourierPartialSum
  by_cases hN : N = 0
  · rw[hN]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    unfold walshInnerProduct
    conv_lhs => rw[walsh_zero hx1 hx2, mul_one]
    apply MeasureTheory.integral_congr_ae
    simp only [measurableSet_Ico, MeasureTheory.ae_restrict_eq]
    refine Filter.eventuallyEq_inf_principal_iff.mpr ?_
    apply Filter.Eventually.of_forall
    intro y hy
    simp only [Set.mem_Ico] at hy
    rw[walsh_zero hy.1 hy.2, walsh_zero hx1 hx2, Kernel.kernel_zero]
    simp only [mul_one]
  push_neg at hN
  obtain ⟨M, hM⟩ := max_binaryRepresentationSet N (Nat.zero_lt_of_ne_zero hN)
  have hM1 : 2^M ≤ N := aboutM1 hM.1
  have hM2 : N < 2^(M+1) := aboutM2 hM.2
  set N' := N - 2^M with hN'
  rw[partition hM1, lemma1_2 hM1 hM2 f hf , lemma2 hM1 hM2 hN' f hf]
  · unfold walshInnerProduct
    simp_rw[← MeasureTheory.integral_mul_const]
    rw[← MeasureTheory.integral_finset_sum, ← MeasureTheory.integral_finset_sum]
    · rw[← MeasureTheory.integral_add']
      · simp only [Pi.mul_apply, Pi.add_apply]
        apply MeasureTheory.integral_congr_ae
        rw[Filter.EventuallyEq ]
        apply Filter.Eventually.of_forall
        intro y
        -- to musi zostac zrobione przez indukcje
        sorry
      · sorry
      · sorry
    · intro i hi
      have : (fun a ↦ (Haar.rademacherFunction M * f) a * walsh i a * Haar.rademacherFunction M x * walsh i x) = (fun a ↦ Haar.rademacherFunction M x * walsh i x * Haar.rademacherFunction M a * walsh i a *  f a) := by
        ext a
        simp only [Pi.mul_apply]
        linarith
      simp_rw[this]
      apply MeasureTheory.BoundedCompactSupport.integrable_mul
      · simp_rw[mul_assoc]
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.const_mul
        apply MeasureTheory.BoundedCompactSupport.restrict
        apply MeasureTheory.BoundedCompactSupport.mul
        · exact Haar.bcs_rademacher
        · exact bcs_walsh
      · exact hf'

    · sorry
  · exact hx1
  · exact hx2

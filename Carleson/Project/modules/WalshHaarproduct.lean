import Carleson.Project.modules.relationWalshRademacher
import Mathlib.Data.Real.StarOrdered

open InnerProductSpace MeasureTheory Set BigOperators
open Walsh Haar BinaryRepresentationSet WalshRademacher
open Function Set
open unitInterval DyadicStructures

noncomputable section

def walshhaar (M k : ℕ) : ℝ → ℝ
| x =>
  walsh (2^M) x * (haarFunctionScaled (-M) k x)

theorem walshhaarprophelp {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) : (∑ n ∈ Finset.range (2 ^ M), haarFunctionScaled (-↑M) (↑n) x) *
    haarFunctionScaled (-↑M) (↑k) x = haarFunctionScaled (-↑M) (↑k) x *
    haarFunctionScaled (-↑M) (↑k) x := by
      rw[Finset.sum_mul, Finset.sum_eq_sum_diff_singleton_add hk fun x_1 ↦
            haarFunctionScaled (-↑M) (↑x_1) x * haarFunctionScaled (-↑M) (↑k) x, add_eq_right]
      apply Finset.sum_eq_zero
      intro l hl
      rw[← haarFunctionScaled_mul (k := -M) (n:= l) (n':= k) (x:= x)]
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hl
      norm_cast
      exact hl.2


theorem walshhaarprop {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) (hx1 : 0 ≤ x) (hx2 : x < 1) :  walshhaar M k x = (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M / 2 : ℝ)) x:= by
  unfold walshhaar
  simp only
  rw[differentwalshRademacherRelation hx1 hx2, rademacherFunction]
  rw[mul_assoc, walshhaarprophelp hk, indicator]
  split_ifs with h1
  · have h : x  ∈ dyadicInterval (-M) k := by
      simp only [eqdef1, Int.cast_natCast, h1]
    rw[eqdef2'', mul_comm] at h
    rw[← pow_two, haarFunctionScaled_sqr h.1 h.2 ]
    simp only [neg_neg, Pi.pow_apply, Pi.ofNat_apply]
    rw[←Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
    congr
    push_cast
    ring
  · rw[haarFunctionScaled_outside]
    · simp
    · simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
      simp only [zpow_neg, zpow_natCast, mem_Ico, Decidable.not_and_iff_or_not, not_le, not_lt] at h1
      rw[ ← lt_inv_mul_iff₀]
      · rw[inv_mul_le_iff₀] at h1
        · rw[le_sub_iff_add_le, add_comm]
          exact h1
        · simp
      · simp





theorem walshhaarprop' {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) :  walshhaar M k x = (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M / 2 : ℝ)) x:= by
  by_cases hx : 0≤ x ∧ x<1
  · exact walshhaarprop hk hx.1 hx.2
  · simp only [walshhaar]
    rw[walsh_not_in x ]
    · rw[zero_mul, indicator]
      rw [@eq_ite_iff]
      right
      constructor
      · by_contra h1
        have h : x  ∈ dyadicInterval (-M) k := by
          simp only [eqdef1, Int.cast_natCast, h1]
        simp only [Finset.mem_range] at hk
        apply ago hk at h
        exact hx h
      · simp
    · simp only [Decidable.not_and_iff_or_not, not_le, not_lt] at hx
      exact hx


theorem walshhaarprop'' {M k : ℕ} (hk : k ∈ Finset.range (2 ^ M)) : (fun x ↦   walshhaar M k x) =(fun x ↦  (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M / 2 : ℝ)) x):= by
  ext x
  exact walshhaarprop' hk



theorem walshhaarpropsqr {M k : ℕ} {x : ℝ} (hk : k ∈ Finset.range (2 ^ M)) (hx1 : 0 ≤ x) (hx2 : x < 1) :  (walshhaar M k x)*(walshhaar M k x) = (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M :ℝ  )) x:= by
  rw[walshhaarprop hk hx1 hx2]
  simp_rw[indicator, zpow_neg, zpow_natCast, mem_Ico, Pi.pow_apply, Pi.ofNat_apply, mul_ite, ite_mul,
    zero_mul, mul_zero]
  by_cases h : (2 ^ M)⁻¹ * ↑k ≤ x ∧ x < (2 ^ M)⁻¹ * (↑k + 1)
  · simp only [h, and_self, ↓reduceIte]
    rw[ ← Real.rpow_add (by norm_num)]
    simp
  · simp[h]

theorem walshhaarsqr' {M k : ℕ} (hk : k ∈ Finset.range (2 ^ M)) :  (walshhaar M k)*(walshhaar M k ) = (2 ^ (M / 2 : ℝ))* walshhaar M k := by
  ext x
  by_cases h : 0 ≤ x ∧ x<1
  · simp only [Pi.mul_apply]
    rw[walshhaarpropsqr hk h.1 h.2, walshhaarprop hk h.1 h.2]
    simp only [indicator, zpow_neg, zpow_natCast, mem_Ico, Pi.pow_apply, Pi.ofNat_apply,
      Real.rpow_natCast, mul_ite, mul_zero]
    split_ifs with h1
    · rw[← Real.rpow_add (zero_lt_two)]
      simp
    · simp
  · unfold walshhaar
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, mul_eq_mul_right_iff, mul_eq_zero]
    rw[walsh_zero_outside_domain, or_comm]
    · left
      left
      simp only
    · rw[Decidable.not_and_iff_or_not, not_le, not_lt] at h
      exact h



theorem walshHaar_ort_help {M k k' : ℕ} {x : ℝ} (h : k ≠ k') :  walshhaar M k x * walshhaar M k' x = 0 := by
  unfold walshhaar
  rw[mul_comm, mul_mul_mul_comm]
  rw[haarFunctionScaled_mul]
  · simp only [mul_zero]
  · simp only [ne_eq, Nat.cast_inj]
    rw[ne_comm, ne_eq] at h
    exact h



theorem walshHaar_ort {M k k' : ℕ} (h : k ≠ k') :  ∫ y in Set.Ico 0 1, walshhaar M k y * walshhaar M k' y = 0 := by
  have h1 : EqOn (walshhaar M k * walshhaar M k') 0 (Set.Ico 0 1) := by
    unfold EqOn
    intro z hz
    apply walshHaar_ort_help h
  simp_rw[← Pi.mul_apply]
  rw[MeasureTheory.setIntegral_congr_fun (measurableSet_Ico) h1]
  simp



theorem walshhaar_s {M k : ℕ} :  (∫ x in Set.Ico  0 0.5,  walshhaar M k x) + ∫ x in Set.Ico 0.5 1,  walshhaar M k x = ∫ x in Set.Ico 0 1, walshhaar M k x  := by
  conv_rhs => rw[Eq.symm (Ico_union_Ico_eq_Ico (b:= 0.5) (by linarith) (by linarith))]
  unfold walshhaar
  rw[MeasureTheory.integral_union_ae]
  · refine Disjoint.aedisjoint (Ico_disjoint_Ico_same)
  · simp
  · apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · refine MeasureTheory.BoundedCompactSupport.restrict bcs_walsh
    · apply MeasureTheory.BoundedCompactSupport.integrable
      refine MeasureTheory.BoundedCompactSupport.restrict bcs_haarscaled
  · apply MeasureTheory.BoundedCompactSupport.integrable_mul
    · refine MeasureTheory.BoundedCompactSupport.restrict bcs_walsh
    · apply MeasureTheory.BoundedCompactSupport.integrable
      refine MeasureTheory.BoundedCompactSupport.restrict bcs_haarscaled






theorem wlashhaar_normhelp {M k : ℕ} (hk : k ≤ 2 ^ M - 1) : ∫ (x : ℝ), (Ico 0 1).indicator (fun y ↦ walshhaar M k y * walshhaar M k y) x = ∫ (x : ℝ), (Ico ((2^(-M :ℤ ) * k) :ℝ ) ((2^(-M :ℤ ) * (k+1)) :ℝ ) ).indicator (2 ^ (M :ℝ  )) x := by
    congr
    ext x
    conv_lhs => simp[indicator]
    split_ifs with h
    · rw[walshhaarpropsqr ?_ h.1 h.2]
      simp only [Finset.mem_range]
      rw[Nat.lt_iff_le_pred ]
      · exact hk
      · simp
    · simp only [indicator]
      split_ifs with h0
      · exfalso
        simp only [zpow_neg, zpow_natCast, mem_Ico] at h0
        have h01 : 0 ≤ ((2 ^ M)⁻¹: ℝ ) * ↑k := by
          rw [@mul_nonneg_iff]
          left
          constructor
          · linarith
          · linarith
        have h02 : ((2 ^ M)⁻¹: ℝ ) * (↑k + 1) ≤ 1 := by
          refine inv_mul_le_one_of_le₀ ?_ ?_
          · norm_cast
            refine Nat.add_le_of_le_sub ?_ hk
            exact Nat.one_le_two_pow
          · simp
        obtain ⟨ h0_01, h0_02⟩ := h0
        apply lt_of_lt_of_le h0_02 at h02
        apply le_trans h01 at h0_01
        push_neg at h
        simp[h0_01] at h
        linarith
      · simp



theorem wlashhaar_norm {M k : ℕ} (hk : k ≤ 2 ^ M - 1) : ∫ y in Set.Ico 0 1, (walshhaar M k y)*(walshhaar M k y)  = 1 := by
  rw[← MeasureTheory.integral_indicator (measurableSet_Ico), wlashhaar_normhelp hk]
  rw[ MeasureTheory.integral_indicator (measurableSet_Ico)]
  ring_nf
  simp




theorem walshindicatorrightformhelp {M k : ℕ} (hk : k < 2 ^ M) : ∃ (f:ℕ  → ℝ), (fun x ↦∑ j ∈ Finset.range (2^M), (walsh j x  * f j ))=  (fun x ↦ walshhaar M k x):= by
  rw[walshhaarprop'']
  · obtain ⟨ g, hg⟩ := (walshindicator' hk)
    use g * 2 ^ (M / 2 :ℝ )
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, ← mul_assoc, ← Finset.sum_mul]
    rw [@funext_iff] at hg
    ext x
    rw[hg]
    simp_rw[← indicator_mul_const, Pi.one_apply, one_mul]
    refine indicator_eq_indicator ?_ rfl
    ring_nf
  · simp only [Finset.mem_range]
    exact hk



theorem walshindicatorrightform {M k : ℕ} : ∃ (f:ℕ  → ℝ), (fun x ↦ ∑ j ∈ Finset.range (2^M), (walsh j x  * f j ))= (fun x ↦walshhaar M k x):= by
  by_cases hk : k < 2 ^ M
  · exact walshindicatorrightformhelp hk
  · use 0
    ext x
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, walshhaar, zero_eq_mul]
    by_cases h : walsh (2 ^ M) x = 0
    · left
      exact h
    · right
      apply domain at h
      rw[haarFunctionScaled_outside]
      simp only [neg_neg, zpow_natCast, Int.cast_natCast, sub_neg, ge_iff_le]
      left
      apply lt_of_lt_of_le (b:= 2^M)
      · norm_num
        exact h.2
      · simp only [not_lt] at hk
        norm_cast

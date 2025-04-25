import Mathlib
open Function Set Classical
noncomputable section

/- ## Walsh Functions and Walsh-Fourier Series -/
namespace Walsh


 /--
 Definition of Walsh function.
 -/
def walsh (n : ℕ) : ℝ → ℝ
| x =>
  if x <0 ∨  1 ≤  x then 0
  else if x < 1/2 then
    let m := n / 2
    if n = 0 then 1
    else walsh m (2 * x)
  else
    if n = 0 then 1
    else
      let m := n / 2
      if  n % 2 = 0 then walsh m (2 * x - 1)
      else -walsh m (2 * x - 1)
    #check walsh.induct

/--
Walsh function is 0 outisde`[0,1)`.
-/
@[simp]
theorem walsh_not_in {n : ℕ} (x : ℝ) (h : x < 0 ∨  1 ≤ x ) : walsh n x = 0 := by
  unfold walsh
  split_ifs with h1 h2
  · exact if_pos h
  · simp only [h, ↓reduceIte]
  simp only [h, ↓reduceIte]

/--
Walsh function for `n=0` is 1 on `[0,1)`.
-/
@[simp]
theorem walsh_zero (x : ℝ) (h1 :0 ≤ x) (h2: x <1 ) : walsh 0 x = 1 := by
  simp [walsh, h1,h2]


/--
Walsh function for `n=1` is 1 on the left half of `[0,1)`.
-/
@[simp]
theorem walsh_one_left (x : ℝ) (h1 :0 ≤ x) (h2: x < 1/2 ) : walsh 1 x =  1:= by
  simp only [walsh, one_div, one_ne_zero, ↓reduceIte, Nat.reduceDiv, ite_self, Nat.mod_succ,
    sub_neg]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain h_l|h_r := h_1
    · linarith
    · linarith
  · exfalso
    obtain h_l|h_r := h_3
    · linarith
    · linarith
  · rfl
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2
      simp_all
      linarith
    · linarith
  · exfalso
    push_neg at h_1 h_4
    linarith

/--
Walsh function for `n=1` is 1 on the right half of `[0,1)`.
-/

@[simp]
theorem walsh_one_right (x : ℝ) (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh 1 x = -1:= by
  simp only [walsh, one_div, one_ne_zero, ↓reduceIte, Nat.reduceDiv, ite_self, Nat.mod_succ,
    sub_neg]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain h_l|h_r := h_1
    · linarith
    · linarith
  · exfalso
    obtain h_l|h_r := h_3
    · linarith
    · push_neg at h_1
      simp_all
      linarith
  · exfalso
    push_neg at h_1 h_3
    linarith
  · exfalso
    obtain h_l|h_r := h_4
    · push_neg at h_2 h_1
      simp_all
      rw[inv_le_iff_one_le_mul₀ (zero_lt_two)] at h_2
      linarith
    · linarith
  · rfl


/--
Walsh function for n being even on the left half of `[0,1)`.
-/
theorem walsh_even_left {n : ℕ}{x : ℝ}(h1 :0 ≤ x) (h2: x < 1/2 ) : walsh (2*n) x = walsh n (2 * x) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ne_eq, not_false_eq_true,
    mul_div_cancel_left₀, Nat.mul_mod_right, ↓reduceIte]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    rw[h_3]
    rw[walsh_zero (2*x)]
    · linarith
    · linarith
  · rfl
  · push_neg at h_1 h_2
    rw[h_4]
    rw[walsh_zero (2*x)]
    · linarith
    · linarith
  · push_neg at h_1 h_2 h_4
    exfalso
    simp_all
    linarith

/--
Walsh function for n being even on the right half of `[0,1)`.
-/
theorem walsh_even_right {n : ℕ}{x : ℝ}  (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh (2*n) x = walsh n (2 * x - 1) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, ne_eq, not_false_eq_true,
    mul_div_cancel_left₀, Nat.mul_mod_right, ↓reduceIte]
  split_ifs with h_1 h_2 h_3 h_4
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    rw[h_3]
    rw[walsh_zero (2*x-1)]
    · linarith
    · linarith
  · push_neg at h_1 h_3
    exfalso
    simp_all
    linarith
  · push_neg at h_1 h_2
    rw[h_4]
    rw[walsh_zero (2*x-1)]
    · linarith
    · linarith
  · rfl


/--
Walsh function for n being odd on the left half of `[0,1)`.
-/


theorem walsh_odd_left {n : ℕ}{x : ℝ}(h1 :0 ≤ x) (h2: x < 1/2 ) : walsh (2*n +1) x = walsh n (2 * x) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    one_ne_zero, and_false, ↓reduceIte]
  have h_odd0 : Odd (2 * n + 1) := by
    simp
  have h_oddp : 2*((2 * n + 1  )/2) = 2*n := by
    rw[Nat.odd_iff] at h_odd0
    rw[Nat.two_mul_odd_div_two h_odd0]
    simp
  have h_odd : (2 * n + 1) / 2 = n := by
    rw[← Nat.mul_left_inj (a:=2), mul_comm, h_oddp]
    linarith
    simp
  split_ifs with h_1 h_2 h_3
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    rw[h_odd]
  · rw[h_odd]
    push_neg at h_1 h_2
    exfalso
    rw[Nat.odd_iff] at h_odd0
    linarith
  · push_neg at h_1 h_2 h_3
    rw[h_odd]
    simp_all
    linarith

/--
Walsh function for n being odd on the right half of `[0,1)`.
-/


theorem walsh_odd_right {n : ℕ}{x : ℝ} (h1 :1/2 ≤ x) (h2: x < 1 ) : walsh (2*n+ 1) x =- walsh n (2 * x - 1) := by
  conv_lhs =>
    unfold walsh
  simp only [one_div, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    one_ne_zero, and_false, ↓reduceIte]
  have h_odd0 : Odd (2 * n + 1) := by
    simp
  have h_oddp : 2*((2 * n + 1  )/2) = 2*n := by
    rw[Nat.odd_iff] at h_odd0
    rw[Nat.two_mul_odd_div_two h_odd0]
    simp
  have h_odd : (2 * n + 1) / 2 = n := by
    rw[← Nat.mul_left_inj (a:=2), mul_comm, h_oddp]
    linarith
    simp
  split_ifs with h_1 h_2 h_3
  · exfalso
    obtain hl|hp := h_1
    · linarith
    · linarith
  · push_neg at h_1
    exfalso
    simp_all
    linarith
  · rw[h_odd]
    push_neg at h_1 h_2
    exfalso
    rw[Nat.odd_iff] at h_odd0
    linarith
  · push_neg at h_1 h_2 h_3
    rw[h_odd]


/--
Relation between Walsh function of `2n` and `2n+1`.
-/
theorem walsh_even_odd_left {n : ℕ}{x : ℝ} (h1 :0 ≤ x) (h2: x < 1/2 ): walsh (2*n) x = walsh (2*n +1) x:= by
  rw[ walsh_even_left h1 h2, walsh_odd_left h1 h2]

theorem walsh_even_odd_right {n : ℕ}{x : ℝ} (h1 :1/2 ≤ x) (h2: x < 1 ) :walsh (2*n) x = - walsh (2*n +1) x:= by
  rw[ walsh_even_right h1 h2, walsh_odd_right h1 h2]
  simp

/--
Walsh functions are nonzero on `[0,1)`.
-/
theorem walsh_in (n : ℕ) : ∀ x : ℝ, 0 ≤ x ∧  x < 1 → walsh n x ≠ 0 := by
  induction' n using Nat.strong_induction_on with n ih
  intro x hx
  set k := n/2 with h_k
  by_cases hzero :n = 0
  · rw[hzero, walsh_zero]
    · linarith
    · let h1:= hx.1
      exact h1
    · let h2:= hx.2
      exact h2
  · by_cases hone : n = 1
    · rw[hone]
      by_cases h : x< 1/2
      · rw[walsh_one_left]
        · linarith
        · linarith
        · exact h
      · push_neg at h
        rw[walsh_one_right]
        · linarith
        · exact h
        · linarith
    · have hk2 : k < n := by
        push_neg at hzero
        rw[h_k]
        apply Nat.div2Induction.proof_2
        apply Nat.pos_of_ne_zero hzero
      by_cases h0 : Odd n
      · have hk1 : 2*k+1 = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_add_one_of_odd
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_odd_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · let h1:= hx.1
            exact h1
          · exact h
        · push_neg at h
          rw[walsh_odd_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            simp only [ne_eq, neg_eq_zero]
            exact ih k hk2 y hy
          · exact h
          · let h2:= hx.2
            exact h2
      · push_neg at h0
        simp only [Nat.not_odd_iff_even] at h0
        have hk1 : 2*k = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_of_even
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_even_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · let h1:= hx.1
            exact h1
          · exact h
        · push_neg at h
          rw[walsh_even_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
          · let h2:= hx.2
            exact h2
--ten dowód jest taki sam jak wcześniejszy - to nie ma sensu -> wcześniejsze twierdzenie powinno korzystać z wcześniejszego
theorem walsh_sqr1 (n : ℕ) : ∀ x : ℝ, 0 ≤ x ∧  x < 1 → (walsh n x)*(walsh n x) =1 := by
  induction' n using Nat.strong_induction_on with n ih
  intro x hx
  set k := n/2 with h_k
  by_cases hzero :n = 0
  · rw[hzero, walsh_zero]
    · linarith
    · let h1:= hx.1
      exact h1
    · let h2:= hx.2
      exact h2
  · by_cases hone : n = 1
    · rw[hone]
      by_cases h : x< 1/2
      · rw[walsh_one_left]
        · linarith
        · linarith
        · exact h
      · push_neg at h
        rw[walsh_one_right]
        · linarith
        · exact h
        · linarith
    · have hk2 : k < n := by
        push_neg at hzero
        rw[h_k]
        apply Nat.div2Induction.proof_2
        apply Nat.pos_of_ne_zero hzero
      by_cases h0 : Odd n
      · have hk1 : 2*k+1 = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_add_one_of_odd
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_odd_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · let h1:= hx.1
            exact h1
          · exact h
        · push_neg at h
          rw[walsh_odd_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            simp only [mul_neg, neg_mul, neg_neg]
            exact ih k hk2 y hy
          · exact h
          · let h2:= hx.2
            exact h2
      · push_neg at h0
        simp only [Nat.not_odd_iff_even] at h0
        have hk1 : 2*k = n := by
          rw[h_k]
          rw[mul_comm]
          apply Nat.div_two_mul_two_of_even
          exact h0
        rw[← hk1]
        by_cases h : x<1/2
        · rw[walsh_even_left]
          · set y:= 2* x with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · let h1:= hx.1
            exact h1
          · exact h
        · push_neg at h
          rw[walsh_even_right]
          · set y:= 2* x -1 with h_y
            have hy : 0≤ y ∧ y<1 := by
              rw[h_y]
              constructor
              · linarith
              · linarith
            exact ih k hk2 y hy
          · exact h
          · let h2:= hx.2
            exact h2

/--
Squere of Wlash functions is 1 on `[0,1).`
-/

theorem sqr_walsh {n : ℕ} (x : ℝ) (h1 : 0 ≤ x)(h2: x < 1) : (walsh n x)*(walsh n x) = 1 := by
  apply walsh_sqr1
  constructor
  · exact h1
  · exact h2

 /--
Walsh function is zero outside the interval `[0, 1)`.
  -/
@[simp]
theorem walsh_zero_outside_domain (n : ℕ) (x : ℝ) (h : x < 0 ∨ x ≥ 1) : walsh n x = 0 := by
simp [walsh, h]







theorem walsh_values {n : ℕ} {x : ℝ} (h1 : 0 ≤ x)(h2: x < 1) : walsh n x = 1 ∨ walsh n x =-1 := by
  rw[← sq_eq_one_iff, pow_two]
  apply sqr_walsh
  · exact h1
  exact h2


/--
Product of Wlash functions of fixed `n` and different arguments is 0 outside `[0, 1)`.
-/
theorem mul_walsh_outside {n : ℕ} (x y : ℝ ) (h : x <0 ∨  1 ≤  x) : (walsh n x)*(walsh n y ) =  0:= by
  rw[walsh_not_in]
  · simp only [zero_mul]
  exact  h


theorem mul_walsh_outside' {n : ℕ} (x y : ℝ ) (h : x <0 ∨  1 ≤  x) : (walsh n y )*(walsh n x) =  0:= by
  rw[mul_comm, mul_walsh_outside]
  exact  h


--**ToDo** : Prove the statement about the product of Wlash functions of fixed `n` and different arguments in `[0, 1)`-/
--theorem mul_walsh {n : ℕ} (x y : ℝ ): (walsh n x)*(walsh n y ) =




/--
Walsh inner product definition.
-/
def walshInnerProduct (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ico 0 1, f x * walsh n x



/--
`n`th Walsh inner product of walsh function of `m` is equal to the `m`th Walsh inner product of walsh function of `n`.
-/
theorem walshInnermul {n m : ℕ}  : walshInnerProduct (walsh n) m = walshInnerProduct (walsh m) n := by
  simp only [walshInnerProduct]
  have h1 : EqOn ((walsh n)*(walsh m)) ((walsh m)*(walsh n))  (Set.Ico 0 (1:ℝ)):= by
    rw[mul_comm]
    exact fun ⦃x⦄ ↦ congrFun rfl
  have h2 : MeasurableSet (Set.Ico 0 (1:ℝ)) := by
    simp
  change ∫ (x : ℝ) in Ico 0 1, (walsh n * walsh m) x = ∫ (x : ℝ) in Ico 0 1, (walsh m * walsh n) x
  rw[MeasureTheory.setIntegral_congr_fun h2 h1]



/--
Walsh functions have norm 1.
-/
theorem walsh_norm (n : ℕ) :
  walshInnerProduct (walsh n) n = 1 := by
  unfold walshInnerProduct
  have hs : MeasurableSet (Set.Ico 0 (1 : ℝ )) := by
    simp
  have h1 : EqOn ((walsh n)*(walsh n)) 1  (Set.Ico 0 (1:ℝ)):= by
    intro x hx
    rw [Pi.mul_apply, Pi.one_apply, sqr_walsh ]
    · simp_all
    · simp_all
  change ∫ (x : ℝ) in Ico 0 1, (walsh n * walsh n) x = 1
  rw[MeasureTheory.setIntegral_congr_fun hs h1]
  simp

/-- Walsh functions are orthogonal.-/
theorem walsh_ort_same {n m : ℕ} (h: m = n) : walshInnerProduct (walsh n) m  = 1 := by
  rw [h]
  apply walsh_norm


theorem walsh_ort_dif {n m : ℕ} (h: m ≠  n) : walshInnerProduct (walsh n) m  = 0 := by

  sorry


/--
Multiplication Walsh inner product by scalar.
-/
theorem walshInnerProduct_smul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (λ x => c * f x) n = c * walshInnerProduct f n := by
  simp only [walshInnerProduct]
  simp_rw[← MeasureTheory.integral_mul_left, mul_assoc]


/--
Multiplication Walsh inner product by function.
-/
theorem mul_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) (x : ℝ ) :
  walshInnerProduct (λ y ↦ g x * f y) n = ∫ y in Set.Ico 0 1, g x * f y * walsh n y := by
  unfold walshInnerProduct
  simp

theorem add_walshInnerProduct (f g : ℝ → ℝ) (n : ℕ) :
  walshInnerProduct (λ y ↦ g y + f y) n = ∫ y in Set.Ico 0 1, (g y + f y) * walsh n y := by
  unfold walshInnerProduct
  simp


/--
Definition of Walsh Fourier partial sum.
-/
def walshFourierPartialSum (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
 λ x => ∑ n in Finset.range N, (walshInnerProduct f n) * walsh n x

/--
Definition of Walsh Fourier Series.
-/
def walshFourierSeries (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x => tsum (λ N => walshFourierPartialSum f N x)

/--
Binary representation of a number as a set of indices.
-/
def binaryRepresentationSet (n : ℕ) : Finset ℕ :=
  Finset.filter (λ m => Nat.testBit n m) (Finset.range (Nat.size n + 1))

/--
Condition for being in the binary representation set.
-/
theorem mem_binaryRepresentationSet_iff (n m : ℕ) :
  m ∈ binaryRepresentationSet n ↔ (Nat.testBit n m = true) := by
  simp only [binaryRepresentationSet, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  apply m.testBit_implies_ge at h
  rw [ge_iff_le, ← m.lt_size] at h
  linarith


/--
Binary representation set of `0` is empty.
-/
theorem binaryRepresentationSet_zero : binaryRepresentationSet 0 = ∅ := by
  simp [binaryRepresentationSet, Nat.testBit_zero]


/--
Binary representation set of `n>0` is nonempty.
-/

theorem binaryRepresentationSet_not_zero (n : ℕ ) (h : n >0 )  : binaryRepresentationSet n ≠  ∅ := by
  rw[gt_iff_lt, ← Nat.ne_zero_iff_zero_lt] at h
  apply Nat.ne_zero_implies_bit_true at h
  obtain ⟨ i, h_i ⟩ := h
  rw[←  mem_binaryRepresentationSet_iff ] at h_i
  simp only [ne_eq]
  intro h
  rw [h] at h_i
  exact Finset.not_mem_empty i h_i




/--
Removing an element from the binary representation set.
-/

theorem remove_bit (N M : ℕ) (h : M ∈ binaryRepresentationSet N) : binaryRepresentationSet N \ {M} = binaryRepresentationSet (N - 2^M) := by
  rw [mem_binaryRepresentationSet_iff] at h
  have h1 : (N - 2^M).testBit M = false := by
    set N' := N - 2^M with hs
    have hs: N' + 2^M = N := by
      rw[hs]
      sorry
    rw[← hs] at h



    sorry
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_binaryRepresentationSet_iff]
  constructor
  · sorry
  · sorry
  --Nat.testBit_two_pow_add_eq
  --Nat.testBit_two_pow_add_gt
 /- rw [mem_binaryRepresentationSet_iff ] at h
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro h1
    rcases h1 with ⟨hr, hl⟩
    · push_neg at hl
      rw [mem_binaryRepresentationSet_iff N x] at hr
      apply (mem_binaryRepresentationSet_iff (N - 2 ^ M) x).mpr ?h.mp.intro.a
      apply Nat.testBit_implies_ge at hr
      sorry
  · sorry-/

/--
Natural number can be written using the sum of two to the power of element of binary representation set.
-/

theorem binaryRepresentationSet_explicit (n :ℕ ) : ∑ k in binaryRepresentationSet n, 2^k = n := by
  induction' n using Nat.strong_induction_on with n ih
  sorry

/--
Binary representation set has maximal element.
-/

theorem max_binaryRepresentationSet (n : ℕ ) (h : n >0 ) : ∃ k ∈  binaryRepresentationSet n, ∀ j > k, j ∉ binaryRepresentationSet n := by
  have h0 : (binaryRepresentationSet n).Nonempty := by
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h
  have h1 :  ∃ (a : ℕ), Finset.max (binaryRepresentationSet n )= a := by
    apply Finset.max_of_nonempty h0
  obtain ⟨ a , ha ⟩ := h1
  have h : a ∈ binaryRepresentationSet n := by
    exact Finset.mem_of_max ha
  use a, h
  simp only [gt_iff_lt]
  intro j hj
  exact Finset.not_mem_of_max_lt hj ha

/--
Binary representation set has minimal element.
-/
theorem min_binaryRepresentationSet (n : ℕ) (h : n >0 ) : ∃ k ∈  binaryRepresentationSet n, ∀ j < k, j ∉ binaryRepresentationSet n := by
  have h0 : (binaryRepresentationSet n).Nonempty := by
    apply binaryRepresentationSet_not_zero at h
    exact Finset.nonempty_iff_ne_empty.mpr h
  have h1 :  ∃ (a : ℕ), Finset.min (binaryRepresentationSet n )= a := by
    apply Finset.min_of_nonempty h0
  obtain ⟨ a , ha ⟩ := h1
  have h : a ∈ binaryRepresentationSet n := by
    exact Finset.mem_of_min ha
  use a, h
  intro j hj
  exact Finset.not_mem_of_lt_min hj ha

theorem wlashradhelp0 (n m : ℕ)(h: m ∈ Walsh.binaryRepresentationSet n) : (m+1) ∈ Walsh.binaryRepresentationSet (2*n) := by
  rw[mem_binaryRepresentationSet_iff] at h
  rw[mem_binaryRepresentationSet_iff]
  rw[← Nat.testBit_div_two]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
  rw[h]






end Walsh

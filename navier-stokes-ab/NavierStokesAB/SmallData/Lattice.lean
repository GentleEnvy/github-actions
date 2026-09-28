import Mathlib

/-!
# Frequencies `ℤ³` and exponential weights

The Fourier modes on `ℝ³/ℤ³` are indexed by `Λ = Fin 3 → ℤ`. We record the Euclidean length
`kn k = |k|`, its basic properties, and summability of `|k|^m e^{-c|k|}` over `Λ`.
-/

open Real

namespace NavierStokesAB.SmallData

/-- Frequencies of `ℝ³/ℤ³`. -/
abbrev Λ := Fin 3 → ℤ

/-- A frequency as a point of `ℝ³`. -/
noncomputable def kR (k : Λ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 fun i => (k i : ℝ)

@[simp] theorem kR_apply (k : Λ) (i : Fin 3) : kR k i = k i := rfl

theorem kR_add (j k : Λ) : kR (j + k) = kR j + kR k := by
  ext i; simp

theorem kR_neg (k : Λ) : kR (-k) = -kR k := by
  ext i; simp

theorem kR_sub (j k : Λ) : kR (j - k) = kR j - kR k := by
  ext i; simp

@[simp] theorem kR_zero : kR 0 = 0 := by
  ext i; simp

/-- The length `|k|` of a frequency. -/
noncomputable def kn (k : Λ) : ℝ := ‖kR k‖

theorem kn_nonneg (k : Λ) : 0 ≤ kn k := norm_nonneg _

theorem kn_add_le (j k : Λ) : kn (j + k) ≤ kn j + kn k := by
  unfold kn; rw [kR_add]; exact norm_add_le _ _

@[simp] theorem kn_neg (k : Λ) : kn (-k) = kn k := by
  unfold kn; rw [kR_neg, norm_neg]

@[simp] theorem kn_zero : kn 0 = 0 := by simp [kn]

/-- `|k| ≤ |j| + |k - j|`: the frequency triangle inequality used for convolutions. -/
theorem kn_le_add_sub (k j : Λ) : kn k ≤ kn j + kn (k - j) := by
  have := kn_add_le j (k - j)
  rwa [add_sub_cancel] at this

theorem abs_le_kn (k : Λ) (i : Fin 3) : |(k i : ℝ)| ≤ kn k := by
  have := PiLp.norm_apply_le (kR k) i
  simpa [kn, Real.norm_eq_abs] using this

theorem one_le_kn {k : Λ} (hk : k ≠ 0) : 1 ≤ kn k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (abs_le_kn k i)

theorem sum_abs_le (k : Λ) : ∑ i, |(k i : ℝ)| ≤ 3 * kn k := by
  have h : ∀ i ∈ Finset.univ, |(k i : ℝ)| ≤ kn k := fun i _ => abs_le_kn k i
  calc ∑ i, |(k i : ℝ)| ≤ ∑ _i : Fin 3, kn k := Finset.sum_le_sum h
    _ = 3 * kn k := by simp

/-! ### Summability -/

theorem summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => exp (-c * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => exp (-c) ^ n :=
    summable_geometric_of_lt_one (exp_pos _).le (exp_lt_one_iff.2 (by linarith))
  apply Summable.of_nat_of_neg
  · refine hg.congr fun n => ?_
    rw [← exp_nat_mul]
    congr 1
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  · refine hg.congr fun n => ?_
    rw [← exp_nat_mul]
    congr 1
    push_cast
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    ring

theorem summable_pi_prod {g : ℤ → ℝ} (hg : Summable g) (h0 : ∀ n, 0 ≤ g n) (m : ℕ) :
    Summable fun k : Fin m → ℤ => ∏ i, g (k i) := by
  induction m with
  | zero =>
    have : Unique (Fin 0 → ℤ) := Pi.uniqueOfIsEmpty _
    exact Summable.of_finite
  | succ m ih =>
    have hf' : (0 : ℤ → ℝ) ≤ g := fun n => h0 n
    have hg' : (0 : (Fin m → ℤ) → ℝ) ≤ fun k => ∏ i, g (k i) :=
      fun k => Finset.prod_nonneg fun i _ => h0 (k i)
    have hprod := Summable.mul_of_nonneg hg ih hf' hg'
    refine (Fin.consEquiv fun _ : Fin (m + 1) => ℤ).summable_iff.1 ?_
    refine hprod.congr fun p => ?_
    show g p.1 * ∏ i, g (p.2 i) = ∏ i, g (Fin.cons (α := fun _ => ℤ) p.1 p.2 i)
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]

theorem summable_exp_neg_kn {c : ℝ} (hc : 0 < c) : Summable fun k : Λ => exp (-c * kn k) := by
  have hprod := summable_pi_prod (summable_exp_neg_abs_int (c := c / 3) (by positivity))
    (fun n => (exp_pos _).le) 3
  refine hprod.of_nonneg_of_le (fun k => (exp_pos _).le) fun k => ?_
  rw [← Real.exp_sum]
  apply exp_le_exp.2
  have h := sum_abs_le k
  have : ∑ i, -(c / 3) * |(k i : ℝ)| = -(c / 3) * ∑ i, |(k i : ℝ)| := by
    rw [Finset.mul_sum]
  rw [this]
  nlinarith

theorem pow_mul_exp_neg_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → r ^ m * exp (-c * r) ≤ C := by
  refine ⟨m.factorial / c ^ m, fun r hr => ?_⟩
  have h := Real.pow_div_factorial_le_exp (c * r) (mul_nonneg hc.le hr) m
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hcm : 0 < c ^ m := pow_pos hc m
  rw [div_le_iff₀ hfac, mul_pow] at h
  rw [le_div_iff₀ hcm, mul_comm (r ^ m), mul_assoc, mul_comm, mul_assoc]
  calc r ^ m * (c ^ m * exp (-c * r)) = (c ^ m * r ^ m) * exp (-c * r) := by ring
    _ ≤ (exp (c * r) * m.factorial) * exp (-c * r) :=
        mul_le_mul_of_nonneg_right h (exp_pos _).le
    _ = m.factorial := by rw [mul_comm (exp _), mul_assoc, ← exp_add]; simp

theorem summable_pow_mul_exp_neg_kn (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable fun k : Λ => kn k ^ m * exp (-c * kn k) := by
  obtain ⟨C, hC⟩ := pow_mul_exp_neg_le m (c := c / 2) (by positivity)
  refine ((summable_exp_neg_kn (c := c / 2) (by positivity)).mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (kn_nonneg k) m) (exp_pos _).le) fun k => ?_
  have h := hC (kn k) (kn_nonneg k)
  calc kn k ^ m * exp (-c * kn k) = (kn k ^ m * exp (-(c / 2) * kn k)) * exp (-(c / 2) * kn k) := by
        rw [mul_assoc, ← exp_add]; ring_nf
    _ ≤ C * exp (-(c / 2) * kn k) := mul_le_mul_of_nonneg_right h (exp_pos _).le

end NavierStokesAB.SmallData

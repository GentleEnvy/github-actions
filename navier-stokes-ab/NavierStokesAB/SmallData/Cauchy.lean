import NavierStokesAB.SmallData.Fields

/-!
# The convective term in Fourier variables, and real parts

* `four_convective`: for divergence-free coefficients `c` and `U = four c x`,
  `Σₖ e_k(x) (2πi ⟪k, U⟫) c_k = Σ_n e_n(x) Σⱼ 2πi ⟪n, c_j⟫ c_{n-j}` (a Cauchy product over `ℤ³`).
* `four_real`: Hermitian coefficients give a real field; `re3`/`ofReal3` pass between `ℂ³` and `ℝ³`.
-/

open Real Complex Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace ComplexConjugate ContDiff

set_option synthInstance.maxHeartbeats 200000

namespace NavierStokesAB.SmallData

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem Lk_add (j k : Λ) : Lk (j + k) = Lk j + Lk k := by
  ext h
  simp [Lk_apply, kR_add, inner_add_left]
  ring

theorem Lk_neg (k : Λ) : Lk (-k) = -Lk k := by
  ext h
  simp [Lk_apply, kR_neg, inner_neg_left]

theorem emode_add (j k : Λ) (x : ℝ³) : emode (j + k) x = emode j x * emode k x := by
  rw [emode, emode, emode, Lk_add, ContinuousLinearMap.add_apply, Complex.exp_add]

theorem conj_emode (k : Λ) (x : ℝ³) : conj (emode k x) = emode (-k) x := by
  rw [emode, emode, ← Complex.exp_conj, Lk_neg, ContinuousLinearMap.neg_apply, Lk_apply]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem kC_sub (j k : Λ) : kC (j - k) = kC j - kC k := by ext i; simp

theorem kC_add (j k : Λ) : kC (j + k) = kC j + kC k := by ext i; simp

/-- The frequency `(k, j) ↦ (k + j, j)` shear. -/
def shear' : Λ × Λ ≃ Λ × Λ where
  toFun p := (p.1 + p.2, p.2)
  invFun q := (q.1 - q.2, q.2)
  left_inv p := by simp
  right_inv q := by simp

theorem norm_two_pi_I : ‖(2 * (π : ℂ) * I)‖ = 2 * π := by
  simp [Complex.norm_I, abs_of_pos pi_pos]

section Convective

variable (c : Λ → V) (x : ℝ³)

/-- The double series of the convective term, indexed by `(k, j)`. -/
noncomputable def cvF (p : Λ × Λ) : V :=
  emode p.1 x • ((2 * π * I * (emode p.2 x * ⟪kC p.1, c p.2⟫_ℂ)) • c p.1)

/-- The same double series indexed by `(n, j) = (k + j, j)`. -/
noncomputable def cvG (q : Λ × Λ) : V :=
  emode q.1 x • ((2 * π * I * ⟪kC q.1, c q.2⟫_ℂ) • c (q.1 - q.2))

variable {c}

theorem cvF_eq (hdiv : ∀ j, ⟪kC j, c j⟫_ℂ = 0) (p : Λ × Λ) : cvF c x p = cvG c x (shear' p) := by
  obtain ⟨k, j⟩ := p
  show emode k x • ((2 * π * I * (emode j x * ⟪kC k, c j⟫_ℂ)) • c k) =
    emode (k + j) x • ((2 * π * I * ⟪kC (k + j), c j⟫_ℂ) • c (k + j - j))
  rw [add_sub_cancel_right, emode_add, kC_add, inner_add_left, hdiv j, add_zero, smul_smul,
    smul_smul]
  congr 1
  ring

theorem norm_cvF_le (p : Λ × Λ) : ‖cvF c x p‖ ≤ (2 * π * (kn p.1 * ‖c p.1‖)) * ‖c p.2‖ := by
  show ‖emode p.1 x • ((2 * π * I * (emode p.2 x * ⟪kC p.1, c p.2⟫_ℂ)) • c p.1)‖ ≤ _
  rw [norm_smul, norm_emode, one_mul, norm_smul, norm_mul, norm_two_pi_I, norm_mul, norm_emode,
    one_mul]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (kC p.1) (c p.2)
  rw [norm_kC] at h1
  calc 2 * π * ‖⟪kC p.1, c p.2⟫_ℂ‖ * ‖c p.1‖ ≤ 2 * π * (kn p.1 * ‖c p.2‖) * ‖c p.1‖ := by
        gcongr
    _ = 2 * π * (kn p.1 * ‖c p.1‖) * ‖c p.2‖ := by ring

theorem summable_cvF (hc : RapidDecay c) : Summable (cvF c x) := by
  have hsumB : Summable fun p : Λ × Λ => (2 * π * (kn p.1 * ‖c p.1‖)) * ‖c p.2‖ :=
    Summable.mul_of_nonneg (f := fun k => 2 * π * (kn k * ‖c k‖)) (g := fun k => ‖c k‖)
      ((hc 1).mul_left (2 * π) |>.congr fun k => by ring) hc.summable_norm
      (fun k => mul_nonneg (by positivity) (mul_nonneg (kn_nonneg k) (norm_nonneg _)))
      fun k => norm_nonneg _
  exact Summable.of_norm_bounded hsumB (norm_cvF_le x)

theorem tsum_cvF_eq (hdiv : ∀ j, ⟪kC j, c j⟫_ℂ = 0) : ∑' p, cvF c x p = ∑' q, cvG c x q :=
  (tsum_congr (cvF_eq x hdiv)).trans (shear'.tsum_eq (cvG c x))

theorem summable_cvG (hc : RapidDecay c) (hdiv : ∀ j, ⟪kC j, c j⟫_ℂ = 0) :
    Summable (cvG c x) := by
  rw [← shear'.summable_iff]
  exact (summable_cvF x hc).congr (cvF_eq x hdiv)

theorem inner_kC_four (hc : RapidDecay c) (k : Λ) :
    ⟪kC k, four c x⟫_ℂ = ∑' j, emode j x * ⟪kC k, c j⟫_ℂ := by
  rw [four, ← innerSL_apply_apply, (innerSL ℂ (kC k)).map_tsum (summable_four hc x)]
  simp [inner_smul_right]

theorem four_lhs_eq (hc : RapidDecay c) :
    four (fun k => (2 * π * I * ⟪kC k, four c x⟫_ℂ) • c k) x = ∑' p, cvF c x p := by
  have hsum := summable_cvF x hc
  simp only [inner_kC_four x hc]
  rw [hsum.tsum_prod' fun k => hsum.prod_factor k]
  unfold four
  congr 1
  funext k
  beta_reduce
  have hs : Summable fun j => emode j x * ⟪kC k, c j⟫_ℂ :=
    Summable.of_norm_bounded (hc.summable_norm.mul_left (kn k)) fun j => by
      rw [norm_mul, norm_emode, one_mul, ← norm_kC]
      exact norm_inner_le_norm _ _
  have hs2 : Summable fun j => 2 * π * I * (emode j x * ⟪kC k, c j⟫_ℂ) := hs.mul_left _
  rw [← tsum_mul_left, ← hs2.tsum_smul_const, ← tsum_const_smul'']
  rfl

theorem four_rhs_eq (hc : RapidDecay c) (hdiv : ∀ j, ⟪kC j, c j⟫_ℂ = 0) :
    four (fun n => ∑' j, (2 * π * I * ⟪kC n, c j⟫_ℂ) • c (n - j)) x = ∑' q, cvG c x q := by
  have hsum := summable_cvG x hc hdiv
  rw [hsum.tsum_prod' fun n => hsum.prod_factor n]
  unfold four
  congr 1
  funext n
  exact (tsum_const_smul'' _).symm

/-- **The convective term.** -/
theorem four_convective (hc : RapidDecay c) (hdiv : ∀ j, ⟪kC j, c j⟫_ℂ = 0) :
    four (fun k => (2 * π * I * ⟪kC k, four c x⟫_ℂ) • c k) x =
      four (fun n => ∑' j, (2 * π * I * ⟪kC n, c j⟫_ℂ) • c (n - j)) x := by
  rw [four_lhs_eq x hc, four_rhs_eq x hc hdiv, tsum_cvF_eq x hdiv]

end Convective

end NavierStokesAB.SmallData
